import subprocess
import re
import random
import os
import shutil
import sys

############################
######## ALLOCATOR #########
############################

class Allocator:
	def __init__(self, tutors, classes, prefs):
		self._tutors = tutors
		self._classes = classes
		self._hours = [1 for i in classes]
		self._prefs = prefs

		self._junior = []
		self._senior = []
		self._nopair = set()

		self._contig_blocks = []
		self._contig_prefs = self._tutors[:]
		self._max_contig = {}

		self._decls = []
		self._assertions = []
		self._add_prefs()
		self._file = None

	def iter_tutors(self):
		for tutor in self._tutors:
			yield tutor

	def iter_classes(self):
		for cls in self._classes:
			yield cls

	def _contig_maximisation(self, value=-1):
		pairings = []
		limits = []
		for i, tutor in enumerate(self._contig_prefs):
			tid = self._index_tutors(tutor)
			tutor_limits = []
			for pre, post in self._contig_blocks:
				pre_id = self._index_classes(pre)
				post_id = self._index_classes(post)
				pairings.append("(if (and i-{}-{} i-{}-{}) 1 0)".format(pre_id, tid, post_id, tid))
				tutor_limits.append("(if (and i-{}-{} i-{}-{}) (+ d-{} d-{}) 0)".format(pre_id, tid, post_id, tid, pre_id, post_id))

			if tutor in self._max_contig:
				limits.append("(assert (<= (+ {}) {}))".format(" ".join(tutor_limits), self._max_contig[tutor]))
		
		if value < 0:
			return limits + ["(maximize (+ {}))".format(" ".join(pairings))]
		else:
			return limits + ["(assert (>= (+ {}) {}))".format(" ".join(pairings), value)]
				

	def _junior_senior_matching(self):
		result = []
		for junior in self._junior:
			jid = self._index_tutors(junior)
			for i in range(len(self._classes)):
				if self._classes[i] not in nopair:
					result.append("(assert (if i-{}-{} (or {}) true))".format(i, jid, " ".join("i-{}-{}".format(i, self.index_tutors(senior)) for senior in self._senior)))

		return result

	def _write(self):
		self._file = open("model", "w")
		random.shuffle(self._decls)
		random.shuffle(self._assertions)
		self._file.write("\n".join(self._decls + ["(declare-const d-{} Int)".format(i) for i in range(len(self._hours))]) + "\n")
		self._file.write("\n".join(self._assertions + ["(assert (= d-{} {}))".format(i, val) for i, val in enumerate(self._hours)] + self._junior_senior_matching()) + "\n")
		print("Model written to file")

	def optimise(self, timeout=10000):
		self._write()
		self._file.write("\n".join(self._contig_maximisation()))
		self._file.write("\n(check-sat)\n".format(timeout))
		self._file.close()
		proc = subprocess.Popen(["z3", "model", "-t:{}".format(timeout)], stdout=subprocess.PIPE)
		stdout, stderr = proc.communicate()
		stdout = stdout.decode("UTF-8").strip()
		if stdout.strip() == "sat":
			return -1

		for line in stdout.split("\n"):
			line = line.strip()
			if line.endswith("))"):
				return int(line.rstrip("))").split("(")[-1].split()[0])# TODO: make this line nicer

		return -1

	def get_alloc(self):
		if len(self._contig_blocks) > 0:
			optim_value = self.optimise()
			self._write()
			self._file.write("\n".join(self._contig_maximisation(optim_value)))
		else:
			self._write()
		self._file.write("\n(check-sat)\n")
		for i in range(len(self._classes)):
			for j in range(len(self._tutors)):
				self._file.write("(get-value (i-{}-{}))\n".format(i, j))
		self._file.close()

		matrix = [[False for i in range(len(self._tutors))] for i in range(len(self._classes))]
		proc = subprocess.Popen(["z3", "model", "-t:10000"], stdout=subprocess.PIPE)
		stdout, stderr = proc.communicate()
		stdout = stdout.decode("UTF-8").strip()
		if stdout.startswith("unsat"):
			print("No satisfiable model could be found")
			raise RuntimeError
		for line in stdout.split("\n")[1:]:
			line = line.strip("((").strip("))")
			var, _, val = line.partition(" ")
			if val == "true":
				_, s, t = var.split("-")
				matrix[int(s)][int(t)] = True

		return matrix

	def _add_prefs(self):
		for i, row in enumerate(self._prefs):
			for j, item in enumerate(row):
				self._decls.append("(declare-const i-{}-{} Bool)".format(i, j))
				if not item:
					self._assertions.append("(assert (not i-{}-{}))".format(i, j))

	def _index_classes(self, cls):
		try:
			return self._classes.index(cls)
		except ValueError:
			print("Class {} cannot be found".format(cls))
			raise RuntimeError

	def _index_tutors(self, tutor):
		try:
			return self._tutors.index(tutor)
		except ValueError:
			print("Tutor {} cannot be found".format(tutor))
			raise RuntimeError

	def set_clash(self, cls, clash):
		cls_i = self._index_classes(cls)
		clash_i = self._index_classes(clash)
		for j in range(len(self._tutors)):
			self._assertions.append("(assert (not (and i-{}-{} i-{}-{})))".format(cls_i, j, clash_i, j))

	def set_single_clash(self, cls, clash, tutor):
		pattern = re.compile(tutor)
		cls_i = self._index_classes(cls)
		clash_i = self._index_classes(clash)
		for j in range(len(self._tutors)):
			if pattern.match(self._tutors[j]):
				self._assertions.append("(assert (not (and i-{}-{} i-{}-{})))".format(cls_i, j, clash_i, j))
		

	def set_duration(self, cls, duration):
		self._hours[self._index_classes(cls)] = duration

	def set_junior(self, tutor):
		self._junior.append(tutor)

	def set_senior(self, tutor):
		self._senior.append(tutor)

	def no_pair(self, cls):
		self._nopair.add(cls)

	def _set_tutor_limit(self, cls, limit, sign):
		i = self._index_classes(cls)
		self._assertions.append("(assert ({} (+ {}) {}))".format(sign, " ".join("(if i-{}-{} 1 0)".format(i, j) for j in range(len(self._tutors))), limit))

	def set_lower_tutor_limit(self, cls, limit):
		self._set_tutor_limit(cls, limit, ">=")

	def set_upper_tutor_limit(self, cls, limit):
		self._set_tutor_limit(cls, limit, "<=")

	def set_exact_tutor_limit(self, cls, limit):
		self._set_tutor_limit(cls, limit, "=")

	def _set_class_limit(self, tutor, limit, sign):
		j = self._index_tutors(tutor)
		self._assertions.append("(assert ({} (+ {}) {}))".format(sign, " ".join("(if i-{}-{} d-{} 0)".format(i, j, i) for i in range(len(self._classes))), limit))

	def set_lower_class_limit(self, tutor, limit):
		self._set_class_limit(tutor, limit, ">=")

	def set_upper_class_limit(self, tutor, limit):
		self._set_class_limit(tutor, limit, "<=")

	def set_exact_class_limit(self, tutor, limit):
		self._set_class_limit(tutor, limit, "=")

	def _set_type_limit(self, tutor, type_, limit, sign):
		pattern = re.compile(type_)
		j = self._index_tutors(tutor)
		self._assertions.append("(assert ({} (+ {}) {}))".format(sign, " ".join("(if i-{}-{} d-{} 0)".format(i, j, i) for i in range(len(self._classes)) 
																				if pattern.match(self._classes[i])), limit))

	def set_lower_type_limit(self, tutor, type_, limit):
		self._set_type_limit(tutor, type_, limit, ">=")

	def set_upper_type_limit(self, tutor, type_, limit):
		self._set_type_limit(tutor, type_, limit, "<=")

	def set_exact_type_limit(self, tutor, type_, limit):
		self._set_type_limit(tutor, type_, limit, "=")

	def set_max_contig(self, tutor, value):
		self._max_contig[tutor] = value

	def pref_contig(self, tutor):
		self._contig_prefs.append(tutor)

	def pref_non_contig(self, tutor):
		self._contig_prefs.remove(tutor)

	def contig(self, flag, *args):
		if not flag:  # flag is used to stop people from calling contig as a T or C command
			print("Contig should be used as a standalone command")
			raise RuntimeError
		for i in range(len(args) - 1):
			self._contig_blocks.append((args[i], args[i + 1]))


############################
##### COMMAND PARSER #######
############################


def _parse_action(alloc, match, action_params):
	assert len(action_params) >= 1
	assert not action_params[0].startswith("_")
	try:
		method = getattr(alloc, action_params[0])
		method_params = [match]
		for param in action_params[1:]:
			if param.isdigit():
				method_params.append(int(param))
			else:
				method_params.append(param)
		method(*method_params)
	except AttributeError as e:
		print("Invalid method {}".format(action_params[0]))
		raise RuntimeError
	except TypeError:
		print("Invalid params for method {}".format(action_params[0]))
		raise RuntimeError


def _parse_contiguous(alloc, action_params):
	alloc.contig(True, *action_params)


def _parse_match(alloc, match_params, action_params):
	generator = None
	if match_params[0].upper() == "C":
		generator = alloc.iter_classes()
	elif match_params[0].upper() == "T":
		generator = alloc.iter_tutors()
	elif match_params[0].upper() == "CONTIGUOUS":
		_parse_contiguous(alloc, action_params)
		return
	else:
		print("Invalid commands")
		raise RuntimeError

	pattern = re.compile(match_params[1])
	for i in generator:
		if pattern.match(i):
			_parse_action(alloc, i, action_params)


def read_commands(filename, alloc):
	with open(filename, "r") as f:
		cmds = [line for line in f]

	for cmd in cmds:
		cmd = cmd.partition("#")[0]
		match, _, action = cmd.partition("=>")
		match_params = match.strip().split()
		action_params = action.strip().split()
		_parse_match(alloc, match_params, action_params)


############################
######## CSV READER ########
############################


def read_csv(filename):
	with open(filename, "r") as f:
		lines = [line.strip().split(",") for line in f]
	first_line = lines[0][1:]
	first_col = [i[0] for i in lines[1:]]
	matrix = [[True if i.upper() == "A" else False for i in line[1:]] for line in lines[1:]]
	return Allocator(first_line, first_col, matrix)


def write_csv(filename, alloc):
	contents = ""
	contents += "," + ",".join(alloc.iter_tutors()) + "\n"
	classes = alloc.iter_classes()
	for row in alloc.get_alloc():
		contents += next(classes) + "," + ",".join("Y" if i else "N" for i in row ) + "\n"
	with open(filename, "w") as f:
		f.write(contents)


def multi_write(folder, alloc, times=1):
	if os.path.exists(folder):
		shutil.rmtree(folder)
	os.mkdir(folder)

	for i in range(times):
		write_csv(os.path.join(folder, "model{}.csv".format(i)), alloc)


############################
########### MAIN ###########
############################


def help(prompt=None):
	if prompt is not None:
		print(prompt)
	print("Usage: python3 realloc.py input_csv output_csv [--cmds commands_file] [--multi count]")
	return 1


def parse_args(**kwargs):
	input_csv = kwargs.get("csv")
	input_cmds = kwargs.get("cmds")
	output_csv = kwargs.get("out")
	multi = int(kwargs.get("multi", 0))

	if input_csv is None:
		return help("Missing input filename")
	else:
		alloc = read_csv(input_csv)
	if input_cmds is not None:
		read_commands(input_cmds, alloc)
	if output_csv is None:
		return help("Missing output filename")
	else:
		if multi > 0:
			multi_write(output_csv, alloc, multi)
		else:
			write_csv(output_csv, alloc)

	print("Verification complete!")
	return 0


def main(args):
	if "-h" in args or "--help" in args:
		return help()

	kwargs = {}
	if len(args) >= 2:
		kwargs["csv"] = args[1]
	if len(args) >= 3:
		kwargs["out"] = args[2]

	args = args[3:][::-1]
	while len(args) > 0:
		if args[-1] == "--cmds" and len(args) > 1:
			args.pop()
			kwargs["cmds"] = args.pop()
		elif args[-1] == "--multi" and len(args) > 1:
			args.pop()
			kwargs["multi"] = args.pop()
	
	try:
		return parse_args(**kwargs)
	except RuntimeError:
		return 1
		

if __name__ == "__main__":
	main(sys.argv)

	
