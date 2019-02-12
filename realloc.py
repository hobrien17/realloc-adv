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

	def check_sat(self):
		self._write()
		self._file.write("\n(check-sat)\n")
		self._file.close()
		try:
			return subprocess.check_output(["z3", "model", "-t:30000"]).decode("UTF-8").strip() == "sat"
		except subprocess.CalledProcessError:
			print("Verification aborted - either an error occured or no satisfiable model could be found")
			print("Please reduce any constraints and try again")
			raise RuntimeError

	def get_alloc(self):
		self._write()
		self._file.write("\n(check-sat)\n")
		for i in range(len(self._classes)):
			for j in range(len(self._tutors)):
				self._file.write("(get-value (i-{}-{}))\n".format(i, j))
		self._file.close()

		matrix = [[False for i in range(len(self._tutors))] for i in range(len(self._classes))]
		try:
			for line in subprocess.check_output(["z3", "model", "-t:30000"]).decode("UTF-8").strip().split("\n")[1:]:
				line = line.strip("((").strip("))")
				var, _, val = line.partition(" ")
				if val == "true":
					_, s, t = var.split("-")
					matrix[int(s)][int(t)] = True

			return matrix
		except subprocess.CalledProcessError:
			print("Verification aborted - either an error occured or no satisfiable model could be found")
			print("Please reduce any constraints and try again")
			raise RuntimeError

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
		chash_i = self._index_classes(clash)
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


def _parse_match(alloc, match_params, action_params):
	assert len(match_params) == 2
	generator = None
	if match_params[0] == "C":
		generator = alloc.iter_classes()
	elif match_params[0] == "T":
		generator = alloc.iter_tutors()
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

	
