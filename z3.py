import sys
import subprocess
import csv
import json
import os
import random
import argparse
from collections import OrderedDict


class Person:
    def __init__(self, id_, **kwargs):
        self._id = id_
        self._min_classes = kwargs.get("minhours", 1)
        self._max_classes = kwargs.get("maxhours", 1)
        self._prefs = kwargs.get("pref", [])

    def get_id(self):
        return self._id

    def get_min_classes(self):
        return self._min_classes

    def get_max_classes(self):
        return self._max_classes

    def get_prefs(self):
        return self._prefs

    def __str__(self):
        return self._id

    def __repr__(self):
        return str(self)


class Session:
    def __init__(self, id_, **kwargs):
        self._id = id_
        self._num_people = kwargs.get("tutors", 1)
        self._hours = kwargs.get("hours", 1)

    def get_id(self):
        return self._id

    def get_num_people(self):
        return self._num_people

    def get_hours(self):
        return self._hours

    def __str__(self):
        return self._id

    def __repr__(self):
        return str(self)


def generate_assertions(people, sessions, clashes, availability, extra_assertions=""):
    z3 = ""

    # generate const declarations
    for person_id in people:
        for session_id in sessions:
            z3 += "(declare-const {} Bool)\n".format(person_id + "-" + session_id)

    # generate unavailability assertions
    for person_id in people:
        for session_id in sessions:
            person = people[person_id]
            session = sessions[session_id]
            if (person, session) not in availability:
                z3 += "(assert (not {}))\n".format(person_id + "-" + session_id)

    # define session count assertions - eg (assert T01 has 1 tutor)
    for session_id in sessions:
        z3 += "(assert (= (+ {}) {}))\n".format(
            " ".join(["(if {} 1 0)".format(person_id + "-" + session_id) for person_id in people]),
            sessions[session_id].get_num_people()
        )

    # define person hour count assertions - eg (assert Alice is working between 3 and 5 hours)
    for person_id in people:
        z3 += "(assert (<= (+ {}) {}))\n".format(
            " ".join(["(if {} {} 0)".format(person_id + "-" + session_id,
                                            sessions[session_id].get_hours()) for session_id in sessions]),
            people[person_id].get_max_classes()
        )
        z3 += "(assert (>= (+ {}) {}))\n".format(
            " ".join(["(if {} {} 0)".format(person_id + "-" + session_id,
                                            sessions[session_id].get_hours()) for session_id in sessions]),
            people[person_id].get_min_classes()
        )

    # define clash assertions
    for session1, session2 in clashes:
        for person_id in people:
            z3 += "(assert (not (and {} {})))\n".format(person_id + "-" + session1.get_id(),
                                                        person_id + "-" + session2.get_id())

    # define preference assertions
    for person_id in people:
        person = people[person_id]
        for pref, sym, count in person.get_prefs():
            session_list = []
            for session_id in sessions:
                if session_id.startswith(pref):
                    session_list.append(session_id)
            z3 += "(assert ({} (+ {}) {}))\n".format(
                sym,
                " ".join(["(if {} 1 0)".format(person_id + "-" + session_id) for session_id in session_list]),
                count
            )

    z3 += extra_assertions
    z3 += "(check-sat)\n"

    return z3


def shuffle_dict(d):
    new = OrderedDict()
    keys = list(d.keys())
    random.shuffle(keys)
    for k in keys:
        new[k] = d[k]
    return new


def find_model(people, sessions, clashes, availability, extra_assertions="", count=1):
    z3 = generate_assertions(people, sessions, clashes, availability, extra_assertions)

    # execute!
    with open("z3.in", "w") as f:
        f.write(z3)

    try:
        if subprocess.check_output(["z3", "z3.in", "-t:30000"]).decode("UTF-8").strip() == "unsat":
            print("No possible allocation")
            return
    except subprocess.CalledProcessError:
        raise RuntimeError("Fatal error thrown while generating allocation")

    models = set()
    for i in range(count):
        people = shuffle_dict(people)
        sesssions = shuffle_dict(sessions)
        z3 = generate_assertions(people, sessions, clashes, availability, extra_assertions)

        with open("z3.in", "w") as f:
            f.write(z3)
            for person_id in people:
                for session_id in sessions:
                    f.write("(get-value ({}))\n".format(person_id + "-" + session_id))

        models.add(frozenset(parse_model(subprocess.check_output(["z3", "z3.in", "-t:10000"]).decode("UTF-8"),
                                         people, sessions)))

    return models


def parse_model(output, people, sessions):
    result = set()

    for line in output.split("\n"):
        if "((" in line and "))" in line:
            line = line.lstrip("((").rstrip("))")
            var, _, val = line.partition(" ")
            p, _, s = var.partition("-")
            if p in people and s in sessions and val == "true":
                result.add((p, s))

    return result


def input_csv(filename):
    with open(filename, "r", newline='') as f:
        reader = list(csv.reader(f, delimiter=","))
        tutor_count, _, session_count = reader[0][0].partition("/")
        tutor_count = int(tutor_count)
        session_count = int(session_count)
        tutors = OrderedDict()
        sessions = OrderedDict()

        for col in range(1, tutor_count + 1):
            kwds = {}
            for row in range(session_count + 1, len(reader)):
                if reader[row][0] in ("minhours", "maxhours"):
                    kwds[reader[row][0]] = reader[row][col]
                elif reader[row][0] == "pref" and reader[row][col].count(" ") == 2:
                    kwds[reader[row][0]] = kwds.get(reader[row][0], []) + [reader[row][col].split(" ")]
            tutors[reader[0][col]] = Person(reader[0][col], **kwds)

        clash_ids = []
        for row in range(1, session_count + 1):
            kwds = {}
            for col in range(tutor_count + 1, len(reader[row])):
                if reader[0][col] in ("tutors", "hours"):
                    kwds[reader[0][col]] = reader[row][col]
                elif reader[0][col] == "clash" and reader[row][col] != "":
                    clash_ids.append((reader[row][0], reader[row][col]))
            sessions[reader[row][0]] = Session(reader[row][0], **kwds)

        clashes = {frozenset((sessions[a], sessions[b])) for a, b in clash_ids}

        availability = set()
        for col, tutor in enumerate(tutors):
            for row, session in enumerate(sessions):
                if reader[row + 1][col + 1] == "A":
                    availability.add((tutors[tutor], sessions[session]))

        return tutors, sessions, clashes, availability


def output_csv(filename, tutors, sessions, model):
    table = [["" for i in range(len(tutors) + 1)] for j in range(len(sessions) + 1)]
    tmap = {}
    smap = {}
    for i, tutor_id in enumerate(tutors):
        table[0][i + 1] = tutor_id
        tmap[tutor_id] = i + 1
    for i, session_id in enumerate(sessions):
        table[i + 1][0] = session_id
        smap[session_id] = i + 1

    for t, s in model:
        table[smap[s]][tmap[t]] = "Y"

    with open(filename, "w") as f:
        writer = csv.writer(f)
        writer.writerows(table)


def output_json(filename, model):
    with open(filename, "w") as f:
        f.write(json.dumps(list(model)))


def run(input_file, **kwargs):
    count = kwargs.get("multi", 1)
    max_model = kwargs.get("max", 10)
    use_csv = kwargs.get("csv", True)
    use_json = kwargs.get("json", False)
    tutors, sessions, clashes, availability = input_csv(input_file)

    models = find_model(tutors, sessions, clashes, availability, count=count)
    models = {m for i, m in enumerate(models) if i < max_model}
    print(len(models), "models found")
    dir_path = os.path.join(os.path.dirname(os.path.realpath(input_file)), "models")
    if os.path.exists(dir_path):
        for file in os.listdir(dir_path):
            filepath = os.path.join(dir_path, file)
            if os.path.isfile(filepath):
                os.unlink(filepath)
    else:
        os.mkdir(dir_path)
    for i, model in enumerate(models):
        if use_csv:
            output_csv(os.path.join(dir_path, "model{}.csv").format(i), tutors, sessions, model)
        if use_json:
            output_json(os.path.join(dir_path, "model{}.json").format(i), model)
    print("Allocation complete! All models can be found in " + dir_path)


def main():
    args = sys.argv
    filename = args[1]
    kwargs = {}
    for arg in args[2:]:
        if arg.startswith("--toCSV"):
            if "=" in arg and arg.parititon("=")[2].lower() == "false":
                kwargs["csv"] = False
            else:
                kwargs["csv"] = True
        elif arg.startswith("--toJSON"):
            if "=" in arg and arg.partition("=")[2].lower() == "false":
                kwargs["json"] = False
            else:
                kwargs["json"] = True
        elif arg.startswith("--multi"):
            if "=" in arg:
                kwargs["multi"] = int(arg.partition("=")[2])
            else:
                pass  # TODO: invalid
        elif arg.startswith("--max"):
            if "=" in arg:
                kwargs["max"] = int(arg.partition("=")[2])
            else:
                pass  # TODO: invalid

    run(filename, **kwargs)


if __name__ == "__main__":
    main()
