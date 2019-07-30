import z3
from reader import Reader
from writer import Writer


class Engine:
    def __init__(self, reader: Reader, optimize=True):
        self._reader = reader
        self._optimize = optimize
        self._solver: z3.Solver = None

        self._optimal = {}
        self._vars = {}

        self.reset()
        self._solver.set("timeout", 10000)
        with open("model.txt", "w") as f:
            f.write(str(self._solver.to_smt2()))

    def generate_decls(self):
        for tutor in self._reader.get_tutors():
            for session in self._reader.get_sessions():
                name = tutor + "-" + session
                self._vars[name] = z3.Bool(name)

    def generate_assertions(self):
        # AVAILABILITY ASSERTIONS
        self._generate_avail_assertions()

        for session_name in self._reader.get_sessions():
            session = self._reader.get_sessions()[session_name]
            self._generate_tutor_count_assertions(session)
            self._generate_clashes(session)

        for tutor_name in self._reader.get_tutors():
            tutor = self._reader.get_tutors()[tutor_name]
            self._generate_lower_limit_assertions(tutor)
            self._generate_upper_limit_assertions(tutor)
            self._generate_lower_type_limits(tutor)

        #self._generate_junior_senior_assertions()
        self._generate_contig_max()

    def _generate_avail_assertions(self):
        for pair in self._reader.get_avail():
            if not self._reader.get_avail()[pair]:
                self._solver.add(z3.Not(self._vars["-".join(pair)]))

    def _generate_tutor_count_assertions(self, session):
        self._solver.add(session.tutor_count == z3.Sum([z3.If(self._vars[t + "-" + session.get_id()], 1, 0)
                                                        for t in self._reader.get_tutors()]))

    def _generate_lower_limit_assertions(self, tutor):
        if tutor.lower_hr_limit is not None:
            self._solver.add(tutor.lower_hr_limit <= z3.Sum([z3.If(self._vars[tutor.get_name() + "-" + s],
                                                                   self._reader.get_sessions()[s].duration, 0)
                                                             for s in self._reader.get_sessions()]))

    def _generate_upper_limit_assertions(self, tutor):
        if tutor.upper_hr_limit is not None:
            self._solver.add(tutor.upper_hr_limit >= z3.Sum([z3.If(self._vars[tutor.get_name() + "-" + s],
                                                                   self._reader.get_sessions()[s].duration, 0)
                                                             for s in self._reader.get_sessions()]))

    def _generate_lower_type_limits(self, tutor):
        print(tutor.get_name(), tutor.lower_type_limits)
        for type_ in tutor.lower_type_limits:
            self._solver.add(tutor.lower_type_limits[type_] <= z3.Sum([z3.If(self._vars[tutor.get_name() + "-" + s],
                                                                             self._reader.get_sessions()[s].duration, 0)
                                                                       for s in self._reader.get_sessions()
                                                                       if s.startswith(type_)]))

    def _generate_junior_senior_assertions(self):
        seniors = []
        for tutor_name in self._reader.get_tutors():
            tutor = self._reader.get_tutors()[tutor_name]
            if not tutor.is_junior:
                seniors.append(tutor_name)
        print(seniors)

        for session_name in self._reader.get_sessions():
            if self._reader.get_sessions()[session_name].tutor_count > 1:
                self._solver.add(z3.Or([self._vars[tutor + "-" + session_name] for tutor in seniors]))

    def _generate_clashes(self, session):
        for tutor in self._reader.get_tutors():
            for clash in session.clashes:
                self._solver.add(z3.Not(z3.And(self._vars[tutor + "-" + session.get_id()],
                                               self._vars[tutor + "-" + clash.get_id()])))

    def _generate_contig_caps(self, tutor):
        pass

    def _generate_contig_max(self, value=0):
        contig = z3.Int("contig")
        self._solver.add(contig == z3.Sum([z3.If(z3.And(
            self._vars[tutor + "-" + name1],
            self._vars[tutor + "-" + name2]), 1, 0)
            for name1, name2 in self._reader.get_contig_pairs()
            for tutor in self._reader.get_tutors()]))
        self._solver.add(contig >= value)

    def _block(self, model):
        # Create a new constraint the blocks the current model
        block = []
        for d in model:
            # create a constant from declaration
            c = d()
            block.append(c != model[d])
        self._solver.add(z3.Or(block))

    def solve(self, cap=5):
        models = []
        while self._solver.check() == z3.sat:
            print("Model found!")
            if cap == 0:
                return models
            model = self._solver.model()
            models.append(model)
            self._block(model)
            cap -= 1
        return models

    def reset(self):
        self._vars = {}
        self._solver = z3.Optimize() if self._optimize else z3.Solver()
        self.generate_decls()
        self.generate_assertions()

    def get_var(self, name):
        return self._vars[name]


def run():
    reader = Reader()
    reader.read_avail()
    reader.read_session_info()
    reader.read_tutor_info()
    reader.compute_clashes()

    engine = Engine(reader, optimize=False)
    models = engine.solve()

    if len(models) == 0:
        print("No valid allocation found")
        return

    writer = Writer(models, engine, reader)
    success = False
    while not success:
        try:
            success = writer.write_model()
        except StopIteration:
            print("No more models left")
            break


if __name__ == "__main__":
    run()