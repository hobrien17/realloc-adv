class Writer:
    def __init__(self, models, engine, reader, filename="output.csv"):
        self._models = (i for i in models)
        self._engine = engine
        self._reader = reader
        self._filename = filename

    def write_model(self, output_char="E", append=True):
        model = next(self._models)

        for i in sorted(model, key=lambda x: str(x)):
            print(i, model[i])

        grid = []
        with open("output.csv", "r") as f:
            for line in f:
                grid.append(line.strip().split(","))
        print(grid)

        tutor_indexes = {}
        for i, tutor in enumerate(self._reader.get_tutors()):
            grid[0][i + 1] = tutor
            tutor_indexes[tutor] = i

        for i, session in enumerate(self._reader.get_sessions()):
            for tutor in tutor_indexes:
                if model[self._engine.get_var(tutor + "-" + session)]:
                    grid[i + 1][tutor_indexes[tutor] + 1] = output_char
                elif not append:
                    grid[i + 1][tutor_indexes[tutor] + 1] = ""

        with open("output.csv", "w") as f:
            for line in grid:
                f.write(",".join(line) + "\n")

        if input("Model written - is it suitable? (y/n) ").upper() == "Y":
            if input("Update availability? (y/n) ").upper() == "Y":
                self.override_existing(model)
            return True
        else:
            return False

    def override_existing(self, model):
        unavailable = set()
        for tutor_name in self._reader.get_tutors():
            for session_name in self._reader.get_sessions():
                if model[self._engine.get_var(tutor_name + "-" + session_name)]:
                    unavailable.add((tutor_name, session_name))
                    for clash in self._reader.get_sessions()[session_name].clashes:
                        unavailable.add((tutor_name, clash.get_id()))

        grid = self._reader.get_grid()
        tutor_indices = {i: item for i, item in enumerate(grid[0][1:])}
        for i, row in enumerate(grid[1:]):
            session_name = row[0]
            for j, item in enumerate(row[1:]):
                tutor_name = tutor_indices[j]
                if (tutor_name, session_name) in unavailable:
                    grid[i + 1][j + 1] = "U"

        with open("avail.csv", "w") as f:
            for row in grid:
                f.write(",".join(row) + "\n")