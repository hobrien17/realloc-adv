class Tutor:
    def __init__(self, name):
        self._name = name
        self.lower_hr_limit = 1
        self.upper_hr_limit = None
        self.type_pref = None
        self.lower_type_limits = {}
        self.is_junior = False
        self.max_contig = None
        self.pref_contig = True

    def get_name(self):
        return self._name


class Session:
    def __init__(self, id_):
        self._id = id_
        self.tutor_count = 1
        self.duration = 1
        self.day = None
        self.start_time = None
        self.clashes = []

    def get_id(self):
        return self._id
