from util import Tutor, Session
import datetime

DAY_MAP = {"MON": "MONDAY", "TUE": "TUESDAY", "WED": "WEDNESDAY", "THU": "THURSDAY", "FRI": "FRIDAY",
           "SAT": "SATURDAY", "SUN": "SUNDAY", "MONDAY": "MONDAY", "TUESDAY": "TUESDAY", "WEDNESDAY": "WEDNESDAY",
           "THURSDAY": "THURSDAY", "FRIDAY": "FRIDAY", "SATURDAY": "SATURDAY", "SUNDAY": "SUNDAY",
           "MO": "MONDAY", "TU": "TUESDAY", "WE": "WEDNESDAY", "TH": "THURSDAY", "FR": "FRIDAY", "SA": "SATURDAY",
           "SU": "SUNDAY", "M": "MONDAY", "W": "WEDNESDAY", "F": "FRIDAY"}


def parse_day(day):
    return DAY_MAP.get(day.upper(), day)


def parse_time(time):
    afternoon = False
    morning = False
    if "pm" in time:
        afternoon = True
        time = time.rstrip("pm")
    elif "am" in time:
        morning = True
        time = time.rstrip("am")

    if ":" in time:
        hrs, _, mins = time.partition(":")
        hrs = int(hrs)
        mins = int(mins)
    else:
        hrs = int(time)
        mins = 0

    if afternoon and hrs != 12:
        hrs += 12
    if morning and hrs == 12:
        hrs = 0

    return datetime.datetime(2019, 1, 1, hrs, mins)


class Reader:
    def __init__(self, filename="avail.csv", tutor_info="tutor_info.csv", session_info="session_info.csv"):
        self._filename = filename
        self._tutor_info = tutor_info
        self._session_info = session_info
        self._tutors = None
        self._sessions = None
        self._avail = None

    def get_grid(self):
        grid = []
        with open(self._filename, "r") as f:
            for line in f:
                grid.append(line.strip().split(","))
        return grid

    def read_avail(self):
        grid = self.get_grid()

        self._avail = {}
        tutor_list = grid[0][1:]
        self._tutors = {i: Tutor(i) for i in tutor_list}
        self._sessions = {}
        for i, row in enumerate(grid[1:]):
            self._sessions[row[0]] = Session(row[0])
            for j, item in enumerate(row[1:]):
                self._avail[(tutor_list[j], row[0])] = True if item in ("A", "1", "OK") else False

    def read_session_info(self):
        with open(self._session_info, "r") as f:
            first = f.readline().strip().split(",")[1:]
            index_name_mapping = {i: item for i, item in enumerate(first)}
            for line in f:
                session = line[:line.index(",")]
                for i, item in enumerate(line.strip().split(",")[1:]):
                    field = index_name_mapping[i]
                    if field == "DAY":
                        self._sessions[session].day = parse_day(item)
                    elif field == "START_TIME":
                        self._sessions[session].start_time = parse_time(item)
                    elif field == "DURATION":
                        self._sessions[session].duration = int(item)
                    elif field == "TUTOR_COUNT":
                        self._sessions[session].tutor_count = int(item)

    def read_tutor_info(self):
        with open(self._tutor_info, "r") as f:
            first = f.readline().strip().split(",")[1:]
            index_tutor_mapping = {i: item for i, item in enumerate(first)}
            for line in f:
                field = line[:line.index(",")]
                for i, item in enumerate(line.strip().split(",")[1:]):
                    tutor = index_tutor_mapping[i]
                    if field == "MIN_HRS":
                        self._tutors[tutor].lower_hr_limit = int(item)
                    elif field == "MAX_HRS":
                        self._tutors[tutor].upper_hr_limit = int(item)
                    elif field == "MAX_CONTIG":
                        self._tutors[tutor].max_contig = int(item)
                    elif field == "PREF_CONTIG":
                        self._tutors[tutor].pref_contig = True if item in ("1", "Y") else False
                    elif field == "IS_JUNIOR":
                        self._tutors[tutor].is_tutor = True if item in ("1", "Y") else False
                    elif field.startswith("MIN_HRS_"):
                        field_type = field.lstrip("MIN_HRS_")
                        self._tutors[tutor].lower_type_limits[field_type] = int(item)

    def compute_clashes(self):
        for session_name in self._sessions:
            session = self._sessions[session_name]
            for other_name in self._sessions:
                other = self._sessions[other_name]
                if other_name != session_name and other.day == session.day:
                    for i in range(session.duration):
                        if session.start_time + datetime.timedelta(hours=i) == other.start_time:
                            session.clashes.append(other)
                    for i in range(other.duration):
                        if other.start_time + datetime.timedelta(hours=i) == session.start_time \
                                and other not in session.clashes:
                            session.clashes.append(other)

    def get_contig_pairs(self):
        pairs = []
        for session_name in self._sessions:
            session = self._sessions[session_name]
            for other_name in self._sessions:
                other_session = self._sessions[other_name]
                if other_name != session_name and other_session.day == session.day \
                        and session.start_time + datetime.timedelta(hours=session.duration) == other_session.start_time:
                    pairs.append((session_name, other_name))
        return pairs

    def get_contig_chains(self):
        pairs = self.get_contig_pairs()
        chains = []

        while len(pairs) > 0:
            pair = pairs.pop()
            chains.append(list(pair))
            for chain in chains:
                if chain[-1] == pair[0]:
                    chain.append(pair[1])
                elif chain[0] == pair[-1]:
                    chain.insert(0, pair[0])

        return pairs

    def get_tutors(self):
        return self._tutors

    def get_sessions(self):
        return self._sessions

    def get_avail(self):
        return self._avail
