"""Define a datastruct of tactic restriction"""
class Restriction:
    """Three arg"""
    def __init__(self, first_set, second_set, interval):
        self.first_set = first_set
        self.second_set = second_set
        self.interval = interval
