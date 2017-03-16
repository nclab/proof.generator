"""
define TacticSet
"""
import random
import logging
import operator
import numpy as np

class TacticsSet():
    """
    regist a tactic set, and some operation
    """
    def __init__(self, tacticBase=None):
        self.usage = None
        self.read(tacticBase)

    def read(self, tactic_base):
        """
        read tactics from file
        """
        self.repeatable = set()
        self.unrepeatable = set()
        rep_flag = True

        for line in tactic_base:
            line = line.strip()
            if not line.startswith("#"):
                for tactic in line.rstrip().split(','):
                    if tactic == "":
                        continue
                    if rep_flag:
                        self.repeatable.add(tactic+".")
                    else:
                        self.unrepeatable.add(tactic+".")
                # rep_flag = True
            else:
                if line.startswith("#unrepeatable"):
                    rep_flag = False
        logging.info("%d tactics loaded",
                     len(self.repeatable) + len(self.unrepeatable))

    @property
    def all_tactics(self):
        """return all tactic"""
        return self.repeatable | self.unrepeatable

    def mutate_select(self):
        """return a tactic by inversion of tactic usage"""
        sorted_stats = sorted(self.usage.items(),
                              key=operator.itemgetter(1), reverse=True)
        tactic = [e[0] for e in sorted_stats]
        prob = [e[1] for e in sorted_stats]
        prob = prob[::-1]
        print(prob)
        index = np.random.choice(tactic, 1, p=prob)
        return index[0]

    def random_select(self):
        """
        return a tactic in the set
        """

        return np.random.choice([e for e in self.all_tactics])
        # return random.choice(tuple(self.repeatable | self.unrepeatable))

    def is_unrepeatable(self, tactic):
        """
        if tactic in the set
        """
        return tactic in self.unrepeatable

    def remove(self, tactic):
        """remove a tactic in the set"""
        if tactic in self.repeatable:
            self.repeatable.remove(tactic)
        if tactic in self.unrepeatable:
            self.unrepeatable.remove(tactic)
