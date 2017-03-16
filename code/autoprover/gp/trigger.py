"""test gene or population"""
class Trigger:
    """Base class"""
    def __init__(self):
        pass

class GeneTrigger(Trigger):
    """Gene trigger"""
    def __init__(self, last_goal=None, last_goal_contain=None, 
                 tactic_restriction=None, json=None):
        super().__init__()
        if json:
            print(type(json))
        else:
            self.last_goal = last_goal
            self.last_goal_contain = last_goal_contain
            self.tactic_restriction = tactic_restriction

    def test(self, gene):
        """test if gene trigger action"""
        if self.last_goal:
            ret = {"status": self.last_goal == gene.goal.rstrip("\n"),
                   "update": True, "count": 1}
            return ret
        if self.last_goal_contain:
            last_goal = gene.goal.split("\n\n")[0]
            if self.last_goal_contain in last_goal:
                print(last_goal)
            ret = {"status": last_goal.find(self.last_goal_contain) != -1,
                   "update": True, "count": 1}
            return ret
        elif self.tactic_restriction:
            first_set = self.tactic_restriction["first_set"]
            second_set = self.tactic_restriction["second_set"]
            interval = self.tactic_restriction["interval"]

            def check_repeat(tactics):
                """check func"""
                index = 0
                count = 0
                while index < len(tactics):
                    if tactics[index] in first_set:
                        for i in range(interval):
                            n_index = index+i+1
                            if n_index >= len(tactics):
                                break
                            else:
                                if tactics[index+i+1] in second_set:
                                    count += 1
                    index += 1
                return count

            count = check_repeat(gene.valid_tactics)
            if count > 0:
                return {"status": True, "update": False, "count": count}
            else:
                return {"status": False, "update": False, "count": 1}
            # return func(gene.valid_tactics)
