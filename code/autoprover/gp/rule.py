"""This module provide rules based on triggers and actions
"""
import json
from autoprover.gp.action import GeneAction
from autoprover.gp.trigger import GeneTrigger

class Rule:
    """base class"""
    def __init__(self, trigger=None, action_list=None, file_name=None):
        if file_name:
            self.read_from_file(file_name)
        else:
            self.trigger = trigger
            self.action_list = action_list

    def read_from_file(self, file_name):
        """Read a rule from a JSON file"""
        self.action_list = []
        with open(file_name) as json_file:
            json_data = json.load(json_file)

        def read_action_helper(data):
            """Read from a dict, construct a Action instance."""
            action_type = data["type"]
            if action_type == "append_tactic":
                cmd = ["edit"]
                data = ["append", data["tactic"]]
                return GeneAction(cmd=cmd, data=data)
            elif action_type == "penalty":
                cmd = ["penalty"]
                return GeneAction(cmd=cmd, data=data["penalty_val"])

        def read_trigger_helper(data):
            """read from a dict, construct a Trigger instance."""
            trigger_type = data["type"]
            if trigger_type == "last_goal":
                return GeneTrigger(last_goal=data["goal"])
            elif trigger_type == "last_goal_contain":
                return GeneTrigger(last_goal_contain=data["goal"])
            elif trigger_type == "tactic_restriction":
                first_set = {e for e in data["first_set"]}
                second_set = {e for e in data["second_set"]}
                restriction = {"first_set": first_set, "second_set": second_set,
                               "interval": int(data["interval"])}
                return GeneTrigger(tactic_restriction=restriction)

        for json_action in json_data["actions"]:
            self.action_list.append(read_action_helper(json_action))
        self.trigger = read_trigger_helper(json_data["trigger"])

    def set_trigger(self, trigger):
        """set trigger"""
        self.trigger = trigger

    def print_trigger(self):
        """print trigger"""
        print(self.trigger)

class GeneRule(Rule):
    """rules applied on gene"""
    def __init__(self, trigger=None, action_list=None, proof=None,
                 file_name=None):
        super().__init__(trigger, action_list, file_name)
        self.proof = proof
        self.type = "gene"

    def check_and_apply(self, gene):
        """Check gene is need to be applied action or not"""
        ret = self.trigger.test(gene)
        if ret["status"]:
            for _ in range(ret["count"]):
                for action in self.action_list:
                    action.apply(gene)
        if ret["update"]:
            gene.update_fitness_for_proof(self.proof)
