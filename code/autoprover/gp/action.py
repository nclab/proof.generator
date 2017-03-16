"""Store user specific action"""

class Action:
    """Base action class"""
    def __init__(self, cmd, data):
        self.cmd = cmd
        self.data = data

class GeneAction(Action):
    """Gene action class"""
    def __init__(self, cmd=None, data=None, json=None):
        if json:
            print(type(json))
        else:
            super().__init__(cmd, data)

    def apply(self, gene):
        """perform action on gene"""
        if self.cmd[0] == "edit":
            gene.modification(data=self.data)
        elif self.cmd[0] == "penalty":
            print(gene.valid_tactics)
            gene.fitness -= float(self.data)
