"""Coqstate
This module describe the state of coqtop, including hypothesis, current goals
and a coq tactic.

Example:
    current_state = Coqstate(some_coq_output, a_tactic)
"""

class CoqState:
    """
    coq state data structure
    Args:
        text (string): a state of coqtop
        tactic (string): tactic used in this state
    """
    def __init__(self, text, tactic):
        self._is_proof = False
        self._tactic = tactic
        self.data = text
        self._goal = ""
        self._hypothesis = ""
        self._error = False
        if not self.is_proof:
            self.parse(text)

    def __eq__(self, other):
        return self.goal == other.goal and self.hypothesis == other.hypothesis

    def __str__(self):
        return 'Tactic: %s\n%s\n%s\n%s' % (self.tactic, self.hypothesis,
                                           "============================",
                                           self.goal)
    @property
    def is_proof(self):
        """If it's a proof

        Returns:
            bool: True if proof complete in this state.
        """
        return self._is_proof

    @property
    def tactic(self):
        """Tactic of this state

        Returns:
            string: a tactic
        """
        return self._tactic

    @property
    def goal(self):
        """Goal of state

        Returns:
            string: goal of current state
        """
        return self._goal

    @property
    def hypothesis(self):
        """Hypothesis of state

        Returns:
            string: hypothesis
        """
        return self._hypothesis

    @property
    def is_error_state(self):
        """Error state attribute

        Returns:
            bool: True if this state has some error message
        """
        return self._error

    def parse(self, text):
        """Parse goal and hypothesis from text
        set _error and _no_more_goal
        """
        goal_flag = False
        goal = []
        hypothesis = []
        for i, line in enumerate(text.split("\n")):
            line = line.strip()
            if line.find("No more subgoals.") > -1:
                self._is_proof = True
                return
            elif (line.startswith("Error: No such unproven subgoal")
                  or line.startswith("Error: No such goal.")):
                self._error = True
                self._is_proof = True
                return
            elif (line.find("Error:") > -1 or line.startswith("H, H")
                  or line.startswith("IHn, H")):
                self._error = True
                return
            if i > 1:
                if line.startswith("==="):
                    goal_flag = True
                else:
                    if goal_flag:
                        goal.append(line)
                    else:
                        hypothesis.append(line)
        self._goal = '\n'.join(goal)
        self._hypothesis = '\n'.join(hypothesis)

        if not self._goal:
            self._is_proof = True
