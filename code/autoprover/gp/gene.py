"""
define class Gene
"""
# from random import randint
from autoprover.evaluation import evaluation
# import logging

def random_chromosome(tactics):
    """generate a random chromosome with length of 15.

    Args:
        tactics (Tactic): a Tactic class instance.

    Returns:
        list: chromosome, a list of string(tactic).
    """
    chromosome = []
    for _ in range(15):
        tactic = tactics.random_select()
        if len(chromosome) == 0:
            chromosome.append(tactic)
        else:
            while (tactics.is_unrepeatable(tactic) and
                   tactic == chromosome[-1]):
                tactic = tactics.random_select()
            chromosome.append(tactic)
    return chromosome

class Gene:
    """
    gene for gp

    Args:
        tactics (Tactic): a Tactic class instance.
        chromosome (list): can provide a chromosome.
    """
    def __init__(self, tactics=None, chromosome=None):
        if chromosome is not None:
            self.chromosome = chromosome
        else:
            self.chromosome = random_chromosome(tactics)
        self.fitness = 0
        self.raw_fitness = 0
        self.coq_states = None
        self.ttl = 0

    def __len__(self):
        return len(self.chromosome)

    @property
    def is_proof(self):
        """True if this gene is a Proof

        Returns:
            bool: is_proof
        """
        if self.coq_states:
            return self.coq_states[-1].is_proof
        else:
            return False

    @property
    def length_of_states(self):
        """A property of length_of_states
        Returns:
            int: length of self.coq_states
        """
        return len(self.coq_states)

    @property
    def valid_tactics(self):
        """valid tactics from self.coq_states
        Returns:
            list: valid tactics
        """
        if self.coq_states:
            return [e.tactic for e in self.coq_states]
        else:
            return self.chromosome

    @property
    def goal(self):
        """return goal of gene
        """
        return self.coq_states[-1].goal

    def update_fitness_for_proof(self, proof, limit_hyp, limit_goal):
        """re-evaluate fitness for a proof
        Args:
            proof (Proof): a Proof instance.
        """
        # TODO extract these two func into coqapi
        coq_script = evaluation.preprocess(proof.theorem, self.chromosome)
        run_output = evaluation.run_coqtop(coq_script)
        self.coq_states = evaluation.get_coq_states(run_output, proof,
                                                    self.chromosome)

        if self.is_proof:
            return

        self.raw_fitness = evaluation.calculate_fitness(
            coq_states=self.coq_states[proof.offset:],
            limit_hyp=limit_hyp,
            limit_goal=limit_goal)
        if len(self.chromosome) <= 20:
            n_error = 0
        else:
            n_error = len(self.chromosome) - len(self.coq_states)
        # self.fitness += 1 - (n_error / len(self.chromosome)) ** 2
        self.raw_fitness += 1 - (n_error / len(self.chromosome))
        # print(self.fitness)
        # for state in self.coq_states:
            # print(state)
        return

    def print_lastest(self):
        """print out gene
        """
        print("c_len\ts_len\tfitness")
        print(len(self.chromosome), end="\t")
        print(self.length_of_states-1, end="\t")
        print(self.fitness)
        print('\n'.join(self.valid_tactics))
        print(self.coq_states[-1])
        return

    def modification(self, data=None):
        """Modify one tactic of gene
        """
        if self.is_proof:
            return

        if data is None:
            self.print_lastest()
        while True:
            try:
                if data:
                    edit_cmd = data
                else:
                    edit_cmd = input("edit > ")
                    edit_cmd = edit_cmd.split()
            except EOFError:
                return
            try:
                if edit_cmd[0] == "state":
                    self.print_progress()
                elif edit_cmd[0] == "list":
                    for index, tactic in enumerate(self.chromosome):
                        print("{}: {}".format(index, tactic))
                elif edit_cmd[0] == "insert" or edit_cmd[0] == "replace":
                    if len(edit_cmd) < 2:
                        print("Expect a index here.")
                        continue
                    else:
                        edit_index = int(edit_cmd[1])
                        if edit_cmd[0] == "replace":
                            del self.chromosome[edit_index]
                        input_tactic = input("Please type a tactic: ")
                        self.chromosome.insert(edit_index, input_tactic)
                        break
                elif edit_cmd[0] == "append":
                    if len(edit_cmd) == 2 and edit_cmd[1]:
                        self.chromosome.append(edit_cmd[1])
                    else:
                        input_tactic = input("Please type a tactic: ")
                        self.chromosome.append(input_tactic)
                    break
                else:
                    print("state: all states")
                    print("list: print chromosome.")
                    print("insert <index>: insert a tactic before the index.")
                    print("replace <index>: replace the tactic of <index>-th.")
                    print("append: append the tactic at the end of chromosome")
            except IndexError:
                continue
        if data is None:
            print(self.chromosome)
        else:
            print("append by trigger!")

    def format_output(self, proof):
        """Prepare a formated gene output
        """
        format_string = ""
        format_string += "\n".join(proof.theorem_body)
        format_string += "\nProof.\n"
        format_string += "\n".join(["  "+e for e in self.valid_tactics[1:]])
        format_string += "\n"
        return format_string

    def print_progress(self):
        """Print all state of gene
        """
        for state in self.coq_states:
            print(state)

    def defrag(self, proof):
        """Defragment gene
        """
        new_chromosome = [] + self.valid_tactics[proof.offset:]
        i = proof.offset
        print(self.chromosome)
        for tactic in self.chromosome:
            if i < len(self.valid_tactics) and tactic == self.valid_tactics[i]:
                i += 1
                continue
            else:
                new_chromosome.append(tactic)
        self.chromosome = new_chromosome
        print(self.chromosome)
