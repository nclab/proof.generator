#!/usr/bin/env python3
"""Autoprover
"""

import pickle
from autoprover.proof import Proof
from autoprover.utils import parser
from autoprover.utils.tactic import TacticsSet
from autoprover.utils.log import reg_logger
from autoprover.gp.model import GPModel

HELP_MESSAGE = """help(h): Print help message.
next(n) <step>: Start n generation.
show-property(show-prop): Show property of GP model.
edit(e): Edit best gene.
list(l): List some property of population.
show-proofs(sp): Show proofs which is found.
"""

def main():
    """Main program
    """
    reg_logger()
    args = parser.get_args()
    tactics = TacticsSet(args.tacticBase)
    proof = Proof(input_file=args.file, tactics=tactics)

    gp_model = GPModel(args=args, proof=proof, tactics=tactics)
    while True:
        try:
            input_string = input(proof.theorem_name + " > ")
        except EOFError:
            break

        input_list = input_string.split(" ")
        if input_list[0] == "h" or input_list[0] == "help":
            print(HELP_MESSAGE)
        elif input_list[0] == "show-property" or input_list[0] == "show-prop":
            gp_model.show_prop()
        elif input_list[0] == "show-proof" or input_list[0] == "sp":
            gp_model.show_proofs()
        elif input_list[0] == "n" or input_list[0] == "next":
            if input_list[1]:
                step = int(input_list[1])
                gp_model.start(gen=step)
        elif input_list[0] == "defrag":
            try:
                index = int(input_list[1])
            except IndexError:
                print("Invaild command")
            gp_model.defrag(index_list=[index])
        elif input_list[0] == "edit" or input_list[0] == "e":
            try:
                index = input_list[1]
                gp_model.edit(index=int(index))
            except IndexError:
                gp_model.edit(index=0)
        elif input_list[0] == "list" or input_list[0] == "l":
            sub_cmd = input_list[1:]
            gp_model.list(sub_cmd)
        elif input_list[0] == "set" or input_list[0] == "s":
            sub_cmd = input_list[1:]
            try:
                gp_model.set_attributes(sub_cmd)
            except IndexError:
                continue
        elif input_list[0] == "stats":
            gp_model.print_stats()
        elif input_list[0] == "save":
            if len(input_list) < 2:
                continue
            out_file = open(input_list[1], "wb")
            pickle.dump(gp_model.population, out_file, protocol=pickle.HIGHEST_PROTOCOL)
            out_file.close()
        elif input_list[0] == "load":
            if len(input_list) < 2:
                continue
            in_file = open(input_list[1], "rb")
            gp_model.population = pickle.load(in_file)
            in_file.close()
        elif input_list[0] == "read" or input_list[0] == "r":
            if len(input_list) < 2:
                continue
            gp_model.read_rule_from_file(input_list[1])
        elif input_list[0] in ["del", "d"]:
            if len(input_list) < 2:
                continue
            gp_model.delete_rule(int(input_list[1]))
        elif input_list[0] in ["remove", "rm"]:
            gp_model.remove_tactic()
        else:
            print("Invaild command")


if __name__ == "__main__":
    main()
