"""
regist a argparse
"""
import sys
import argparse

def get_args():
    """
    get argument from command line
    """
    parser = argparse.ArgumentParser(description='Autoprover')
    parser.add_argument("file", type=open, help="a theorem to be proved")
    parser.add_argument(
        "-o", "--output", dest='outputFile',
        type=argparse.FileType('w'), default=sys.stdout,
        help="a file your proof to be stored, default is stdout.")
    parser.add_argument(
        "-b", "--tactic-base", dest='tacticBase',
        type=open, default='tactic_base',
        help="a tactic base file")
    parser.add_argument(
        "-p", "--population-size", dest='populationSize',
        type=int, default=500,
        help="the population size, default is 1000")
    parser.add_argument(
        "-g", "--max-generation", dest='maxGeneration',
        type=int, default=1000,
        help="a maximun generation, defalut is 100")
    parser.add_argument(
        "-m", "--mutate-rate", dest='mutateRate',
        type=float, default=0.25,
        help="a mutate rate in interval (0, 1), default is 0.25")
    parser.add_argument(
        "-e", "--elite-rate", dest='eliteRate',
        type=float, default=0,
        help="the percentage of elitism, default is 0")
    parser.add_argument(
        "-c", "--cross-rate", dest='crossRate',
        type=float, default=0.5,
        help="a cross rate, defalut is 0.5")
    parser.add_argument(
        "-t", "--cross-type", dest='crossType',
        type=int, default=0,
        help="different type of cross, default is 0")
    parser.add_argument(
        "-n", "--verify-num", dest='verifyNum',
        type=int, default=50,
        help="number of top proofs to be verified in each generation\
        , default is 50")
    parser.add_argument(
        "--limit-hyp", dest='limit_hyp',
        type=int, default=100,
        help="default=100")
    parser.add_argument(
        "--limit-goal", dest='limit_goal',
        type=int, default=300,
        help="default=300")
    parser.add_argument("--debug", dest='debug', action='store_true')
    parser.add_argument(
        "--brute-force", dest='bruteForce', action='store_true')
    args = parser.parse_args()
    return args
