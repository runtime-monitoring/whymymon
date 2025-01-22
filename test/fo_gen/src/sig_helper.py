import random
import re
from src.operators import *

class Sig:
    def __init__(self, predicates):
        self.predicates = predicates
        self.prednames = [pred.predicate for pred in predicates]
        self.len = len(predicates)
        self.max_arity = max([args.len for args in predicates])
        self.min_arity = min([args.len for args in predicates])

    def __2str__(self):
        predi = []
        for pred in self.predicates:
            if pred.len > 0:
                predi.append(f"{pred.name}({', '.join(pred.variables)})")
            else:
                predi.append(f"{pred.name}()")
        return "\n".join(predi)

    def __repr__(self):
        return str(self)

    def __add__(self, other):
        predicates = {**self.predicates, **other.predicates}
        return Sig(predicates)


def generate_signature(num_predicates, max_arity, seed, nozero=False): # ):
    """
    Generate a random signature as a dictionary
    Arguments are of type int.
    """
    rng = random.Random()
    rng.seed(seed)
    predicates = {}
    if nozero:
        min_arity = 1
    else:
        min_arity = 0
    for i in range(num_predicates):
        # Create predicate name of P0, P1,...
        predicate_name = f"P{i}"

        # number of arguments
        arity = rng.randint(min_arity, max_arity)

        # arguments list
        if arity > 0:
            predicates[predicate_name] = ["x:int" for _ in range(arity)]
        else:
            predicates[predicate_name] = []
    return predicates, Sig([Pred(pred, args) for pred, args in predicates.items()])

def sig2str(sig):
    """Convert signature to string"""
    predicates = []
    for pred, args in sig.items():
        if args:
            predicates.append(f"{pred}({', '.join(args)})")
        else:
            predicates.append(f"{pred}()")
    return "\n".join(predicates)

def f2sig(file):
    """Convert signature file to signature"""
    sig = {}
    with open(file, "r") as f:
        content = f.read()

    pattern = re.compile(r'(\w+)\(([^)]*)\)')
    matches = pattern.findall(content)

    for name, args in matches:
        args_list = [arg.strip() for arg in args.split(',')] if args.strip() else []

        sig[name] = args_list
    return sig, Sig([Pred(pred, args) for pred, args in sig.items()])
