import graphviz as gz
import networkx as nx

# from pysat.formula import *
# from pysat.solvers import Solver

import logging

from functools import reduce
from itertools import permutations
from collections import deque
from math import factorial
from time import time

# v = Formula.export_vpool()

def tseitin(f):
    curr = []
    match f:
        case Atom():
            return curr
        case Neg():
            curr += tseitin(f.subformula)
            curr += [[v.id(f), v.id(f.subformula)], [-v.id(f), -v.id(f.subformula)]]
            return curr
        case Implies():
            curr += tseitin(f.left)
            curr += tseitin(f.right)
            curr += [[v.id(f), -v.id(f.left)], [v.id(f), -v.id(f.right)], [-v.id(f), -v.id(f.left), v.id(f.right)]]
            return curr
        case And():
            for sf in f.subformulas:
                curr += tseitin(sf)
            curr += [[-v.id(f), v.id(sf)] for sf in f.subformulas] + [[v.id(f)] + [-v.id(sf) for sf in f.subformulas]]
            return curr
        case Or():
            for sf in f.subformulas:
                curr += tseitin(sf)
            curr += [[v.id(f), -v.id(sf)] for sf in f.subformulas] + [[-v.id(f)] + [v.id(sf) for sf in f.subformulas]]
            return curr

# x1, x2, x3, x4, x5, x6, x7, x8 = Atom('1'), Atom('2'), Atom('3'), Atom('4'), Atom('5'), Atom('6'), Atom('7'), Atom('8')
# vars = [x1, x2, x3, x4, x5, x6, x7, x8]
# for var in vars:
#     print(v.id(var))
# f = ((x1 | x2) & (x3 | x4)) | ((x5 | x6) & (x7 | x8))
# # print(tseitin(f))
# for c in tseitin(f):
#     print(c)

from pysat.solvers import Glucose3

# Function to check if two formulas (lists of clauses) are logically equivalent
def are_logically_equivalent(cnf1, cnf2):
    # Step 1: Create the equivalence formula
    # Formula1 -> Formula2
    equivalence_cnf = []

    # (Formula1 -> Formula2): this is simply Formula1 OR (NOT Formula2)
    # We negate all clauses in Formula2 and combine with Formula1
    for clause1 in cnf1:
        equivalence_cnf.append(clause1)
    for clause2 in cnf2:
        equivalence_cnf.append([-lit for lit in clause2])

    # (Formula2 -> Formula1): this is simply Formula2 OR (NOT Formula1)
    # We negate all clauses in Formula1 and combine with Formula2
    for clause2 in cnf2:
        equivalence_cnf.append(clause2)
    for clause1 in cnf1:
        equivalence_cnf.append([-lit for lit in clause1])

    # Step 2: Check satisfiability using SAT solver
    with Glucose3() as solver:
        for clause in equivalence_cnf:
            solver.add_clause(clause)
        result = solver.solve()

    # If SAT solver returns 'unsat', the formulas are logically equivalent
    return not result

# Example formulas (list of lists of clauses)
# Formula 1: ((x1 OR x2) AND (x3 OR x4)) OR ((x5 OR x6) AND (x7 OR x8))
# chatgpt magic
cnf1 = [
[9, -1],
[9, -2],
[-9, 1, 2],
[10, -3],
[10, -4],
[-10, 3, 4],
[11, 9, 10],
[-12, 5, 6],
[12, -5],
[12, -6],
[-13, 7, 8],
[13, -7],
[13, -8],
[14, 12, 13],
[-15, 11],
[-15, 14],
[15, -11],
[15, -14],
]

# Formula 2: ((x1 OR x2) AND (x3 OR x4)) OR ((x5 OR x6) AND (x7 OR x8))
# my encoding
cnf2 = [
[9, -1],
[9, -2],
[-9, 1, 2],
[10, -3],
[10, -4],
[-10, 3, 4],
[-11, 9],
[-11, 10],
[11, -9, -10],
[12, -5],
[12, -6],
[-12, 5, 6],
[13, -7],
[13, -8],
[-13, 7, 8],
[-14, 12],
[-14, 13],
[14, -12, -13],
[15, -11],
[15, -14],
[-15, 11, 14],
]

# Check if formula1 and formula2 are logically equivalent
# if are_logically_equivalent(cnf1, cnf2):
#     print("The formulas are logically equivalent.")
# else:
#     print("The formulas are not logically equivalent.")

from z3 import *
s = Solver()

a1, a2, a3, a4, a5, a6, a7, a8 = Bool('a1'), Bool('a2'), Bool('a3'), Bool('a4'), Bool('a5'), Bool('a6'), Bool('a7'), Bool('a8')
a9, a10, a11, a12, a13, a14, a15 = Bool('a9'), Bool('a10'), Bool('a11'), Bool('a12'), Bool('a13'), Bool('a14'), Bool('a15')

correct = BoolVal(True)
for clause in cnf2:
    c = BoolVal(False)
    for lit in clause:
        if lit > 0:
            c = Or(c, Bool(f'a{lit}'))
        else:
            c = Or(c, Not(Bool(f'a{-lit}')))
    correct = simplify(And(correct, c))

test = BoolVal(True)
for clause in cnf1:
    c = BoolVal(False)
    for lit in clause:
        if lit > 0:
            c = Or(c, Bool(f'a{lit}'))
        else:
            c = Or(c, Not(Bool(f'a{-lit}')))
    test = simplify(And(correct, c))

s.add( Not(correct == test) )

# # s.add( Not(g) )
print(s.check())
# m = s.model()
# # print(m[a], m[b], m[c], m[d], m[e], m[f], m[g])
