

from pysat.formula import *
from pysat.solvers import Solver

v = Formula.export_vpool()

def tseitin_or_and_or(formula):
    """
    Perform Tseitin transformation for a formula with AND groups of OR clauses.

    Formula is given as a list of AND groups, each containing OR clauses.
    Args:
        formula (list): The input formula, consisting of multiple AND groups of ORs.
    Returns:
        tuple: CNF clauses and the updated variable counter.
    """
    clauses = []
    and_group_vars = []  # To store the auxiliary variables for each AND group

    # Step 1: Encode each OR group with an auxiliary variable
    for and_group in formula:
        and_group_vars_in_group = []

        # Encode each OR group in the AND group
        for or_group in and_group:
            # Generate a new variable for this OR group
            group_var = v.id()
            and_group_vars_in_group.append(group_var)

            # Flatten the literals in the OR group
            group_literals = or_group

            # Encode the OR group as a set of clauses
            clauses.append([-group_var] + group_literals)  # (-group_var OR all literals)
            for literal in group_literals:
                clauses.append([group_var, -literal])  # (group_var OR -literal)

        # Step 2: Combine the OR groups in the AND group with a new AND auxiliary variable
        and_group_var = v.id()
        and_group_vars.append(and_group_var)

        # Add clause to combine the OR groups using AND (i.e., a new variable for the AND)
        and_group_clause = [and_group_var]
        for group_var in and_group_vars_in_group:
            and_group_clause.append(group_var)
        clauses.append(and_group_clause)

    # Step 3: Combine the AND groups using an OR operation
    or_var = v.id()
    for and_group_var in and_group_vars:
        clauses.append([-or_var] + [and_group_var])  # (-or_var OR each AND group variable)
    for and_group_var in and_group_vars:
        clauses.append([or_var, -and_group_var])  # (or_var OR -each AND group variable)

    return clauses, or_var

# Example input formula: ((x1|x2)&(x3|x4)) | ((x5|x6)&(x7|x8))
formula = [
    [[v.id(), v.id()], [v.id(), v.id()]],  # ((x1 OR x2) AND (x3 OR x4))
    [[v.id(), v.id()], [v.id(), v.id()]]   # ((x5 OR x6) AND (x7 OR x8))
]

# Tseitin encoding
cnf_clauses, or_var = tseitin_or_and_or(formula)

print("CNF Clauses:")
# print(cnf_clauses)
for clause in cnf_clauses:
    print(clause)
print("OR variable:", or_var)

def poset_axioms(universe, name, total=False):
    constraints = []
    omega = set(universe)

    for x in omega:
        for y in omega-{x}:
            # forall x!=y, -(x<y & y<x)
            constraints.append( [-v.id((x,y)),-v.id((y,x))] )

            for z in omega-{x,y}:
                # forall x!=y!=z, (x<y & y<z) => x<z
                constraints.append( [-v.id((x,y)),-v.id((y,z)),v.id((x,z))] )
    return constraints

def le_constraints(universe, name, lin):
    constraints = []
    omega = set(universe)

    ords = set()
    # cartesian set
    for x in omega:
        for y in omega-{x}:
            ords.add( (x,y) )

    for i,x in enumerate(lin):
        for y in lin[i+1:]:
            try:
                ords.remove( (x,y) )
            except:
                pass

    # build constraints on name : forall r not in <lin>, r not in <name>
    for r in ords:
        constraints.append( [-v.id(r)] )
    return constraints

def nle_constraints(universe, name, lin):
    constraints = []
    omega = set(universe)

    ords = set()
    # cartesian set
    for x in omega:
        for y in omega-{x}:
            ords.add( (x,y) )

    for i,x in enumerate(lin):
        for y in lin[i+1:]:
            try:
                ords.remove( (x,y) )
            except:
                pass

    # build constraints on name : forall r not in <lin>, r not in <name>
    for r in ords:
        constraints.append( v.id(r) )
    return constraints

a = poset_axioms(set('abc'), '1')
# print(a)
l = le_constraints(set('abc'), '1', 'abc')
# print(l)
l2 = le_constraints(set('abc'), '1', 'acb')
# print(l2)

s = Solver(name='m22')
s.append_formula(a)
s.append_formula(l)
s.append_formula(l2)

s.add_clause(nle_constraints(set('abc'), '1', 'bac'))
s.add_clause(nle_constraints(set('abc'), '1', 'bca'))
s.add_clause(nle_constraints(set('abc'), '1', 'cab'))
s.add_clause(nle_constraints(set('abc'), '1', 'cba'))

# print(s.solve())
# print(s.get_model())

# omega = set('abc')
# # poset = set()
# for x in omega:
#     for y in omega-{x}:
#         # print((x,y), v.id((x, y)))
#         if v.id((x,y)) in s.get_model():
            # print((x,y), v.id((x, y)))
            # poset.add( (x,y) )
