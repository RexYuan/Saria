

from pysat.formula import *
from pysat.solvers import Solver

v = Formula.export_vpool()

def tseitin_or_and(and_groups):
    cnf = []
    or_auxiliary_vars = []  # To collect auxiliary variables representing OR terms

    for and_group in and_groups:
        # Create an auxiliary variable for this AND group
        and_aux_var = v.id()
        and_clauses = []

        # Each AND group must be true if the auxiliary variable is true
        for literal in and_group:
            clause = [literal] + [-and_aux_var]
            cnf.append(clause)  # Literal implies auxiliary variable
            and_clauses.append(-literal)

        # The auxiliary variable implies the AND of the literals
        cnf.append(and_clauses + [and_aux_var])

        # Collect the auxiliary variable for the OR term
        or_auxiliary_vars.append(and_aux_var)

    or_clause = []
    top_aux_var = v.id()
    for or_auxiliary_var in or_auxiliary_vars:
        clause = [-or_auxiliary_var] + [top_aux_var]
        cnf.append(clause)
        or_clause.append(or_auxiliary_var)
    cnf.append(or_clause + [-top_aux_var])

    return cnf, top_aux_var

# formula = [
#     [[v.id()], [v.id()]],
#     [[v.id()], [v.id()]]
# ]

# cnf_clauses, or_var = tseitin_or_and(formula)

# print("CNF Clauses:")
# print(cnf_clauses)
# for clause in cnf_clauses:
#     print(clause)
# print("OR variable:", or_var)

def poset_axioms(universe, name, total=False):
    constraints = []
    omega = set(universe)

    for x in omega:
        for y in omega-{x}:
            # forall x!=y, -(x<y & y<x)
            constraints.append( [-v.id((name,x,y)),-v.id((name,y,x))] )

            for z in omega-{x,y}:
                # forall x!=y!=z, (x<y & y<z) => x<z
                constraints.append( [-v.id((name,x,y)),-v.id((name,y,z)),v.id((name,x,z))] )
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
        constraints.append( -v.id((name,*r)) )
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
        constraints.append( v.id((name,*r)) )
    return constraints

a = poset_axioms(set('ab'), '1')
b = poset_axioms(set('ab'), '2')

l1 = le_constraints(set('ab'), '1', 'ab')
l2 = le_constraints(set('ab'), '1', 'ba')

l3=le_constraints(set('ab'), '2', 'ab')
l4=le_constraints(set('ab'), '2', 'ba')

s = Solver(name='m22')
s.append_formula(a)
s.append_formula(b)

f1 = [l1,l3]
cnf_clauses, or_var = tseitin_or_and(f1)
s.append_formula(cnf_clauses)
s.add_clause([or_var])

f1 = [l2,l4]
cnf_clauses, or_var = tseitin_or_and(f1)
s.append_formula(cnf_clauses)
s.add_clause([or_var])

# s.add_clause(nle_constraints(set('abc'), '1', 'bac'))
# s.add_clause(nle_constraints(set('abc'), '1', 'bca'))
# s.add_clause(nle_constraints(set('abc'), '1', 'cab'))
# s.add_clause(nle_constraints(set('abc'), '1', 'cba'))

# s.add_clause(nle_constraints(set('abc'), '2', 'bac'))
# s.add_clause(nle_constraints(set('abc'), '2', 'bca'))
# s.add_clause(nle_constraints(set('abc'), '2', 'cab'))
# s.add_clause(nle_constraints(set('abc'), '2', 'cba'))

print(s.solve())
print(s.get_model())

omega = set('abc')
for name in ['1', '2']:
    for x in omega:
        for y in omega-{x}:
            # print((x,y), v.id((x, y)))
            if v.id((name,x,y)) in s.get_model():
                print((name,x,y), v.id((name,x, y)))
