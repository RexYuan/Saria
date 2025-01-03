
from time import time
from functools import reduce
from itertools import permutations

import graphviz as gz
import networkx as nx

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

    cnf.append([top_aux_var])  # The top auxiliary variable must be true
    return cnf

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

def connected_poset_cover(lins):
    omega = set(lins[0])
    s = Solver(name='m22')

    def get_swap(s):
        if type(s) == str:
            for i in range(len(s)-1):
                yield s[:i]+s[i+1]+s[i]+s[i+2:]
        else:
            for i in range(len(s)-1):
                yield s[:i]+(s[i+1],)+(s[i],)+s[i+2:]

    bar = list(filter( lambda l : l not in lins ,
               reduce( lambda x,y : x|y ,
               map( lambda l : set(get_swap(l)) , lins ) ) ))

    # make k posets ; worst case is size of lins
    for k in range(1, len(lins)+1):
        print('k =', k)
        s.delete()
        s = Solver(name='m22')

        # poset axioms : basic poset contraints
        for i in range(k):
            s.append_formula( poset_axioms(omega , str(i)) )

        # extension constraints : forall l, exists p, p covers l
        for l in lins:
            ands = [ le_constraints(omega, str(i), l) for i in range(k) ]
            s.append_formula(tseitin_or_and(ands))

        # non-extension constraints : forall not l, forall p, p does not cover l
        for l in bar:
            for i in range(k):
                s.add_clause( nle_constraints(omega, str(i), l) )

        if s.solve():
            cover = set()
            poset = set()
            for name in range(k):
                name = str(name)
                for x in omega:
                    for y in omega-{x}:
                        if v.id((name,x,y)) in s.get_model():
                            print((name,x,y), v.id((name,x, y)))
                            poset.add( (x,y) )
                cover.add(frozenset(poset))
                poset = set()
            break
        else:
            print('no solution for k =', k)
    return cover

def poset_cover(lins, render=True, dir='graphs'):
    omega = set(lins[0])

    start_time = time()

    def is_swap(s1, s2):
        pair = False
        i = 0
        while i < len(s1):
            if s1[i] != s2[i]:
                if i == len(s1)-1:
                    return False
                if (s1[i] == s2[i+1] and s1[i+1] == s2[i]):
                    if pair:
                        return False
                    pair = True
                    i += 1
                else:
                    return False
            i += 1
        return pair

    # generate swap graph from lins
    swap_graph = nx.Graph()
    swap_graph.add_nodes_from(lins)
    for i,l1 in enumerate(lins):
        for l2 in lins[i+1:]:
            if is_swap(l1, l2):
                swap_graph.add_edge(l1, l2)

    # render swap graph
    if render:
        g = gz.Graph('G', filename=dir+'/swap_graph', format='pdf')
        g.attr(rankdir='LR')
        # if type(lins[0]) == str:
        #     g.attr(label='[ '+' '.join(lins)+' ]')
        # else:
        #     g.attr(label='[ '+' '.join(map(lambda t : '-'.join(t) , lins))+' ]')
        # render components as clusters
        for i, comp in enumerate(nx.connected_components(swap_graph)):
            comp = swap_graph.subgraph(comp)
            nodes, edges = list(comp.nodes), list(comp.edges)
            if type(nodes[0]) != str:
                nodes = list(map(lambda t : '-'.join(t), nodes))
                edges = list(map(lambda p : ('-'.join(p[0]), '-'.join(p[1])), edges))
            # copy information from networkx to graphviz
            with g.subgraph(name='cluster_'+str(i+1)) as c:
                # c.attr(label='Component '+str(i+1))
                for n in nodes:
                    c.node(n)
                c.edges(edges)
        g.render()

    # divide & conquer on connected components
    component_covers = []
    for i, comp in enumerate(nx.connected_components(swap_graph)):
        comp = swap_graph.subgraph(comp)
        lins = list(comp.nodes)

        # find poset cover(s) for each and every components
        covers = connected_poset_cover(lins)

        # well shit
        if covers == None:
            continue
        else:
            component_covers.append( (lins, covers) )

        def rm_trans_closure(uni, rs):
            crels = set()
            for x,y in rs:
                cover = True
                for z in uni:
                    if (x,z) in rs and (z,y) in rs:
                        cover = False
                if cover:
                    crels.add( (x,y) )
            return crels

        # render cover
        if render:
            for j, cover in enumerate([covers]):
                g = gz.Digraph('G', filename=dir+'/comp_'+str(i+1)+'_cover_'+str(j+1), format='pdf')
                # g.attr(label='Cover '+str(j+1)+' for component '+str(i+1))
                # render posets as clusters
                for k, poset in enumerate(cover):
                    with g.subgraph(name='cluster_'+str(k+1)) as c:
                        # c.attr(label='Poset '+str(k+1))
                        for x,y in rm_trans_closure(omega, poset):
                            c.node('P'+str(k+1)+'_'+x, x)
                            c.node('P'+str(k+1)+'_'+y, y)
                            c.edge('P'+str(k+1)+'_'+x,'P'+str(k+1)+'_'+y)
                g.render()

    if covers:
        print("Solution found")
        print(f"All done! Total time = {round(time()-start_time,4)}")
    else:
        print(f"Failed! Total time = {round(time()-start_time,4)}")

    return covers

poset_cover(['abc', 'acb', 'bac'])
