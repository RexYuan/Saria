import graphviz as gz
import networkx as nx

from z3 import *
from functools import reduce
from graphviz import Digraph

from poset_cover import poset_axioms, le_constraints
from poset_cover import TAUTO, CONTRA
from poset_cover import rm_trans_closure

def torder_to_string(universe, rs):
    '''
    rs : order as a set of 2-tuples

    return the string form of total order
    '''
    omega = set(universe)
    xs = reduce( lambda x,y : set(x)|set(y) , rs )
    elem_tab = {x: 0 for x in xs}

    # the order of elements is the same as the their
    # number of occurances in the first position
    for r in rs:
        x = r[0]
        # keep count of their occurances in the first position
        elem_tab[x] += 1

    # sort by their occurance in descending order and
    # concat them as a string
    ret = ''.join(map( lambda p : str(p[0]),
                       sorted(elem_tab.items(),
                              key= lambda p : p[1] , reverse=True)))
    return ret

def partial_cover(lins, l):
    '''
    maximal partial cover containing l for lins
    '''
    omega = set(lins[0])
    s = Solver()

    # to make relation
    def rel(x, y):
        return Bool('P'+'_'+x+'<'+y)

    # to generate swaps
    def get_swap(s):
        if type(s) == str:
            for i in range(len(s)-1):
                yield s[:i]+s[i+1]+s[i]+s[i+2:]
        else:
            for i in range(len(s)-1):
                yield s[:i]+(s[i+1],)+(s[i],)+s[i+2:]

    # if s1 s2 are off by one swap
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

    # ignore components not including l
    for i, comp in enumerate(nx.connected_components(swap_graph)):
        comp = swap_graph.subgraph(comp)
        ls = list(comp.nodes)
        if l not in ls:
            continue

        # find the insulating barrier
        bar = list(filter( lambda l : l not in ls ,
                   reduce( lambda x,y : x|y ,
                   map( lambda l : set(get_swap(l)) , ls ) ) ))

        # make poset
        s.add( simplify(poset_axioms(omega , '')) )

        # extension constraints : at least l is covered
        s.add( simplify(le_constraints(omega , '' , l)) )

        # non-extension constraints
        for l in bar:
            s.add( simplify(Not(le_constraints(omega , '' , l))) )

        # candidates
        posets = set()
        poset = set()
        # size of smallest poset yet
        k = float("inf")

        # get all blanketing posets
        result = s.check()
        while result == sat:
            m = s.model()
            counter = TAUTO

            # collect example
            for x in omega:
                for y in omega-{x}:
                    if m[ rel(x, y) ]:
                        poset.add( (x,y) )
                        counter = And( counter , rel(x, y) )
                    else:
                        counter = And( counter , Not(rel(x, y)) )

            # update if it's smaller
            if len(poset) < k:
                posets = {frozenset(poset)}
                k = len(poset)
            # include if it's as small
            elif len(poset) == k:
                posets.add(frozenset(poset))
            poset = set()

            # force this example to false
            s.add( simplify(Not(counter)) )
            result = s.check()

        # return all the minimum posets
        return posets

def get_linearizations(universe, rs):
    '''
    rs : order as a set of 2-tuples

    return all linearizations of rs
    '''
    omega = set(universe)
    s = Solver()

    # to make relation
    def rel(x, y):
        return Bool('P'+'_'+x+'<'+y)

    # make poset
    s.add( simplify(poset_axioms(omega , '', total=True)) )

    # force base poset
    for r in rs:
        s.add( rel(*r) )

    # linear orders
    lins = set()
    lin = set()

    # solve all linear orders
    result = s.check()
    while result == sat:
        m = s.model()
        counter = TAUTO

        # collect example
        for x in omega:
            for y in omega-{x}:
                if m[ rel(x, y) ]:
                    lin.add( (x,y) )
                    counter = And( counter , rel(x, y) )
                else:
                    counter = And( counter , Not(rel(x, y)) )
        lins.add(frozenset(lin))
        lin = set()

        # force this example to false
        s.add( simplify(Not(counter)) )
        result = s.check()

    # return all the minimum posets
    return list(map(lambda l : torder_to_string(omega, l), lins))

def cover_overlap(universe, cover):
    '''
    if linearizations generated by this cover overlap
    '''
    seen = []
    for poset in cover:
        tmp = set(get_linearizations(universe, poset))
        if seen == []:
            seen.append(tmp)
            continue
        for saw in seen:
            if tmp & saw != set():
                return (tmp & saw)
        seen.append(tmp)
    return False

# example
'''
lins = [
'13245',
'12345',
'21345',
'23145',
'32145',
'13254',
'12354',
'21354',
'23154',
'32154',
'31245'
]
lins = list(map(str, lins))
rets = partial_cover(lins, '12345')
for ret in rets:
    print(frozenset(rm_trans_closure(set('12345'), ret)))
    print(get_linearizations('12345',ret))

print()

ans = frozenset({
('1','4'),
('1','5'),
('2','3'),
('3','4'),
('3','5')
})
print(ans)
print(get_linearizations('12345',ans))
'''
'''
l = 'abfced'
ls = [
'afbced',
'afbecd',
'abfecd',
'abfced',
'bfaced',
'bafced',
'bacfed',
'abcfed',
'abcefd',
'bacefd'
]
rets = partial_cover(ls, l)
x = []
for i,ret in enumerate(rets):
    #print(frozenset(rm_trans_closure(set('abcdef'), ret)))
    print('poset',i)
    print(set(ret))
    x.append(set(ret))
    #print(get_linearizations('abcdef',ret))
    print()
'''
