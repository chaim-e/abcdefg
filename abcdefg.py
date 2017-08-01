print "Automated Business of Chord Diagram Expectations For Grids (ABCDEFG)"

# tested with python 2.7.5+, numpy 1.7.1 (?)

import itertools
from numpy.lib.polynomial import *
from fractions import *
from math import factorial

all = __builtins__.all
any = __builtins__.any
sum = __builtins__.sum

#===============================================================================
#
#   Chord diagrams
#

class CD:
    """
    chord diagram
    """

    def __init__(self, tips, weights = 1, coef = 1):
        """
        tips        list of integers/letters, each appears twice
        weights     dictionary, chord to weight
        coef        number
        """        
        self.tips = list(tips)
        self.weights = {x:weights for x in tips} if type(weights) == int else weights
        self.coef = coef
        self.chords = sorted(list(set(tips)))
        assert all([tips.count(chord) == 2 for chord in self.chords])
        self.locs = {ch:(tips.index(ch), tips.index(ch, tips.index(ch)+1))
                     for ch in self.chords}
        
    def __repr__(self):
        w = ','.join(['%s:%s'%(x,y) for x,y in self.weights.items() if y!=1])
        return '%s*[%s%s]' % (self.coef, ''.join(map(str,self.tips)), '|%s'%w if w else '')

    def expectation(self, *args, **kargs):
        return exp_cd(self, *args, **kargs)


class CDF:
    """
    chord diagram formula
    """

    def __init__(self, *args, **kargs):
        if isinstance(args[0], CD):
            self.cds = args
        elif isinstance(args[0], list):
            self.cds = args[0]
        else:
            self.cds = [CD(*args, **kargs)]

    def __repr__(self):
        return ' + '.join(['%s' % cd for cd in self.cds]) if len(self.cds) else '0*[]'

    def __add__(self, other):
        return CDF(collect_cds(self.cds + other.cds))

    def __mul__(self, other):
        cds = reduce(lambda x,y:x+y,
                     [list(merge_cds(a,b)) for a in self.cds for b in other.cds],
                     [])
        return CDF(collect_cds(cds))

    def __rmul__(self, num):
        return CDF(collect_cds([CD(cd.tips,cd.weights,num*cd.coef) for cd in self.cds]))

    def __neg__(self):
        return (-1) * self

    def __sub__(self, other):
        return self + (-other)

    def __pow__(self, exponent):
        return reduce(lambda x,y:x*y, [self]*exponent)

    def expectation(self, *args, **kargs):
        exps = [cd.expectation(*args, **kargs) for cd in self.cds]
        exps = [x for x in exps if poly1d(x) != poly1d(0)]
        return reduce(polyadd, exps) if exps else Fraction(0)


class Expectator:
    """
    self[other] returns other.expectation()
    """                 
    def __getitem__(self, cdf):
        return cdf.expectation()

E = Expectator()

   
def merge_cds(cd1, cd2, new_names = 'abcdefgh'):
    cd1.weights[None] = cd2.weights[None] = 0
    for tips in merger(cd1.tips, cd2.tips):
        weights = {(t1,t2):cd1.weights[t1]+cd2.weights[t2] for t1,t2 in tips}
        coef = cd1.coef*cd2.coef
        if new_names:
            d = {tips[y]:x for x,y in zip(new_names,sorted(map(tips.index,set(tips))))}
            tips = [d[tip] for tip in tips]
            weights = {d[tip]:val for tip,val in weights.items()}
        yield CD(tips, weights, coef)
    for cd in [cd1,cd2]:
        if None in cd.weights:
            del cd.weights[None]

def collect_cds(cds):
    d = {}
    for cd in cds:
        k = (tuple(cd.tips), tuple(cd.weights.items()))
        d[k] = d.get(k,0) + cd.coef
    return [CD(list(tips), dict(weights), coef)
            for (tips, weights), coef in d.items() if coef != 0]

#===============================================================================
#
#   Iterators etc.
#

def merger(list1, list2):
    if not list1 and not list2:
        yield []
    if list1:
        for m in merger(list1[1:],list2):
            if dict(m).get(list1[0], None) == None:
                yield [(list1[0], None)] + m
    if list2:
        for m in merger(list1,list2[1:]):
            if dict(map(reversed,m)).get(list2[0], None) == None:
                yield [(None, list2[0])] + m
    if list1 and list2:
        for m in merger(list1[1:],list2[1:]):
            if dict(m).get(list1[0], list2[0]) == list2[0] and \
               dict(map(reversed,m)).get(list2[0], list1[0]) == list1[0]:
                yield [(list1[0], list2[0])] + m

def perms(items):
    if len(items) == 1:
        yield items
    for item in items[:]:
        items.remove(item)
        for perm in perms(items):
            yield [item] + perm
        items.append(item)

def runs(seq):
    fr,to = 0,0
    for new in seq:
        if fr < to and new != item:
            yield fr,to,item
            fr = to
        to += 1
        item = new
    if fr < to:
        yield fr,to,item

def connected_components(vertices, relation):
    todo = set(vertices)
    while todo:
        check = set([todo.pop()])
        comp = []
        while check:
            v = check.pop()
            comp.append(v)
            for u in set(todo):
                if relation(u,v):
                    check.add(u)
                    todo.remove(u)
        yield comp


#===============================================================================
#
#   Expectations
#

def monotone(a, up = 1, down = -1):
    if all([x<y for x,y in zip(a,a[1:])]):
        return up
    if all([x>y for x,y in zip(a,a[1:])]):
        return down
    return 0


def canonical(arcs):
    """
    this function can be ignored, i.e., replaced by "lambda x:(x,1)"
    it generates arcs problems that are equivalent, and picks a canonical one
    """
    minimum = None
    for s in perms(list(arcs)):
        for r in itertools.product([1,-1], repeat = len(s)):
            old = reduce(lambda a,b:a+b, [arc[::rr] for (arc,up,down),rr in zip(s,r)])
            names = {old[y]:x for x,y in zip(range(len(old)),sorted(map(old.index,set(old))))}
            arcs = [tuple([names[x] for x in arc[::rr]]) for (arc,up,down),rr in zip(s,r)]
            updowns = [(up, down)[::rr] for (arc,up,down),rr in zip(s,r)]
            signs = [-1 if down > up else 1 for up,down in updowns]
            updowns = [(up*sign, down*sign) for (up,down),sign in zip(updowns,signs)]
            coef = reduce(lambda x,y:x*y, signs)
            new = tuple([(arc,up,down) for arc,(up,down) in zip(arcs, updowns)]), coef
            if new < minimum or minimum == None:
                minimum = new                
    return minimum


def exp_monotone(arcs, cache = {}, allperms = {}):
    """
    arcs = ((arc,up,down),(arc,up,down),...) where arc = (x0,x1,...)
    return expected value of the product over arcs of:
        up      if p[x0] < p[x1] < ...
        down    if p[x0] > p[x1] > ...
        0       otherwise
    """
    canon,coef = canonical(arcs)
    if canon in cache:
        return cache[canon] * coef
    
    vals = list(set(reduce(lambda x,y:x+y, [x[0] for x in canon])))
    vals = {x:y for x,y in zip(vals, range(len(vals)))}
    expect = 0
    for perm in perms(range(len(vals))):    
        expect += reduce(lambda x,y:x*y,
                         [monotone([perm[vals[v]] for v in arc], up, down)
                          for arc,up,down in canon])
    res = Fraction(expect, factorial(len(vals)))

    cache[canon] = res
    return res * coef


def exp_cd(cd, neglect = 0, basepoint = 0):
    """
    compute expectation as a polynomial in parameter n.
    terms of lower order than n^(neglect) are not important
    basepoint in [0, None, long] resp. for [leftmost, random, two-sides]
    """
    coefs = {}
    nsegs = len(cd.tips)+1
    slices = [slice(cd.locs[ch][0]+1,cd.locs[ch][1]+1) for ch in cd.chords]
    cross = {a:b for x,y in cd.locs.values() for a,b in [(x,y),(y,x)]}
    for turns in itertools.product([0,1,2,3,4], repeat = nsegs):        
        if turns[-1] == 0:
            continue        # base point is a corner => there is > 1 turn after last segment 
        if basepoint in [0,long] and turns[0]==0:
            continue        # no crossing on first segment if it is on the boundary
        bins = turns.count(3)+turns.count(4)
        if bins <= neglect:
            continue        # we don't care about terms that are O(n^k) for k < neglect
        total = sum(turns)
        if total % 2:
            continue        # there is an even number of segments, n vertical and n horizontal
        dists = [sum(turns[s]) for s in slices]
        if not all([x % 2 for x in dists]):
            continue        # a crossing is always between vertical and horizontal segments
        if any([x == 1 or total-x == 1 for x in dists]):
            continue        # no crossings between adjacent segments
        if any([min(turns[i:i+2]) >= 3 and cd.weights[cd.tips[i]] % 2 == 1 for i in range(len(cd.tips))]):
            continue        # segment has reflection symmetry => expectation of crossing is zero

        # prepare arcs = sequences whose monotonicity is required for crossing
        segs = [sum(turns[:i]) for i in range(1,nsegs)]
        #print segs,cd.tips,cd.weights
        if any([cd.weights[ch]/10%10 and (segs[fr]%2,segs[to]%2) != (0,1) or
                cd.weights[ch]/100%10 and (segs[fr]%2,segs[to]%2) != (1,0) for ch,(fr,to) in cd.locs.items()]):
            #print 'out'
            continue        # patch for grid diagrams weights 11=acsending 101=descending
        arcs = []
        for fr,to,seg in runs(segs):
            arc = tuple([(seg-1)%total] + [segs[cross[x]] for x in range(fr,to)] + [(seg+1)%total])
            up = 1
            down = (-1)**sum([cd.weights[cd.tips[x]] for x in range(fr,to)])
            if basepoint in [0,long] and arc[0] == 0:
                arc = arc[1:]
                down = 0
            if basepoint == 0 and arc[-1] == 0:
                arc = arc[:-1]
                up = 0
            if basepoint == long and arc[-1] == 0:
                arc = arc[:-1]
                down = 0                
            arcs.append((arc,up,down))
        if any([len(arc) > len(set(arc)) for arc,up,down in arcs]):
            continue        # you cannot cross twice the same segment

        # calculate expected value of sign, affected also by whether horizontal/vertical comes first
        term = (-1) ** sum([segs[cd.locs[tip][0]] * cd.weights[tip] for tip in cd.weights])
        for comp in connected_components(arcs, lambda x,y:set(x[0])&set(y[0])):
            term *= exp_monotone(tuple(comp))

        # collect together (n-t+b-1 choose b-1) terms
        k = (- total/2 + bins - 1,bins - 1)
        coefs[k] = coefs.get(k, Fraction(0)) + term

    # return polynomial
    terms = [(poly1d([Fraction(-k[0]+i) for i in range(k[1])], True) if k[1] else poly1d([Fraction(1)])
              ) * Fraction(v, factorial(k[1]))
             for k,v in coefs.items() if v != 0]
    if len(terms) == 0:
        return Fraction(0)    
    p = reduce(lambda x,y:x+y, terms) * Fraction(cd.coef)
    if p == poly1d(0):
        return Fraction(0)    
    return p

#===============================================================================
#
#   Test
#

def polystr(p, var = 'n'):
    if poly1d(p) == poly1d(0):
        return '0'
    return ' + '.join(['%s %s^%s' % (p[d],var,d) for d in range(p.order, -1, -1) if p[d]]
                      ).replace(' %s^1'%var,' %s'%var).replace(' %s^0'%var,'')

def curve_invs(only_quick = True):
    """
    only_quick: True - runs in few seconds, False - in few hours
    """
    print
    print 'Invariants'
    print '~~~~~~~~~~'
    print 'i(D) = <aa,D> = whitney index*'
    print 'c(D) = <AA,D> (doubled) = #crossings'
    print 'd(D) = -<abab,D> = defect'
    print 'u(D) = <aabb-abba,D>'
    print 'g(D) = -<aabb+abba,D>'
    print
    
    i,c,d,u,g = [CDF('aa'),
                 CDF('aa',2),
                 CDF('abab',coef=-1),
                 CDF('aabb')-CDF('abba'),
                 -CDF('aabb')-CDF('abba'),
                 ]
    
    print 'E[i] =',polystr(E[i])
    print 'V[i] =',polystr(E[i**2]), '\twith base point on boundary'
    print 'V[i] =',polystr((i**2).expectation(basepoint = None)), '\twith random base point'
    print
    print 'E[c] =',polystr(E[c])
    print 'E[d] =',polystr(E[d])
    print 'E[u] =',polystr(E[u])
    print 'E[g] =',polystr(E[g])
    print
    print 'V[c] =',polystr(E[c**2] - E[c]**2)
    print 'V[d] =','...' if only_quick else polystr(E[d**2] - E[d]**2)
    print 'V[u] =','...' if only_quick else polystr(E[u**2] - E[u]**2)
    print 'V[g] =','...' if only_quick else polystr(E[g**2] - E[g]**2)
    print
    print 'COV[c,d] =',polystr(E[c*d] - E[c]*E[d])
    print 'COV[c,u] =',polystr(E[c*u] - E[c]*E[u])
    print 'COV[d,u] =','...' if only_quick else polystr(E[d*u] - E[d]*E[u])
    print 'COV[c,g] =',polystr(E[c*g] - E[c]*E[g])
    print 'COV[d,g] =','...' if only_quick else polystr(E[d*g] - E[d]*E[g])
    print 'COV[u,g] =','...' if only_quick else polystr(E[u*g] - E[u]*E[g])
    print
    print 'E[i^3] =',polystr(E[i**3])
    print 'E[i^4] =','...' if only_quick else polystr(E[i**4])
    print 'E[i^2]^2 * 3 =',polystr(3 * E[i**2]**2)
    print
    print 'E[(c-E[c])^3] =',polystr(E[c**3] - 3*E[c**2]*E[c] + 2*E[c]**3)
    print 'E[(c-E[c])^4] =','...' if only_quick else polystr(E[c**4] - 4*E[c**3]*E[c] + 6*E[c**2]*E[c]**2 - 3*E[c]**4)
    print 'E[(c-E[c])^2]^2 * 3 =',polystr(3 * (E[c**2] - E[c]**2)**2)
    print

def knot_invs():
    d = CDF('abab',coef=-1)
    print 'E[c2(griddle)] =', polystr(E[d]/8)
    print 'V[c2(griddle)] =',
    terms = sorted((d**2).cds, key = lambda x:len(repr(x)))
    PV = reduce(lambda x,y:x+y,
                [p for p in [E[t]/16 for t in terms[:27]] + [E[t]/8 for t in terms[27:31]] + [E[terms[-1]]/4]
              if poly1d(0) != poly1d(p)]) - E[d]**2 / 16
    print polystr(PV)
