#!/usr/bin/env python3
"""Test that the encoder's waste literals compute exactly the left-hand sides of (F), (V), (H).

For random sets D (dominating or not) on boards up to 16: build the case formula of D's own case with the
debug hook, evaluate every waste term (a conjunction of line literals) under D's true line occupancy,
and compare  (number of true waste terms)  with  bound + [u0] + [v0] + U,  where U = number of needy
squares of the border / the sides lying on no occupied diagonal (computed by listing squares).  For a
dominating set U = 0, so the encoded constraint "true waste terms <= bound (+[u0]+[v0])" holds with
equality; in particular the constraint is satisfied by every dominating set of the case.
Also checks all FRAME unit clauses against D.     usage: test_waste.py [seed] [samples]"""
import random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import *
import enc


def check(n, D, bases):
    D = set(D); k = len(D)
    if frame_of(n, D) is None:
        return 0
    case = case_of(n, D)
    a, b, c, d = frame_of(n, D)
    w, h = b - a, d - c
    key = (n, k, case[4:])
    if key not in bases:
        bases.clear()                      # keep memory small
        bases[key] = enc.Base(n, k, case[4:])
    B = bases[key]
    R, C, T, S = lines(D)
    val = {}
    for y in range(n): val[B.oR[y]] = y in R
    for x in range(n): val[B.oC[x]] = x in C
    for t, v in B.oT.items(): val[v] = t in T
    for s, v in B.oS.items(): val[v] = s in S
    ev = lambda l: val[l] if l > 0 else not val[-l]
    dbg = {}
    extra, nv = enc.case_extra(B, case, debug=dbg)
    nfr = a + (n - 1 - b) + c + (n - 1 - d) + 4
    for cl in extra[:nfr]:                 # the FRAME unit clauses come first
        assert len(cl) == 1 and ev(cl[0]), 'frame unit violated'
    needy = lambda s: s[0] not in C and s[1] not in R
    m = lambda s: ((s[1] - s[0]) in T) + ((s[0] + s[1]) in S)
    sets = {'F': border(a, b, c, d), 'V': vsides(a, b, c, d), 'H': hsides(a, b, c, d)}
    assert ('V' in dbg) == (w >= h) and ('H' in dbg) == (h >= w) and 'F' in dbg
    for name in dbg:
        if name == 'waste':
            continue
        conds, bound, extra_lits = dbg[name]
        true_terms = sum(all(ev(l) for l in cnd) for cnd in conds)
        U = sum(1 for s in sets[name] if needy(s) and m(s) == 0)
        assert true_terms == bound + sum(ev(l) for l in extra_lits) + U, (name, n, sorted(D), true_terms, bound, U)
    return 1


def main():
    rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    bases = {}; done = 0; dom = 0
    for it in range(N):
        n = rnd.randint(4, 16)
        cells = [(x, y) for x in range(n) for y in range(n)]
        mode = rnd.random()
        if mode < 0.5:
            D = set(rnd.sample(cells, rnd.randint(2, n - 2)))
        else:                               # random dominating set with two forced empty rows/columns
            ex = set(rnd.sample(range(n), 2)); ey = set(rnd.sample(range(n), 2))
            rnd.shuffle(cells); D = set()
            for s in cells:
                if dominated(n, D):
                    break
                if s[0] not in ex and s[1] not in ey:
                    D.add(s)
        if len(D) < 2:
            continue
        done += check(n, D, bases); dom += dominated(n, D)
    print('waste-term test: %d sets (%d dominating): OK' % (done, dom))


if __name__ == '__main__':
    main()
