#!/usr/bin/env python3
"""Find a dominating set of (n+1)/2 queens on the n x n board, n odd, of the shape: exactly one queen in every
even-indexed row and every even-indexed column (a permutation on the even lines).  Squares with an even row or column
are then dominated along rows/columns; the SAT search requires every odd-odd square to lie on an occupied diagonal.
Used only to get an upper bound (adding a corner gives an (n+3)/2-set of Q_{n+1}); the result is checked directly
elsewhere (check_upper.py style), so nothing about this search needs to be trusted.   usage: find_odd_perm.py n"""
import sys, os, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType


def find(n, solver='cadical195'):
    ev = list(range(0, n, 2))
    nv = [0]
    def new():
        nv[0] += 1
        return nv[0]
    p = {(x, y): new() for x in ev for y in ev}
    T = {t: new() for t in range(1 - n, n)}; S = {s: new() for s in range(2 * n - 1)}
    cls = []
    def card(lits, b):
        c = CardEnc.equals(lits=lits, bound=b, top_id=nv[0], encoding=EncType.seqcounter)
        cls.extend(c.clauses); nv[0] = max(nv[0], c.nv)
    for x in ev:
        card([p[(x, y)] for y in ev], 1)
    for y in ev:
        card([p[(x, y)] for x in ev], 1)
    for t in T:
        cls.append([-T[t]] + [v for (x, y), v in p.items() if y - x == t])
    for s in S:
        cls.append([-S[s]] + [v for (x, y), v in p.items() if x + y == s])
    for x in range(1, n, 2):
        for y in range(1, n, 2):
            cls.append([T[y - x], S[x + y]])
    with Solver(name=solver, bootstrap_with=cls) as sv:
        if not sv.solve():
            return None
        m = set(l for l in sv.get_model() if l > 0)
    return sorted(s for s, v in p.items() if v in m)


if __name__ == '__main__':
    n = int(sys.argv[1]); t0 = time.process_time()
    D = find(n)
    und = None if D is None else sum(1 for x in range(n) for y in range(n) if not any(x == a or y == b or x - y == a - b or x + y == a + b for a, b in D))
    print(json.dumps({'n': n, 'size': None if D is None else len(D), 'undominated': und, 'cpu_s': round(time.process_time() - t0, 1), 'set_col_row': D}))
