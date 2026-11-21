#!/usr/bin/env python3
"""Find a dominating set of n/2 + 1 queens on the n x n board (n even) of the classical shape: one queen in
every odd-indexed column and every odd-indexed row (a permutation on the odd lines) plus one further queen
anywhere.  SAT search (PySAT / CaDiCaL); the result is checked by a direct domination test, so nothing
about this search needs to be trusted.   usage: find_plus1.py n [x y]   (x y: optional fixed position of the extra queen)"""
import sys, os, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import dominated
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType


def find(n, solver='cadical195', extra=None):
    odd = list(range(1, n, 2))
    nv = [0]
    def new():
        nv[0] += 1
        return nv[0]
    p = {(x, y): new() for x in odd for y in odd}
    e = {(x, y): new() for x in range(n) for y in range(n)}
    T = {t: new() for t in range(1 - n, n)}; S = {s: new() for s in range(2 * n - 1)}
    ER = [new() for _ in range(n)]; EC = [new() for _ in range(n)]     # row / column of the extra queen
    cls = []
    def card(lits, b):
        c = CardEnc.equals(lits=lits, bound=b, top_id=nv[0], encoding=EncType.seqcounter)
        cls.extend(c.clauses); nv[0] = max(nv[0], c.nv)
    for x in odd:
        card([p[(x, y)] for y in odd], 1)
    for y in odd:
        card([p[(x, y)] for x in odd], 1)
    card(list(e.values()), 1)
    if extra is not None:
        cls.append([e[extra]])            # optional: fix the position of the extra queen
    for t in T:
        cls.append([-T[t]] + [v for (x, y), v in p.items() if y - x == t] + [v for (x, y), v in e.items() if y - x == t])
    for s in S:
        cls.append([-S[s]] + [v for (x, y), v in p.items() if x + y == s] + [v for (x, y), v in e.items() if x + y == s])
    for y in range(n):
        cls.append([-ER[y]] + [e[(x, y)] for x in range(n)])
    for x in range(n):
        cls.append([-EC[x]] + [e[(x, y)] for y in range(n)])
    for x in range(0, n, 2):
        for y in range(0, n, 2):
            cls.append([T[y - x], S[x + y], ER[y], EC[x]])
    with Solver(name=solver, bootstrap_with=cls) as sv:
        if not sv.solve():
            return None
        m = set(l for l in sv.get_model() if l > 0)
    D = sorted([s for s, v in p.items() if v in m] + [s for s, v in e.items() if v in m])
    return D


if __name__ == '__main__':
    n = int(sys.argv[1]); t0 = time.process_time()
    extra = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else None
    D = find(n, extra=extra)
    ok = D is not None and len(set(D)) == n // 2 + 1 and dominated(n, D)
    print(json.dumps({'n': n, 'size': None if D is None else len(set(D)), 'dominating': ok, 'cpu_s': round(time.process_time() - t0, 1), 'set_col_row': D}))
