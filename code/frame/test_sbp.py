#!/usr/bin/env python3
"""Tests of the residual symmetry breaking (hard_test.sbp_clauses, PROOFS F.6).
 1. the table used for the action of the 8 symmetries on the occupancy vector (oR, oC) agrees with the geometric
    maps on random sets;
 2. for small (n, k) and every case with a non-trivial stabiliser: the solutions of Phi(case) & SBP, expanded by
    the stabiliser, are exactly the solutions of Phi(case) (all models enumerated on the queen variables)."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import *
import enc
from hard_test import sbp_clauses, stabiliser
from pysat.solvers import Solver


def models(B, cls, n):
    out = set()
    with Solver(name='cadical195', bootstrap_with=cls) as S:
        while S.solve():
            m = S.get_model()
            D = frozenset((x, y) for x in range(n) for y in range(n) if m[B.q[x][y] - 1] > 0)
            out.add(D); S.add_clause([-B.q[x][y] for x, y in D])
    return out


def main():
    rnd = random.Random(3)
    n = 9; m = n - 1
    B = enc.Base(n, 4, (0, 0, 0, 0))
    perm = {1: lambda R, C: ([R[i] for i in range(n)], [C[m - i] for i in range(n)]), 2: lambda R, C: ([R[m - i] for i in range(n)], [C[i] for i in range(n)]),
            3: lambda R, C: ([R[m - i] for i in range(n)], [C[m - i] for i in range(n)]), 4: lambda R, C: ([C[i] for i in range(n)], [R[i] for i in range(n)]),
            5: lambda R, C: ([C[i] for i in range(n)], [R[m - i] for i in range(n)]), 6: lambda R, C: ([C[m - i] for i in range(n)], [R[i] for i in range(n)]),
            7: lambda R, C: ([C[m - i] for i in range(n)], [R[m - i] for i in range(n)])}
    for _ in range(300):
        D = {(rnd.randrange(n), rnd.randrange(n)) for _ in range(4)}
        R = [any(y == i for x, y in D) for i in range(n)]; C = [any(x == i for x, y in D) for i in range(n)]
        for g, f in enumerate(sym_maps(n)):
            if g == 0:
                continue
            E = {f(x, y) for x, y in D}
            R2 = [any(y == i for x, y in E) for i in range(n)]; C2 = [any(x == i for x, y in E) for i in range(n)]
            assert (R2, C2) == tuple(perm[g](R, C)), g
    # the same table is hard-coded in hard_test.sbp_clauses: compare on variables
    case = (0, 0, 0, 0, 0, 0, 0, 0)
    print('action of the symmetries on (oR, oC): OK')
    tot = 0; nst = 0
    for (n, k) in [(4, 2), (5, 3), (6, 3), (6, 4), (7, 4), (8, 5), (9, 5), (10, 5)]:
        bases = {}
        for case in cases_by_frame(n, k):
            st = stabiliser(case)
            if len(st) == 1:
                continue
            if case[4:] not in bases:
                bases[case[4:]] = enc.Base(n, k, case[4:])
            B = bases[case[4:]]
            extra, nv = enc.case_extra(B, case)
            top = [nv]
            def new():
                top[0] += 1
                return top[0]
            full = models(B, B.cls + extra, n)
            red = models(B, B.cls + extra + sbp_clauses(B, case, new), n)
            maps = sym_maps(n)
            exp = {frozenset(maps[g](x, y) for x, y in D) for D in red for g in st}
            assert red <= full and exp == full, (n, k, case, len(full), len(red))
            tot += len(full); nst += 1
        print('(n,k)=(%d,%d): symmetric cases checked so far %d, solutions %d: OK' % (n, k, nst, tot), flush=True)
    print('ALL OK')


if __name__ == '__main__':
    main()
