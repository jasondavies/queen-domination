#!/usr/bin/env python3
"""Planted positives for encoding X: every known dominating set D (k = |D| <= n-2) must, in every board
orientation whose frame is canonical, (i) have its case in cases.case_list(n, k), and (ii) satisfy Psi(case)
with all queen variables fixed to D (solved by kissat).  Control: moving one queen to a square that leaves a
non-dominated square must make the fixed formula of the original case UNSAT.
Sources (data only): Kamenetsky's best-known sets n <= 26 (file of the n = 28 folder); the explicit sets quoted
in the frame method's planted test (Q27 Ostergard-Weakley + corner, Q29/Q31 from Weakley's Q30 set, Q31 even-lines set, Q30,
Q32, Q34, Q36 sets) and the 19-set of Q35 of data/frame/q35_19.json (k = 19 > 18: a positive control at k = 19)."""
import sys, os, re, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cases as CS
from encx import Psi
from ksolve import kissat

KAM = os.environ.get('QD_KAMENETSKY', 'kamenetsky.txt')     # Kamenetsky's file of best known placements (OEIS A075458)


def kamenetsky():
    out = []
    L = open(KAM).read().split('\n')
    for i, line in enumerate(L):
        m = re.match(r'a\((\d+)\)', line)
        if m:
            n = int(m.group(1))
            rows = L[i + 1:i + 1 + n]
            out.append(('kamenetsky a(%d)%s' % (n, ' #2' if 'another' in line else ''), n,
                        [(x, y) for y in range(n) for x in range(n) if rows[y][x] == 'Q']))
    return out


def others():
    w30 = [(x + 14, y + 14) for x, y in zip(range(-13, 16, 2), [1, -9, 9, 15, -11, -5, 3, -3, 13, 11, 7, -13, -7, -1, 5])]
    ow27 = [(x + 13, y + 13) for x, y in zip(range(-12, 13, 2), [6, -12, -6, 8, 0, -8, 10, -2, 4, 12, -10, -4, 2])] + [(4, 4)]
    q34 = [(1, 19), (3, 7), (5, 27), (7, 9), (9, 17), (11, 1), (13, 23), (15, 15), (17, 31), (19, 5), (21, 13), (23, 21),
           (25, 3), (27, 33), (29, 11), (31, 25), (32, 32), (33, 29)]
    return [('weakley30', 30, w30), ('ow27+corner', 27, ow27), ('q29 from w30', 29, [(x - 1, y - 1) for x, y in w30]),
            ('q31 = w30+corner', 31, w30 + [(30, 30)]),
            ('q31 even lines', 31, [(0, 22), (2, 2), (4, 6), (6, 12), (8, 26), (10, 20), (12, 16), (14, 0), (16, 30),
                                    (18, 14), (20, 10), (22, 4), (24, 18), (26, 24), (28, 28), (30, 8)]),
            ('q32_17 from w30', 32, w30 + [(30, 30), (31, 31)]),
            ('q34_18', 34, q34), ('q35_19 (k=19)', 35, q34 + [(34, 34)])]


def check(name, n, D, rnd):
    k = len(D)
    assert len(set(D)) == k and CS.dominates(n, D), name
    cl = set(CS.case_list(n, k))
    n_or = 0
    seen = set()
    for g in CS.symmetries(n):
        E = tuple(sorted(g(p) for p in D))
        if E in seen:
            continue
        seen.add(E)
        c = CS.case_of_set(n, E)
        if min(CS.sym_case(n, h, c)[:4] for h in CS.symmetries(n)) != c[:4]:
            continue                                   # frame not canonical in this orientation
        assert c in cl, (name, c)
        P = Psi(n, k, c)
        P.cnf.clauses += P.fix_set_units(E)
        r = kissat(P.cnf.dimacs())
        assert r[0] == 'SAT', (name, c, r[0])
        # control: move one queen so that the set no longer dominates
        for _ in range(200):
            i = rnd.randrange(k); p = (rnd.randrange(n), rnd.randrange(n))
            F = list(E); F[i] = p
            if len(set(F)) == k and not CS.dominates(n, F):
                break
        else:
            raise AssertionError('no control found')
        P2 = Psi(n, k, c)
        P2.cnf.clauses += P2.fix_set_units(F)
        r2 = kissat(P2.cnf.dimacs())
        assert r2[0] == 'UNSAT', (name, 'control accepted')
        n_or += 1
    return n_or


def main():
    rnd = random.Random(3)
    total = 0
    for name, n, D in kamenetsky() + others():
        if len(D) > n - 2 or n < 4:
            continue
        m = check(name, n, D, rnd)
        total += 1
        print('%-22s n=%2d k=%2d  accepted in %d canonical orientation(s); moved-queen control rejected' % (name, n, len(D), m), flush=True)
    print('planted_x: %d sets OK' % total)


if __name__ == '__main__':
    main()
