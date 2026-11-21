#!/usr/bin/env python3
"""Tests of the frame encoder.
 1. sequential counter: brute force over all assignments, with repeated literals.
 2. solution counts: for small (n, k), enumerate ALL models of every canonical admissible case (projected
    to the queen variables), check each decoded set (k squares, dominating, belongs to this case), and
    compare (a) the orbit-weighted total and (b) the set of all symmetry images with a theory-free
    enumeration of all dominating k-sets (plain CNF: domination clauses + PySAT cardinality, no frames).
usage: test_enc.py [n k ...]   (default list below)"""
import itertools, sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import *
import enc
if os.environ.get('QD_ENC') == 'b':
    import enc_b as enc_alt
    enc.Base, enc.case_extra = enc_alt.Base, enc_alt.case_extra      # second encoding (pysat mode / tests only)
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType

CLAIMED = {(4, 2): 12, (5, 3): 186, (6, 3): 4, (6, 4): 2744, (7, 4): 86, (7, 5): 56188, (8, 4): 0, (8, 5): 4860,
           (9, 5): 114, (10, 5): 8}     # also the counts of the earlier, uncertified implementation


def test_counter():
    for nl in range(1, 7):
        for k in range(0, nl + 1):
            for pattern in ([i + 1 for i in range(nl)], [1 + (i // 2) for i in range(nl)], [(-1) ** i * (1 + i // 2) for i in range(nl)]):
                cnt = [0]
                def new():
                    cnt[0] += 1
                    return 100 + cnt[0]
                cls = []
                enc.atmost(pattern, k, new, cls)
                base = sorted({abs(l) for l in pattern})
                for bits in itertools.product([False, True], repeat=len(base)):
                    val = dict(zip(base, bits))
                    tot = sum(val[abs(l)] == (l > 0) for l in pattern)
                    with Solver(name='cadical195', bootstrap_with=cls + [[v if val[v] else -v] for v in base]) as S:
                        assert S.solve() == (tot <= k), (pattern, k, val)
    print('sequential counter: OK')


def theory_free(n, k):
    var = lambda x, y: x * n + y + 1
    cls = []
    for x in range(n):
        for y in range(n):
            cls.append([var(u, v) for u in range(n) for v in range(n) if u == x or v == y or v - u == y - x or u + v == x + y])
    lits = [var(x, y) for x in range(n) for y in range(n)]
    cls += CardEnc.equals(lits=lits, bound=k, top_id=n * n, encoding=EncType.totalizer).clauses
    out = set()
    with Solver(name='cadical195', bootstrap_with=cls) as S:
        while S.solve():
            m = S.get_model()
            D = frozenset((x, y) for x in range(n) for y in range(n) if m[var(x, y) - 1] > 0)
            assert len(D) == k and dominated(n, D)
            out.add(D)
            S.add_clause([-var(x, y) for x, y in D])
    return out


def frame_method(n, k, **kw):
    cases = all_cases(n, k)
    bases = {}
    total = 0; allsets = set(); nsat = 0
    for case, orb in sorted(cases.items()):
        dv = case[4:]
        if dv not in bases:
            bases[dv] = enc.Base(n, k, dv)
        B = bases[dv]
        extra, nv = enc.case_extra(B, case, **kw)
        cnt = 0
        with Solver(name='cadical195', bootstrap_with=B.cls + extra) as S:
            while S.solve():
                m = S.get_model()
                D = frozenset((x, y) for x in range(n) for y in range(n) if m[B.q[x][y] - 1] > 0)
                assert len(D) == k and dominated(n, D) and case_of(n, D) == case, (case, sorted(D))
                cnt += 1
                imgs = {frozenset(g(x, y) for x, y in D) for g in sym_maps(n)}
                allsets |= imgs
                S.add_clause([-B.q[x][y] for x, y in D])
        total += cnt * orb; nsat += cnt > 0
    return total, allsets, len(cases), nsat


def main():
    test_counter()
    args = list(map(int, sys.argv[1:]))
    jobs = list(zip(args[0::2], args[1::2])) or [(4, 2), (5, 3), (6, 3), (6, 4), (7, 4), (8, 4), (8, 5), (9, 5), (10, 5), (7, 5)]
    ok = True
    for n, k in jobs:
        t0 = time.time()
        tf = theory_free(n, k)
        total, allsets, ncases, nsat = frame_method(n, k)
        good = total == len(tf) and allsets == tf and (CLAIMED.get((n, k), len(tf)) == len(tf))
        ok &= good
        print('(n,k)=(%d,%d): theory-free %d sets; frame method: %d cases (%d satisfiable), orbit-weighted count %d, set equality %s; claimed %s  %s (%.0fs)' % (
            n, k, len(tf), ncases, nsat, total, allsets == tf, CLAIMED.get((n, k), '-'), 'OK' if good else 'MISMATCH', time.time() - t0), flush=True)
    print('ALL OK' if ok else 'FAILED')


if __name__ == '__main__':
    main()
