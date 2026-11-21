#!/usr/bin/env python3
"""Exact solution-set comparison for small (n, k):
  reference  = all dominating k-sets of Q_n, enumerated by a theory-free formula (domination clauses on the
               queen variables + PySAT's CardEnc 'exactly k', blocking clauses), each checked directly;
  frame (X)  = for every case of cases.case_list(n, k), all models of encx.Psi(case) projected onto the queen
               variables (blocking clauses), each decoded set checked to dominate and to have exactly that
               case; then closed under the 8 board symmetries.
The two sets must be equal (this tests the case list, the symmetry action, Proposition C and the encoding
together, on positive and negative instances).  Solver: Glucose 4 (PySAT) for both sides.
Usage: test_sets.py n k [n k ...] [--no-vh]"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cases
from encx import Psi
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType


def reference(n, k, solver='glucose4'):
    var = {(x, y): 1 + x * n + y for x in range(n) for y in range(n)}
    cls = []
    for x in range(n):
        for y in range(n):
            cl = [var[(u, v)] for u in range(n) for v in range(n)
                  if u == x or v == y or u - v == x - y or u + v == x + y]
            cls.append(cl)
    card = CardEnc.equals(lits=list(var.values()), bound=k, top_id=n * n, encoding=EncType.seqcounter)
    s = Solver(name=solver, bootstrap_with=cls + card.clauses)
    sols = set()
    while s.solve():
        m = set(l for l in s.get_model() if l > 0)
        D = tuple(sorted(p for p, v in var.items() if v in m))
        assert len(D) == k and cases.dominates(n, D)
        sols.add(D)
        s.add_clause([-var[p] for p in D])
    s.delete()
    return sols


def frame_sets(n, k, vh_always=True, solver='glucose4'):
    G = cases.symmetries(n)
    found = set(); per_case = {}
    for c in cases.case_list(n, k):
        P = Psi(n, k, c, vh_always=vh_always)
        s = Solver(name=solver, bootstrap_with=P.cnf.clauses)
        cnt = 0
        while s.solve():
            D = tuple(P.decode(s.get_model()))
            assert len(D) == k and cases.dominates(n, D), (c, D)
            assert cases.case_of_set(n, D) == c, (c, D, cases.case_of_set(n, D))
            cnt += 1
            for g in G:
                found.add(tuple(sorted(g(p) for p in D)))
            s.add_clause([-P.q[p] for p in D])
        s.delete()
        if cnt:
            per_case[c] = cnt
    return found, per_case


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    vh = '--no-vh' not in sys.argv
    ok = True
    for i in range(0, len(args), 2):
        n, k = int(args[i]), int(args[i + 1])
        t0 = time.time(); ref = reference(n, k); t1 = time.time()
        fr, pc = frame_sets(n, k, vh_always=vh); t2 = time.time()
        eq = (ref == fr)
        ok &= eq
        print('(n,k)=(%d,%d) cases %d: reference %d sets (%.1fs), frame/X %d sets from %d satisfiable cases (%.1fs): %s'
              % (n, k, len(cases.case_list(n, k)), len(ref), t1 - t0, len(fr), len(pc), t2 - t1,
                 'EQUAL' if eq else 'DIFFERENT'), flush=True)
    print('ALL EQUAL' if ok else 'MISMATCH')


if __name__ == '__main__':
    main()
