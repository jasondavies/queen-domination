#!/usr/bin/env python3
"""Theory-free reference for the zero-deficit negative controls: is there a set of exactly k mutually non-attacking
queens dominating Q_n?  (These are exactly the dominating k-sets with all four deficits 0.)  Formula: queen variables, pairwise at-most-one on every row,
column and diagonal, a domination clause per square, PySAT CardEnc (totalizer) 'exactly k'; no frames, no
identities, no symmetry breaking.  Solver kissat.  A model is decoded and checked directly.
Usage: plain_indep.py n k [timeout]"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cases as CS
from ksolve import kissat
from pysat.card import CardEnc, EncType


def main():
    n, k = int(sys.argv[1]), int(sys.argv[2])
    tl = int(sys.argv[3]) if len(sys.argv) > 3 else None
    var = {(x, y): 1 + x * n + y for x in range(n) for y in range(n)}
    cls = []
    lines = {}
    for (x, y), v in var.items():
        for key in (('r', y), ('c', x), ('t', y - x), ('s', x + y)):
            lines.setdefault(key, []).append(v)
    for L in lines.values():
        for i in range(len(L)):
            for j in range(i + 1, len(L)):
                cls.append([-L[i], -L[j]])
    for (x, y) in var:
        cls.append([v for (u, w), v in var.items() if u == x or w == y or u - w == x - y or u + w == x + y])
    card = CardEnc.equals(lits=list(var.values()), bound=k, top_id=n * n, encoding=EncType.totalizer)
    cls += card.clauses
    nv = max(card.nv, n * n)
    dim = 'p cnf %d %d\n' % (nv, len(cls)) + ''.join(' '.join(map(str, c)) + ' 0\n' for c in cls)
    res, model, cpu, wall, rc = kissat(dim, timeout=tl)
    line = 'plain independent-dominating check n=%d k=%d: %s (kissat %.1f CPU-s)' % (n, k, res, cpu)
    if res == 'SAT':
        pos = set(l for l in model if l > 0)
        D = sorted(p for p, v in var.items() if v in pos)
        ok = CS.dominates(n, D) and all(
            not (p != q and (p[0] == q[0] or p[1] == q[1] or p[0] - p[1] == q[0] - q[1] or p[0] + p[1] == q[0] + q[1]))
            for p in D for q in D)
        line += ' set %s, |D|=%d, dominating & independent: %s' % (D, len(D), ok)
    print(line, flush=True)


if __name__ == '__main__':
    main()
