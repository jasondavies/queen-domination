#!/usr/bin/env python3
"""Known positives for the two CNF encoders at n = 28 (a check that they are not too strong).

  * every listed n = 28 survivor (A, B, z0) satisfies relax_cnf(28, 14, z0) (without exclusion clauses);
  * the 15-queen dominating set of data/q28_15.txt satisfies the stage-2 encoding sat_place.build for
    g = 15, with 13 of its empty rows and 13 of its empty columns as (A, B).
usage: encode_check28.py SURVIVORS.xz Q28_15   -- prints JSON."""
import json, lzma, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pysat.solvers import Solver
from refcheck import relax_cnf, bits
import sat_place

N, G = 28, 14


def main():
    surv = [l.split() for l in lzma.decompress(open(sys.argv[1], 'rb').read()).decode().splitlines() if l.startswith('C ')]
    pairs = [(int(p[1], 16), int(p[2], 16), int(p[3])) for p in surv]
    ok = 0
    for z0 in sorted(set(p[2] for p in pairs)):
        cls, a, b, pool = relax_cnf(N, G, z0)
        with Solver(name='cadical195', bootstrap_with=cls) as S:
            for (A, B, z) in pairs:
                if z != z0:
                    continue
                assum = [a[r] if A >> r & 1 else -a[r] for r in range(N)] + [b[x] if B >> x & 1 else -b[x] for x in range(N)]
                ok += bool(S.solve(assumptions=assum))
    rows = [l.rstrip('\n') for l in open(sys.argv[2]) if l.strip()]
    Q = [(r, c) for r in range(N) for c in range(N) if rows[r][c] == 'Q']
    A = sum(1 << r for r in bits(sum(1 << r for r in range(N) if all(q[0] != r for q in Q)), N)[:13])
    B = sum(1 << c for c in bits(sum(1 << c for c in range(N) if all(q[1] != c for q in Q)), N)[:13])
    z0 = sum(1 for (r, c) in Q if (r + c) % 2 == 0)
    txt = sat_place.build(N, 15, A, B, z0).splitlines()[1:]
    clauses = [list(map(int, l.split()))[:-1] for l in txt]
    cells = [(r, c) for r in range(N) if not A >> r & 1 for c in range(N) if not B >> c & 1]
    var = {p: i + 1 for i, p in enumerate(cells)}
    with Solver(name='cadical195', bootstrap_with=clauses) as S:
        known = bool(S.solve(assumptions=[var[p] if p in Q else -var[p] for p in cells]))
    print(json.dumps({'pairs': len(pairs), 'pairs_satisfy_relaxation': ok, 'q28_15_satisfies_sat_place': known,
                      'q28_15_empty_rows_cols': [len(bits(A, N)), len(bits(B, N))]}))


if __name__ == '__main__':
    main()
