#!/usr/bin/env python3
"""Check run_hard.py records: every selected case must be covered by UNSAT + DRAT-VERIFIED cubes (a cube is
covered if it has such a record or all 16 children of the next layer are covered); with --rehash every CNF is
rebuilt and its SHA-256 compared.   usage: check_hard.py n k records.jsonl --select square0|squaredef|all [--rehash]"""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from geom import cases_by_frame
import enc, run_hard

n, k, path = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
sel = sys.argv[sys.argv.index('--select') + 1] if '--select' in sys.argv else 'square0'
sq = lambda c: c[0] + c[1] == c[2] + c[3]
pick = {'square0': lambda c: sq(c) and sum(c[4:]) == 0, 'squaredef': lambda c: sq(c) and sum(c[4:]) > 0, 'all': lambda c: True}[sel]
cases = [c for c in cases_by_frame(n, k) if pick(c)]
if '--cases-file' in sys.argv:
    cases = [tuple(json.loads(l)['case']) for l in open(sys.argv[sys.argv.index('--cases-file') + 1])]
good = {}; sbp = None; sat = []
for l in open(path):
    r = json.loads(l)
    if 'cube' not in r:
        continue
    if r['result'] == 'SAT':
        sat.append(r)
    if r['result'] == 'UNSAT' and r.get('drat') == 'VERIFIED':
        good[(tuple(r['case']), r['cube'])] = r; sbp = r['sbp'] if sbp is None else sbp
def has_desc(case, cube):
    return any(c == case and cb.startswith(cube) and len(cb) > len(cube) for (c, cb) in good)


def covered(case, cube, depth=0):
    if (case, cube) in good:
        return True
    if depth >= 6 or not has_desc(case, cube):
        return False
    return all(covered(case, cube + format(i, '04b'), depth + 1) for i in range(16))


cov = [c for c in cases if covered(c, '')]
mism = 0
if '--rehash' in sys.argv:
    run_hard._A.update(n=n, k=k, sbp=bool(sbp))
    for (case, cube), r in good.items():
        B, txt = run_hard.build(case, cube)
        mism += enc.sha(txt) != r['cnf_sha256']
print(json.dumps({'n': n, 'k': k, 'select': sel, 'cases': len(cases), 'covered_by_verified_unsat_cubes': len(cov), 'not_covered': len(cases) - len(cov),
                  'verified_cubes': len(good), 'sat_records': len(sat), 'rehash_mismatch': mism if '--rehash' in sys.argv else None,
                  'uncovered_examples': [c for c in cases if c not in set(cov)][:5]}))
