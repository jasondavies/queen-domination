#!/usr/bin/env python3
"""Coverage check of cross-check records (from the records alone):
  xcover.py n k CASES.jsonl RECORDS.jsonl [--rehash] [--summary OUT.json]
A cube (case, cube) is refuted if it has an UNSAT record, or an UNKNOWN record with field "split" = four
distinct line keys not fixed by the cube, and each of the 16 cubes  cube + (assignment of the four keys)
is refuted (the 16 assignments of 4 Boolean variables are exhaustive, so the cube is then unsatisfiable).
A case is refuted iff its empty cube is.  Also reports SAT records (each must be examined), the case list
membership of every case (against cases.case_list), and with --rehash rebuilds every CNF of the tree from
encx.py and compares the SHA-256 recorded at run time."""
import sys, os, json, hashlib, itertools, lzma
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cases as CS


def _open(p):
    return lzma.open(p, 'rt') if p.endswith('.xz') else open(p)


def key(case, cube):
    return json.dumps([list(case), sorted([list(k), v] for k, v in cube)])


def main():
    n, k = int(sys.argv[1]), int(sys.argv[2])
    clist = [tuple(json.loads(l)['case']) for l in _open(sys.argv[3]) if l.strip()]
    rehash = '--rehash' in sys.argv
    recs = {}
    nsat = 0; sats = []
    for l in _open(sys.argv[4]):
        r = json.loads(l)
        if 'case' not in r:
            continue
        kk = key(r['case'], r['cube'])
        if r['result'] == 'SAT':
            nsat += 1; sats.append(r)
        # a later UNSAT record for the same cube supersedes an UNKNOWN one
        if kk not in recs or r['result'] == 'UNSAT':
            recs[kk] = r
    valid = set(CS.case_list(n, k))
    bad_case = [c for c in clist if c not in valid]
    used = []

    def refuted(case, cube, depth=0):
        r = recs.get(key(case, cube))
        if r is None:
            return False
        used.append(r)
        if r['result'] == 'UNSAT':
            return True
        if r['result'] != 'UNKNOWN' or 'split' not in r:
            return False
        sv = [tuple(v) for v in r['split']]
        fixed = set(tuple(kk) for kk, v in cube)
        if len(set(sv)) != 4 or any(v in fixed for v in sv):
            return False
        return all(refuted(case, list(cube) + [[list(sv[i]), bits[i]] for i in range(4)], depth + 1)
                   for bits in itertools.product([0, 1], repeat=4))

    notref = []; nsplit = 0; leaves = 0; cpu = 0.0
    for c in clist:
        used.clear()
        if not refuted(c, []):
            notref.append(c)
        if len(used) > 1:
            nsplit += 1
        leaves += sum(1 for r in used if r['result'] == 'UNSAT')
        cpu += sum(r['cpu'] for r in used)
    mism = 0; nre = 0
    if rehash:
        from encx import Psi
        for r in recs.values():
            P = Psi(n, k, tuple(r['case']), cube=[(tuple(kk), v) for kk, v in r['cube']])
            nre += 1
            if hashlib.sha256(P.cnf.dimacs().encode()).hexdigest() != r['cnf_sha256']:
                mism += 1
    out = {'n': n, 'k': k, 'cases': len(clist), 'cases_not_in_independent_list': len(bad_case),
           'refuted': len(clist) - len(notref), 'not_refuted': len(notref), 'split_cases': nsplit,
           'unsat_leaves': leaves, 'SAT_records': nsat, 'cpu_s_in_trees': round(cpu, 1),
           'rehashed': nre, 'hash_mismatches': mism, 'not_refuted_list': notref[:50]}
    print(json.dumps(out))
    for r in sats:
        print('SAT record:', json.dumps(r))
    if '--summary' in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index('--summary') + 1], 'w'), indent=1)


if __name__ == '__main__':
    main()
