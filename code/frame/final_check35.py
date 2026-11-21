#!/usr/bin/env python3
"""Complete coverage check for (n, k) = (35, 18) [or another pair given as arguments].

The case list is rebuilt (geom.cases_by_frame).  A case counts as refuted iff
 (a) frame/out/d_N_K.jsonl or d_N_K_sq.jsonl holds a record for it with result UNSAT and drat VERIFIED whose
     cnf_sha256 equals the SHA-256 of the CNF rebuilt now by enc.py (default options), or
 (b) frame/out/h_N_K.jsonl (run_hard.py) holds UNSAT + VERIFIED cube records that cover it (the empty cube, or
     recursively all 16 children of a cube), each with cnf_sha256 equal to the CNF rebuilt now
     (enc.py defaults + residual symmetry breaking + the cube's unit clauses).
Any SAT record is reported.  Exit status 0 only if every case is refuted and no hash differs.
usage: final_check35.py [n k] [--jobs 8] [--no-rehash]"""
import sys, os, json
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from geom import cases_by_frame
import enc, run_hard
OUT = os.environ.get('QD_FRAME_OUT', os.path.join(HERE, 'out'))     # uncompressed run records
_B = {}


def rehash_plain(arg):
    n, k, case = arg
    if case[4:] not in _B:
        _B.clear(); _B[case[4:]] = enc.Base(n, k, case[4:])
    extra, nv = enc.case_extra(_B[case[4:]], case)
    return ('p', case, '', enc.sha(enc.dimacs(_B[case[4:]], extra, nv)))


def rehash_cube(arg):
    n, k, case, cube = arg
    run_hard._A.update(n=n, k=k, sbp=True)
    B, txt = run_hard.build(case, cube)
    return ('h', case, cube, enc.sha(txt))


def work(arg):
    return rehash_plain(arg) if len(arg) == 3 else rehash_cube(arg)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    n, k = (int(args[0]), int(args[1])) if len(args) >= 2 else (35, 18)
    jobs = int(sys.argv[sys.argv.index('--jobs') + 1]) if '--jobs' in sys.argv else 8
    cases = cases_by_frame(n, k)
    plain = {}; sat = []
    for fn in ('d_%d_%d.jsonl' % (n, k), 'd_%d_%d_sq.jsonl' % (n, k)):
        p = os.path.join(OUT, fn)
        if os.path.exists(p):
            for l in open(p):
                try:
                    r = json.loads(l)
                except ValueError:
                    continue
                if 'case' in r:
                    if r['result'] == 'SAT':
                        sat.append(r)
                    if r['result'] == 'UNSAT' and r.get('drat') == 'VERIFIED':
                        plain[tuple(r['case'])] = r
    cubes = {}
    p = os.path.join(OUT, 'h_%d_%d.jsonl' % (n, k))
    if os.path.exists(p):
        for l in open(p):
            try:
                r = json.loads(l)
            except ValueError:
                continue
            if 'cube' in r:
                if r['result'] == 'SAT':
                    sat.append(r)
                if r['result'] == 'UNSAT' and r.get('drat') == 'VERIFIED' and r.get('sbp') is True:
                    cubes[(tuple(r['case']), r['cube'])] = r
    by_case = {}
    for (c, cb) in cubes:
        by_case.setdefault(c, set()).add(cb)

    def covered(case, cube, depth=0):
        have = by_case.get(case, ())
        if cube in have:
            return True
        if depth >= 8 or not any(cb.startswith(cube) and len(cb) > len(cube) for cb in have):
            return False
        return all(covered(case, cube + format(i, '04b'), depth + 1) for i in range(16))
    st = {'n': n, 'k': k, 'frames': len({c[:4] for c in cases}), 'cases': len(cases), 'refuted_unsplit_plain': 0, 'refuted_by_run_hard_unsplit': 0,
          'refuted_by_run_hard_cubes': 0, 'NOT_REFUTED': 0, 'sat_records': len(sat)}
    missing = []; todo = []
    for c in cases:
        if c in plain:
            st['refuted_unsplit_plain'] += 1; todo.append((n, k, c))
        elif covered(c, ''):
            if '' in by_case.get(c, ()):
                st['refuted_by_run_hard_unsplit'] += 1
            else:
                st['refuted_by_run_hard_cubes'] += 1
        else:
            st['NOT_REFUTED'] += 1; missing.append(c)
    used_cubes = [(c, cb) for (c, cb) in cubes if c not in plain]
    todo += [(n, k, c, cb) for (c, cb) in used_cubes]
    st['verified_cube_records_used'] = len(used_cubes)
    mism = 0
    if '--no-rehash' not in sys.argv:
        todo.sort(key=lambda t: t[2][4:])
        with Pool(jobs) as P:
            for kind, case, cube, h in P.imap_unordered(work, todo, chunksize=32):
                rec = plain[case] if kind == 'p' else cubes[(case, cube)]
                mism += h != rec['cnf_sha256']
        st['cnf_hashes_rebuilt'] = len(todo); st['hash_mismatches'] = mism
    st['t_solve_cpu_h'] = round((sum(r['t_solve'] for r in plain.values()) + sum(cubes[x]['t_solve'] for x in used_cubes)) / 3600, 1)
    st['t_check_cpu_h'] = round((sum(r.get('t_check', 0) for r in plain.values()) + sum(cubes[x].get('t_check', 0) for x in used_cubes)) / 3600, 1)
    st['not_refuted_examples'] = missing[:5]
    st['ALL_CASES_UNSAT_WITH_VERIFIED_PROOFS'] = st['NOT_REFUTED'] == 0 and not sat and mism == 0 and '--no-rehash' not in sys.argv
    print(json.dumps(st))
    sys.exit(0 if st['ALL_CASES_UNSAT_WITH_VERIFIED_PROOFS'] else 1)


if __name__ == '__main__':
    main()
