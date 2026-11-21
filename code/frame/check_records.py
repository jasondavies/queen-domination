#!/usr/bin/env python3
"""Check the records of a DRAT run: rebuild the case list from first principles (geom.cases_by_frame), require
exactly one final record per case with result UNSAT and drat VERIFIED, and (--rehash) rebuild every CNF and
compare its SHA-256 with the recorded one.  Prints a SHA-256 over the sorted (case, cnf hash) list.
usage: check_records.py n k records.jsonl [--rehash] [--jobs 6]"""
import sys, os, json, hashlib
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import cases_by_frame
import enc

_B = {}


def rehash(arg):
    n, k, case = arg
    key = case[4:]
    if key not in _B:
        _B[key] = enc.Base(n, k, key)
    extra, nv = enc.case_extra(_B[key], case)
    return case, enc.sha(enc.dimacs(_B[key], extra, nv))


if __name__ == '__main__':
    n, k, path = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    jobs = int(sys.argv[sys.argv.index('--jobs') + 1]) if '--jobs' in sys.argv else 6
    cases = cases_by_frame(n, k)
    rec = {}
    for l in open(path):
        r = json.loads(l)
        if 'case' in r:
            rec[tuple(r['case'])] = r
    missing = [c for c in cases if c not in rec]
    extra_ = [c for c in rec if c not in set(cases)]
    bad = [c for c in cases if c in rec and not (rec[c]['result'] == 'UNSAT' and rec[c].get('drat') == 'VERIFIED')]
    mism = []
    if '--rehash' in sys.argv:
        with Pool(jobs) as P:
            for case, h in P.imap_unordered(rehash, [(n, k, c) for c in cases if c in rec], chunksize=16):
                if h != rec[case]['cnf_sha256']:
                    mism.append(case)
    digest = hashlib.sha256('\n'.join('%s %s' % (' '.join(map(str, c)), rec[c]['cnf_sha256']) for c in sorted(rec)).encode()).hexdigest()
    out = {'n': n, 'k': k, 'frames': len({c[:4] for c in cases}), 'cases': len(cases), 'records': len(rec), 'missing': len(missing),
           'not_in_case_list': len(extra_), 'not_unsat_verified': len(bad), 'rehash_checked': '--rehash' in sys.argv,
           'hash_mismatch': len(mism), 'records_digest': digest,
           't_solve': round(sum(r.get('t_solve', 0) for r in rec.values()), 1), 't_check': round(sum(r.get('t_check', 0) for r in rec.values()), 1),
           'proof_GB': round(sum(r.get('proof_bytes', 0) for r in rec.values()) / 1e9, 3),
           'max_proof_MB': round(max(r.get('proof_bytes', 0) for r in rec.values()) / 1e6, 1),
           'max_t_solve': max(r.get('t_solve', 0) for r in rec.values())}
    out['ALL_UNSAT_VERIFIED'] = not (missing or extra_ or bad or mism)
    print(json.dumps(out))
    sys.exit(0 if out['ALL_UNSAT_VERIFIED'] else 1)
