#!/usr/bin/env python3
"""Regression tests for the resumable certificate driver code/cert_stage1.py (external review, finding 1).

Repro of the reported defect: n = 4, g = 2, z0 = 0, T = 1 with the survivor file "C 5 a 0" gives 7
genuine UNSAT + VERIFIED cube records.  Rerunning into the same output file with an EMPTY survivor file
(a different, satisfiable formula: A = {0,2}, B = {1,3} is feasible) and nonexistent solver and checker
paths used to report all_unsat_verified = true.  It must now refuse.  Further cases: a record whose CNF
hash does not match the rebuilt CNF, a failed record and a truncated last line are solved again and
superseded; and the formula without exclusion clauses is reported as not refuted.
usage: test_resume.py CADICAL DRATTRIM   -- prints JSON; exit status 0 iff every case behaves."""
import json, os, subprocess, sys, tempfile
from pathlib import Path

CODE = Path(__file__).resolve().parent
CAD, DRAT = (str(Path(p).resolve()) for p in sys.argv[1:3])


def run(surv, out, wd, cad=CAD, drat=DRAT):
    r = subprocess.run([sys.executable, str(CODE / 'cert_stage1.py'), '4', '2', '0', surv, cad, drat, wd, '1', '2', out],
                       capture_output=True, text=True)
    last = [l for l in r.stdout.splitlines() if l.startswith('{')]
    return r.returncode, (json.loads(last[-1]) if last else {})


def edit(out, fn):
    L = open(out).read().splitlines()
    L = fn(L)
    open(out, 'w').write('\n'.join(L) + '\n')


def main():
    res = {}
    with tempfile.TemporaryDirectory() as td:
        surv, empty, out, wd = (os.path.join(td, x) for x in ('surv.txt', 'empty.txt', 'out.jsonl', 'wd'))
        open(surv, 'w').write('C 5 a 0\n')
        open(empty, 'w').write('')
        rc, d = run(surv, out, wd)
        res['genuine_run'] = rc == 0 and d.get('all_unsat_verified') is True and d.get('cube_reps') == 7 and d.get('solved') == 7
        before = open(out).read()
        rc, d = run(empty, out, wd, cad='/nonexistent/cadical', drat='/nonexistent/drat-trim')
        res['refuses_other_formula'] = rc == 2 and 'error' in d and open(out).read() == before
        # a record with a wrong CNF hash, then a failed record, then a truncated line: solved again
        edit(out, lambda L: L[:1] + [json.dumps(dict(json.loads(L[1]), cnf_sha256='0' * 64))] + L[2:])
        rc, d = run(surv, out, wd)
        res['bad_hash_resolved'] = rc == 0 and d.get('all_unsat_verified') is True and d.get('reused') == 6 and d.get('solved') == 1
        edit(out, lambda L: L + [json.dumps(dict(json.loads(L[2]), result='ERR1', drat=None))])
        rc, d = run(surv, out, wd)
        res['failed_record_retried'] = rc == 0 and d.get('reused') == 6 and d.get('solved') == 1 and d.get('superseded_records', 0) >= 2
        with open(out, 'a') as f:
            f.write('{"cube": "0001", "cnf_sha')
        rc, d = run(surv, out, wd)
        res['truncated_line_ignored'] = rc == 0 and d.get('all_unsat_verified') is True and d.get('reused') == 7 and d.get('solved') == 0
        rc, d = run(surv, out, wd, cad='/nonexistent/cadical', drat='/nonexistent/drat-trim')
        res['complete_reuse_needs_no_solver'] = rc == 0 and d.get('reused') == 7 and d.get('solved') == 0
        # the formula without exclusion clauses is satisfiable: not certified
        out2 = os.path.join(td, 'out2.jsonl')
        rc, d = run(empty, out2, wd)
        res['satisfiable_formula_not_certified'] = rc == 1 and d.get('all_unsat_verified') is False
        # a header for other parameters (different T) is refused
        edit(out2, lambda L: [json.dumps(dict(json.loads(L[0]), T=2))] + L[1:])
        rc, d = run(empty, out2, wd)
        res['refuses_other_T'] = rc == 2
    res['all_ok'] = all(res.values())
    print(json.dumps(res))
    sys.exit(0 if res['all_ok'] else 1)


if __name__ == '__main__':
    main()
