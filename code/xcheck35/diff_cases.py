#!/usr/bin/env python3
"""Differential test of the two pipelines on a case file:
   A = enc.py (Base + case_extra, called unmodified) with CaDiCaL 1.9.5 (PySAT), no symmetry breaking;
   X = encx.py with kissat 4.0.4.
Per case: both verdicts; every model of either side is decoded and checked (dominating, size k, case).
  diff_cases.py n k CASES.jsonl OUT.jsonl [--jobs J]"""
import sys, os, json, time, argparse
import multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(1, os.path.join(os.path.dirname(HERE), 'frame'))
import cases as CS
from encx import Psi
from ksolve import kissat

_B = {}


def run(args):
    n, k, case = args
    import enc
    from pysat.solvers import Solver
    case = tuple(case)
    dv = case[4:]
    if dv not in _B:
        _B[dv] = enc.Base(n, k, dv)
    B = _B[dv]
    extra, nv = enc.case_extra(B, case)
    t0 = time.process_time()
    with Solver(name='cadical195', bootstrap_with=B.cls + extra) as S:
        ra = S.solve()
        ma = S.get_model() if ra else None
    ta = time.process_time() - t0
    rec = {'case': list(case), 'A': 'SAT' if ra else 'UNSAT', 'tA': round(ta, 2)}
    if ra:
        # decode A's model through the set of q-variables of the A encoding: q[x][y] is not exposed by a
        # documented API, so check by re-solving X with the decoded set is not possible; instead decode by
        # fixing: a set D is A's model iff it satisfies A's formula -- we use B.q if present.
        q = getattr(B, 'q', None)
        if q is not None:
            pos = set(l for l in ma if l > 0)
            D = sorted((x, y) for x in range(n) for y in range(n) if q[x][y] in pos)
            rec['A_set'] = D
            rec['A_ok'] = (len(D) == k and CS.dominates(n, D) and CS.case_of_set(n, D) == case)
    P = Psi(n, k, case)
    rx, model, cpu, wall, rc = kissat(P.cnf.dimacs())
    rec['X'] = rx; rec['tX'] = round(cpu, 2)
    if rx == 'SAT':
        D = P.decode(model)
        rec['X_set'] = D
        rec['X_ok'] = (len(D) == k and CS.dominates(n, D) and CS.case_of_set(n, D) == case)
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('n', type=int); ap.add_argument('k', type=int); ap.add_argument('cases'); ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=2)
    a = ap.parse_args()
    cl = [tuple(json.loads(l)['case']) for l in open(a.cases) if l.strip()]
    agree = dis = sa = sx = 0
    with open(a.out, 'w') as f, mp.Pool(a.jobs) as pool:
        for rec in pool.imap_unordered(run, [(a.n, a.k, c) for c in cl]):
            f.write(json.dumps(rec) + '\n')
            if rec['A'] == rec['X']:
                agree += 1
            else:
                dis += 1
                print('DISAGREE', json.dumps(rec), flush=True)
            sa += rec['A'] == 'SAT'; sx += rec['X'] == 'SAT'
            for side in 'AX':
                if rec.get(side + '_ok') is False:
                    print('BAD MODEL', side, json.dumps(rec), flush=True)
    print('n=%d k=%d cases %d: agree %d disagree %d; SAT cases A %d X %d' % (a.n, a.k, len(cl), agree, dis, sa, sx), flush=True)


if __name__ == '__main__':
    main()
