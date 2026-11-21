#!/usr/bin/env python3
"""Cross-check runner: encoding X (encx.py) + kissat 4.0.4, no symmetry breaking.

  xrun.py n k CASES.jsonl OUT.jsonl [--jobs J] [--tl SECONDS] [--order ORDER.json]

CASES.jsonl: one {"case": [...]} per line.  Every case is first solved as a whole with time limit tl; a
(sub)formula that times out is replaced by its 16 children: the parent cube extended by each of the 16
assignments of the next 4 split variables (diagonal occupancies, see split_vars) not already fixed.  The 16
assignments of 4 Boolean variables are exhaustive, so a case is refuted iff all leaves of its tree are UNSAT
(checked independently by xcover.py from the records alone).
Records (one per solver call): case, cube (list of [line key, value]), result (SAT/UNSAT/UNKNOWN), cpu, wall,
tl, cnf_sha256, vars, clauses; split records add "split": the 4 variables.  A SAT record carries the decoded
queens and the results of the direct checks (dominating, case).  Resumable (finished calls are skipped)."""
import sys, os, json, time, hashlib, argparse
import multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cases as CS
from encx import Psi
from ksolve import kissat, glucose

SOLVER = 'kissat 4.0.4 (tools/kissat, sha256 1aeb303c...)'


def split_vars(n, case, cube):
    """the next 4 diagonal-occupancy variables not fixed by the cube: diagonals through the four box corners
    first, then their parallels at distance 1, 2, ... (all keys are valid diagonals of the board)"""
    ml, mr, mb, mt = case[:4]
    a, b, c, d = ml, n - 1 - mr, mb, n - 1 - mt
    fixed = set(tuple(k) for k, v in cube)
    cand = []
    for j in range(0, 2 * n):
        for key in (('T', c - a + j), ('S', a + d - j), ('T', d - b - j), ('S', b + c + j),
                    ('T', c - a - j), ('S', a + d + j), ('T', d - b + j), ('S', b + c - j)):
            ok = (-(n - 1) <= key[1] <= n - 1) if key[0] == 'T' else (0 <= key[1] <= 2 * n - 2)
            if ok and key not in fixed and key not in cand:
                cand.append(key)
    return cand[:4]


def children(n, case, cube):
    sv = split_vars(n, case, cube)
    assert len(sv) == 4
    out = []
    for m in range(16):
        out.append(list(cube) + [[list(sv[i]), (m >> i) & 1] for i in range(4)])
    return sv, out


def cube_key(case, cube):
    return json.dumps([list(case), sorted([list(k), v] for k, v in cube)])


def solve_task(args):
    n, k, case, cube, tl, solver = args
    case = tuple(case)
    P = Psi(n, k, case, cube=[(tuple(kk), v) for kk, v in cube])
    dim = P.cnf.dimacs()
    sha = hashlib.sha256(dim.encode()).hexdigest()
    if solver == 'kissat':
        res, model, cpu, wall, rc = kissat(dim, timeout=tl)
    else:
        res, model, cpu, wall, rc = glucose(P.cnf.clauses, timeout=tl, name=solver)
    rec = {'case': list(case), 'cube': cube, 'result': res, 'cpu': round(cpu, 2), 'wall': round(wall, 2),
           'tl': tl, 'solver': solver, 'cnf_sha256': sha, 'vars': P.cnf.nv, 'clauses': len(P.cnf.clauses), 'rc': rc}
    if res == 'SAT':
        D = P.decode(model)
        rec['queens'] = D
        rec['n_queens'] = len(D)
        rec['dominating'] = CS.dominates(n, D)
        rec['case_of_set'] = CS.case_of_set(n, D)
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('n', type=int); ap.add_argument('k', type=int)
    ap.add_argument('cases'); ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=13)
    ap.add_argument('--tl', type=int, default=4000)
    ap.add_argument('--solver', default='kissat', help="kissat, or a PySAT solver name (e.g. glucose4)")
    ap.add_argument('--order', default=None, help='json {case-string: predicted seconds}, largest first')
    a = ap.parse_args()
    n, k = a.n, a.k
    clist = [tuple(json.loads(l)['case']) for l in open(a.cases) if l.strip()]
    valid = set(CS.case_list(n, k))
    assert all(c in valid for c in clist), 'case not in the independent case list'
    if a.order:
        pred = json.load(open(a.order))
        clist.sort(key=lambda c: -pred.get(json.dumps(list(c)), 0))
    done = {}
    if os.path.exists(a.out):
        for l in open(a.out):
            r = json.loads(l)
            if 'case' in r:
                done[cube_key(r['case'], r['cube'])] = r
    # frontier reconstruction
    pending = []
    for c in clist:
        stack = [[]]
        while stack:
            cube = stack.pop()
            r = done.get(cube_key(c, cube))
            if r is None:
                pending.append((c, cube))
            elif r['result'] == 'UNKNOWN':
                stack.extend(children(n, c, cube)[1])
            elif r['result'] == 'SAT':
                print('SAT record present for', c, cube, flush=True)
    print('cases %d, pending solver calls %d, records %d' % (len(clist), len(pending), len(done)), flush=True)
    fout = open(a.out, 'a')
    t0 = time.time()
    nsat = nuns = nunk = 0
    with mp.Pool(a.jobs) as pool:
        inflight = {}
        queue = list(pending)
        def submit():
            while queue and len(inflight) < a.jobs * 2:
                c, cube = queue.pop(0)
                inflight[cube_key(c, cube)] = pool.apply_async(solve_task, ((n, k, c, cube, a.tl, a.solver),))
        submit()
        while inflight:
            time.sleep(0.5)
            for key in [kk for kk, f in inflight.items() if f.ready()]:
                rec = inflight.pop(key).get()
                c, cube = tuple(rec['case']), rec['cube']
                if rec['result'] == 'UNKNOWN':
                    sv, ch = children(n, c, cube)
                    rec['split'] = [list(v) for v in sv]
                    queue[0:0] = [(c, x) for x in ch]          # children first (depth-first per case)
                    nunk += 1
                elif rec['result'] == 'SAT':
                    nsat += 1
                    print('!!! SAT', json.dumps(rec), flush=True)
                else:
                    nuns += 1
                fout.write(json.dumps(rec) + '\n'); fout.flush()
                if (nuns + nsat + nunk) % 50 == 0 or rec['cpu'] > 600 or rec['result'] != 'UNSAT':
                    print('%.0fs  UNSAT %d SAT %d split %d  queue %d  last %s %s %.0fs' % (
                        time.time() - t0, nuns, nsat, nunk, len(queue), c, rec['result'], rec['cpu']), flush=True)
            submit()
    print('finished: UNSAT %d SAT %d split %d wall %.0fs' % (nuns, nsat, nunk, time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
