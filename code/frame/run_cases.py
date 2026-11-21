#!/usr/bin/env python3
"""Run all cases of the frame method for (n, k).

 --mode pysat : in-process CaDiCaL (PySAT), verdict only; a model is decoded and checked.
 --mode drat  : CaDiCaL binary writes a DRAT proof, drat-trim checks it, the proof is deleted;
                the record keeps the SHA-256 of the exact CNF text, verdict, checker status, times.
Records: one JSON line per case in --out; a summary line at the end.  Resumable (--resume): cases whose
record exists with the same CNF hash and a final verdict are skipped (the CNF is rebuilt and re-hashed).
usage: run_cases.py n k --mode pysat|drat --jobs 6 --out out.jsonl [--stop-on-sat] [--limit N] [--no-F --no-V --no-H]
"""
import argparse, json, os, resource, subprocess, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from geom import cases_by_frame, case_of, dominated
import enc
if os.environ.get('QD_ENC') == 'b':
    import enc_b as enc_alt
    enc.Base, enc.case_extra = enc_alt.Base, enc_alt.case_extra      # second encoding (pysat mode / tests only)

CAD = os.path.join(HERE, '..', '..', 'tools', 'cadical')
DRAT = os.path.join(HERE, '..', '..', 'tools', 'drat-trim')
_B = {}
_A = {}


def init(n, k, mode, wd, kw, tl=0):
    _A.update(n=n, k=k, mode=mode, wd=wd, kw=kw, tl=tl)
    os.nice(10)


def base(dv):
    if dv not in _B:
        _B[dv] = enc.Base(_A['n'], _A['k'], dv)
    return _B[dv]


def cpu_children():
    r = resource.getrusage(resource.RUSAGE_CHILDREN)
    return r.ru_utime + r.ru_stime


def work(case):
    n, k = _A['n'], _A['k']
    B = base(case[4:])
    extra, nv = enc.case_extra(B, case, **_A['kw'])
    rec = {'case': list(case)}
    if _A['mode'] == 'pysat':
        from pysat.solvers import Solver
        t0 = time.process_time()
        with Solver(name=os.environ.get('QD_SOLVER', 'cadical195'), bootstrap_with=B.cls + extra) as S:
            sat = S.solve()
            if sat:
                m = S.get_model()
                D = sorted((x, y) for x in range(n) for y in range(n) if m[B.q[x][y] - 1] > 0)
                assert len(D) == k and dominated(n, D) and case_of(n, D) == case
                rec['model'] = D
        rec['result'] = 'SAT' if sat else 'UNSAT'
        rec['t'] = round(time.process_time() - t0, 3)
        return rec
    txt = enc.dimacs(B, extra, nv)
    rec['cnf_sha256'] = enc.sha(txt)
    tag = '_'.join(map(str, case))
    fc = os.path.join(_A['wd'], tag + '.cnf'); fp = os.path.join(_A['wd'], tag + '.drat')
    with open(fc, 'w') as f:
        f.write(txt)
    c0 = cpu_children()
    r = subprocess.run([CAD, '-q'] + (['-t', str(_A['tl'])] if _A.get('tl') else []) + [fc, fp], capture_output=True, text=True)
    c1 = cpu_children()
    rec['result'] = {10: 'SAT', 20: 'UNSAT', 0: 'TIMEOUT'}.get(r.returncode, 'ERR%d' % r.returncode)
    rec['t_solve'] = round(c1 - c0, 3)
    if rec['result'] == 'UNSAT':
        rec['proof_bytes'] = os.path.getsize(fp)
        d = subprocess.run([DRAT, fc, fp, '-w', '-t', '1000000'], capture_output=True, text=True)
        rec['drat'] = 'VERIFIED' if 's VERIFIED' in d.stdout else 'FAILED'
        rec['t_check'] = round(cpu_children() - c1, 3)
    elif rec['result'] == 'SAT':
        lits = [int(t) for l in r.stdout.splitlines() if l.startswith('v ') for t in l.split()[1:]]
        pos = set(l for l in lits if l > 0)
        D = sorted((x, y) for x in range(n) for y in range(n) if B.q[x][y] in pos)
        rec['model'] = D
        rec['model_ok'] = len(D) == k and dominated(n, D) and case_of(n, D) == case
    for f in (fc, fp):
        if os.path.exists(f):
            os.remove(f)
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('n', type=int); ap.add_argument('k', type=int)
    ap.add_argument('--mode', default='pysat'); ap.add_argument('--jobs', type=int, default=6)
    ap.add_argument('--out', required=True); ap.add_argument('--stop-on-sat', action='store_true')
    ap.add_argument('--limit', type=int, default=0); ap.add_argument('--resume', action='store_true')
    ap.add_argument('--tl', type=int, default=0, help='drat mode: wall-clock limit per case in seconds (TIMEOUT records are redone by --resume)')
    ap.add_argument('--order', default='list', help='list | easy')
    ap.add_argument('--skip-hard35', action='store_true', help='leave the cases with plan35.hard(c) to run_hard.py')
    ap.add_argument('--select', default='all', help='all | square | nonsquare | squaredef | square0  (subset of the case list to run now)')
    ap.add_argument('--no-F', action='store_true'); ap.add_argument('--no-V', action='store_true'); ap.add_argument('--no-H', action='store_true')
    a = ap.parse_args()
    kw = dict(use_F=not a.no_F, use_V=not a.no_V, use_H=not a.no_H)
    cases = cases_by_frame(a.n, a.k)
    ncases = len(cases); nframes = len({c[:4] for c in cases})
    done = {}
    if a.resume and os.path.exists(a.out):
        for l in open(a.out):
            try:
                r = json.loads(l)
            except ValueError:
                continue
            if 'case' in r and (r.get('result') == 'SAT' or (r.get('result') == 'UNSAT' and (a.mode != 'drat' or r.get('drat') == 'VERIFIED'))):
                done[tuple(r['case'])] = r
    todo = [c for c in cases if c not in done]
    if a.select != 'all':
        sq = lambda c: (c[0] + c[1]) == (c[2] + c[3])
        pick = {'square': sq, 'nonsquare': lambda c: not sq(c), 'squaredef': lambda c: sq(c) and sum(c[4:]) > 0,
                'square0': lambda c: sq(c) and sum(c[4:]) == 0}[a.select]
        todo = [c for c in todo if pick(c)]
    if a.skip_hard35:
        import plan35
        todo = [c for c in todo if not plan35.hard(c)]
    if a.order == 'easy':      # cheapest first: far-from-square boxes, large deficits, large margins (heuristic; affects order only)
        todo.sort(key=lambda c: (-min(abs((c[0] + c[1]) - (c[2] + c[3])), 8), -min(sum(c[4:]), 2), -sum(c[:4])))
    if a.limit:
        todo = todo[:a.limit]
    wd = a.out + '.wd'
    os.makedirs(wd, exist_ok=True)
    t0 = time.time()
    st = {'n': a.n, 'k': a.k, 'mode': a.mode, 'frames': nframes, 'cases': ncases, 'reused': len(done), 'run': 0, 'SAT': 0, 'UNSAT': 0,
          'verified': 0, 'other': 0, 't_solve': 0.0, 't_check': 0.0, 'proof_bytes': 0, 'max_t_solve': 0.0, 'constraints': kw}
    for r in done.values():
        st[r['result']] += 1; st['verified'] += r.get('drat') == 'VERIFIED'
    first_sat = None
    with open(a.out, 'a' if a.resume else 'w') as f, Pool(a.jobs, initializer=init, initargs=(a.n, a.k, a.mode, wd, kw, a.tl)) as P:
        for rec in P.imap_unordered(work, todo, chunksize=1):
            f.write(json.dumps(rec) + '\n'); f.flush()
            st['run'] += 1
            if rec['result'] in ('SAT', 'UNSAT'):
                st[rec['result']] += 1
            else:
                st['other'] += 1
            st['verified'] += rec.get('drat') == 'VERIFIED'
            ts = rec.get('t_solve', rec.get('t', 0))
            st['t_solve'] += ts; st['t_check'] += rec.get('t_check', 0); st['proof_bytes'] += rec.get('proof_bytes', 0)
            st['max_t_solve'] = max(st['max_t_solve'], ts)
            if rec['result'] == 'SAT' and first_sat is None:
                first_sat = rec
                if a.stop_on_sat:
                    P.terminate()
                    break
        st['wall'] = round(time.time() - t0, 1)
        st['t_solve'] = round(st['t_solve'], 1); st['t_check'] = round(st['t_check'], 1)
        st['complete'] = (st['SAT'] + st['UNSAT'] == ncases)
        st['verdict'] = 'SAT' if st['SAT'] else ('UNSAT' if st['complete'] and st['other'] == 0 else 'INCOMPLETE')
        if a.mode == 'drat' and st['verdict'] == 'UNSAT':
            st['all_proofs_verified'] = st['verified'] == ncases
        if first_sat:
            st['example'] = first_sat['model']
        f.write(json.dumps({'summary': st}) + '\n')
    print(json.dumps(st))


if __name__ == '__main__':
    main()
