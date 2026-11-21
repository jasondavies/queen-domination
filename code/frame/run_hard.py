#!/usr/bin/env python3
"""Certified runs of hard cases with residual symmetry breaking and adaptive cube splitting.

For every selected case the formula is Phi(case) (enc.py, default options) AND SBP(case) (lex-leader over the
board symmetries fixing the case; hard_test.sbp_clauses; PROOFS F.6).  A cube fixes, for layers j = 1..L, the four
variables oR[c+j], oR[d-j], oC[a+j], oC[b-j].  The empty cube is tried first; a cube that exceeds --tl seconds is
replaced by its 16 children of the next layer.  Every UNSAT cube has its DRAT proof checked by drat-trim.
Records: one JSON line per solved cube {case, cube, cnf_sha256, result, drat, t_solve, t_check, proof_bytes}.
check_hard.py verifies that the UNSAT/VERIFIED cubes of a case cover it.
usage: run_hard.py n k --select square0|squaredef|all [--only "ml mr mb mt dR dC dT dS"] --tl 600 --jobs 6 --out F [--no-sbp] [--resume] [--maxlayer 4]
"""
import argparse, json, os, resource, subprocess, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from geom import cases_by_frame, case_of, dominated
import enc
from hard_test import sbp_clauses, stabiliser
CAD = os.path.join(HERE, '..', '..', 'tools', 'cadical'); DRAT = os.path.join(HERE, '..', '..', 'tools', 'drat-trim')
_A = {}; _B = {}


def layer_vars(base, case, j):
    n = base.n; ml, mr, mb, mt = case[:4]
    a, b, c, d = ml, n - 1 - mr, mb, n - 1 - mt
    if not (c + j < d - j and a + j < b - j):
        return None
    return [base.oR[c + j], base.oR[d - j], base.oC[a + j], base.oC[b - j]]


def build(case, cube):
    n, k = _A['n'], _A['k']
    if case[4:] not in _B:
        _B.clear(); _B[case[4:]] = enc.Base(n, k, case[4:])
    B = _B[case[4:]]
    extra, nv = enc.case_extra(B, case)
    top = [nv]
    def new():
        top[0] += 1
        return top[0]
    if _A['sbp']:
        extra = extra + sbp_clauses(B, case, new)
    units = []
    for j in range(len(cube) // 4):
        vs = layer_vars(B, case, j + 1)
        units += [[v] if bit == '1' else [-v] for v, bit in zip(vs, cube[4 * j:4 * j + 4])]
    return B, enc.dimacs(B, extra + units, top[0])


def cpu():
    r = resource.getrusage(resource.RUSAGE_CHILDREN)
    return r.ru_utime + r.ru_stime


def work(arg):
    case, cube = arg
    n, k = _A['n'], _A['k']
    B, txt = build(case, cube)
    rec = {'case': list(case), 'cube': cube, 'sbp': _A['sbp'], 'cnf_sha256': enc.sha(txt)}
    tag = '_'.join(map(str, case)) + '-' + (cube or 'root')
    fc = os.path.join(_A['wd'], tag + '.cnf'); fp = os.path.join(_A['wd'], tag + '.drat')
    open(fc, 'w').write(txt)
    c0 = cpu()
    r = subprocess.run(['nice', '-n', '10', CAD, '-q', '-t', str(_A['tl']), fc, fp], capture_output=True, text=True)
    c1 = cpu()
    rec['result'] = {10: 'SAT', 20: 'UNSAT', 0: 'TIMEOUT'}.get(r.returncode, 'ERR%d' % r.returncode)
    rec['t_solve'] = round(c1 - c0, 2)
    if rec['result'] == 'UNSAT':
        rec['proof_bytes'] = os.path.getsize(fp)
        dchk = subprocess.run(['nice', '-n', '10', DRAT, fc, fp, '-w', '-t', '1000000'], capture_output=True, text=True)
        rec['drat'] = 'VERIFIED' if 's VERIFIED' in dchk.stdout else 'FAILED'
        rec['t_check'] = round(cpu() - c1, 2)
    elif rec['result'] == 'SAT':
        pos = set(int(t) for l in r.stdout.splitlines() if l.startswith('v ') for t in l.split()[1:] if int(t) > 0)
        D = sorted((x, y) for x in range(n) for y in range(n) if B.q[x][y] in pos)
        rec['model'] = D; rec['model_ok'] = len(D) == k and dominated(n, D) and case_of(n, D) == case
    for f in (fc, fp):
        if os.path.exists(f):
            os.remove(f)
    return rec


def init(n, k, tl, wd, sbp):
    _A.update(n=n, k=k, tl=tl, wd=wd, sbp=sbp)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('n', type=int); ap.add_argument('k', type=int)
    ap.add_argument('--select', default='square0'); ap.add_argument('--only', default='')
    ap.add_argument('--tl', type=int, default=600); ap.add_argument('--jobs', type=int, default=6)
    ap.add_argument('--out', required=True); ap.add_argument('--no-sbp', action='store_true')
    ap.add_argument('--resume', action='store_true'); ap.add_argument('--maxlayer', type=int, default=4)
    ap.add_argument('--minh', type=int, default=0, help='only cases with ml + mr >= this (easy-first passes)')
    ap.add_argument('--cases-file', default='', help='JSON lines {"case": [...], "start": L}: run exactly these cases, in this order; start = 1: begin with the 16 cubes of layer 1')
    a = ap.parse_args()
    sq = lambda c: c[0] + c[1] == c[2] + c[3]
    pick = {'square0': lambda c: sq(c) and sum(c[4:]) == 0, 'squaredef': lambda c: sq(c) and sum(c[4:]) > 0, 'all': lambda c: True}[a.select]
    startlayer = {}
    if a.cases_file:
        cases = []
        for l in open(a.cases_file):
            r = json.loads(l); cases.append(tuple(r['case'])); startlayer[tuple(r['case'])] = r.get('start', 0)
    elif a.only:
        cases = [tuple(map(int, a.only.split()))]
    else:
        cases = [c for c in cases_by_frame(a.n, a.k) if pick(c) and c[0] + c[1] >= a.minh]
    wd = a.out + '.wd'; os.makedirs(wd, exist_ok=True)
    init(a.n, a.k, a.tl, wd, not a.no_sbp)
    done = {}
    if a.resume and os.path.exists(a.out):
        for l in open(a.out):
            try:
                r = json.loads(l)
            except ValueError:
                continue
            if 'cube' in r:
                done[(tuple(r['case']), r['cube'])] = r
    final = lambda r: r['result'] == 'SAT' or (r['result'] == 'UNSAT' and r.get('drat') == 'VERIFIED')
    todo = []
    def expand(case, cube):
        r = done.get((case, cube))
        if r is not None and final(r):
            return
        ch = children(case, cube)
        if r is None and cube == '' and startlayer.get(case, 0) >= 1 and ch:
            for c2 in ch:
                expand(case, c2)
            return
        if r is not None and r['result'] == 'TIMEOUT' and ch and (r.get('tl', 0) >= a.tl or any((case, c2) in done for c2 in ch)):
            for c2 in ch:          # already split (or the old limit was at least the new one): work on the children
                expand(case, c2)
            return
        todo.append((case, cube))  # new cube, or a timed-out cube that cannot be split / was not split: (re)run it
    def children(case, cube):
        j = len(cube) // 4 + 1
        B = enc.Base(a.n, a.k, case[4:]) if False else None
        ml, mr, mb, mt = case[:4]; aa, bb, cc, dd = ml, a.n - 1 - mr, mb, a.n - 1 - mt
        if j > a.maxlayer or not (cc + j < dd - j and aa + j < bb - j):
            return []
        return [cube + format(i, '04b') for i in range(16)]
    for c in cases:
        expand(c, '')
    st = {'n': a.n, 'k': a.k, 'cases': len(cases), 'sbp': not a.no_sbp, 'tl': a.tl, 'cubes_run': 0, 'UNSAT': 0, 'verified': 0, 'SAT': 0,
          'TIMEOUT': 0, 'unsplittable_timeouts': 0, 't_solve': 0.0, 't_check': 0.0}
    t0 = time.time()
    with open(a.out, 'a' if a.resume else 'w') as f, Pool(a.jobs, initializer=init, initargs=(a.n, a.k, a.tl, wd, not a.no_sbp)) as P:
        while todo:
            nxt = []
            for rec in P.imap_unordered(work, todo, chunksize=1):
                rec['tl'] = a.tl
                f.write(json.dumps(rec) + '\n'); f.flush()
                st['cubes_run'] += 1; st[rec['result']] = st.get(rec['result'], 0) + 1
                st['verified'] += rec.get('drat') == 'VERIFIED'
                st['t_solve'] += rec['t_solve']; st['t_check'] += rec.get('t_check', 0)
                if rec['result'] == 'TIMEOUT':
                    ch = children(tuple(rec['case']), rec['cube'])
                    if not ch:
                        st['unsplittable_timeouts'] += 1
                    nxt += [(tuple(rec['case']), c) for c in ch]
                if rec['result'] == 'SAT':
                    print('*** SAT', json.dumps(rec), flush=True)
                    f.write(json.dumps({'summary': st, 'stopped_on_sat': True}) + '\n'); f.flush()
                    P.terminate()
                    sys.exit(10)
            todo = nxt
        st['wall'] = round(time.time() - t0, 1); st['t_solve'] = round(st['t_solve'], 1); st['t_check'] = round(st['t_check'], 1)
        f.write(json.dumps({'summary': st}) + '\n')
    print(json.dumps(st))


if __name__ == '__main__':
    main()
