#!/usr/bin/env python3
"""Experiments on hard cases: residual symmetry breaking and cube splitting.

  --sbp        lex-leader on v = (oR[0..n-1], oC[0..n-1]) for every board symmetry that fixes the case
               (frame and deficit vector), PROOFS F.6
  --split X    u0v0  : 4 cubes on the occupancy of the two box diagonals
               rc1   : 16 cubes on oR[c+1], oR[d-1], oC[a+1], oC[b-1];   rc2: 256 cubes (two layers)
               u0v0rc1: both (64 cubes)
Each cube is solved by the CaDiCaL binary (CPU time measured); prints total, max and number of cubes.
usage: hard_test.py n k ml mr mb mt dR dC dT dS [--sbp] [--split X] [--tl SEC]"""
import sys, os, itertools, subprocess, resource, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from geom import case_images
import enc
CAD = os.path.join(HERE, '..', '..', 'tools', 'cadical')
TMP = os.path.join(HERE, 'out', 'hard_tmp')


def stabiliser(case):
    return [g for g, img in enumerate(case_images(case)) if img == case]


def sbp_clauses(base, case, new):
    n = base.n; m = n - 1
    oR, oC = base.oR, base.oC
    img = {1: lambda: ([oR[i] for i in range(n)], [oC[m - i] for i in range(n)]),
           2: lambda: ([oR[m - i] for i in range(n)], [oC[i] for i in range(n)]),
           3: lambda: ([oR[m - i] for i in range(n)], [oC[m - i] for i in range(n)]),
           4: lambda: ([oC[i] for i in range(n)], [oR[i] for i in range(n)]),
           5: lambda: ([oC[i] for i in range(n)], [oR[m - i] for i in range(n)]),
           6: lambda: ([oC[m - i] for i in range(n)], [oR[i] for i in range(n)]),
           7: lambda: ([oC[m - i] for i in range(n)], [oR[m - i] for i in range(n)])}
    v = list(oR) + list(oC)
    cls = []
    for g in stabiliser(case):
        if g == 0:
            continue
        r, c = img[g](); u = r + c
        e = None
        for i in range(len(v)):
            if v[i] == u[i]:
                continue
            pre = [] if e is None else [-e]
            cls.append(pre + [-v[i], u[i]])
            if i < len(v) - 1:
                e2 = new()
                cls.append(pre + [-v[i], -u[i], e2]); cls.append(pre + [v[i], u[i], e2])
                e = e2
    return cls


def cubes(base, case, how):
    n = base.n
    ml, mr, mb, mt = case[:4]
    a, b, c, d = ml, n - 1 - mr, mb, n - 1 - mt
    groups = []
    if 'u0v0' in how:
        groups += [base.oT[c - a], base.oS[a + d]]
    if 'rc1' in how or 'rc2' in how:
        groups += [base.oR[c + 1], base.oR[d - 1], base.oC[a + 1], base.oC[b - 1]]
    if 'rc2' in how:
        groups += [base.oR[c + 2], base.oR[d - 2], base.oC[a + 2], base.oC[b - 2]]
    return [[v if bit else -v for v, bit in zip(groups, bits)] for bits in itertools.product((0, 1), repeat=len(groups))]


def main():
    a = sys.argv[1:]
    n, k = int(a[0]), int(a[1]); case = tuple(map(int, a[2:10]))
    sbp = '--sbp' in a
    how = a[a.index('--split') + 1] if '--split' in a else ''
    tl = a[a.index('--tl') + 1] if '--tl' in a else None
    B = enc.Base(n, k, case[4:])
    extra, nv = enc.case_extra(B, case)
    top = [nv]
    def new():
        top[0] += 1
        return top[0]
    if sbp:
        extra = extra + sbp_clauses(B, case, new)
    cs = cubes(B, case, how) if how else [[]]
    tot = 0; mx = 0; res = {}
    os.makedirs(TMP, exist_ok=True)
    for i, cube in enumerate(cs):
        f = os.path.join(TMP, '%d_%s_%d.cnf' % (os.getpid(), '_'.join(map(str, case)), i))
        open(f, 'w').write(enc.dimacs(B, extra + [[l] for l in cube], top[0]))
        r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
        r = subprocess.run(['nice', '-n', '10', CAD, '-q'] + (['-t', tl] if tl else []) + [f], capture_output=True)
        r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
        os.remove(f)
        t = r1.ru_utime - r0.ru_utime; tot += t; mx = max(mx, t)
        v = {10: 'SAT', 20: 'UNSAT'}.get(r.returncode, 'TIMEOUT'); res[v] = res.get(v, 0) + 1
    print(json.dumps({'n': n, 'k': k, 'case': case, 'stabiliser': stabiliser(case), 'sbp': sbp, 'split': how or None, 'cubes': len(cs),
                      'results': res, 'cpu_total': round(tot, 1), 'cpu_max': round(mx, 1)}), flush=True)


if __name__ == '__main__':
    main()
