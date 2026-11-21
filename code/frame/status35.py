#!/usr/bin/env python3
"""Coverage of the certified n = 35, k = 18 runs so far: frame/out/d_35_18.jsonl (non-square cases, run_cases.py),
d_35_18_sq.jsonl (square cases with a positive deficit, run_cases.py) and h_35_18.jsonl (square zero-deficit cases,
run_hard.py with symmetry breaking; root cubes only).   usage: status35.py"""
import sys, os, json, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import cases_by_frame
path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out', 'd_35_18.jsonl')
n, k = 35, 18
cases = cases_by_frame(n, k)
rec = {}
D = os.path.dirname(path)
files = [path] + [os.path.join(D, f) for f in ('d_35_18_sq.jsonl', 'h_35_18.jsonl') if os.path.exists(os.path.join(D, f)) and len(sys.argv) <= 1]
for fn in files:
    for l in open(fn):
        try:
            r = json.loads(l)
        except ValueError:
            continue
        if 'case' in r and r.get('cube', '') == '':        # h_35_18.jsonl: only unsplit (root-cube) records count here
            c = tuple(r['case'])
            if c not in rec or r['result'] in ('SAT', 'UNSAT'):
                rec[c] = r
cls = lambda c: ('square' if c[0] + c[1] == c[2] + c[3] else 'non-square, |w-h| <= 5' if abs(c[0] + c[1] - c[2] - c[3]) <= 5 else 'non-square, |w-h| >= 6',
                 'deficits 0' if sum(c[4:]) == 0 else 'deficit sum >= 1')
tab = collections.OrderedDict()
for c in cases:
    t = tab.setdefault(cls(c), collections.Counter())
    t['cases'] += 1
    r = rec.get(c)
    if r is None:
        t['not run'] += 1
    elif r['result'] == 'UNSAT' and r.get('drat') == 'VERIFIED':
        t['UNSAT verified'] += 1; t['cpu'] += r['t_solve'] + r.get('t_check', 0)
    elif r['result'] == 'SAT':
        t['SAT'] += 1
    else:
        t['timeout/other'] += 1
tot = collections.Counter()
for key in sorted(tab):
    t = tab[key]; tot.update(t)
    print('%-26s %-18s cases %6d  UNSAT+DRAT verified %6d  SAT %d  timeout(300 s) %4d  not run %6d  CPU-h %.2f' % (
        key[0], key[1], t['cases'], t['UNSAT verified'], t['SAT'], t['timeout/other'], t['not run'], t['cpu'] / 3600))
print('TOTAL: cases %d, UNSAT+DRAT verified %d (%.1f%%), SAT %d, timeouts %d, not run %d, CPU-h %.2f' % (
    tot['cases'], tot['UNSAT verified'], 100.0 * tot['UNSAT verified'] / tot['cases'], tot['SAT'], tot['timeout/other'], tot['not run'], tot['cpu'] / 3600))
