#!/usr/bin/env python3
"""Work plan for n = 35, k = 18.

hard(c): cases sent straight to run_hard.py (symmetry breaking + adaptive cube splitting) instead of the plain
per-case run: all deficits 0, |w - h| <= 1 and the smaller margin sum <= 11 (measured: these take from minutes to
an hour or more each).  This is only a scheduling heuristic; it has no bearing on soundness.

`plan35.py write F`: writes to F (JSON lines {"case": [...], "start": L}) every case of the list that has no
UNSAT + DRAT-VERIFIED record yet in frame/out/d_35_18.jsonl / d_35_18_sq.jsonl, easiest first; start = 1 (begin with
the 16 cubes of layer 1 instead of the unsplit formula) for cases that already timed out unsplit and for square
zero-deficit cases with margin sum <= 9."""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from geom import cases_by_frame

N, K = 35, 18
OUT = os.environ.get('QD_FRAME_OUT', os.path.join(HERE, 'out'))     # uncompressed run records


def hard(c):
    hc, hr = c[0] + c[1], c[2] + c[3]
    return sum(c[4:]) == 0 and abs(hc - hr) <= 1 and min(hc, hr) <= 11


def plain_records():
    ok = set(); timed = set(); sat = []
    for fn in ('d_35_18.jsonl', 'd_35_18_sq.jsonl'):
        p = os.path.join(OUT, fn)
        if not os.path.exists(p):
            continue
        for l in open(p):
            try:
                r = json.loads(l)
            except ValueError:
                continue
            if 'case' not in r:
                continue
            c = tuple(r['case'])
            if r['result'] == 'UNSAT' and r.get('drat') == 'VERIFIED':
                ok.add(c)
            elif r['result'] == 'TIMEOUT':
                timed.add(c)
            elif r['result'] == 'SAT':
                sat.append(r)
    return ok, timed - ok, sat


if __name__ == '__main__':
    ok, timed, sat = plain_records()
    todo = [c for c in cases_by_frame(N, K) if c not in ok]
    def start(c):
        return 1 if (c in timed or (sum(c[4:]) == 0 and c[0] + c[1] == c[2] + c[3] and c[0] + c[1] <= 9)) else 0
    # easiest first: positive deficits, far from square, large margins
    todo.sort(key=lambda c: (start(c), -min(sum(c[4:]), 2), -abs((c[0] + c[1]) - (c[2] + c[3])), -min(c[0] + c[1], c[2] + c[3])))
    if len(sys.argv) > 2 and sys.argv[1] == 'write':
        with open(sys.argv[2], 'w') as f:
            for c in todo:
                f.write(json.dumps({'case': list(c), 'start': start(c)}) + '\n')
    print(json.dumps({'cases': len(cases_by_frame(N, K)), 'plain_verified': len(ok), 'plain_timeouts': len(timed), 'sat_records': len(sat),
                      'for_run_hard': len(todo), 'of_which_start_layer_1': sum(start(c) for c in todo)}))
