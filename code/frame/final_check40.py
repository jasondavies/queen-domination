#!/usr/bin/env python3
"""Final check for (n, k) = (40, 20) [or n k given as arguments]; used for n = 40, 42, 44, 46.

1. The case list is rebuilt from first principles, independently of geom.py: frames are boxes [a,b] x [c,d]
   whose images under the 8 board maps are computed geometrically (corner coordinates), canonical = the
   lexicographically least margin vector; deficit vectors admissible by PROOFS F.2 (each deficit in [0,k-1];
   ml+mr <= k-dC, mb+mt <= k-dR; w,h >= 1; (F) sum <= 4k-2n+2; (V) for w >= h: dT+dS+2dR <= 4k-2n+2[w=h];
   (H) for h >= w: dT+dS+2dC <= 4k-2n+2[w=h]).  The frame count is also checked by Burnside's lemma.
   The list must equal geom.cases_by_frame(n, k) as a set (and have no duplicates).
2. final_check35.py n k is run: every case refuted by a plain UNSAT + DRAT-VERIFIED record of d_N_K.jsonl or by a
   complete cover of UNSAT + VERIFIED run_hard cubes (h_N_K.jsonl), 0 SAT records, every CNF rebuilt and its
   SHA-256 compared with the record.
Exit 0 only if both parts pass.   usage: final_check40.py [n k] [--jobs 4] [--list-only]"""
import sys, os, json, subprocess
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)

nums = [a for a in sys.argv[1:] if a.isdigit()]
jobs = sys.argv[sys.argv.index('--jobs') + 1] if '--jobs' in sys.argv else '4'
if '--jobs' in sys.argv:
    nums.remove(jobs)
n, k = (int(nums[0]), int(nums[1])) if len(nums) >= 2 else (40, 20)

MAPS = [lambda x, y: (x, y), lambda x, y: (n - 1 - x, y), lambda x, y: (x, n - 1 - y), lambda x, y: (n - 1 - x, n - 1 - y),
        lambda x, y: (y, x), lambda x, y: (n - 1 - y, x), lambda x, y: (y, n - 1 - x), lambda x, y: (n - 1 - y, n - 1 - x)]
assert len({tuple(g(x, y) for x in range(3) for y in range(3)) for g in MAPS}) == 8


def margins_of_box(a, b, c, d):
    return (a, n - 1 - b, c, n - 1 - d)


def frame_images(f):
    ml, mr, mb, mt = f
    a, b, c, d = ml, n - 1 - mr, mb, n - 1 - mt
    out = []
    for g in MAPS:
        pts = [g(x, y) for x in (a, b) for y in (c, d)]
        xs = [p[0] for p in pts]; ys = [p[1] for p in pts]
        out.append(margins_of_box(min(xs), max(xs), min(ys), max(ys)))
    return out


frames = []
allf = []
for ml in range(k + 1):
    for mr in range(k + 1 - ml):
        for mb in range(k + 1):
            for mt in range(k + 1 - mb):
                if n - 1 - ml - mr >= 1 and n - 1 - mb - mt >= 1:
                    f = (ml, mr, mb, mt); allf.append(f)
                    if f == min(frame_images(f)):
                        frames.append(f)
# Burnside: number of orbits = average number of fixed frames
fixed = sum(sum(1 for f in allf if frame_images(f)[i] == f) for i in range(8))
assert fixed % 8 == 0 and fixed // 8 == len(frames), (fixed, len(frames))

cases = []
for f in frames:
    ml, mr, mb, mt = f
    w, h = n - 1 - ml - mr, n - 1 - mb - mt
    sl = 4 * k - 2 * n + 2
    for dR in range(k):
        for dC in range(k):
            for dT in range(k):
                for dS in range(k):
                    if ml + mr > k - dC or mb + mt > k - dR:
                        continue
                    if dR + dC + dT + dS > sl:
                        continue
                    sq = 2 if w == h else 0
                    if w >= h and dT + dS + 2 * dR > 4 * k - 2 * n + sq:
                        continue
                    if h >= w and dT + dS + 2 * dC > 4 * k - 2 * n + sq:
                        continue
                    cases.append(f + (dR, dC, dT, dS))
from geom import cases_by_frame
G = cases_by_frame(n, k)
part1 = {'frames_independent': len(frames), 'burnside_orbits': fixed // 8, 'cases_independent': len(cases), 'cases_geom': len(G),
         'no_duplicates': len(set(G)) == len(G) and len(set(cases)) == len(cases), 'equal_as_sets': set(G) == set(cases)}
part1['ok'] = part1['no_duplicates'] and part1['equal_as_sets']
print(json.dumps({'case_list_check': part1}), flush=True)
if '--list-only' in sys.argv:
    sys.exit(0 if part1['ok'] else 1)
r = subprocess.run([sys.executable, os.path.join(HERE, 'final_check35.py'), str(n), str(k), '--jobs', jobs], capture_output=True, text=True)
print(r.stdout.strip()); sys.stderr.write(r.stderr)
ok = part1['ok'] and r.returncode == 0
print(json.dumps({'FINAL': 'PASS' if ok else 'FAIL'}))
sys.exit(0 if ok else 1)
