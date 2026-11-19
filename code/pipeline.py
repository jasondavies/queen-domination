#!/usr/bin/env python3
"""Run the two-stage pipeline (build/stage1, build/place) for one (n, g) and summarise it as JSON.

usage: pipeline.py BUILD_DIR N G [--xcheck]
  For every z0 = 0..floor(g/2): stage1 N G z0 (canonical feasible pairs), then place N G on them.
  Output: pairs per z0, number of g-dominating sets found, number of classes under the dihedral group
  and how many of those are monochromatic.
  --xcheck: also run build/stage1_v (independent stage 1) and, for N <= 12, build/brute_ab (all pairs, no
  pruning, no symmetry), and compare the orbit sets with those of stage1.
"""
import json, subprocess, sys, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from refcheck import orbit_key, d4_key


def run(cmd, inp=None):
    return subprocess.run(cmd, input=inp, capture_output=True, text=True, check=True).stdout


def orbits(text, n):
    return set(orbit_key(int(p[1], 16), int(p[2], 16), n) for p in (l.split() for l in text.splitlines()) if p and p[0] == 'C')


def main():
    bd, n, g = Path(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    xcheck = '--xcheck' in sys.argv
    t0 = time.time()
    out = {'n': n, 'g': g, 'pairs': {}, 'xcheck': {}}
    sets, classes = 0, set()
    for z0 in range(g // 2 + 1):
        cand = run([str(bd / 'stage1'), str(n), str(g), str(z0)])
        out['pairs'][z0] = sum(1 for l in cand.splitlines() if l.startswith('C '))
        place = run([str(bd / 'place'), str(n), str(g)], cand)
        done = [l for l in place.splitlines() if l.startswith('DONE')]
        assert len(done) == out['pairs'][z0]
        assert not any(l.startswith('SMALLER') for l in place.splitlines())
        for l in place.splitlines():
            if l.startswith('SOL'):
                v = list(map(int, l.split()[2:]))
                classes.add(d4_key([(v[2 * i], v[2 * i + 1]) for i in range(g)], n))
                sets += 1
        if xcheck:
            mine = orbits(cand, n)
            rec = {'stage1_v': orbits(run([str(bd / 'stage1_v'), str(n), str(g), str(z0)]), n) == mine}
            if n <= 12:
                rec['brute'] = orbits(run([str(bd / 'brute_ab'), str(n), str(g), str(z0)]), n) == mine
            out['xcheck'][z0] = rec
    out['sets'] = sets
    out['classes'] = len(classes)
    out['monochromatic'] = sum(1 for D in classes if len(set((r + x) % 2 for r, x in D)) == 1)
    out['seconds'] = round(time.time() - t0, 1)
    print(json.dumps(out))


if __name__ == '__main__':
    main()
