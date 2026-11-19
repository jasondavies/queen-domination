#!/usr/bin/env python3
"""Rerun (parts of) the n = 26, g = 13 computation and compare with the committed records in data/n26/.

usage: run_n26.py ROOT JOBS OUT.json MODE [SEED]
  MODE sample : stage 1 on a seeded random sample of parts (all of z0 <= 3 is cheap; a few of z0 = 4..6),
                stage 2 (place) on the survivors of the sampled parts, the SAT stage-2 check on a seeded
                sample of survivors, and the stage-1 DRAT certificate on a seeded sample of cubes.
  MODE full   : everything: stage 1 (all 7 x 480 parts), stage 2 on all survivors, independent stage 1
                (1080 parts), SAT + DRAT on all 10,888 survivors and the complete stage-1 certificate.
                About 12-15 CPU hours.
At most JOBS processes run at once (each under nice 10).  The output JSON records, for every rerun
item, whether it reproduced the committed record exactly (SHA-256 of program outputs, SAT results and
CNF hashes).
"""
import hashlib, json, os, random, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve()
JOBS = int(sys.argv[2])
OUT = Path(sys.argv[3])
MODE = sys.argv[4]
SEED = int(sys.argv[5]) if len(sys.argv) > 5 else 2026
D = ROOT / 'data' / 'n26'
B = ROOT / 'build'
PY = sys.executable
NICE = ['nice', '-n', '10']
MAN = {}


def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()


def sh(cmd, inp=None):
    return subprocess.run(NICE + cmd, input=inp, capture_output=True, text=True, check=True)


def manifest():
    m = {}
    for l in open(D / 'MANIFEST'):
        k, hc, hp, nc, ns = l.split()
        m[k] = (hc, hp, int(nc), int(ns))
    return m


def stage1_part(zp):
    z, p = zp
    r = sh([str(B / 'stage1'), '26', '13', str(z), str(p), '480'])
    # stage 2 on the part's survivors; skipped in sample mode for the part holding the monochromatic pair
    # (about 2 CPU hours of place.c), whose stage-2 record is then compared by its SAT check only
    if MODE == 'sample' and (z, p) == (0, 0):
        return 'z0/part_0', sha(r.stdout), MAN['z0/part_0'][1], r.stdout
    place = sh([str(B / 'place'), '26', '13'], r.stdout).stdout
    return 'z%d/part_%d' % (z, p), sha(r.stdout), sha(place), r.stdout


def stage1v_part(zpm):
    z, p, m = zpm
    r = sh([str(B / 'stage1_v'), '26', '13', str(z), str(p), str(m)])
    return r.stdout


def sat_chunk(lines):
    with __import__('tempfile').TemporaryDirectory() as td:
        r = sh([PY, str(ROOT / 'code' / 'sat_place.py'), '26', '13', str(ROOT / 'tools' / 'cadical'),
                str(ROOT / 'tools' / 'drat-trim'), td], ''.join(lines))
    return r.stdout.splitlines()


def sat_records():
    rec = {}
    for l in open(D / 'sat_stage2.txt'):
        p = l.split()
        rec[(p[1], p[2], p[3])] = (p[4], p[5], p[6])
    return rec


def main():
    t0 = time.time()
    rnd = random.Random(SEED)
    man = manifest()
    MAN.update(man)
    out = {'mode': MODE, 'seed': SEED}
    if MODE == 'sample':
        parts = [(0, 0)] + [(z, p) for z in range(4) for p in rnd.sample(range(1, 480), 6)] + \
                [(z, p) for z in (4, 5, 6) for p in rnd.sample(range(480), 2)]
    else:
        parts = [(z, p) for z in range(7) for p in range(480)]
    with ThreadPoolExecutor(JOBS) as ex:
        res = list(ex.map(stage1_part, parts))
    bad = [k for k, hc, hp, _ in res if man[k][:2] != (hc, hp)]
    out['stage1_parts'] = len(res)
    out['stage1_parts_reproduced'] = len(res) - len(bad)
    out['stage1_mismatch'] = bad
    if MODE == 'full':
        surv = ''.join(r[3] for r in sorted(res, key=lambda r: (int(r[0][1]), int(r[0].split('_')[1]))))
        out['survivors_sha256_equal'] = sha(surv) == hashlib.sha256((D / 'survivors.txt').read_bytes()).hexdigest()
        jobs = [(z, p, 480 if z >= 5 else 24) for z in range(7) for p in range(480 if z >= 5 else 24)]
        with ThreadPoolExecutor(JOBS) as ex:
            vout = ''.join(ex.map(stage1v_part, jobs))
        sys.path.insert(0, str(ROOT / 'code'))
        from refcheck import orbit_key
        orb = lambda txt: set((orbit_key(int(p[1], 16), int(p[2], 16), 26), p[3]) for p in (l.split() for l in txt.splitlines()) if p and p[0] == 'C')
        out['stage1_v_orbits_equal'] = orb(vout) == orb(surv)
        out['stage1_v_sha256_equal'] = sha(vout) == hashlib.sha256((D / 'survivors_v.txt').read_bytes()).hexdigest()
    # SAT stage 2
    surv_lines = [l for l in open(D / 'survivors.txt') if l.startswith('C ')]
    if MODE == 'sample':
        pick = [l for l in rnd.sample(surv_lines, 40) if not l.startswith('C 2aaaaaa 1555555 0')]
    else:
        pick = surv_lines
    chunks = [pick[i:i + 50] for i in range(0, len(pick), 50)]
    with ThreadPoolExecutor(JOBS) as ex:
        vl = [v for c in ex.map(sat_chunk, chunks) for v in c]
    rec = sat_records()
    agree = 0
    for v in vl:
        p = v.split()
        r = rec.get((p[1], p[2], p[3]))
        if r and r == (p[4], p[5], p[6]) and p[4] == 'UNSAT' and p[5] == 'drat=VERIFIED':
            agree += 1
    out['sat_rerun'] = len(vl)
    out['sat_reproduced'] = agree
    out['sat_expected'] = len(pick)
    # stage-1 certificate cubes
    sys.path.insert(0, str(ROOT / 'code'))
    import cert_stage1 as C
    cube_ok = cube_n = 0
    for z0 in range(7):
        recs = [json.loads(l) for l in open(D / ('cert_stage1_z%d.jsonl' % z0))]
        hdr, cubes = recs[0], {r['cube']: r for r in recs[1:]}
        T = hdr['T']
        keys = sorted(cubes)
        if MODE == 'sample':
            keys = rnd.sample(keys, 2 if z0 < 6 else 3)
        cls, a, b, npairs = C.build_base(26, 13, z0, str(D / 'survivors.txt'))
        wd = OUT.parent / ('cert_wd_%d' % z0)
        os.makedirs(wd, exist_ok=True)
        C._CTX.update(n=26, cls=cls, a=a, b=b, T=T, cad=str(ROOT / 'tools' / 'cadical'),
                      drat=str(ROOT / 'tools' / 'drat-trim'), wd=str(wd))
        from multiprocessing import Pool
        with Pool(JOBS) as P:
            for r in P.imap_unordered(C.solve_cube, [tuple(int(c) for c in k) for k in keys]):
                cube_n += 1
                old = cubes[r['cube']]
                cube_ok += (r['cnf_sha256'] == old['cnf_sha256'] and r['result'] == 'UNSAT' and r['drat'] == 'VERIFIED')
        os.rmdir(wd)
    out['cert_cubes_rerun'] = cube_n
    out['cert_cubes_reproduced'] = cube_ok
    out['seconds'] = round(time.time() - t0, 1)
    OUT.write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps(out))


if __name__ == '__main__':
    main()
