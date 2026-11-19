#!/usr/bin/env python3
"""Rerun parts of the n = 28, g = 14 computation and compare with the committed records in data/n28/.

usage: run_n28.py ROOT JOBS OUT.json MODE [SEED]
  MODE sample : stage 1 on a seeded random sample of parts (3 for each z0 <= 3, 2 for each z0 = 4..7; for
                z0 = 6, 7 drawn among the parts whose recorded CPU time is below 60 s), the SAT stage-2 check
                on 40 seeded random survivors (not the z0 = 0 pair, which takes about 1.6 CPU hours), and the
                stage-1 DRAT certificate on 2 seeded random cubes for each z0 (for z0 = 7 among the cubes whose
                recorded time is below 120 s).  About 10 minutes on 3 cores.
  MODE heavy  : stage 1 on every part with z0 <= 5 and on 24 random parts with z0 = 6, 7; SAT + DRAT on
                2000 random survivors; the complete stage-1 certificate for z0 <= 6 and 40 random cubes for
                z0 = 7.  About 6 CPU hours.
At most JOBS processes run at once (each under nice 10).  The output JSON records, for every rerun item,
whether it reproduced the committed record exactly (SHA-256 of the stage-1 output, SAT result and CNF hash,
certificate CNF hash and result).  The full n = 28 stage 1 (about 80 CPU hours) is not rerun here.
"""
import hashlib, json, lzma, os, random, re, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve()
JOBS = int(sys.argv[2])
OUT = Path(sys.argv[3])
MODE = sys.argv[4]
SEED = int(sys.argv[5]) if len(sys.argv) > 5 else 2028
D = ROOT / 'data' / 'n28'
B = ROOT / 'build'
PY = sys.executable
NICE = ['nice', '-n', '10']
MODS = {z: (480 if z <= 4 else 4800) for z in range(8)}


def sh(cmd, inp=None):
    return subprocess.run(NICE + cmd, input=inp, capture_output=True, text=True, check=True)


def xz(name):
    return lzma.decompress((D / name).read_bytes()).decode()


def stage1_part(zp):
    z, p = zp
    r = sh([str(B / 'stage1'), '28', '14', str(z), str(p), str(MODS[z])])
    return (z, p), hashlib.sha256(r.stdout.encode()).hexdigest()


def tmpdir():
    t = OUT.parent / 'tmp'
    t.mkdir(parents=True, exist_ok=True)
    return tempfile.TemporaryDirectory(dir=t)


def sat_chunk(lines):
    with tmpdir() as td:
        r = sh([PY, str(ROOT / 'code' / 'sat_place.py'), '28', '14', str(ROOT / 'tools' / 'cadical'),
                str(ROOT / 'tools' / 'drat-trim'), td], ''.join(lines))
    return r.stdout.splitlines()


def main():
    t0 = time.time()
    rnd = random.Random(SEED)
    man = {}
    for l in open(D / 'MANIFEST'):
        k, h, c = l.split()
        man[(int(k[1]), int(k.split('_')[1]))] = h
    times = {}
    for l in xz('stage1_parts.txt.xz').splitlines():
        f = l.split()
        times[(int(f[2]), int(f[4]))] = float(re.search(r'time=([\d.]+)s', l).group(1))
    out = {'mode': MODE, 'seed': SEED}
    if MODE == 'sample':
        parts = [(z, p) for z in range(4) for p in rnd.sample(range(MODS[z]), 3)] + \
                [(z, p) for z in (4, 5) for p in rnd.sample(range(MODS[z]), 2)] + \
                [(z, p) for z in (6, 7) for p in rnd.sample(sorted(p for p in range(MODS[z]) if times[(z, p)] < 60), 2)]
    else:
        parts = [(z, p) for z in range(6) for p in range(MODS[z])] + \
                [(z, p) for z in (6, 7) for p in rnd.sample(range(MODS[z]), 12)]
    with ThreadPoolExecutor(JOBS) as ex:
        res = list(ex.map(stage1_part, parts))
    bad = ['z%d/part_%d' % k for k, h in res if man[k] != h]
    out['stage1_parts'] = len(res)
    out['stage1_parts_reproduced'] = len(res) - len(bad)
    out['stage1_mismatch'] = bad
    # SAT stage 2
    rec = {}
    for l in xz('sat_stage2.txt.xz').splitlines():
        p = l.split()
        rec[(p[1], p[2], p[3])] = (p[4], p[5], p[6])
    surv = [l + '\n' for l in xz('survivors.txt.xz').splitlines() if l.startswith('C ') and not l.endswith(' 0')]
    pick = rnd.sample(surv, 40 if MODE == 'sample' else 2000)
    chunks = [pick[i:i + 50] for i in range(0, len(pick), 50)]
    with ThreadPoolExecutor(JOBS) as ex:
        vl = [v for c in ex.map(sat_chunk, chunks) for v in c]
    agree = 0
    for v in vl:
        p = v.split()
        r = rec.get((p[1], p[2], p[3]))
        agree += bool(r and r == (p[4], p[5], p[6]) and p[4] == 'UNSAT' and p[5] == 'drat=VERIFIED')
    out['sat_rerun'] = len(vl)
    out['sat_reproduced'] = agree
    out['sat_expected'] = len(pick)
    # stage-1 certificate cubes
    sys.path.insert(0, str(ROOT / 'code'))
    import cert_stage1 as C
    from multiprocessing import Pool
    cube_ok = cube_n = 0
    with tmpdir() as td:
        survf = Path(td) / 'survivors.txt'
        survf.write_text(xz('survivors.txt.xz'))
        for z0 in range(8):
            recs = [json.loads(l) for l in open(D / ('cert_stage1_z%d.jsonl' % z0))]
            hdr, cubes = recs[0], {r['cube']: r for r in recs[1:]}
            keys = sorted(cubes)
            if MODE == 'sample':
                keys = rnd.sample(keys if z0 < 7 else [k for k in keys if cubes[k]['t_solve'] + cubes[k]['t_check'] < 120], 2)
            elif z0 == 7:
                keys = rnd.sample(keys, 40)
            cls, a, b, npairs = C.build_base(28, 14, z0, str(survf))
            wd = Path(td) / ('wd_%d' % z0)
            wd.mkdir()
            C._CTX.update(n=28, cls=cls, a=a, b=b, T=hdr['T'], cad=str(ROOT / 'tools' / 'cadical'),
                          drat=str(ROOT / 'tools' / 'drat-trim'), wd=str(wd))
            with Pool(JOBS) as P:
                for r in P.imap_unordered(C.solve_cube, [tuple(int(c) for c in k) for k in keys]):
                    cube_n += 1
                    old = cubes[r['cube']]
                    cube_ok += (r['cnf_sha256'] == old['cnf_sha256'] and r['result'] == 'UNSAT' and r['drat'] == 'VERIFIED')
    out['cert_cubes_rerun'] = cube_n
    out['cert_cubes_reproduced'] = cube_ok
    out['seconds'] = round(time.time() - t0, 1)
    OUT.write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps(out))


if __name__ == '__main__':
    main()
