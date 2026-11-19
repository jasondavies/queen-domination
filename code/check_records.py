#!/usr/bin/env python3
"""Consistency of the committed n = 26 records (data/n26/), without rerunning anything expensive.

  * stage1_parts.txt: one record per part, 480 parts for each z0 = 0..6; totals of nodes, survivors, CPU.
  * survivors.txt split by the per-part survivor counts reproduces the per-part SHA-256 of MANIFEST;
    stage2_place.txt split the same way reproduces the per-part SHA-256 of the stage-2 outputs.
  * stage 2 (place.c): one DONE line per survivor, no solution, no smaller set.
  * independent stage 1 (stage1_v.c): every part present; same orbit set as stage 1.
  * SAT stage 2: exactly one record per survivor, all UNSAT with drat-trim VERIFIED.
  * stage-1 certificate: for every z0, a header whose base-CNF hash equals the hash of the CNF rebuilt
    here from survivors.txt, and an UNSAT + VERIFIED record for every orbit representative cube.
Prints JSON."""
import collections, hashlib, json, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from refcheck import orbit_key
import cert_stage1 as C

D = Path(sys.argv[1])
H = lambda s: hashlib.sha256(s.encode()).hexdigest()


def main():
    out = {}
    man = [l.split() for l in open(D / 'MANIFEST')]
    parts = [l for l in open(D / 'stage1_parts.txt')]
    out['parts_per_z0'] = dict(collections.Counter(int(l.split()[2]) for l in parts))
    keys = [(int(l.split()[2]), int(l.split()[4])) for l in parts]
    out['parts_complete'] = sorted(keys) == [(z, p) for z in range(7) for p in range(480)] and keys == [(z, p) for z in range(7) for p in range(480)]
    agg = collections.defaultdict(collections.Counter)
    for l in parts:
        z = int(l.split()[2])
        agg[z]['cand'] += int(re.search(r'cand=(\d+)', l).group(1))
        agg[z]['sol'] += int(re.search(r'sol=(\d+)', l).group(1))
        agg[z]['nodes'] += int(re.search(r' nodes=(\d+)', l).group(1))
        agg[z]['ms'] += round(float(re.search(r'time=([\d.]+)s', l).group(1)) * 100)
    s2 = collections.defaultdict(collections.Counter)
    for l in open(D / 'stage2_logs.txt'):
        z = int(l[1])
        m = re.search(r'candidates=(\d+) nodes=(\d+) time=([\d.]+)s', l)
        s2[z]['cand'] += int(m.group(1)); s2[z]['nodes'] += int(m.group(2)); s2[z]['cs'] += round(float(m.group(3)) * 100)
    out['stage1'] = {z: {'pairs': a['cand'], 'sets': a['sol'], 'nodes': a['nodes'], 'cpu_s': a['ms'] / 100} for z, a in sorted(agg.items())}
    out['stage2'] = {z: {'pairs': a['cand'], 'nodes': a['nodes'], 'cpu_s': a['cs'] / 100} for z, a in sorted(s2.items())}
    surv = open(D / 'survivors.txt').read().splitlines(keepends=True)
    place = open(D / 'stage2_place.txt').read().splitlines(keepends=True)
    i = j = 0
    okc = okp = 0
    for (k, hc, hp, nc, ns) in man:
        nc = int(nc)
        okc += H(''.join(surv[i:i + nc])) == hc
        okp += H(''.join(place[j:j + nc])) == hp and ns == '0'
        i += nc; j += nc
    out['manifest_parts'] = len(man)
    out['manifest_cand_sha_ok'] = okc
    out['manifest_place_sha_ok'] = okp
    out['manifest_consumed_all'] = i == len(surv) and j == len(place)
    out['survivors_sha256'] = hashlib.sha256((D / 'survivors.txt').read_bytes()).hexdigest()
    S = [tuple(l.split()[1:4]) for l in surv]
    out['survivors'] = len(S)
    out['survivors_distinct'] = len(set(S))
    out['survivors_per_z0'] = dict(collections.Counter(int(s[2]) for s in S))
    done = [l.split() for l in place]
    out['place_done_all_zero'] = all(p[0] == 'DONE' and p[5] == '0' for p in done) and [tuple(p[1:4]) for p in done] == S
    # independent stage 1
    vparts = [l for l in open(D / 'stage1_v_parts.txt')]
    vk = collections.Counter()
    vnodes = 0; vcs = 0
    for l in vparts:
        z = int(re.search(r'z=\((\d+)', l).group(1)); p, m = map(int, re.search(r'part (\d+)/(\d+)', l).groups())
        vk[(z, m)] += 1 if p < m else 0
        vnodes += int(re.search(r'nodes=(\d+)', l).group(1)); vcs += round(float(re.search(r'time=([\d.]+)s', l).group(1)) * 100)
    out['stage1_v_parts_complete'] = (len(set((re.search(r'z=\((\d+)', l).group(1), re.search(r'part (\d+/\d+)', l).group(1)) for l in vparts)) == len(vparts)
                                      and all(vk[(z, 480 if z >= 5 else 24)] == (480 if z >= 5 else 24) for z in range(7)))
    out['stage1_v_nodes'] = vnodes
    out['stage1_v_cpu_s'] = vcs / 100
    V = [tuple(l.split()[1:4]) for l in open(D / 'survivors_v.txt') if l.startswith('C ')]
    orb = lambda L: set((orbit_key(int(a, 16), int(b, 16), 26), z) for a, b, z in L)
    out['stage1_v_orbits_equal'] = orb(V) == orb(S) and len(orb(S)) == len(S)
    # SAT stage 2
    sat = [l.split() for l in open(D / 'sat_stage2.txt')]
    out['sat_records'] = len(sat)
    out['sat_all_unsat_verified'] = all(p[4] == 'UNSAT' and p[5] == 'drat=VERIFIED' for p in sat)
    out['sat_covers_survivors'] = sorted(tuple(p[1:4]) for p in sat) == sorted(S)
    ts = sum(float(p[7][3:]) for p in sat); tc = sum(float(p[8][3:]) for p in sat)
    mono = [p for p in sat if p[3] == '0']
    out['sat_cpu'] = {'solve': round(ts, 1), 'check': round(tc, 1), 'mono_solve': float(mono[0][7][3:]), 'mono_check': float(mono[0][8][3:]),
                      'max_other_solve': max(float(p[7][3:]) for p in sat if p[3] != '0'), 'max_other_check': max(float(p[8][3:]) for p in sat if p[3] != '0')}
    # stage-1 certificate
    cert = {}
    for z0 in range(7):
        f = D / ('cert_stage1_z%d.jsonl' % z0)
        if not f.exists():
            cert[z0] = {'present': False}
            continue
        recs = [json.loads(l) for l in open(f)]
        hdr, cubes = recs[0], recs[1:]
        cls, a, b, npairs = C.build_base(26, 13, z0, str(D / 'survivors.txt'))
        reps = set(''.join(map(str, c)) for c in C.rep_cubes(hdr['T']))
        cert[z0] = {'present': True, 'T': hdr['T'], 'pairs': npairs, 'base_sha_ok': hdr['base_sha256'] == hashlib.sha256(repr(cls).encode()).hexdigest(),
                    'cube_reps': len(reps), 'cover_ok': C.check_cover(C.rep_cubes(hdr['T']), hdr['T']),
                    'all_reps_unsat_verified': set(r['cube'] for r in cubes) == reps and len(cubes) == len(reps)
                    and all(r['result'] == 'UNSAT' and r['drat'] == 'VERIFIED' for r in cubes),
                    'solve_s': round(sum(r['t_solve'] for r in cubes), 1), 'check_s': round(sum(r['t_check'] for r in cubes), 1),
                    'max_proof_bytes': max(r['proof_bytes'] for r in cubes), 'proof_bytes': sum(r['proof_bytes'] for r in cubes)}
    out['cert'] = cert
    # recorded validation runs n = 20, 22, 24 (g = n/2): every part present, no dominating set
    val = {}
    for n in (20, 22, 24):
        L = [l.split() for l in open(D.parent / 'validation' / ('n%d_parts.txt' % n))]
        keys = set((int(p[2]), int(p[4]), int(p[3])) for p in L)
        mods = {int(p[3]) for p in L}
        zs = sorted({int(p[2]) for p in L})
        val[n] = {'complete': len(mods) == 1 and zs == list(range(n // 4 + 1)) and len(L) == len(keys) == len(zs) * mods.pop(),
                  'pairs': sum(int(p[5][5:]) for p in L), 'sets': sum(int(p[6][4:]) for p in L)}
    out['validation'] = val
    print(json.dumps(out))


if __name__ == '__main__':
    main()
