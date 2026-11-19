#!/usr/bin/env python3
"""Consistency of the committed n = 28 records (data/n28/), without rerunning anything expensive.

  * stage1_parts.txt.xz: one record per part (480 parts for each z0 = 0..4, 4800 for each z0 = 5..7),
    with totals of nodes, survivors and CPU time per z0, and where the part ran (local or cloud).
  * MANIFEST: survivors.txt.xz, split by the per-part survivor counts in MANIFEST order, reproduces the
    per-part SHA-256 of MANIFEST, and every part's count and hash prefix agree with its stage-1 record.
  * survivors: distinct canonical orbits, counts per z0.
  * SAT stage 2 (sat_stage2.txt.xz): exactly one record per survivor, all UNSAT with drat-trim VERIFIED.
  * stage-1 certificate: for every z0 = 0..7, a header whose base-CNF hash equals the hash of the CNF
    rebuilt here from the survivor list, and an UNSAT + VERIFIED record for every orbit representative
    cube; the orbits of the representatives cover all 16^T cubes.
  * partial second checks: stage1_v (second stage-1 program) on every part for z0 <= 5 with the same orbits,
    and on some parts for z0 = 6 with orbits contained in those of stage 1; place.c on every survivor
    with z0 = 1 or 6, no dominating set.
  * cloud ledger: every part marked as run in the cloud has one ledger record, and conversely.
Prints JSON."""
import collections, hashlib, json, lzma, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from refcheck import orbit_key
import cert_stage1 as C

D = Path(sys.argv[1])
N, G = 28, 14
MODS = {z: (480 if z <= 4 else 4800) for z in range(8)}
H = lambda b: hashlib.sha256(b).hexdigest()


def xz(name):
    return lzma.decompress((D / name).read_bytes()).decode()


def main():
    out = {}
    parts = xz('stage1_parts.txt.xz').splitlines()
    keys = [(int(l.split()[2]), int(l.split()[4])) for l in parts]
    out['parts'] = len(parts)
    out['parts_complete'] = keys == [(z, p) for z in range(8) for p in range(MODS[z])] and \
        all(int(l.split()[3]) == MODS[int(l.split()[2])] and l.split()[:2] == ['28', '14'] for l in parts)
    agg = collections.defaultdict(collections.Counter)
    rec = {}
    for l in parts:
        f = l.split(); z, p = int(f[2]), int(f[4])
        a = agg[z]
        a['pairs'] += int(re.search(r'cand=(\d+)', l).group(1))
        a['nodes'] += int(re.search(r' nodes=(\d+)', l).group(1))
        a['cs'] += round(float(re.search(r'time=([\d.]+)s', l).group(1)) * 100)
        a['cloud'] += l.endswith('where=modal')
        ok_log = re.search(r'z=\(%d,%d\) part %d/%d:' % (z, G - z, p, MODS[z]), l) is not None and \
            int(re.search(r'surv=(\d+)', l).group(1)) == int(re.search(r'cand=(\d+)', l).group(1))
        a['log_ok'] += ok_log
        rec[(z, p)] = (int(re.search(r'cand=(\d+)', l).group(1)), f[6])
    out['stage1'] = {z: {'pairs': a['pairs'], 'nodes': a['nodes'], 'cpu_s': a['cs'] / 100, 'cloud_parts': a['cloud'],
                         'logs_ok': a['log_ok'] == MODS[z]} for z, a in sorted(agg.items())}
    sraw = xz('survivors.txt.xz')
    surv = sraw.splitlines(keepends=True)
    man = [l.split() for l in open(D / 'MANIFEST')]
    i = okc = okrec = 0
    seen = set()
    for (k, hc, nc) in man:
        z, p = int(k[1]), int(k.split('_')[1]); nc = int(nc)
        seen.add((z, p))
        okc += H(''.join(surv[i:i + nc]).encode()) == hc
        okrec += rec.get((z, p)) == (nc, hc[:16])
        i += nc
    out['manifest_parts'] = len(man)
    out['manifest_sha_ok'] = okc
    out['manifest_matches_stage1_records'] = okrec
    out['manifest_covers_all_parts'] = seen == set(rec) and len(man) == len(rec)
    out['manifest_consumed_all'] = i == len(surv)
    out['survivors_sha256'] = H(sraw.encode())
    S = [tuple(l.split()[1:4]) for l in surv]
    out['survivors'] = len(S)
    out['survivors_distinct'] = len(set(S))
    orbS = set((orbit_key(int(a, 16), int(b, 16), N), z) for a, b, z in S)
    out['survivors_distinct_orbits'] = len(orbS)
    out['survivors_per_z0'] = dict(sorted(collections.Counter(int(s[2]) for s in S).items()))
    out['survivors_per_stage1'] = all(out['survivors_per_z0'].get(z, 0) == out['stage1'][z]['pairs'] for z in range(8))
    # SAT stage 2
    sat = [l.split() for l in xz('sat_stage2.txt.xz').splitlines()]
    out['sat_records'] = len(sat)
    out['sat_all_unsat_verified'] = all(p[0] == 'V' and p[4] == 'UNSAT' and p[5] == 'drat=VERIFIED' for p in sat)
    out['sat_covers_survivors'] = sorted(tuple(p[1:4]) for p in sat) == sorted(S)
    ts = sum(float(p[7][3:]) for p in sat); tc = sum(float(p[8][3:]) for p in sat)
    mono = [p for p in sat if p[3] == '0']
    other = [p for p in sat if p[3] != '0']
    out['sat_cpu'] = {'solve': round(ts, 1), 'check': round(tc, 1), 'mono_solve': float(mono[0][7][3:]), 'mono_check': float(mono[0][8][3:]),
                      'max_other_solve': max(float(p[7][3:]) for p in other), 'max_other_check': max(float(p[8][3:]) for p in other),
                      'mono_pairs': len(mono)}
    pz = collections.defaultdict(float)
    for p in sat:
        pz[int(p[3])] += float(p[7][3:]) + float(p[8][3:])
    out['sat_cpu_per_z0'] = {z: round(v, 1) for z, v in sorted(pz.items())}
    # stage-1 certificate
    cert = {}
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        survf = Path(td) / 'survivors.txt'
        survf.write_text(sraw)
        for z0 in range(8):
            recs = [json.loads(l) for l in open(D / ('cert_stage1_z%d.jsonl' % z0))]
            hdr, cubes = recs[0], recs[1:]
            cls, a, b, npairs = C.build_base(N, G, z0, str(survf))
            reps = set(''.join(map(str, c)) for c in C.rep_cubes(hdr['T']))
            cert[z0] = {'T': hdr['T'], 'pairs': npairs, 'header_ok': hdr.get('header') is True and (hdr['n'], hdr['g'], hdr['z0'], hdr['pairs']) == (N, G, z0, npairs),
                        'base_sha_ok': hdr['base_sha256'] == hashlib.sha256(repr(cls).encode()).hexdigest(),
                        'clauses': len(cls), 'cube_reps': len(reps), 'cover_ok': C.check_cover(C.rep_cubes(hdr['T']), hdr['T']),
                        'all_reps_unsat_verified': set(r['cube'] for r in cubes) == reps and len(cubes) == len(reps)
                        and all(r['result'] == 'UNSAT' and r['drat'] == 'VERIFIED' for r in cubes),
                        'solve_s': round(sum(r['t_solve'] for r in cubes), 1), 'check_s': round(sum(r['t_check'] for r in cubes), 1),
                        'max_proof_bytes': max(r['proof_bytes'] for r in cubes), 'proof_bytes': sum(r['proof_bytes'] for r in cubes)}
            del cls
    out['cert'] = cert
    # second stage-1 program (partial)
    vparts = xz('stage1_v_parts.txt.xz').splitlines()
    vk = collections.defaultdict(set)
    vnodes = vcs = 0
    for l in vparts:
        z = int(re.search(r'z=\((\d+)', l).group(1)); p, m = map(int, re.search(r'part (\d+)/(\d+)', l).groups())
        assert m == MODS[z] and int(l.split()[2]) == z and int(l.split()[4]) == p
        vk[z].add(p)
        vnodes += int(re.search(r'nodes=(\d+)', l).group(1)); vcs += round(float(re.search(r'time=([\d.]+)s', l).group(1)) * 100)
    out['stage1_v_parts'] = {z: len(vk[z]) for z in range(8)}
    out['stage1_v_records_distinct'] = sum(len(v) for v in vk.values()) == len(vparts)
    out['stage1_v_complete_z0'] = [z for z in range(8) if len(vk[z]) == MODS[z]]
    V = [tuple(l.split()[1:4]) for l in open(D / 'survivors_v.txt') if l.startswith('C ')]
    orb = lambda L, zs: set((orbit_key(int(a, 16), int(b, 16), N), z) for a, b, z in L if int(z) in zs)
    full = set(out['stage1_v_complete_z0'])
    out['stage1_v_orbits_equal_complete'] = orb(V, full) == orb(S, full)
    out['stage1_v_orbits_subset_partial'] = orb(V, {6}) <= orb(S, {6})
    out['stage1_v_pairs'] = dict(sorted(collections.Counter(int(v[2]) for v in V).items()))
    out['stage1_v_nodes'] = vnodes
    out['stage1_v_cpu_s'] = vcs / 100
    # place.c (partial)
    done = [l.split() for l in open(D / 'stage2_place.txt')]
    P = set(tuple(p[1:4]) for p in done if p[0] == 'DONE')
    out['place_pairs'] = len(done)
    out['place_all_zero'] = all(p[0] == 'DONE' and p[5] == '0' for p in done)
    out['place_covers_z0'] = sorted(z for z in range(8) if out['survivors_per_z0'].get(z, 0) > 0 and
                                    set(s for s in S if int(s[2]) == z) <= P)
    out['place_subset_of_survivors'] = P <= set(S) and len(P) == len(done)
    pl = collections.Counter()
    for l in open(D / 'stage2_logs.txt'):
        m = re.search(r'candidates=(\d+) nodes=(\d+) time=([\d.]+)s', l)
        pl['nodes'] += int(m.group(2)); pl['cs'] += round(float(m.group(3)) * 100); pl['cand'] += int(m.group(1))
    out['place_nodes'] = pl['nodes']; out['place_cpu_s'] = pl['cs'] / 100; out['place_log_pairs'] = pl['cand']
    # cloud ledger
    led = [l.rstrip('\n').split('\t') for l in xz('modal_parts.tsv.xz').splitlines() if not l.startswith('#')]
    lk = set((int(t[1]), int(t[3])) for t in led if t[0] == 'lines2')
    ck = set(k for k, l in zip(keys, parts) if l.endswith('where=modal'))
    out['cloud_parts'] = len(ck)
    out['cloud_ledger_matches'] = lk == ck and len(led) == len(lk)
    calls = [l.rstrip('\n').split('\t') for l in open(D / 'modal_calls.tsv') if not l.startswith('#')]
    out['cloud_calls'] = len(calls)
    out['cloud_est_usd'] = round(sum(float(t[6]) for t in calls), 3)
    out['cloud_binary_sha256'] = sorted(set(t[9] for t in calls))
    print(json.dumps(out))


if __name__ == '__main__':
    main()
