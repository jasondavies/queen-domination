#!/usr/bin/env python3
"""Certificate-only full replay for n = 26 and n = 28.

Rebuilds, from the committed survivor lists only, every stage-1 certificate cube formula (all z0, with the
T of the committed records) and every stage-2 placement formula (one per survivor), solves each with
CaDiCaL writing a DRAT proof, checks every proof with drat-trim, and deletes the proofs.  The searches
that found the survivor lists are not rerun: the certificates do not depend on them.

usage: certify_all.py ROOT JOBS WORKDIR [N ...]          (default N: 26 28)
       certify_all.py ROOT --compare [N ...]             (compare data/replay/ with the original records)

Resume is bound to a manifest: WORKDIR/n<N>/manifest.json records n, g, the SHA-256 of the survivor list,
of the solver and checker binaries and of the encoder sources, and the T used for every z0.  An existing
WORKDIR/n<N> whose manifest differs is refused (exit 2).  Stage-1 cube records are reused only through
cert_stage1.py's own validation (header and base-CNF hash, cube set, rebuilt CNF hash per reused cube).
A stage-2 chunk is reused only if its header names the same chunk and input hash, it has one
UNSAT + VERIFIED line per input pair in input order, and every CNF hash matches the formula rebuilt now.
When everything is certified, the compacted records are written to ROOT/data/replay/n<N>/ and compared
with the original records in ROOT/data/n<N>/: same cubes and instances, same CNF hashes, all UNSAT with
VERIFIED proofs.  Prints JSON.
"""
import hashlib, json, lzma, os, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve()
CODE = ROOT / 'code'
sys.path.insert(0, str(CODE))
import sat_place                                    # noqa: E402

PY = sys.executable
NICE = ['nice', '-n', '10']
G = {26: 13, 28: 14}
CHUNK = 100


def sha_file(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def survivors_text(n):
    d = ROOT / 'data' / ('n%d' % n)
    return (d / 'survivors.txt').read_text() if n == 26 else lzma.decompress((d / 'survivors.txt.xz').read_bytes()).decode()


def orig_cert(n, z0):
    recs = [json.loads(l) for l in open(ROOT / 'data' / ('n%d' % n) / ('cert_stage1_z%d.jsonl' % z0))]
    return recs[0], {r['cube']: r for r in recs[1:]}


def orig_sat(n):
    d = ROOT / 'data' / ('n%d' % n)
    txt = (d / 'sat_stage2.txt').read_text() if n == 26 else lzma.decompress((d / 'sat_stage2.txt.xz').read_bytes()).decode()
    return {tuple(l.split()[1:4]): l.split() for l in txt.splitlines()}


def manifest(n):
    return {'n': n, 'g': G[n], 'survivors_sha256': hashlib.sha256(survivors_text(n).encode()).hexdigest(),
            'cadical_sha256': sha_file(ROOT / 'tools' / 'cadical'), 'drat_trim_sha256': sha_file(ROOT / 'tools' / 'drat-trim'),
            'sources_sha256': {f: sha_file(CODE / f) for f in ('cert_stage1.py', 'refcheck.py', 'sat_place.py')},
            'T': {str(z): orig_cert(n, z)[0]['T'] for z in range(G[n] // 2 + 1)}, 'chunk': CHUNK}


def chunks(lines):
    """deterministic chunks: each z0 = 0 pair alone (the hardest instances, started first), then the rest
    in file order, CHUNK at a time"""
    mono = [[l] for l in lines if l.split()[3] == '0']
    rest = [l for l in lines if l.split()[3] != '0']
    return mono + [rest[i:i + CHUNK] for i in range(0, len(rest), CHUNK)]


def chunk_ok(n, k, inp, outf, rehash=True):
    """reuse test for a stage-2 chunk (see the module docstring); rehash=False only for a chunk just written
    by sat_place.py, whose CNF hashes were computed from the formulas it gave to the solver"""
    if not outf.exists():
        return False
    L = outf.read_text().splitlines()
    try:
        hdr = json.loads(L[0])
    except (ValueError, IndexError):
        return False
    if hdr != {'n': n, 'g': G[n], 'chunk': k, 'count': len(inp), 'input_sha256': hashlib.sha256(''.join(inp).encode()).hexdigest()}:
        return False
    V = [l.split() for l in L[1:] if l.startswith('V ')]
    if len(V) != len(inp):
        return False
    for v, l in zip(V, inp):
        p = l.split()
        if v[1:4] != p[1:4] or v[4] != 'UNSAT' or v[5] != 'drat=VERIFIED':
            return False
        if rehash:
            cnf = sat_place.build(n, G[n], int(p[1], 16), int(p[2], 16), int(p[3]))
            if v[6] != 'cnf=' + hashlib.sha256(cnf.encode()).hexdigest()[:16]:
                return False
    return True


def run_chunk(arg):
    n, k, inp, outf, wd = arg
    if chunk_ok(n, k, inp, outf):
        return k, 'reused'
    with tempfile.TemporaryDirectory(dir=wd) as td:
        r = subprocess.run(NICE + [PY, str(CODE / 'sat_place.py'), str(n), str(G[n]), str(ROOT / 'tools' / 'cadical'),
                                   str(ROOT / 'tools' / 'drat-trim'), td], input=''.join(inp), capture_output=True, text=True)
    hdr = {'n': n, 'g': G[n], 'chunk': k, 'count': len(inp), 'input_sha256': hashlib.sha256(''.join(inp).encode()).hexdigest()}
    tmp = outf.with_suffix('.tmp')
    tmp.write_text(json.dumps(hdr) + '\n' + r.stdout)
    os.replace(tmp, outf)
    return k, 'solved' if chunk_ok(n, k, inp, outf, rehash=False) else 'FAILED'


def replay(n, jobs, work):
    t0 = time.time()
    W = work / ('n%d' % n)
    W.mkdir(parents=True, exist_ok=True)
    man = manifest(n)
    mf = W / 'manifest.json'
    if mf.exists() and json.loads(mf.read_text()) != man:
        print(json.dumps({'error': '%s belongs to a different run; refusing to reuse it' % W}))
        sys.exit(2)
    mf.write_text(json.dumps(man, indent=1) + '\n')
    survf = W / 'survivors.txt'
    survf.write_text(survivors_text(n))
    out = {'n': n, 'manifest': man, 'stage1': {}, 'stage2': {}}
    wd = W / 'wd'
    wd.mkdir(exist_ok=True)
    for z0 in range(G[n] // 2 + 1):
        T = man['T'][str(z0)]
        r = subprocess.run(NICE + [PY, str(CODE / 'cert_stage1.py'), str(n), str(G[n]), str(z0), str(survf), str(ROOT / 'tools' / 'cadical'),
                                   str(ROOT / 'tools' / 'drat-trim'), str(wd), str(T), str(jobs), str(W / ('cert_stage1_z%d.jsonl' % z0))],
                           capture_output=True, text=True)
        last = [l for l in r.stdout.splitlines() if l.startswith('{')]
        out['stage1'][z0] = dict(json.loads(last[-1]) if last else {'error': r.stderr[-500:]}, exit=r.returncode)
    lines = [l + '\n' for l in survivors_text(n).splitlines() if l.startswith('C ')]
    ch = chunks(lines)
    S = W / 'sat'
    S.mkdir(exist_ok=True)
    with ThreadPoolExecutor(jobs) as ex:
        st = list(ex.map(run_chunk, [(n, k, c, S / ('chunk_%05d.txt' % k), wd) for k, c in enumerate(ch)]))
    out['stage2'] = {'chunks': len(ch), 'reused': sum(s == 'reused' for _, s in st), 'solved': sum(s == 'solved' for _, s in st),
                     'failed': sum(s == 'FAILED' for _, s in st)}
    ok1 = all(v.get('all_unsat_verified') is True and v['exit'] == 0 for v in out['stage1'].values())
    ok2 = out['stage2']['failed'] == 0
    out['certified'] = ok1 and ok2
    if out['certified']:
        R = ROOT / 'data' / 'replay' / ('n%d' % n)
        R.mkdir(parents=True, exist_ok=True)
        for z0 in out['stage1']:
            L = [json.loads(l) for l in open(W / ('cert_stage1_z%d.jsonl' % z0)) if l.strip()]
            latest = {}
            for r in L[1:]:
                if r.get('result') == 'UNSAT' and r.get('drat') == 'VERIFIED':
                    latest[r['cube']] = r
            (R / ('cert_stage1_z%d.jsonl' % z0)).write_text(''.join(json.dumps(x) + '\n' for x in [L[0]] + [latest[c] for c in sorted(latest)]))
        V = {}
        for k in range(len(ch)):
            for l in (S / ('chunk_%05d.txt' % k)).read_text().splitlines()[1:]:
                if l.startswith('V '):
                    V[tuple(l.split()[1:4])] = l
        txt = ''.join(V[tuple(l.split()[1:4])] + '\n' for l in lines)
        (R / 'sat_stage2.txt.xz').write_bytes(lzma.compress(txt.encode(), preset=9))
        (R / 'manifest.json').write_text(json.dumps(man, indent=1) + '\n')
    out['seconds'] = round(time.time() - t0, 1)
    return out


def compare(n):
    """the replay records in data/replay/n<N>/ against the original records in data/n<N>/"""
    R = ROOT / 'data' / 'replay' / ('n%d' % n)
    res = {'n': n, 'present': R.exists()}
    if not R.exists():
        return res
    man = json.loads((R / 'manifest.json').read_text())
    res['survivors_sha_ok'] = man['survivors_sha256'] == hashlib.sha256(survivors_text(n).encode()).hexdigest()
    cubes = cubes_ok = hash_eq = 0
    cert = {}
    for z0 in range(G[n] // 2 + 1):
        oh, oc = orig_cert(n, z0)
        L = [json.loads(l) for l in open(R / ('cert_stage1_z%d.jsonl' % z0))]
        rh, rc = L[0], {r['cube']: r for r in L[1:]}
        same = rh == oh and set(rc) == set(oc) and len(rc) == len(L) - 1
        ok = sum(r['result'] == 'UNSAT' and r['drat'] == 'VERIFIED' for r in rc.values())
        eq = sum(rc[c]['cnf_sha256'] == oc[c]['cnf_sha256'] for c in rc if c in oc)
        cubes += len(rc); cubes_ok += ok; hash_eq += eq
        cert[z0] = {'header_equal': rh == oh, 'same_cubes': same, 'cubes': len(rc), 'unsat_verified': ok, 'cnf_hash_equal': eq,
                    'solve_s': round(sum(r['t_solve'] for r in rc.values()), 1), 'check_s': round(sum(r['t_check'] for r in rc.values()), 1)}
    res['cert'] = cert
    res['cubes'] = cubes; res['cubes_unsat_verified'] = cubes_ok; res['cubes_cnf_hash_equal'] = hash_eq
    res['cert_all_ok'] = all(c['same_cubes'] for c in cert.values()) and cubes == cubes_ok == hash_eq
    orig = orig_sat(n)
    new = [l.split() for l in lzma.decompress((R / 'sat_stage2.txt.xz').read_bytes()).decode().splitlines()]
    nk = [tuple(v[1:4]) for v in new]
    res['instances'] = len(new)
    res['instances_same_set'] = set(nk) == set(orig) and len(nk) == len(set(nk))
    res['instances_unsat_verified'] = sum(v[4] == 'UNSAT' and v[5] == 'drat=VERIFIED' for v in new)
    res['instances_cnf_hash_equal'] = sum(v[6] == orig[tuple(v[1:4])][6] for v in new if tuple(v[1:4]) in orig)
    res['sat_solve_s'] = round(sum(float(v[7][3:]) for v in new), 1); res['sat_check_s'] = round(sum(float(v[8][3:]) for v in new), 1)
    res['sat_all_ok'] = res['instances_same_set'] and len(new) == res['instances_unsat_verified'] == res['instances_cnf_hash_equal'] == len(orig)
    res['all_ok'] = res['survivors_sha_ok'] and res['cert_all_ok'] and res['sat_all_ok']
    return res


def main():
    if sys.argv[2] == '--compare':
        ns = [int(x) for x in sys.argv[3:]] or [26, 28]
        res = [compare(n) for n in ns]
        print(json.dumps(res if len(res) > 1 else res[0]))
        sys.exit(0 if all(r.get('all_ok') for r in res) else 1)
    jobs, work = int(sys.argv[2]), Path(sys.argv[3]).resolve()
    ns = [int(x) for x in sys.argv[4:]] or [26, 28]
    res = []
    for n in ns:
        r = replay(n, jobs, work)
        if r['certified']:
            r['compare'] = compare(n)
        res.append(r)
        print(json.dumps(r), flush=True)
    sys.exit(0 if all(r['certified'] and r['compare']['all_ok'] for r in res) else 1)


if __name__ == '__main__':
    main()
