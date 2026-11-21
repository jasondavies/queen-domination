"""Reading the run records of the frame method (read-only input).  Shared by gen_cases.py and check_cases.py.

For (n, k) the records are (in data/frame/ of the repository, xz-compressed; uncompressed files are also read)
  d_N_K.jsonl, d_N_K_sq.jsonl   (code/frame/run_cases.py: one record per case, plain formula), and
  h_N_K.jsonl                   (code/frame/run_hard.py: cube records, formula + residual SBP + cube),
the same files and the same refutation rule as code/frame/final_check35.py and code/frame/check_frame.py:
  a case is refuted iff it has a plain record UNSAT + drat VERIFIED, or its verified sbp cube records cover it
  (the empty cube, or recursively all 16 children of a cube)."""
import json, os, hashlib, lzma


def code(c):
    """decimal code of a case: ml mr mb mt (two digits each) dR dC dT dS (one digit each)"""
    ml, mr, mb, mt, dR, dC, dT, dS = c
    assert max(c[:4]) < 100 and max(c[4:]) < 10 and min(c) >= 0
    return (((ml * 100 + mr) * 100 + mb) * 100 + mt) * 10000 + dR * 1000 + dC * 100 + dT * 10 + dS


def decode(c):
    return (c // 10**10 % 100, c // 10**8 % 100, c // 10**6 % 100, c // 10**4 % 100,
            c // 1000 % 10, c // 100 % 10, c // 10 % 10, c % 10)


def sha(path):
    """SHA-256 of the (uncompressed) record file"""
    b = open(path, 'rb').read()
    return hashlib.sha256(lzma.decompress(b) if path.endswith('.xz') else b).hexdigest()


def records(path):
    out = []
    if os.path.exists(path):
        for line in (lzma.open(path, 'rt') if path.endswith('.xz') else open(path)):
            try:
                out.append(json.loads(line))
            except ValueError:
                pass
    return out


def run_files(outdir, n, k):
    out = []
    for f in ('d_%d_%d.jsonl', 'd_%d_%d_sq.jsonl', 'h_%d_%d.jsonl'):
        p = os.path.join(outdir, f % (n, k))
        out.append(p + '.xz' if not os.path.exists(p) and os.path.exists(p + '.xz') else p)
    return out


def analyse(outdir, n, k):
    """returns (refuted, info): refuted = sorted list of refuted cases; info = dict of statistics"""
    dfiles = run_files(outdir, n, k)[:2]
    hfile = run_files(outdir, n, k)[2]
    plain, keys, sat, other = set(), set(), [], 0
    per_file = {}
    for p in dfiles:
        rs = [r for r in records(p) if 'case' in r]
        per_file[os.path.basename(p)] = {'records': len(rs), 'sha256': sha(p) if os.path.exists(p) else None}
        for r in rs:
            c = tuple(r['case'])
            keys.add(c)
            if r.get('result') == 'SAT':
                sat.append(r)
            if r.get('result') == 'UNSAT' and r.get('drat') == 'VERIFIED':
                plain.add(c)
            else:
                other += 1
    cubes = {}
    rs = [r for r in records(hfile) if 'cube' in r]
    per_file[os.path.basename(hfile)] = {'records': len(rs), 'sha256': sha(hfile) if os.path.exists(hfile) else None}
    for r in rs:
        c = tuple(r['case'])
        keys.add(c)
        if r.get('result') == 'SAT':
            sat.append(r)
        if r.get('result') == 'UNSAT' and r.get('drat') == 'VERIFIED' and r.get('sbp') is True:
            cubes.setdefault(c, set()).add(r['cube'])

    def covered(case, cube, depth=0):
        have = cubes.get(case, ())
        if cube in have:
            return True
        if depth >= 8 or not any(cb.startswith(cube) and len(cb) > len(cube) for cb in have):
            return False
        return all(covered(case, cube + format(i, '04b'), depth + 1) for i in range(16))

    by_cube = {c for c in cubes if c not in plain and covered(c, '')}
    refuted = sorted(plain | by_cube)
    info = {'files': per_file, 'case_keys_in_records': len(keys), 'plain_refuted': len(plain),
            'cube_refuted': len(by_cube), 'cube_refuted_unsplit': sum('' in cubes[c] for c in by_cube),
            'keys_not_refuted': sorted(keys - set(refuted))[:5], 'n_keys_not_refuted': len(keys - set(refuted)),
            'sat_records': len(sat), 'nonverified_plain_records': other}
    return refuted, info, keys
