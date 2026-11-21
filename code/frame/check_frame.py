#!/usr/bin/env python3
"""Checks of the committed frame-method records (data/frame/) for scripts/verify.py.

  check_frame.py coverage N K DATA [--rehash-sample M] [--rehash-all] [--seed S] [--jobs J]
  check_frame.py resolve N K DATA CADICAL DRAT_TRIM WORKDIR [--sample M] [--seed S] [--max-solve T]
  check_frame.py upper DATA
  check_frame.py tests
  check_frame.py validation DATA/validation

coverage: the case list L(N, K) is rebuilt from first principles (geom.cases_by_frame).  The records are
  DATA/d_N_K.jsonl.xz (run_cases.py, one record per case), and for N = 35 also DATA/d_N_K_sq.jsonl.xz
  (run_cases.py) and DATA/h_N_K.jsonl.xz (run_hard.py, cube records of the formula with residual symmetry
  breaking).  It checks that the set of case keys occurring in the records equals L(N, K), and applies the rule
  of final_check35.py: a case is refuted iff it has a plain record UNSAT + drat VERIFIED, or its UNSAT +
  VERIFIED cube records (with sbp) cover it -- the empty cube, or recursively all 16 children of a cube.
  Any SAT record is reported.  With --rehash-sample M (seeded) or --rehash-all, the CNF of the refuting
  records is rebuilt with enc.py (and run_hard.build for cubes) and its SHA-256 compared with the record.
resolve: a seeded sample of M cases whose recorded solve time is at most T seconds is solved again exactly
  as run_cases.py --mode drat does (CaDiCaL writes a DRAT proof, drat-trim -w checks it); the CNF hash, the
  verdict and the checker status must equal the record.
upper: the explicit dominating sets of DATA/plus1_{32,34,36}.json, DATA/q35_19.json and DATA/q{40_21,42_22,44_23,46_24}.json
  are checked directly; the 22-set of Q_43 in DATA/neuhaus/ (Neuhaus 2009) is checked to dominate Q_43, and the
  Q_44 set to be that set plus the corner (43, 43).
validation: summarises the recorded validation runs (run_cases.py --mode pysat; QD_ENC=b for vb_*): per (n, k)
  the number of cases run, satisfiable and unsatisfiable cases, whether every case of L(n, k) was run, and a
  direct check of every recorded model (k squares, dominating, and of the case it was found for).
tests: runs the tests of the identities and of the encoder (verify_identities.py, test_waste.py, test_sbp.py, and
  test_enc.py on the nine (n, k) of its exact solution-set comparison up to (10, 5)).
Prints JSON."""
import hashlib, json, lzma, os, random, subprocess, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from geom import cases_by_frame
import enc, run_hard

_B = {}


def opt(name, default, conv=int):
    return conv(sys.argv[sys.argv.index(name) + 1]) if name in sys.argv else default


def read(path):
    """records of a .jsonl.xz file (missing file: empty) and the SHA-256 of its uncompressed text"""
    if not os.path.exists(path):
        return [], None
    txt = lzma.decompress(open(path, 'rb').read())
    recs = []
    for l in txt.decode().splitlines():
        try:
            recs.append(json.loads(l))
        except ValueError:
            pass
    return recs, hashlib.sha256(txt).hexdigest()


def rehash(arg):
    n, k, case, cube = arg
    if cube is None:
        if case[4:] not in _B:
            _B.clear(); _B[case[4:]] = enc.Base(n, k, case[4:])
        extra, nv = enc.case_extra(_B[case[4:]], case)
        return case, cube, enc.sha(enc.dimacs(_B[case[4:]], extra, nv))
    run_hard._A.update(n=n, k=k, sbp=True)
    return case, cube, enc.sha(run_hard.build(case, cube)[1])


def coverage(n, k, data):
    cases = cases_by_frame(n, k)
    cset = set(cases)
    files, plain, cubes, keys, sat, timeouts = {}, {}, {}, set(), [], 0
    for fn in ('d_%d_%d.jsonl.xz' % (n, k), 'd_%d_%d_sq.jsonl.xz' % (n, k)):
        recs, h = read(os.path.join(data, fn))
        if h is None:
            continue
        recs = [r for r in recs if 'case' in r]
        files[fn] = {'records': len(recs), 'sha256_uncompressed': h}
        for r in recs:
            c = tuple(r['case']); keys.add(c)
            sat += [c] if r['result'] == 'SAT' else []
            timeouts += r['result'] == 'TIMEOUT'
            if r['result'] == 'UNSAT' and r.get('drat') == 'VERIFIED':
                plain[c] = r
    recs, h = read(os.path.join(data, 'h_%d_%d.jsonl.xz' % (n, k)))
    if h is not None:
        recs = [r for r in recs if 'cube' in r]
        files['h_%d_%d.jsonl.xz' % (n, k)] = {'records': len(recs), 'sha256_uncompressed': h}
        for r in recs:
            c = tuple(r['case']); keys.add(c)
            sat += [c] if r['result'] == 'SAT' else []
            timeouts += r['result'] == 'TIMEOUT'
            if r['result'] == 'UNSAT' and r.get('drat') == 'VERIFIED' and r.get('sbp') is True:
                cubes[(c, r['cube'])] = r
    by_case = {}
    for c, cb in cubes:
        by_case.setdefault(c, set()).add(cb)

    def covered(case, cube, depth=0):
        have = by_case.get(case, ())
        if cube in have:
            return True
        if depth >= 8 or not any(cb.startswith(cube) and len(cb) > len(cube) for cb in have):
            return False
        return all(covered(case, cube + format(i, '04b'), depth + 1) for i in range(16))

    st = {'n': n, 'k': k, 'frames': len({c[:4] for c in cases}), 'cases': len(cases), 'files': files,
          'record_keys': len(keys), 'keys_equal_case_list': keys == cset, 'keys_not_in_case_list': len(keys - cset),
          'cases_without_record': len(cset - keys), 'refuted_plain': 0, 'refuted_cubes_unsplit': 0, 'refuted_cubes_split': 0,
          'not_refuted': 0, 'sat_records': len(sat), 'timeout_records': timeouts}
    used = []
    for c in cases:
        if c in plain:
            st['refuted_plain'] += 1; used.append((c, None))
        elif covered(c, ''):
            st['refuted_cubes_unsplit' if '' in by_case[c] else 'refuted_cubes_split'] += 1
            used += [(c, cb) for cb in by_case[c]]
        else:
            st['not_refuted'] += 1
    st['cube_records_used'] = sum(cb is not None for _, cb in used)
    st['split_cases_with_second_layer'] = sum(1 for c in by_case if c not in plain and covered(c, '')
                                              and any(len(cb) > 4 for cb in by_case[c]))
    R = [plain[c] if cb is None else cubes[(c, cb)] for c, cb in used]
    st['t_solve_s'] = round(sum(r['t_solve'] for r in R), 1)
    st['t_check_s'] = round(sum(r.get('t_check', 0) for r in R), 1)
    st['proof_bytes'] = sum(r.get('proof_bytes', 0) for r in R)
    st['max_proof_bytes'] = max(r.get('proof_bytes', 0) for r in R)
    st['max_t_solve_plain'] = max([plain[c]['t_solve'] for c, cb in used if cb is None] or [0])
    per_case = {}
    for (c, cb), r in zip(used, R):
        per_case[c] = per_case.get(c, 0) + r['t_solve'] + r.get('t_check', 0)
    st['max_case_s'] = round(max(per_case.values()), 1)
    by_phase = {'nonsquare': [0.0, 0.0], 'square_deficit': [0.0, 0.0], 'hard': [0.0, 0.0]}
    for (c, cb), r in zip(used, R):
        ph = 'hard' if cb is not None else 'nonsquare' if c[0] + c[1] != c[2] + c[3] else 'square_deficit'
        by_phase[ph][0] += r['t_solve']; by_phase[ph][1] += r.get('t_check', 0)
    st['phases'] = {ph: {'solve_s': round(v[0], 1), 'check_s': round(v[1], 1)} for ph, v in by_phase.items()}
    st['phases']['nonsquare']['cases'] = sum(1 for c, cb in used if cb is None and c[0] + c[1] != c[2] + c[3])
    st['phases']['square_deficit']['cases'] = sum(1 for c, cb in used if cb is None and c[0] + c[1] == c[2] + c[3])
    st['phases']['hard']['cases'] = st['refuted_cubes_unsplit'] + st['refuted_cubes_split']
    st['ALL_REFUTED'] = st['not_refuted'] == 0 and not sat and st['keys_equal_case_list']
    rh = None
    if '--rehash-all' in sys.argv:
        rh = list(used)
    elif '--rehash-sample' in sys.argv:
        m = opt('--rehash-sample', 0)
        rnd = random.Random(opt('--seed', 1))
        pl = [u for u in used if u[1] is None]; cb = [u for u in used if u[1] is not None]
        rh = rnd.sample(pl, min(m, len(pl))) + rnd.sample(cb, min(max(m // 10, 1), len(cb)) if cb else 0)
    if rh is not None:
        rh.sort(key=lambda u: (u[0][4:], u[1] is not None))
        mism = 0
        with Pool(opt('--jobs', 3)) as P:
            for c, cb, h in P.imap_unordered(rehash, [(n, k, c, cb) for c, cb in rh], chunksize=16):
                mism += h != (plain[c] if cb is None else cubes[(c, cb)])['cnf_sha256']
        st['rehash'] = {'mode': 'all' if '--rehash-all' in sys.argv else 'sample', 'plain': sum(u[1] is None for u in rh),
                        'cubes': sum(u[1] is not None for u in rh), 'mismatches': mism}
    return st


def resolve(n, k, data, cad, drat, wd):
    recs = []
    for fn in ('d_%d_%d.jsonl.xz' % (n, k), 'd_%d_%d_sq.jsonl.xz' % (n, k)):
        recs += [r for r in read(os.path.join(data, fn))[0] if r.get('result') == 'UNSAT' and r.get('drat') == 'VERIFIED']
    tmax = opt('--max-solve', 2.0, float)
    pool = sorted((r for r in recs if r['t_solve'] <= tmax), key=lambda r: r['case'])
    pick = random.Random(opt('--seed', 1)).sample(pool, min(opt('--sample', 8), len(pool)))
    os.makedirs(wd, exist_ok=True)
    out = {'n': n, 'k': k, 'sample': len(pick), 'reproduced': 0, 'max_solve_recorded_s': tmax, 'cases': []}
    for r in pick:
        c = tuple(r['case'])
        B = enc.Base(n, k, c[4:])
        extra, nv = enc.case_extra(B, c)
        txt = enc.dimacs(B, extra, nv)
        fc, fp = os.path.join(wd, 'case.cnf'), os.path.join(wd, 'case.drat')
        open(fc, 'w').write(txt)
        rc = subprocess.run([cad, '-q', fc, fp], capture_output=True, text=True).returncode
        res = {10: 'SAT', 20: 'UNSAT'}.get(rc, 'OTHER')
        chk = None
        if res == 'UNSAT':
            d = subprocess.run([drat, fc, fp, '-w', '-t', '1000000'], capture_output=True, text=True)
            chk = 'VERIFIED' if 's VERIFIED' in d.stdout else 'FAILED'
        for f in (fc, fp):
            if os.path.exists(f):
                os.remove(f)
        ok = enc.sha(txt) == r['cnf_sha256'] and res == 'UNSAT' and chk == 'VERIFIED'
        out['reproduced'] += ok
        out['cases'].append({'case': list(c), 'cnf_hash_equal': enc.sha(txt) == r['cnf_sha256'], 'result': res, 'drat': chk})
    return out


def upper(data):
    def undominated(n, Q):
        return sum(1 for x in range(n) for y in range(n)
                   if not any(x == a or y == b or y - x == b - a or x + y == a + b for a, b in Q))
    out = {}
    for name in ('plus1_32.json', 'plus1_34.json', 'plus1_36.json', 'q35_19.json', 'q40_21.json', 'q42_22.json', 'q44_23.json', 'q46_24.json'):
        d = json.load(open(os.path.join(data, name)))
        Q = [tuple(p) for p in d['set_col_row']]
        n = d['n']
        out['q%d' % n] = {'n': n, 'queens': len(set(Q)), 'on_board': all(0 <= a < n and 0 <= b < n for a, b in Q),
                          'undominated': undominated(n, Q)}
    import re
    txt = open(os.path.join(data, 'neuhaus', 'appendix_01_q43_01cover.txt')).read()
    P = [tuple(map(int, m)) for m in re.findall(r'^\((\d+),\s*(\d+)\)\s*$', txt, re.M)]
    q44 = {tuple(p) for p in json.load(open(os.path.join(data, 'q44_23.json')))['set_col_row']}
    out['neuhaus43'] = {'n': 43, 'queens': len(set(P)), 'on_board': all(0 <= a < 43 and 0 <= b < 43 for a, b in P),
                        'undominated': undominated(43, P), 'q44_is_it_plus_corner': q44 == set(P) | {(43, 43)}}
    return out


TESTS = [('identities', ['verify_identities.py'], 'ALL IDENTITIES OK'), ('waste', ['test_waste.py'], ': OK'),
         ('sbp', ['test_sbp.py'], 'ALL OK'),
         ('encoder', ['test_enc.py'] + '4 2 5 3 6 3 6 4 7 4 8 4 8 5 9 5 10 5'.split(), 'ALL OK')]


def tests():
    out = {}
    for name, cmd, want in TESTS:
        t0 = time.time()
        r = subprocess.run([sys.executable, os.path.join(HERE, cmd[0])] + cmd[1:], capture_output=True, text=True)
        last = [l for l in r.stdout.splitlines() if l.strip()]
        out[name] = {'ok': r.returncode == 0 and bool(last) and want in last[-1], 'last_line': last[-1] if last else r.stderr[-300:],
                     'seconds': round(time.time() - t0, 1)}
        if name == 'encoder':
            out[name]['pairs'] = sum('set equality True' in l and l.rstrip().endswith('s)') for l in last)
    return out


def validation(vdir):
    from geom import dominated, case_of
    out = {}
    for fn in sorted(os.listdir(vdir)):
        if not fn.endswith('.jsonl.xz'):
            continue
        tag = fn[:-len('.jsonl.xz')]
        parts = tag.split('_')
        n, k = int(parts[1]), int(parts[2])
        R = [r for r in read(os.path.join(vdir, fn))[0] if 'case' in r]
        sat = [r for r in R if r['result'] == 'SAT']
        L = cases_by_frame(n, k)
        out[tag] = {'n': n, 'k': k, 'cases': len(L), 'records': len(R), 'complete': {tuple(r['case']) for r in R} == set(L),
                    'sat': len(sat), 'unsat': sum(r['result'] == 'UNSAT' for r in R),
                    'models_ok': all(len(r['model']) == k and dominated(n, [tuple(p) for p in r['model']])
                                     and case_of(n, [tuple(p) for p in r['model']]) == tuple(r['case']) for r in sat),
                    'cpu_s': round(sum(r.get('t', 0) for r in R), 1)}
    return out


def main():
    cmd = sys.argv[1]
    if cmd == 'validation':
        print(json.dumps(validation(sys.argv[2])))
        return
    if cmd == 'tests':
        r = tests()
        print(json.dumps(r))
        sys.exit(0 if all(v['ok'] for v in r.values()) else 1)
    if cmd == 'upper':
        print(json.dumps(upper(sys.argv[2])))
        return
    n, k, data = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    if cmd == 'coverage':
        st = coverage(n, k, data)
        print(json.dumps(st))
        sys.exit(0 if st['ALL_REFUTED'] and st.get('rehash', {}).get('mismatches', 0) == 0 else 1)
    if cmd == 'resolve':
        r = resolve(n, k, data, sys.argv[5], sys.argv[6], sys.argv[7])
        print(json.dumps(r))
        sys.exit(0 if r['reproduced'] == r['sample'] > 0 else 1)


if __name__ == '__main__':
    main()
