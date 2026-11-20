#!/usr/bin/env python3
"""DRAT certificate for stage 1 (the line relaxation), by cube and conquer with symmetry reduction.

Claim certified for (N, G, z0): every z-feasible pair (A, B) of (N-G)-subsets of [0, N) lies in the orbit,
under the four colour-preserving symmetries, of a pair listed in the survivor file.

F := relax_cnf(N, G, z0) (see refcheck.py) plus, for every listed pair and each of its four images
(P, Q), the blocking clause  OR_{r in P} -a_r  OR  OR_{x in Q} -b_x .  The (a, b)-projection of the
models of F is the set of feasible pairs outside the orbits of the listed ones; it is invariant under
the symmetry group, because feasibility is (Lemma 2.3 of the paper) and the blocking clauses are closed
under it.  The claim is: F is unsatisfiable.

Cubes: the 4T variables a_t, a_{N-1-t}, b_t, b_{N-1-t} (t < T) are fixed in all 16^T ways.  The group
acts on these cubes; F & c is unsatisfiable iff F & g(c) is.  We solve one cube per orbit (the lex-least
code), each with CaDiCaL writing a DRAT proof that drat-trim checks; `check_cover` confirms that the
orbits of the solved cubes are all 16^T cubes.  Proofs are deleted after checking (they can be
regenerated deterministically: same CNF, same solver version, same options).

usage: cert_stage1.py N G z0 SURVIVORS CADICAL DRATTRIM WORKDIR T JOBS OUT.jsonl

Resuming.  OUT.jsonl starts with a header (n, g, z0, T, number of pairs, number of cubes and orbit
representatives, SHA-256 of the base CNF).  If OUT.jsonl exists, the header is compared with the one
rebuilt from the arguments and the survivor file; on any difference the program refuses to run (exit 2).
A recorded cube is reused only if it is an orbit representative, its latest record is UNSAT + VERIFIED,
and the SHA-256 of its CNF, rebuilt now, equals the recorded one; otherwise (failed, interrupted,
mismatched) it is solved again and the new record supersedes the old.  The final verdict
(all_unsat_verified) requires exactly the expected set of cubes, each with a reused-and-revalidated or a
freshly produced UNSAT + VERIFIED record; the exit status is 0 only in that case.  The CNF hash of a
record is always computed from the exact text written to the file given to the solver.
"""
import hashlib, json, os, subprocess, sys, time
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from refcheck import relax_cnf, images, block, read_pairs


def cube_vars(n, T):
    out = []
    for t in range(T):
        out += [('a', t), ('a', n - 1 - t), ('b', t), ('b', n - 1 - t)]
    return out


def act(code, g):
    """image of one group code (a_t, a_t', b_t, b_t') -- t' = N-1-t -- under g in {id, T, R, AT}."""
    a1, a2, b1, b2 = code
    return [(a1, a2, b1, b2), (b1, b2, a1, a2), (a2, a1, b2, b1), (b2, b1, a2, a1)][g]


def cube_orbit(cube, T):
    """cube = tuple of 4T bits; returns its 4 images."""
    out = []
    for g in range(4):
        img = []
        for t in range(T):
            img += act(cube[4 * t:4 * t + 4], g)
        out.append(tuple(img))
    return out


def rep_cubes(T):
    reps = []
    for k in range(16 ** T):
        c = tuple((k >> (4 * T - 1 - i)) & 1 for i in range(4 * T))
        if c == min(cube_orbit(c, T)):
            reps.append(c)
    return reps


def check_cover(reps, T):
    covered = set()
    for c in reps:
        covered.update(cube_orbit(c, T))
    return len(covered) == 16 ** T


_CTX = {}


def build_base(n, g, z0, surv):
    cls, a, b, pool = relax_cnf(n, g, z0)
    pairs = read_pairs(surv, z0)
    for (A, B, _) in pairs:
        for (P, Q) in set(images(A, B, n)):
            cls.append(block(P, Q, a, b, n))
    return cls, a, b, len(pairs)


def cube_cnf(cube):
    """the exact CNF text given to the solver for this cube, and its SHA-256"""
    n, cls, a, b, T = (_CTX[k] for k in ('n', 'cls', 'a', 'b', 'T'))
    lits = []
    for (kind, i), v in zip(cube_vars(n, T), cube):
        var = a[i] if kind == 'a' else b[i]
        lits.append(var if v else -var)
    allc = cls + [[l] for l in lits]
    nv = max(abs(l) for c in allc for l in c)
    cnf = 'p cnf %d %d\n' % (nv, len(allc)) + ''.join(' '.join(map(str, c)) + ' 0\n' for c in allc)
    return cnf, hashlib.sha256(cnf.encode()).hexdigest()


def cube_hash(cube):
    return ''.join(map(str, cube)), cube_cnf(cube)[1]


def solve_cube(cube):
    cad, drat, wd = (_CTX[k] for k in ('cad', 'drat', 'wd'))
    cnf, h = cube_cnf(cube)
    tag = ''.join(map(str, cube))
    fc, fp = os.path.join(wd, tag + '.cnf'), os.path.join(wd, tag + '.drat')
    with open(fc, 'w') as f:
        f.write(cnf)
    t0 = time.time()
    r = subprocess.run([cad, '-q', '--no-binary', fc, fp], capture_output=True, text=True)
    t1 = time.time()
    res = {10: 'SAT', 20: 'UNSAT'}.get(r.returncode, 'ERR%d' % r.returncode)
    chk = None
    if res == 'UNSAT':
        d = subprocess.run([drat, fc, fp, '-w', '-t', '1000000'], capture_output=True, text=True)
        chk = 'VERIFIED' if 's VERIFIED' in d.stdout else 'FAILED'
    t2 = time.time()
    psize = os.path.getsize(fp) if os.path.exists(fp) else 0
    for f in (fc, fp):
        if os.path.exists(f):
            os.remove(f)
    return {'cube': tag, 'cnf_sha256': h, 'result': res, 'drat': chk, 'proof_bytes': psize,
            't_solve': round(t1 - t0, 2), 't_check': round(t2 - t1, 2)}


def read_records(out):
    """parse OUT.jsonl; returns (header or None, list of cube records); unparsable lines are ignored
    (an interrupted write), so the cubes concerned are solved again"""
    hdr, recs = None, []
    for i, l in enumerate(open(out)):
        if not l.strip():
            continue
        try:
            r = json.loads(l)
        except ValueError:
            continue
        if i == 0 and r.get('header') is True:
            hdr = r
        elif 'cube' in r:
            recs.append(r)
        else:
            raise SystemExit('unexpected record in %s: %r' % (out, l[:80]))
    return hdr, recs


def main():
    n, g, z0 = map(int, sys.argv[1:4])
    surv, cad, drat, wd = sys.argv[4:8]
    T, jobs, out = int(sys.argv[8]), int(sys.argv[9]), sys.argv[10]
    os.makedirs(wd, exist_ok=True)
    cls, a, b, npairs = build_base(n, g, z0, surv)
    _CTX.update(n=n, cls=cls, a=a, b=b, T=T, cad=os.path.abspath(cad), drat=os.path.abspath(drat), wd=wd)
    reps = rep_cubes(T)
    assert check_cover(reps, T)
    tags = {''.join(map(str, c)): c for c in reps}
    base_sha = hashlib.sha256(repr(cls).encode()).hexdigest()
    header = {'header': True, 'n': n, 'g': g, 'z0': z0, 'T': T, 'pairs': npairs,
              'cubes_total': 16 ** T, 'cube_reps': len(reps), 'base_sha256': base_sha}
    good = {}          # tag -> record, validated (reused) or produced in this run
    reused = superseded = 0
    if os.path.exists(out) and os.path.getsize(out) > 0:
        hdr, recs = read_records(out)
        if hdr != header:
            print(json.dumps({'error': 'header of %s does not match this run; refusing to reuse it' % out,
                              'found': hdr, 'expected': header}))
            sys.exit(2)
        unknown = sorted(set(r['cube'] for r in recs) - set(tags))
        if unknown:
            print(json.dumps({'error': 'records for cubes that are not orbit representatives', 'cubes': unknown[:5]}))
            sys.exit(2)
        latest = {}
        for r in recs:
            superseded += r['cube'] in latest
            latest[r['cube']] = r
        cand = [t for t, r in latest.items() if r.get('result') == 'UNSAT' and r.get('drat') == 'VERIFIED']
        with Pool(jobs) as P:
            for t, h in P.imap_unordered(cube_hash, [tags[t] for t in cand]):
                if h == latest[t]['cnf_sha256']:
                    good[t] = latest[t]; reused += 1
        if not open(out).read().endswith('\n'):
            open(out, 'a').write('\n')
    else:
        with open(out, 'w') as f:
            f.write(json.dumps(header) + '\n')
    todo = [c for t, c in tags.items() if t not in good]
    with open(out, 'a') as f:
        with Pool(jobs) as P:
            for rec in P.imap_unordered(solve_cube, todo):
                f.write(json.dumps(rec) + '\n')
                f.flush()
                if rec['result'] == 'UNSAT' and rec['drat'] == 'VERIFIED':
                    good[rec['cube']] = rec
    hdr, recs = read_records(out)
    ok = hdr == header and set(good) == set(tags) and all(r['result'] == 'UNSAT' and r['drat'] == 'VERIFIED' for r in good.values())
    cubes = list(good.values())
    print(json.dumps({'n': n, 'g': g, 'z0': z0, 'T': T, 'cube_reps': len(reps), 'pairs': npairs, 'all_unsat_verified': ok,
                      'reused': reused, 'solved': len(todo), 'superseded_records': superseded,
                      't_solve': round(sum(r['t_solve'] for r in cubes), 1), 't_check': round(sum(r['t_check'] for r in cubes), 1),
                      'max_proof_bytes': max((r['proof_bytes'] for r in cubes), default=0)}))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
