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
       (resumable: cubes already recorded in OUT.jsonl are skipped)
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


def solve_cube(cube):
    n, cls, a, b, T, cad, drat, wd = (_CTX[k] for k in ('n', 'cls', 'a', 'b', 'T', 'cad', 'drat', 'wd'))
    lits = []
    for (kind, i), v in zip(cube_vars(n, T), cube):
        var = a[i] if kind == 'a' else b[i]
        lits.append(var if v else -var)
    allc = cls + [[l] for l in lits]
    nv = max(abs(l) for c in allc for l in c)
    cnf = 'p cnf %d %d\n' % (nv, len(allc)) + ''.join(' '.join(map(str, c)) + ' 0\n' for c in allc)
    h = hashlib.sha256(cnf.encode()).hexdigest()
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


def main():
    n, g, z0 = map(int, sys.argv[1:4])
    surv, cad, drat, wd = sys.argv[4:8]
    T, jobs, out = int(sys.argv[8]), int(sys.argv[9]), sys.argv[10]
    os.makedirs(wd, exist_ok=True)
    cls, a, b, npairs = build_base(n, g, z0, surv)
    _CTX.update(n=n, cls=cls, a=a, b=b, T=T, cad=os.path.abspath(cad), drat=os.path.abspath(drat), wd=wd)
    reps = rep_cubes(T)
    assert check_cover(reps, T)
    done = set()
    if os.path.exists(out):
        done = set(json.loads(l)['cube'] for l in open(out) if l.strip() and 'cube' in json.loads(l))
    todo = [c for c in reps if ''.join(map(str, c)) not in done]
    base_sha = hashlib.sha256(repr(cls).encode()).hexdigest()
    with open(out, 'a') as f:
        if not done:
            f.write(json.dumps({'header': True, 'n': n, 'g': g, 'z0': z0, 'T': T, 'pairs': npairs,
                                'cubes_total': 16 ** T, 'cube_reps': len(reps), 'base_sha256': base_sha}) + '\n')
        with Pool(jobs) as P:
            for rec in P.imap_unordered(solve_cube, todo):
                f.write(json.dumps(rec) + '\n')
                f.flush()
    recs = [json.loads(l) for l in open(out) if l.strip()]
    cubes = [r for r in recs if 'cube' in r]
    ok = (len(set(r['cube'] for r in cubes)) == len(reps) and all(r['result'] == 'UNSAT' and r['drat'] == 'VERIFIED' for r in cubes))
    print(json.dumps({'n': n, 'g': g, 'z0': z0, 'T': T, 'cube_reps': len(reps), 'pairs': npairs, 'all_unsat_verified': ok,
                      't_solve': round(sum(r['t_solve'] for r in cubes), 1), 't_check': round(sum(r['t_check'] for r in cubes), 1),
                      'max_proof_bytes': max((r['proof_bytes'] for r in cubes), default=0)}))


if __name__ == '__main__':
    main()
