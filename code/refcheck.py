#!/usr/bin/env python3
"""Independent referee checks of the two-stage computation, written separately from the C programs.

Everything here is formulated as SAT and solved with CaDiCaL (through python-sat, or the pinned
stand-alone binary when a DRAT proof is wanted).  Nothing is shared with stage1.c / stage1_v.c /
place.c except the input/output format "C A B z0" (hex bitmasks of the row set A and column set B).

Board: squares (r, x), 0 <= r, x < n; colour (r + x) mod 2; difference line r - x; sum line r + x.

relax_cnf(n, g, z0)  -- the line relaxation of Lemma 2.2 as CNF:
    a_r  (row r in A),  b_x  (column x in B),  |A| = |B| = n - g,
    y_d  (difference line d chosen), w_s (sum line s chosen),
    for every colour q: #{chosen difference lines of colour q} <= z_q, same for sum lines,
    for every square (r, x):  a_r & b_x  ->  y_{r-x} | w_{r+x}.
  Its models restricted to (a, b) are exactly the feasible pairs (A, B).

dom_cnf(n, g, z, region) -- "a set of queens inside region, with exactly z_q of colour q, dominates Q_n".

Subcommands (all print one JSON object):
  pairs N G Z0                 all feasible pairs up to the 4 colour-preserving symmetries (orbit keys)
  compare N G Z0 FILE          orbit set of FILE ("C A B z0" lines) == orbit set from `pairs`
  compare_c STAGE1 N G Z0      same, with FILE replaced by the output of the program STAGE1 N G Z0
  pipeline N G                 full independent pipeline: pairs for every z0 <= G/2, then all dominating
                               sets inside each pair's region; number of D4-classes of G-dominating sets
  direct N G                   all G-dominating sets of Q_n by a plain SAT enumeration (no relaxation)
  suite STAGE1 NMAX             the referee's small-n suite: compare_c for even n <= NMAX and every z0,
                               pipeline and direct for the cases listed in SUITE_PIPE / SUITE_DIRECT
  encode_check SURVIVORS KAMENETSKY  sanity checks of the two CNF encoders against known positives:
                               every listed n = 26 pair satisfies relax_cnf; the known 14-queen
                               dominating sets of Q_26 satisfy sat_place.build for g = 14
  cert N G Z0 FILE CADICAL DRATTRIM WORKDIR
                               write relax_cnf + one blocking clause for every symmetric image of every
                               pair in FILE, solve with CaDiCaL writing a DRAT proof, check it with
                               drat-trim.  UNSAT + VERIFIED certifies that FILE contains (up to symmetry)
                               every feasible pair, i.e. it certifies stage 1 for (N, G, Z0).
"""
import hashlib, json, os, subprocess, sys, time
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver


def rev(m, n):
    return sum(1 << (n - 1 - i) for i in range(n) if m >> i & 1)


def images(A, B, n):
    """(A, B) under id, transpose, half-turn, anti-transpose: the colour-preserving symmetries."""
    rA, rB = rev(A, n), rev(B, n)
    return [(A, B), (B, A), (rA, rB), (rB, rA)]


def orbit_key(A, B, n):
    return min(images(A, B, n))


def bits(m, n):
    return [i for i in range(n) if m >> i & 1]


def relax_cnf(n, g, z0):
    s, z = n - g, (z0, g - z0)
    pool = IDPool()
    a = [pool.id(('a', r)) for r in range(n)]
    b = [pool.id(('b', x)) for x in range(n)]
    y = {d: pool.id(('y', d)) for d in range(-(n - 1), n)}
    w = {t: pool.id(('w', t)) for t in range(0, 2 * n - 1)}
    cls = []
    for lits in (a, b):
        enc = CardEnc.equals(lits=lits, bound=s, vpool=pool, encoding=EncType.seqcounter)
        cls += enc.clauses
    for q in (0, 1):
        for fam in (y, w):
            lits = [v for k, v in fam.items() if k % 2 == q]
            if z[q] < len(lits):
                cls += CardEnc.atmost(lits=lits, bound=z[q], vpool=pool, encoding=EncType.seqcounter).clauses
    for r in range(n):
        for x in range(n):
            cls.append([-a[r], -b[x], y[r - x], w[r + x]])
    return cls, a, b, pool


def block(A, B, a, b, n):
    return [-a[r] for r in bits(A, n)] + [-b[x] for x in bits(B, n)]


def feasible_orbits(n, g, z0):
    cls, a, b, pool = relax_cnf(n, g, z0)
    orbits = set()
    with Solver(name='cadical195', bootstrap_with=cls) as S:
        while S.solve():
            m = set(l for l in S.get_model() if l > 0)
            A = sum(1 << r for r in range(n) if a[r] in m)
            B = sum(1 << x for x in range(n) if b[x] in m)
            orbits.add(orbit_key(A, B, n))
            for (P, Q) in set(images(A, B, n)):
                S.add_clause(block(P, Q, a, b, n))
    return orbits


def read_pairs(path, z0=None):
    out = []
    for line in open(path):
        p = line.split()
        if p and p[0] == 'C' and (z0 is None or int(p[3]) == z0):
            out.append((int(p[1], 16), int(p[2], 16), int(p[3])))
    return out


def attacks(r, x, r2, x2):
    return r == r2 or x == x2 or r - x == r2 - x2 or r + x == r2 + x2


def dom_cnf(n, z, cells):
    """queens on `cells`, exactly z[q] of colour q, dominating every square of Q_n."""
    pool = IDPool()
    v = {c: pool.id(c) for c in cells}
    cls = [[v[c] for c in cells if attacks(r, x, *c)] for r in range(n) for x in range(n)]
    for q in (0, 1):
        lits = [v[c] for c in cells if sum(c) % 2 == q]
        if z[q] > len(lits):
            return None, v
        cls += CardEnc.equals(lits=lits, bound=z[q], vpool=pool, encoding=EncType.seqcounter).clauses
    return cls, v


def all_dominating(n, z, cells):
    cls, v = dom_cnf(n, z, cells)
    sols = []
    if cls is None or any(len(c) == 0 for c in cls):
        return sols
    with Solver(name='cadical195', bootstrap_with=cls) as S:
        while S.solve():
            m = set(l for l in S.get_model() if l > 0)
            D = tuple(sorted(c for c in cells if v[c] in m))
            sols.append(D)
            S.add_clause([-v[c] for c in D])
    return sols


def d4_key(D, n):
    keys = []
    for k in range(8):
        T = []
        for (r, x) in D:
            for _ in range(k % 4):
                r, x = x, n - 1 - r
            if k >= 4:
                x = n - 1 - x
            T.append((r, x))
        keys.append(tuple(sorted(T)))
    return min(keys)


def pipeline(n, g):
    t0 = time.time()
    classes, npairs = set(), {}
    for z0 in range(0, g // 2 + 1):
        orb = feasible_orbits(n, g, z0)
        npairs[z0] = len(orb)
        for (A, B) in orb:
            cells = [(r, x) for r in range(n) if not A >> r & 1 for x in range(n) if not B >> x & 1]
            for D in all_dominating(n, (z0, g - z0), cells):
                classes.add(d4_key(D, n))
    mono = sum(1 for D in classes if len(set(sum(c) % 2 for c in D)) == 1)
    return {'n': n, 'g': g, 'pairs_per_z0': npairs, 'classes': len(classes), 'monochromatic': mono,
            'seconds': round(time.time() - t0, 1)}


def direct(n, g):
    t0 = time.time()
    cells = [(r, x) for r in range(n) for x in range(n)]
    classes = set()
    for z0 in range(0, g + 1):
        for D in all_dominating(n, (z0, g - z0), cells):
            classes.add(d4_key(D, n))
    return {'n': n, 'g': g, 'classes': len(classes), 'seconds': round(time.time() - t0, 1)}


def cert(n, g, z0, path, cadical, drat, wd):
    cls, a, b, pool = relax_cnf(n, g, z0)
    pairs = read_pairs(path, z0)
    for (A, B, _) in pairs:
        for (P, Q) in set(images(A, B, n)):
            cls.append(block(P, Q, a, b, n))
    nv = max(abs(l) for c in cls for l in c)
    cnf = 'p cnf %d %d\n' % (nv, len(cls)) + ''.join(' '.join(map(str, c)) + ' 0\n' for c in cls)
    os.makedirs(wd, exist_ok=True)
    h = hashlib.sha256(cnf.encode()).hexdigest()
    fc, fp = os.path.join(wd, 'cert_%d_%d_%d.cnf' % (n, g, z0)), os.path.join(wd, 'cert_%d_%d_%d.drat' % (n, g, z0))
    open(fc, 'w').write(cnf)
    t0 = time.time()
    r = subprocess.run([cadical, '-q', '--no-binary', fc, fp], capture_output=True, text=True)
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
    return {'n': n, 'g': g, 'z0': z0, 'pairs': len(pairs), 'vars': nv, 'clauses': len(cls), 'cnf_sha256': h,
            'result': res, 'drat': chk, 'proof_bytes': psize, 't_solve': round(t1 - t0, 1), 't_check': round(t2 - t1, 1)}


SUITE_PIPE = [(4, 2), (6, 3), (8, 4), (10, 5), (12, 6), (8, 5)]
SUITE_DIRECT = [(4, 2), (6, 3), (8, 4), (10, 5), (8, 5)]


def suite(stage1, nmax):
    out = {'compare': [], 'pipeline': [], 'direct': []}
    for n in range(4, nmax + 1, 2):
        g = n // 2
        for z0 in range(g // 2 + 1):
            txt = subprocess.run([stage1, str(n), str(g), str(z0)], capture_output=True, text=True, check=True).stdout
            theirs = set(orbit_key(int(p[1], 16), int(p[2], 16), n) for p in (l.split() for l in txt.splitlines()) if p and p[0] == 'C')
            mine = feasible_orbits(n, g, z0)
            out['compare'].append({'n': n, 'z0': z0, 'orbits': len(mine), 'equal': mine == theirs})
    out['pipeline'] = [pipeline(n, g) for n, g in SUITE_PIPE]
    out['direct'] = [direct(n, g) for n, g in SUITE_DIRECT]
    return out


def encode_check(surv, kam):
    n, g = 26, 13
    cls, a, b, pool = relax_cnf(n, g, 6)
    cls0 = relax_cnf(n, g, 0)
    ok_pairs = 0
    pairs = read_pairs(surv)
    solvers = {6: Solver(name='cadical195', bootstrap_with=cls), 0: Solver(name='cadical195', bootstrap_with=cls0[0])}
    for (A, B, z0) in pairs:
        S, aa, bb = (solvers[6], a, b) if z0 == 6 else (solvers[0], cls0[1], cls0[2])
        assum = [aa[r] if A >> r & 1 else -aa[r] for r in range(n)] + [bb[x] if B >> x & 1 else -bb[x] for x in range(n)]
        ok_pairs += bool(S.solve(assumptions=assum))
    for S in solvers.values():
        S.delete()
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import sat_place
    from check_upper import ow_sets
    rows = [l.rstrip('\n') for l in open(kam) if l.strip()]
    sets = {'kamenetsky26': [(r, c) for r in range(26) for c in range(26) if rows[r][c] == 'Q'], 'ow26': ow_sets()[1]}
    known = {}
    for name, Q in sets.items():
        A = sum(1 << r for r in range(26) if all(q[0] != r for q in Q))
        B = sum(1 << c for c in range(26) if all(q[1] != c for q in Q))
        # keep exactly 26 - 14 = 12 empty rows and columns, as stage 1 would
        A = sum(1 << r for r in bits(A, 26)[:12]); B = sum(1 << c for c in bits(B, 26)[:12])
        z0 = sum(1 for (r, c) in Q if (r + c) % 2 == 0)
        txt = sat_place.build(26, 14, A, B, z0).splitlines()[1:]
        clauses = [list(map(int, l.split()))[:-1] for l in txt]
        cells = [(r, c) for r in range(26) if not A >> r & 1 for c in range(26) if not B >> c & 1]
        var = {p: i + 1 for i, p in enumerate(cells)}
        with Solver(name='cadical195', bootstrap_with=clauses) as S:
            known[name] = bool(S.solve(assumptions=[var[p] if p in Q else -var[p] for p in cells]))
    return {'pairs': len(pairs), 'pairs_satisfy_relaxation': ok_pairs, 'known_sets_satisfy_sat_place': known}


def main():
    cmd, args = sys.argv[1], sys.argv[2:]
    if cmd == 'pairs':
        n, g, z0 = map(int, args[:3])
        orb = feasible_orbits(n, g, z0)
        out = {'n': n, 'g': g, 'z0': z0, 'orbits': len(orb),
               'sha256': hashlib.sha256(repr(sorted(orb)).encode()).hexdigest()}
    elif cmd == 'compare':
        n, g, z0 = map(int, args[:3])
        mine = feasible_orbits(n, g, z0)
        theirs = set(orbit_key(A, B, n) for (A, B, z) in read_pairs(args[3]) if z == z0)
        out = {'n': n, 'g': g, 'z0': z0, 'orbits_sat': len(mine), 'orbits_file': len(theirs), 'equal': mine == theirs}
    elif cmd == 'compare_c':
        n, g, z0 = map(int, args[1:4])
        txt = subprocess.run([args[0], str(n), str(g), str(z0)], capture_output=True, text=True, check=True).stdout
        theirs = set(orbit_key(int(p[1], 16), int(p[2], 16), n) for p in (l.split() for l in txt.splitlines()) if p and p[0] == 'C')
        mine = feasible_orbits(n, g, z0)
        out = {'n': n, 'g': g, 'z0': z0, 'orbits_sat': len(mine), 'orbits_c': len(theirs), 'equal': mine == theirs}
    elif cmd == 'pipeline':
        out = pipeline(int(args[0]), int(args[1]))
    elif cmd == 'direct':
        out = direct(int(args[0]), int(args[1]))
    elif cmd == 'suite':
        out = suite(args[0], int(args[1]))
    elif cmd == 'encode_check':
        out = encode_check(args[0], args[1])
    elif cmd == 'cert':
        out = cert(int(args[0]), int(args[1]), int(args[2]), args[3], args[4], args[5], args[6])
    else:
        raise SystemExit(__doc__)
    print(json.dumps(out), flush=True)


if __name__ == '__main__':
    main()
