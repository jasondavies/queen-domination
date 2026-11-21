#!/usr/bin/env python3
"""Independent enumeration of the (frame, deficit) cases of the frame method (PROOFS.md F.0-F.2),
written for the n = 35 cross-check without using geom.py.

Board squares (x, y) = (column, row), 0 <= x, y < n.  A case is (ml, mr, mb, mt, dR, dC, dT, dS) with
box columns [a, b] = [ml, n-1-mr], rows [c, d] = [mb, n-1-mt].

The action of the 8 board symmetries on cases is NOT taken from a table: it is computed geometrically
by applying each symmetry to the box and to sample lines (sym_case below), so a wrong table in geom.py
would show up as a disagreement of the case lists.

Necessary conditions for a dominating k-set D (k <= n-2) with case c (derived from PROOFS F.1/F.2):
  0 <= dX <= k-1 (some line of each type is occupied);
  ml + mr <= k - dC, mb + mt <= k - dR (all columns outside [a,b] / rows outside [c,d] are occupied);
  w = b - a >= 1, h = d - c >= 1;
  Theorem F with U = 0 and nonnegative left side: 8k - 4n + 4 - 2(dR+dC+dT+dS) >= 0;
  Theorem V (w >= h): 4k - 2n - dT - dS - 2dR + 2[w = h] >= 0   (u0, v0 terms are at most 2);
  Theorem H (h >= w): 4k - 2n - dT - dS - 2dC + 2[w = h] >= 0.
Case list = every canonical frame (lexicographically least frame in its symmetry orbit) with every deficit
vector satisfying the conditions (no reduction of the deficit vector by the frame stabiliser).
"""
import itertools
import sys


def symmetries(n):
    """the 8 symmetries as functions on squares, generated from the two reflections (closure computed)"""
    m = n - 1
    gens = [lambda p: (m - p[0], p[1]), lambda p: (p[1], p[0])]
    pts = [(0, 0), (1, 0), (0, 1), (2, 3)]          # enough to identify an affine symmetry
    group = {tuple(pts): (lambda p: p)}
    frontier = [lambda p: p]
    while frontier:
        new = []
        for f in frontier:
            for g in gens:
                h = (lambda f, g: (lambda p: g(f(p))))(f, g)
                key = tuple(h(p) for p in pts)
                if key not in group:
                    group[key] = h
                    new.append(h)
        frontier = new
    assert len(group) == 8
    return list(group.values())


def line_type_map(n, g):
    """for a symmetry g: (rows map to rows?, difference diagonals map to difference diagonals?)"""
    p, q = g((1, 1)), g((2, 1))                     # two squares on a common row
    rows_to_rows = (p[1] == q[1])
    assert rows_to_rows or p[0] == q[0]
    p, q = g((1, 1)), g((2, 2))                     # two squares on a common difference diagonal
    diff_to_diff = (q[1] - q[0] == p[1] - p[0])
    assert diff_to_diff or q[0] + q[1] == p[0] + p[1]
    return rows_to_rows, diff_to_diff


def sym_case(n, g, case):
    ml, mr, mb, mt, dR, dC, dT, dS = case
    a, b, c, d = ml, n - 1 - mr, mb, n - 1 - mt
    # the box is the product of the interval of empty-column extremes and of empty-row extremes;
    # its image under g is the box spanned by the images of two opposite corners
    p, q = g((a, c)), g((b, d))
    a2, b2 = min(p[0], q[0]), max(p[0], q[0])
    c2, d2 = min(p[1], q[1]), max(p[1], q[1])
    rr, dd = line_type_map(n, g)
    dR2, dC2 = (dR, dC) if rr else (dC, dR)
    dT2, dS2 = (dT, dS) if dd else (dS, dT)
    return (a2, n - 1 - b2, c2, n - 1 - d2, dR2, dC2, dT2, dS2)


def conditions(n, k, case):
    ml, mr, mb, mt, dR, dC, dT, dS = case
    if not all(0 <= v <= k - 1 for v in (dR, dC, dT, dS)):
        return False
    if min(ml, mr, mb, mt) < 0:
        return False
    if ml + mr > k - dC or mb + mt > k - dR:
        return False
    w, h = n - 1 - ml - mr, n - 1 - mb - mt
    if w < 1 or h < 1:
        return False
    if 8 * k - 4 * n + 4 - 2 * (dR + dC + dT + dS) < 0:
        return False
    sq = 2 if w == h else 0
    if w >= h and 4 * k - 2 * n - dT - dS - 2 * dR + sq < 0:
        return False
    if h >= w and 4 * k - 2 * n - dT - dS - 2 * dC + sq < 0:
        return False
    return True


def frames(n, k):
    """all frames (ml, mr, mb, mt) that can occur for some k-set with >= 2 empty rows and columns"""
    out = []
    for ml, mr, mb, mt in itertools.product(range(k + 1), repeat=4):
        if ml + mr <= k and mb + mt <= k and n - 1 - ml - mr >= 1 and n - 1 - mb - mt >= 1:
            out.append((ml, mr, mb, mt))
    return out


def canonical_frames(n, k):
    G = symmetries(n)
    res = []
    for f in frames(n, k):
        imgs = [sym_case(n, g, f + (0, 0, 0, 0))[:4] for g in G]
        if f == min(imgs):
            res.append(f)
    return res


def case_list(n, k):
    res = []
    # pre-filter by the condition (F), which does not involve the frame (pure speed-up; conditions() re-checks)
    dvs = [dv for dv in itertools.product(range(k), repeat=4) if 8 * k - 4 * n + 4 - 2 * sum(dv) >= 0]
    for f in canonical_frames(n, k):
        for dv in dvs:
            if conditions(n, k, f + dv):
                res.append(f + dv)
    return res


def case_of_set(n, D):
    """case of a set D with >= 2 empty rows and columns (None otherwise)"""
    k = len(D)
    R = {y for x, y in D}; C = {x for x, y in D}
    T = {y - x for x, y in D}; S = {x + y for x, y in D}
    ec = [x for x in range(n) if x not in C]; er = [y for y in range(n) if y not in R]
    if len(ec) < 2 or len(er) < 2:
        return None
    return (ec[0], n - 1 - ec[-1], er[0], n - 1 - er[-1], k - len(R), k - len(C), k - len(T), k - len(S))


def dominates(n, D):
    R = {y for x, y in D}; C = {x for x, y in D}
    T = {y - x for x, y in D}; S = {x + y for x, y in D}
    return all(y in R or x in C or (y - x) in T or (x + y) in S for x in range(n) for y in range(n))


def canonical_image(n, D):
    """an image of D under a board symmetry whose frame is canonical (and that image's case)"""
    best = None
    for g in symmetries(n):
        E = sorted(g(p) for p in D)
        c = case_of_set(n, E)
        if best is None or c[:4] < best[0][:4]:
            best = (c, E)
    return best


def self_test(n=9, trials=3000, seed=1):
    """sym_case agrees with the case of the transformed set, on random sets"""
    import random
    rnd = random.Random(seed)
    G = symmetries(n)
    cnt = 0
    for _ in range(trials):
        k = rnd.randint(1, n - 2)
        D = rnd.sample([(x, y) for x in range(n) for y in range(n)], k)
        c = case_of_set(n, D)
        if c is None:
            continue
        for g in G:
            assert sym_case(n, g, c) == case_of_set(n, [g(p) for p in D]), (D, c)
        cnt += 1
    return cnt


if __name__ == '__main__':
    n, k = int(sys.argv[1]), int(sys.argv[2])
    print('symmetry self-test on', self_test(), 'random sets: ok')
    cf = canonical_frames(n, k)
    cl = case_list(n, k)
    print('n=%d k=%d canonical frames %d cases %d' % (n, k, len(cf), len(cl)))
