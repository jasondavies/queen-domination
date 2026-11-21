#!/usr/bin/env python3
"""Brute-force test of the identities (F), (V), (H) in their general form (any set D of k squares with at
least two empty rows and two empty columns, dominating or not):

 (F)  sum_{occupied diagonals L} (2 - beta(L)) + #{(L, s): L occupied, s non-needy border square on L}
        + #{needy border squares on two occupied diagonals}
      = 8k - 4n + 4 - 2(dR + dC + dT + dS) + U_F,        U_F = #{needy border squares on no occupied diagonal}
 (V)  [w >= h]  #{occupied L meeting no vertical-side square} + #{(L, s): L occupied, s non-needy vertical-side
        square on L} + #{needy vertical-side squares on two occupied diagonals}
      = 4k - 2n - dT - dS - 2 dR + [w = h]([u0 occupied] + [v0 occupied]) + U_V
 (H)  [h >= w]  the same with horizontal sides and dC.
For a dominating set U_F = U_V = U_H = 0.  Also tested: the border has exactly 2(n-|R|) + 2(n-|C|) - 4 needy
squares (corners once), every diagonal has beta <= 2 border squares, a diagonal has two vertical-side squares
only if w = h and it is u0 (difference diagonal c - a) or v0 (sum diagonal a + d) (and never if w > h),
no border square is occupied, and the table geom.case_images is the action of the 8 symmetries on cases.
All counts are done by listing squares; nothing is taken from the proofs.
usage: verify_identities.py [seed]"""
import itertools, random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import *

STAT = {'sets': 0, 'dominating': 0, 'w=h': 0, 'w>h': 0, 'w<h': 0, 'w=1 or h=1': 0, 'box=board': 0, 'deficit>0': 0}


def check(n, D):
    D = set(D); k = len(D)
    fr = frame_of(n, D)
    if fr is None:
        return
    a, b, c, d = fr; w, h = b - a, d - c
    R, C, T, S = lines(D)
    dR, dC, dT, dS = k - len(R), k - len(C), k - len(T), k - len(S)
    needy = lambda s: s[0] not in C and s[1] not in R
    occ = [('T', t) for t in T] + [('S', s) for s in S]
    on = lambda L, s: (s[1] - s[0] == L[1]) if L[0] == 'T' else (s[0] + s[1] == L[1])
    Bd = border(a, b, c, d)
    assert len(Bd) == len(set(Bd)) == 2 * w + 2 * h
    assert not (set(Bd) & D), 'occupied border square'
    assert sum(needy(s) for s in Bd) == 2 * (n - len(R)) + 2 * (n - len(C)) - 4
    for kind, rng in (('T', range(-(n - 1), n)), ('S', range(0, 2 * n - 1))):
        for i in rng:
            assert sum(on((kind, i), s) for s in Bd) <= 2
    def lhs(sq, full):
        m = {s: sum(on(L, s) for L in occ) for s in sq}
        x = sum((2 if full else 1) - sum(on(L, s) for s in sq) for L in occ) if full else sum(1 for L in occ if not any(on(L, s) for s in sq))
        x += sum(m[s] for s in sq if not needy(s))
        x += sum(1 for s in sq if needy(s) and m[s] == 2)
        U = sum(1 for s in sq if needy(s) and m[s] == 0)
        return x, U
    x, U = lhs(Bd, True)
    assert x == 8 * k - 4 * n + 4 - 2 * (dR + dC + dT + dS) + U, ('F', n, sorted(D))
    dom = dominated(n, D)
    if dom:
        assert U == 0
    u0 = ('T', c - a) in occ; v0 = ('S', a + d) in occ
    for name, sq, dd, cond in (('V', vsides(a, b, c, d), dR, w >= h), ('H', hsides(a, b, c, d), dC, h >= w)):
        if not cond:
            continue
        for kind, rng in (('T', range(-(n - 1), n)), ('S', range(0, 2 * n - 1))):
            for i in rng:
                cnt = sum(on((kind, i), s) for s in sq)
                assert cnt <= 1 or (w == h and (kind, i) in (('T', c - a), ('S', a + d)) and cnt == 2)
        assert sum(needy(s) for s in sq) == 2 * (n - (len(R) if name == 'V' else len(C)))
        x, U = lhs(sq, False)
        assert x == 4 * k - 2 * n - dT - dS - 2 * dd + (u0 + v0 if w == h else 0) + U, (name, n, sorted(D))
        if dom:
            assert U == 0
    # symmetry table
    case = case_of(n, D)
    for g, img in zip(sym_maps(n), case_images(case)):
        assert case_of(n, {g(x, y) for x, y in D}) == img
    STAT['sets'] += 1; STAT['dominating'] += dom
    STAT['w=h' if w == h else ('w>h' if w > h else 'w<h')] += 1
    STAT['w=1 or h=1'] += (w == 1 or h == 1); STAT['box=board'] += (w == n - 1 and h == n - 1)
    STAT['deficit>0'] += (dR + dC + dT + dS > 0)


def main():
    rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    # exhaustive: all sets of k squares, n <= 5 (k <= n - 2 is not required: any set with a frame is tested)
    for n in (3, 4, 5):
        sq = [(x, y) for x in range(n) for y in range(n)]
        for k in range(1, n + 1):
            for D in itertools.combinations(sq, k):
                check(n, D)
    print('exhaustive n <= 5:', STAT, flush=True)
    # random sets, all sizes, n up to 16 (with repeated rows/columns/diagonals forced in part of the samples)
    for it in range(60000):
        n = rnd.randint(4, 16); k = rnd.randint(1, n)
        sq = [(x, y) for x in range(n) for y in range(n)]
        mode = rnd.random()
        if mode < 0.4:
            D = rnd.sample(sq, k)
        elif mode < 0.7:      # concentrated in few rows/columns -> big deficits, small boxes at the edge
            xs = rnd.sample(range(n), rnd.randint(1, max(1, n - 2))); ys = rnd.sample(range(n), rnd.randint(1, max(1, n - 2)))
            D = {(rnd.choice(xs), rnd.choice(ys)) for _ in range(k)}
        else:                 # leave exactly two empty rows and/or columns, possibly adjacent (degenerate boxes w = 1 / h = 1)
            ex = sorted(rnd.sample(range(n), 2)) if rnd.random() < 0.5 else [rnd.randrange(n - 1)]
            ex = ex if len(ex) == 2 else [ex[0], ex[0] + 1]
            ey = sorted(rnd.sample(range(n), 2)) if rnd.random() < 0.5 else [rnd.randrange(n - 1)]
            ey = ey if len(ey) == 2 else [ey[0], ey[0] + 1]
            xs = [x for x in range(n) if x not in ex]; ys = [y for y in range(n) if y not in ey]
            D = {(x, rnd.choice(ys)) for x in xs} | {(rnd.choice(xs), y) for y in ys}
        check(n, D)
    print('after random sets:', STAT, flush=True)
    # random DOMINATING sets: random greedy completions on boards up to 14
    for it in range(4000):
        n = rnd.randint(5, 14)
        D = set()
        cells = [(x, y) for x in range(n) for y in range(n)]
        rnd.shuffle(cells)
        ex = set(rnd.sample(range(n), 2)); ey = set(rnd.sample(range(n), 2))
        for s in cells:
            if dominated(n, D):
                break
            if s[0] in ex or s[1] in ey:
                continue
            D.add(s)
        if dominated(n, D):
            check(n, D)
    print('after random dominating sets:', STAT)
    print('ALL IDENTITIES OK')


if __name__ == '__main__':
    main()
