#!/usr/bin/env python3
"""Geometry of the frame method.  Squares are (x, y) = (column, row), 0 <= x, y < n.
Difference diagonal of (x, y): t = y - x;  sum diagonal: s = x + y.
For a set D of squares:  R, C, T, S = occupied rows, columns, difference diagonals, sum diagonals.
Extreme empty columns a < b, extreme empty rows c < d (they exist iff >= 2 empty columns and rows).
Box = [a, b] x [c, d];  border = squares of the box with x in {a, b} or y in {c, d};  w = b - a, h = d - c.
A square is needy iff its column and its row are both empty."""


def lines(D):
    return ({y for x, y in D}, {x for x, y in D}, {y - x for x, y in D}, {x + y for x, y in D})


def frame_of(n, D):
    R, C, T, S = lines(D)
    ER = [y for y in range(n) if y not in R]; EC = [x for x in range(n) if x not in C]
    if len(ER) < 2 or len(EC) < 2:
        return None
    return EC[0], EC[-1], ER[0], ER[-1]


def border(a, b, c, d):
    return [(x, y) for x in range(a, b + 1) for y in range(c, d + 1) if x in (a, b) or y in (c, d)]


def vsides(a, b, c, d):
    return [(x, y) for x in (a, b) for y in range(c, d + 1)]


def hsides(a, b, c, d):
    return [(x, y) for y in (c, d) for x in range(a, b + 1)]


def dominated(n, D):
    R, C, T, S = lines(D)
    return all(y in R or x in C or (y - x) in T or (x + y) in S for x in range(n) for y in range(n))


# the 8 symmetries of the board, as maps on squares
def sym_maps(n):
    m = n - 1
    return [lambda x, y: (x, y), lambda x, y: (m - x, y), lambda x, y: (x, m - y), lambda x, y: (m - x, m - y),
            lambda x, y: (y, x), lambda x, y: (m - y, x), lambda x, y: (y, m - x), lambda x, y: (m - y, m - x)]


def case_images(case):
    """images of a case (ml, mr, mb, mt, dR, dC, dT, dS) under the 8 symmetries, in the order of sym_maps:
    ml = a, mr = n-1-b (left/right margins, counted in columns), mb = c, mt = n-1-d."""
    ml, mr, mb, mt, dR, dC, dT, dS = case
    return [(ml, mr, mb, mt, dR, dC, dT, dS),          # identity
            (mr, ml, mb, mt, dR, dC, dS, dT),          # x -> m-x : swaps left/right, difference <-> sum
            (ml, mr, mt, mb, dR, dC, dS, dT),          # y -> m-y
            (mr, ml, mt, mb, dR, dC, dT, dS),          # half-turn
            (mb, mt, ml, mr, dC, dR, dT, dS),          # transpose (x,y)->(y,x): rows <-> columns
            (mt, mb, ml, mr, dC, dR, dS, dT),          # (x,y)->(m-y,x)
            (mb, mt, mr, ml, dC, dR, dS, dT),          # (x,y)->(y,m-x)
            (mt, mb, mr, ml, dC, dR, dT, dS)]          # anti-transpose (x,y)->(m-y,m-x)


def case_of(n, D):
    k = len(D)
    R, C, T, S = lines(D)
    a, b, c, d = frame_of(n, D)
    return (a, n - 1 - b, c, n - 1 - d, k - len(R), k - len(C), k - len(T), k - len(S))


def canonical(case):
    return min(case_images(case))


def admissible(n, k, case):
    """necessary conditions for a dominating k-set with this case (NOTES, section F.2); k <= n - 2"""
    ml, mr, mb, mt, dR, dC, dT, dS = case
    if min(dR, dC, dT, dS) < 0 or max(dR, dC, dT, dS) > k - 1:
        return False
    if ml + mr > k - dC or mb + mt > k - dR:         # the margin columns/rows are occupied, pairwise distinct
        return False
    w = n - 1 - ml - mr; h = n - 1 - mb - mt
    if w < 1 or h < 1:
        return False
    if 8 * k - 4 * n + 4 - 2 * (dR + dC + dT + dS) < 0:                      # (F)
        return False
    sq = 2 if w == h else 0
    if w >= h and 4 * k - 2 * n - dT - dS - 2 * dR + sq < 0:                  # (V)
        return False
    if h >= w and 4 * k - 2 * n - dT - dS - 2 * dC + sq < 0:                  # (H)
        return False
    return True


def all_cases(n, k):
    """canonical admissible cases with their orbit sizes"""
    out = {}
    dm = k - 1                       # each deficit is at most k - 1
    sm = 4 * k - 2 * n + 2           # (F): the deficits sum to at most 4k - 2n + 2
    for ml in range(0, k + 1):
        for mr in range(0, k + 1 - ml):
            for mb in range(0, k + 1):
                for mt in range(0, k + 1 - mb):
                    for dR in range(0, dm + 1):
                        for dC in range(0, dm + 1):
                            for dT in range(0, dm + 1):
                                for dS in range(0, dm + 1):
                                    if dR + dC + dT + dS > sm:
                                        continue
                                    case = (ml, mr, mb, mt, dR, dC, dT, dS)
                                    if not admissible(n, k, case):
                                        continue
                                    imgs = case_images(case)
                                    if case == min(imgs):
                                        out[case] = len(set(imgs))
    return out


def canonical_frames(n, k):
    fr = set()
    for ml in range(0, k + 1):
        for mr in range(0, k + 1 - ml):
            for mb in range(0, k + 1):
                for mt in range(0, k + 1 - mb):
                    if n - 1 - ml - mr < 1 or n - 1 - mb - mt < 1:
                        continue
                    f = (ml, mr, mb, mt, 0, 0, 0, 0)
                    fr.add(min(case_images(f))[:4])
    return fr


if __name__ == '__main__':
    import sys
    n, k = int(sys.argv[1]), int(sys.argv[2])
    cs = all_cases(n, k)
    print('n=%d k=%d: canonical frames %d, canonical admissible cases %d, cases with orbits %d' % (
        n, k, len(canonical_frames(n, k)), len(cs), sum(cs.values())))
    import collections
    print(sorted(collections.Counter(c[4:] for c in cs).items()))


def cases_by_frame(n, k):
    """the case list used for the runs: every canonical frame with every admissible deficit vector (no
    reduction by the stabiliser of the frame).  For k = n/2 and n = 32 this gives 3321 frames, 11,466 cases."""
    out = []
    dm = k - 1; sm = 4 * k - 2 * n + 2
    for f in sorted(canonical_frames(n, k)):
        for dR in range(0, dm + 1):
            for dC in range(0, dm + 1):
                for dT in range(0, dm + 1):
                    for dS in range(0, dm + 1):
                        if dR + dC + dT + dS <= sm and admissible(n, k, f + (dR, dC, dT, dS)):
                            out.append(f + (dR, dC, dT, dS))
    return out


def to_canonical_frame(n, D):
    """image of D under a symmetry such that its frame is canonical"""
    best = None
    for g in sym_maps(n):
        E = frozenset(g(x, y) for x, y in D)
        c = case_of(n, E)
        if best is None or c[:4] < best[0][:4]:
            best = (c, E)
    return best
