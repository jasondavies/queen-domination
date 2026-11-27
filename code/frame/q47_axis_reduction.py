"""Propagate forced occupied parities from counts on a Q47 frame branch.

Fix row parity p and column parity q. If at least r occupied rows and s
occupied columns have those parities, at most (k-r)+(k-s) queens have
square colour different from p+q mod 2. Each queen of that other
colour hits at most two squares of a fixed empty row along diagonals.
If there are more than twice this bound in empty columns of parity 1-q,
every row of parity p must be occupied. The transpose forces columns.
After all occupied lines on an axis have the preferred parity, no queen
can miss it on that axis. Apply these implications until counts stabilise.
"""

from itertools import product


def line_bounds(n, lo, hi, pairs, total):
    occupied = set(range(lo)) | set(range(hi + 1, n))
    empty = {lo, hi}
    for j, (left, right) in enumerate(pairs, 1):
        for i, b in ((lo + j, left), (hi - j, right)):
            (occupied if b == "1" else empty).add(i)
    sizes = ((n + 1) // 2, n // 2)
    low = [sum(i % 2 == p for i in occupied) for p in (0, 1)]
    high = [sizes[p] - sum(i % 2 == p for i in empty) for p in (0, 1)]
    return [max(low[p], total - high[1 - p]) for p in (0, 1)], [
        min(high[p], total - low[1 - p]) for p in (0, 1)
    ]


def profile(case, bits, n=47):
    """Return a necessary profile or 'impossible'; None means undecided."""
    if n % 2 == 0:
        raise ValueError("expected an odd board")
    left, right, bottom, top, dr, dc, _, _ = case
    w, h = n - 1 - left - right, n - 1 - bottom - top
    if (
        min(left, right, bottom, top) < 0
        or len(bits) % 4
        or set(bits) - {"0", "1"}
        or 2 * (len(bits) // 4) >= min(w, h)
    ):
        raise ValueError("invalid case or cube")
    k = (n + 1) // 2
    rt, ct = k - dr, k - dc
    rl, rh = line_bounds(n, bottom, n - 1 - top, zip(bits[0::4], bits[1::4]), rt)
    cl, ch = line_bounds(n, left, n - 1 - right, zip(bits[2::4], bits[3::4]), ct)
    sizes = (k, n // 2)
    while True:
        if any(lo > hi for lo, hi in zip(rl + cl, rh + ch)):
            return "impossible"
        old = tuple(rl + cl)
        for p, q in product(range(2), repeat=2):
            other_colour_bound = (0 if rl[p] == rt else k - rl[p]) + (
                0 if cl[q] == ct else k - cl[q]
            )
            if sizes[1 - q] - (ct - cl[q]) > 2 * other_colour_bound:
                rl[p] = sizes[p]
            if sizes[1 - p] - (rt - rl[p]) > 2 * other_colour_bound:
                cl[q] = sizes[q]
        # The fixed totals turn any improved lower bound into an upper
        # bound for the opposite parity on that axis.
        for p in range(2):
            rh[p] = min(rh[p], rt - rl[1 - p])
            ch[p] = min(ch[p], ct - cl[1 - p])
        if tuple(rl + cl) == old:
            break
    if rl[0] == cl[0] == k:
        return "even-permutation"
    if (
        (rt, ct) == (k, k - 1)
        and rl[0] == k
        and cl[1] == k - 1
        or (rt, ct) == (k - 1, k)
        and cl[0] == k
        and rl[1] == k - 1
    ):
        return "orthodox"
    if rt == ct == rl[1] == cl[1] == k - 1:
        return "odd-repeat"
    return None
