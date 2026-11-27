"""Check the two-hole Q47 even-even permutation and a matching lower bound.

Run with Python 3 from any directory. Coordinates are zero-based. The proof of
completeness of the finite enumeration is in the diagonal-moments section of paper/q47-domination.tex.
"""
import json
from functools import lru_cache
from pathlib import Path


VALUES = range(-23, 24)
WITNESS = Path(__file__).resolve().parents[2] / "data/frame/q47_24_two_holes.json"


@lru_cache(maxsize=None)
def extensions(required):
    """Support masks of 24 indices with zero sum, by square sum and odd count."""
    groups = {}
    initial = sum(1 << (v + 23) for v in required)

    def visit(low, remaining, target_sum, squares, odd, mask):
        if remaining == 0:
            if target_sum == 0:
                groups.setdefault((squares, odd), set()).add(mask)
            return
        if remaining == 1:
            if low <= target_sum <= 23:
                v = target_sum
                groups.setdefault((squares + v*v, odd + v%2), set()).add(mask | (1 << (v+23)))
            return
        # Sorted indices with repetition. The other terms lie between v and 23.
        first = max(low, target_sum - 23*(remaining-1))
        last = min(23, target_sum // remaining)
        for v in range(first, last+1):
            visit(v, remaining-1, target_sum-v, squares+v*v, odd+v%2, mask | (1 << (v+23)))

    visit(-23, 24-len(required), -sum(required), sum(v*v for v in required),
          sum(v%2 for v in required), initial)
    return groups


def candidate_masks():
    candidates = set()
    for even in range(0, 25, 2):
        for odd in range(1, 24, 2):
            radius = (even, odd)
            differences = tuple(d for d in VALUES if abs(d) < radius[d%2])
            sums = tuple(t for t in VALUES if abs(t) <= 22-radius[t%2])
            if len(differences) > 24 or len(sums) > 25:
                continue
            for omit in (None,) + sums:
                required = tuple(t for t in sums if t != omit)
                if len(required) > 24:
                    continue
                sum_groups = extensions(required)
                for (ss, count_odd), diff_masks in extensions(differences).items():
                    for sm in sum_groups.get((4600-ss, 24-count_odd), ()):
                        candidates.update((dm, sm) for dm in diff_masks)
    return candidates


def check():
    q = [tuple(p) for p in json.loads(WITNESS.read_text())["set_col_row"]]
    evens = set(range(0, 47, 2))
    if len(q) != 24 or {x for x, y in q} != evens or {y for x, y in q} != evens:
        raise ValueError("placement is not an even-even permutation")
    holes = [(x, y) for x in range(47) for y in range(47)
             if not any(x == u or y == v or abs(x-u) == abs(y-v) for u, v in q)]
    candidates = candidate_masks()
    def missed(dm, sm):
        return sum(not ((dm >> (u-v+23) | sm >> (u+v+1)) & 1)
                   for u in range(23) for v in range(23))
    near = sum(missed(dm, sm) <= 1 for dm, sm in candidates)
    if near or len(holes) != 2:
        raise ValueError(f"failed extremal check: {near} support pairs, {holes} uncovered")
    print(json.dumps(dict(moment_support_pairs=len(candidates), pairs_with_at_most_one_hole=near,
                          minimum_uncovered_even_even_permutation=len(holes), holes=holes)))


if __name__ == "__main__":
    check()
