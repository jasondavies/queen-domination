"""Count odd-board cases excluded by the exterior-queen bounds.

Run from any directory with Python 3, e.g. odd_margin_bounds.py 35 47.
At n=35, also sum the times of the archived, verified records selected by
final_check35.py. The accounting does not rerun SAT or check DRAT proofs.
"""
import argparse
from collections import Counter, defaultdict
from itertools import product
import json
import lzma
from pathlib import Path

from geom import admissible, canonical_frames


DATA = Path(__file__).resolve().parents[2] / "data" / "frame"


def excluded(n, case):
    """Necessary bounds for n=2k-1. All spans are coordinate differences."""
    k = (n + 1) // 2
    left, right, bottom, top, dr, dc, _, _ = case
    width = n - 1 - left - right
    height = n - 1 - bottom - top
    allowance = 4 - dr - dc
    if width >= height:
        allowance = min(allowance, 2 - 2 * dr + 2 * (width == height))
    if height >= width:
        allowance = min(allowance, 2 - 2 * dc + 2 * (width == height))
    return left + right + bottom + top > k + allowance


def cases(n):
    k = (n + 1) // 2
    deficits = [d for d in product(range(5), repeat=4) if sum(d) <= 4]
    for frame in canonical_frames(n, k):
        for d in deficits:
            case = frame + d
            if admissible(n, k, case):
                yield case


def forces_equal_colors(n, case):
    """Sufficient conditions for a surviving case on Q_(4m-1) to require m of each."""
    if n % 4 != 3:
        return False
    left, right, bottom, top, dr, dc, _, _ = case
    w = n - 1 - left - right
    h = n - 1 - bottom - top
    if w != h and max(w, h) % 2:
        return True
    if w == h and w % 2 and dr + dc > 0:
        return True
    orthodox_axis = {(0, 0), (0, 2), (2, 0), (1, 1)}
    if (left, right) in orthodox_axis and (bottom, top) in orthodox_axis:
        return False
    return dr + dc > 2 or (dr + dc == 2 and dr != dc)


def recorded_times():
    def verified(name):
        with lzma.open(DATA / name, "rt") as stream:
            for line in stream:
                record = json.loads(line)
                if record.get("result") == "UNSAT" and record.get("drat") == "VERIFIED":
                    yield record

    plain = {}
    for name in ("d_35_18.jsonl.xz", "d_35_18_sq.jsonl.xz"):
        for r in verified(name):
            plain[tuple(r["case"])] = r
    cubes = {(tuple(r["case"]), r["cube"]): r for r in verified("h_35_18.jsonl.xz")
             if r.get("sbp") is True and tuple(r["case"]) not in plain}
    times = defaultdict(lambda: [0., 0.])
    for r in (*plain.values(), *cubes.values()):
        pair = times[tuple(r["case"])]
        pair[0] += r["t_solve"]
        pair[1] += r["t_check"]
    return times


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("orders", type=int, nargs="+")
    args = parser.parse_args()
    for n in args.orders:
        if n < 5 or n % 2 == 0:
            parser.error("use odd board orders of at least five")
        counts = Counter()
        rejected = set()
        for case in cases(n):
            counts["cases"] += 1
            if excluded(n, case):
                rejected.add(case)
            elif forces_equal_colors(n, case):
                counts["remaining_forced_balanced"] += 1
        counts["excluded"] = len(rejected)
        result = dict(n=n, **counts)
        if n == 35:
            with (DATA / "hard35_cases.jsonl").open() as stream:
                hard = {tuple(json.loads(line)["case"]) for line in stream}
            times = recorded_times()
            assert len(times) == counts["cases"] and rejected <= times.keys()
            result.update(hard=len(hard), hard_excluded=len(hard & rejected))
            for label, group in (("all", times.keys()), ("excluded", rejected),
                                 ("hard_excluded", hard & rejected)):
                result[label + "_solve_check_hours"] = [
                    round(sum(times[c][i] for c in group) / 3600, 3) for i in (0, 1)]
        print(json.dumps(result))


if __name__ == "__main__":
    main()
