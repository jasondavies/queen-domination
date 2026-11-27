"""Verify a Q47 arithmetic branch exclusion by enumerating parity counts.

Each empty row of parity p meets every empty column of parity q in a target
of colour (p+q) mod 2. One queen of that colour hits at most two such
targets on any fixed empty line. Enumerate counts consistent with this
necessary condition, including every possible placement's row and column
multiplicities. Check the indicated profile on every survivor. The
profile-specific exclusions reuse the existing Q47 arithmetic checks.

Run from the repository root with data/frame/q47_axis_reductions.json.gz.
"""

from functools import lru_cache
from hashlib import sha256
import gzip
from pathlib import Path
from tempfile import TemporaryDirectory
import json

from check_q47_even_permutation import check as check_even
from check_q47_orthodox_enumeration import check as check_orthodox
from check_q47_terminal_enumeration import verify_profile
from q47_orthodox import install
from q47_batch import build
from run_hard import layer_vars


def parity_counts(occupied, empty, total):
    """All possible numbers of distinct even lines on this axis."""
    for even in range(25):
        odd = total - even
        if sum(i % 2 == 0 for i in occupied) <= even <= 24 - sum(
            i % 2 == 0 for i in empty
        ) and sum(i % 2 == 1 for i in occupied) <= odd <= 23 - sum(
            i % 2 == 1 for i in empty
        ):
            yield even


def queen_counts(even, odd):
    return range(24 if not odd else even, 1 + (0 if not even else 24 - odd))


def exceptional_even_lines(occupied, empty):
    """Even coordinates consistent with all odd lines and one even line occupied."""
    odds = set(range(1, 47, 2))
    for i in range(0, 47, 2):
        lines = odds | {i}
        if occupied <= lines and lines.isdisjoint(empty):
            yield i


def check_branch(case, bits, kind):
    l, r, b, t, dr, dc, dt, ds = case
    if (
        len(bits) % 4
        or set(bits) - {"0", "1"}
        or 2 * (len(bits) // 4) >= min(46 - l - r, 46 - b - t)
    ):
        raise ValueError("invalid layer string")

    def lines(lo, hi, lower, upper):
        on = set(range(lo)) | set(range(hi + 1, 47))
        off = {lo, hi}
        for j, (v, w) in enumerate(zip(lower, upper, strict=True), 1):
            (on if v == "1" else off).add(lo + j)
            (on if w == "1" else off).add(hi - j)
        return on, off

    rows = lines(b, 46 - t, bits[0::4], bits[1::4])
    cols = lines(l, 46 - r, bits[2::4], bits[3::4])
    for re in parity_counts(*rows, 24 - dr):
        ro = 24 - dr - re
        for ce in parity_counts(*cols, 24 - dc):
            co = 24 - dc - ce
            if (
                kind == "even-permutation"
                and re == ce == 24
                or kind == "odd-repeat"
                and ro == co == 23
                and re == ce == 0
                or kind == "mixed-moments"
                and (re, ro, ce, co) == (1, 23, 1, 23)
                or kind == "orthodox"
                and (
                    (re, ro, ce, co) == (24, 0, 0, 23)
                    or (ce, co, re, ro) == (24, 0, 0, 23)
                )
            ):
                continue
            need = [0, 0]
            for p, nrows in enumerate((24 - re, 23 - ro)):
                for q, ncols in enumerate((24 - ce, 23 - co)):
                    if nrows and ncols:
                        need[p ^ q] = max(need[p ^ q], (max(nrows, ncols) + 1) // 2)
            for er in queen_counts(re, ro):
                for ec in queen_counts(ce, co):
                    # If z queens occupy even-even squares, 24-er-ec+z
                    # occupy odd-odd squares. All four cell counts are nonnegative.
                    for z in range(max(0, er + ec - 24), min(er, ec) + 1):
                        same = 24 - er - ec + 2 * z
                        if same >= need[0] and 24 - same >= need[1]:
                            raise ValueError(
                                (
                                    "unexcluded parity counts",
                                    case,
                                    bits,
                                    kind,
                                    re,
                                    ce,
                                    er,
                                    ec,
                                    z,
                                )
                            )

    if kind == "mixed-moments":
        if dr or dc:
            raise ValueError("mixed moment rule requires distinct rows and columns")
        # The 23-by-23 empty even grid forces the exceptional queen to
        # the intersection. Check the remaining odd permutation at every
        # possible intersection of the surviving parity profile.
        xs = list(exceptional_even_lines(*cols))
        ys = list(exceptional_even_lines(*rows))
        if not xs or not ys:
            raise ValueError("branch admits no exceptional intersection")
        for x in xs:
            for y in ys:
                verify_profile((x, y), dt, ds)


@lru_cache(maxsize=None)
def check_exclusion(kind, dt, ds):
    if kind == "orthodox":
        check_orthodox()
        with TemporaryDirectory() as store:
            install(Path(store))
    elif kind == "even-permutation":
        check_even()
    elif kind == "odd-repeat":
        verify_profile(None, dt, ds)
    elif kind != "impossible":
        raise ValueError("unknown arithmetic rule")


@lru_cache(maxsize=1)
def frame(case):
    base, formula = build(case)
    return base, sha256(formula).hexdigest()


def verify(rows):
    for row in rows:
        case = tuple(row["case"])
        base, h = frame(case)
        if row["root"] != h:
            raise ValueError("baseline root digest mismatch")
        l, r, b, t = case[:4]
        for j in range(1, len(row["cube"]) // 4 + 1):
            if layer_vars(base, case, j) != [
                base.oR[b + j],
                base.oR[46 - t - j],
                base.oC[l + j],
                base.oC[46 - r - j],
            ]:
                raise ValueError("unexpected layer order")
        dt, ds = case[-2:] if row["kind"] == "odd-repeat" else (0, 0)
        check_exclusion(row["kind"], dt, ds)
        check_branch(case, row["cube"], row["kind"])


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipts", type=Path)
    path = parser.parse_args().receipts
    raw = path.read_bytes()
    receipts = json.loads(gzip.decompress(raw) if path.suffix == ".gz" else raw)
    verify(receipts)
    print(f"Checked {len(receipts)} arithmetic exclusions.")
