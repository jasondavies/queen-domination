"""Replay a compact Q47 archive case-by-case from its proof index and payloads.

Run with --index-only for the frame census, the prefix partitions and the 25-queen
placement. Use --regenerate for verification from the Git release alone, or
omit both options to check the stored proof payloads. --case takes the eight
comma-separated frame parameters and restricts proof replay to that root.
"""

import argparse
from collections import Counter
from contextlib import contextmanager, nullcontext
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
from functools import lru_cache
import gzip
import hashlib
from io import BytesIO
import json
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory
from zipfile import ZipFile

from check_q47_axis_reduction import check_branch, check_exclusion
from check_q47_cube_core import replay as replay_core
from odd_colour_perimeter import build_q47_colour
from geom import canonical, lines
from odd_margin_bounds import cases, excluded
import q47_batch
from q47_core_reuse import covered
import q47_same_parity
import q47_terminal_moments
import run_hard

REPO = Path(__file__).resolve().parents[2]


@contextmanager
def index_rows(index):
    proc = subprocess.Popen(["zstd", "-dc", index], stdout=subprocess.PIPE)
    try:
        with proc.stdout as stream:
            yield map(json.loads, stream)
        if proc.wait() != 0:
            raise ValueError("zstd index read failed")
    finally:
        if proc.poll() is None:
            proc.terminate()
            proc.wait()


def check_partition(leaves):
    bits = sorted(b for b, _ in leaves)
    if not bits or any(len(b) % 4 or set(b) - {"0", "1"} for b in bits):
        raise ValueError("invalid cube prefixes")
    if any(b.startswith(a) for a, b in zip(bits, bits[1:])):
        raise ValueError("overlapping cube prefixes")
    depth = max(map(len, bits))
    if sum(1 << (depth - len(b)) for b in bits) != 1 << depth:
        raise ValueError("incomplete cube partition")


@lru_cache(maxsize=1)
def root_formula(case):
    base, cnf = q47_batch.build(case)
    return base, cnf, hashlib.sha256(cnf).hexdigest()


def plain_cube(case, bits):
    base, root, _ = root_formula(case)
    if not bits:
        return root
    head, body = root.split(b"\n", 1)
    prefix, count = head.rsplit(b" ", 1)
    units = []
    for i in range(0, len(bits), 4):
        variables = run_hard.layer_vars(base, case, 1 + i // 4)
        if variables is None:
            raise ValueError("cube extends past frame layers")
        for bit, v in zip(bits[i : i + 4], variables, strict=True):
            units.append(f"{v if bit == '1' else -v} 0\n")
    return (
        prefix
        + b" "
        + str(int(count) + len(units)).encode()
        + b"\n"
        + body
        + "".join(units).encode()
    )


def sat_formula(case, h, bits, rule):
    if rule == "frame":
        return plain_cube(case, bits)
    if rule == "colour":
        _, cnf, _ = build_q47_colour(case, bits, expected_root_sha256=h)
        return cnf
    if rule == "legacy":
        run_hard.init(47, 24, 0, "", True)
        return run_hard.build(case, bits)[1].encode()
    raise ValueError("unknown SAT encoding")


def local(root, name):
    p = (root / name).resolve()
    if not p.is_relative_to(root):
        raise ValueError("archive path outside the payload directory")
    return p


@lru_cache(maxsize=1)
def regeneration_formulas():
    return json.loads((REPO / "data/frame/q47_release/regeneration-formulas.json").read_bytes())


def replay_trace(case, h, bits, r, archive, regenerate=False):
    formula = r
    if regenerate:
        formula = regeneration_formulas().get(r["cnf"], r)
        if formula["rule"] not in ("frame", "colour"):
            raise ValueError("missing or invalid regeneration encoding")
    data = sat_formula(case, h, bits, formula["rule"])
    if hashlib.sha256(data).hexdigest() != formula["cnf"]:
        raise ValueError("CNF digest mismatch")
    with TemporaryDirectory() as tmp:
        cnf = Path(tmp) / "case.cnf"
        cnf.write_bytes(data)
        proof = Path(tmp) / "proof.drat"
        if regenerate:
            solver = subprocess.run(
                [REPO / "tools/cadical", "-q", cnf, proof], stdout=subprocess.DEVNULL
            )
            if solver.returncode != 20 or not proof.is_file():
                raise RuntimeError(
                    f"CaDiCaL failed to produce an UNSAT proof for {case} {bits!r} "
                    f"(exit {solver.returncode})"
                )
        else:
            path = local(archive, r["file"])
            if path.suffix == ".zst":
                with proof.open("wb") as out:
                    subprocess.run(["zstd", "-dc", path], stdout=out, check=True)
            elif path.suffix == ".gz":
                with gzip.open(path, "rb") as src, proof.open("wb") as out:
                    shutil.copyfileobj(src, out)
            else:
                proof = path
            with proof.open("rb") as f:
                if hashlib.file_digest(f, "sha256").hexdigest() != r["proof"]:
                    raise ValueError("DRAT digest mismatch")
        ck = subprocess.run(
            [REPO / "tools/drat-trim", cnf, proof, "-w"],
            capture_output=True,
            check=True,
        )
        if b"s VERIFIED" not in ck.stdout.splitlines():
            raise ValueError("DRAT replay failed")


@lru_cache(maxsize=1)
def release_cores():
    bundle = REPO / "data/frame/q47_release/core-certificates.zip"
    return ZipFile(BytesIO(bundle.read_bytes()))


@lru_cache(maxsize=4096)
def checked_core(path, regenerate=False):
    location_context = TemporaryDirectory() if regenerate else nullcontext(path)
    with location_context as location:
        directory = Path(location)
        if regenerate:
            for name in ("info.json", "core.cnf", "core.drat"):
                (directory / name).write_bytes(release_cores().read(f"{path.name}/{name}"))
        info = json.loads((directory / "info.json").read_text())
        return tuple(info["case"]), info["root_sha256"], replay_core(directory)


def replay_leaf(case, h, bits, r, archive, regenerate=False):
    rule = r["rule"]
    if rule in ("frame", "legacy", "colour"):
        replay_trace(case, h, bits, r, archive, regenerate)
    elif rule == "mixed-moments":
        if hashlib.sha256(plain_cube(case, bits)).hexdigest() != r["cnf"]:
            raise ValueError("mixed moment branch digest mismatch")
        check_branch(case, bits, rule)
    elif rule == "axis":
        profile = r["profile"]
        split = case[-2:] if profile == "odd-repeat" else (0, 0)
        check_exclusion(profile, *split)
        check_branch(case, bits, profile)
    elif rule == "core":
        masks = []
        for path in r["certificates"]:
            directory = Path(path) if regenerate else local(archive, path)
            c, root, mask = checked_core(directory, regenerate)
            if (c, root) != (case, h):
                raise ValueError("core belongs to a different frame")
            masks.append(mask)
        if not covered(bits, masks):
            raise ValueError("core masks do not cover cube")
    elif rule in ("same-parity", "terminal-moments"):
        checker = q47_same_parity if rule == "same-parity" else q47_terminal_moments
        if checker.replay(local(archive, r["receipt"]), h) != (case, bits):
            raise ValueError("moment branch mismatch")
    else:
        raise ValueError("unknown certificate rule")


def check_witness():
    directory = REPO / "data/frame"
    placements = (("q47_closeout.json", "upper_bound_set_col_row", False),
                  ("q47_independent_25.json", "set_col_row", True))
    for filename, key, independent in placements:
        witness = [tuple(p) for p in json.loads((directory / filename).read_text())[key]]
        if len(witness) != 25 or len(set(witness)) != 25 or any(
            x not in range(47) or y not in range(47) for x, y in witness
        ):
            raise ValueError(f"invalid upper-bound placement in {filename}")
        rows, columns, differences, sums = lines(witness)
        if independent and min(map(len, (rows, columns, differences, sums))) != 25:
            raise ValueError("independent placement contains attacking queens")
        if any(y not in rows and x not in columns and y - x not in differences and x + y not in sums
               for x in range(47) for y in range(47)):
            raise ValueError(f"placement in {filename} misses a square")


def replay_case(case, h, leaves, archive, regenerate=False):
    base, _, computed = root_formula(case)
    if h != computed:
        raise ValueError(f"root digest mismatch for {case}")
    for bits, record in leaves:
        if bits and run_hard.layer_vars(base, case, len(bits) // 4) is None:
            raise ValueError(f"invalid layer depth in {case}")
        replay_leaf(case, h, bits, record, archive, regenerate)
    return len(leaves)


def audited_rows(index, selected_cases, cube, index_only, counts):
    expected = {c for c in cases(47) if not excluded(47, c)}
    if not selected_cases.issubset(expected):
        raise ValueError("unknown frame case")
    # Resolve targeted requests before streaming proofs: the representative
    # may precede the referring row. Older indexes prove both cases directly.
    selected = set(selected_cases)
    if not index_only and any(case != canonical(case) for case in selected):
        with index_rows(index) as stream:
            for row in stream:
                case = tuple(row["case"])
                if case in selected_cases and "representative" in row:
                    if cube is not None:
                        raise ValueError(f"this root uses symmetry; select a cube of {canonical(case)}")
                    selected.discard(case)
                    selected.add(canonical(case))
    proof_roots = set()
    representatives = set()
    with index_rows(index) as stream:
        for row in stream:
            case = tuple(row["case"])
            expected.remove(case)
            counts["indexed_roots"] += 1
            if "representative" in row:
                target = tuple(row["representative"])
                if set(row) != {"case", "representative"} or target == case or target != canonical(case):
                    raise ValueError(f"invalid whole-root symmetry for {case}")
                representatives.add(target)
                counts["symmetry_roots"] += 1
                continue
            proof_roots.add(case)
            leaves = row["leaves"]
            check_partition(leaves)
            if index_only or selected and case not in selected:
                continue
            if cube is not None:
                leaves = [(bits, r) for bits, r in leaves if bits == cube]
                if not leaves:
                    raise ValueError("cube is not an indexed leaf of this root")
            yield case, row["root"], leaves
    if expected or counts["indexed_roots"] != 98114:
        raise ValueError("missing frame cases")
    if not representatives <= proof_roots:
        raise ValueError("symmetry representative has no direct proof partition")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("index", type=Path)
    parser.add_argument("--payload-dir", type=Path, help="Read stored proof payloads from this directory")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--index-only", action="store_true")
    mode.add_argument("--regenerate", action="store_true", help="Generate and check temporary SAT proofs using the bundled certificates")
    parser.add_argument(
        "--case",
        action="append",
        type=lambda x: tuple(map(int, x.split(","))),
        help="Restrict replay to a frame; can be specified more than once",
    )
    parser.add_argument(
        "--cube", help="Replay this exact indexed leaf of the selected case"
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=1,
        help="Number of independent frame replays to run concurrently",
    )
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("--workers must be positive")
    if args.regenerate and args.payload_dir is not None:
        parser.error("--regenerate uses the bundled certificates; omit --payload-dir")
    selected_cases = set(args.case or ())
    if args.cube is not None and (len(selected_cases) != 1 or args.index_only):
        parser.error("--cube requires --case and proof replay")
    archive = (args.payload_dir or REPO).resolve()
    check_witness()
    counts = Counter()
    frames = audited_rows(
        args.index, selected_cases, args.cube, args.index_only, counts
    )
    if args.workers == 1 or args.index_only or len(selected_cases) == 1:
        for case, h, leaves in frames:
            counts["checked_leaves"] += replay_case(case, h, leaves, archive, args.regenerate)
            if args.cube is None:
                counts["checked_roots"] += 1
    else:
        with ProcessPoolExecutor(args.workers) as pool:
            pending = set()
            # Keep only a bounded number of future roots and their leaf records in memory.
            for case, h, leaves in frames:
                pending.add(pool.submit(replay_case, case, h, leaves, archive, args.regenerate))
                if len(pending) >= 2 * args.workers:
                    done, pending = wait(pending, return_when=FIRST_COMPLETED)
                    counts["checked_leaves"] += sum(f.result() for f in done)
                    counts["checked_roots"] += len(done)
            counts["checked_leaves"] += sum(f.result() for f in pending)
            counts["checked_roots"] += len(pending)
    print(json.dumps(counts))


if __name__ == "__main__":
    main()
