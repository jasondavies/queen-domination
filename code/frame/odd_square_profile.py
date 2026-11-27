"""Additional CNF clauses for the square-frame bound in odd-frame-bounds.tex.

Call square_profile(base, case, new, clauses) after building the original
formula. The positive test literals count differences between the numbers
of occupied rows and columns in each reflected pair of indices.
Run this file directly to reproduce the bounded Q35 pilot in the note.
"""
from itertools import count
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from enc import atmost


def square_profile(base, case, new, clauses):
    left, right, bottom, top, *deficits = case
    width = base.n - 1 - left - right
    if base.n != 2 * base.k - 1 or width != base.n - 1 - bottom - top:
        raise ValueError("the profile bound requires n=2k-1 and a square frame")

    def thresholds(a, b):
        either, both = new(), new()
        clauses.extend([[-a, either], [-b, either], [a, b, -either],
                        [a, -both], [b, -both], [-a, -b, both]])
        return (either, both)

    def different(a, b):
        mismatch = new()
        clauses.extend([[-a, b, mismatch], [a, -b, mismatch]])
        return mismatch

    mismatches = []
    for i in range(1, (width + 1) // 2):
        j = width - i
        rows = thresholds(base.oR[bottom + i], base.oR[bottom + j])
        cols = thresholds(base.oC[left + i], base.oC[left + j])
        mismatches.extend(different(r, c) for r, c in zip(rows, cols))
    if width % 2 == 0:
        mid = width // 2
        mismatches.append(different(base.oR[bottom + mid], base.oC[left + mid]))
    atmost(mismatches, 4 - sum(deficits), new, clauses)


def pilot():
    import run_hard

    case = (1, 4, 2, 3, 0, 0, 0, 0)
    run_hard.init(35, 18, 0, "", True)
    with TemporaryDirectory() as work:
        cnf = Path(work) / "cube.cnf"
        proof = Path(work) / "cube.drat"
        for i in range(16):
            cube = format(i, "04b")
            base, original = run_hard.build(case, cube)
            header, body = original.split("\n", 1)
            _, _, variables, clause_count = header.split()
            ids = count(int(variables) + 1)
            extra = []
            square_profile(base, case, lambda: next(ids), extra)
            extended = f"p cnf {next(ids) - 1} {int(clause_count) + len(extra)}\n" + body
            extended += "".join(" ".join(map(str, clause)) + " 0\n" for clause in extra)
            for label, formula in (("original", original), ("profile", extended)):
                cnf.write_text(formula)
                run = subprocess.run([run_hard.CAD, "-q", "-c", "8000", cnf, proof],
                                     capture_output=True)
                if run.returncode == 20:
                    checked = subprocess.run([run_hard.DRAT, cnf, proof, "-w"],
                                             capture_output=True)
                    if b"s VERIFIED" not in checked.stdout:
                        raise RuntimeError(f"proof failed for {cube} {label}")
                    print(cube, label, "verified UNSAT", flush=True)
                elif run.returncode == 0 and b"UNKNOWN" in run.stdout:
                    print(cube, label, "conflict limit", flush=True)
                else:
                    raise RuntimeError(f"unexpected solver result for {cube} {label}: {run}")


if __name__ == "__main__":
    pilot()
