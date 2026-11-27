"""Build, solve and check Q47 frame cases. Coordinates are zero-based."""
import hashlib
import itertools
import os
from pathlib import Path
import resource
import subprocess
import tempfile
import time
from functools import lru_cache

import enc
import geom
from hard_test import sbp_clauses
from odd_margin_bounds import forces_equal_colors
from odd_square_profile import square_profile


def queen_count(squares, k, new, clauses):
    """Exactly k via unary prefix counts truncated after k+1."""
    previous = []
    for lit in squares:
        current = [new() for _ in range(min(len(previous) + 1, k + 1))]
        for j, v in enumerate(current):
            old = previous[j:j+1]
            if old:
                clauses.append([-old[0], v])
            clauses.append([-v, *old, lit])
            if j:
                clauses.extend([[-v, *old, previous[j-1]], [-previous[j-1], -lit, v]])
            else:
                clauses.append([-lit, v])
        previous = current
    clauses.extend([[previous[k-1]], [-previous[k]]])


@lru_cache(maxsize=1)
def base_for(deficits):
    return enc.Base(47, 24, deficits, queen_cardinality=queen_count)


def build(case):
    base = base_for(case[4:])
    extra, nv = enc.case_extra(base, case)
    ids = itertools.count(nv + 1)
    def new():
        return next(ids)
    extra.extend(sbp_clauses(base, case, new))
    if sum(case[:2]) == sum(case[2:4]):
        square_profile(base, case, new, extra)
    if forces_equal_colors(47, case) and 0 in case[6:]:
        family = base.oT if case[6] == 0 else base.oS
        enc.exactly([v for z, v in family.items() if z % 2 == 0], 12, new, extra)
    return base, enc.dimacs(base, extra, next(ids)-1).encode()


def child_cpu():
    r = resource.getrusage(resource.RUSAGE_CHILDREN)
    return r.ru_utime + r.ru_stime


def solve_case(case, tools, seconds=5):
    start = time.monotonic()
    case = tuple(case)
    base, formula = build(case)
    result = dict(case=case, cube="", limit=seconds, cnf_sha256=hashlib.sha256(formula).hexdigest())
    with tempfile.TemporaryDirectory() as tmp:
        cnf = Path(tmp) / "case.cnf"
        proof = Path(tmp) / "case.drat"
        cnf.write_bytes(formula)
        def cpu_limit():
            resource.setrlimit(resource.RLIMIT_CPU, (seconds, seconds+1))
        t = child_cpu()
        run = subprocess.run([tools/"cadical", "-q", cnf, proof], capture_output=True, preexec_fn=cpu_limit)
        result['t_solve'] = child_cpu()-t
        if run.returncode == 20:
            t = child_cpu()
            check = subprocess.run([tools/"drat-trim", cnf, proof, "-w", "-t", "30"], capture_output=True)
            ok = b"s VERIFIED" in check.stdout
            result.update(result='UNSAT' if ok else 'UNCHECKED', drat='VERIFIED' if ok else 'UNCHECKED',
                          proof_sha256=hashlib.file_digest(proof.open('rb'), 'sha256').hexdigest(),
                          proof_bytes=proof.stat().st_size, t_check=child_cpu()-t)
        elif run.returncode == 10:
            positive = {int(t) for l in run.stdout.splitlines() if l.startswith(b'v ') for t in l.split()[1:] if int(t)>0}
            queens = [(x,y) for x in range(47) for y in range(47) if base.q[x][y] in positive]
            if len(queens)!=24 or geom.case_of(47,queens)!=case or not geom.dominated(47,queens):
                raise ValueError("invalid SAT placement")
            result.update(result='SAT', set_col_row=queens)
        elif run.returncode in (-24, -9):
            result.update(result='TIMEOUT')
        else:
            raise RuntimeError((run.returncode, run.stderr[-500:]))
    result['elapsed'] = time.monotonic()-start
    return result
