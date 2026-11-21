#!/usr/bin/env python3
"""Run kissat on a DIMACS string via stdin (no temp files); returns (result, model, cpu_s, wall_s, returncode)."""
import os, subprocess, time, resource

HERE = os.path.dirname(os.path.abspath(__file__))
KISSAT = os.path.join(HERE, '..', '..', 'tools', 'kissat')     # kissat 4.0.4 (not included; see README)


def kissat(dimacs, timeout=None, extra=()):
    args = [KISSAT, '-q'] + list(extra)
    if timeout:
        args.append('--time=%d' % int(timeout))
    t0 = time.time()
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    p = subprocess.Popen(args, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = p.communicate(dimacs.encode())
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)     # delta = this child (one solver at a time per process)
    cpu = (r1.ru_utime - r0.ru_utime) + (r1.ru_stime - r0.ru_stime)
    wall = time.time() - t0
    rc = p.returncode
    res = {10: 'SAT', 20: 'UNSAT'}.get(rc, 'UNKNOWN')
    model = []
    if res == 'SAT':
        for line in out.decode().split('\n'):
            if line.startswith('v '):
                model += [int(v) for v in line[2:].split() if v != '0']
    return res, model, cpu, wall, rc


def glucose(clauses, timeout=None, name='glucose4'):
    """in-process PySAT solver (Glucose 4 by default) with a wall-clock limit; same return convention"""
    import threading
    from pysat.solvers import Solver
    t0 = time.time(); c0 = time.process_time()
    s = Solver(name=name, bootstrap_with=clauses)
    timer = None
    if timeout:
        timer = threading.Timer(timeout, s.interrupt); timer.start()
    r = s.solve_limited(expect_interrupt=True)
    if timer:
        timer.cancel()
    res = {True: 'SAT', False: 'UNSAT', None: 'UNKNOWN'}[r]
    model = s.get_model() if r else []
    s.delete()
    return res, model, time.process_time() - c0, time.time() - t0, None
