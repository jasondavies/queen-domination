#!/usr/bin/env python3
"""Exhaustive tests of cnf.py: for every assignment of the input variables, the cardinality / AMO clauses
are satisfiable (by some extension to the auxiliary variables) iff the constraint holds.  Inputs include
repeated literals, negated literals and constants."""
import itertools, random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cnf import CNF, TRUE, FALSE
from pysat.solvers import Solver


def check(build, nin, pred, label):
    c = CNF()
    xs = [c.var() for _ in range(nin)]
    build(c, xs)
    s = Solver(name='minisat22', bootstrap_with=c.clauses)
    for bits in itertools.product([0, 1], repeat=nin):
        assum = [x if b else -x for x, b in zip(xs, bits)]
        got = s.solve(assumptions=assum)
        want = pred(bits)
        assert got == want, (label, bits, got, want)
    s.delete()


def lit_value(l, xs, bits):
    if l == TRUE:
        return 1
    if l == FALSE:
        return 0
    v = bits[xs.index(abs(l))]
    return v if l > 0 else 1 - v


def main():
    rnd = random.Random(7)
    ntest = 0
    # plain counts
    for m in range(0, 10):
        for K in range(-1, m + 2):
            check(lambda c, xs, K=K: c.count_eq(list(xs), K), m, lambda bits, K=K: sum(bits) == K, ('eq', m, K))
            ntest += 1
    # random literal multisets with repetitions, negations, constants
    for trial in range(300):
        nin = rnd.randint(1, 7)
        L = rnd.randint(1, 14)
        K = rnd.randint(-1, L + 1)

        def mk(c, xs, spec):
            lits = []
            for kind, i in spec:
                lits.append(TRUE if kind == 'T' else FALSE if kind == 'F' else (xs[i] if kind == '+' else -xs[i]))
            return lits
        spec = [(rnd.choice('++++--TF'), rnd.randrange(nin)) for _ in range(L)]

        def build(c, xs, spec=spec, K=K):
            c.count_eq(mk(c, xs, spec), K)

        def pred(bits, spec=spec, K=K, nin=nin):
            tot = 0
            for kind, i in spec:
                tot += 1 if kind == 'T' else 0 if kind == 'F' else (bits[i] if kind == '+' else 1 - bits[i])
            return tot == K
        check(build, nin, pred, ('rand', spec, K))
        ntest += 1
    # AMO
    for m in range(0, 14):
        check(lambda c, xs: c.amo(list(xs)), m, lambda bits: sum(bits) <= 1, ('amo', m))
        ntest += 1
    for m in range(1, 9):
        check(lambda c, xs: c.amo(list(xs) + [TRUE]), m, lambda bits: sum(bits) == 0, ('amoT', m))
        check(lambda c, xs: c.amo([FALSE] + list(xs)), m, lambda bits: sum(bits) <= 1, ('amoF', m))
        ntest += 2
    # and/or definitions
    for m in range(1, 6):
        def b_and(c, xs):
            v = c.and_def(list(xs)); w = c.var() if False else None
            c.unit(v)
        check(b_and, m, lambda bits: all(bits), ('and', m))
        def b_nand(c, xs):
            v = c.and_def(list(xs)); c.unit(-v)
        check(b_nand, m, lambda bits: not all(bits), ('nand', m))
        def b_or(c, xs):
            v = c.or_def(list(xs)); c.unit(v)
        check(b_or, m, lambda bits: any(bits), ('or', m))
        def b_nor(c, xs):
            v = c.or_def(list(xs)); c.unit(-v)
        check(b_nor, m, lambda bits: not any(bits), ('nor', m))
        ntest += 4
    # a large network: exactly K of 40, random assignments (fixed inputs)
    for trial in range(200):
        m = rnd.randint(20, 60); K = rnd.randint(0, m)
        c = CNF(); xs = [c.var() for _ in range(m)]; c.count_eq(xs, K)
        s = Solver(name='minisat22', bootstrap_with=c.clauses)
        bits = [rnd.random() < (K + rnd.choice([-1, 0, 0, 1])) / m for _ in range(m)]
        assert s.solve(assumptions=[x if b else -x for x, b in zip(xs, bits)]) == (sum(bits) == K)
        s.delete(); ntest += 1
    print('test_cnf: %d exhaustive/random tests passed' % ntest)


if __name__ == '__main__':
    main()
