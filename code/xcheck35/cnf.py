#!/usr/bin/env python3
"""CNF builder with the cardinality and at-most-one encodings of the cross-check encoding.

Cardinality: Batcher's odd-even merge sorting network with full comparators (six clauses), restricted to the
cone of influence of the outputs that are actually constrained.  Wires are literals or the constants
TRUE/FALSE (constant inputs are propagated through the comparators at build time).
  outputs are sorted in decreasing order: out[j] is true iff at least j+1 inputs are true.
At-most-one: Chen's product encoding (two-dimensional, recursive, pairwise at the base).
All of this is tested exhaustively in test_cnf.py."""

TRUE = 'T'
FALSE = 'F'


class CNF:
    def __init__(self):
        self.nv = 0
        self.clauses = []

    def var(self):
        self.nv += 1
        return self.nv

    def add(self, cl):
        self.clauses.append(list(cl))

    # ---------- definitions ----------
    def and_def(self, lits):
        """fresh v with v <-> AND(lits) (lits may contain constants)"""
        lits = [l for l in lits if l != TRUE]
        if FALSE in lits:
            return FALSE
        if not lits:
            return TRUE
        v = self.var()
        for l in lits:
            self.add([-v, l])
        self.add([v] + [-l for l in lits])
        return v

    def or_def(self, lits):
        lits = [l for l in lits if l != FALSE]
        if TRUE in lits:
            return TRUE
        if not lits:
            return FALSE
        v = self.var()
        for l in lits:
            self.add([v, -l])
        self.add([-v] + lits)
        return v

    def unit(self, lit):
        if lit == TRUE:
            return
        if lit == FALSE:
            self.add([])          # empty clause: formula is unsatisfiable
            return
        self.add([lit])

    # ---------- sorting network ----------
    def sort_net(self, inputs, need):
        """returns the sorted (decreasing) output wires of a Batcher odd-even merge sort of `inputs`;
        only the comparators in the cone of the output indices in `need` are materialised (their output
        variables are fresh, defined by the full six-clause comparator)."""
        m = len(inputs)
        N = 1
        while N < m:
            N *= 2
        wires = list(inputs) + [FALSE] * (N - m)
        comps = []                   # list of (i, j) with i < j: after the comparator, wire i = max, j = min

        def merge(lo, n, r):
            step = r * 2
            if step < n:
                merge(lo, n, step)
                merge(lo + r, n, step)
                for i in range(lo + r, lo + n - r, step):
                    comps.append((i, i + r))
            else:
                comps.append((lo, lo + r))

        def sort(lo, n):
            if n > 1:
                h = n // 2
                sort(lo, h)
                sort(lo + h, h)
                merge(lo, n, 1)

        sort(0, N)
        # cone of influence: walk the comparator list backwards
        needed_wire = [False] * N
        for j in need:
            needed_wire[j] = True
        use = [False] * len(comps)
        for ci in range(len(comps) - 1, -1, -1):
            i, j = comps[ci]
            if needed_wire[i] or needed_wire[j]:
                use[ci] = True
                needed_wire[i] = needed_wire[j] = True
        for ci, (i, j) in enumerate(comps):
            if not use[ci]:
                continue
            a, b = wires[i], wires[j]
            wires[i], wires[j] = self.comparator(a, b)
        return wires[:m]

    def comparator(self, a, b):
        """(max, min) of two wires"""
        if a == FALSE:
            return b, FALSE
        if b == FALSE:
            return a, FALSE
        if a == TRUE:
            return TRUE, b
        if b == TRUE:
            return TRUE, a
        hi, lo = self.var(), self.var()
        self.add([-a, hi]); self.add([-b, hi]); self.add([-a, -b, lo])
        self.add([-hi, a, b]); self.add([-lo, a]); self.add([-lo, b])
        return hi, lo

    def count_eq(self, lits, K):
        """exactly K of lits are true (repetitions count with multiplicity)"""
        m = len(lits)
        if K < 0 or K > m:
            self.add([])
            return
        need = [j for j in (K - 1, K) if 0 <= j < m]
        out = self.sort_net(lits, need)
        if K >= 1:
            self.unit(out[K - 1])
        if K < m:
            self.unit(neg(out[K]))

    # ---------- at most one ----------
    def amo(self, lits):
        lits = [l for l in lits if l != FALSE]
        if lits.count(TRUE) > 1:
            self.add([])
            return
        if TRUE in lits:
            for l in lits:
                if l != TRUE:
                    self.add([-l])
            return
        m = len(lits)
        if m <= 5:
            for i in range(m):
                for j in range(i + 1, m):
                    self.add([-lits[i], -lits[j]])
            return
        p = 1
        while p * p < m:
            p += 1
        q = (m + p - 1) // p
        u = [self.var() for _ in range(p)]       # u[i]: some element of group i is true
        v = [self.var() for _ in range(q)]       # v[j]: some element with index j in its group is true
        for idx, l in enumerate(lits):
            i, j = divmod(idx, q)
            self.add([-l, u[i]])
            self.add([-l, v[j]])
        self.amo(u)
        self.amo(v)

    def dimacs(self):
        out = ['p cnf %d %d' % (self.nv, len(self.clauses))]
        out.extend(' '.join(map(str, c)) + ' 0' for c in self.clauses)
        return '\n'.join(out) + '\n'


def neg(l):
    if l == TRUE:
        return FALSE
    if l == FALSE:
        return TRUE
    return -l
