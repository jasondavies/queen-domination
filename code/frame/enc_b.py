#!/usr/bin/env python3
"""Second encoding of the case formula Phi(case), written separately from enc.py, for cross-checking.
Differences: cardinalities by PySAT totalizers (not the own sequential counter); AMO by PySAT ladder
encoding; the waste terms are obtained by listing all board squares of every diagonal and intersecting with
explicitly listed border / side squares; waste variables are defined by full equivalences and (F), (V), (H)
are imposed as EQUALITIES (the exact identities), with weight-2 terms via an equivalent copy variable;
"exactly k queens" is always present.  Same interface as enc.py (Base, case_extra)."""
from pysat.card import CardEnc, EncType


class Base:
    def __init__(self, n, k, dv):
        self.n, self.k, self.dv = n, k, tuple(dv)
        self.nv = 0
        self.q = [[self.new() for y in range(n)] for x in range(n)]
        self.oR = [self.new() for _ in range(n)]
        self.oC = [self.new() for _ in range(n)]
        self.oT = {t: self.new() for t in range(1 - n, n)}
        self.oS = {s: self.new() for s in range(2 * n - 1)}
        cls = self.cls = []
        sq = [(x, y) for x in range(n) for y in range(n)]
        groups = [('R', self.oR, lambda x, y: y), ('C', self.oC, lambda x, y: x),
                  ('T', self.oT, lambda x, y: y - x), ('S', self.oS, lambda x, y: x + y)]
        for (kind, ov, idx), dd in zip(groups, dv):
            members = {}
            for (x, y) in sq:
                members.setdefault(idx(x, y), []).append(self.q[x][y])
            keys = range(n) if kind in 'RC' else list(ov)
            for i in keys:
                o = ov[i]
                cls.append([-o] + members[i])
                cls.extend([-v, o] for v in members[i])
                if dd == 0 and len(members[i]) > 1:
                    self.card(CardEnc.atmost(lits=members[i], bound=1, top_id=self.nv, encoding=EncType.ladder))
            lits = [ov[i] for i in keys]
            self.card(CardEnc.equals(lits=lits, bound=k - dd, top_id=self.nv, encoding=EncType.totalizer))
        for (x, y) in sq:
            cls.append([self.oS[x + y], self.oT[y - x], self.oC[x], self.oR[y]])
        self.card(CardEnc.equals(lits=[self.q[x][y] for (x, y) in sq], bound=k, top_id=self.nv, encoding=EncType.totalizer))

    def new(self):
        self.nv += 1
        return self.nv

    def card(self, enc_):
        self.cls.extend(enc_.clauses)
        self.nv = max(self.nv, enc_.nv)


def case_extra(base, case, use_F=True, use_V=True, use_H=True, debug=None):
    n, k = base.n, base.k
    ml, mr, mb, mt, dR, dC, dT, dS = case
    a, b, c, d = ml, n - 1 - mr, mb, n - 1 - mt
    w, h = b - a, d - c
    top = [base.nv]
    cls = []

    def new():
        top[0] += 1
        return top[0]

    def AND(lits):
        """fresh variable equivalent to the conjunction of lits"""
        v = new()
        cls.append([v] + [-l for l in lits])
        cls.extend([-v, l] for l in lits)
        return v
    for x in range(n):
        cls.append([-base.oC[x]] if x in (a, b) else ([base.oC[x]] if not (a < x < b) else None) or [])
    for y in range(n):
        cls.append([-base.oR[y]] if y in (c, d) else ([base.oR[y]] if not (c < y < d) else None) or [])
    cls[:] = [cl for cl in cls if cl]
    diag = {}
    for x in range(n):
        for y in range(n):
            diag.setdefault(('T', y - x), []).append((x, y))
            diag.setdefault(('S', x + y), []).append((x, y))
    lit = lambda L: base.oT[L[1]] if L[0] == 'T' else base.oS[L[1]]
    empty_col = lambda x: -base.oC[x]
    empty_row = lambda y: -base.oR[y]

    def terms(X, full):
        X = set(X); out = []
        for L, squares in diag.items():
            hit = [s for s in squares if s in X]
            missing = (2 - len(hit)) if full else (1 if not hit else 0)
            for _ in range(missing):
                out.append(AND([lit(L)]))
            for (x, y) in hit:                       # occupied diagonal through a non-needy square of X
                if x in (a, b) and y in (c, d):
                    continue                         # corners are needy
                occ_line = base.oR[y] if x in (a, b) else base.oC[x]
                out.append(AND([lit(L), occ_line]))
        for (x, y) in X:                             # needy square on two occupied diagonals
            out.append(AND([base.oT[y - x], base.oS[x + y], empty_col(x), empty_row(y)]))
        return out

    def equals(lits, bound):
        if bound < 0 or bound > len(lits):
            cls.append([]); return
        e = CardEnc.equals(lits=lits, bound=bound, top_id=top[0], encoding=EncType.totalizer)
        cls.extend(e.clauses); top[0] = max(top[0], e.nv)
    box = [(x, y) for x in range(a, b + 1) for y in range(c, d + 1)]
    u0, v0 = base.oT[c - a], base.oS[a + d]
    if use_F:
        equals(terms([s for s in box if s[0] in (a, b) or s[1] in (c, d)], True), 8 * k - 4 * n + 4 - 2 * (dR + dC + dT + dS))
    for use, cond, X, dd in ((use_V, w >= h, [s for s in box if s[0] in (a, b)], dR), (use_H, h >= w, [s for s in box if s[1] in (c, d)], dC)):
        if use and cond:
            g = 4 * k - 2 * n - dT - dS - 2 * dd
            if w == h:
                equals(terms(X, False) + [AND([-u0]), AND([-v0])], g + 2)
            else:
                equals(terms(X, False), g)
    return cls, top[0]
