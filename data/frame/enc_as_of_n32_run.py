#!/usr/bin/env python3
"""CNF for one case of the frame method.

Case = (n, k, ml, mr, mb, mt, dR, dC, dT, dS): a set D of exactly k queens on the n x n board, dominating,
whose extreme empty columns are a = ml, b = n-1-mr, extreme empty rows c = mb, d = n-1-mt, and with
exactly k-dR occupied rows, k-dC occupied columns, k-dT occupied difference diagonals, k-dS occupied sum
diagonals.  Squares (x, y) = (column, row); difference diagonal t = y - x, sum diagonal s = x + y.

Variables: q[x][y]; oR[y], oC[x], oT[t], oS[s] ("line occupied"), defined by full equivalences.
Clauses:
  DEF   q[x][y] -> oR[y], oC[x], oT[y-x], oS[x+y];   o(L) -> OR of q on L
  DOM   oR[y] v oC[x] v oT[y-x] v oS[x+y]                         for every square
  CARD  exactly k-dR of oR, k-dC of oC, k-dT of oT, k-dS of oS; exactly k of q
        (the last one is omitted when some deficit is 0: then it is implied by AMO + CARD of that type)
  AMO   at most one queen on every line of a type with deficit 0
  FRAME oC[x] for x < a and x > b, not oC[a], not oC[b]; oR[y] for y < c and y > d, not oR[c], not oR[d]
  (F)   at most G_F = 8k-4n+4-2(dR+dC+dT+dS) of the "waste" literals of the border        (see NOTES F.1)
  (V)   if w >= h: at most 4k-2n-dT-dS-2dR (+ [u0] + [v0] if w = h) waste literals of the vertical sides
  (H)   if h >= w: the same for the horizontal sides with dC
Cardinalities: Sinz sequential counter (own implementation, tested in test_enc.py).
"""
import hashlib


def atmost(lits, k, new, cls):
    """sum(lits) <= k; lits may contain repeated literals (each occurrence counts)."""
    n = len(lits)
    if k < 0:
        cls.append([]); return
    if k >= n:
        return
    if k == 0:
        for l in lits:
            cls.append([-l])
        return
    s = [[new() for _ in range(k)] for _ in range(n - 1)]      # s[i][j]: at least j+1 of lits[0..i] are true
    cls.append([-lits[0], s[0][0]])
    for j in range(1, k):
        cls.append([-s[0][j]])
    for i in range(1, n - 1):
        cls.append([-lits[i], s[i][0]]); cls.append([-s[i - 1][0], s[i][0]])
        for j in range(1, k):
            cls.append([-lits[i], -s[i - 1][j - 1], s[i][j]]); cls.append([-s[i - 1][j], s[i][j]])
        cls.append([-lits[i], -s[i - 1][k - 1]])
    cls.append([-lits[n - 1], -s[n - 2][k - 1]])


def exactly(lits, k, new, cls):
    atmost(lits, k, new, cls)
    atmost([-l for l in lits], len(lits) - k, new, cls)


class Base:
    """the part of the formula that depends only on (n, k, deficits)"""

    def __init__(self, n, k, dv, use_amo=True):
        self.n, self.k, self.dv = n, k, dv
        dR, dC, dT, dS = dv
        self.nv = 0
        self.q = [[self.new() for y in range(n)] for x in range(n)]
        self.oR = [self.new() for y in range(n)]
        self.oC = [self.new() for x in range(n)]
        self.oT = {t: self.new() for t in range(-(n - 1), n)}
        self.oS = {s: self.new() for s in range(0, 2 * n - 1)}
        cls = self.cls = []
        q = self.q
        fam = {('R', y): [q[x][y] for x in range(n)] for y in range(n)}
        fam.update({('C', x): [q[x][y] for y in range(n)] for x in range(n)})
        fam.update({('T', t): [q[x][x + t] for x in range(n) if 0 <= x + t < n] for t in self.oT})
        fam.update({('S', s): [q[x][s - x] for x in range(n) if 0 <= s - x < n] for s in self.oS})
        ov = {'R': lambda i: self.oR[i], 'C': lambda i: self.oC[i], 'T': lambda i: self.oT[i], 'S': lambda i: self.oS[i]}
        for (kind, i), qs in fam.items():
            o = ov[kind](i)
            for v in qs:
                cls.append([-v, o])
            cls.append([-o] + qs)
        for x in range(n):
            for y in range(n):
                cls.append([self.oR[y], self.oC[x], self.oT[y - x], self.oS[x + y]])
        exactly(self.oR, k - dR, self.new, cls)
        exactly(self.oC, k - dC, self.new, cls)
        exactly(list(self.oT.values()), k - dT, self.new, cls)
        exactly(list(self.oS.values()), k - dS, self.new, cls)
        zero = [kind for kind, dd in zip('RCTS', dv) if dd == 0]
        if use_amo:
            for (kind, i), qs in fam.items():
                if kind in zero:
                    for u in range(len(qs)):
                        for v in range(u + 1, len(qs)):
                            cls.append([-qs[u], -qs[v]])
        if not (use_amo and zero):
            exactly([q[x][y] for x in range(n) for y in range(n)], k, self.new, cls)
        self.text = ''.join(' '.join(map(str, c)) + ' 0\n' for c in cls)

    def new(self):
        self.nv += 1
        return self.nv


def case_extra(base, case, use_F=True, use_V=True, use_H=True, debug=None):
    """frame-dependent clauses; returns (clauses, number of variables in total)"""
    n, k = base.n, base.k
    ml, mr, mb, mt, dR, dC, dT, dS = case
    assert (dR, dC, dT, dS) == tuple(base.dv)
    a, b, c, d = ml, n - 1 - mr, mb, n - 1 - mt
    w, h = b - a, d - c
    assert w >= 1 and h >= 1
    nv = [base.nv]

    def new():
        nv[0] += 1
        return nv[0]
    cls = []
    oR, oC, oT, oS = base.oR, base.oC, base.oT, base.oS
    for x in range(n):
        if x < a or x > b:
            cls.append([oC[x]])
    for y in range(n):
        if y < c or y > d:
            cls.append([oR[y]])
    cls += [[-oC[a]], [-oC[b]], [-oR[c]], [-oR[d]]]
    lines_ = [('T', t) for t in oT] + [('S', s) for s in oS]
    lv = lambda L: oT[L[1]] if L[0] == 'T' else oS[L[1]]

    def nonneedy_lit(sq):
        """literal that is true iff the border square sq is NOT needy (None if it is always needy: corners)"""
        x, y = sq
        colE = x in (a, b); rowE = y in (c, d)
        if colE and rowE:
            return None
        return oR[y] if colE else oC[x]

    def waste(squares, weight_full):
        """waste literals for the incidence count between occupied diagonals and the given border squares"""
        sqs = set(squares)
        lits = []
        conds = []          # for tests: the conjunction of literals that makes each waste literal true
        for L in lines_:
            if L[0] == 'T':
                on = [(x, x + L[1]) for x in range(a, b + 1) if (x, x + L[1]) in sqs]
            else:
                on = [(x, L[1] - x) for x in range(a, b + 1) if (x, L[1] - x) in sqs]
            assert len(on) <= 2
            if weight_full:
                lits += [lv(L)] * (2 - len(on)); conds += [(lv(L),)] * (2 - len(on))
            elif not on:
                lits.append(lv(L)); conds.append((lv(L),))
            for sq in on:
                nl = nonneedy_lit(sq)
                if nl is not None:
                    e = new(); cls.append([-lv(L), -nl, e]); lits.append(e); conds.append((lv(L), nl))
        for (x, y) in squares:
            nl = nonneedy_lit((x, y))
            f = new()
            cls.append([-oT[y - x], -oS[x + y], f] + ([nl] if nl is not None else []))
            lits.append(f); conds.append((oT[y - x], oS[x + y]) + ((-nl,) if nl is not None else ()))
        if debug is not None:
            debug.setdefault('waste', []).append(conds)
        return lits

    if use_F:
        Bd = [(x, y) for x in range(a, b + 1) for y in range(c, d + 1) if x in (a, b) or y in (c, d)]
        atmost(waste(Bd, True), 8 * k - 4 * n + 4 - 2 * (dR + dC + dT + dS), new, cls)
        if debug is not None:
            debug['F'] = (debug['waste'][-1], 8 * k - 4 * n + 4 - 2 * (dR + dC + dT + dS), ())
    u0, v0 = oT[c - a], oS[a + d]
    if use_V and w >= h:
        VS = [(x, y) for x in (a, b) for y in range(c, d + 1)]
        g = 4 * k - 2 * n - dT - dS - 2 * dR
        if w == h:
            atmost(waste(VS, False) + [-u0, -v0], g + 2, new, cls)
        else:
            atmost(waste(VS, False), g, new, cls)
        if debug is not None:
            debug['V'] = (debug['waste'][-1], g, (u0, v0) if w == h else ())
    if use_H and h >= w:
        HS = [(x, y) for y in (c, d) for x in range(a, b + 1)]
        g = 4 * k - 2 * n - dT - dS - 2 * dC
        if w == h:
            atmost(waste(HS, False) + [-u0, -v0], g + 2, new, cls)
        else:
            atmost(waste(HS, False), g, new, cls)
        if debug is not None:
            debug['H'] = (debug['waste'][-1], g, (u0, v0) if w == h else ())
    return cls, nv[0]


def dimacs(base, extra, nv):
    txt = 'p cnf %d %d\n' % (nv, len(base.cls) + len(extra)) + base.text + ''.join(' '.join(map(str, c)) + ' 0\n' for c in extra)
    return txt


def sha(txt):
    return hashlib.sha256(txt.encode()).hexdigest()
