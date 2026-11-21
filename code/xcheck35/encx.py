#!/usr/bin/env python3
"""Encoding X: the cross-check formula Psi(case) for the frame method, written independently of enc.py
and enc_b.py (neither was read while writing this file).

Case (ml, mr, mb, mt, dR, dC, dT, dS); a = ml, b = n-1-mr (extreme empty columns), c = mb, d = n-1-mt
(extreme empty rows).  Squares (x, y) = (column, row); difference diagonal t = y - x, sum diagonal s = x + y.

Variables and constraints (every one is satisfied by any dominating k-set with this case, with all
auxiliary variables given their defined meaning -- see the soundness argument in NOTES / README):
  Q     q(x, y) for every square.
  LINES R[y], C[x], T[t], S[s] with full definitions o(L) <-> OR of the q on L.
  DOM   R[y] v C[x] v T[y-x] v S[x+y] for every square.
  FRAME C[x] for x < a or x > b, -C[a], -C[b]; R[y] for y < c or y > d, -R[c], -R[d].
  CARD  exactly k of the q;  exactly k-dR of the R, k-dC of the C, k-dT of the T, k-dS of the S
        (odd-even merge sorting networks).
  AMO   for each line type with deficit 0, at most one q per line (product encoding).
  NEEDY for each border square s = (x, y): nd(s) <-> -C[x] & -R[y]   (full AND definition).
  IDENT for a set X of border squares and a cap in {1, 2}:  for a dominating set every needy square lies on
        an occupied diagonal (and on at most two), so double counting the pairs (occupied diagonal L, needy
        square of X on L) gives
            sum_L o(L) * (cap - nb_X(L))  +  #{s in X needy with both diagonals occupied}
              =  cap * (2k - dT - dS) - N_X,
        nb_X(L) = number of needy squares of X on L, N_X = number of needy squares of X, which is fixed by
        the case: N_border = 2(n-k+dR) + 2(n-k+dC) - 4, N_vertical sides = 2(n-k+dR),
        N_horizontal sides = 2(n-k+dC) (all empty rows lie in [c, d], all empty columns in [a, b]).
        Per diagonal L with squares s_1..s_m in X:  o(L)(cap - sum nd(s_i)) is encoded
           if m <= cap:  (cap - m) copies of o(L)  +  sum_i [o(L) & -nd(s_i)]
           if m >  cap:  cap copies of o(L) + sum_i -[o(L) & nd(s_i)]   and the right side is raised by m.
        The identity is imposed as an equality (sorting network), with all AND variables fully defined.
        Imposed: X = border with cap 2 (Theorem F); X = vertical sides with cap 1 (Theorem V) and X =
        horizontal sides with cap 1 (Theorem H) -- both for every box shape, which is valid in this
        generic form because diagonals meeting X twice are handled exactly (the m > cap branch).
  CUBE  optional unit literals (for cube splitting).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cnf import CNF, TRUE, FALSE, neg


class Psi:
    def __init__(self, n, k, case, vh_always=True, cube=()):
        self.n, self.k, self.case = n, k, tuple(case)
        ml, mr, mb, mt, dR, dC, dT, dS = case
        a, b, c, d = ml, n - 1 - mr, mb, n - 1 - mt
        self.box = (a, b, c, d)
        w, h = b - a, d - c
        F = CNF()
        self.cnf = F
        q = {(x, y): F.var() for x in range(n) for y in range(n)}
        self.q = q
        on = {}                      # line key -> list of squares
        for (x, y) in q:
            for key in (('R', y), ('C', x), ('T', y - x), ('S', x + y)):
                on.setdefault(key, []).append((x, y))
        self.on = on
        o = {key: F.or_def([q[p] for p in sq]) for key, sq in sorted(on.items())}
        self.o = o
        # DOM
        for (x, y) in q:
            F.add([o[('R', y)], o[('C', x)], o[('T', y - x)], o[('S', x + y)]])
        # FRAME
        for x in range(n):
            F.unit(o[('C', x)] if (x < a or x > b) else (neg(o[('C', x)]) if x in (a, b) else TRUE))
        for y in range(n):
            F.unit(o[('R', y)] if (y < c or y > d) else (neg(o[('R', y)]) if y in (c, d) else TRUE))
        # CARD
        F.count_eq([q[p] for p in sorted(q)], k)
        for typ, dfc in (('R', dR), ('C', dC), ('T', dT), ('S', dS)):
            F.count_eq([o[key] for key in sorted(o) if key[0] == typ], k - dfc)
        # AMO
        for typ, dfc in (('R', dR), ('C', dC), ('T', dT), ('S', dS)):
            if dfc == 0:
                for key in sorted(on):
                    if key[0] == typ:
                        F.amo([q[p] for p in on[key]])
        # NEEDY
        border = [(x, y) for x in range(a, b + 1) for y in range(c, d + 1) if x in (a, b) or y in (c, d)]
        nd = {p: F.and_def([neg(o[('C', p[0])]), neg(o[('R', p[1])])]) for p in border}
        self.nd = nd
        vert = [p for p in border if p[0] in (a, b)]
        hor = [p for p in border if p[1] in (c, d)]
        diags = [key for key in sorted(on) if key[0] in 'TS']

        def ident(X, cap, rhs):
            Xs = set(X)
            lits = []
            for L in diags:
                XL = [p for p in on[L] if p in Xs]
                m = len(XL)
                if m <= cap:
                    lits += [o[L]] * (cap - m)
                    lits += [F.and_def([o[L], neg(nd[p])]) for p in XL]
                else:
                    lits += [o[L]] * cap
                    lits += [neg(F.and_def([o[L], nd[p]])) for p in XL]
                    rhs += m
            for p in X:
                x, y = p
                lits.append(F.and_def([nd[p], o[('T', y - x)], o[('S', x + y)]]))
            F.count_eq(lits, rhs)

        ident(border, 2, 2 * (2 * k - dT - dS) - (2 * (n - k + dR) + 2 * (n - k + dC) - 4))
        if vh_always or w >= h:
            ident(vert, 1, (2 * k - dT - dS) - 2 * (n - k + dR))
        if vh_always or h >= w:
            ident(hor, 1, (2 * k - dT - dS) - 2 * (n - k + dC))
        # CUBE: literals given as (line key, value) or (('q', x, y), value)
        for key, val in cube:
            v = q[(key[1], key[2])] if key[0] == 'q' else o[tuple(key)]
            F.unit(v if val else neg(v))

    def decode(self, model):
        pos = set(l for l in model if l > 0)
        return sorted(p for p, v in self.q.items() if v in pos)

    def fix_set_units(self, D):
        Ds = set(D)
        return [[v if p in Ds else -v] for p, v in self.q.items()]


if __name__ == '__main__':
    n, k = int(sys.argv[1]), int(sys.argv[2])
    case = tuple(int(v) for v in sys.argv[3].split(','))
    P = Psi(n, k, case)
    print('vars %d clauses %d' % (P.cnf.nv, len(P.cnf.clauses)))
