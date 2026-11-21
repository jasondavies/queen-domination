#!/usr/bin/env python3
"""Upper bounds: check explicit dominating sets for Q_26, ..., Q_31.

* Q_26: Kamenetsky's 14-queen set (data/kamenetsky26.txt, from the file of best known placements attached
  to OEIS A075458), given as a 26 x 26 board with 'Q' for queens.
* Q_27: the set of Ostergard and Weakley (Electron. J. Combin. 8 (2001) #R29, Section 5, entry
  "i(Q26) in {13,14} and gamma(Q27) = 14"): in centred coordinates -13..13, the squares (x, y) for even
  x = -12, -10, ..., 12 with y = 6, -12, -6, 8, 0, -8, 10, -2, 4, 12, -10, -4, 2, plus (-9, -9).
  Together with gamma(Q_n) >= n/2 for n < 143, n != 3, 11 (their Corollary 2) this gives gamma(Q_27) = 14.
  The same 13 squares plus (-9, 13) form an independent dominating set of Q_26 (their Proposition 6(B)),
  also checked here.
* Q_28: a 15-queen set found by local search for this work (data/q28_15.txt, a 28 x 28 board).
* Q_30: Weakley's monochromatic 15-queen set (Electron. J. Combin. 29(2) (2022) #P2.50, proof of
  Proposition 21): in coordinates -14..15, the squares (x, y) for odd x = -13, -11, ..., 15 with
  y = 1, -9, 9, 15, -11, -5, 3, -3, 13, 11, 7, -13, -7, -1, 5.
* Q_29: the same 15 squares, after deleting the first row and the first column of the board (all 15 lie
  in the remaining 29 x 29 board); domination is checked directly.
* Q_31: the Q_30 set plus a queen on the new corner square (30, 30).
Together with gamma(Q_n) >= n/2 for n < 143, n != 3, 11 (Ostergard-Weakley, Corollary 2) the last three
give gamma(Q_29) = gamma(Q_30) = 15 and gamma(Q_31) = 16.
* Q_35: the independent 19-queen set of Ostergard and Weakley (Section 5, entry "i(Q35), gamma(Q35), i(Q36),
  gamma(Q36) in {18,19}"): in centred coordinates -17..17, the squares (x, y) for odd x = -17, -15, ..., 17 with
  y = 3, -17, -9, 13, 7, -11, 1, 9, -7, 11, -13, -5, 15, -15, -1, 5, 17, -3, plus (2, 2).  With gamma(Q_35) >= 19
  it gives i(Q_35) = 19.
usage: check_upper.py KAMENETSKY26 Q28_15
Prints JSON."""
import json, sys
from pathlib import Path


def undominated(n, Q):
    return [(r, c) for r in range(n) for c in range(n)
            if not any(r == a or c == b or r - c == a - b or r + c == a + b for a, b in Q)]


def independent(Q):
    return all(not (a == c or b == d or a - b == c - d or a + b == c + d)
               for i, (a, b) in enumerate(Q) for (c, d) in Q[i + 1:])


def ow_sets():
    ys = [6, -12, -6, 8, 0, -8, 10, -2, 4, 12, -10, -4, 2]
    base = list(zip(range(-12, 13, 2), ys))
    ow27 = [(x + 13, y + 13) for x, y in base + [(-9, -9)]]       # board [-13, 13]^2 -> [0, 27)^2
    # Q_25 occupies [-12, 12]^2; adding (-9, 13) gives a set on [-12, 13]^2, i.e. a copy of Q_26
    ow26 = [(x + 12, y + 12) for x, y in base + [(-9, 13)]]
    return ow27, ow26


def weakley30():
    xs = range(-13, 16, 2)
    ys = [1, -9, 9, 15, -11, -5, 3, -3, 13, 11, 7, -13, -7, -1, 5]
    return [(x + 14, y + 14) for x, y in zip(xs, ys)]               # board [-14, 15]^2 -> [0, 30)^2


def ow35():
    ys = [3, -17, -9, 13, 7, -11, 1, 9, -7, 11, -13, -5, 15, -15, -1, 5, 17, -3]
    return [(x + 17, y + 17) for x, y in list(zip(range(-17, 18, 2), ys)) + [(2, 2)]]   # [-17, 17]^2 -> [0, 35)^2


def board(path, n):
    rows = [l.rstrip('\n') for l in open(path) if l.strip()]
    assert len(rows) == n and all(len(r) == n for r in rows)
    return [(r, c) for r in range(n) for c in range(n) if rows[r][c] == 'Q']


def main():
    rows = [l.rstrip('\n') for l in open(sys.argv[1]) if l.strip()]
    assert len(rows) == 26 and all(len(r) == 26 for r in rows)
    K = [(r, c) for r in range(26) for c in range(26) if rows[r][c] == 'Q']
    ow27, ow26 = ow_sets()
    out = {'kamenetsky26': {'queens': len(K), 'undominated': len(undominated(26, K))},
           'ow27': {'queens': len(set(ow27)), 'undominated': len(undominated(27, ow27))},
           'ow26': {'queens': len(set(ow26)), 'undominated': len(undominated(26, ow26)),
                    'independent': independent(ow26)}}
    q28 = board(sys.argv[2], 28)
    w30 = weakley30()
    q29 = [(r - 1, c - 1) for r, c in w30]
    q31 = w30 + [(30, 30)]
    for key, n, Q in (('q28', 28, q28), ('q29', 29, q29), ('weakley30', 30, w30), ('q31', 31, q31)):
        out[key] = {'n': n, 'queens': len(set(Q)), 'on_board': all(0 <= r < n and 0 <= c < n for r, c in Q),
                    'undominated': len(undominated(n, Q))}
    out['weakley30']['monochromatic'] = len(set((r + c) % 2 for r, c in w30)) == 1
    o35 = ow35()
    out['ow35'] = {'n': 35, 'queens': len(set(o35)), 'on_board': all(0 <= r < 35 and 0 <= c < 35 for r, c in o35),
                   'undominated': len(undominated(35, o35)), 'independent': independent(o35)}
    out['ok'] = (out['kamenetsky26'] == {'queens': 14, 'undominated': 0} and out['ow27'] == {'queens': 14, 'undominated': 0}
                 and out['ow26'] == {'queens': 14, 'undominated': 0, 'independent': True}
                 and all(out[k]['on_board'] and out[k]['undominated'] == 0 for k in ('q28', 'q29', 'weakley30', 'q31'))
                 and (out['q28']['queens'], out['q29']['queens'], out['weakley30']['queens'], out['q31']['queens']) == (15, 15, 15, 16)
                 and out['ow35'] == {'n': 35, 'queens': 19, 'on_board': True, 'undominated': 0, 'independent': True})
    print(json.dumps(out))


if __name__ == '__main__':
    main()
