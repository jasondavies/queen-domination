#!/usr/bin/env python3
"""Upper bound gamma(Q44) <= 23: Neuhaus's 22-queen dominating set of Q43 (thesis appendix 01, file
data/frame/neuhaus/appendix_01_q43_01cover.txt, copied unchanged from github.com/stefanneuhaus/queens-domination-solutions,
CC BY 4.0)
plus the corner (43, 43).  Any dominating set of Q_{n-1} plus the new corner dominates Q_n (the corner queen covers the
new row and column).  Both sets are checked here by brute force over all squares, without geom.py.  The file's pairs
are used as (column, row); domination is invariant under transposition, so the reading does not matter.
Prints the 23-set as JSON (the run wrote it to data/frame/q44_23.json)."""
import json, os, re
HERE = os.path.dirname(os.path.abspath(__file__))
src = os.path.join(HERE, '..', '..', 'data', 'frame', 'neuhaus', 'appendix_01_q43_01cover.txt')
P = [tuple(map(int, m)) for m in re.findall(r'^\((\d+),\s*(\d+)\)\s*$', open(src).read(), re.M)]


def undominated(n, D):
    return [(x, y) for x in range(n) for y in range(n) if not any(x == a or y == b or x - y == a - b or x + y == a + b for a, b in D)]


assert len(P) == 22 == len(set(P)) and all(0 <= x < 43 and 0 <= y < 43 for x, y in P)
u43 = undominated(43, P)
D = sorted(P + [(43, 43)])
u44 = undominated(44, D)
out = {'n': 44, 'size': len(D), 'set_col_row': [list(p) for p in D], 'undominated': len(u44), 'q43_22_undominated': len(u43),
       'source': "Neuhaus 2009 thesis appendix 01 (22-set of Q43, via github stefanneuhaus/queens-domination-solutions) + corner (43,43); checked directly here"}
print(json.dumps(out))
