#!/usr/bin/env python3
"""Compare the output of scripts/CrossCheck.lean (stdin) with geom.cases_by_frame of code/frame/geom.py.
usage (in lean/): lake env lean scripts/CrossCheck.lean | python3 -B scripts/crosscheck.py ../code/frame"""
import sys, ast
sys.dont_write_bytecode = True
sys.path.insert(0, sys.argv[1])
import geom

ok = True
npairs = 0
for line in sys.stdin:
    line = line.strip()
    if not line or not line[0].isdigit():
        if line:
            print('unexpected line:', line[:200]); ok = False
        continue
    n, k, rest = line.split(' ', 2)
    n, k = int(n), int(k)
    lean = ast.literal_eval(rest)
    py = []
    for c in geom.cases_by_frame(n, k):
        ml, mr, mb, mt, dR, dC, dT, dS = c
        py.append((((ml * 100 + mr) * 100 + mb) * 100 + mt) * 100000000 + dR * 1000000 + dC * 10000 + dT * 100 + dS)
    same = (lean == py)
    ok &= same
    npairs += 1
    print('n=%d k=%d: lean %d cases, python %d cases, frames %d, identical lists: %s' % (
        n, k, len(lean), len(py), len({c[:4] for c in geom.cases_by_frame(n, k)}), same))
print('ALL IDENTICAL' if ok and npairs else 'MISMATCH')
sys.exit(0 if ok and npairs else 1)
