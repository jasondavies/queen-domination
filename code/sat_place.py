#!/usr/bin/env python3
"""Independent stage-2 verifier (shares no code with place.c): for each candidate (A,B,z0) build a CNF that is satisfiable iff
some set D of queens inside (rows not in A) x (columns not in B), with at most z0 queens of colour 0
and at most G-z0 of colour 1, dominates Q_N.  Solve with CaDiCaL writing a DRAT proof and check
the proof with drat-trim.  (Independent of place.c: different method, different code.)

usage: sat_place.py N G cadical drat-trim workdir < candidates   (lines "C A B z0", hex)
prints one line per candidate: "V A B z0 UNSAT|SAT drat=VERIFIED|... sha256(cnf) t_solve t_check"
"""
import sys, os, subprocess, hashlib, time

def seq_atmost(lits, k, nv, clauses):
    """Sinz sequential counter: sum(lits) <= k.  returns new nv."""
    n = len(lits)
    if k >= n: return nv
    if k == 0:
        for l in lits: clauses.append([-l])
        return nv
    s = [[0]*(k+1) for _ in range(n)]
    for i in range(n):
        for j in range(1, k+1):
            nv += 1; s[i][j] = nv
    # i = 0
    clauses.append([-lits[0], s[0][1]])
    for j in range(2, k+1): clauses.append([-s[0][j]])
    for i in range(1, n):
        clauses.append([-lits[i], s[i][1]])
        clauses.append([-s[i-1][1], s[i][1]])
        for j in range(2, k+1):
            clauses.append([-lits[i], -s[i-1][j-1], s[i][j]])
            clauses.append([-s[i-1][j], s[i][j]])
        clauses.append([-lits[i], -s[i-1][k]])
    return nv

def build(N, G, A, B, z0):
    z = [z0, G - z0]
    cells = [(r, c) for r in range(N) if not (A >> r) & 1 for c in range(N) if not (B >> c) & 1]
    var = {p: i+1 for i, p in enumerate(cells)}
    nv = len(cells); clauses = []
    for r in range(N):
        for c in range(N):
            cl = [var[(rr, cc)] for (rr, cc) in cells
                  if rr == r or cc == c or rr - cc == r - c or rr + cc == r + c]
            clauses.append(cl)   # empty clause if nothing attacks (r,c): trivially UNSAT
    for q in (0, 1):
        lits = [var[p] for p in cells if (p[0] + p[1]) % 2 == q]
        nv = seq_atmost(lits, z[q], nv, clauses)
    out = ["p cnf %d %d" % (nv, len(clauses))]
    out += [" ".join(map(str, cl)) + " 0" for cl in clauses]
    return "\n".join(out) + "\n"

def main():
    N, G = int(sys.argv[1]), int(sys.argv[2])
    cadical, drat, wd = sys.argv[3], sys.argv[4], sys.argv[5]
    os.makedirs(wd, exist_ok=True)
    for line in sys.stdin:
        p = line.split()
        if not p or p[0] != 'C': continue
        A, B, z0 = int(p[1], 16), int(p[2], 16), int(p[3])
        cnf = build(N, G, A, B, z0)
        h = hashlib.sha256(cnf.encode()).hexdigest()[:16]
        fc = os.path.join(wd, h + ".cnf"); fp = os.path.join(wd, h + ".drat")
        open(fc, "w").write(cnf)
        t0 = time.time()
        r = subprocess.run([cadical, "-q", "--no-binary", fc, fp], capture_output=True, text=True)
        t1 = time.time()
        res = {10: "SAT", 20: "UNSAT"}.get(r.returncode, "ERR%d" % r.returncode)
        chk = "-"
        if res == "UNSAT":
            d = subprocess.run([drat, fc, fp, "-w"], capture_output=True, text=True)
            chk = "VERIFIED" if "s VERIFIED" in d.stdout else "FAILED"
        t2 = time.time()
        print("V %x %x %d %s drat=%s cnf=%s ts=%.3f tc=%.3f" % (A, B, z0, res, chk, h, t1-t0, t2-t1), flush=True)
        os.remove(fc); os.remove(fp)

if __name__ == "__main__":
    main()
