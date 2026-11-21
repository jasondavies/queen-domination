#!/usr/bin/env python3
"""Check that QueenDom/Cases<N>Data.lean is exactly the case list solved by the SAT run.

usage: python3 -B scripts/check_cases.py N K QueenDom/Cases<N>Data.lean RECORDS CODE [--json]
       (from the repository root: lean/scripts/check_cases.py 35 18 lean/QueenDom/Cases35Data.lean data/frame code/frame)

Reads the Lean file directly (the defs caseCodes<N>_<p>_<q> and the table caseCodes<N>T), rebuilds the list
`tableList K caseCodes<N>T` (concatenation in the order of marginPairs K = lexicographic (ml, mr)), and checks:
 1. every def caseCodes<N>_<p>_<q> sits at position [p][q] of the table and contains only cases with
    (ml, mr) = (p, q); the rebuilt list is strictly increasing (so: sorted, no duplicates);
 2. the set of case keys occurring in ANY record of RECORDS/d_N_K.jsonl, d_N_K_sq.jsonl, h_N_K.jsonl (or .xz)
    equals the Lean list (no case missing, no extra key);
 3. every case of the Lean list is refuted by the run (plain record UNSAT + VERIFIED, or a cover by verified
    sbp cube records, the rule of final_check35.py); no SAT record;
 4. the Lean list equals geom.cases_by_frame(N, K) of CODE/geom.py, in the same order.
Exit status 0 iff all checks pass."""
import sys, os, re, json
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from runlog import analyse, decode, sha

n, k, lean_path, recdir, codedir = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4], sys.argv[5]
txt = open(lean_path).read()
defs = {}
for m in re.finditer(r'def caseCodes%d_(\d+)_(\d+) : List Nat := \[([^\]]*)\]' % n, txt):
    defs[(int(m.group(1)), int(m.group(2)))] = [int(t) for t in re.findall(r'\d+', m.group(3))]
tm = re.search(r'def caseCodes%dT : List \(List \(List Nat\)\) := \[\n(.*?)\n\]' % n, txt, re.S)
rows = [re.findall(r'caseCodes%d_\d+_\d+|\[\]' % n, line) for line in tm.group(1).split('\n')]
ok = True
problems = []
codes = []
used = set()
for p in range(k + 1):                                  # marginPairs k
    for q in range(k + 1 - p):
        entry = rows[p][q] if p < len(rows) and q < len(rows[p]) else '[]'
        if entry == '[]':
            continue
        pq = tuple(int(t) for t in entry.split('_')[1:])
        if pq != (p, q):
            problems.append('table entry [%d][%d] is %s' % (p, q, entry))
        used.add(pq)
        for c in defs[pq]:
            if decode(c)[:2] != (p, q):
                problems.append('case %s in def %s' % (decode(c), entry))
        codes += defs[pq]
if len(rows) != k + 1 or any(len(rows[p]) != k + 1 - p for p in range(k + 1)):
    problems.append('table shape differs from marginPairs %d' % k)
if used != set(defs):
    problems.append('defs not referenced by the table: %s' % sorted(set(defs) - used))
lean = [decode(c) for c in codes]
increasing = all(a < b for a, b in zip(lean, lean[1:]))
refuted, info, keys = analyse(recdir, n, k)
sys.path.insert(0, codedir)
import geom
g = geom.cases_by_frame(n, k)
res = {
    'n': n, 'k': k, 'lean_file': lean_path, 'lean_file_sha256': sha(lean_path), 'lean_cases': len(lean),
    'lean_frames': len({c[:4] for c in lean}), 'strictly_increasing': increasing,
    'record_files': info['files'], 'case_keys_in_records': len(keys),
    'keys_equal_lean_list': set(lean) == keys,
    'keys_missing_from_records': len(set(lean) - keys), 'record_keys_not_in_lean': len(keys - set(lean)),
    'refuted_plain': info['plain_refuted'], 'refuted_by_cubes': info['cube_refuted'],
    'refuted_by_cubes_unsplit': info['cube_refuted_unsplit'],
    'every_lean_case_refuted': set(lean) <= set(refuted), 'sat_records': info['sat_records'],
    'geom_cases_by_frame': len(g), 'equal_to_geom_same_order': g == lean, 'problems': problems[:10],
}
ok = (not problems and increasing and res['keys_equal_lean_list'] and res['every_lean_case_refuted']
      and set(refuted) == set(lean) and info['sat_records'] == 0 and res['equal_to_geom_same_order'])
res['OK'] = ok
print(json.dumps(res) if '--json' in sys.argv else json.dumps(res, indent=1))
print('OK' if ok else 'MISMATCH')
sys.exit(0 if ok else 1)
