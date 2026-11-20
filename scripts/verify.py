#!/usr/bin/env python3
"""Reproduce every computation and every number in the paper.

  .venv/bin/python scripts/verify.py                 # default: about 20 minutes, at most 3 processes
  .venv/bin/python scripts/verify.py --only build|small|referee|records|sample|records28|sample28|upper|paper
  .venv/bin/python scripts/verify.py --full          # default steps + the whole n = 26 computation again
                                                     # (about 15 CPU hours on 3 cores) and n = 16 (g = 9), 20, 22
  .venv/bin/python scripts/verify.py --heavy28       # default steps + a larger n = 28 rerun (about 6 CPU hours):
                                                     # stage 1 for all parts with z0 <= 5, the whole stage-1
                                                     # certificate for z0 <= 6, 40 cubes for z0 = 7, 2000 SAT checks
  .venv/bin/python scripts/verify.py --certify-all   # default steps + the complete certificate replay for n = 26
                                                     # and n = 28 (about 45 CPU hours): every stage-1 cube and every
                                                     # stage-2 formula rebuilt from the survivor lists, solved and
                                                     # checked; resumable (build/certify, manifest-bound)
  options: --jobs J (parallel processes, default 3); --write-pdf (copy the reproducible build to paper/)

verification/ is not tracked: a run never modifies tracked files.  The paper is built in build/paper with
SOURCE_DATE_EPOCH, so the build is byte-identical to the committed paper/queen-domination.pdf.

Each step writes a machine-readable JSON file to verification/.  Each gate below parses that JSON and
compares it EXACTLY with the paper's claims in claims.json (printed roundings must be correct roundings).
Logs go to verification/<step>.log and a summary with input and PDF hashes to verification/summary.json.
The exit status is nonzero if any gate fails, or if the LaTeX log has a warning or a bad box.

CaDiCaL rel-3.1.0 and drat-trim (commit 2e3b2dc) are not part of the repository: scripts/get_tools.sh
downloads them, checks their SHA-256 and builds them in tools/ (git-ignored).
"""
import argparse, hashlib, json, os, re, shutil, subprocess, sys, time
from decimal import Decimal, ROUND_HALF_UP
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LOGS = ROOT / 'verification'
PY = sys.executable
CODE = ROOT / 'code'
BUILD = ROOT / 'build'
ENV = dict(os.environ, OMP_NUM_THREADS='1', PYTHONHASHSEED='0')
CLAIMS = json.loads((ROOT / 'claims.json').read_text())
JOBS = 3


def C(k):
    return CLAIMS[k]


def I(k):
    return int(CLAIMS[k])


def rnd(x, places=0):
    """x rounded half-up to `places` decimals, as a string (the form printed in the paper)."""
    q = Decimal(1).scaleb(-places)
    return str(Decimal(repr(x)).quantize(q, rounding=ROUND_HALF_UP))


def sanitize(text):
    return text.replace(str(ROOT), '.').replace(str(Path.home()), '~')


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def J(name):
    return json.loads((LOGS / name).read_text())


def run(name, cmd, cwd, gate, json_out=None):
    """Run cmd; if json_out, its stdout (JSON lines) is stored as verification/<json_out>; then apply gate."""
    t0 = time.time()
    proc = subprocess.run(['nice', '-n', '10'] + cmd, cwd=cwd, capture_output=True, text=True, env=ENV)
    shown = ['python' if c == PY else sanitize(str(c)) for c in cmd]
    if json_out:
        recs = [json.loads(l) for l in proc.stdout.splitlines() if l.startswith('{')]
        (LOGS / json_out).write_text(json.dumps(recs if len(recs) != 1 else recs[0], indent=1) + '\n')
    out = sanitize(proc.stdout[-20000:] + proc.stderr[-20000:])
    msgs, ok = [], proc.returncode == 0
    if ok:
        try:
            msgs = gate()
            ok = all(m[0] for m in msgs)
        except Exception as exc:              # a missing or malformed output is a failure
            ok, msgs = False, [(False, 'gate error: %r' % exc)]
    (LOGS / (name + '.log')).write_text('$ ' + ' '.join(shown) + '\n' + out +
                                        ''.join('\n[gate] %s %s' % ('ok  ' if g else 'FAIL', t) for g, t in msgs) + '\n')
    print('%-22s %s  (%.0fs)' % (name, 'PASS' if ok else 'FAIL', time.time() - t0), flush=True)
    for g, t in msgs:
        if not g:
            print('    gate failed:', t)
    return {'name': name, 'ok': ok, 'seconds': round(time.time() - t0, 1), 'cmd': shown,
            'gates': [{'ok': g, 'check': t} for g, t in msgs]}


# ------------------------------------------------------------------ gates
def g_build():
    progs = ['stage1', 'stage1_v', 'brute_ab', 'place']
    return [(all(os.access(BUILD / p, os.X_OK) for p in progs), 'C programs compiled: ' + ', '.join(progs)),
            (os.access(ROOT / 'tools' / 'cadical', os.X_OK) and os.access(ROOT / 'tools' / 'drat-trim', os.X_OK),
             'CaDiCaL %s and drat-trim built from SHA-256-checked tarballs' % C('cadicalVersion'))]


def small_case(d, row):
    n, g = int(row['n']), int(row['g'])
    ok = (d['n'], d['g'], d['classes']) == (n, g, int(row['classes'])) and all(all(v.values()) for v in d['xcheck'].values())
    if 'mono' in row:
        ok = ok and d['monochromatic'] == int(row['mono'])
    if 'pairs' in row:
        ok = ok and sum(d['pairs'].values()) == int(row['pairs'])
    return ok


def g_small(name, rows):
    def g():
        ds = J(name + '.json')
        ds = ds if isinstance(ds, list) else [ds]
        msgs = []
        for d, row in zip(ds, rows):
            msgs.append((small_case(d, row), 'n = %s, g = %s: %s classes%s; stage1 = stage1_v%s on every z0'
                         % (row['n'], row['g'], row['classes'], (', %s pairs' % row['pairs']) if 'pairs' in row else '',
                            ' = brute force' if int(row['n']) <= I('bruteMaxN') else '')))
        msgs.append((len(ds) == len(rows), '%d cases' % len(rows)))
        return msgs
    return g


def g_referee():
    d = J('referee.json')
    msgs = [(all(c['equal'] for c in d['compare']) and max(c['n'] for c in d['compare']) == I('refCompareMaxN')
             and len(d['compare']) == sum(n // 4 + 1 for n in range(4, I('refCompareMaxN') + 1, 2)),
             'SAT enumeration of feasible pairs = stage 1, all even n <= %s and all z0' % C('refCompareMaxN'))]
    lit = {(int(r['n']), int(r['g'])): int(r['classes']) for r in CLAIMS['validation'] + CLAIMS['gplus']}
    msgs.append((all(p['classes'] == lit[(p['n'], p['g'])] for p in d['pipeline']) and max(p['n'] for p in d['pipeline']) == I('refPipeMaxN'),
                 'independent SAT pipeline reproduces the class counts for %s'
                 % ', '.join('(%d,%d)' % (p['n'], p['g']) for p in d['pipeline'])))
    msgs.append((all(p['classes'] == lit[(p['n'], p['g'])] for p in d['direct']) and max(p['n'] for p in d['direct']) == I('refDirectMaxN'),
                 'direct SAT enumeration (no relaxation) reproduces them for %s' % ', '.join('(%d,%d)' % (p['n'], p['g']) for p in d['direct'])))
    e = J('encode_check.json')
    msgs.append((e['pairs'] == e['pairs_satisfy_relaxation'] == I('pairsTotal') and all(e['known_sets_satisfy_sat_place'].values()),
                 'encoders accept known positives: all %s survivors satisfy relax_cnf; both known 14-sets satisfy sat_place' % C('pairsTotal')))
    for n in (16, 18):
        cs = J('cert_small_%d.json' % n)
        cs = cs if isinstance(cs, list) else [cs]
        msgs.append((len(cs) == n // 4 + 1 and all(c['all_unsat_verified'] for c in cs),
                     'n = %d: stage-1 DRAT certificate (cubes, drat-trim) for every z0' % n))
    return msgs


def g_records():
    d = J('records.json')
    msgs = [(d['parts_complete'] and d['manifest_parts'] == d['manifest_cand_sha_ok'] == d['manifest_place_sha_ok'] == 7 * 480
             and d['manifest_consumed_all'], 'all 3360 stage-1 parts present; per-part SHA-256 of MANIFEST reproduced')]
    rows = {int(r['z0']): r for r in CLAIMS['n26']}
    for z in range(7):
        r, s1, s2 = rows[z], d['stage1'][str(z)], d['stage2'][str(z)]
        ok = (s1['nodes'], s1['pairs'], rnd(s1['cpu_s'])) == (int(r['nodes']), int(r['pairs']), r['cpu'])
        if r['nodesTwo'] != '--':
            ok = ok and (s2['nodes'], rnd(s2['cpu_s'])) == (int(r['nodesTwo']), r['cpuTwo']) and s1['sets'] == int(r['sets'])
        else:
            ok = ok and s2['pairs'] == 0
        c = d['cert'][str(z)]
        ok = ok and c['present'] and c['base_sha_ok'] and c['cover_ok'] and c['all_reps_unsat_verified'] and \
            (c['cube_reps'], rnd(c['solve_s'] + c['check_s'])) == (int(r['cubes']), r['cpuCert'])
        msgs.append((ok, 'z0 = %d: stage-1 nodes %s, pairs %s, %s s; stage 2 %s nodes, %s s; certificate %s cubes, %s s'
                     % (z, r['nodes'], r['pairs'], r['cpu'], r['nodesTwo'], r['cpuTwo'], r['cubes'], r['cpuCert'])))
    msgs.append((d['survivors'] == d['survivors_distinct'] == I('pairsTotal') and d['survivors_per_z0'] == {'0': 1, '6': I('pairsSix')}
                 and d['survivors_sha256'].startswith(C('survSha')), '%s survivors (1 + %s), SHA-256 %s...' % (C('pairsTotal'), C('pairsSix'), C('survSha'))))
    msgs.append((d['place_done_all_zero'], 'stage 2 (place.c): every survivor searched, no dominating set'))
    msgs.append((d['stage1_v_parts_complete'] and d['stage1_v_orbits_equal'] and d['stage1_v_nodes'] == I('vNodes')
                 and rnd(d['stage1_v_cpu_s']) == C('vCpu'), 'independent stage 1: all parts, same orbits, %s nodes, %s s' % (C('vNodes'), C('vCpu'))))
    s = d['sat_cpu']
    msgs.append((d['sat_records'] == I('pairsTotal') and d['sat_all_unsat_verified'] and d['sat_covers_survivors']
                 and (rnd(s['solve']), rnd(s['check']), rnd(s['mono_solve']), rnd(s['mono_check'])) == (C('satSolve'), C('satCheck'), C('satMonoSolve'), C('satMonoCheck'))
                 and s['max_other_solve'] < I('satOtherMax') and s['max_other_check'] < I('satOtherMax'),
                 'SAT stage 2: %s UNSAT, all DRAT VERIFIED; %s s + %s s; mono pair %s s + %s s; others < %s s'
                 % (C('pairsTotal'), C('satSolve'), C('satCheck'), C('satMonoSolve'), C('satMonoCheck'), C('satOtherMax'))))
    cs = sum(d['cert'][str(z)]['solve_s'] + d['cert'][str(z)]['check_s'] for z in range(7))
    s1 = sum(d['stage1'][str(z)]['cpu_s'] for z in range(7)); s2 = sum(d['stage2'][str(z)]['cpu_s'] for z in range(7))
    msgs.append(((rnd(s1 / 3600, 1), rnd(s2 / 3600, 1), rnd(d['stage1_v_cpu_s'] / 3600, 1), rnd((s['solve'] + s['check']) / 3600, 1), rnd(cs / 3600, 1))
                 == (C('hStageOne'), C('hStageTwo'), C('hStageOneV'), C('hSat'), C('hCert')),
                 'CPU hours: stage 1 %s, stage 2 %s, independent stage 1 %s, SAT stage 2 %s, stage-1 certificate %s'
                 % (C('hStageOne'), C('hStageTwo'), C('hStageOneV'), C('hSat'), C('hCert'))))
    for r in CLAIMS['validationRec']:
        v = d['validation'][r['n']]
        msgs.append((v['complete'] and v['sets'] == 0 and v['pairs'] == int(r['pairs']),
                     'recorded run n = %s, g = n/2: all parts, %s pairs, no dominating set' % (r['n'], r['pairs'])))
    msgs.append((all(d['cert'][str(z)]['solve_s'] + d['cert'][str(z)]['check_s'] < d['stage1'][str(z)]['cpu_s'] for z in range(3, 7)),
                 'for z0 >= 3 the certificate took less CPU time than the stage-1 search'))
    pb = sum(d['cert'][str(z)]['proof_bytes'] for z in range(7))
    msgs.append((rnd(pb / 1e9) == C('certProofGB') and d['cert']['6']['cube_reps'] == I('cubesSix'),
                 'stage-1 DRAT proofs total %s GB; %s cubes for z0 = 6' % (C('certProofGB'), C('cubesSix'))))
    return msgs


def g_sample():
    d = J('n26_sample.json')
    return [(d['stage1_parts'] == d['stage1_parts_reproduced'] == I('sampleParts'), '%s stage-1 parts rerun, outputs identical (SHA-256)' % C('sampleParts')),
            (d['sat_rerun'] == d['sat_reproduced'] == d['sat_expected'] > 0, 'SAT stage 2 rerun on a sample: same CNF hashes, UNSAT, VERIFIED'),
            (d['cert_cubes_rerun'] == d['cert_cubes_reproduced'] > 0, 'stage-1 certificate cubes rerun: same CNF hashes, UNSAT, VERIFIED')]


def g_full():
    d = J('n26_full.json')
    return [(d['stage1_parts'] == d['stage1_parts_reproduced'] == 3360 and d['survivors_sha256_equal'], 'stage 1 + stage 2 rerun: all 3360 parts identical'),
            (d['stage1_v_orbits_equal'] and d['stage1_v_sha256_equal'], 'independent stage 1 rerun: identical output'),
            (d['sat_rerun'] == d['sat_reproduced'] == I('pairsTotal'), 'SAT stage 2 rerun on all survivors'),
            (d['cert_cubes_rerun'] == d['cert_cubes_reproduced'] == 6 * 76 + I('cubesSix'), 'stage-1 certificate rerun on all cubes')]


def g_upper():
    d = J('upper.json')
    return [(d['ok'] and d['kamenetsky26']['queens'] == 14 and d['ow27']['queens'] == 14,
             'Kamenetsky 14-set dominates Q_26; Ostergard-Weakley 14-set dominates Q_27; their independent 14-set dominates Q_26'),
            (d['ok'] and (d['q28']['queens'], d['q29']['queens'], d['weakley30']['queens'], d['q31']['queens']) == (15, 15, 15, 16)
             and all(d[k]['undominated'] == 0 for k in ('q28', 'q29', 'weakley30', 'q31')) and d['weakley30']['monochromatic'],
             'a 15-set dominates Q_28; 15-sets dominate Q_29 and Q_30 (Weakley, monochromatic); a 16-set dominates Q_31')]


def g_records28():
    d = J('records28.json')
    T = 'XXVIII'
    msgs = [(d['parts'] == I('parts' + T) and d['parts_complete'] and d['manifest_parts'] == d['manifest_sha_ok'] == d['manifest_matches_stage1_records'] == I('parts' + T)
             and d['manifest_covers_all_parts'] and d['manifest_consumed_all'],
             'all %s stage-1 parts present; per-part SHA-256 of MANIFEST reproduced and equal to the part records' % C('parts' + T))]
    for r in CLAIMS['n28']:
        z = r['z0']; s1, c = d['stage1'][z], d['cert'][z]
        ok = (s1['nodes'], s1['pairs'], rnd(s1['cpu_s'])) == (int(r['nodes']), int(r['pairs']), r['cpu']) and s1['logs_ok']
        ok = ok and c['header_ok'] and c['base_sha_ok'] and c['cover_ok'] and c['all_reps_unsat_verified'] and \
            (c['cube_reps'], rnd(c['solve_s'] + c['check_s'])) == (int(r['cubes']), r['cpuCert'])
        sz = d['sat_cpu_per_z0'].get(z)
        ok = ok and ((sz is None and r['cpuSat'] == '--' and s1['pairs'] == 0) or (sz is not None and rnd(sz) == r['cpuSat']))
        msgs.append((ok, 'z0 = %s: stage-1 nodes %s, pairs %s, %s s; certificate %s cubes UNSAT + VERIFIED, base CNF rebuilt, %s s; SAT stage 2 %s s'
                     % (z, r['nodes'], r['pairs'], r['cpu'], r['cubes'], r['cpuCert'], r['cpuSat'])))
    msgs.append((d['survivors'] == d['survivors_distinct'] == d['survivors_distinct_orbits'] == I('pairsTotal' + T) and d['survivors_per_stage1']
                 and d['survivors_per_z0'] == {'0': 1, '1': 1, '6': I('pairsSix' + T), '7': I('pairsSeven' + T)}
                 and d['survivors_sha256'].startswith(C('survSha' + T)),
                 '%s survivors in distinct orbits (1 + 1 + %s + %s), SHA-256 %s...' % (C('pairsTotal' + T), C('pairsSix' + T), C('pairsSeven' + T), C('survSha' + T))))
    s = d['sat_cpu']
    msgs.append((d['sat_records'] == I('pairsTotal' + T) and d['sat_all_unsat_verified'] and d['sat_covers_survivors'] and s['mono_pairs'] == 1
                 and (rnd(s['solve']), rnd(s['check']), rnd(s['mono_solve']), rnd(s['mono_check'])) == (C('satSolve' + T), C('satCheck' + T), C('satMonoSolve' + T), C('satMonoCheck' + T))
                 and s['max_other_solve'] < I('satOtherMax' + T) and s['max_other_check'] < I('satOtherMax' + T),
                 'SAT stage 2: %s UNSAT, all DRAT VERIFIED, exactly the survivors; %s s + %s s; z0 = 0 pair %s s + %s s; others < %s s'
                 % (C('pairsTotal' + T), C('satSolve' + T), C('satCheck' + T), C('satMonoSolve' + T), C('satMonoCheck' + T), C('satOtherMax' + T))))
    cs = sum(d['cert'][str(z)]['solve_s'] + d['cert'][str(z)]['check_s'] for z in range(8))
    s1 = sum(d['stage1'][str(z)]['cpu_s'] for z in range(8))
    msgs.append(((rnd(s1 / 3600, 1), rnd((s['solve'] + s['check']) / 3600, 1), rnd(cs / 3600, 1), rnd(d['stage1_v_cpu_s'] / 3600, 1), rnd(d['place_cpu_s'] / 3600, 1))
                 == (C('hStageOne' + T), C('hSat' + T), C('hCert' + T), C('hStageOneV' + T), C('hPlace' + T)),
                 'CPU hours: stage 1 %s, SAT stage 2 %s, stage-1 certificate %s, second stage-1 program %s, place.c %s'
                 % (C('hStageOne' + T), C('hSat' + T), C('hCert' + T), C('hStageOneV' + T), C('hPlace' + T))))
    pb = sum(d['cert'][str(z)]['proof_bytes'] for z in range(8))
    msgs.append((rnd(pb / 1e9) == C('certProofGB' + T) and rnd(d['cert']['7']['max_proof_bytes'] / 1e9, 2) == C('certMaxProofGB' + T)
                 and d['cert']['7']['clauses'] == I('clausesSeven' + T) and all(d['cert'][str(z)]['T'] == (2 if z <= 5 else 3) for z in range(8)),
                 'stage-1 certificate: T = 2 for z0 <= 5, T = 3 for z0 = 6, 7; %s clauses for z0 = 7; proofs %s GB in total, at most %s GB'
                 % (C('clausesSeven' + T), C('certProofGB' + T), C('certMaxProofGB' + T))))
    msgs.append((all(d['cert'][str(z)]['solve_s'] + d['cert'][str(z)]['check_s'] < d['stage1'][str(z)]['cpu_s'] for z in range(3, 8)),
                 'for z0 >= 3 the certificate took less CPU time than the stage-1 search'))
    msgs.append((d['stage1_v_complete_z0'] == [0, 1, 2, 3, 4, 5] and d['stage1_v_orbits_equal_complete'] and d['stage1_v_records_distinct']
                 and d['stage1_v_parts']['6'] == I('vPartsSix' + T) and d['stage1_v_parts']['7'] == 0 and d['stage1_v_orbits_subset_partial']
                 and d['stage1_v_pairs'] == {'0': 1, '1': 1, '6': I('vPairsSix' + T)} and d['stage1_v_nodes'] == I('vNodes' + T) and rnd(d['stage1_v_cpu_s']) == C('vCpu' + T),
                 'second stage-1 program: all parts for z0 <= 5 with the same orbits; %s of 4800 parts for z0 = 6, its %s pairs among those of stage 1; %s nodes, %s s'
                 % (C('vPartsSix' + T), C('vPairsSix' + T), C('vNodes' + T), C('vCpu' + T))))
    msgs.append((d['place_pairs'] == d['place_log_pairs'] == I('placePairs' + T) and d['place_all_zero'] and d['place_covers_z0'] == [1, 6]
                 and d['place_subset_of_survivors'] and rnd(d['place_cpu_s']) == C('placeCpu' + T),
                 'place.c on all %s pairs with z0 = 1, 6: no dominating set; %s s' % (C('placePairs' + T), C('placeCpu' + T))))
    msgs.append((d['cloud_parts'] == I('cloudParts' + T) and d['cloud_ledger_matches'] and d['cloud_calls'] == I('cloudCalls' + T)
                 and len(d['cloud_binary_sha256']) == 1,
                 '%s parts ran in the cloud (%s calls, one binary); ledger and part records agree' % (C('cloudParts' + T), C('cloudCalls' + T))))
    e = J('encode_check28.json')
    msgs.append((e['pairs'] == e['pairs_satisfy_relaxation'] == I('pairsTotal' + T) and e['q28_15_satisfies_sat_place'],
                 'encoders accept known positives: all %s n = 28 survivors satisfy relax_cnf; the 15-set satisfies sat_place for g = 15' % C('pairsTotal' + T)))
    return msgs


def g_resume():
    d = J('resume_test.json')
    return [(d['all_ok'] and len(d) == 9, 'certificate driver resume: refuses a different formula or T (the reported repro), '
             're-solves records with a wrong CNF hash, failed or truncated records, and does not certify a satisfiable formula')]


def g_certify_all():
    d = J('certify_all.json')
    d = d if isinstance(d, list) else [d]
    want = {26: (6 * 76 + I('cubesSix'), I('pairsTotal')), 28: (6 * 76 + 2 * I('cubesSix'), I('pairsTotalXXVIII'))}
    msgs = []
    for r in d:
        c = r.get('compare', {})
        msgs.append((r['certified'] and c.get('all_ok') and (c['cubes'], c['instances']) == want[r['n']],
                     'n = %d: all %d stage-1 cubes and all %d stage-2 formulas rebuilt, UNSAT, VERIFIED, with the recorded CNF hashes'
                     % (r['n'], want[r['n']][0], want[r['n']][1])))
    msgs.append((sorted(r['n'] for r in d) == [26, 28], 'both n replayed'))
    return msgs


def g_tamper():
    d = J('tamper.json')
    return [(d['baseline_pass'], 'an unmodified copy of the tracked files passes'),
            (all(c['failed'] for c in d['cases']) and len(d['cases']) == 10,
             'each of %d altered copies fails: %s' % (len(d['cases']), ', '.join(c['name'] for c in d['cases'])))]


def g_sample28():
    d = J('n28_sample.json')
    return [(d['stage1_parts'] == d['stage1_parts_reproduced'] == I('samplePartsXXVIII'), '%s n = 28 stage-1 parts rerun, outputs identical (SHA-256)' % C('samplePartsXXVIII')),
            (d['sat_rerun'] == d['sat_reproduced'] == d['sat_expected'] == 40, '40 n = 28 SAT stage-2 instances rerun: same CNF hashes, UNSAT, VERIFIED'),
            (d['cert_cubes_rerun'] == d['cert_cubes_reproduced'] == 16, '16 n = 28 certificate cubes (2 per z0) rerun: same CNF hashes, UNSAT, VERIFIED')]


def g_heavy28():
    d = J('n28_heavy.json')
    return [(d['stage1_parts'] == d['stage1_parts_reproduced'] == 5 * 480 + 4800 + 24, 'n = 28 stage 1 rerun: all parts with z0 <= 5 and 24 parts with z0 = 6, 7'),
            (d['sat_rerun'] == d['sat_reproduced'] == d['sat_expected'] == 2000, '2000 n = 28 SAT stage-2 instances rerun'),
            (d['cert_cubes_rerun'] == d['cert_cubes_reproduced'] == 6 * 76 + 1072 + 40, 'n = 28 certificate: all cubes for z0 <= 6 and 40 for z0 = 7 rerun')]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--only', choices=['build', 'small', 'referee', 'records', 'sample', 'records28', 'sample28', 'upper', 'tamper', 'paper'])
    ap.add_argument('--full', action='store_true', help='also rerun the whole n = 26 computation (~15 CPU hours)')
    ap.add_argument('--heavy28', action='store_true', help='also rerun a larger part of the n = 28 computation (~6 CPU hours)')
    ap.add_argument('--certify-all', action='store_true', help='also replay every certificate formula for n = 26, 28 (~45 CPU hours)')
    ap.add_argument('--jobs', type=int, default=3)
    ap.add_argument('--write-pdf', action='store_true', help='copy the reproducible paper build to paper/')
    ap.add_argument('--no-tamper', action='store_true', help=argparse.SUPPRESS)
    a = ap.parse_args()
    global JOBS
    JOBS = a.jobs
    LOGS.mkdir(exist_ok=True)
    want = lambda s: a.only in (None, s)
    tmp = LOGS / 'tmp'
    tmp.mkdir(exist_ok=True)
    steps = []
    if a.only in (None, 'build', 'small', 'referee', 'sample', 'sample28') or a.certify_all:
        cc = ' && '.join('gcc -O2 -o build/%s code/%s.c' % (p, p) for p in ('stage1', 'stage1_v', 'brute_ab', 'place'))
        steps.append(('build', ['sh', '-c', 'mkdir -p build && %s && sh scripts/get_tools.sh' % cc], ROOT, g_build, None))
    if want('small'):
        rows = CLAIMS['validation']
        steps.append(('small', ['sh', '-c', ' ; '.join('%s code/pipeline.py build %s %s --xcheck' % (PY, r['n'], r['g']) for r in rows)],
                      ROOT, g_small('small', rows), 'small.json'))
        rows = [r for r in CLAIMS['gplus'] if r.get('mode') != 'full']
        steps.append(('gplus', ['sh', '-c', ' ; '.join('%s code/pipeline.py build %s %s --xcheck' % (PY, r['n'], r['g']) for r in rows)],
                      ROOT, g_small('gplus', rows), 'gplus.json'))
    if want('referee'):
        steps.append(('encode_check', [PY, 'code/refcheck.py', 'encode_check', 'data/n26/survivors.txt', 'data/kamenetsky26.txt'], ROOT,
                      lambda: [(True, 'ran')], 'encode_check.json'))
        for n in (16, 18):
            g = n // 2
            cmd = ' ; '.join('build/stage1 %d %d %d > %s/s1_%d_%d.cand 2>/dev/null && %s code/cert_stage1.py %d %d %d %s/s1_%d_%d.cand tools/cadical '
                             'tools/drat-trim %s/wd 1 %d %s/cert_%d_%d.jsonl' % (n, g, z, tmp, n, z, PY, n, g, z, tmp, n, z, tmp, JOBS, tmp, n, z)
                             for z in range(g // 2 + 1))
            steps.append(('cert_small_%d' % n, ['sh', '-c', 'rm -f %s/cert_%d_*.jsonl; %s' % (tmp, n, cmd)], ROOT, lambda: [(True, 'ran')],
                          'cert_small_%d.json' % n))
        steps.append(('referee', [PY, 'code/refcheck.py', 'suite', 'build/stage1', C('refCompareMaxN')], ROOT, g_referee, 'referee.json'))
        steps.append(('resume_test', [PY, 'code/test_resume.py', 'tools/cadical', 'tools/drat-trim'], ROOT, g_resume, 'resume_test.json'))
    if want('records'):
        steps.append(('records', [PY, 'code/check_records.py', 'data/n26'], ROOT, g_records, 'records.json'))
    if want('sample'):
        steps.append(('n26_sample', [PY, 'code/run_n26.py', str(ROOT), str(JOBS), str(LOGS / 'n26_sample.json'), 'sample'], ROOT, g_sample, None))
    if want('records28'):
        steps.append(('encode_check28', [PY, 'code/encode_check28.py', 'data/n28/survivors.txt.xz', 'data/q28_15.txt'], ROOT,
                      lambda: [(True, 'ran')], 'encode_check28.json'))
        steps.append(('records28', [PY, 'code/check_records28.py', 'data/n28'], ROOT, g_records28, 'records28.json'))
    if want('sample28'):
        steps.append(('n28_sample', [PY, 'code/run_n28.py', str(ROOT), str(JOBS), str(LOGS / 'n28_sample.json'), 'sample'], ROOT, g_sample28, None))
    if a.heavy28:
        steps.append(('n28_heavy', [PY, 'code/run_n28.py', str(ROOT), str(JOBS), str(LOGS / 'n28_heavy.json'), 'heavy'], ROOT, g_heavy28, None))
    if a.full:
        rows = [r for r in CLAIMS['gplus'] if r.get('mode') == 'full']
        steps.append(('gplus_full', ['sh', '-c', ' ; '.join('%s code/pipeline.py build %s %s --xcheck' % (PY, r['n'], r['g']) for r in rows)],
                      ROOT, g_small('gplus_full', rows), 'gplus_full.json'))
        rows = CLAIMS['validationFull']
        steps.append(('small_full', ['sh', '-c', ' ; '.join('%s code/pipeline.py build %s %s --xcheck' % (PY, r['n'], r['g']) for r in rows)],
                      ROOT, g_small('small_full', rows), 'small_full.json'))
        steps.append(('n26_full', [PY, 'code/run_n26.py', str(ROOT), str(JOBS), str(LOGS / 'n26_full.json'), 'full'], ROOT, g_full, None))
    if a.certify_all:
        steps.append(('certify_all', [PY, 'code/certify_all.py', str(ROOT), str(JOBS), str(BUILD / 'certify'), '26', '28'], ROOT,
                      g_certify_all, 'certify_all.json'))
    if want('upper'):
        steps.append(('upper', [PY, 'code/check_upper.py', 'data/kamenetsky26.txt', 'data/q28_15.txt'], ROOT, g_upper, 'upper.json'))
    if want('tamper') and not a.no_tamper:
        steps.append(('tamper', [PY, 'scripts/tamper.py', str(ROOT)], ROOT, g_tamper, 'tamper.json'))
    bp = BUILD / 'paper'
    if want('paper'):
        cp = ' && '.join('cp paper/%s %s/' % (f, bp) for f in ('queen-domination.tex', 'claims.tex'))
        steps += [('claims_tex', [PY, 'scripts/make_claims_tex.py', '--check'], ROOT,
                   lambda: [(True, 'paper/claims.tex is in sync with claims.json')], None),
                  ('paper', ['sh', '-c', 'rm -rf %s && mkdir -p %s && %s && cd %s && SOURCE_DATE_EPOCH=%s FORCE_SOURCE_DATE=1 '
                             'latexmk -pdf -interaction=nonstopmode -halt-on-error queen-domination.tex' % (bp, bp, cp, bp, C('pdfEpoch'))],
                   ROOT, lambda: [(True, 'latexmk succeeded in build/paper')], None)]
    results = [run(*s) for s in steps]
    if want('paper'):
        log = bp / 'queen-domination.log'
        txt = log.read_text(errors='replace') if log.exists() else 'missing log: There were undefined'
        bad = re.findall(r'(LaTeX Warning|Package \w+ Warning|Overfull \\[hv]box|Underfull \\[hv]box|There were undefined)', txt)
        m = re.search(r'Output written on queen-domination.pdf \((\d+) pages', txt)
        results.append({'name': 'paper_log_clean', 'ok': not bad and bool(m) and m.group(1) == C('pages'), 'issues': len(bad),
                        'pages': m.group(1) if m else None})
        print('%-22s %s' % ('paper_log_clean', 'PASS' if results[-1]['ok'] else 'FAIL (%d issues, %s pages)' % (len(bad), m and m.group(1))))
        built = bp / 'queen-domination.pdf'
        if a.write_pdf and built.exists():
            shutil.copy2(built, ROOT / 'paper' / 'queen-domination.pdf')
        same = built.exists() and sha(built) == sha(ROOT / 'paper' / 'queen-domination.pdf')
        results.append({'name': 'paper_reproducible', 'ok': same})
        print('%-22s %s' % ('paper_reproducible', 'PASS' if same else 'FAIL (build differs from paper/queen-domination.pdf)'))
    inputs = sorted(p for p in ROOT.rglob('*') if p.is_file() and (p.suffix in {'.py', '.c', '.sh', '.tex', '.md', '.txt', '.cff', '.json', '.jsonl', '.xz', '.tsv'} or p.name == 'MANIFEST')
                    and not ({'.git', '.venv', 'verification', 'tools', 'build', '__pycache__'} & set(p.relative_to(ROOT).parts)))
    import pysat
    cad = subprocess.run([str(ROOT / 'tools' / 'cadical'), '--version'], capture_output=True, text=True).stdout.strip() \
        if (ROOT / 'tools' / 'cadical').exists() else None
    summary = {'time_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), 'only': a.only, 'full': a.full, 'heavy28': a.heavy28,
               'certify_all': a.certify_all, 'jobs': JOBS,
               'python': sys.version.split()[0], 'python-sat': pysat.__version__, 'cadical': cad,
               'gcc': subprocess.run(['gcc', '--version'], capture_output=True, text=True).stdout.splitlines()[0],
               'results': results, 'inputs_sha256': {str(p.relative_to(ROOT)): sha(p) for p in inputs}}
    pdf = ROOT / 'paper' / 'queen-domination.pdf'
    if pdf.exists():
        summary['pdf_sha256'] = sha(pdf)
    allok = all(r['ok'] for r in results)
    summary['overall'] = 'PASS' if allok else 'FAIL'
    name = ('summary.json' if a.only is None and not (a.full or a.heavy28 or a.certify_all) else 'summary-full.json' if a.only is None else 'summary-partial.json')
    (LOGS / name).write_text(json.dumps(summary, indent=1) + '\n')
    print('OVERALL', summary['overall'])
    return 0 if allok else 1


if __name__ == '__main__':
    raise SystemExit(main())
