#!/usr/bin/env python3
"""Checks of the committed records of the independent n = 35 cross-check (data/xcheck35/) for scripts/verify.py.

  check_xcheck.py DATA FRAME_DATA

* case list: cases.case_list(35, 18) (written without geom.py) equals geom.cases_by_frame(35, 18);
* negative controls k = (n-1)/2, odd n = 5..35 (ctl/km_*): every case refuted (xcover.py), except n = 11 (one
  satisfiable case: the known 5-set); complete runs (13, 7) and (15, 8) (ctl/all_*): for (13, 7) the satisfiable
  cases are exactly those of the main pipeline's complete run (FRAME_DATA/validation/o_13_7.jsonl.xz), each with
  a model checked to dominate and to have its case; (15, 8) is refuted completely;
* differential tests on the zero-deficit cases (ctl/diff_z0_*): verdicts of enc.py + CaDiCaL 1.9.5 and of
  encoding X + kissat agree on every case;
* the 585 hard cases (x_hard_35_18.jsonl.xz) and the stratified sample (x_sample_35_18.jsonl.xz): number of
  cases refuted by complete cube trees (xcover.py), SAT records.  While the run is in progress these files are
  absent or partial.
Prints JSON."""
import json, lzma, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(1, os.path.join(os.path.dirname(HERE), 'frame'))
import cases as CS


def recs(p):
    return [json.loads(l) for l in lzma.open(p, 'rt') if l.strip()] if os.path.exists(p) else None


def xcover(n, k, cases, records):
    r = subprocess.run([sys.executable, os.path.join(HERE, 'xcover.py'), str(n), str(k), cases, records],
                       capture_output=True, text=True)
    return json.loads(r.stdout.splitlines()[0])


def main():
    data, fdata = sys.argv[1], sys.argv[2]
    import geom
    out = {'case_list_35_18': len(CS.case_list(35, 18)),
           'case_list_equal_geom': sorted(CS.case_list(35, 18)) == sorted(geom.cases_by_frame(35, 18))}
    km = {}
    for n in range(5, 36, 2):
        k = (n - 1) // 2
        c = xcover(n, k, os.path.join(data, 'ctl', 'km_%d_%d.jsonl.xz' % (n, k)), os.path.join(data, 'ctl', 'x_km_%d_%d.jsonl.xz' % (n, k)))
        sat = [r for r in recs(os.path.join(data, 'ctl', 'x_km_%d_%d.jsonl.xz' % (n, k))) if r['result'] == 'SAT']
        km[n] = {'cases': c['cases'], 'refuted': c['refuted'], 'sat_cases': len({tuple(r['case']) for r in sat}),
                 'sat_models_checked': all(r.get('dominating') and r.get('n_queens') == k and r.get('case_of_set') == r['case'] for r in sat)}
    out['km'] = km
    for n, k in ((13, 7), (15, 8)):
        c = xcover(n, k, os.path.join(data, 'ctl', 'all_%d_%d.jsonl.xz' % (n, k)), os.path.join(data, 'ctl', 'x_all_%d_%d.jsonl.xz' % (n, k)))
        sat = [r for r in recs(os.path.join(data, 'ctl', 'x_all_%d_%d.jsonl.xz' % (n, k))) if r['result'] == 'SAT']
        d = {'cases': c['cases'], 'refuted': c['refuted'], 'sat_cases': len({tuple(r['case']) for r in sat}),
             'sat_models_checked': all(r.get('dominating') and r.get('n_queens') == k and r.get('case_of_set') == r['case'] for r in sat)}
        main_run = recs(os.path.join(fdata, 'validation', 'o_%d_%d.jsonl.xz' % (n, k)))
        if main_run is not None:
            d['sat_cases_equal_main_run'] = {tuple(r['case']) for r in sat} == {tuple(r['case']) for r in main_run if r.get('result') == 'SAT'}
            d['main_run_cases'] = sum(1 for r in main_run if 'case' in r)
        out['all_%d_%d' % (n, k)] = d
    diff = {}
    for n, k in ((13, 7), (15, 8), (17, 9), (19, 10)):
        R = recs(os.path.join(data, 'ctl', 'diff_z0_%d_%d.jsonl.xz' % (n, k)))
        C = recs(os.path.join(data, 'ctl', 'z0_%d_%d.jsonl.xz' % (n, k)))
        diff['%d_%d' % (n, k)] = {'cases': len(C), 'records': len(R), 'agree': sum(r['A'] == r['X'] and r['A'] in ('SAT', 'UNSAT') for r in R),
                                  'same_cases': sorted(tuple(r['case']) for r in R) == sorted(tuple(r['case']) for r in C),
                                  'sat_cases': sum(r['A'] == 'SAT' for r in R),
                                  'models_ok': all(r.get('A_ok', True) and r.get('X_ok', True) for r in R)}
    out['diff_z0'] = diff
    for name in ('hard', 'sample'):
        cf, rf = os.path.join(data, '%s_cases_35_18.jsonl.xz' % name), os.path.join(data, 'x_%s_35_18.jsonl.xz' % name)
        if os.path.exists(cf) and os.path.exists(rf):
            c = xcover(35, 18, cf, rf)
            out[name] = {k: c[k] for k in ('cases', 'refuted', 'not_refuted', 'split_cases', 'unsat_leaves', 'SAT_records', 'cpu_s_in_trees',
                                           'cases_not_in_independent_list')}
        else:
            out[name] = {'present': False}
    print(json.dumps(out))


if __name__ == '__main__':
    main()
