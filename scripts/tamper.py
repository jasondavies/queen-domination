#!/usr/bin/env python3
"""Tamper test: altered copies of the tracked files must fail verification.

For each case (15 in all), the committed tree (git archive HEAD, so uncommitted edits never change what is tested)
is extracted to a temporary directory, one record is altered, and `scripts/verify.py --only STEP` is run
on the copy; the case passes if that run FAILS.  An unaltered copy must pass the same steps.
usage: tamper.py ROOT   -- prints JSON (including the commit tested and whether the working tree is dirty)."""
import json, lzma, re, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve()
HEAD = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture_output=True, text=True, check=True).stdout.strip()
DIRTY = bool(subprocess.run(['git', 'status', '--porcelain'], cwd=ROOT, capture_output=True, text=True, check=True).stdout.strip())


def xz_edit(p, fn):
    s = lzma.decompress(p.read_bytes()).decode().splitlines(True)
    p.write_bytes(lzma.compress(''.join(fn(s)).encode()))


def txt_edit(p, fn):
    p.write_text(''.join(fn(p.read_text().splitlines(True))))


def flip_first7(L):
    i = next(k for k, x in enumerate(L) if x.endswith(' 7\n'))
    f = L[i].split(); f[1] = format(int(f[1], 16) ^ 3, 'x'); L[i] = ' '.join(f) + '\n'
    return L


def alter_base(L):
    L[0] = re.sub(r'"base_sha256": "(.)', lambda m: '"base_sha256": "' + ('0' if m.group(1) != '0' else '1'), L[0])
    return L


def first_unsat_to_sat(L):
    i = next(k for k, x in enumerate(L) if '"result": "UNSAT"' in x)
    L[i] = L[i].replace('"result": "UNSAT"', '"result": "SAT"')
    return L


def drop_split_cube(L):
    i = next(k for k, x in enumerate(L) if re.search(r'"cube": "[01]{4}"', x) and '"result": "UNSAT"' in x)
    return L[:i] + L[i + 1:]


def json_drop_queen(L):
    d = json.loads(''.join(L))
    d['set_col_row'] = d['set_col_row'][1:]
    return [json.dumps(d)]


def drop_queen(L):
    i = next(k for k, x in enumerate(L) if 'Q' in x)
    L[i] = L[i].replace('Q', '.', 1)
    return L


CASES = [
    ('n28 survivor altered', 'records28', lambda d: xz_edit(d / 'data/n28/survivors.txt.xz', flip_first7)),
    ('n28 survivor deleted', 'records28', lambda d: xz_edit(d / 'data/n28/survivors.txt.xz', lambda L: L[:-1])),
    ('n28 certificate cube marked SAT', 'records28', lambda d: txt_edit(d / 'data/n28/cert_stage1_z7.jsonl',
                                                                         lambda L: L[:4] + [L[4].replace('"UNSAT"', '"SAT"')] + L[5:])),
    ('n28 certificate cube dropped', 'records28', lambda d: txt_edit(d / 'data/n28/cert_stage1_z6.jsonl', lambda L: L[:6] + L[7:])),
    ('n28 SAT record not verified', 'records28', lambda d: xz_edit(d / 'data/n28/sat_stage2.txt.xz',
                                                                    lambda L: [L[0].replace('drat=VERIFIED', 'drat=FAILED')] + L[1:])),
    ('n28 claim altered', 'records28', lambda d: txt_edit(d / 'claims.json', lambda L: [re.sub(r'"pairsSevenXXVIII": "118662"',
                                                                                            '"pairsSevenXXVIII": "118661"', l) for l in L])),
    ('n28 stage-1 part record dropped', 'records28', lambda d: xz_edit(d / 'data/n28/stage1_parts.txt.xz', lambda L: L[:10000] + L[10001:])),
    ('Q28 15-set with a queen removed', 'upper', lambda d: txt_edit(d / 'data/q28_15.txt', drop_queen)),
    ('n26 survivor altered', 'records', lambda d: txt_edit(d / 'data/n26/survivors.txt', lambda L: L[:5] + [L[5].replace(' 6\n', ' 5\n')] + L[6:])),
    ('n26 certificate base hash altered', 'records', lambda d: txt_edit(d / 'data/n26/cert_stage1_z6.jsonl', alter_base)),
    ('n35 frame record marked SAT', 'frame', lambda d: xz_edit(d / 'data/frame/d_35_18.jsonl.xz', first_unsat_to_sat)),
    ('n35 cube of a split case dropped', 'frame', lambda d: xz_edit(d / 'data/frame/h_35_18.jsonl.xz', drop_split_cube)),
    ('n32 frame record dropped', 'frame', lambda d: xz_edit(d / 'data/frame/d_32_16.jsonl.xz', lambda L: L[:100] + L[101:])),
    ('Q35 19-set with a queen removed', 'upper', lambda d: txt_edit(d / 'data/frame/q35_19.json', json_drop_queen)),
    ('n28 replay cube marked SAT', 'replay', lambda d: txt_edit(d / 'data/replay/n28/cert_stage1_z7.jsonl',
                                                              lambda L: L[:3] + [L[3].replace('"UNSAT"', '"SAT"')] + L[4:])),
]


def copy(td):
    d = Path(td) / 'r'
    d.mkdir()
    arc = subprocess.run(['git', 'archive', '--format=tar', HEAD], cwd=ROOT, capture_output=True, check=True).stdout
    subprocess.run(['tar', '-x', '-C', str(d)], input=arc, check=True)
    return d


def verify(d, step):
    r = subprocess.run([sys.executable, 'scripts/verify.py', '--only', step, '--no-tamper'], cwd=d, capture_output=True, text=True)
    return r.returncode == 0 and 'OVERALL PASS' in r.stdout


def main():
    out = {'commit': HEAD, 'working_tree_dirty': DIRTY, 'cases': []}
    with tempfile.TemporaryDirectory() as td:
        d = copy(td)
        out['baseline_pass'] = all(verify(d, s) for s in ('records', 'records28', 'upper', 'frame', 'replay'))
    for name, step, fn in CASES:
        with tempfile.TemporaryDirectory() as td:
            d = copy(td)
            fn(d)
            out['cases'].append({'name': name, 'step': step, 'failed': not verify(d, step)})
    print(json.dumps(out))


if __name__ == '__main__':
    main()
