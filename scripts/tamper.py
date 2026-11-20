#!/usr/bin/env python3
"""Tamper test: altered copies of the tracked files must fail verification.

For each case, the tracked files (git ls-files) are copied to a temporary directory, one record is
altered, and `scripts/verify.py --only STEP` is run on the copy; the case passes if that run FAILS.  An
unaltered copy must pass the same steps.  usage: tamper.py ROOT   -- prints JSON."""
import json, lzma, re, shutil, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve()
FILES = subprocess.run(['git', 'ls-files'], cwd=ROOT, capture_output=True, text=True, check=True).stdout.split()


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
]


def copy(td):
    d = Path(td) / 'r'
    for f in FILES:
        (d / f).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / f, d / f)
    return d


def verify(d, step):
    r = subprocess.run([sys.executable, 'scripts/verify.py', '--only', step, '--no-tamper'], cwd=d, capture_output=True, text=True)
    return r.returncode == 0 and 'OVERALL PASS' in r.stdout


def main():
    out = {'cases': []}
    with tempfile.TemporaryDirectory() as td:
        d = copy(td)
        out['baseline_pass'] = all(verify(d, s) for s in ('records', 'records28', 'upper'))
    for name, step, fn in CASES:
        with tempfile.TemporaryDirectory() as td:
            d = copy(td)
            fn(d)
            out['cases'].append({'name': name, 'step': step, 'failed': not verify(d, step)})
    print(json.dumps(out))


if __name__ == '__main__':
    main()
