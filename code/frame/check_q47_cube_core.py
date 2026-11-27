"""Replay a plain Q47 cube core and verify exactly where its proof applies.

Usage: python code/frame/check_q47_cube_core.py DIRECTORY
DIRECTORY contains info.json (case, root_sha256, mask), core.cnf and core.drat.
The checker uses the baseline root with the same variable numbering throughout.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import q47_batch
from run_hard import layer_vars


def clauses(data):
    """Parse the one-clause-per-line DIMACS produced by our encoder and drat-trim."""
    lines = iter(line.strip() for line in data.splitlines() if line.strip() and not line.lstrip().startswith(b'c'))
    p, cnf, variables, count = next(lines).split()
    if (p, cnf) != (b'p', b'cnf'):
        raise ValueError('invalid DIMACS header')
    variables = int(variables)
    found = 0
    for line in lines:
        values = list(map(int, line.split()))
        if values.pop() != 0 or any(v == 0 or abs(v) > variables for v in values):
            raise ValueError('invalid DIMACS clause')
        found += 1
        yield tuple(sorted(values))
    if found != int(count):
        raise ValueError('incorrect clause count')


def replay(directory):
    record = json.loads((directory/'info.json').read_text())
    case, mask = tuple(record['case']), record['mask']
    if len(mask) % 4 or set(mask) - set('01*'):
        raise ValueError('invalid cube mask')
    base, root = q47_batch.build(case)
    if hashlib.sha256(root).hexdigest() != record['root_sha256']:
        raise ValueError('baseline root hash mismatch')
    required = set(clauses((directory/'core.cnf').read_bytes()))
    for clause in clauses(root):
        required.discard(clause)
    for i in range(0, len(mask), 4):
        layer = layer_vars(base, case, i//4+1)
        if layer is None:
            raise ValueError('mask extends past the available frame layers')
        for bit, v in zip(mask[i:i+4], layer, strict=True):
            if bit != '*':
                required.discard((v if bit == '1' else -v,))
    if required:
        raise ValueError('core contains clauses outside the root and masked units')
    checker = Path(__file__).resolve().parents[2]/'tools/drat-trim'
    result = subprocess.run([checker,directory/'core.cnf',directory/'core.drat','-w'],
                            capture_output=True, check=True)
    if b's VERIFIED' not in result.stdout.splitlines():
        raise ValueError('core refutation did not verify')
    return mask


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    print('VERIFIED', replay(parser.parse_args().directory))
