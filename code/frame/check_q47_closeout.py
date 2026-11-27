"""Reconcile the Q47 run ledgers, replay terminal certificates, and check the upper bound.

Requires the original build/q47-closeout working ledgers and archived branches.
The initial batch records DRAT checks at solve time. This audit consumes those
receipts; it does not rerun all historical SAT solvers or DRAT checks.
Prints JSON only after all checks have passed.
"""
from collections import Counter
from contextlib import redirect_stdout
from hashlib import sha256
from io import StringIO
from pathlib import Path
import json
import runpy
import sys

from geom import dominated
from odd_margin_bounds import cases, excluded

ROOT=Path(__file__).resolve().parents[2]

def check():
    build=ROOT/'build'
    final=build/'q47-closeout'
    with redirect_stdout(StringIO()):
        ledger=runpy.run_path(str(final/'progress.py'))
    generated=set(cases(47))
    expected={case for case in generated if not excluded(47,case)}
    assert expected==set(ledger['base'])==ledger['closed'] and not ledger['res']['witness']
    assert len(expected)==98114
    # Compare recorded solver/encoder sources to the binary and source files in this checkout.
    for name,wanted in json.loads((build/'q47-frame-modal/source-hashes.json').read_text()).items():
        file=ROOT/('code/frame' if name.endswith('.py') else 'tools')/name
        assert sha256(file.read_bytes()).hexdigest()==wanted
    data=ROOT/'data/frame'
    receipts=[json.loads(f.read_text()) for f in sorted((data/'q47_terminal_moments').glob('*.receipt.json'))]
    assert len({r['cube_sha256'] for r in receipts})==len(receipts)==15
    targets={tuple(r['case']) for r in receipts}
    assert len(targets)==13
    for r in receipts:
        c=tuple(r['case'])
        assert r['root_sha256']==ledger['base'][c]['cnf_sha256'] and r['cube'] in ledger['night_pieces'][c]
    assert all(ledger['whole'](ledger['night_pieces'][c]) for c in targets)
    seed=json.loads((data/'q47_24_one_hole.json').read_text())
    queens=list(map(tuple,seed['set_col_row']))
    assert len(queens)==len(set(queens))==24 and all(0<=x<47 and 0<=y<47 for x,y in queens)
    holes=[(x,y) for x in range(47) for y in range(47)
           if all(x!=a and y!=b and abs(x-a)!=abs(y-b) for a,b in queens)]
    assert holes==[(7,46)] and dominated(47,queens+holes)
    return dict(board=47,queens_excluded=24,canonical_cases=len(generated),
                geometrically_excluded=len(generated)-len(expected),remaining_case_roots=len(expected),
                roots_closed=len(ledger['closed']),roots_open=0,terminal_frames=len(targets),
                terminal_receipts=len(receipts),terminal_types=dict(Counter(r['kind'] for r in receipts)),
                upper_bound_set_col_row=queens+holes,domination_number=25)

if __name__=='__main__':
    if not __debug__:raise RuntimeError('Run without -O so all verification assertions are enabled')
    print(json.dumps(check(),indent=2))
