"""A shared exclusion for 24 queens occupying the 24 even rows and 23 odd
columns of Q47 (or their transpose). Coordinates start at zero. The proof
also allows repeated diagonals and any choice of the doubled odd column.
"""
from functools import lru_cache
from hashlib import sha256
from itertools import combinations_with_replacement, product
from pathlib import Path
import json
import os
import subprocess
from tempfile import NamedTemporaryFile


def forces_profile(case, cube, n=47):
    """Sufficient condition from the actual frame and occupied cube lines."""
    left, right, bottom, top, dr, dc, _, _ = case
    if n % 4 != 3 or (dr, dc) not in ((0, 1), (1, 0)):
        return False
    a, b, c, d = left, n - 1 - right, bottom, n - 1 - top
    if (len(cube) % 4 or set(cube) - {'0', '1'} or
            not (0 <= a < b < n and 0 <= c < d < n) or
            2 * (len(cube) // 4) >= min(b-a, d-c)):
        raise ValueError('invalid frame or cube')
    rows = set(range(c)) | set(range(d + 1, n))
    cols = set(range(a)) | set(range(b + 1, n))
    for i in range(len(cube) // 4):
        j = i + 1
        for bit, axis, line in zip(cube[4*i:4*j], (rows, rows, cols, cols),
                                   (c+j, d-j, a+j, b-j)):
            if bit == '1':
                axis.add(line)
    if dr == 1:
        rows, cols = cols, rows
    k = (n+1)//2
    r = sum(y % 2 == 0 for y in rows)
    s = sum(x % 2 == 1 for x in cols)
    # Every even-colour queen is either outside the even rows or outside
    # the odd columns. Each of the r and s occupied lines needs a queen.
    minority = (k-r) + (k-s)
    # An empty even row needs at least 1+s empty even columns covered
    # diagonally. An empty odd column needs at least r-1 empty odd rows.
    # A queen of that colour can cover at most two on one line. Once one
    # entire axis is forced, tighten the bound on the other axis.
    if r == k or 1+s > 2*minority:
        r = k
    if s == k-1 or r-1 > 2*((k-r)+(k-s)):
        s = k-1
    if s == k-1:
        # All k-1 occupied columns are odd, so even-colour queens can
        # only be on odd rows.
        return r == k or 1+s > 2*(k-r)
    return False


def moment_formula(n=47):
    """Encode necessary conditions for the mixed-parity profile.

    Write D=y-x and S=x+y-(n-1). Each needy (even,odd) square requires
    its D or S to occur. Within each D residue mod 4 the neighbourhoods
    of target S values are nested. Before the first missing D in that
    order all D values are required; at the first miss all neighbouring
    S values are required. The no-miss option is included on each side.

    For a choice of those two prefixes, complete the required multisets
    to k diagonal entries, repetitions allowed. The same queen has
    D=S mod 4. There is one queen per even row and one per odd column
    plus a duplicate in column x*. Thus sum(D)=centre-x*, sum(S)=-sum(D)
    and sum(D²+S²)=2 sum_over_queens((x-centre)²+(y-centre)²).
    A real placement must give both multisets the same moment key below.
    """
    if n < 3 or n % 4 != 3:
        raise ValueError('expected n = 3 mod 4')
    centre = (n-1)//2
    k = centre+1
    evens, odds = range(0, n, 2), range(1, n, 2)
    values = range(2-n, n-1, 2)
    neighbours = {v: set() for v in values}
    for x, y in product(evens, odds):
        neighbours[y-x].add(x+y-2*centre)
    orders = [sorted((v for v in values if v%4 == residue),
                     key=lambda v: -len(neighbours[v])) for residue in (1, 3)]
    for order in orders:
        if any(not neighbours[b] <= neighbours[a] for a, b in zip(order, order[1:])):
            raise ValueError('target neighbourhoods are not nested')
    fixed_squares = sum((i-centre)**2 for i in range(n))
    clauses, selectors = [], []
    top = 0
    for lengths in product(*(range(len(order)+1) for order in orders)):
        diff, sums = [], set()
        for order, length in zip(orders, lengths):
            diff.extend(order[:length])
            if length < len(order):
                sums.update(neighbours[order[length]])
        if len(diff) > k or len(sums) > k:
            continue
        top += 1
        selector = top
        selectors.append(selector)
        keys = set()
        for extra in combinations_with_replacement(values, k-len(diff)):
            entries = (*diff, *extra)
            total = sum(entries)
            if centre-total in odds:
                keys.add((-total, 2*(fixed_squares+total**2)-sum(i*i for i in entries),
                          sum(i%4 == 1 for i in entries)))
        sum_keys = set()
        for extra in combinations_with_replacement(values, k-len(sums)):
            entries = (*sums, *extra)
            sum_keys.add((sum(entries), sum(i*i for i in entries), sum(i%4 == 1 for i in entries)))
        choices = []
        for key in sorted(keys):
            top += 1
            choices.append(top)
            if key not in sum_keys:
                clauses.append([-selector, -top])
        clauses.append([-selector, *choices])
    clauses.append(selectors)
    dimacs = f'p cnf {top} {len(clauses)}\n' + ''.join(
        ' '.join(map(str, row)) + ' 0\n' for row in clauses)
    return dimacs.encode(), selectors


RULE = 'q47-even-rows-odd-columns-v1'
ROOT = Path(__file__).resolve().parents[2]


@lru_cache(maxsize=1)
def bundle():
    formula, selectors = moment_formula()
    # RUP-check each impossible choice of prefixes, then the disjunction.
    proof = (''.join(f'-{s} 0\n' for s in selectors) + '0\n').encode()
    return formula, proof, sha256(formula).hexdigest(), sha256(proof).hexdigest()


def check_bundle(store):
    _, _, cnf_hash, proof_hash = bundle()
    paths = (store/(cnf_hash+'.cnf'), store/(proof_hash+'.drat'))
    stats = [p.stat() for p in paths]
    versions = tuple((s.st_dev, s.st_ino, s.st_size, s.st_ctime_ns) for s in stats)
    return _verified_bundle(store, versions)


@lru_cache(maxsize=4)
def _verified_bundle(store, versions):
    formula, proof, cnf_hash, proof_hash = bundle()
    cnf = store/(cnf_hash+'.cnf')
    archive = store/(proof_hash+'.drat')
    if cnf.read_bytes() != formula or archive.read_bytes() != proof:
        raise ValueError('orthodox certificate hash mismatch')
    checked = subprocess.run([ROOT/'tools/drat-trim', cnf, archive, '-w'],
                             capture_output=True, check=True)
    if b's VERIFIED' not in checked.stdout.splitlines():
        raise ValueError('orthodox moment certificate failed verification')
    return dict(rule=RULE, cnf_sha256=cnf_hash, proof_sha256=proof_hash,
                archive_file=archive.name, archive_bytes=len(proof), proof_bytes=len(proof))


def install(store):
    formula, proof, cnf_hash, proof_hash = bundle()
    for name, data in ((cnf_hash+'.cnf', formula), (proof_hash+'.drat', proof)):
        with NamedTemporaryFile(dir=store) as f:
            f.write(data)
            f.flush()
            try:
                os.link(f.name, store/name)
            except FileExistsError:
                pass
    return check_bundle(store)


@lru_cache(maxsize=2)
def _root(case):
    import q47_batch
    base, data = q47_batch.build(case)
    return base, data, sha256(data).hexdigest()


def receipt(case, cube, expected_root, store):
    from run_hard import layer_vars
    if not forces_profile(case, cube):
        raise ValueError('branch does not force the certified profile')
    base, data, root_hash = _root(case)
    if expected_root != root_hash:
        raise ValueError('orthodox parent hash mismatch')
    head, body = data.split(b'\n', 1)
    _, _, top, count = head.split()
    variables = [v for level in range(1, len(cube)//4+1) for v in layer_vars(base, case, level)]
    units = ''.join(f'{v if bit=="1" else -v} 0\n' for bit,v in zip(cube, variables)).encode()
    plain = b'p cnf '+top+b' '+str(int(count)+len(cube)).encode()+b'\n'+body+units
    return dict(check_bundle(store), baseline_cnf_sha256=sha256(plain).hexdigest(),
                parent_sha256=root_hash, kind='orthodox-profile', case=list(case), cube=cube,
                result='UNSAT', drat='VERIFIED')


def check_record(row, root_hash, store):
    expected = receipt(tuple(row['case']), row['cube'], root_hash, store)
    if any(row.get(k) != v for k,v in expected.items()):
        raise ValueError('orthodox receipt differs from reconstructed branch or certificate')


def save_branch(case, cube, root_hash, out):
    row = receipt(case, cube, root_hash, out/'proofs')
    folder = out/'orthodox'
    folder.mkdir(exist_ok=True)
    target = folder/(row['baseline_cnf_sha256']+'.json')
    with NamedTemporaryFile(dir=folder, mode='w') as f:
        json.dump(row, f, sort_keys=True)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())
        try:
            os.link(f.name, target)
        except FileExistsError:
            if json.loads(target.read_text()) != row:
                raise ValueError('conflicting orthodox branch receipt')
    return row


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description='Replay a Q47 orthodox branch receipt')
    parser.add_argument('receipt', type=Path)
    args = parser.parse_args()
    row = json.loads(args.receipt.read_text())
    check_record(row, row['parent_sha256'], args.receipt.resolve().parents[1]/'proofs')
    print('VERIFIED', row['baseline_cnf_sha256'], 'using shared formula', row['cnf_sha256'])
