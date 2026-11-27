"""Moment certificates for two terminal Q47 cubes with same-parity occupied axes.

A queen on (p+2i,p+2j) has D=(x-y)/2=i-j and S=(x+y-46)/2=i+j-Q,
where Q=23-p. Every target (empty row and empty column) requires its D or S.
Each of the two frames has 23 distinct diagonals of each kind for 24 queens:
the diagonal multiset is its support plus one duplicate.

For p=0 both i and j are permutations of 0..23. The D and S sums vanish.
For p=1 each axis contains 0..22 once plus one duplicate, at I and J.
The D and S sums are I-J and I+J-Q. In either case summing
D²+S²=2[(i-Q/2)²+(j-Q/2)²] shows

  (sum D² - (sum D)²) + (sum S² - (sum S)²) = sum_{i=0}^Q (2i-Q)².

For p=1 the two squared sums cancel exactly the contributions from I and J.
For each queen S-D has parity Q, constraining the two odd-entry counts.

For each parity of target D choose the smallest missing D magnitude, or the
next magnitude beyond the target range if none is missing. The target S
neighbourhoods for +D and -D of the same magnitude coincide (checked below).
Thus smaller D values are compulsory and so are the neighbours at the first
missing magnitude. Enumerate every completion of each compulsory set to 23
distinct values, then duplicate each possible member. The CNF requires a
pair of compatible moment/odd-count choices for one pair of magnitudes.
Every dominating placement on the input cube supplies such an assignment.
"""
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, product

import q47_batch
from run_hard import layer_vars

CASES = {(1,1,1,1,0,0,1,1): 0, (0,0,0,0,1,1,1,1): 1}


def occupied_axes(case, bits, root_hash, cube_hash):
    base, root = q47_batch.build(case)
    if sha256(root).hexdigest() != root_hash:
        raise ValueError('frame root hash mismatch')
    if len(bits)%4 or set(bits)-{'0','1'}:
        raise ValueError('invalid layer bits')
    ml,mr,mb,mt,dr,dc,dt,ds = case
    def lines(lo,hi):
        known = {i:True for i in range(47) if i<lo or i>hi}
        known.update({lo:False,hi:False})
        return known
    rows,cols = lines(mb,46-mt),lines(ml,46-mr)
    units = []
    for j in range(1,len(bits)//4+1):
        variables = layer_vars(base,case,j)
        lines_at_layer = [(rows,mb+j,base.oR),(rows,46-mt-j,base.oR),
                          (cols,ml+j,base.oC),(cols,46-mr-j,base.oC)]
        if variables != [axis[i] for _,i,axis in lines_at_layer]:
            raise ValueError('unexpected layer encoding')
        for v,(known,i,_),bit in zip(variables,lines_at_layer,bits[4*j-4:4*j]):
            if i in known:raise ValueError('overlapping layers')
            known[i] = bit=='1'
            units.append(v if bit=='1' else -v)
    head,body = root.split(b'\n',1)
    prefix,count = head.rsplit(b' ',1)
    formula = prefix+b' '+str(int(count)+len(units)).encode()+b'\n'+body
    formula += ''.join(f'{v} 0\n' for v in units).encode()
    if sha256(formula).hexdigest()!=cube_hash:raise ValueError('cube hash mismatch')
    for known,deficit in ((rows,dr),(cols,dc)):
        centre, = set(range(47))-known.keys()
        final = 24-deficit-sum(known.values())
        if final not in (0,1):raise ValueError('inconsistent line count')
        known[centre] = bool(final)
    return tuple(frozenset(i for i,v in known.items() if v) for known in (rows,cols))


def forced_axes(case, bits, root_hash, cube_hash):
    rows,cols=occupied_axes(case,bits,root_hash,cube_hash)
    parity=CASES[case]
    if rows!=cols or rows!=set(range(parity,47,2)) or case[6:]!=(1,1):
        raise ValueError('cube does not force the required parity and deficits')
    return parity


@lru_cache(maxsize=256)
def _keys(required, extent):
    domain = set(range(-extent,extent+1))
    if len(required)>23 or not required<=domain:return ()
    result=set()
    for extra in combinations(sorted(domain-required),23-len(required)):
        support=required.union(extra)
        total=sum(support)
        squares=sum(v*v for v in support)
        odds=sum(v%2 for v in support)
        for duplicate in support:
            s=total+duplicate
            if extent==23 and s:continue
            result.add((squares+duplicate*duplicate-s*s,odds+duplicate%2))
    return tuple(sorted(result))


@lru_cache(maxsize=2)
def projection(parity):
    if parity not in (0,1):raise ValueError('invalid queen parity')
    extent=23-parity
    constant=sum((2*i-extent)**2 for i in range(extent+1))
    target_axis=range(1-parity,47,2)
    neighbours={}
    for x,y in product(target_axis,repeat=2):
        neighbours.setdefault((x-y)//2,set()).add((x+y-46)//2)
    assert all(neighbours[d]==neighbours[-d] for d in neighbours)
    def options(p):
        magnitudes=sorted({abs(d) for d in neighbours if d%2==p})
        return [*magnitudes,magnitudes[-1]+2]
    clauses=[];selectors=[];top=0;possible=0
    for first in product(options(0),options(1)):
        required_d=frozenset(d for d in neighbours if abs(d)<first[d%2])
        required_s=frozenset().union(*(neighbours.get(v,()) for v in first))
        domain=set(range(-extent,extent+1))
        if max(len(required_d),len(required_s))>23 or not (required_d|required_s)<=domain:
            continue
        dkeys=_keys(required_d,extent)
        skeys=_keys(required_s,extent)
        top+=1;selector=top;selectors.append(selector)
        diff_ids=range(top+1,top+1+len(dkeys));top+=len(dkeys)
        sum_ids=range(top+1,top+1+len(skeys));top+=len(skeys)
        clauses.extend(([-selector,*diff_ids],[-selector,*sum_ids]))
        for i,(moment,odd) in zip(diff_ids,dkeys):
            other=(constant-moment,24-odd if extent%2 else odd)
            for j,key in zip(sum_ids,skeys):
                if key==other:possible+=1
                else:clauses.append([-i,-j])
    clauses.append(selectors)
    text=f'p cnf {top} {len(clauses)}\n'+''.join(
        ' '.join(map(str,clause))+' 0\n' for clause in clauses)
    return text.encode(),dict(parity=parity,constant=constant,profiles=len(selectors),compatible_pairs=possible)


def build(case,bits,root_hash,cube_hash):
    return projection(forced_axes(case,bits,root_hash,cube_hash))

def replay(receipt_path, expected_root):
    import json
    import subprocess
    from pathlib import Path
    path=Path(receipt_path)
    row=json.loads(path.read_text())
    case=tuple(row['case'])
    if row['root_sha256']!=expected_root or row['rule']!='same-parity-moments-v1':
        raise ValueError('unexpected root or reduction')
    data,stats=build(case,row['cube'],expected_root,row['cube_sha256'])
    digest=sha256(data).hexdigest()
    if row['cnf_sha256']!=digest or path.name!=row['cube_sha256']+'.receipt.json':
        raise ValueError('unexpected projected formula or receipt name')
    if stats['compatible_pairs'] or any(row[k]!=v for k,v in stats.items()):
        raise ValueError('projection has a compatible moment pair or inconsistent metadata')
    formula=path.parent/(digest+'.cnf')
    proof=path.parent/(row['proof_sha256']+'.drat')
    if formula.read_bytes()!=data or sha256(proof.read_bytes()).hexdigest()!=row['proof_sha256']:
        raise ValueError('archive differs from reconstructed certificate')
    checked=subprocess.run([Path(__file__).resolve().parents[2]/'tools/drat-trim',formula,proof,'-w'],
                           check=True,capture_output=True)
    if b's VERIFIED' not in checked.stdout.splitlines():raise ValueError('invalid DRAT proof')
    return case,row['cube']


if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser(description='Replay a Q47 same-parity terminal certificate')
    ap.add_argument('receipt')
    ap.add_argument('--root-sha256',required=True)
    args=ap.parse_args()
    case,bits=replay(args.receipt,args.root_sha256)
    print('VERIFIED',case,bits)
