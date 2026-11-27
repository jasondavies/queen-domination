"""Certificates for the remaining terminal Q47 frame cubes.

The line counts and the layer unit clauses determine both occupied axes.
For monochromatic parity grids see q47_same_parity.py for the two moment
identities. Here the diagonal supports have sizes 24-dT and 24-dS, and the
remaining multiset entries are repetitions. On the odd grid the sums u,v of
D,S satisfy |u|+|v|<=22 and u=v mod 2, since the duplicate ranks I,J in
0..22 satisfy u=I-J, v=I+J-22.

In the mixed case each axis is the 23 odd coordinates plus one even line.
Each line has exactly one queen. If the even lines were occupied by two
different queens, only 22 queens could diagonally attack the 23 by 23 grid
of empty even lines. This is impossible: the product of the 22 factors
((X-a)^2-(Y-b)^2) would vanish on that grid. Reducing it modulo the two
monic degree-23 coordinate polynomials cannot change the coefficient of
X^22 Y^22 (every reduction lowers total degree). That coefficient is
(-1)^11 binom(22,11), whereas the reduced grid-vanishing polynomial is zero.
Thus the exceptional queen is at the intersection of the even occupied lines.

After removing targets attacked by that queen, the remaining 23 queens form
a permutation on the odd axes. In ranks 0..22, D=i-j and S=i+j-22 have the
same parity. Their sums both vanish and sum(D²+S²)=4048. The targets have
D,S of opposite parity. In the graph with D of parity p and S of parity
1-p, the body queens supply precisely 23 entries in total (one per queen).
Enumerate the D support, forcing all neighbours of every omitted D into S.
Complete S and distribute repeated entries. A repeat is charged also when
the exceptional queen uses a body diagonal. The two parity graphs must
then have complementary keys, as implemented in mixed_profiles().

Each CNF selector chooses a profile. For that profile both key sets restrict
one common binary index. Clauses forbid exactly the prefix intervals outside
each set. Any full placement gives an index allowed by both sides.
"""
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import json
import subprocess

from q47_same_parity import occupied_axes

RULE = 'q47-terminal-diagonal-moments-v1'
ROOT = Path(__file__).resolve().parents[2]


@lru_cache(maxsize=256)
def diagonal_keys(required, extent, deficit):
    domain = frozenset(range(-extent,extent+1))
    distinct = 24-deficit
    if len(required)>distinct or not required<=domain:
        return frozenset()
    keys=set()
    for extra in combinations(sorted(domain-required),distinct-len(required)):
        support = required.union(extra)
        total=sum(support)
        squares=sum(i*i for i in support)
        odd=sum(i%2 for i in support)
        for duplicates in combinations_with_replacement(sorted(support),deficit):
            value=total+sum(duplicates)
            if (extent==23 and value!=0) or abs(value)>22:
                continue
            moment=squares+sum(i*i for i in duplicates)-value*value
            keys.add((moment,odd+sum(i%2 for i in duplicates),value))
    return frozenset(keys)


def other_sums(value, extent):
    if extent==23:
        return (0,)
    return range(abs(value)-22,23-abs(value),2)


def pure_profiles(parity, dt, ds):
    extent=23-parity
    constant=sum((2*i-extent)**2 for i in range(extent+1))
    neighbours={}
    for x,y in product(range(1-parity,47,2),repeat=2):
        neighbours.setdefault((x-y)//2,set()).add((x+y-46)//2)
    assert all(neighbours[d]==neighbours[-d] for d in neighbours)
    bounds=[]
    for p in (0,1):
        radii=sorted({abs(d) for d in neighbours if d%2==p})
        bounds.append([*radii,radii[-1]+2])
    domain=frozenset(range(-extent,extent+1))
    for radii in product(*bounds):
        dreq=frozenset(d for d in neighbours if abs(d)<radii[d%2])
        sreq=frozenset().union(*(neighbours.get(r,()) for r in radii))
        if len(dreq)>24-dt or len(sreq)>24-ds or not (dreq|sreq)<=domain:
            continue
        left={(m,o,u,v) for m,o,u in diagonal_keys(dreq,extent,dt) for v in other_sums(u,extent)}
        right={(constant-m,24-o if extent%2 else o,u,v)
               for m,o,v in diagonal_keys(sreq,extent,ds) for u in other_sums(v,extent)}
        yield left,right


def mixed_keys(x, y, parity, dt, ds):
    d0,s0=(x-y)//2,(x+y-46)//2
    differences=set(range(-22+parity,23,2))
    sums=set(range(-22+(1-parity),23,2))
    neighbours={d:set() for d in differences}
    required_d=set()
    required_s=set()
    for col,row in product(set(range(0,47,2))-{x},set(range(0,47,2))-{y}):
        d,s=(col-row)//2,(col+row-46)//2
        if d%2!=parity or d==d0 or s==s0:
            continue
        if d not in differences and s not in sums:
            return set()
        if d not in differences:
            required_s.add(s)
        elif s not in sums:
            required_d.add(d)
        else:
            neighbours[d].add(s)
    order=sorted(differences-required_d,key=lambda d:(-len(neighbours[d]),d))
    keys=set()
    def extend(dset,forced):
        for dreps in range(dt-int(d0 in dset)+1):
            for sreps in range(ds+1):
                extra=23-len(dset)-len(forced)-dreps-sreps
                if extra<0:continue
                for more in combinations(sorted(sums-forced),extra):
                    sset=forced.union(more)
                    scost=sreps+int(s0 in sset)
                    if scost>ds:continue
                    sd,ss=sum(dset),sum(sset)
                    sq=sum(v*v for v in dset)+sum(v*v for v in sset)
                    for du in combinations_with_replacement(sorted(dset),dreps):
                        for su in combinations_with_replacement(sorted(sset),sreps):
                            keys.add((len(dset)+dreps,sd+sum(du),ss+sum(su),
                                      sq+sum(i*i for i in du+su),dreps+int(d0 in dset),scost))
    def visit(i,dset,forced):
        if len(dset)+len(forced)>23:return
        if i==len(order):
            extend(dset,forced)
            return
        d=order[i]
        visit(i+1,dset|{d},forced)
        visit(i+1,dset,forced|neighbours[d])
    visit(0,required_d,required_s)
    return keys


def mixed_profiles(x,y,dt,ds):
    left=mixed_keys(x,y,0,dt,ds)
    right={(23-n,-d,-s,4048-q,dt-a,ds-b) for n,d,s,q,a,b in mixed_keys(x,y,1,dt,ds)}
    yield left,right


def project(profiles):
    clauses=[];selectors=[];top=0;matches=0
    for left,right in profiles:
        # Rank the union injectively; use the same rank map on both sides.
        ranks={k:i for i,k in enumerate(sorted(left|right))}
        matches+=len(left&right)
        top+=1;selector=top;selectors.append(selector)
        width=max(0,len(ranks)-1).bit_length()
        variables=tuple(range(top+1,top+1+width));top+=width
        def restrict(allowed):
            indices=sorted(ranks[k] for k in allowed)
            # Exclude contiguous gaps using aligned dyadic intervals.
            start=0
            for end in [*indices,1<<width]:
                while start<end:
                    size=1<<((end-start).bit_length()-1)
                    if start:size=min(size,start & -start)
                    prefix_len=width-(size.bit_length()-1)
                    clause=[-selector]
                    for pos,var in enumerate(variables[:prefix_len]):
                        clause.append(-var if start & (1<<(width-pos-1)) else var)
                    clauses.append(clause);start+=size
                start=end+1
        restrict(left);restrict(right)
    clauses.append(selectors)
    data=f'p cnf {top} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)
    return data.encode(),dict(profiles=len(selectors),compatible_keys=matches)


@lru_cache(maxsize=64)
def projection(kind,x,y,dt,ds):
    return project(mixed_profiles(x,y,dt,ds) if kind=='exception' else pure_profiles(int(kind=='odd'),dt,ds))


def build(case,bits,root_hash,cube_hash):
    rows,cols=occupied_axes(case,bits,root_hash,cube_hash)
    evens=frozenset(range(0,47,2));odds=frozenset(range(1,47,2))
    dt,ds=case[6:]
    x=y=None
    if rows==cols==evens:
        kind='even'
    elif rows==cols==odds:
        kind='odd'
    elif odds<rows and odds<cols and case[4:6]==(0,0):
        x,=cols-odds;y,=rows-odds
        kind='exception'
    else:
        raise ValueError('unrecognised occupied axes')
    data,stats=projection(kind,x,y,dt,ds)
    return data,dict(stats,kind=kind,even_column=x,even_row=y)


def replay(path, expected_root):
    row=json.loads(path.read_text())
    case=tuple(row['case'])
    if row['root_sha256']!=expected_root or row['rule']!=RULE:raise ValueError('root or rule mismatch')
    data,stats=build(case,row['cube'],expected_root,row['cube_sha256'])
    digest=sha256(data).hexdigest()
    if row['cnf_sha256']!=digest or path.name!=row['cube_sha256']+'.receipt.json':raise ValueError('formula hash mismatch')
    if stats['compatible_keys'] or any(row[k]!=v for k,v in stats.items()):raise ValueError('moment key mismatch')
    formula=path.parent/(digest+'.cnf');proof=path.parent/(row['proof_sha256']+'.drat')
    if formula.read_bytes()!=data or sha256(proof.read_bytes()).hexdigest()!=row['proof_sha256']:
        raise ValueError('certificate content mismatch')
    ck=subprocess.run([ROOT/'tools/drat-trim',formula,proof,'-w'],capture_output=True,check=True)
    if b's VERIFIED' not in ck.stdout.splitlines():raise ValueError('proof replay failed')
    return case,row['cube']


if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser(description='Reconstruct and replay a Q47 terminal moment certificate')
    ap.add_argument('receipt',type=Path);ap.add_argument('--root-sha256',required=True)
    args=ap.parse_args()
    print('VERIFIED',*replay(args.receipt,args.root_sha256))
