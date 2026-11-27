"""Independent finite enumeration for the Q47 terminal moment receipts.

For each parity graph, enumerate unions F of difference-neighbour sets of
sum vertices. For any cover, take the union over its absent sum vertices,
including differences forced by unavailable sums. F consists of selected
differences. Every sum with a neighbour outside F must also be present.
This enumerates a subcover of every possible placement. Extend each such
subcover to the full multiset by adding any entries, including repetitions.
This check uses no projected CNF, radius thresholds or SAT solver.
"""
from functools import lru_cache
from itertools import combinations_with_replacement, product
from pathlib import Path
import json

import check_q47_even_permutation as even
from q47_same_parity import occupied_axes


@lru_cache(maxsize=32)
def signatures(exception, dlimit, slimit, parity):
    count=23 if exception else 24
    columns=set(range(0,47,2))
    rows=columns.copy()
    ed=es=None
    if exception:
        x,y=exception
        columns.remove(x);rows.remove(y)
        ed,es=(y-x)//2,(x+y-46)//2
    domain=range(-22,23)
    differences={d for d in domain if d%2==parity}
    sums={s for s in domain if s%2!=parity}
    neighbours={s:frozenset() for s in sums}
    forced_d=set();forced_s=set()
    for x,y in product(columns,rows):
        d,s=(y-x)//2,(x+y-46)//2
        if d%2!=parity or d==ed or s==es:continue
        if d not in differences and s not in sums:return set()
        if s not in sums:forced_d.add(d)
        elif d not in differences:forced_s.add(s)
        else:neighbours[s]=neighbours[s]|{d}
    unions={frozenset(forced_d)}
    for s in sorted(sums-forced_s):
        unions|={f|neighbours[s] for f in unions}
    allowed=[(0,d) for d in sorted(differences)]+[(1,s) for s in sorted(sums)]
    result=set()
    for ds in unions:
        ss=forced_s|{s for s,ns in neighbours.items() if not ns<=ds}
        remaining=count-len(ds)-len(ss)
        if remaining<0:continue
        for extra in combinations_with_replacement(allowed,remaining):
            dvals=tuple(ds)+tuple(v for family,v in extra if family==0)
            svals=tuple(ss)+tuple(v for family,v in extra if family==1)
            cd=len(dvals)-len(set(dvals))+int(ed in dvals)
            cs=len(svals)-len(set(svals))+int(es in svals)
            if cd<=dlimit and cs<=slimit:
                result.add((len(dvals),sum(dvals),sum(svals),
                            sum(i*i for i in dvals+svals),cd,cs))
    return result


def verify_profile(exception,dt,ds):
    n=23 if exception else 24
    # For the odd permutation both first moments vanish. With duplicates,
    # enumerate the actual extra row and column independently of the diagonals.
    base_squares=4*sum((i-11)**2 for i in range(23))
    totals=[(0,0,base_squares)] if exception else [
        (j-i,i+j-22,base_squares+2*((i-11)**2+(j-11)**2))
        for i,j in product(range(23),repeat=2)]
    a=signatures(exception,dt,ds,0)
    b=signatures(exception,dt,ds,1)
    # The complement lookup is symmetric between the two parity classes.
    if len(a)>len(b):a,b=b,a
    for k,d,s,q,t,u in a:
        for td,ts,tq in totals:
            if (n-k,td-d,ts-s,tq-q,dt-t,ds-u) in b:
                raise AssertionError('a compatible moment signature survived')


def main():
    even.check()  # independent enumeration, covers all even-even permutations
    data=Path(__file__).resolve().parents[2]/'data/frame/q47_terminal_moments'
    count=0
    for path in sorted(data.glob('*.receipt.json')):
        r=json.loads(path.read_text());case=tuple(r['case'])
        rows,cols=occupied_axes(case,r['cube'],r['root_sha256'],r['cube_sha256'])
        evens=set(range(0,47,2));odds=set(range(1,47,2))
        if rows==cols==evens:pass
        elif rows==cols==odds:verify_profile(None,*case[6:])
        else:
            assert odds<rows and odds<cols and case[4:6]==(0,0)
            y,=rows-odds;x,=cols-odds
            verify_profile((x,y),*case[6:])
        count+=1
    assert count==15
    print('All 15 terminal occupancy profiles passed the independent enumeration.')

if __name__=='__main__':main()
