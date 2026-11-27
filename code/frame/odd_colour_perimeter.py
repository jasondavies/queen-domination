"""Colour-specific perimeter budgets for a zero-deficit square frame on n = 2k-1.

F, V and H count the wasted diagonal incidences on the perimeter, its two
vertical sides, and its two horizontal sides, in the sense of enc.case_extra.
A colour with z queens supplies 2z distinct diagonals. For that colour let
v,h be the numbers of needy squares on V,H, b the number of occupied box
diagonals, and c its number of corners. The exact wastes in a cover are
F = 4z-v-h+c, V = 2z+b-v, H = 2z+b-h. Each box diagonal can hit each pair
of opposite sides twice. The full perimeter counts a needy corner once.

The ordinary waste-term encoding already enforces the total over both
colours. Here each admissible split imposes upper bounds separately.
"""
from itertools import product

from pysat.card import ITotalizer

import enc


def budget_splits(k, span, corner, bits):
    """Yield (even queen count or None, F-pair, V-pair, H-pair)."""
    if span % 2:
        # Opposite sides have opposite parity, so v=h=k-1 in both colours.
        bonuses = [0, 0]
        bonuses[corner], bonuses[1-corner] = bits
        for even in range(k + 1):
            counts = (even, k-even)
            full = tuple(4*z - 2*(k-1) + 2 for z in counts)
            side = tuple(2*z + b - (k-1) for z, b in zip(counts, bonuses))
            if min(*full, *side) >= 0:
                yield even, full, side, side
    else:
        # All corners have the same colour. In the other colour v,h are
        # even, b=c=0, hence V,H are even and F=V+H. Total F=8.
        total_side = 2 + sum(bits)
        def ordered(noncorner, total):
            pair = (total-noncorner, noncorner)
            return pair if corner == 0 else pair[::-1]
        for v, h in product(range(0, total_side+1, 2), repeat=2):
            yield None, ordered(v+h, 8), ordered(v, total_side), ordered(h, total_side)


def colour_clauses(base, case, top):
    """Build additional clauses in fresh variables above top."""
    a, right, c, upper, *deficits = case
    span = base.n - 1 - a - right
    if any(deficits) or base.n != 2*base.k-1 or span != base.n-1-c-upper:
        raise ValueError("requires a zero-deficit square frame on an odd board")
    corner = (a+c) % 2
    debug = {}
    enc.case_extra(base, case, debug=debug)
    colours = {lit: index % 2 for family in (base.oT, base.oS)
               for index, lit in family.items()}
    clauses = []
    gates = {}
    def new():
        nonlocal top
        top += 1
        return top

    def indicator(condition):
        if len(condition) == 1:
            return condition[0]
        if condition not in gates:
            gate = gates[condition] = new()
            # Only the forward implication is needed for upper bounds.
            clauses.append([-lit for lit in condition] + [gate])
        return gates[condition]

    def thresholds(literals, limit):
        nonlocal top
        with ITotalizer(lits=literals, ubound=limit, top_id=top) as totalizer:
            top = max(top, totalizer.top_id)
            clauses.extend(totalizer.cnf.clauses)
            return list(totalizer.rhs)

    counters = {}
    for name, limit in (('F', 8), ('V', 4), ('H', 4)):
        groups = [[], []]
        for condition in debug[name][0]:
            groups[colours[condition[0]]].append(indicator(condition))
        counters[name] = [thresholds(group, limit) for group in groups]
    if span % 2:
        counters['Q'] = [thresholds([v for t, v in base.oT.items() if t%2 == p],
                                    base.k) for p in range(2)]
    diagonals = [base.oT[c-a], base.oS[a+c+span]]
    for bits in product(range(2), repeat=2):
        branches = []
        for even, f, v, h in budget_splits(base.k, span, corner, bits):
            branch = new()
            branches.append(branch)
            bounds = [('F', f), ('V', v), ('H', h)]
            if even is not None:
                bounds.append(('Q', (even, base.k-even)))
            for name, pair in bounds:
                for rhs, limit in zip(counters[name], pair):
                    if limit < len(rhs):
                        clauses.append([-branch, -rhs[limit]])
        clauses.append([(-lit if bit else lit) for lit, bit in zip(diagonals, bits)]
                       + branches)
    return clauses, top


def build_q47_colour(case, cube='', *, expected_root_sha256=None):
    """Return (base, colour DIMACS bytes, baseline cube SHA-256).

    The optional hash is for the baseline root, before adding cube units.
    Cube bits have the same order as the Q47 overnight runner. The returned
    baseline digest identifies the ordinary root or cube that a refutation
    closes. Check a DRAT trace against the returned colour DIMACS bytes.
    """
    from hashlib import sha256

    import q47_batch
    from run_hard import layer_vars

    case = tuple(case)
    if len(case) != 8 or any(case[4:]) or sum(case[:2]) != sum(case[2:4]):
        raise ValueError('requires a zero-deficit square frame')
    if len(cube) % 4 or set(cube) - {'0', '1'}:
        raise ValueError('expected four bits per cube layer')
    base, plain = q47_batch.build(case)
    if expected_root_sha256 is not None and sha256(plain).hexdigest() != expected_root_sha256:
        raise ValueError('baseline root digest differs from the supplied digest')
    head, body = plain.split(b'\n', 1)
    top, clause_count = map(int, head.split()[2:])
    if cube:
        units = []
        for start in range(0, len(cube), 4):
            layer = layer_vars(base, case, 1 + start//4)
            if layer is None or len(layer) != 4:
                raise ValueError('cube extends beyond the available frame layers')
            for bit, variable in zip(cube[start:start+4], layer):
                units.append(f'{variable if bit == "1" else -variable} 0\n')
        body += ''.join(units).encode()
        clause_count += len(units)
        plain = f'p cnf {top} {clause_count}\n'.encode() + body

    clauses, new_top = colour_clauses(base, case, top)
    suffix = ''.join(' '.join(map(str, clause)) + ' 0\n' for clause in clauses)
    header = f'p cnf {new_top} {clause_count+len(clauses)}\n'
    return base, header.encode() + body + suffix.encode(), sha256(plain).hexdigest()
