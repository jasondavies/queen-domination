"""Exclude the Q47 even-row, odd-column profile by enumerating diagonal covers.

Coordinates are centered. Queens occupy odd rows and even columns, with
one doubled column. Targets have even rows and odd columns. This checker
works directly from the grid and uses neither the prefix CNF nor its generator.
"""
from functools import lru_cache
from itertools import combinations_with_replacement, product


def check():
    diagonals = range(-45, 46, 2)
    neighbours = {s: set() for s in diagonals}
    for x, y in product(range(-23, 24, 2), range(-22, 23, 2)):
        neighbours[x + y].add(y - x)

    # Every omitted sum forces all its incident differences. Enumerate the
    # possible unions of those neighbourhoods, keeping at most 24 differences.
    unions = {frozenset()}
    for incident in neighbours.values():
        unions |= {covered | incident for covered in unions if len(covered | incident) <= 24}

    @lru_cache(maxsize=None)
    def completions(required):
        keys = set()
        for extra in combinations_with_replacement(diagonals, 24 - len(required)):
            values = (*required, *extra)
            keys.add((sum(values), sum(v * v for v in values), sum(v % 4 == 1 for v in values)))
        return keys

    base = 2 * sum(i * i for i in range(-23, 24))
    profiles = 0
    for differences in unions:
        sums = frozenset(s for s, incident in neighbours.items() if not incident <= differences)
        if len(sums) > 24:
            continue
        profiles += 1
        sum_keys = completions(sums)
        for total, squares, residue_count in completions(differences):
            doubled_column = -total
            if doubled_column not in range(-22, 23, 2):
                continue
            required_key = (doubled_column, base + 2 * doubled_column**2 - squares, residue_count)
            if required_key in sum_keys:
                raise ValueError("compatible orthodox moment signature survived")
    return profiles


if __name__ == "__main__":
    print(f"Checked {check()} orthodox diagonal support pairs; none admits compatible moments.")
