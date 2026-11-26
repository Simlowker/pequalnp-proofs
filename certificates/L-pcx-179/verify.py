"""Verify the finite root-cover bounds for tree-like Res(XOR) on PHP(5,4).

Run with Python 3.10 or later. The checks use integer arithmetic throughout.
"""
import json
from functools import lru_cache
from itertools import combinations, permutations
from pathlib import Path

ROWS, HOLES = 5, 4
ALL_AXIOMS = (1 << 45) - 1
ROW_CELLS = [15 << (4 * row) for row in range(ROWS)]
COLLISIONS = [
    (1 << (4 * i + h)) | (1 << (4 * j + h))
    for h in range(HOLES) for i, j in combinations(range(ROWS), 2)
]


def check(condition, message):
    if not condition:
        raise ValueError(message)


@lru_cache(None)
def faults(x):
    check(isinstance(x, int) and 0 <= x < 1 << 20, "invalid assignment")
    row_faults = sum(1 << i for i, row in enumerate(ROW_CELLS) if not x & row)
    return row_faults | sum(1 << (5 + i) for i, pair in enumerate(COLLISIONS)
                            if x & pair == pair)


def critical_groups():
    groups = [set() for _ in range(45)]
    for unused in range(ROWS):
        others = [i for i in range(ROWS) if i != unused]
        for holes in permutations(range(HOLES)):
            base = sum(1 << (4 * i + h) for i, h in zip(others, holes))
            for x in [base] + [base | (1 << (4 * unused + h)) for h in holes]:
                mask = faults(x)
                check(mask.bit_count() == 1, "expected a unique axiom")
                groups[mask.bit_length() - 1].add(x)
    check([len(g) for g in groups] == [24] * 5 + [6] * 40, "critical groups")
    return groups


def split_counts():
    # Each 32-bit lane contains the truth values on one group of assignments.
    # After five OR shifts its low bit records whether the group has a set bit.
    grouped = [(32 * i + j, x) for i, g in enumerate(critical_groups())
               for j, x in enumerate(sorted(g))]
    occupied = sum(1 << pos for pos, _ in grouped)
    lane_starts = sum(1 << (32 * i) for i in range(45))
    columns = [sum(1 << pos for pos, x in grouped if x >> v & 1)
               for v in range(20)]

    def lanes(mask):
        for shift in (1, 2, 4, 8, 16):
            mask |= mask >> shift
        return mask & lane_starts

    small = set()
    minimum = 45
    values = 0
    for i in range(1, 1 << 20):
        # Gray code changes exactly the bit indexed by the low set bit of i.
        values ^= columns[(i & -i).bit_length() - 1]
        count = (lanes(values) & lanes(occupied ^ values)).bit_count()
        if count < 22:
            small.add(i ^ (i >> 1))
        else:
            minimum = min(minimum, count)
    return small, 45 + minimum


def special_bounds(certificates):
    # Row and hole permutations preserve the set of PHP axioms. Complementing
    # both index sets preserves the coefficient mask of their XOR.
    def mask(rows, cols):
        return sum(1 << (4 * i + h) for i in range(ROWS) for h in range(HOLES)
                   if (i in rows) != (h in cols))

    covered = set()
    minimum = 90
    for a in range(3):
        for b in range(5):
            if a == b == 0:
                continue
            q = mask(range(a), range(b))
            sides = certificates[str(q)]
            check(len(sides) == 2, "expected two parity sides")
            costs = [side_cost(q, parity, side) for parity, side in enumerate(sides)]
            minimum = min(minimum, sum(costs))
            for rows in combinations(range(ROWS), a):
                for cols in combinations(range(HOLES), b):
                    covered.add(mask(rows, cols))
    return covered, minimum


def side_cost(query, parity, certificate):
    def witness(x):
        check((x & query).bit_count() % 2 == parity, "witness on wrong parity side")
        return faults(x)

    selected = 0
    for x in certificate["mandatory"]:
        mask = witness(x)
        check(mask.bit_count() == 1, "mandatory witness must have one fault")
        selected |= mask

    def bound(tree, included, excluded):
        tag, *args = tree
        if tag == "split":
            index, yes, no = args
            check(isinstance(index, int) and 0 <= index < 45, "invalid split")
            bit = 1 << index
            check(not (included | excluded) & bit, "repeated split")
            return min(bound(yes, included | bit, excluded),
                       bound(no, included, excluded | bit))
        if tag == "impossible":
            (x,) = args
            check(witness(x) & ~excluded == 0, "the cover is still possible")
            return 46  # greater than the number of all axioms
        capacity = tag
        (weights,) = args
        check(isinstance(capacity, int) and capacity > 0, "invalid capacity")
        load = [0] * 45
        total = 0
        for x, weight in weights:
            check(isinstance(weight, int) and weight > 0, "invalid weight")
            f = witness(x)
            check(not f & included, "already-covered witness")
            total += weight
            active = f & (ALL_AXIOMS ^ excluded)
            while active:
                bit = active & -active
                load[bit.bit_length()-1] += weight
                active ^= bit
        check(max(load) <= capacity, "dual axiom capacity exceeded")
        return included.bit_count() + (total + capacity - 1) // capacity

    return bound(certificate["tree"], selected, 0)


if __name__ == "__main__":
    certs = json.loads(Path(__file__).with_name("weights.json").read_text())
    small, ordinary = split_counts()
    covered, special = special_bounds(certs)
    check(small == covered and len(small) == 255, "exceptional pivots mismatch")
    leaves = min(ordinary, special)
    check(leaves >= 67, "leaf bound below 67")
    print(f"{(1<<20)-1-len(small):,} ordinary pivots: at least {ordinary} leaves")
    print(f"{len(small)} exceptional pivots: at least {special} leaves")
    print(f"Tree lower bound: {leaves} axiom leaves, {2*leaves-1} line occurrences")
