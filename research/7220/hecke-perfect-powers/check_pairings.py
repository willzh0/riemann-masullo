"""Enumerate alternating pairings on every subgroup of small finite abelian groups."""

from collections import Counter
from functools import cache
from itertools import combinations, product
from math import gcd, isqrt, lcm, prod


# Invariant factors and independently known numbers of subgroups.
CASES = (
    ((), 1), ((2,), 2), ((4,), 3), ((6,), 4), ((12,), 6),
    ((2, 4), 8), ((4, 4), 15), ((3, 3), 6), ((6, 6), 30),
    ((2, 2, 2), 16), ((2, 2, 2, 2), 67), ((2, 2, 6), 32),
    ((3, 3, 3, 3), 212),
)


def elements(orders):
    return product(*(range(n) for n in orders))


def subgroups(orders):
    """Return each subgroup once with the orders of a direct-product basis."""
    zero = (0,) * len(orders)
    trivial = frozenset((zero,))
    cyclic = set()
    for point in elements(orders):
        if point != zero:
            order = lcm(*(n // gcd(x, n) for x, n in zip(point, orders)))
            cyclic.add(frozenset(tuple(k * x % n for x, n in zip(point, orders))
                                 for k in range(order)))

    bases = {trivial: ()}
    pending = [trivial]
    while pending:
        group = pending.pop()
        for factor in cyclic:
            if len(group & factor) != 1:
                continue
            larger = frozenset(tuple((x + y) % n for x, y, n in zip(a, b, orders))
                               for a in group for b in factor)
            if larger not in bases:
                # Every subgroup is reachable by successively adjoining its cyclic summands.
                bases[larger] = tuple(sorted((*bases[group], len(factor))))
                pending.append(larger)
    return bases


@cache
def pairing_histogram(orders):
    """Count all alternating forms by h, representing roots as additive residues."""
    modulus = lcm(*orders)
    pairs = list(combinations(range(len(orders)), 2))
    # b(e_i,e_j) can be any root whose order divides both cyclic orders.
    options = [range(0, modulus, modulus // gcd(orders[i], orders[j])) for i, j in pairs]
    points = list(elements(orders))
    counts = Counter()
    for values in product(*options):
        columns = [[0] * len(orders) for _ in orders]
        for (i, j), v in zip(pairs, values):
            columns[j][i] = v
            columns[i][j] = -v

        # Pairing to zero with every basis element is exactly radical membership.
        radical_size = sum(all(sum(x * y for x, y in zip(point, col)) % modulus == 0
                               for col in columns) for point in points)
        index, remainder = divmod(len(points), radical_size)
        h = isqrt(index)
        assert remainder == 0 and h * h == index
        counts[h] += 1
    assert sum(counts.values()) == prod(gcd(orders[i], orders[j]) for i, j in pairs)
    return counts


def main():
    total_subgroups = total_pairings = total_full = 0
    for orders, expected_subgroups in CASES:
        assert all(b % a == 0 for a, b in zip(orders, orders[1:]))
        bound = prod(tuple(reversed(orders))[1::2])
        bases = subgroups(orders)
        assert len(bases) == expected_subgroups
        counts = Counter()
        for parts in bases.values():
            counts.update(pairing_histogram(parts))
        full = pairing_histogram(orders)
        assert full == pairing_histogram(bases[frozenset(elements(orders))])
        assert all(bound % h == 0 for h in counts) and full[bound] > 0
        if orders == (2, 2, 2, 2):
            # The 35 possible two-dimensional radicals each yield one rank-two form.
            assert full == {1: 1, 2: 35, 4: 28}
        name = "x".join(f"C{n}" for n in orders) or "1"
        print(f"{name:12} D={bound:2}  subgroups={len(bases):3}  "
              f"subgroup-pairings={sum(counts.values()):4}  full h={dict(sorted(full.items()))}")
        total_subgroups += len(bases)
        total_pairings += sum(counts.values())
        total_full += sum(full.values())
    print(f"Total groups={len(CASES)}  subgroups={total_subgroups}  "
          f"subgroup-pairings={total_pairings}  full-group pairings={total_full}")


if __name__ == "__main__":
    main()
