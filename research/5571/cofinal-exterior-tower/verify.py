"""Exact finite checks for the induction identity and the two sampling stencils."""

from fractions import Fraction
from itertools import permutations
from math import factorial, gcd, lcm, prod


def compose(left, right):
    return tuple(left[i] for i in right)


def inverse(element):
    return tuple(element.index(i) for i in range(len(element)))


def sign(element):
    return (-1) ** sum(x > y for i, x in enumerate(element) for y in element[i + 1:])


def powers_of(generator):
    identity = tuple(range(len(generator)))
    powers = [identity]
    item = generator
    while item != identity:
        powers.append(item)
        item = compose(item, generator)
    return powers


def mobius(number):
    result = 1
    prime = 2
    while prime * prime <= number:
        if number % prime == 0:
            number //= prime
            if number % prime == 0:
                return 0
            result = -result
        prime += 1
    return -result if number > 1 else result


def ramanujan(order, index):
    common = gcd(order, index)
    return sum(d * mobius(order // d) for d in range(1, common + 1) if common % d == 0)


def at_primitive_root(polynomial, degree):
    """Exact zero at a primitive root via all Galois conjugates of its squared norm."""
    return sum(a * b * ramanujan(degree, abs(i - j))
               for i, a in enumerate(polynomial) if a
               for j, b in enumerate(polynomial) if b)


def verify_induction(group):
    identity = tuple(range(len(group[0])))
    cyclic = {}
    for element in group:
        powers = powers_of(element)
        if len(powers) > 1:
            cyclic.setdefault(frozenset(powers), powers)
    exponent = lcm(1, *(len(powers) for powers in cyclic.values()))
    inverse_table = {h: inverse(h) for h in group}
    checks = 0
    for x in group:
        values = [0] * exponent
        conjugates = [compose(compose(inverse_table[h], x), h) for h in group]
        for subgroup, powers in cyclic.items():
            order = len(powers)
            phi = ramanujan(order, 0)
            coefficients = [phi - ramanujan(order, r) for r in range(order)]
            assert coefficients[0] == 0 and all(c > 0 for c in coefficients[1:])
            for conjugate in conjugates:
                if conjugate not in subgroup:
                    continue
                power = powers.index(conjugate)
                for r in range(1, order):
                    frequency = (power * r * (exponent // order)) % exponent
                    values[frequency] += coefficients[r] * (exponent // order)
        expected = len(group) * (len(group) * int(x == identity) - 1)
        values[0] -= exponent * expected
        assert at_primitive_root(values, exponent) == 0, (x, exponent, values)
        checks += 1
    return checks


def generated_group(generators):
    identity = tuple(range(len(generators[0])))
    seen = {identity}
    stack = [identity]
    while stack:
        item = stack.pop()
        for generator in generators:
            successor = compose(item, generator)
            if successor not in seen:
                seen.add(successor)
                stack.append(successor)
    return sorted(seen)


def sample_weights(nodes, point):
    return [prod((point - other) / (node - other) for other in nodes if other != node)
            for node in nodes]


def check_interpolation(nodes, point):
    weights = sample_weights(nodes, point)
    for degree in range(len(nodes)):
        assert sum(w * x**degree for w, x in zip(weights, nodes)) == point**degree
    return sum(abs(w) for w in weights)


def verify_sampling():
    central = 0
    for m in range(1, 10):
        nodes = [Fraction(j) for j in range(-m, m + 1)]
        bound = 1 + 2 * sum(Fraction(1, 2*j - 1) for j in range(1, m + 1))
        for numerator in range(-6, 7):
            assert check_interpolation(nodes, Fraction(numerator, 12)) <= bound
            central += 1
    scheduled = 0
    all_times = set()
    for k in range(2, 24):
        packets = {}
        for j in range(k*k):
            point = k + Fraction(j, k*k)
            stage = ((j + 1) & -(j + 1)).bit_length()
            assert point not in all_times
            all_times.add(point)
            packets.setdefault(stage, []).append(point)
        for stage, grid in packets.items():
            mesh = Fraction(2**stage, k*k)
            assert all(y - x == mesh for x, y in zip(grid, grid[1:]))
            assert grid[0] - k <= mesh and k + 1 - grid[-1] <= mesh
            count = min(7, len(grid))
            for point in [Fraction(k), k + Fraction(19, 53), Fraction(k + 1)]:
                nodes = sorted(sorted(grid, key=lambda x: (abs(x-point), x))[:count])
                y = (point - nodes[0]) / mesh
                assert -1 <= y <= count
                bound = Fraction(2**(count-1) * count**(count-1), factorial(count-1))
                assert check_interpolation(nodes, point) <= bound
                scheduled += 1
    assert len(all_times) == sum(k*k for k in range(2, 24))
    return central, scheduled, len(all_times)


def main():
    symmetric = {n: list(permutations(range(n))) for n in (3, 4, 5)}
    dihedral = generated_group([(1, 2, 3, 0), (0, 3, 2, 1)])
    cyclic = generated_group([(1, 2, 3, 4, 5, 0)])
    all_groups = [cyclic, dihedral, symmetric[3], symmetric[4],
                  [p for p in symmetric[4] if sign(p) == 1],
                  [p for p in symmetric[5] if sign(p) == 1]]
    assert [len(group) for group in all_groups] == [6, 8, 6, 24, 12, 60]
    checked = sum(verify_induction(group) for group in all_groups)
    for x in symmetric[3]:
        standard = sum(i == value for i, value in enumerate(x)) - 1
        regular = 6 * int(x == (0, 1, 2))
        assert regular == 1 + sign(x) + 2 * standard
    central, scheduled, times = verify_sampling()
    print(f"Positive cyclic induction checked at {checked} elements in {len(all_groups)} groups.")
    print(f"S3 norm fibre and double cubic surplus checked at every group element.")
    print(f"Interpolation checked at {central} centered and {scheduled} scheduled evaluations.")
    print(f"All {times} assigned times were distinct.")


if __name__ == "__main__":
    main()
