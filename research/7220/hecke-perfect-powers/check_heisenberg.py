"""Check the Heisenberg induction identities using exact cyclotomic arithmetic."""

from itertools import product


def divide_monic(dividend, divisor):
    """Return quotient and remainder; coefficient lists run from degree zero up."""
    rem = dividend[:]
    quot = [0] * max(1, len(rem) - len(divisor) + 1)
    for degree in range(len(rem) - len(divisor), -1, -1):
        leading = rem[degree + len(divisor) - 1]
        quot[degree] = leading
        for j, value in enumerate(divisor):
            rem[degree + j] -= leading * value
    return quot, rem[:len(divisor) - 1]


def cyclotomic_polynomials(limit):
    polys = {}
    for n in range(1, limit + 1):
        poly = [-1] + [0] * (n - 1) + [1]
        for d in range(1, n):
            if n % d == 0:
                poly, rem = divide_monic(poly, polys[d])
                assert not any(rem)
        polys[n] = poly
    return polys


def conjugate_by_rep(g, a, b, n):
    # In UT3, (a,b,0)^(-1) * (x,y,z) * (a,b,0) has this central entry.
    x, y, z = g
    return x, y, (z + x * b - a * y) % n


def check(n, phi):
    all_elements = list(product(range(n), repeat=3))
    line_reps = [(a, 0) for a in range(n)]
    center_reps = list(product(range(n), repeat=2))
    central_elements = 0
    irreducible_norm_numerator = 0
    for g in all_elements:
        line_trace = [0] * n
        center_trace = [0] * n
        # Induce mu(0,y,z)=zeta^z from the abelian plane x=0.
        for a, b in line_reps:
            x, y, z = conjugate_by_rep(g, a, b, n)
            if x == 0:
                line_trace[z] += 1
        # Independently induce lambda(0,0,z)=zeta^z from the center.
        for a, b in center_reps:
            x, y, z = conjugate_by_rep(g, a, b, n)
            if x == y == 0:
                center_trace[z] += 1
        difference = [a - n * b for a, b in zip(center_trace, line_trace)]
        _, rem = divide_monic(difference, phi)
        assert not any(rem), (n, g, "induction mismatch")
        expected = [0] * n
        if g[0] == g[1] == 0:
            central_elements += 1
            expected[g[2]] = n
            irreducible_norm_numerator += n * n
        _, rem = divide_monic([a - b for a, b in zip(line_trace, expected)], phi)
        assert not any(rem), (n, g, "central trace formula")
    assert central_elements == n
    assert irreducible_norm_numerator == len(all_elements)
    print(f"n={n:2}: {len(all_elements):4} group elements, "
          f"degree {n} irreducible, degree {n*n} monomial character = {n} copies")


if __name__ == "__main__":
    values = (2, 3, 4, 5, 6, 7, 8, 9, 10, 12)
    polys = cyclotomic_polynomials(max(values))
    for value in values:
        check(value, polys[value])
