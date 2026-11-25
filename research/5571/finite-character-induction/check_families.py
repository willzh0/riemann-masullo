"""Exact finite checks for the quadratic Hecke-character families, Python 3.8+.

The curve is y^2 = x^3 - x + 1. The point counts certify mod-ell image
witnesses. The matrix and Walsh checks concern the finite groups themselves.
"""

from collections import Counter
from itertools import product
from math import gcd, prod


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def legendre(value, p):
    residue = pow(value % p, (p - 1) // 2, p)
    return -1 if residue == p - 1 else residue


def frobenius(p):
    require(gcd(p, 368) == 1, f"bad reduction at {p}")
    affine = sum((y * y - x**3 + x - 1) % p == 0
                 for x, y in product(range(p), repeat=2))
    points = affine + 1  # The unique point at infinity.
    trace = p + 1 - points
    return points, trace, trace**2 - 4 * p


def check_witnesses(ell, irreducible_prime, jordan_prime):
    for prime, kind in ((irreducible_prime, "irreducible"), (jordan_prime, "Jordan")):
        points, trace, disc = frobenius(prime)
        require(prime != ell, "Frobenius prime equals the torsion prime")
        if kind == "irreducible":
            require(legendre(disc, ell) == -1, "discriminant is not a nonsquare")
        else:
            # A matrix scalar modulo ell has discriminant divisible by ell^2.
            require(disc % ell == 0 and disc % (ell**2) != 0,
                    "discriminant does not have valuation one")
        print(f"ell={ell} {kind}: p={prime}, #E(F_p)={points}, a_p={trace}, D={disc}")


def check_induced_traces(ell):
    lines = [(1, t) for t in range(ell)] + [(0, 1)]
    matrices = 0
    for a, b, c, d in product(range(ell), repeat=4):
        det = (a * d - b * c) % ell
        if not det:
            continue
        matrices += 1
        line_trace = quotient_trace = 0
        for x, y in lines:
            u, v = (a * x + b * y) % ell, (c * x + d * y) % ell
            if (x * v - y * u) % ell:
                continue
            eigenvalue = u if x else v  # The first nonzero coordinate was 1.
            line_trace += legendre(eigenvalue, ell)
            quotient_trace += legendre(det * pow(eigenvalue, -1, ell), ell)
        require(line_trace == quotient_trace, f"induced traces differ at {(a, b, c, d)}")
    require(matrices == (ell**2 - 1) * (ell**2 - ell), "GL2 count failed")
    print(f"ell={ell}: equal induced traces on all {matrices} invertible matrices")


def walsh(mask, cell):
    return prod(sign for selected, sign in zip(mask, cell) if selected)


def check_walsh_cells(primes):
    masks = list(product((False, True), repeat=len(primes)))
    positive = (1,) * len(primes)
    cells = list(product((1, -1), repeat=len(primes)))
    counts = Counter()
    # Integer numerators of the Walsh coefficients, all with denominator 2^m.
    weights = {cell: [walsh(mask, cell) for mask in masks] for cell in cells}
    for cell, vector in weights.items():
        if cell != positive:
            require(sum(vector) == 0, "Walsh coefficients fail to cancel")

    diagonals = [product(range(1, p), repeat=2) for p in primes]
    for diagonal in product(*diagonals):
        # Unipotent entries do not affect any of these characters.
        signs = [(legendre(a, p), legendre(d, p)) for p, (a, d) in zip(primes, diagonal)]
        base = prod(line for line, _ in signs)
        cell = tuple(line * quotient for line, quotient in signs)
        counts[cell, base] += 1
        rows = []
        for mask in masks:
            choices = (quotient if selected else line
                       for selected, (line, quotient) in zip(mask, signs))
            rows.append(prod(choices))
        for target, vector in weights.items():
            value = sum(w * character for w, character in zip(vector, rows))
            expected = len(masks) * base if target == cell else 0
            require(value == expected, f"incorrect Walsh value on {diagonal}")

    diagonals_per_cell = prod((p - 1)**2 for p in primes) // len(masks)
    for cell in cells:
        for base in (1, -1):
            require(2 * counts[cell, base] == diagonals_per_cell, "unequal sign counts")
    degree = prod(p + 1 for p in primes)
    print(f"primes={primes}: degree {degree}, {len(masks)} rows, "
          f"disjoint zero-sum basis size {len(masks) - 1}, {diagonals_per_cell} diagonals per cell")


if __name__ == "__main__":
    for ell, irreducible_prime, jordan_prime in ((3, 5, 7), (5, 3, 11), (7, 5, 79)):
        check_witnesses(ell, irreducible_prime, jordan_prime)
        check_induced_traces(ell)
    for primes in ((3,), (3, 5), (3, 5, 7)):
        check_walsh_cells(primes)
