"""Verify the exact prime coefficients of the fourth-power annular identity."""
from fractions import Fraction
from math import isqrt


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def kernel(u):
    if 2 * u <= 1:
        return 1 - 3 * u / 2
    if u <= 1:
        return (1 - u) ** 2 / (2 * u)
    return Fraction(0)


checked = interior = endpoints = 0
for j in (*range(1, 26), 29, 36, 40):
    x, n_lower = j**4, j**3
    for p in filter(prime, range(2, j + 6)):
        # Directly enumerate the true integers of the trapezoid.
        first = max(0, x - p * n_lower)
        last = max(0, x - 2 * p * n_lower)
        middle = sum(max(0, x - p * n) for n in range(n_lower + 1, 2 * n_lower))
        enumerated = Fraction(first + last, 2) + middle
        u = Fraction(p, j)
        linear_mass = j**7 * kernel(u)
        theta = Fraction(x % p, p)
        correction = Fraction(0)
        if j < 2 * p and p < j:
            correction = p * theta * (1 - theta) / 2
            assert 0 <= correction <= Fraction(p, 8)
            interior += 1
        if p == j or 2 * p == j:
            endpoints += 1
        assert enumerated == linear_mass + correction, (j, p)
        assert kernel(u) >= 0
        checked += 1
print(f"Verified {checked} exact logarithmic prime coefficients, including "
      f"{interior} interior corrections and {endpoints} endpoint cases.")
