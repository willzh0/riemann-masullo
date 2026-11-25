"""Exact finite checks of the additive rows and analytic sector constants."""

from fractions import Fraction
from math import factorial
from math import isqrt


chi = (0, 1, 1j, -1j, -1)
for h in range(1, 5):
    eta = chi[h] ** 2
    for residue in range(5):
        value = chi[residue]
        paired = chi[(residue + h) % 5] + chi[(residue - h) % 5]
        assert 2 * paired == -value + eta * (1 + 2j) * value.conjugate()
        assert 2 * value == paired + eta * (1 + 2j) * paired.conjugate()


def exponential_lower(x, degree):
    return sum(x**k / factorial(k) for k in range(degree + 1))


assert exponential_lower(Fraction(9, 5), 6) > 6
assert exponential_lower(Fraction(24, 5), 7) > 100
assert Fraction(1, 3) + Fraction(23, 600) < Fraction(3, 8)
assert 23**2 > 2 * 16**2

# An exact rational parametrization of the phase circle tests the two divisor
# coefficients on many coincident, opposite, and unequal multiplicities.
for t_numerator in range(-25, 26):
    t = Fraction(t_numerator, 13)
    a, b = (1 - t*t)/(1 + t*t), 2*t/(1 + t*t)
    for left in range(8):
        for right in range(8):
            projected = (left + right)**2 * a*a + (left - right)**2 * b*b
            assert projected >= (left-right)**2

def prime(k):
    return k >= 2 and all(k % d for d in range(2, isqrt(k) + 1))


# Compare independently enumerated coefficients of the individual log p in
# the actual crossed sum, with exact Gaussian integers at these small sizes.
checks = 0
for x in (1, 2, 17, 100, 257, 400):
    for p in filter(prime, range(2, x + 1)):
        by_dilation = sum(chi[n % 5].conjugate() * chi[p % 5] * (x - n*p)
                          for n in range(1, x // p + 1))
        by_product = sum(chi[m % 5].conjugate() * chi[p % 5]**2 * (x-m)
                         for m in range(p, x + 1, p))
        assert by_dilation == by_product
        checks += 1

print(f"20 residue inverses, exponential and sector bounds, 3,264 phase inequalities,"
      f" and {checks} crossed logarithm coefficients passed.")
