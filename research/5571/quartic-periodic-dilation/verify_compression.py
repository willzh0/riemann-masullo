"""Exact coefficient check for the finite Moebius elimination in compression.md.

The divisor identity holds for arbitrary weights. Use an exact rational taper
and dyadic scale choices to check every coefficient before using a smooth taper.
"""
from collections import defaultdict
from fractions import Fraction
from math import isqrt


def mobius(n):
    primes = 0
    for p in range(2, isqrt(n) + 1):
        if n % p:
            continue
        if n % (p*p) == 0:
            return 0
        n //= p
        primes += 1
    return (-1)**(primes + (n > 1))


def chi(k):
    return [0, 1, 1j, -1j, -1][k % 5]


def taper(r):
    return max(Fraction(0), min(Fraction(1), 2-r))


def check(y, scale):
    # Arbitrary inverse-scale multipliers with scale_d*d >= y.
    scales = {d: Fraction(scale * (d+2), 3*d) for d in range(1,y+1)}
    cut = max(int(2 * d * scales[d]) for d in scales)
    expanded = defaultdict(Fraction)
    for d, n_scale in scales.items():
        for n in range(1, int(2*n_scale)+1):
            expanded[d*n] += mobius(d)*taper(Fraction(n)/n_scale)
    for m in range(1, cut+1):
        direct = sum(mobius(d) * taper(Fraction(m)/(d * scales[d])) for d in scales if m % d == 0)
        assert direct == expanded[m]
        if m <= y:
            assert direct == int(m == 1)
        if y < m <= scale and all(m % p for p in range(2,isqrt(m)+1)):
            assert direct == 1
        for d in scales:
            if m % d == 0:
                assert chi(d) * chi(m//d) == chi(m)
    return cut


if __name__ == "__main__":
    for y, scale in [(4,17), (12,55), (32,181), (79,401)]:
        print("Y", y, "all coefficients through", check(y,scale))
