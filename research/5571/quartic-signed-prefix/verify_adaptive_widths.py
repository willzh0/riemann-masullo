# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint==0.8.0"]
# ///
"""Outward checks for actual compensated Gaussian prime samples."""

from fractions import Fraction
from math import isqrt

import flint
from flint import acb, arb, ctx, fmpq


def primes(bound):
    return [
        n for n in range(2, bound + 1)
        if all(n % d for d in range(2, isqrt(n) + 1))
    ]


def norm_kernel(ratio, variance):
    # h ~ N(0,variance). K(ratio*exp(-h)) changes form at log(ratio)
    # and log(2*ratio). Tilted Gaussian tail moments integrate each piece.
    left, right = ratio.log(), (2 * ratio).log()
    scale = (2 * variance).sqrt()

    def tail(h, a):
        return (a*a*variance/2).exp() * ((h - a*variance)/scale).erfc()/2

    low = tail(right, 0) - 3*ratio*tail(right, -1)/2
    mid = (
        (tail(left, 1) - tail(right, 1))/(2*ratio)
        - (tail(left, 0) - tail(right, 0))
        + ratio*(tail(left, -1) - tail(right, -1))/2
    )
    return low + mid


def compensated(ratio, variance):
    c = (-variance/2).exp()
    return (1+c)*norm_kernel(ratio, variance) - c*norm_kernel(ratio, 2*variance)


def quadrature_slice(prime, x, left, right, direction):
    # A lower bound on the whole terminal integral comes from this interval
    # alone. Subdivide in variance and bound each entire cell from below.
    cuts = 100
    step = (right - left)/cuts
    lower_bound = arb(0)
    for j in range(cuts):
        v = arb(left + (j+fmpq(1, 2))*step, step/2)
        value = direction*arb(prime).log()*compensated(arb(prime)/x, v)
        assert value > 0
        lower_bound += (step*(-4*v).exp()*value).lower()
    return lower_bound


def run(bits):
    ctx.prec = bits
    # These rational checks use the stricter of the two historical bounds
    # on 1/|rho|^2 for any one low zero and the actual verified height.
    bound = Fraction(203222, 10**6)
    assert bound/(4*(2-bound)) < Fraction(1, 35)
    assert Fraction(1, 2*(20_000_000**2-1)) < Fraction(1, 35)
    assert Fraction(1, 41) + Fraction(1, 41**2) < Fraction(1, 35)

    real = {1: 1, 2: 0, 3: 0, 4: -1, 0: 0}
    assert [(p, real[p % 5]) for p in primes(16) if real[p % 5]] == [(11, 1)]
    neg = quadrature_slice(11, 4, fmpq(49, 100), fmpq(1, 2), -1)
    pos = quadrature_slice(11, 4, fmpq(119, 100), fmpq(6, 5), 1)
    assert neg > fmpq(1, 100000) and pos > fmpq(1, 1000000)

    character = [acb(0), acb(1), acb(0, 1), acb(0, -1), acb(-1)]
    x, n, a = 2, 4096, 5
    v = arb(x).log()
    measured = acb(0)
    for p in primes(n):
        measured += character[p % 5]*arb(p).log()*compensated(arb(p)/x, v)
    c = (-v/2).exp()
    moment = (1+c)*(((1+a)**2)*v/2).exp() + c*(((1+a)**2)*v).exp()
    tail = 2*arb(x)**(a+1)/arb(n)**a * moment
    assert tail < fmpq(6, 10**6)
    print("precision", bits)
    print("  A_minus(4), lower from [0.49,0.50]:", neg.str(14))
    print("  A_plus(4), lower from [1.19,1.20]:", pos.str(14))
    print("  Q at x=2, variance log 2, primes through 4096:", measured.str(14))
    print("  omitted complex modulus upper:", tail.str(14))


if __name__ == "__main__":
    assert flint.__version__ == "0.8.0"
    for precision in (128, 192):
        run(precision)
