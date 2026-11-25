# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint==0.8.0"]
# ///
"""Bound the absolute quartic zero spectrum through height 20,000,000.

Run 'uv run verify_quartic_low_spectrum.py' to print the JSON
receipt. The quartic character has modulus 5 and chi(2) = i.

Platt, Theorem 7.1, places these zeros on the critical line. This computation
covers that line from -22 to 22 and applies Bennett--Martin--O'Bryant--
Rechnitzer, Theorem 1.1, to the remaining ordinates. The published bounds
and URLs appear in the receipt.
"""

import argparse
import json
from functools import lru_cache

import flint
from flint import acb, acb_series, arb, ctx, fmpq


MODULUS = 5
CUTOFF = 22
VERIFIED_HEIGHT = 20_000_000
PRECISION = 128


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def quartic_l(s):
    values = (1, acb(0, 1), acb(0, -1), -1)
    hurwitz = sum(
        value * s.zeta(fmpq(r, MODULUS))
        for r, value in enumerate(values, start=1)
    )
    return (-arb(MODULUS).log() * s).exp() * hurwitz


def critical_point(t):
    return acb(fmpq(1, 2), t)


@lru_cache(maxsize=None)
def hardy_sign(rational_t):
    # The odd-character functional equation makes this normalization real.
    t = arb(rational_t)
    root_five = arb(5).sqrt()
    epsilon = acb(((5 + root_five) / 10).sqrt(), ((5 - root_five) / 10).sqrt())
    gamma = acb(fmpq(3, 4), t / 2).gamma()
    phase = acb(0, (arb(5) / arb.pi()).log() * t / 2).exp()
    hardy = (
        epsilon.sqrt().conjugate() * gamma / abs(gamma) * phase
        * quartic_l(critical_point(t))
    ).real
    if hardy > 0:
        return 1
    if hardy < 0:
        return -1
    raise ArithmeticError(f"Hardy endpoint sign undecided at {rational_t}")


def root_bracket(left, right):
    require(hardy_sign(left) != hardy_sign(right), "missing bracket sign change")
    for _ in range(25):
        middle = (left + right) / 2
        if hardy_sign(middle) == hardy_sign(left):
            left = middle
        else:
            right = middle
    return left, right


def rational_ball(left, right):
    return arb((left + right) / 2, (right - left) / 2)


def enumerate_low_zeros():
    roots = []
    excluded = 0
    derivative_certified = 0

    def cover(left, right, depth=0):
        nonlocal excluded, derivative_certified
        middle = (left + right) / 2
        s = critical_point(rational_ball(left, right))
        if abs(quartic_l(s)) > 0:
            excluded += 1
            return
        require(depth <= 14, f"unresolved interval [{left}, {right}]")
        if right - left <= fmpq(1, 32):
            derivative = quartic_l(acb_series([s, 1]))[1]
            anchor = quartic_l(acb_series([critical_point(arb(middle)), 1]))[1]
            # Im(L(1/2+it) conjugate(anchor)) has positive derivative.
            # There is at most one zero, necessarily simple. A simple zero
            # reverses the sign of the real Hardy normalization.
            if (derivative * anchor.conjugate()).real > 0:
                derivative_certified += 1
                if hardy_sign(left) != hardy_sign(right):
                    roots.append(root_bracket(left, right))
                return
        cover(left, middle, depth + 1)
        cover(middle, right, depth + 1)

    for n in range(-CUTOFF, CUTOFF):
        cover(fmpq(n), fmpq(n + 1))
    return roots, excluded, derivative_certified


def inverse_cube_tail(count):
    # With N(t)=F(t)+error(t), partial summation at the exact N(T) gives
    # integral(t^-3 dF) + [F(T)-N(T)+B+d/3]/T^3. Concavity bounds
    # |error(t)| <= B + d log(t/T) for t >= T.
    pi = arb.pi()
    t = arb(CUTOFF)
    ell = (MODULUS * (t + 2) / (2 * pi)).log()
    require(ell > fmpq(1567, 1000), "outside the BMOR upper-bound regime")
    main = t / pi * ((MODULUS * t / (2 * pi)).log() - 1) + arb(1) / 4
    coefficient = fmpq(22737, 100000)
    error_at_t = coefficient * ell + 2 * (1 + ell).log() - arb(1) / 2
    error_slope = coefficient + 2 / (1 + ell)
    integral = ((MODULUS * t / (2 * pi)).log() + arb(1) / 2) / (2 * pi * t**2)
    return integral + (main - count + error_at_t + error_slope / 3) / t**3


def main(bits):
    require(flint.__version__ == "0.8.0", "this replay uses python-flint 0.8.0")
    ctx.prec = bits
    ctx.cap = 2
    roots, excluded, derivative_certified = enumerate_low_zeros()
    require(len(roots) == 13, "unexpected zero count in the closed interval")
    absolute_mass = arb(0)
    for left, right in roots:
        rho = critical_point(rational_ball(left, right))
        kernel = (acb(2) ** (1 - rho) - 1) / ((1 - rho) * rho * (1 + rho))
        absolute_mass += abs(kernel)
    tail = inverse_cube_tail(len(roots))
    # On the verified critical line |2^(1-rho)-1| <= 1+sqrt(2);
    # |(1-rho)rho(1+rho)| >= |Im rho|^3.
    upper = absolute_mass + (1 + arb(2).sqrt()) * tail
    require(absolute_mass < fmpq(46048078, 10**9), "finite zero sum too large")
    require(tail < fmpq(1430297, 10**9), "inverse-cube tail too large")
    require(upper < fmpq(49502, 10**6), "combined bound too large")

    receipt = {
        "python_flint": flint.__version__,
        "precision_bits": bits,
        "character": "primitive modulo 5, chi(2)=i",
        "line_scan_height": CUTOFF,
        "published_critical_line_height": VERIFIED_HEIGHT,
        "published_inputs": {
            "Platt_theorem_7_1": "https://arxiv.org/pdf/1305.3087#page=14",
            "BMOR_theorem_1_1": "https://arxiv.org/pdf/2005.02989#page=2",
        },
        "nonvanishing_cells": excluded,
        "derivative_certified_cells": derivative_certified,
        "accepted_cells": excluded + derivative_certified,
        "nontrivial_zeros_counted_with_multiplicity": len(roots),
        "rational_ordinate_brackets": [[str(left), str(right)] for left, right in roots],
        "finite_absolute_mass": str(absolute_mass),
        "inverse_cube_tail_upper_enclosure": str(tail),
        "combined_upper_enclosure": str(upper),
        "strict_rational_bound": "49502/1000000",
    }
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, choices=(128, 192), default=PRECISION)
    main(parser.parse_args().precision)
