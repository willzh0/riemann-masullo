"""Enclose the quartic Cauchy-weighted critical-line log mean of #7696."""
from argparse import ArgumentParser
import json

from flint import acb, arb, ctx, dirichlet_char


def inverse_square_tail(height):
    """BMOR, Counting zeros of Dirichlet L-functions, Theorem 1.1."""
    ell = (5 * (height + 2) / (2 * arb.pi())).log()
    size = arb(".22737") * ell + 2 * (1 + ell).log() - arb(1) / 2
    slope = arb(".22737") + 2 / (1 + ell)
    center = ((5 * height / (2 * arb.pi())).log() + 1) / (arb.pi() * height)
    radius = (2 * size + slope / 2) / height**2
    return center + radius


def independent_log_range(terms):
    """Use complete periods; max absolute prefix per period is sqrt(2)."""
    assert terms % 5 == 0 and terms > 0
    real, imag = arb(0), arb(0)
    for k in range(0, terms, 5):
        real += arb(1) / (k + 1)**2 - arb(1) / (k + 4)**2
        imag += arb(1) / (k + 2)**2 - arb(1) / (k + 3)**2
    size = abs(acb(real, imag))
    radius = arb(2).sqrt() / (terms + 1)**2
    assert size > radius
    return (size - radius).log(), (size + radius).log()


def calculation(bits):
    ctx.prec = bits
    n = 1_000_000
    log_low, log_high = independent_log_range(n)
    direct = abs(acb(2).dirichlet_l(dirichlet_char(5, 2))).log()
    assert log_low < direct < log_high
    tail = inverse_square_tail(arb(20_000_000))
    green = arb(3) * tail / 4
    assert green < arb("2.09879293e-7")
    assert arb("-.030764312543") < direct and direct + green < arb("-.030764102663")
    assert arb("-.030764312545") < log_low
    assert log_high + green < arb("-.030764102661")
    hardy = -(-2 * green).expm1()
    assert hardy < arb("4.1975850e-7") and hardy.sqrt() < arb(".000647888")
    return {
        "Hardy_squared_distance_upper": str(hardy),
        "Hardy_distance_upper": str(hardy.sqrt()),
        "precision_bits": bits,
        "direct_log_abs_L2": str(direct),
        "periodic_terms": n,
        "periodic_lower": str(log_low),
        "periodic_upper": str(log_high),
        "whole_divisor_inverse_square_tail_upper": str(tail),
        "Green_defect_upper": str(green),
        "log_mean_upper_using_L2": str(direct + green),
    }


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--bits", type=int, default=192)
    opts = parser.parse_args()
    assert opts.bits >= 96
    result = calculation(opts.bits)
    print(json.dumps(result, indent=2))
