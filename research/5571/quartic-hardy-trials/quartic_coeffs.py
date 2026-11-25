"""Enclose the Hardy coefficients for χ(2)=i mod 5 by finite arithmetic."""
import argparse
import json
from math import comb
from pathlib import Path
from flint import acb, arb, ctx, fmpq, fmpz_poly


def coefficient_row(degree, bits):
    iterations = 8 * (degree + 1)
    ctx.prec = bits + 2 * iterations + 4 * degree
    denominator = 3 ** iterations
    cyclotomic = fmpz_poly([1, 1, 1, 1, 1])
    remainder_base = fmpz_poly([2, -1, -1, -1, -1])
    exact, remainder = divmod(fmpz_poly([denominator]) - remainder_base ** iterations,
                              cyclotomic)
    assert not remainder
    real = exact * fmpz_poly([0, 1, 1, 1])
    imag = exact * fmpz_poly([0, 0, 1])
    largest = 4 * iterations - 1
    assert real.degree() == largest
    sums = [acb(0) for _ in range(degree + 1)]
    for k in range(1, largest + 1):
        scale = denominator * k * k
        coefficient = acb(fmpq(real[k], scale), fmpq(imag[k], scale))
        x = 3 * arb(k).log()
        previous, current = arb(1), -x
        sums[0] += coefficient
        if degree:
            sums[1] += coefficient * current
        for j in range(1, degree):
            following = ((2*j - x)*current - (j-1)*previous)/(j+1)
            sums[j+1] += coefficient * following
            previous, current = current, following
    row = [
        sum(((-1)**k)*comb(5, k)*sums[j-k] for k in range(min(5, j) + 1)) / 243
        for j in range(degree + 1)
    ]
    assert all(abs(v.rad()) < arb(2) ** (-bits) for v in row)
    # Every ball encloses the finite expression. An additional complex norm
    # error from analytic truncation is proved in README.md for each row entry.
    err = 8 * arb(fmpq(2, 3)) ** iterations * arb(5) ** degree
    assert err <= arb(4) ** (-degree)
    return row, err, largest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--degree', type=int, required=True)
    parser.add_argument('--bits', type=int, default=128)
    parser.add_argument('--out', type=Path, required=True)
    ns = parser.parse_args()
    assert ns.degree >= 1 and ns.bits >= 64
    row, error, largest = coefficient_row(ns.degree, ns.bits)
    data = {
        'degree': ns.degree,
        'output_bits': ns.bits,
        'working_bits': ctx.prec,
        'positive_integer_bases': largest,
        'coefficient_analytic_error': str(error.str(25)),
        'finite_c0_real': row[0].real.str(32),
        'finite_c0_imag': row[0].imag.str(32),
        'midpoints_for_trial_selection': [[float(x.real), float(x.imag)] for x in row]
    }
    ns.out.write_text(json.dumps(data, indent=2)+'\n', encoding='utf8')


if __name__ == '__main__':
    main()
