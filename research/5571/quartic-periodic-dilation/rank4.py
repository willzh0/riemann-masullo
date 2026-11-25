"""Certify the kernel of the four critical-zero evaluations of period-five weights."""

import argparse
import json
from fractions import Fraction
from pathlib import Path

import flint
from flint import acb, acb_mat, acb_series, arb, ctx, fmpq


# Integer left numerators from the 13-zero calibration, denominator 2**24.
# The brackets are seeds only: all signs, slopes and mirror bounds are replayed.
SEEDS = (-330998614, -285143952, -236818193, -189295591)
SIGMA_LOWER = Fraction(10653, 12500)


def ball(q):
    return arb(fmpq(q.numerator, q.denominator))


def residue_rows(s):
    scale = (-s * arb(5).log()).exp()
    return [scale * s.zeta(fmpq(r, 5)) for r in range(1, 6)]


def quartic(s):
    row = residue_rows(s)
    return row[0] - row[3] + acb(0, 1) * (row[1] - row[2])


def quadratic(s):
    row = residue_rows(s)
    return row[0] - row[1] - row[2] + row[3]


def hardy(t):
    root_number = acb(((5+arb(5).sqrt())/10).sqrt(),
                      ((5-arb(5).sqrt())/10).sqrt())
    s = acb(arb(1)/2, t)
    gamma = acb(arb(3)/4, t/2).gamma()
    phase = acb(0, t/2*(arb(5)/arb.pi()).log()).exp()
    return (root_number.sqrt().conjugate()*phase*gamma/abs(gamma)*quartic(s)).real


def sign(value):
    if value > 0:
        return 1
    if value < 0:
        return -1
    raise AssertionError("Hardy sign unresolved")


def isolate(seed):
    left = Fraction(seed, 2**24)
    right = Fraction(seed+1, 2**24)
    initial_sign = sign(hardy(ball(left)))
    assert sign(hardy(ball(right))) == -initial_sign
    for _ in range(24):
        mid = (left+right)/2
        if sign(hardy(ball(mid))) == initial_sign:
            left = mid
        else:
            right = mid
    t = arb(ball((left+right)/2), ball((right-left)/2))
    s = acb(arb(1)/2, t)
    left_value, right_value = hardy(ball(left)), hardy(ball(right))
    assert sign(left_value) == initial_sign and sign(right_value) == -initial_sign

    # Nonvanishing derivative throughout the bracket gives simplicity at any
    # Hardy root supplied by the two endpoint signs.  The tangent projection
    # below gives injectivity along the whole interval by the mean-value theorem.
    derivative = quartic(acb_series([s, 1]))[1]
    mid_derivative = quartic(acb_series([acb(arb(1)/2, ball((left+right)/2)), 1]))[1]
    directional = (derivative * mid_derivative.conjugate()).real
    assert directional > 0
    mirror = abs(quartic(s.conjugate()))
    assert abs(derivative) > fmpq(1, 10) and mirror > fmpq(1, 10)
    kappa = fmpq(21, 100)
    moved = (s - kappa) / (1-kappa)
    exclusions = {
        "eta_at_twice_root": abs(quadratic(2*s)),
        "chi_at_moved": abs(quartic(moved)),
        "chibar_at_moved": abs(quartic(moved.conjugate())),
        "eta_at_twice_moved": abs(quadratic(2*moved)),
    }
    for value in exclusions.values():
        assert value > fmpq(1, 1000)
    assert abs(s*(1+s)) < 400
    return residue_rows(s)[1:], {
        "denominator": 2**48,
        "left_numerator": int(left * 2**48),
        "right_numerator": int(right * 2**48),
        "hardy_left": str(left_value),
        "hardy_right": str(right_value),
        "Lprime_abs": str(abs(derivative)),
        "Lprime_direction": str(directional),
        "reflected_L_abs": str(mirror),
        "mean_term_nonvanishing": {key: str(value) for key, value in exclusions.items()},
    }


def certify(bits):
    ctx.prec, ctx.cap = bits, 2
    results = [isolate(seed) for seed in SEEDS]
    rows = [record[0] for record in results]
    matrix = acb_mat(rows)
    gram = [[sum(rows[k][i].conjugate()*rows[k][j] for k in range(4))
             for j in range(4)] for i in range(4)]
    alpha = ball(SIGMA_LOWER)
    for i in range(4):
        gram[i][i] -= alpha**2
    # For the true point choices this matrix is Hermitian.  Arb's complex
    # determinant ball contains each real leading minor, so Sylvester applies.
    minors = []
    for size in range(1, 5):
        block = acb_mat([row[:size] for row in gram[:size]])
        value = block.det()
        assert value.imag.contains(0) and value.real > 0
        minors.append(str(value.real))
    determinant = abs(matrix.det())
    assert determinant > fmpq(3487, 1000)
    return {
        "bits": bits, "roots": [record[1] for record in results], "residue_columns": [2,3,4,5],
        "matrix_determinant_abs": str(determinant), "least_singular_value_lower": str(SIGMA_LOWER),
        "shifted_gram_leading_minors": minors,
        "maximum_multiplier_per_quotient_norm_lower": str(SIGMA_LOWER/2),
        "fixed_phase_oscillation_per_quotient_norm_lower": str(SIGMA_LOWER/1600),
        "fixed_phase_prefix_limsup_per_quotient_norm_lower": str(SIGMA_LOWER/22400),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = {
        "version": flint.__version__, "seed_sha": "53cac8a4461b84ad1d9c96ea2305f48e82ba4a31",
        "seed_denominator": 2**24, "seed_left_numerators": SEEDS,
        "runs": [certify(bits) for bits in (128, 192)],
    }
    output = json.dumps(data, indent=2) + "\n"
    if args.output:
        args.output.write_bytes(output.encode("utf-8"))
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
