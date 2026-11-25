"""Certify a quartic Hardy-space trial using the finite Laguerre table."""
import argparse
import json
from pathlib import Path

from flint import acb, arb, fmpq
from quartic_coeffs import coefficient_row


def certify(trial, bits):
    degree = trial["degree"]
    denominator = trial["denominator"]
    assert denominator > 0 and 0 <= trial["trial_degree"] < degree
    assert len(trial["numerators"]) == trial["trial_degree"] + 1
    row, analytic_error, inputs = coefficient_row(degree, bits)
    multipliers = [acb(fmpq(x, denominator), fmpq(y, denominator))
                   for x, y in trial["numerators"]]
    visible_squared = arb(0)
    for j in range(degree + 1):
        residual = acb(int(j == 0))
        for k in range(min(j + 1, len(multipliers))):
            residual -= multipliers[k] * row[j-k]
        visible_squared += abs(residual)**2
    sizes = [abs(value) for value in multipliers]
    error = analytic_error * (arb(degree + 1).sqrt()) * sum(sizes)
    invisible = sum(6 * size / ((degree-k)*(degree-k+1))
                    for k, size in enumerate(sizes))
    squared = (visible_squared.sqrt() + error)**2 + invisible**2
    assert squared < 1
    green = -(1 - squared).log() / 2
    return {
        "coefficient_degree": degree,
        "trial_degree": len(sizes) - 1,
        "positive_integer_bases": inputs,
        "requested_bits": bits,
        "analytic_coefficient_error": analytic_error.str(25),
        "visible_finite_norm": visible_squared.sqrt().str(25),
        "visible_analytic_error": error.str(25),
        "tail_norm_upper": invisible.str(25),
        "squared_distance_bound": squared.str(25),
        "green_bound": green.str(25),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trial", type=Path, required=True)
    parser.add_argument("--bits", type=int, default=128)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    assert args.bits >= 64
    receipt = certify(json.loads(args.trial.read_text(encoding="utf8")), args.bits)
    args.out.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf8")
    print(receipt["squared_distance_bound"], receipt["green_bound"])
