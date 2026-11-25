"""Check a fixed coordinate and the finite constants in the original ideal grid schedule."""
import argparse
import json
from fractions import Fraction
from pathlib import Path
from flint import arb, ctx


def verify(trial, receipt):
    n = 15999999
    M = 2*n+1
    precision = 6*(M+1)
    j = (precision+2).bit_length()
    u = 1 << j
    q = trial["denominator"]
    a = trial["numerators"]
    energy = Fraction(sum((k+1)**2*(x*x+y*y) for k,(x,y) in enumerate(a)), q*q)
    assert (n+1)**3 % q == 0 and energy <= n+1
    assert max(max(abs(x), abs(y)) for x,y in a) <= (n+1)*q
    assert u >= 2**20 and 4 * 52**4 <= 32 * u and 36*52*u < 4**min(u,100)
    assert (52*52*u < 4**min(u,100)) and (precision+1) <= u
    assert M >= 80 and 4**80 >= 10**40
    ctx.prec = 192
    error = arb(1) / 10**40
    true_residual = arb(receipt["squared_distance_bound"]).sqrt()
    coeff_mass = arb(sum(abs(x)+abs(y) for x,y in a))/q
    finite_grid_bound = true_residual + arb(M+1).sqrt()*coeff_mass*error
    row_correction = (2*arb((n+1)*(M+1)).sqrt()*error
                      + arb(32)/(9*arb(n+1).sqrt()))
    argument = (finite_grid_bound+row_correction)**2
    assert argument < 1
    return {
        "original_stage": n, "normalizer_exponent": 5, "row_degree": M,
        "extrapolate_precision_input": precision, "dyadic_scale": u,
        "exact_grid_trial_energy": str(energy),
        "grid_trial_denominator": q, "verified_row_error_replacement": "10^-40",
        "finite_grid_norm_bound": finite_grid_bound.str(25),
        "original_row_correction_bound": row_correction.str(25),
        "upper_argument_bound": argument.str(25),
        "green_upper_via_original_grid": (-(1-argument).log()/2).str(25),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trial", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    result = verify(json.loads(args.trial.read_text(encoding="utf8")),
                    json.loads(args.receipt.read_text(encoding="utf8")))
    args.out.write_text(json.dumps(result,indent=2)+"\n",encoding="utf8")
    print(result["upper_argument_bound"], result["green_upper_via_original_grid"])
