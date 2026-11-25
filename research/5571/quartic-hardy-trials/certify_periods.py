"""Independently evaluate the finite Hardy residual by complete periods modulo five."""
import argparse
import json
from fractions import Fraction
from pathlib import Path
from math import isqrt
import numpy as np


def finite_mass(trial, cutoff, bits):
    q = trial["dilation_denominator"]
    scale = trial["coefficient_denominator"]
    terms = trial["terms"]
    end = q*cutoff
    weight = sum(abs(a)+abs(b) for _, a, b in terms)
    max_d = max(d for d, _, _ in terms)
    # Every real/imag partial-period entry has absolute value at most m+6,
    # and its exact completed character moment has modulus at most sqrt(2)*m.
    assert scale*q + 3*(end+max_d)*max(1,weight) < 2**62
    total = 0
    S_re, S_im = np.array([0,1,1,1,0]), np.array([0,0,1,0,0])
    B_re, B_im = np.array([0,1,1,1,-3]), np.array([0,0,2,-1,-1])
    for first in range(q, end+1, 12000):
        indices = np.arange(first, min(end+1, first+12000), dtype=np.int64)
        re, im = np.full_like(indices, q*scale), np.zeros_like(indices)
        for d, a, b in terms:
            quotient, residue = np.divmod(indices//d, 5)
            x = d*(quotient*(-3+5*S_re[residue]) + B_re[residue])
            y = d*(quotient*(-1+5*S_im[residue]) + B_im[residue])
            re -= a*x-b*y
            im -= a*y+b*x
        for idx, u, v in zip(indices.tolist(), re.tolist(), im.tolist()):
            top = ((u*u + v*v) << bits)*((idx+1)**3-idx**3)
            bottom = idx**3*(idx+1)**3
            total -= (-top)//bottom
    return Fraction(q*total, (1 << bits)*scale**2)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trial", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    trial = json.loads(args.trial.read_text(encoding="utf8"))
    receipt = json.loads(args.receipt.read_text(encoding="utf8"))
    result = finite_mass(trial, receipt["summation_cutoff"], receipt["rounding_bits"])
    assert result == Fraction(receipt["finite_upper_exact"])
    q = trial["dilation_denominator"]
    scale = trial["coefficient_denominator"]
    size_scale = 10**12
    norm_bounds = [(d, Fraction(isqrt((a*a+b*b)*size_scale**2)+1,scale*size_scale))
                   for d,a,b in trial["terms"]]
    # B_m equals m times a five-periodic slope plus a bounded remainder.
    # Their exact maximal norms are sqrt(20)/5 and sqrt(10)/5.
    intercept = 1 + Fraction(633,1000)*sum(Fraction(d,q)*size for d,size in norm_bounds)
    slope = Fraction(179,200)*sum(size for _,size in norm_bounds)
    reciprocal = Fraction(q, q*receipt["summation_cutoff"]+1)
    tail = intercept**2*reciprocal**3 + 3*intercept*slope*reciprocal**2 + 3*slope**2*reciprocal
    squared = result+tail
    assert squared < 1
    green = (sum(squared**j/j for j in range(1,12)) + squared**12/(12*(1-squared)))/2
    evidence = {
        "terms": len(norm_bounds),
        "summation_cutoff": receipt["summation_cutoff"],
        "rounding_bits": receipt["rounding_bits"],
        "dilation_denominator": q,
        "finite_period_sum_checked_against_progressions": str(result),
        "period_tail_bound_exact": str(tail),
        "squared_distance_upper_exact": str(squared),
        "squared_distance_upper_ceiling_1e12": (squared*10**12).__ceil__(),
        "green_upper_ceiling_1e12": (green*10**12).__ceil__(),
    }
    args.out.write_text(json.dumps(evidence,indent=2)+"\n",encoding="utf8")
    print(evidence["squared_distance_upper_ceiling_1e12"],evidence["green_upper_ceiling_1e12"])
