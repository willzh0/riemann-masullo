"""Certify a finite dilation trial for the quartic character by exact integer sums."""
import argparse
import json
from array import array
from fractions import Fraction
from pathlib import Path


def certify(trial, cutoff, bits):
    mesh = trial["dilation_denominator"]
    denominator = trial["coefficient_denominator"]
    terms = trial["terms"]
    assert mesh > 0 and denominator > 0 and all(d >= mesh for d, _, _ in terms)
    assert 0 < cutoff and 32 <= bits
    weight = sum(abs(a)+abs(b) for _, a, b in terms)
    assert weight < 2**62
    end = mesh * cutoff
    bumps_re = array("q", [0])*(end+1)
    bumps_im = array("q", [0])*(end+1)
    for d, a, b in terms:
        for j, (cx, cy) in enumerate(((a,b),(-b,a),(b,-a),(-a,-b)), start=1):
            for n in range(d*j, end+1, 5*d):
                bumps_re[n] += cx
                bumps_im[n] += cy
    u, v = mesh*denominator, 0
    total = 0
    dyadic = 1 << bits
    for n in range(mesh, end+1):
        u -= n * bumps_re[n]
        v -= n * bumps_im[n]
        top = dyadic * (u*u+v*v)*(3*n*n+3*n+1)
        bottom = (n*(n+1))**3
        total += (top+bottom-1)//bottom
    finite = Fraction(total*mesh, dyadic*denominator**2)
    reciprocal = Fraction(mesh, end+1)
    amplitude = Fraction(3*weight, 2*denominator)
    tail = reciprocal**3 + 3*amplitude*reciprocal**2 + 3*amplitude**2*reciprocal
    bound = finite + tail
    assert bound < 1
    # Seven explicit logarithm terms and a geometric majorant for the rest.
    green = (sum(bound**j/j for j in range(1,8)) + bound**8/(8*(1-bound)))/2
    return {
        "terms": len(terms),
        "dilation_denominator": mesh,
        "summation_cutoff": cutoff,
        "rounding_bits": bits,
        "finite_upper_exact": str(finite),
        "tail_upper_exact": str(tail),
        "squared_distance_upper_exact": str(bound),
        "squared_distance_upper_ceiling_1e12": (bound*10**12).__ceil__(),
        "green_upper_ceiling_1e12": (green*10**12).__ceil__(),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trial", type=Path, required=True)
    parser.add_argument("--cutoff", type=int, default=1000000)
    parser.add_argument("--bits", type=int, default=96)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    receipt = certify(json.loads(args.trial.read_text(encoding="utf8")), args.cutoff, args.bits)
    args.out.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf8")
    print(receipt["squared_distance_upper_ceiling_1e12"], receipt["green_upper_ceiling_1e12"])
