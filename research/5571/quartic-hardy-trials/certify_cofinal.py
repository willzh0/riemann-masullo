"""Verify the rational bounds for the explicit cofinal transfer to the canonical Hardy grid."""
from fractions import Fraction
from pathlib import Path
import json
from math import isqrt


def ceiling_sqrt(value, digits):
    scale = 10**digits
    return Fraction(isqrt((value.numerator*scale**2)//value.denominator)+1, scale)


def verify(here):
    trial = json.loads((here/"dilates-1-512.json").read_text(encoding="utf8"))
    physical = json.loads((here/"dilates-1-512-period-receipt.json").read_text(encoding="utf8"))
    A = Fraction(sum(abs(a)+abs(b) for _,a,b in trial["terms"]),
                 trial["coefficient_denominator"])
    assert A < 56 and max(d for d,_,_ in trial["terms"]) == 512
    squared = Fraction(physical["squared_distance_upper_exact"])
    T = 10**36
    inv_gap = 10**88
    D = 10**92
    n0 = 10**1200
    M = 56*(6*inv_gap)**5
    assert M < 10**446 and M*M*(D+1)**3 <= n0
    # log(1+1/(2*inv_gap)) >= 1/(4*inv_gap). Since e>2.7,
    # bound the Taylor tail by a rational upper on 2*M*inv_gap*exp(-2500).
    assert D == 2500*4*inv_gap
    tail = 2*M*inv_gap*Fraction(10,27)**2500
    assert tail < Fraction(1,10**500)
    physical_norm = ceiling_sqrt(squared, 30)
    central = Fraction(3000*(T+2)**2,inv_gap)
    high = Fraction(3*56*11,10**9)
    assert T == (10**9)**4
    rounding = Fraction(2*(D+1),n0**3)
    # sqrt(2(n+1))<=2sqrt(n+1), 4^(2n+1)>=(n+1)^2.
    root_n0 = 10**600
    assert root_n0*root_n0 == n0
    row = Fraction(2*M*(D+1),n0*root_n0)
    original_correction = Fraction(3,n0) + Fraction(4,root_n0)
    argument = (physical_norm+central+high+tail+rounding+row+original_correction)**2
    # Work with a compact outward rational for the logarithm enclosure.
    upper = Fraction((argument*10**15).__ceil__(),10**15)
    green = (sum(upper**j/j for j in range(1,12))+upper**12/(12*(1-upper)))/2
    return {"stage_at_least": "10^1200", "outer_exponent": 5, "height": "10^36",
            "disk_gap": "10^-88", "trial_degree_at_most": "10^92",
            "rational_norm_upper_for_original_physical_trial": str(physical_norm),
            "low_frequency_error": str(central), "high_frequency_error": str(high),
            "upper_argument_ceiling_1e15": (upper*10**15).__ceil__(),
            "green_bound_via_original_grid_ceiling_1e12": (green*10**12).__ceil__()}


if __name__ == "__main__":
    root = Path(__file__).resolve().parent
    result = verify(root)
    print(json.dumps(result,indent=2))
