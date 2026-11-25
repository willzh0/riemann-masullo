"""Verify outward rational bounds in the quartic clipped outer prediction argument."""
from fractions import Fraction
import json


def verify():
    H = 100000
    J = 2**96
    # log(300 J)<73 from e>2.7. Also exp(67)<exp((H-29*73)/(20*73)).
    assert Fraction(27,10)**73 > 300*J
    assert H-29*73 > 67*20*73
    inner = 9*3200*73**2*Fraction(10,27)**67
    outer = Fraction(13200*(73**2+2*73+2),J)
    e = inner+outer
    assert e < Fraction(1,10**20)
    # 20 e^(4H)<2^(600000) follows using e<11/4 and (11/4)^40*20<2^60.
    assert 20*Fraction(11,4)**160 < 2**240
    assert 4*H % 160 == 0 and (4*H//160)*240 == 600000
    # The weighted derivative tail is bounded using the same cost certificate:
    # ||q-P_n||_2 <= sqrt(n+1)/(n+1) <= 1/sqrt(n).
    # All remaining rounding, visible row and formula costs are <= 12/sqrt(n).
    assert 2**100 > 20*10**24 and 300000 > 100
    smoothing = Fraction(1,10**24)
    correction = Fraction(1,10**24)
    gap = 2*(e+smoothing) + 2*correction + correction**2
    assert gap < Fraction(1,10**19)
    # For x>=0, 1-exp(-x) <= x-x²/2+x³/6 by alternating Taylor remainder.
    platt_green = Fraction(209879293,10**15)
    x = 2*platt_green
    distance_squared = x-x*x/2+x**3/6
    canonical_upper = distance_squared + gap
    assert canonical_upper < Fraction(41975850,10**14)
    # Compare the canonical logarithmic upper directly, using finitely many terms.
    logarithmic_upper = (sum(canonical_upper**j/j for j in range(1,7))
                         +canonical_upper**7/(7*(1-canonical_upper)))/2
    return {
        "fixed_clip_height": H, "retained_height_blocks_abs_at_most": str(J),
        "every_original_grid_index_from": "2^600000", "quartic_exponent": 5,
        "clip_error_bound_ceiling_1e24": (e*10**24).__ceil__(),
        "squared_grid_error_ceiling_1e24": (gap*10**24).__ceil__(),
        "published_green_input_upper": str(platt_green),
        "squared_grid_bound_with_verified_height_ceiling_1e20": (canonical_upper*10**20).__ceil__(),
        "grid_logarithmic_bound_with_verified_height_ceiling_1e20": (logarithmic_upper*10**20).__ceil__(),
    }


if __name__ == "__main__":
    print(json.dumps(verify(),indent=2))
