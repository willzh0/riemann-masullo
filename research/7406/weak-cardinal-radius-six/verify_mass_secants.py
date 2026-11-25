# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint==0.8.0"]
# ///
"""Independently enclose the actual weak squared norm in the finite window using mass differences."""
from functools import lru_cache
import json

from flint import acb, arb, arb_mat, ctx


def rational(numerator, denominator):
    return arb(numerator) / denominator


def checked_ordinates(start, count):
    values = list(acb.zeta_zeros(start, count))
    assert len(values) == count
    assert all(z.real == rational(1, 2) for z in values)
    heights = [z.imag for z in values]
    assert all(a < b for a, b in zip(heights, heights[1:]))
    return dict(zip(range(start, start + count), heights))


def calibrate(heights, targets):
    pi = arb.pi()
    theta = rational(3, 2)
    step = rational(1, 2**24)
    mass_ratio = (1 + step) ** theta
    lower_slope = 1 - 1 / mass_ratio
    upper_slope = mass_ratio - 1
    assert upper_slope > theta * step

    @lru_cache(None)
    def gram_entry(i, j, advanced):
        b = 1 + step if advanced else arb(1)
        if i == j:
            return 1 / (pi * b)
        d = abs(heights[j] - heights[i])
        v = d * b.sqrt()
        return d * v.bessel_k(1) / (pi * b.sqrt())

    bounds = []
    for w in targets:
        if min(heights) == 1:
            assert heights[w] - 6 > 0
        else:
            assert heights[w] - 6 > heights[min(heights)]
        assert heights[w] + 6 < heights[max(heights)]
        E = []
        for i, y in heights.items():
            if i == w:
                E.append(i)
                continue
            d = abs(y - heights[w])
            assert d < 6 or d > 6
            if d < 6:
                E.append(i)
        rhs = arb_mat([[int(i == w)] for i in E])
        def energy(advanced):
            G = arb_mat([[gram_entry(min(i, j), max(i, j), advanced)
                          for j in E] for i in E])
            return G.solve(rhs)[E.index(w), 0]
        difference = energy(True) - energy(False)
        lower, upper = difference / upper_slope, difference / lower_slope
        assert lower > 0 and upper.is_finite()
        bounds.append((w, lower, upper, E))
    return bounds


def main():
    ctx.prec = 144
    assert arb(300).zeta_nzeros() == 138
    early = calibrate(checked_ordinates(1, 139), range(1, 129))
    pair = calibrate(checked_ordinates(6702, 16), (6709, 6710))
    ceiling = rational(419, 200)
    floors = [rational(429, 20), rational(93, 4)]
    assert all(upper < ceiling for _, _, upper, _ in early)
    assert early[0][3] == [1]
    for (_, lower, _, sites), floor in zip(pair, floors):
        assert lower > floor and sites == list(range(6703, 6717))
    delta = 13 * arb(3).sqrt() / 48
    assert (1 + delta) * ceiling.sqrt() < rational(213, 100)
    assert (1 - delta) * floors[0].sqrt() > rational(245, 100)
    assert (1 - delta) * floors[1].sqrt() > rational(255, 100)
    print(json.dumps({
        "bits": ctx.prec, "mass_step": "2^-24", "physical_radius": 6,
        "early_indices": [1, 128], "local_squared_norm_ceiling": "2.095",
        "early_full_weak_norm_strict_upper": "2.13",
        "lehmer_indices": [6709, 6710], "local_sites_at_each": [6703, 6716],
        "local_squared_norm_strict_lowers": ["21.45","23.25"],
        "full_weak_norm_strict_lowers": ["2.45","2.55"]}, indent=2))


if __name__ == "__main__":
    main()
