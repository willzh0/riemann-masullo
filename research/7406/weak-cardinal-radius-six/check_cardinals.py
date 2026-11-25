# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint==0.8.0"]
# ///
"""Certify radius-six weak cardinal norms at the first 128 zeros and Lehmer's pair."""

import argparse
import json
from collections import Counter
from functools import cache
from pathlib import Path

import flint
from flint import acb, arb, arb_mat, ctx


CENTERS = 128
RADIUS = 6


def require(proposition, description):
    if not proposition:
        raise ArithmeticError(description)


def count_zeros(height):
    count = arb(height).zeta_nzeros().unique_fmpz()
    require(count is not None, "inconclusive zero count")
    return int(count)


def isolated_zeros(lo, hi):
    """Count with multiplicity at both endpoints and enclose consecutive indexed roots."""
    lo_count, hi_count = count_zeros(lo), count_zeros(hi)
    start = max(1, lo_count)
    roots = acb.zeta_zeros(start, hi_count + 2 - start)
    require(len(roots) == hi_count + 2 - start, "wrong number of isolating balls")
    require(all(z.real == arb(1) / 2 for z in roots), "noncentral real part")
    heights = {i: z.imag for i, z in enumerate(roots, start)}
    require(all(heights[i] < heights[i + 1] for i in range(start, hi_count + 1)),
            "overlapping zero enclosures")
    require(lo < heights[lo_count + 1] and (lo_count == 0 or heights[lo_count] < lo),
            "lower endpoint not bracketed")
    require(heights[hi_count] < hi < heights[hi_count + 1], "upper endpoint not bracketed")
    return lo_count, hi_count, heights


def kernel(b, order, distance):
    """The order of K is r - 1/2, either one or two."""
    pi = arb.pi()
    if distance.is_zero():
        return 1 / (pi * b) if order == 1 else 2 / (3 * pi * b**2)
    require(distance > 0, "unresolved off-diagonal distance")
    root_b = arb(b).sqrt()
    if order == 1:
        return distance * (root_b * distance).bessel_k(1) / (pi * root_b)
    return distance**2 * (root_b * distance).bessel_k(2) / (3 * pi * b)


def certify_positive_definite(matrix):
    """Interval LDL^T for the exact symmetric matrix enclosed by the input."""
    size = matrix.nrows()
    lower = arb_mat(size, size)
    pivots = []
    for j in range(size):
        pivot = matrix[j, j] - sum(lower[j, t]**2 * pivots[t] for t in range(j))
        require(pivot > 0, "uncertified Gram pivot")
        pivots.append(pivot)
        for i in range(j + 1, size):
            correction = sum(lower[i, t] * lower[j, t] * pivots[t] for t in range(j))
            lower[i, j] = (matrix[i, j] - correction) / pivot


def solve_cardinal(matrix, target):
    rhs = arb_mat(matrix.nrows(), 1)
    rhs[target, 0] = 1
    coefficients = matrix.solve(rhs)
    residual = matrix * coefficients - rhs
    require(all(x.contains(0) for x in residual.entries()), "cardinal residual")
    return coefficients


def extrema(values, digits):
    result = {}
    for name, extreme in (("min", min), ("max", max)):
        index = extreme(values, key=lambda i: values[i].lower())
        tied = [i for i, value in values.items() if value.overlaps(values[index])]
        require(len(tied) == 1, f"could not uniquely order the {name}")
        result[name] = {"index": index, "value": values[index].str(digits)}
    return result


def measure_window(lo, hi, centers, digits):
    lo_count, hi_count, heights = isolated_zeros(lo, hi)

    @cache
    def entries(i, j):
        distance = arb(0) if i == j else heights[j] - heights[i]
        return (kernel(1, 1, distance), kernel(1, 2, distance), kernel(2, 1, distance))

    @cache
    def gram_matrices(first, last):
        indices = range(first, last + 1)
        result = []
        for family in range(3):
            matrix = arb_mat([
                [entries(min(i, j), max(i, j))[family] for j in indices] for i in indices
            ])
            certify_positive_definite(matrix)
            result.append(matrix)
        return result

    rows = []
    weak_values, delta_values = {}, {}
    margins = {}
    sizes = Counter()
    for i in centers:
        require(lo < heights[i] - RADIUS and heights[i] + RADIUS < hi, "missing guard")
        included = []
        for j in range(lo_count + 1, hi_count + 1):
            d = arb(0) if i == j else abs(heights[i] - heights[j])
            margins[min(i, j), max(i, j)] = abs(d - RADIUS)
            if d < RADIUS:
                included.append(j)
            else:
                require(d > RADIUS, f"unresolved radius comparison at {i},{j}")
        first, last = included[0], included[-1]
        require(included == list(range(first, last + 1)), "noncontiguous neighborhood")
        require(count_zeros(heights[i] - RADIUS) == first - 1, "incorrect first local index")
        require(count_zeros(heights[i] + RADIUS) == last, "incorrect last local index")
        sizes[len(included)] += 1
        strong, weak, displaced = gram_matrices(first, last)
        target = i - first
        coefficients = solve_cardinal(strong, target)
        second = solve_cardinal(displaced, target)
        w = (coefficients.transpose() * weak * coefficients)[0, 0]
        delta = second[target, 0] - coefficients[target, 0]
        require(w > 0 and delta > 0, "unresolved positive quadratic")
        if i == 1:
            require(included == [1], "first window must be a singleton")
            require(w.overlaps(2 * arb.pi() / 3), "singleton W normalization")
            require(delta.overlaps(arb.pi()), "singleton delta normalization")
        weak_values[i] = w
        delta_values[i] = delta
        rows.append([i, first, last, w.str(digits), delta.str(digits)])

    closest = min(margins, key=lambda pair: margins[pair].lower())
    require(all(margin > margins[closest] for pair, margin in margins.items() if pair != closest),
            "uncertified nearest distinct pair to the cutoff")
    window = {
        "endpoints": [lo, hi], "N_at_endpoints": [lo_count, hi_count],
        "first_stored_zero_index": min(heights),
        "heights_with_guards": [t.str(digits) for t in heights.values()],
        "radius_comparisons": len(centers) * (hi_count - lo_count),
        "independent_local_endpoint_counts": 2 * len(centers),
        "closest_pair_to_radius": closest, "minimum_radius_margin": margins[closest].str(digits),
        "neighborhood_sizes": dict(sorted(sizes.items())),
        "rows": rows,
    }
    if centers[0] == 1:
        window["extrema"] = {
            str(n): {"W": extrema({i: weak_values[i] for i in range(1, n + 1)}, digits),
                     "delta": extrema({i: delta_values[i] for i in range(1, n + 1)}, digits)}
            for n in (32, CENTERS)
        }
    else:
        window["pair_gap"] = (heights[centers[1]] - heights[centers[0]]).str(digits)
    return window


def certificate(bits):
    require(bits >= 96, "use at least 96 bits")
    ctx.prec = bits
    digits = bits // 5
    return {
        "settings": {"bits": bits, "python_flint": flint.__version__,
                     "flint": flint.__FLINT_VERSION__, "alpha": 0, "a": "1/2",
                     "s": 3, "theta": "3/2", "radius": RADIUS},
        "row_columns": ["center", "first", "last", "W", "delta"],
        "prefix": measure_window(0, 300, range(1, CENTERS + 1), digits),
        "lehmer_pair": measure_window(6998, 7012, [6709, 6710], digits),
    }


def compare(left, right):
    left, right = sorted((left, right), key=lambda doc: doc["settings"]["bits"])
    ctx.prec = right["settings"]["bits"] + 40
    require(left["settings"]["bits"] < right["settings"]["bits"], "use different precisions")
    for name in ("prefix", "lehmer_pair"):
        low, high = left[name], right[name]
        za, zb = low["heights_with_guards"], high["heights_with_guards"]
        require(len(za) == len(zb) and all(arb(a).contains_interior(arb(b)) for a, b in zip(za, zb)),
                "high-precision zero balls do not lie in low-precision enclosures")
        require(len(low["rows"]) == len(high["rows"]), "inconsistent row count")
        for a, b in zip(low["rows"], high["rows"]):
            require(a[:3] == b[:3], "inconsistent neighborhood")
            require(all(arb(x).contains_interior(arb(y)) for x, y in zip(a[3:], b[3:])),
                    f"high-precision quadratic not enclosed at zero {a[0]}")
        require(low["closest_pair_to_radius"] == high["closest_pair_to_radius"],
                "inconsistent nearest pair to the cutoff")
        require(arb(low["minimum_radius_margin"]).contains_interior(arb(high["minimum_radius_margin"])),
                "high-precision minimum margin not enclosed")
        require(low["endpoints"] == high["endpoints"] and
                low["N_at_endpoints"] == high["N_at_endpoints"], "inconsistent guard counts")
        if "pair_gap" in low:
            require(arb(low["pair_gap"]).contains_interior(arb(high["pair_gap"])), "pair gap not enclosed")
        print(f"{name}: verified {len(za)} indexed zero balls and {len(low['rows'])} rows.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--bits", type=int)
    mode.add_argument("--compare", nargs=2, type=Path, metavar=("LEFT", "RIGHT"))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.compare:
        compare(*(json.loads(path.read_text(encoding="utf-8")) for path in args.compare))
    else:
        data = certificate(args.bits)
        destination = args.output or Path(f"weak-cardinals-{args.bits}.json")
        destination.write_text(json.dumps(data, ensure_ascii=True, separators=(",", ":")) + "\n",
                               encoding="utf-8")
        print(destination)
        print(json.dumps(data["prefix"]["extrema"], indent=2))
        print(json.dumps(data["lehmer_pair"]["rows"]))
