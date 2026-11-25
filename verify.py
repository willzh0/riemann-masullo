"""Replay the exact integer decisions and Poisson bounds using only the standard library."""

import argparse
import gzip
import hashlib
import json
import math
from fractions import Fraction as Q
from pathlib import Path


def require(test, message):
    if not test:
        raise ValueError(message)


def endpoints(record):
    scale = 10 ** record["digits"]
    lo, hi = Q(record["lo"], scale), Q(record["hi"], scale)
    require(lo <= hi, "inverted outward enclosure")
    return lo, hi


def intersects(a, b):
    alo, ahi = endpoints(a)
    blo, bhi = endpoints(b)
    return max(alo, blo) <= min(ahi, bhi)


def unpack(runs):
    return [k for lo, hi in runs for k in range(lo, hi + 1)]


def signed(k):
    return (sum(j < 0 for j in k), sum(j >= 0 for j in k))


def check_one(directory):
    report = json.loads((directory / "certificate.json").read_bytes())
    p = report["line_polynomial"]
    require((p["N"], p["p"], p["max_abs_height"]) == (256, 28, 40), "polynomial parameters")
    # Invert the cyclic difference independently by convolution with (0,1,2,3,4)/5.
    anti = [(0, 0), (1, 0), (0, 1), (0, -1), (-1, 0)]
    for _ in range(p["p"]):
        anti = [
            tuple(sum(Q(k, 5) * anti[(r - k) % 5][v] for k in range(5)) for v in (0, 1))
            for r in range(5)
        ]
    norm = max(abs(a) + abs(b) for a, b in anti)
    require(norm == Q(p["antidifference_l1_bound"]), "independent coefficient bound")
    sigma = Q(1, 2)
    rising_squared = math.prod((j + sigma) ** 2 + p["max_abs_height"] ** 2 for j in range(p["p"]))
    tail_squared = (
        norm**2 * rising_squared / ((p["p"] - sigma) ** 2 * (p["N"] - 1) ** (2 * p["p"] - 1))
    )
    tail_upper = endpoints(p["uniform_analytic_tail"])[1]
    require(tail_squared <= tail_upper**2 < Q(1636, 10**27) ** 2, "exact uniform tail bound")
    raw = gzip.decompress((directory / "magnitude-tables.json.gz").read_bytes())
    digest = hashlib.sha256(raw).hexdigest()
    require(digest == report["table_raw_sha256"], "table digest")
    tables = json.loads(raw)
    require([row["mesh"] for row in tables] == [8, 12, 16, 24], "mesh list")
    counts = []
    for table, info in zip(tables, report["meshes"], strict=True):
        n = table["mesh"]
        numerators = table["numerators"]
        lo, last = -(n**3), n**3 + 1
        guard = 2**20
        require(
            info["mesh"] == n
            and table["magnitude_denominator"] == 2 ** (n + 20)
            and table["epsilon_numerator"] == guard,
            "dyadic conventions",
        )
        require(
            table["left"] == lo
            and table["last_successor"] == last
            and len(numerators) == last - lo + 1 == info["rows"],
            "grid boundary or size",
        )
        require(endpoints(info["max_enclosure_error"])[1] < Q(1, 2**n), "enclosure tolerance")
        indices = [
            lo + i
            for i, (left, right) in enumerate(zip(numerators, numerators[1:]))
            if (n + 1) * (left + guard) < n * max(0, right - guard)
        ]
        actual = unpack(table["true_positive_runs"])
        unresolved = table["unresolved_true_indices"]
        require(
            indices == unpack(table["accepted_index_runs"]) == unpack(info["accepted_index_runs"]),
            "integer passes",
        )
        require(set(indices) <= set(actual) and not unresolved, "strict comparison status")
        require(
            all(lo <= k < last for k in actual) and actual == sorted(set(actual)), "true indices"
        )
        for label, seq in [
            ("accepted", indices),
            ("true_rise_interval_proved", actual),
            ("true_rise_unresolved", unresolved),
        ]:
            c = info[label]
            require(
                (*signed(seq), len(seq)) == (c["negative"], c["nonnegative"], c["total"]), label
            )
        counts.append((n, len(numerators) - 1, *signed(indices), *signed(actual)))
    ev = report["signed_events"]
    brackets = []
    for i, b in enumerate(ev["hardy_brackets"]):
        lo, hi = Q(b["lo"]), Q(b["hi"])
        require(b["id"] == i and -40 <= lo < hi <= 40 and hi - lo == Q(1, 2**24), "Hardy width")
        require(not brackets or brackets[-1][1] < lo, "overlapping Hardy brackets")
        for left, right in [("Z_lo", "Z_hi"), ("Z_elementary_lo", "Z_elementary_hi")]:
            ll, lh = endpoints(b[left])
            rl, rh = endpoints(b[right])
            require(lh < 0 < rl or rh < 0 < ll, "opposite rigorous signs")
        require(
            intersects(b["Z_lo"], b["Z_elementary_lo"])
            and intersects(b["Z_hi"], b["Z_elementary_hi"]),
            "dual phase intervals",
        )
        brackets.append((lo, hi))
    require(not any(lo <= 0 <= hi for lo, hi in brackets), "bracket includes zero")
    require(
        (sum(hi < 0 for lo, hi in brackets), sum(lo > 0 for lo, hi in brackets))
        == (ev["scan_counts"]["negative"], ev["scan_counts"]["positive"]),
        "signed scan",
    )
    a, eta = Q(3, 2), Q(2)
    costs = [Q(9, 20), Q(12, 25), Q(6, 25)]
    centers = tuple(range(-20, 21, 4))
    require(tuple(v["center"] for v in report["translated_cells"]) == centers, "closed tiling")
    selected = []
    decisions = []
    for y, v in zip(centers, report["translated_cells"], strict=True):
        require(
            Q(v["radius"]) == eta and intersects(v["D_interval"], v["elementary_D_interval"]),
            "matching arithmetic centers",
        )
        dlo, dhi = endpoints(v["D_interval"])
        ddlo, ddhi = endpoints(v["elementary_D_interval"])
        inside = [i for i, (lo, hi) in enumerate(brackets) if y - eta <= lo and hi <= y + eta]
        require(
            not any(
                lo <= boundary <= hi for lo, hi in brackets for boundary in (y - eta, y, y + eta)
            ),
            "a bracket crosses a decision boundary",
        )
        selected += inside
        row = []
        for key, used in [
            ("both_signs", brackets),
            (
                "same_side_tau_abs_y",
                [(lo, hi) for lo, hi in brackets if y - abs(y) <= lo and hi <= y + abs(y)],
            ),
        ]:
            if key.startswith("same_side") and y == 0:
                require(key not in v, "center-zero one-sided geometry")
                continue
            claim = v[key]
            known = sum((a / (a * a + max(abs(lo - y), abs(hi - y)) ** 2) for lo, hi in used), Q(0))
            klo, khi = endpoints(claim["known_mass_lower"])
            require(
                klo <= known <= khi
                and claim["brackets_used"] == len(used)
                and claim["bracket_ids_inside"] == inside,
                "computed bracket mass",
            )
            rlo, rhi = endpoints(claim["residual_upper_interval"])
            # Each of D and D-known was rounded outwards independently.
            require(
                rlo - 2 * Q(1, 10**12) <= dlo - known <= rhi + 2 * Q(1, 10**12)
                and rlo - 2 * Q(1, 10**12) <= dhi - known <= rhi + 2 * Q(1, 10**12),
                "published residual",
            )
            require([Q(c) for c in claim["hik_costs"]] == costs, "translated costs")
            flags = []
            for b in [Q(1, 5), *costs]:
                if dhi - known < b:
                    flags.append(True)
                else:
                    require(b < dlo - known, "unresolved rounded comparison")
                    flags.append(False)
            require(
                flags == [claim["exact_cell_via_one_zero"], *claim["hik_pass"]],
                "strict antecedents",
            )
            if key == "both_signs":
                require(
                    flags[0] and ddhi - known < Q(1, 5),
                    "single-copy margin via both arithmetic forms",
                )
                require(
                    endpoints(v["elementary_one_zero_margin"])[0] > 0, "elementary margin bound"
                )
            row.append(tuple(flags))
        decisions.append(tuple(row))
    require(selected == sorted(set(selected)), "duplicate bracket in closed cells")
    expected = [i for i, (lo, hi) in enumerate(brackets) if -22 <= lo and hi <= 22]
    require(selected == expected and ev["complete_window"] == [-22, 22], "cover of closed cells")
    c = ev["complete_counts"]
    require(
        (
            sum(brackets[i][1] < 0 for i in selected),
            sum(brackets[i][0] > 0 for i in selected),
            len(selected),
        )
        == (c["negative"], c["positive"], c["total"]),
        "complete signed count",
    )
    return (digest, tuple(counts), tuple(brackets), tuple(decisions), tuple(selected))


def rounded_pair(box, digits):
    """Exact outward conversion of a published decimal enclosure to a coarser one."""
    require(box["digits"] >= digits, "unexpected decimal precision")
    unit = 10 ** (box["digits"] - digits)
    return [box["lo"] // unit, -((-box["hi"]) // unit)]


def compact_from_run(directory):
    r = json.loads((directory / "certificate.json").read_bytes())
    tables = json.loads(gzip.decompress((directory / "magnitude-tables.json.gz").read_bytes()))
    samples = []
    for tab, mesh in zip(tables, r["meshes"], strict=True):
        n = mesh["mesh"]
        pick = [-(n**3), -6 * n * n, 0, 6 * n * n, n**3, n**3 + 1]
        counts = [mesh[k] for k in ("accepted", "true_rise_interval_proved")]
        samples.append(
            {
                "n": n,
                "pairs": mesh["comparisons"],
                "accepted": [counts[0]["negative"], counts[0]["nonnegative"]],
                "strict_rises": [counts[1]["negative"], counts[1]["nonnegative"]],
                "sample_numerators": [tab["numerators"][k - tab["left"]] for k in pick],
            }
        )
    denom = 2**24
    hardy = []
    for bracket in r["signed_events"]["hardy_brackets"]:
        left, right = Q(bracket["lo"]) * denom, Q(bracket["hi"]) * denom
        require(left.denominator == 1 and right == left + 1, "dyadic bracket convention")
        hardy.append(
            [
                int(left),
                *rounded_pair(bracket["Z_elementary_lo"], 12),
                *rounded_pair(bracket["Z_elementary_hi"], 12),
            ]
        )
    return {
        "character_values_mod_5": [[0, 0], [1, 0], [0, 1], [0, -1], [-1, 0]],
        "polynomial": r["line_polynomial"],
        "root_number": r["root_number"],
        "line_magnitude_examples": {
            k: rounded_pair(v["abs_L"], 14)
            for v in r["enclosure_crosscheck"]
            for k in [v["t"]]
            if k in ("-6", "6")
        },
        "magnitude_table_sha256": r["table_raw_sha256"],
        "grids": samples,
        "hardy_denominator": denom,
        "hardy_value_decimal_digits": 12,
        "hardy_brackets": hardy,
        "scalar_decimal_digits": 10,
        "scalars": [
            [
                v["center"],
                *rounded_pair(v["D_interval"], 10),
                *rounded_pair(v["elementary_D_interval"], 10),
            ]
            for v in r["translated_cells"]
        ],
    }


def check_compact(data):
    denom, scale = data["hardy_denominator"], 10 ** data["scalar_decimal_digits"]
    require(denom == 2**24 and data["hardy_value_decimal_digits"] == 12, "bracket units")
    require(
        data["character_values_mod_5"] == [[0, 0], [1, 0], [0, 1], [0, -1], [-1, 0]], "character"
    )
    brackets = []
    for k, ll, lh, rl, rh in data["hardy_brackets"]:
        lo, hi = Q(k, denom), Q(k + 1, denom)
        require(-40 <= lo < hi <= 40 and (not brackets or brackets[-1][1] < lo), "bracket domain")
        require(ll <= lh and rl <= rh and (lh < 0 < rl or rh < 0 < ll), "opposite endpoint signs")
        brackets.append((lo, hi))
    a, eta = Q(3, 2), Q(2)
    costs = [Q(9, 20), Q(12, 25), Q(6, 25)]
    require([v[0] for v in data["scalars"]] == list(range(-20, 21, 4)), "closed cell cover")
    represented = []
    worst = [Q(0), Q(0)]
    for y, pl, ph, dl, dh in data["scalars"]:
        require(pl <= ph and dl <= dh and max(pl, dl) <= min(ph, dh), "scalar enclosures")

        def lower(br):
            return sum((a / (a * a + max(abs(lo - y), abs(hi - y)) ** 2) for lo, hi in br), Q(0))

        known = lower(brackets)
        for i, upper in enumerate([ph, dh]):
            remaining = Q(upper, scale) - known
            require(remaining < Q(1, 5), "unrepresented zero could fit")
            worst[i] = max(worst[i], remaining)
        if y:
            side = lower([(lo, hi) for lo, hi in brackets if y - abs(y) <= lo and hi <= y + abs(y)])
            expected = [True, True, y != 4]
            for threshold, yes in zip(costs, expected, strict=True):
                require(
                    Q(ph, scale) - side < threshold if yes else Q(pl, scale) - side > threshold,
                    "one-sided strict costs",
                )
        for i, (lo, hi) in enumerate(brackets):
            require(not any(lo <= edge <= hi for edge in (y - eta, y, y + eta)), "bracket crossing")
            if y - eta <= lo and hi <= y + eta:
                represented.append(i)
    require(represented == sorted(set(represented)), "duplicate representative")
    neg = sum(brackets[i][1] < 0 for i in represented)
    pos = sum(brackets[i][0] > 0 for i in represented)
    require((neg, pos, len(represented)) == (7, 6, 13), "signed finite count")
    print(
        f"Compact certificate: {len(brackets)} sign brackets, {neg} negative and {pos} positive in [-22,22]."
    )
    print(
        "Published prime-power and direct residual bounds below",
        *[f"{math.ceil(x*10**6)/10**6:.6f}" for x in worst],
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "runs", type=Path, nargs="*", help="optional output directories from quartic5.py"
    )
    parser.add_argument("--receipt", type=Path, default=Path(__file__).with_name("receipt.json"))
    args = parser.parse_args()
    reference = json.loads(args.receipt.read_bytes())
    check_compact(reference)
    if args.runs:
        checked = [check_one(path) for path in args.runs]
        require(all(result == checked[0] for result in checked), "complete replay decisions differ")
        for path in args.runs:
            require(compact_from_run(path) == reference, "regenerated figures differ from receipt")
        digest, counts, _, _, _ = checked[0]
        print(
            "Verified every integer comparison, two phase enclosures, and both arithmetic sums in",
            len(checked),
            "full run(s).",
        )
        print("mesh, pairs, accepted(-,+), strict rises(-,+):", list(counts))
        print("Full magnitude table SHA-256:", digest)


if __name__ == "__main__":
    main()
