"""Certified finite-sum calibration for the primitive quartic character chi(2)=i modulo 5."""

import argparse
import gzip
import hashlib
import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

import flint
from flint import acb, arb, ctx, fmpq

HERE = Path(__file__).resolve().parent
CHI = [(0, 0), (1, 0), (0, 1), (0, -1), (-1, 0)]
CUTOFF = 256
ORDER = 28
HEIGHT = 40
MESHES = (8, 12, 16, 24)
EULER_CUTOFF = 32768
GUARD = 20
PHASE_CUTOFF = 256
DIGAMMA_CUTOFF = 4096
DIRECT_CUTOFF = 8192
BRACKET_BITS = 24


def real(x):
    q = F(x)
    return arb(fmpq(q.numerator, q.denominator))


def box(x, digits=14):
    """Outward decimal endpoints, stored as exact integers over 10**digits."""
    scale = 10**digits
    lo = int((x * scale).lower().floor().unique_fmpz())
    hi = int((x * scale).upper().ceil().unique_fmpz())
    return {"lo": lo, "hi": hi, "digits": digits}


def pair_sub(x, y):
    return x[0] - y[0], x[1] - y[1]


def primitive_antidifference(values):
    """The unique mean-zero b satisfying b[r-1]-b[r]=values[r] cyclically."""
    b = []
    last = (F(0), F(0))
    for v in values:
        last = pair_sub(last, v)
        b.append(last)
    assert last == (0, 0)
    avg = tuple(sum(x[j] for x in b) / len(b) for j in (0, 1))
    b = [pair_sub(x, avg) for x in b]
    assert all(pair_sub(b[(r - 1) % len(b)], b[r]) == v for r, v in enumerate(values))
    return b


def add_scaled(x, c, y):
    return x[0] + c * y[0], x[1] + c * y[1]


class LinePolynomial:
    """Finite Gaussian-rational coefficients and a uniform analytic remainder."""

    def __init__(self, cutoff, order, max_height):
        self.cutoff, self.order = cutoff, order
        self.height = max_height
        base = [(F(a), F(b)) for a, b in CHI]
        ends = [(F(0), F(0)) for _ in range(order)]
        b = base
        for h in range(order):
            b = primitive_antidifference(b)
            for j in range(h + 1):
                c = (-1) ** (h - j) * math.comb(h, j)
                ends[j] = add_scaled(ends[j], c, b[(cutoff - 1) % 5])
        coeff = [base[m % 5] for m in range(1, cutoff)] + ends
        self.active = [(m, a) for m, a in enumerate(coeff, 1) if a != (0, 0)]
        self.logs = [arb(m).log() for m, _ in self.active]
        self.at_zero = [acb(real(c[0]), real(c[1])) / arb(m).sqrt() for m, c in self.active]
        self.anti_bound = max(abs(x) + abs(y) for x, y in b)
        rising = arb(1)
        for h in range(order):
            rising *= ((real(F(1, 2) + h)) ** 2 + max_height**2).sqrt()
        exponent = F(1, 2) - order
        self.tail = (
            real(self.anti_bound)
            * rising
            * (real(exponent) * arb(cutoff - 1).log()).exp()
            / real(-exponent)
        ).upper()
        assert self.tail > 0

    def _terms(self, t):
        return [c * acb(0, -t * v).exp() for c, v in zip(self.at_zero, self.logs)]

    def evaluate(self, t):
        assert abs(t) <= self.height
        return sum(self._terms(real(t)), acb(0))

    def grid(self, n):
        """Block restarts bound enclosure growth, including the last successor."""
        last = n**3 + 1
        phase = [acb(0, -v / n**2).exp() for v in self.logs]
        for start in range(-(n**3), last + 1, 128):
            terms = self._terms(real(F(start, n**2)))
            for k in range(start, min(start + 128, last + 1)):
                assert abs(F(k, n**2)) <= self.height
                yield k, sum(terms, acb(0))
                if k < min(start + 127, last):
                    terms = [entry * z for entry, z in zip(terms, phase)]


def root_number():
    i = acb(0, 1)
    angle = 2 * arb.pi() / 5
    z = acb(0, angle).exp()
    tau = sum((acb(*CHI[r]) * z**r for r in range(1, 5)), acb(0))
    from_sum = tau / (i * arb(5).sqrt())
    from_trig = 2 * acb(angle.sin(), (2 * angle).sin()) / arb(5).sqrt()
    root = acb(((5 + arb(5).sqrt()) / 10).sqrt(), ((5 - arb(5).sqrt()) / 10).sqrt())
    assert root.overlaps(from_sum) and root.overlaps(from_trig)
    assert abs(root).contains(1) and root.real > 0 and root.imag > 0
    return root, tau


def certified_grid(poly, n):
    eps = real(F(1, 2**n))
    den, eps_units = 2 ** (n + GUARD), 2**GUARD
    rows, passes, exact, undecided = [], [], [], []
    previous = None
    max_error = arb(0)
    for k, value in poly.grid(n):
        if k in (-(n**3), 0, n**3 + 1):
            assert value.overlaps(poly.evaluate(F(k, n**2)))
        mag = abs(value)
        a = int((mag.mid() * den).floor().unique_fmpz())
        error = (abs(mag - real(F(a, den))) + poly.tail).upper()
        if error > max_error:
            max_error = error
        assert error < eps
        true_mag = mag + arb(0, poly.tail)
        if previous is not None:
            j, prev_a, prev_mag = previous
            assert k == j + 1
            delta = n * true_mag - (n + 1) * prev_mag
            cert = n * max(0, a - eps_units) > (n + 1) * (prev_a + eps_units)
            if delta > 0:
                exact.append(j)
            elif not delta < 0:
                undecided.append(j)
            if cert:
                assert delta > 0
                passes.append(j)
        rows.append(a)
        previous = k, a, true_mag
    assert len(rows) == 2 * n**3 + 2

    def signed(ks):
        return {
            "negative": sum(k < 0 for k in ks),
            "nonnegative": sum(k >= 0 for k in ks),
            "total": len(ks),
        }

    def runs(ks):
        chunks = []
        for k in ks:
            if chunks and k == chunks[-1][1] + 1:
                chunks[-1][1] = k
            else:
                chunks.append([k, k])
        return chunks

    record = {
        "mesh": n,
        "left": -(n**3),
        "last_successor": n**3 + 1,
        "magnitude_denominator": den,
        "epsilon_numerator": eps_units,
        "numerators": rows,
        "accepted_index_runs": runs(passes),
        "true_positive_runs": runs(exact),
        "unresolved_true_indices": undecided,
    }
    report = {
        "mesh": n,
        "rows": len(rows),
        "comparisons": len(rows) - 1,
        "last_successor_coordinate": str(F(n**3 + 1, n**2)),
        "accepted": signed(passes),
        "true_rise_interval_proved": signed(exact),
        "true_rise_unresolved": signed(undecided),
        "accepted_index_runs": runs(passes),
        "max_enclosure_error": box(max_error, 22),
    }
    return record, report


def hardy(poly, root_sqrt, t):
    u = real(t)
    gamma = acb(real(F(3, 4)), u / 2).gamma()
    unit = acb(0, u * (5 / arb.pi()).log() / 2).exp() * gamma / abs(gamma) / root_sqrt
    value = poly.evaluate(t)
    error = arb(0, poly.tail)
    z = unit * (value + acb(error, error))
    assert z.imag.contains(0)
    return z.real


def elementary_hardy(poly, root, t):
    """Bound Gamma's phase by Euler's elementary finite product and its tail."""
    x, b = real(F(3, 4)), real(t / 2)
    m = PHASE_CUTOFF
    theta = b * arb(m).log() - sum(((b / (k + x)).atan() for k in range(m + 1)), arb(0))
    radius = abs(b) * (real(F(3, 2)) + x) / (m - 1) + abs(b) ** 3 / (6 * (m - 1) ** 2)
    phase = theta + arb(0, radius.upper()) + real(t) * (5 / arb.pi()).log() / 2 - root.arg() / 2
    e = arb(0, poly.tail)
    z = acb(0, phase).exp() * (poly.evaluate(t) + acb(e, e))
    assert z.imag.contains(0)
    return z.real


def sign(z):
    if z > 0:
        return 1
    if z < 0:
        return -1
    raise ArithmeticError("Hardy endpoint sign ambiguous: " + str(z))


def scan_hardy(poly, root):
    root_sqrt = root.sqrt()
    assert root_sqrt.real > 0
    brackets = []
    prev = (F(-HEIGHT), None)
    for j in range(-8 * HEIGHT, 8 * HEIGHT + 1):
        t = F(j, 8)
        h = hardy(poly, root_sqrt, t)
        sg = sign(h)
        if prev[1] is not None and sg != sign(prev[1]):
            lo, hi = prev[0], t
            vlow, vhigh = prev[1], h
            while hi - lo > F(1, 2**BRACKET_BITS):
                mid = (hi + lo) / 2
                val = hardy(poly, root_sqrt, mid)
                if sign(val) == sign(vlow):
                    lo, vlow = mid, val
                else:
                    hi, vhigh = mid, val
            assert sign(vlow) * sign(vhigh) == -1
            assert not brackets or brackets[-1][1] < lo
            brackets.append((lo, hi, vlow, vhigh))
        prev = t, h
    return brackets


def bernoulli(n):
    # The recurrence gives the usual even Bernoulli numbers.
    b = [F(1)]
    for k in range(1, n + 1):
        b.append(-sum(math.comb(k + 1, j) * b[j] for j in range(k)) / (k + 1))
    return b


def independent_em(t, blocks=32, p=12):
    """Separate residue-class Euler--Maclaurin check; no special L-function evaluation."""
    s = acb(real(F(1, 2)), real(t))
    poch = [acb(1)]
    for k in range(2 * p):
        poch.append(poch[-1] * (s + k))
    b = bernoulli(2 * p)
    total = acb(0)
    remainder = arb(0)
    for r in range(1, 5):
        ch = acb(*CHI[r])
        partial = sum(((-s * arb(5 * k + r).log()).exp() for k in range(blocks)), acb(0))
        x = 5 * blocks + r
        xs = (-s * arb(x).log()).exp()
        residual = xs * (x / (5 * (s - 1)) + real(F(1, 2)))
        for j in range(1, p + 1):
            c = b[2 * j] * F(5 ** (2 * j - 1), math.factorial(2 * j) * x ** (2 * j - 1))
            residual += real(c) * poch[2 * j - 1] * xs
        # |periodic B_2p|/(2p)! <= 4/6^(2p); integrate its derivative majorant.
        power = (real(F(1, 2) - 2 * p) * arb(x).log()).exp()
        remainder += (
            real(F(4 * 5 ** (2 * p - 1), 6 ** (2 * p)))
            * abs(poch[2 * p])
            * power
            / real(2 * p - F(1, 2))
        )
        total += ch * (partial + residual)
    err = arb(0, remainder.upper())
    return total + acb(err, err), remainder.upper()


def positive_scalar_power(a, v):
    return a / (a * a + v * v)


def prime_powers(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start::p] = b"\x00" * len(range(start, limit + 1, p))
    values = []
    for p in range(2, limit + 1):
        if not sieve[p] or p == 5:
            continue
        m = p
        while m <= limit:
            values.append((arb(m).log(), acb(*CHI[m % 5]) * arb(p).log() / m**2))
            m *= p
    return values


def translated_D(terms, y):
    # This computes the signed ordinate +y for this same character.
    val = (5 / arb.pi()).log() / 2 + acb(real(F(3, 2)), real(F(y, 2))).digamma().real / 2
    val -= sum((coef * acb(0, -y * logm).exp() for logm, coef in terms), acb(0)).real
    error = (arb(EULER_CUTOFF).log() + 1) / EULER_CUTOFF
    return val + arb(0, error.upper())


def elementary_D(y):
    """Independent completed-log-derivative enclosure using direct L and L' sums."""
    yb = real(y)
    x, b = real(F(3, 2)), real(F(y, 2))
    m = DIGAMMA_CUTOFF
    psi = arb(m).log() - sum(((k + x) / ((k + x) ** 2 + b * b) for k in range(m + 1)), arb(0))
    psi_error = (real(F(1, 2)) + abs(acb(1 + x, b))) / (m - 1)
    arch = ((5 / arb.pi()).log() + psi + arb(0, psi_error.upper())) / 2
    n = DIRECT_CUTOFF
    value, derivative = acb(0), acb(0)
    for k in range(1, n + 1):
        if k % 5:
            logk = arb(k).log()
            term = acb(*CHI[k % 5]) * acb(0, -yb * logk).exp() / k**2
            value += term
            derivative -= term * logk
    epsilon = arb(0, real(F(1, n)).upper())
    value += acb(epsilon, epsilon)
    epsilon = arb(0, ((arb(n).log() + 1) / n).upper())
    derivative += acb(epsilon, epsilon)
    assert not value.contains(0)
    return arch + (derivative / value).real


def poisson_certificate(brackets, centers):
    terms = prime_powers(EULER_CUTOFF)
    out = []
    a = F(3, 2)
    eta = F(2)
    single = min(positive_scalar_power(F(1), eta), positive_scalar_power(F(2), eta))
    phi0 = positive_scalar_power(F(1), eta) + positive_scalar_power(F(2), eta)
    phim = 2 * positive_scalar_power(a, eta)
    costs = [min(phi0, phim), phim, min(phi0, phim / 2)]

    def local(which, y, total):
        assert all(not lo <= y <= hi for lo, hi, _, _ in which)
        known = sum(
            (positive_scalar_power(a, max(abs(lo - y), abs(hi - y))) for lo, hi, _, _ in which),
            F(0),
        )
        included = [
            i for i, (lo, hi, _, _) in enumerate(brackets) if y - eta <= lo and hi <= y + eta
        ]
        for lo, hi, _, _ in brackets:
            assert not (lo <= y - eta <= hi or lo <= y + eta <= hi)
        assert (real(known) - total).upper() < 0
        remaining = total - real(known)
        margin = real(single) - remaining
        return {
            "brackets_used": len(which),
            "known_mass_lower": box(real(known), 12),
            "residual_upper_interval": box(remaining, 12),
            "one_zero_cost": str(single),
            "one_zero_margin": box(margin, 12),
            "exact_cell_via_one_zero": bool(margin > 0),
            "hik_costs": [str(x) for x in costs],
            "hik_margins": [box(real(x) - remaining, 12) for x in costs],
            "hik_pass": [bool(real(x) - remaining > 0) for x in costs],
            "bracket_ids_inside": included,
        }

    for y in centers:
        total = translated_D(terms, y)
        direct = elementary_D(y)
        assert total.overlaps(direct)
        direct_check = local(brackets, y, direct)
        assert direct_check["exact_cell_via_one_zero"]
        entry = {
            "elementary_D_interval": box(direct, 12),
            "elementary_one_zero_margin": direct_check["one_zero_margin"],
            "center": y,
            "radius": str(eta),
            "D_interval": box(total, 12),
            "both_signs": local(brackets, y, total),
        }
        if abs(y) >= eta:
            # A separate antecedent using only brackets in the original one-sided geometry.
            one_side = [b for b in brackets if y - abs(y) <= b[0] and b[1] <= y + abs(y)]
            entry["same_side_tau_abs_y"] = local(one_side, y, total)
        out.append(entry)
    return out


def write_json(path, obj):
    path.write_text(
        json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n"
    )


def main():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=HERE / "output")
    parser.add_argument("--bits", type=int, default=160)
    args = parser.parse_args()
    if args.bits < 128:
        raise ValueError("At least 128 bits are required for this configuration")
    ctx.prec = args.bits
    out = args.out
    out.mkdir(parents=True, exist_ok=True)
    root, tau = root_number()
    poly = LinePolynomial(CUTOFF, ORDER, HEIGHT)
    assert max(MESHES) + 1 <= HEIGHT
    assert poly.tail < real(F(1, 10**20))
    cross = []
    for t in map(F, [-40, -24, -12, -6, -1, 0, 1, 6, 12, 24, 40]):
        p = poly.evaluate(t)
        e = arb(0, poly.tail)
        c = p + acb(e, e)
        alt, em_tail = independent_em(t)
        assert c.overlaps(alt)
        cross.append(
            {
                "t": str(t),
                "L_re": box(c.real),
                "L_im": box(c.imag),
                "abs_L": box(abs(p) + e),
                "EM_remainder_bound": box(em_tail, 32),
            }
        )
    assert not (abs(poly.evaluate(F(6))) + arb(0, poly.tail)).overlaps(
        abs(poly.evaluate(F(-6))) + arb(0, poly.tail)
    )
    tables = []
    meshes = []
    for n in MESHES:
        table, summary = certified_grid(poly, n)
        tables.append(table)
        meshes.append(summary)
        print(
            f"mesh {n:2d}: {summary['accepted']} conservative; true positive "
            f"{summary['true_rise_interval_proved']}, unresolved {summary['true_rise_unresolved']['total']}",
            flush=True,
        )
    tbytes = json.dumps(tables, separators=(",", ":"), sort_keys=True).encode() + b"\n"
    (out / "magnitude-tables.json.gz").write_bytes(gzip.compress(tbytes, compresslevel=9, mtime=0))
    brackets = scan_hardy(poly, root)
    neg = sum(hi < 0 for lo, hi, _, _ in brackets)
    pos = sum(lo > 0 for lo, hi, _, _ in brackets)
    assert neg + pos == len(brackets)
    cells = poisson_certificate(brackets, range(-20, 21, 4))
    for cell in cells:
        assert cell["both_signs"]["exact_cell_via_one_zero"]
        assert all(cell["both_signs"]["hik_pass"])
    selected = [(lo, hi) for lo, hi, _, _ in brackets if -22 <= lo and hi <= 22]
    assert not any(lo <= -22 <= hi or lo <= 22 <= hi for lo, hi, _, _ in brackets)
    event = {
        "scan_counts": {"negative": neg, "positive": pos},
        "complete_window": [-22, 22],
        "complete_counts": {
            "negative": sum(hi < 0 for lo, hi in selected),
            "positive": sum(lo > 0 for lo, hi in selected),
            "total": len(selected),
        },
        "hardy_brackets": [
            {"id": i, "lo": str(lo), "hi": str(hi), "Z_lo": box(vlo, 18), "Z_hi": box(vhi, 18)}
            for i, (lo, hi, vlo, vhi) in enumerate(brackets)
        ],
    }
    for (lo, hi, narrow_lo, narrow_hi), record in zip(brackets, event["hardy_brackets"]):
        wide_lo, wide_hi = elementary_hardy(poly, root, lo), elementary_hardy(poly, root, hi)
        assert wide_lo.overlaps(narrow_lo) and wide_hi.overlaps(narrow_hi)
        assert sign(wide_lo) == sign(narrow_lo) == -sign(wide_hi) == -sign(narrow_hi)
        record.update(Z_elementary_lo=box(wide_lo, 18), Z_elementary_hi=box(wide_hi, 18))
        for left, right in [
            (record["Z_lo"], record["Z_hi"]),
            (record["Z_elementary_lo"], record["Z_elementary_hi"]),
        ]:
            assert left["hi"] < 0 < right["lo"] or right["hi"] < 0 < left["lo"]
    report = {
        "character": "primitive quartic modulo 5, chi(2)=+i, chi(-1)=-1",
        "python": sys.version.split()[0],
        "python_flint": flint.__version__,
        "flint": flint.__FLINT_VERSION__,
        "precision_bits": args.bits,
        "gauss_sum": {"real": box(tau.real, 24), "imag": box(tau.imag, 24)},
        "root_number": {"real": box(root.real, 24), "imag": box(root.imag, 24)},
        "principal_root_half_phase_arg": box(root.arg() / 2, 24),
        "line_polynomial": {
            "N": CUTOFF,
            "p": ORDER,
            "max_abs_height": HEIGHT,
            "largest_integer": max(m for m, _ in poly.active),
            "nonzero_terms": len(poly.active),
            "antidifference_l1_bound": str(poly.anti_bound),
            "uniform_analytic_tail": box(poly.tail, 38),
        },
        "elementary_checks": {
            "gamma_phase_cutoff": PHASE_CUTOFF,
            "digamma_cutoff": DIGAMMA_CUTOFF,
            "direct_Dirichlet_cutoff": DIRECT_CUTOFF,
        },
        "prime_power_limit": EULER_CUTOFF,
        "log_derivative_tail_bound": box((arb(EULER_CUTOFF).log() + 1) / EULER_CUTOFF, 15),
        "table_raw_sha256": hashlib.sha256(tbytes).hexdigest(),
        "enclosure_crosscheck": cross,
        "meshes": meshes,
        "signed_events": event,
        "translated_cells": cells,
    }
    write_json(out / "certificate.json", report)
    print("Gauss/root/phase", root.str(22), (root.arg() / 2).str(22))
    print("line tail", poly.tail.str(10), "nonzero terms", len(poly.active))
    print("Hardy sign brackets", event["scan_counts"], "in [-40,40]")
    print("Poisson cells", len(cells), "exact counts in [-22,22]", event["complete_counts"])
    print(
        "full-cell residual upper bounds",
        [(v["center"], v["both_signs"]["residual_upper_interval"]["hi"]) for v in cells],
        "in units 10^-12",
    )
    print(
        "single-side HIK (i),(ii),(iii)",
        [
            (v["center"], v["same_side_tau_abs_y"]["hik_pass"])
            for v in cells
            if "same_side_tau_abs_y" in v
        ],
    )
    print("elementary Hardy endpoint checks", 2 * len(brackets), "of", 2 * len(brackets))
    print("direct integer L and L' / elementary digamma verified centers", len(cells))
    print(
        "worst elementary one-zero margin lower bound",
        min(c["elementary_one_zero_margin"]["lo"] for c in cells),
        "in units 10^-12",
    )
    print("table raw SHA-256", report["table_raw_sha256"])


if __name__ == "__main__":
    main()
