"""Certify two signs for the actual rational width-restriction trace.

Install python-flint 0.9.0, then run this script. All spectral samples use
the first 256 integers, the gamma factor and interval arithmetic. The proof
uses the fixed rational theta center 0, widths 1/4 and 3/4, and order 2.
"""
from math import comb
from pathlib import Path
import json

from flint import acb, arb, ctx, fmpq

ctx.prec = 224
half = fmpq(1, 2)
quarter = fmpq(1, 4)
count = 256
cutoff = 64
bisections = 32
epsilon = fmpq(1, 2**32)
log_pi = arb.pi().log()
logs = [arb(j).log() for j in range(1, count + 1)]

# Every seed names an interval [k/4,(k+1)/4]. The signs and completeness
# of the selected sites below the cutoff are proved separately below.
seeds = [56, 84, 100, 121, 131, 150, 163, 173, 192, 199, 211, 225, 237, 243, 260, 268]

def rational_hull(left, right):
    return arb((left + right) / 2, (right - left) / 2)

def hardy_coefficients():
    denominator = 3**count
    tail = 0
    coefficients = [None] * count
    for j in range(count, 0, -1):
        tail += comb(count, j) * 2**j
        signed = tail if j % 2 else -tail
        coefficients[j - 1] = arb(fmpq(signed, denominator)) / arb(j).sqrt()
    return coefficients

amplitudes = hardy_coefficients()
hardy_error = (arb(2).sqrt() + 1) * (68 * arb.pi()).cosh().sqrt() / (3**count)

def hardy_sign(t):
    point = arb(t)
    assert abs(point) <= 68
    numerator = sum((a * acb(0, -point * l).exp()
                     for a, l in zip(amplitudes, logs)), acb(0))
    denominator = 1 - arb(2).sqrt() * acb(0, -point * logs[1]).exp()
    phase = acb(quarter, point / 2).lgamma().imag - point * log_pi / 2
    value = (acb(0, phase).exp() * numerator / denominator).real
    if value > hardy_error:
        return 1
    if value < -hardy_error:
        return -1
    raise ArithmeticError(f"Hardy sign undecided at {t}")

def isolate_sign_change(k):
    left, right = fmpq(k, 4), fmpq(k + 1, 4)
    sign_left = hardy_sign(left)
    assert sign_left == -hardy_sign(right)
    for _ in range(bisections):
        mid = (left + right) / 2
        if hardy_sign(mid) == sign_left:
            left = mid
        else:
            right = mid
    return left, right

def upper_log_derivative(k):
    s = acb(2, k)
    partial = [(-s * l).exp() for l in logs]
    z = sum(partial, acb(0))
    w = sum((l * term for l, term in zip(logs, partial)), acb(0))
    r0 = arb(1) / count
    r1 = (1 + arb(count).log()) / count
    assert abs(z) > r0
    ratio_error = r1 / (abs(z) - r0) + abs(w) * r0 / (abs(z) * (abs(z) - r0))
    scalar = (1/s + 1/(s-1) - log_pi/2 + (s/2).digamma()/2 - w/z).real
    return (scalar + ratio_error).upper()

def four_pole_multiplier(z):
    return (z*z - quarter)*z*(z - 1)

def box_multiplier(z):
    return ((z / 16).sinh() / (z / 16))**16

def trace_interval(center, positive):
    low = arb(0)
    smooth_error = arb(0)
    for left, right in positive:
        z = acb(half, rational_hull(left, right))
        reference = (center*z).exp() * four_pole_multiplier(z) * box_multiplier(z)
        low += 2 * reference.real
        # Integrated over any probability bump supported on [-epsilon,epsilon].
        smooth_error += 2 * abs(reference) * epsilon * abs(z) * (arb(epsilon)/2).exp()

    # For a contributing site z, 0 <= Re z <= 3/4. Each horizontal
    # difference from a root of the polar polynomial has modulus <= 5/4.
    polynomial_constant = (1 + arb(fmpq(5, 4*cutoff))**2)**2
    sinc_constant = 16 * arb(fmpq(3, 64)).cosh()
    unknown_tail = (3 * polynomial_constant * (fmpq(3, 4) * arb(center + epsilon)).exp()
                    * sinc_constant**16 / arb(cutoff)**10)
    error = (smooth_error + unknown_tail).upper()
    full = (low + arb(0, error)) / 10000
    return full, {
        "center": str(center),
        "low_without_mollification_unscaled": str(low),
        "mollification_error_upper_unscaled": str(smooth_error.upper()),
        "uncounted_tail_upper_unscaled": str(unknown_tail.upper()),
        "trace_lower": str(full.lower()),
        "trace_upper": str(full.upper()),
    }

brackets = [isolate_sign_change(k) for k in seeds]
assert all(u < v for (_, u), (v, _) in zip(brackets, brackets[1:]))
symmetric = brackets + [(-u, -l) for l, u in brackets]
residuals = []
for k in range(cutoff + 1):
    known_lower = sum((arb(6) / (9 + 4 * max(abs(k-l), abs(k-u))**2)
                       for l, u in symmetric), arb(0))
    residual = (upper_log_derivative(k) - known_lower).upper()
    # Any further zero in the half-height cell costs at least 8/17.
    assert residual < fmpq(8, 17)
    residuals.append(residual)
positive = [(l, u) for l, u in brackets if u < cutoff]
assert len(positive) == 14 and all(l > cutoff for l, u in brackets if u >= cutoff)

values, rows = [], []
for center in (fmpq(7, 4), fmpq(2)):
    val, row = trace_interval(center, positive)
    values.append(val)
    rows.append(row)
assert values[0] > fmpq(28190, 10000) and values[0] < fmpq(28555, 10000)
assert values[1] > fmpq(-25528, 10000) and values[1] < fmpq(-25089, 10000)

# The same first critical zero also supplies the signed large-translate bound.
first = acb(half, rational_hull(*positive[0]))
first_reference = abs((fmpq(7,4)*first).exp()*four_pole_multiplier(first)*box_multiplier(first))/10000
first_relative_error = epsilon*abs(first)*(arb(epsilon)/2).exp()
first_coefficient = first_reference*(1-first_relative_error)
assert first_coefficient > 1

result = {
    "precision_bits": ctx.prec, "terms": count, "cutoff": cutoff,
    "positive_sign_change_seeds": seeds, "bisections": bisections,
    "hardy_error": str(hardy_error), "positive_sites_below_64": len(positive),
    "complete_height_cell_count": len(residuals),
    "largest_cell_budget_upper": str(max(residuals)), "extra_site_cost_lower": "8/17",
    "positive_sign_brackets": [[str(l), str(u)] for l, u in brackets],
    "first_coefficient_modulus_lower":str(first_coefficient.lower()),
    "trace_enclosures": rows,
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2)+"\n",encoding="utf-8")
print("largest cell budget", result["largest_cell_budget_upper"])
for row in rows:
    print("center",row["center"],"trace range",row["trace_lower"],row["trace_upper"])
