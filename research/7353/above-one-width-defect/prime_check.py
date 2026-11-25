"""Evaluate the full-stripe scalar on the prime side and widen the zero-side test.

Use python-flint 0.9.0. The prime-side function does not read spectral input.
The separate uniform-width check reuses the finite brackets from certificate.py.
"""
from math import comb, factorial, isqrt
from pathlib import Path
import json

from flint import arb, ctx, fmpq

ctx.prec = 224
directory = Path(__file__).resolve().parent
epsilon = fmpq(1, 2**32)
centers = (fmpq(7, 4), fmpq(2))
differential = ((4, 1), (3, 1), (2, fmpq(-1, 4)), (1, fmpq(-1, 4)))


def left_derivative(offset, order):
    """Derivative of the centered sixteen-box density, given offset <= 0."""
    degree = 15 - order
    acc = arb(0)
    for j in range(17):
        u = (1 + offset - fmpq(j, 8)).nonnegative_part()
        acc += (-1)**j * comb(16, j) * u**degree
    return fmpq(8**16, factorial(degree)) * acc


def derivative(offset, order):
    if offset <= 0:
        return left_derivative(offset, order)
    if offset >= 0:
        return (-1)**order * left_derivative(-offset, order)
    # Only needed if a future log(n) straddles the exact center.
    negative = left_derivative(offset.min(0), order)
    positive = (-1)**order * left_derivative(-offset.max(0), order)
    return negative.union(positive)


def spline_profile(offset, extra_derivatives=0):
    return sum((coefficient * derivative(offset, order + extra_derivatives)
                for order, coefficient in differential), arb(0)) / 10000


def mollified_profile(log_n, center):
    interval = log_n - center
    whole = interval + arb(0, epsilon)
    # Even probability density: the linear term integrates to zero.
    error = abs(spline_profile(whole, 2)) * epsilon**2 / 2
    return spline_profile(interval) + arb(0, error.upper())


def prime_base(n):
    for p in range(2, isqrt(n) + 1):
        if n % p == 0:
            q = n
            while q % p == 0:
                q //= p
            return p if q == 1 else None
    return n


def trivial_zero_mass(center):
    last = 40
    partial = arb(0)
    for k in range(1, last + 1):
        t = arb(2*k)
        polynomial = (t*t - fmpq(1, 4))*t*(t+1)
        u = t/16
        mass = (-t*center).exp() * polynomial * (u.sinh()/u)**16 / 10000
        # The real, even bump has moment between 1 and cosh(2*k*epsilon).
        partial += mass * arb(1).union((t*epsilon).cosh())
    first_omitted = last + 1
    rate = (-2*arb(center - 1 - epsilon)).exp()
    first_bound = fmpq(24, 10000) * first_omitted**4 * rate**first_omitted
    ratio = fmpq(first_omitted+1, first_omitted)**4 * rate
    assert ratio < 1
    tail_bound = (first_bound/(1-ratio)).upper()
    return partial + arb(0).union(tail_bound), tail_bound


def prime_side(center):
    cutoff = int(arb(center+1+epsilon).exp().floor().unique_fmpz())
    prime_terms = {}
    total = arb(0)
    for n in range(2, cutoff+1):
        log_n = arb(n).log()
        if log_n < center-1-epsilon:
            continue
        p = prime_base(n)
        if p is None:
            continue
        contribution = arb(p).log() * mollified_profile(log_n, center)
        total += contribution
        prime_terms[n] = str(contribution)
    trivial, tail = trivial_zero_mass(center)
    trace = -total-trivial
    return trace, dict(center=str(center), prime_terms=prime_terms,
                       prime_power_sum=str(total), trivial_zero_mass=str(trivial),
                       arch_tail_upper=str(tail), full_zero_sum=str(trace))


def uniform_width(row):
    # Only the universal coefficient cap d <= multiplicity enters the high tail.
    center = fmpq(row["center"])
    cutoff = 64
    horizontal = (1+arb(fmpq(3, 2*cutoff))**2)**2
    box = 16*arb(fmpq(1, 16)).cosh()
    tail = 3*horizontal*arb(center+epsilon).exp()*box**16 / arb(cutoff)**10
    low = arb(row["low_without_mollification_unscaled"])
    smooth = arb(row["mollification_error_upper_unscaled"])
    result = (low+arb(0, (smooth+tail).upper()))/10000
    return result, dict(center=str(center), unknown_tail_upper_unscaled=str(tail.upper()),
                        all_widths_enclosure=str(result),
                        lower=str(result.lower()), upper=str(result.upper()))


def run():
    values = [prime_side(center) for center in centers]
    assert list(values[0][1]["prime_terms"]) == [3,4,5,7,8,9,11,13]
    assert list(values[1][1]["prime_terms"]) == [3,4,5,7,8,9,11,13,16,17,19]
    assert values[0][0] > fmpq(28, 10) and values[1][0] < fmpq(-25, 10)
    certificate = json.loads((directory / "certificate.json").read_text(encoding="utf-8"))
    assert certificate["positive_sites_below_64"] == 14
    widths = [uniform_width(row) for row in certificate["trace_enclosures"]]
    assert widths[0][0] > fmpq(28, 10) and widths[1][0] < fmpq(-249, 100)
    assert all(w.contains(v) for (v, _), (w, _) in zip(values, widths))
    receipt = dict(precision_bits=ctx.prec, prime_side=[v[1] for v in values],
                   all_widths=[w[1] for w in widths])
    Path(__file__).with_suffix(".json").write_text(json.dumps(receipt, indent=2)+"\n",
                                                  encoding="utf-8")
    for (v, details), (w, bounds) in zip(values, widths):
        print(details["center"], "prime side", v, "uniform", bounds["lower"], bounds["upper"])


if __name__ == "__main__":
    run()
