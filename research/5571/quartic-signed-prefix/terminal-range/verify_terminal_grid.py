# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint==0.8.0"]
# ///
"""Certify the prescribed terminal grid and its continuous integral at x=8,32.

Run: uv run verify_terminal_grid.py --precision 128
Run again with --precision 192. Each invocation emits a self-contained JSON
receipt, including the original unsmoothed prime value and integer grid signs.

Let k(r)=K(exp(r)). On its three pieces k is 1-3exp(r)/2, cosh(r)-1,
and 0, joined C1 at -log(2),0. Its first derivative is bounded by 3/4;
its first derivative is globally 5/4-Lipschitz. For F_a(delta)=E k(r-a delta Z),
|F_a'| <= (3/4)a E|Z| and |F_a''| <= (5/4)a^2 (with the latter interpreted
as a Lipschitz bound on F_a'). The compensated weight is F_1+c(F_1-F_sqrt2),
c=exp(-delta^2/2). Thus |weight''| <= (5/4)(2+2) + 1
 + 2 exp(-1/2) (3/4)(1+sqrt(2)) E|Z| < 8. This uses |c''|<=1 and
|F_1-F_sqrt2|<=1. All prime logarithms in the Lipschitz bound are unsigned.

For a cell of width h, the true signed row differs from its linear chord L
by at most E=M h^2/8, where M=8 sum(real-character primes p) log p.
The positive-part map is 1-Lipschitz. With g(delta)=2 delta exp(-4 delta^2
-b delta^4), b=0,1, the difference between the integral of g [L]_+ and
the cell mass times the unweighted mean of [L]_+ is at most
3 |row_right-row_left| h^2/12. This follows by integrating
(g(t)-g(s))([L(t)]_+-[L(s)]_+) over the square and dividing by 2h.
Here |g'|<=3, since z=4 delta^2+b delta^4 and 8 delta^2+4b delta^4<=4z.
Adding E times the exact cell mass encloses the continuous integral.
"""

import argparse
import json
from math import isqrt

import flint
from flint import arb, ctx, fmpq


FINE_DENOMINATOR = 4096
WEIGHTS = ("exp(-4v)", "exp(-4v-v^2)")


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def kernel(r):
    if r <= fmpq(1, 2):
        return 1 - fmpq(3, 2) * r
    if r < 1:
        return (1 - r) ** 2 / (2 * r)
    return fmpq(0)


def primes_through(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((n - p*p) // p + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


class PrimeRow:
    def __init__(self, x):
        self.full_primes = primes_through(x*x)
        self.terms = []
        self.zero_value = arb(0)
        self.curvature = arb(0)
        log2 = arb(2).log()
        for p in self.full_primes:
            if p % 5 not in (1, 4):
                continue
            sign = 1 if p % 5 == 1 else -1
            logp = arb(p).log()
            ratio = fmpq(p, x)
            left = arb(ratio).log()
            # Breaks in the Gaussian shift h are log(p/x), log(2p/x).
            self.terms.append((left, left + log2, arb(1/(2*ratio)),
                               arb(ratio/2), arb(2*ratio), sign * logp))
            self.zero_value += sign * logp * kernel(ratio)
            self.curvature += 8 * logp

    def gaussian(self, variance):
        # Integrating each of the three pieces of K against a Gaussian uses
        # E[exp(a h) 1_{h>t}]=exp(a^2 v/2) erfc((t-a v)/sqrt(2v))/2.
        inv_scale = 1 / (2 * variance).sqrt()
        tilt = (variance / 2).exp()
        total = arb(0)
        for left, right, inverse, half_ratio, twice_ratio, signed_logp in self.terms:
            constant = 2 * (right * inv_scale).erfc() - (left * inv_scale).erfc()
            positive_tilt = inverse * (
                ((left - variance) * inv_scale).erfc()
                - ((right - variance) * inv_scale).erfc()
            )
            negative_tilt = (half_ratio * ((left + variance) * inv_scale).erfc()
                             - twice_ratio * ((right + variance) * inv_scale).erfc())
            total += signed_logp * (constant + tilt * (positive_tilt + negative_tilt)) / 2
        return total

    def evaluate(self, delta):
        if delta.is_zero():
            return self.zero_value
        v = delta**2
        c = (-v/2).exp()
        return (1+c) * self.gaussian(v) - c * self.gaussian(2*v)


def tails(v):
    # These are the integrals from v to infinity of the two weights.
    return ((-4*v).exp() / 4, arb(4).exp() * arb.pi().sqrt() * (v+2).erfc() / 2)


def affine_positive_mean(left, right):
    if left >= 0 and right >= 0:
        return (left + right) / 2
    if left <= 0 and right <= 0:
        return arb(0)
    require((left < 0 < right) or (right < 0 < left), "unresolved endpoint sign")
    top = left if left > 0 else right
    return top**2 / (2 * abs(right - left))


class Integral:
    def __init__(self):
        self.grid = [arb(0), arb(0)]
        self.continuous = [arb(0), arb(0)]

    def add_grid(self, masses, left):
        for sign_id, sign in enumerate((1, -1)):
            self.grid[sign_id] += masses * (sign * left).nonnegative_part()

    def add_continuous(self, mass, left, right, h, curvature_error):
        covariance = abs(right-left) * h**2 / 4
        for sign_id, sign in enumerate((1, -1)):
            a, b = sign * left, sign * right
            if a.max(b) + curvature_error <= 0:
                continue
            centre = mass * affine_positive_mean(a, b)
            radius = mass * curvature_error + covariance
            self.continuous[sign_id] += arb(centre, radius.upper()).nonnegative_part()


def sign_class(value):
    if value > 0:
        return "positive"
    if value < 0:
        return "negative"
    require(value.is_zero(), "unresolved prescribed-grid sign")
    return "zero"


def finite_and_continuous(x):
    n = x*x
    fine = FINE_DENOMINATOR
    require(fine % n == 0, "the output grid must nest in the integration mesh")
    stride = fine // n
    end = arb(x).log().sqrt()
    last = int((end * fine).floor().unique_fmpz())
    require(arb(last)/fine < end < arb(last+1)/fine, "uncertain final cell")

    row = PrimeRow(x)
    aggregators = [Integral() for _ in WEIGHTS]
    coarse_left = old_value = row.zero_value
    coarse_tails = old_tails = tails(arb(0))
    old_delta = arb(0)
    counts = {"positive": 0, "negative": 0, "zero": 0}
    range_low = range_high = old_value

    for index in range(1, last+2):
        endpoint = index == last+1
        delta = end if endpoint else arb(index)/fine
        value = row.evaluate(delta)
        new_tails = tails(delta**2)
        h = delta - old_delta
        curve_error = row.curvature * h**2 / 8
        range_low = range_low.min(old_value.min(value) - curve_error)
        range_high = range_high.max(old_value.max(value) + curve_error)
        for k, integral in enumerate(aggregators):
            mass = old_tails[k] - new_tails[k]
            require(mass > 0, "nonpositive integration cell mass")
            integral.add_continuous(mass, old_value, value, h, curve_error)

        if index % stride == 0 or endpoint:
            counts[sign_class(coarse_left)] += 1
            for k, integral in enumerate(aggregators):
                integral.add_grid(coarse_tails[k] - new_tails[k], coarse_left)
            coarse_left, coarse_tails = value, new_tails
        old_delta, old_value, old_tails = delta, value, new_tails

    require(counts == ({'negative': 30, 'positive': 62, 'zero': 1} if x == 8 else
                       {'negative': 0, 'positive': 1907, 'zero': 0}), "grid sign counts")
    if x == 32:
        require(range_low > fmpq(49, 100), "continuous positive sign at x=32")
    rows = {}
    for label, integral in zip(WEIGHTS, aggregators, strict=True):
        result = {}
        for sign_id, sign_name in enumerate(("positive", "negative")):
            grid = integral.grid[sign_id]
            continuous = integral.continuous[sign_id]
            difference = continuous - grid
            if x == 32 and sign_id == 1:
                require(grid.is_zero() and continuous.is_zero(), "negative mass at x=32")
            else:
                require(grid > 0 and continuous > 0, "missing strictly positive mass")
                if x == 8 and sign_id == 0:
                    require(difference > 0, "finite positive rule should underestimate at x=8")
                else:
                    require(difference < 0, "finite rule should overestimate on this sign")
            result[sign_name] = {
                "prescribed_grid": str(grid),
                "continuous_lower": str(continuous.lower()),
                "continuous_upper": str(continuous.upper()),
                "continuous_minus_grid_lower": str(difference.lower()),
                "continuous_minus_grid_upper": str(difference.upper()),
            }
        rows[label] = result
    return {
        "x": x,
        "prime_cutoff": n,
        "all_prime_count": len(row.full_primes),
        "nonzero_real_character_prime_count": len(row.terms),
        "unsmoothed_real_prime_row": str(row.zero_value),
        "prescribed_delta_denominator": n,
        "prescribed_including_partial_last_cell": sum(counts.values()),
        "prescribed_left_endpoint_counts": counts,
        "continuous_delta_denominator": fine,
        "continuous_including_partial_last_cell": last+1,
        "continuous_row_common_lower": str(range_low.lower()),
        "continuous_row_common_upper": str(range_high.upper()),
        "weights": rows,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, choices=(128, 192), required=True)
    args = parser.parse_args()
    require(flint.__version__ == "0.8.0", "this replay uses python-flint 0.8.0")
    ctx.prec = args.precision
    # At these x the second variant's prime-cutoff minimum is also x^2.
    for x in (8, 32):
        lx = arb(x).log()
        require(6 * lx**fmpq(3, 4) > lx, "alternative cutoff not equal to x^2")

    receipt = {
        "python_flint": flint.__version__,
        "precision_bits": ctx.prec,
        "statistic": "Finite-prime compensated quartic row at one terminal x",
        "cutoffs": [finite_and_continuous(x) for x in (8, 32)],
    }
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
