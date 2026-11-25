"""Certify finite ordinary-prime fourth-power deficits using exact arithmetic.

Let theta(x) = sum_{p<=x} log(p), d(x) = x^2/2 - sum_{p<=x} (x-p)log(p),
and D(J) = sum_{j=1}^J max(0,d(j^4)). All logarithms are natural.

Jan Büthe, Theorem 2 (1.6) and (1.7), https://arxiv.org/pdf/1511.02032#page=2
proves 0.05 sqrt(t) < t-theta(t) on [1,10^19] and t-theta(t) <= 1.95 sqrt(t)
on [1423,10^19]. The bibliographic source supplies those two inequalities.
Since d(y)-d(x) is the integral of t-theta(t) from x to y, d(1)=1/2 gives
d(x) >= x^(3/2)/30 + 7/15 on [1,10^19]. The upper derivative bound and
the checked value at 1423 give d(x) <= 13 x^(3/2)/10 on [1423,10^19].
The six earlier fourth powers are checked individually below. Hence for
each integer 1 <= J <= 56234, every d(j^4) is positive and

    sum_{j=1}^J j^6 / 30 + 7 J / 15 <= D(J) <= (13/10) sum_{j=1}^J j^6.

Run with standard Python 3. No network or third-party packages are required.
"""

from fractions import Fraction
from math import isqrt


SCALE = 10**12
TERMS = 16
ANCHOR = 1423
LIMIT = 10**19
LAST_INDEX = 56234


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def primes_through(limit):
    return [
        n for n in range(2, limit + 1)
        if all(n % divisor != 0 for divisor in range(2, isqrt(n) + 1))
    ]


def twice_atanh_bounds(z):
    """Bound log((1+z)/(1-z)) for an exact rational 0 <= z <= 1/3."""
    require(0 <= z <= Fraction(1, 3), "invalid logarithm-series argument")
    squared = z * z
    power = z
    lower = Fraction(0)
    for term in range(TERMS):
        lower += 2 * power / (2 * term + 1)
        power *= squared
    # The first omitted power is z^(2*TERMS+1). Bound the rest by a
    # geometric series after replacing every denominator by 2*TERMS+1.
    remainder = 2 * power / ((2 * TERMS + 1) * (1 - squared))
    return lower, lower + remainder


def scaled_log_bounds(n, log_two):
    """Return integers L,U with L/SCALE <= log(n) <= U/SCALE."""
    exponent = n.bit_length() - 1
    power_of_two = 1 << exponent
    low, high = twice_atanh_bounds(Fraction(n - power_of_two, n + power_of_two))
    low += exponent * log_two[0]
    high += exponent * log_two[1]
    lower = (SCALE * low.numerator) // low.denominator
    upper = -((-SCALE * high.numerator) // high.denominator)
    return lower, upper


def deficit_bounds(x, prime_logs):
    """Enclose SCALE*d(x) by integers, reversing log endpoints on subtraction."""
    lower = upper = (SCALE * x * x) // 2
    for prime, (log_lower, log_upper) in prime_logs:
        if prime > x:
            break
        lower -= (x - prime) * log_upper
        upper -= (x - prime) * log_lower
    require(0 <= lower <= upper, f"positivity or interval error at x={x}")
    return lower, upper


def fixed_decimal(value):
    whole, fraction = divmod(value, SCALE)
    return f"{whole}.{fraction:012d}"


def main():
    require(6**4 < ANCHOR < 7**4, "initial grid is incomplete")
    require(LAST_INDEX**4 <= LIMIT < (LAST_INDEX + 1)**4, "wrong final index")
    primes = primes_through(ANCHOR)
    log_two = twice_atanh_bounds(Fraction(1, 3))
    prime_logs = [(p, scaled_log_bounds(p, log_two)) for p in primes]

    for j in range(1, 7):
        x = j**4
        lower, upper = deficit_bounds(x, prime_logs)
        require(30 * lower >= (j**6 + 14) * SCALE, f"lower bound fails at j={j}")
        require(10 * upper <= 13 * j**6 * SCALE, f"upper bound fails at j={j}")
        print(f"j={j}, x={x}, d(x) in [{fixed_decimal(lower)}, {fixed_decimal(upper)}]")

    lower, upper = deficit_bounds(ANCHOR, prime_logs)
    # Both sides are nonnegative, so compare 10*d(1423) <= 13*1423^(3/2)
    # by squaring the outward upper endpoint before cancelling SCALE.
    require(100 * upper**2 <= 169 * ANCHOR**3 * SCALE**2, "anchor upper bound fails")
    print(f"x={ANCHOR}, d(x) in [{fixed_decimal(lower)}, {fixed_decimal(upper)}]")
    print(f"{LAST_INDEX}^4 = {LAST_INDEX**4} <= {LIMIT} < {(LAST_INDEX + 1)**4} = {LAST_INDEX+1}^4")
    print(f"Verified both cumulative bounds for 1 <= J <= {LAST_INDEX} using {len(primes)} small primes.")


if __name__ == "__main__":
    main()
