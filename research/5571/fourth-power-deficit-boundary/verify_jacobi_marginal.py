"""Integer-only certificate for whole rows of minimum rational Jacobi-class deficits."""

from functools import cache
from fractions import Fraction
from math import factorial, gcd, isqrt, prod


ROWS = {
    12: (8916111053933, 8916111354233),
    16: (281474983810103, 281474989846133),
    24: (36520347437664173, 36520347441087593),
    32: (1152921504614729933, 1152921504623798993),
    40: (16777216000046562143, 16777216000127523023),
    48: (149587343098188695783, 149587343098255062083),
    60: (2176782336000004572923, 2176782336000141269483),
}
LUCAS = {
    1451899187: (2, [2, 61, 89, 133717]),
    4204246933: (2, [2, 2, 3, 3, 116784637]),
    14129466457: (10, [2, 2, 2, 3, 7, 199, 211, 2003]),
    16002171331: (2, [2, 3, 5, 1109, 480979]),
    76863026327: (5, [2, 4139, 9285217]),
    81306354473: (3, [2, 2, 2, 7, 1451899187]),
    92493432527: (5, [2, 11, 4204246933]),
    124635343981: (10, [2, 2, 3, 5, 7, 71, 857, 4877]),
    562821283459: (13, [2, 3, 3, 7, 7, 638119369]),
    1114513919279: (13, [2, 109, 601, 8506571]),
    1580716157747: (2, [2, 11, 283, 253889521]),
    8916111053933: (2, [2, 2, 29, 76863026327]),
    8916111354233: (3, [2, 2, 2, 1114513919279]),
    26173422236011: (7, [2, 3, 5, 7, 124635343981]),
    60490704872659: (3, [2, 3, 109, 92493432527]),
    281474983810103: (5, [2, 53, 5851, 453841117]),
    281474989846133: (2, [2, 2, 659, 10607, 10067041]),
    545890863931723: (3, [2, 3, 3, 373, 81306354473]),
    36520347437664173: (2, [2, 2, 570553, 16002171331]),
    36520347441087593: (3, [2, 2, 2, 8111, 562821283459]),
    72057594038987437: (2, [2, 2, 3, 11, 545890863931723]),
    1152921504614729933: (2, [2, 2, 270037, 978347, 1090997]),
    1152921504623798993: (3, [2, 2, 2, 2, 72057594038987437]),
    16777216000046562143: (5, [2, 145963, 443437, 129603041]),
    16777216000127523023: (5, [2, 17, 17, 1109, 26173422236011]),
    74793671549127531041: (3, [2, 2, 2, 2, 2, 5, 295727, 1580716157747]),
    149587343098188695783: (5, [2, 1236449, 60490704872659]),
    149587343098255062083: (2, [2, 74793671549127531041]),
    2176782336000004572923: (2, [2, 103, 1831, 18526231, 311510267]),
    2176782336000141269483: (2, [2, 185051, 416263, 14129466457]),
}


@cache
def prime_certificate(n):
    if n < 10**9:
        return n >= 2 and all(n % d != 0 for d in range(2, isqrt(n) + 1))
    base, factors = LUCAS[n]
    return (
        prod(factors) == n - 1
        and all(prime_certificate(p) for p in factors)
        and pow(base, n - 1, n) == 1
        and all(gcd(pow(base, (n - 1)//p, n) - 1, n) == 1 for p in set(factors))
    )


SCALE = 1 << 44


def log_ratio_lower(numer, denom):
    """A scaled lower bound for 2*atanh(numer/denom), using positive terms."""
    argument = numer * SCALE // denom
    argument_squared = argument * argument // SCALE
    power = argument
    total = 0
    for k in range(12):
        total += power // (2*k + 1)
        power = power * argument_squared // SCALE
    return 2 * total


LOG_TWO_LOWER = log_ratio_lower(1, 3)


def log_lower(p):
    k = p.bit_length() - 1
    unit = 1 << k
    return k * LOG_TWO_LOWER + log_ratio_lower(p - unit, p + unit)


def odd_prime_weights(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\0\0"
    for p in range(2, isqrt(limit)+1):
        if sieve[p]:
            sieve[p*p::p] = bytes((limit - p*p)//p+1)
    return [(p, log_lower(p)) for p in range(3, limit+1, 2) if sieve[p]]


def verify_row(cutoff, q, weights):
    assert prime_certificate(q)
    assert cutoff**12 < q <= 2 * cutoff**12
    total_weight = weighted_prime_sum = index = 0
    margins = []
    for j in range(2, cutoff+1):
        x = j**4
        while index < len(weights) and weights[index][0] <= x:
            p, weight = weights[index]
            index += 1
            if pow(q % p, (p-1)//2, p) == p-1:
                total_weight += weight
                weighted_prime_sum += p * weight
        lower = 4 * (x * total_weight - weighted_prime_sum)
        required = x*x * SCALE
        assert lower > required, (cutoff, q, j)
        margins.append(((lower - required) * 10**9 // required, j))
    return min(margins)


def verify_need_to_change_class(weights):
    q, d = ROWS[12]
    psmall = (3, 5, 7, 11, 13)
    for p in psmall:
        assert all(pow(a % p, (p-1)//2, p) == p-1 for a in (q, d))
    # Both mixed cells are empty at the second sample. Bound the -- cell at sample 11.
    log_two_upper = Fraction(694, 1000)
    assert sum(log_two_upper**k / factorial(k) for k in range(6)) > 2
    x = 11**4
    numerator = 0
    for p, _ in weights:
        if p > x:
            break
        if any(pow(a % p, (p-1)//2, p) != p-1 for a in (q,d)):
            continue
        upper_integer = (p**256).bit_length()
        n = p
        while n <= x:
            numerator += (x-n) * upper_integer
            n *= p*p
    complete_upper = Fraction(4*numerator, 256) * log_two_upper
    deficit_lower = Fraction(x*x, 2) - complete_upper
    assert deficit_lower > 128
    return deficit_lower.numerator // deficit_lower.denominator


if __name__ == "__main__":
    weights = odd_prime_weights(max(ROWS)**4)
    for cutoff, primes in ROWS.items():
        for q in primes:
            margin, j = verify_row(cutoff, q, weights)
            print(f"J={cutoff} q={q} min_margin_ppb={margin} at j={j}", flush=True)
    print(f"J=12 fixed -- deficit at j=11 exceeds {verify_need_to_change_class(weights)}")
