"""Recompute four inclusive cutoff #7703 moments for chi(2)=i using integer intervals."""

from math import comb, factorial, isqrt

BITS = 128
UNIT = 1 << BITS
TERMS = 48
ZERO = (0, 0)
DIGITS = 15


def ceil_div(x, y):
    return -(-x // y)


def rational(num, den=1):
    assert den > 0
    return (num * UNIT // den, ceil_div(num * UNIT, den))


def plus(x, y):
    return (x[0] + y[0], x[1] + y[1])


def times(x, y):
    products = tuple(a * b for a in x for b in y)
    return (min(products) // UNIT, ceil_div(max(products), UNIT))


def scaled(x, n, d=1):
    assert d > 0
    lo, hi = sorted((x[0] * n, x[1] * n))
    return (lo // d, ceil_div(hi, d))


def log_on_one_two(a, b):
    """Enclose log(a/b), with b <= a <= 2b, using the atanh series."""
    assert b <= a <= 2 * b
    u = rational(a - b, a + b)
    u2 = times(u, u)
    partial = ZERO
    for j in range(TERMS - 1, -1, -1):
        partial = plus(rational(1, 2 * j + 1), times(u2, partial))
    lo, hi = scaled(times(u, partial), 2)
    # First omitted geometric majorant is 9/[4(2J+1)3^(2J+1)].
    assert 9 * UNIT < 4 * (2 * TERMS + 1) * 3 ** (2 * TERMS + 1)
    return (lo, hi + 1)


LOG2 = log_on_one_two(2, 1)


def log_integer(m):
    assert m > 0
    e = m.bit_length() - 1
    return plus(scaled(LOG2, e), log_on_one_two(m, 1 << e))


def prime_list(x):
    sieve = bytearray([1]) * (x + 1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(x) + 1):
        if sieve[p]:
            j = p * p
            sieve[j::p] = bytes((x - j) // p + 1)
    return [p for p in range(2, x + 1) if sieve[p]]


def laguerre(n, x):
    acc = ZERO
    for j in range(n, 0, -1):
        acc = plus(rational(comb(n - 1, j - 1), factorial(j)), times(x, acc))
    return times(x, acc)


def moment(n, primes):
    cutoff = 25**n
    total = ZERO
    powers = active = 0
    exponent = {1: 0, 2: 1, 3: 3, 4: 2}
    real_part = (1, 0, -1, 0)
    for p in primes:
        if p > cutoff:
            break
        ell, m = 1, p
        logp = None
        while m <= cutoff:
            powers += 1
            real_weight = 0 if p == 5 else real_part[(exponent[p % 5] * ell) % 4]
            if real_weight:
                active += 1
                if logp is None:
                    logp = log_integer(p)
                poly = laguerre(n, scaled(logp, -3 * ell))
                total = plus(total, scaled(poly, n * real_weight, ell * m**2))
            ell += 1
            m *= p
    return total, powers, active


def fixed(v):
    d = 10**DIGITS
    return ('-' if v < 0 else '') + f'{abs(v)//d}.{abs(v)%d:0{DIGITS}d}'


def printed(interval):
    lo, hi = interval
    return '[' + fixed(lo*10**DIGITS//UNIT) + ', ' + fixed(ceil_div(hi*10**DIGITS, UNIT)) + ']'


if __name__ == '__main__':
    primes = prime_list(25**4)
    print(f'{BITS} fixed-point fractional bits, {TERMS} log-series terms, inclusive cutoffs')
    pos = neg = rational(1)
    for n in range(1, 5):
        value, powers, active = moment(n, primes)
        pos = plus(pos, (max(0,value[0]), max(0,value[1])))
        neg = plus(neg, (max(0,-value[1]), max(0,-value[0])))
        assert max(abs(value[0]-UNIT), abs(value[1]-UNIT))*25 < 146*n*UNIT
        print(f'n={n} X={25**n} prime_powers={powers} nonzero_real_weights={active} E={printed(value)}')
    print(f'positive_prefix(4)={printed(pos)} negative_prefix(4)={printed(neg)}')
    T = max(10**8//5, 37500000//5 + 200)
    N = T*T//9
    assert 9*N <= T*T < 9*(N+1)
    print(f'T={T} inclusive_N={N} T_squared_minus_9N={T*T-9*N}')
