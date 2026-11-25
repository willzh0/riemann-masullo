"""Finite checks of the cell and moment identities. Run with Python, NumPy and SymPy."""
from collections import Counter
from itertools import combinations, permutations, product
from math import log, sqrt
from random import Random

import numpy as np
from sympy import isprime, primerange


def symbol(q, p):
    if p == 2:
        return 1
    value = pow(q % p, (p - 1) // 2, p)
    assert value in (1, p - 1)
    return 1 if value == 1 else -1


def exact_moments():
    """Enumerate every prime in (2^12,2*2^12], using small integer weights."""
    aux = list(primerange(2**12 + 1, 2**13 + 1))
    small = [3, 5, 7, 11, 13]
    weights = [13, 11, 9, 5, 3]
    signs = np.array([[symbol(q, p) for p in small] for q in aux], dtype=np.int64)
    gram = (signs * weights) @ signs.T
    for k in range(1, 5):
        coefficients = Counter()
        for indices in product(range(len(small)), repeat=k):
            mask, weight = 0, 1
            for i in indices:
                mask ^= 1 << i
                weight *= weights[i]
            coefficients[mask] += weight
        predicted = 0
        for mask, weight in coefficients.items():
            cols = [i for i in range(len(small)) if (mask >> i) & 1]
            column_sums = int(np.prod(signs[:, cols], axis=1).sum()) if cols else len(aux)
            predicted += weight * column_sums**2
        full_sum = int((gram**k).sum())
        distinct_sum = int((gram**k)[~np.eye(len(aux), dtype=bool)].sum())
        assert predicted == full_sum
        assert distinct_sum == full_sum - len(aux) * sum(weights)**k
        if k == 4:
            assert coefficients[0] == 3 * sum(w**2 for w in weights)**2 - 2 * sum(w**4 for w in weights)
    return len(aux)


def exact_sieve():
    """Check the optimizing weights and their majorant exactly at a finite radius."""
    from fractions import Fraction
    from math import gcd, lcm
    from sympy import mobius, totient

    radius, Q = 30, 2**12
    divisors = [d for d in range(1, radius + 1) if mobius(d)]
    mu = {d: int(mobius(d)) for d in divisors}
    phi = {d: int(totient(d)) for d in divisors}
    G = sum(Fraction(1, phi[d]) for d in divisors)
    weights = {
        d: Fraction(mu[d] * d, phi[d]) / G
        * sum(Fraction(1, phi[m]) for m in divisors if m <= radius // d and gcd(m, d) == 1)
        for d in divisors
    }
    assert weights[1] == 1 and all(abs(w) <= 1 for w in weights.values())
    for r in divisors:
        assert sum(weights[d]/d for d in divisors if d % r == 0) == Fraction(mu[r], phi[r])/G
    assert sum(weights[d]*weights[e]/lcm(d, e) for d in divisors for e in divisors) == 1/G
    W = [sum(weights[d] for d in divisors if n % d == 0)**2 for n in range(Q + 1, 2*Q + 1)]
    assert all(W[q - Q - 1] == 1 for q in primerange(Q+1, 2*Q+1))
    assert abs(sum(W) - Q/G) <= radius**2
    return radius


def exact_distinct_partition():
    """Average over uneven labeled blocks and check the complete distinct-tuple law."""
    primes = tuple(primerange(2**12 + 1, 2**12 + 160))[:7]
    assert len(primes) == 7

    def partitions(values, sizes):
        if len(sizes) == 1:
            yield (values,)
            return
        for first in combinations(values, sizes[0]):
            rest = tuple(q for q in values if q not in first)
            for other in partitions(rest, sizes[1:]):
                yield (first, *other)

    for sizes in [(3, 2, 2), (2, 2, 2, 1)]:
        tally = Counter()
        for blocks in partitions(primes, sizes):
            for sample in product(*blocks):
                tally[sample] += 1
            left = len(sizes) // 2
            for half in (blocks[:left], blocks[left:]):
                from math import prod
                factors = [prod(t) for t in product(*half)]
                assert len(factors) == len(set(factors))
        assert set(tally) == set(permutations(primes, len(sizes)))
        assert len(set(tally.values())) == 1
    return len(primes)


def sample_primes(J, size):
    rng = Random(55717627)
    Q = J**12
    chosen = set()
    while len(chosen) < size:
        q = rng.randrange(Q + 1, 2 * Q, 2)
        if isprime(q):
            chosen.add(q)
    # The sample falls below 2^64, where SymPy's primality result is deterministic.
    assert max(chosen) < 2**64
    return sorted(chosen)


def check_cumulative(J=12, size=96):
    """Enumerate all distinct pairs in a reproducible subsample, including actual powers."""
    aux = sample_primes(J, size)
    primes = list(primerange(2, J**4 + 1))
    logs = np.log(primes)
    signs = np.array([[symbol(q, p) for p in primes] for q in aux], dtype=float)
    mask = ~np.eye(size, dtype=bool)
    fixed_gain = np.zeros((size, size))
    union_full = np.zeros((size, size))
    adaptive_full = np.zeros((size, size))
    for j in range(1, J+1):
        x = j**4
        b = np.maximum(0, x - np.array(primes)) * logs
        higher = np.zeros(len(primes))
        for i, p in enumerate(primes):
            power = p**3
            while power < x:
                higher[i] += (x-power) * logs[i]
                power *= p**2

        def cells(weights):
            single = signs @ weights
            kernel = (signs * weights) @ signs.T
            base = weights.sum()
            return {
                (e, f): base + e*single[:, None] + f*single[None, :] + e*f*kernel
                for e, f in [(1, -1), (-1, 1), (-1, -1)]
            }

        prime, correction = cells(b), cells(higher)
        full = {key: prime[key] + correction[key] for key in prime}
        center = x*x/2
        prime_def = np.maximum(0, center - prime[1, -1])
        full_def = np.maximum(0, center - full[1, -1])
        gain = prime_def - full_def
        assert np.allclose(gain, np.minimum(prime_def, correction[1, -1]), atol=1e-6)
        fixed_gain += gain
        union = (full[1, -1] + full[-1, 1]) / 2
        union_full += np.maximum(0, center - union)
        adaptive_full += np.minimum.reduce([np.maximum(0, center - a) for a in full.values()])

        for a, d in [(0, 1), (3, 12), (9, 20)]:
            for e, f in prime:
                actual_prime = actual_full = 0.0
                for i, p in enumerate(primes):
                    if p >= x:
                        break
                    power, k = p, 1
                    while power < x:
                        if symbol(aux[a], p)**k == e and symbol(aux[d], p)**k == f:
                            actual_full += 4*(x-power)*log(p)
                            if k == 1:
                                actual_prime += 4*(x-power)*log(p)
                        k += 1
                        power *= p
                assert np.isclose(prime[e, f][a, d], actual_prime, atol=1e-6)
                assert np.isclose(full[e, f][a, d], actual_full, atol=1e-6)
    # The p=2 term in the auxiliary product is constant and removed in the moment theorem.
    bo, xo = b[1:], signs[:, 1:]
    standardized = ((xo * bo) @ xo.T)[mask] / np.linalg.norm(bo)
    moments = [np.mean(standardized**k) for k in range(1, 5)]
    assert np.all(adaptive_full <= union_full + 1e-6)
    print(f"J={J}, actual primes={size}, ordered distinct pairs={int(mask.sum())}")
    print("off-diagonal terminal standardized moments:", [round(v.item(), 5) for v in moments])
    print("fixed mixed gain / J^(19/3):", round(float(fixed_gain[mask].mean()/J**(19/3)), 6))
    scale = J**7 * sqrt(log(J))
    print("parity-union complete H / (J^7 sqrt(log J)):", round(float(union_full[mask].mean()/scale), 6))
    print("best complete H / (J^7 sqrt(log J)):", round(float(adaptive_full[mask].mean()/scale), 6))


if __name__ == "__main__":
    print("Balanced distinct-tuple laws and unique factor products:", exact_distinct_partition(), "primes")
    print("Exact Selberg weights, quadratic form, and interval majorant at radius", exact_sieve())
    print("Exact integer moments and diagonal check:", exact_moments(), "primes in the entire J=2 interval")
    check_cumulative()
