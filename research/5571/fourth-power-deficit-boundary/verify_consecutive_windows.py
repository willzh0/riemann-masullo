"""Certify two opposite complete behaviors on a single genuine window.

Uses the reproducible 96-prime family at J=12 and exact integer bounds on log p.
The counts refer only to this finite sample. Run beside the two companion verifiers.
"""
from fractions import Fraction
from math import factorial

import numpy as np
from sympy import integer_nthroot, primerange

from verify_jacobi_marginal import SCALE as ORIGINAL_SCALE, log_lower
from verify_product_moments import sample_primes, symbol


def main():
    cutoff = 12
    scale = 1 << 20
    aux = sample_primes(cutoff, 96)
    primes = [int(p) for p in primerange(3, cutoff**4 + 1)]
    # e^0.694 > 2 by a rational lower Taylor sum, so 0.694 is an upper bound on log 2.
    assert sum(Fraction(694, 1000)**k / factorial(k) for k in range(6)) > 2
    denom = 1000 * 1024
    lows = [log_lower(p) * scale // ORIGINAL_SCALE for p in primes]
    highs = [(694 * (p**1024).bit_length() * scale + denom-1) // denom for p in primes]
    plus = np.array([[int(symbol(q, p) == 1) for p in primes] for q in aux], dtype=np.int64)
    minus = 1 - plus
    distinct = ~np.eye(len(aux), dtype=bool)
    always_zero = distinct.copy()
    always_saturated = distinct.copy()

    for j in range(9, 13):
        x = j**4
        prime = [max(0, x - p) for p in primes]
        powers = []
        for p in primes:
            mass, power = 0, p**3
            while power < x:
                mass += x - power
                power *= p * p
            powers.append(mass)
        total = [a+b for a, b in zip(prime, powers)]
        # Each mixed cell is four times a sub-sum. Positive coefficients give two intervals.
        def fourfold(weights, logs):
            raw = [a*b for a,b in zip(weights, logs)]
            assert 8 * sum(raw) < 2**63
            return 4 * (plus * np.array(raw, dtype=np.int64)) @ minus.T

        complete_lower = fourfold(total, lows)
        complete_upper = fourfold(total, highs)
        power_lower = fourfold(powers, lows)
        required, exact = integer_nthroot(j**16 * scale**3, 3)
        cube_threshold = int(required) if exact else int(required) + 1
        always_zero &= 2 * complete_lower >= x*x*scale
        always_saturated &= (2 * complete_upper < x*x*scale) & (2 * power_lower >= cube_threshold)
    zeros, full = int(always_zero.sum()), int(always_saturated.sum())
    assert not np.any(always_zero & always_saturated)
    # Transposing enumerates the other preassigned mixed orientation with identical counts.
    print(f"J={cutoff}, fixed mixed class, {len(aux)} primes, {int(distinct.sum())} ordered distinct pairs")
    print(f"Samples 9, 10, 11, 12: {zeros} have identically zero true deficit")
    print(f"Samples 9, 10, 11, 12: {full} have positive true deficit and gain >= j^(16/3)/2 throughout")
    assert zeros > 0 and full > 0


if __name__ == "__main__":
    main()
