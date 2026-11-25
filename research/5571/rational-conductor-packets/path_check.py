"""Finite checks for BASE-TWIST-PATHS.md. The proof of the limit is in the note.

The small character calculation uses 160-bit Arb enclosures. The large prime
sums are ordinary floating-point illustrations of the two covariance constants.
Run with Python and python-flint.
"""
from itertools import combinations_with_replacement
import json
from math import isqrt, log
from pathlib import Path
from flint import arb, ctx, dirichlet_char, fmpz

ctx.prec = 160


def good_primes(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for n in range(2, isqrt(limit) + 1):
        if sieve[n]:
            sieve[n * n::n] = bytes((limit - n * n) // n + 1)
    return sieve


def gaussian_terms(sieve):
    """Return the degree-one split representatives a+ib, with a<b."""
    limit = len(sieve) - 1
    terms = {}
    for a in range(1, isqrt(limit // 2) + 1):
        for b in range(a + 1, isqrt(limit - a * a) + 1):
            p = a * a + b * b
            if sieve[p]:
                assert p not in terms and p % 4 == 1
                terms[p] = 2 * (a**4 - 6 * a * a * b * b + b**4)
    assert len(terms) == sum(sieve[5::4])
    return terms


def coefficients(p, terms, make):
    one = make(1)
    if p == 2:
        return one, one, -one
    if p % 4 == 3:
        return one, make(0), make(0)
    return one, make(2), make(terms[p]) / (p * p)


def finite_character_check():
    limit, level = 16, 263
    assert level > limit**2 and fmpz(level).is_prime()
    sieve = good_primes(limit)
    terms = gaussian_terms(sieve)
    primes = [p for p in range(limit) if sieve[p]]
    aux = (4099, 4111)
    assert all(fmpz(a).is_prime() for a in aux)
    classes = [tuple(1 if p == 2 else int(fmpz(a).jacobi(p)) for a in aux) for p in primes]
    masks = [None, (-1,-1), (-1,1), (1,-1), (1,1)]
    keys = [(x, mask) for x in (8, 12, 16) for mask in masks]
    pairs = list(combinations_with_replacement(range(len(keys)), 2))
    counts = []
    for field in range(3):
        angular = [coefficients(p, terms, arb)[field] for p in primes]
        rows = [
            [arb(max(0, x-p)) * arb(p).log() * coeff *
             (1 if mask is None else 4 * (cell == mask))
             for p, coeff, cell in zip(primes, angular, classes)]
            for x, mask in keys
        ]
        raw = [arb(0) for _ in pairs]
        principal = [sum(row, arb(0)) for row in rows]
        for label in range(2, level):
            char = dirichlet_char(level, label)
            assert not char.is_principal()
            values = [char(p).real for p in primes]
            sites = [sum((w*v for w,v in zip(row,values)), arb(0)) for row in rows]
            for j, (i,k) in enumerate(pairs):
                raw[j] += sites[i] * sites[k]
        for j, (i,k) in enumerate(pairs):
            energy = sum((a*b for a,b in zip(rows[i],rows[k])), arb(0))
            exact = (level-1) * energy/2 - principal[i]*principal[k]
            difference = (raw[j]-exact)/(level-2)
            assert difference.contains(0) and difference.rad() < arb("1e-30")
        counts.append(len(pairs))
    return dict(level=level, primitive_characters=level-2, maximum_cutoff=limit,
                cutoffs=[8,12,16], fields=["Q", "Q(i) principal", "Q(i) angular weight four"],
                primitive_second_moment_checks=counts, interval_bits=ctx.prec)


def numerical_energies():
    stops = [10_000, 100_000, 1_000_000]
    sieve = good_primes(stops[-1])
    terms = gaussian_terms(sieve)
    output = []
    for n in stops:
        totals = [0.0, 0.0, 0.0]
        riesz = [0.0, 0.0, 0.0]
        for p in range(2, n+1):
            if not sieve[p]:
                continue
            lp = log(p)
            for i, value in enumerate(coefficients(p, terms, float)):
                totals[i] += lp * value * value
                riesz[i] += ((n-p) * lp * value)**2
        output.append(dict(cutoff=n, logarithmic_prime_mass_over_x=[v/n for v in totals],
                           riesz_energy_relative_to_Q=[v/riesz[0] for v in riesz]))
    return output


if __name__ == "__main__":
    data = dict(character_check=finite_character_check(),
                finite_floating_point_examples=numerical_energies(),
                predicted_multiplicities=[1,2,1])
    Path(__file__).with_suffix(".json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(data))
