"""Check the exact ramified packet coefficients and two complete mod-5 traces.

Run with python-flint 0.9.0. Supply the previous fixed-profile prime_check.py on
the command line. Its immutable source link is in the adjoining write-up.
"""

from functools import lru_cache
from math import gcd, isqrt
from pathlib import Path
import importlib.util
import json
import sys

from flint import acb, arb, ctx, dirichlet_char, dirichlet_group, fmpq, fmpz, fmpz_poly

ctx.prec = 224


@lru_cache(None)
def units(q):
    return [i for i in range(1, q+1) if gcd(i, q) == 1]


def prime_base(n):
    for p in range(2, isqrt(n)+1):
        if n % p == 0:
            while n % p == 0:
                n //= p
            return p if n == 1 else None
    return n


@lru_cache(None)
def part_at(q, p):
    part = 1
    while q % p == 0:
        q //= p
        part *= p
    return part, q


def primitive_phase(character, q, n):
    modulus = int(character.conductor())
    if gcd(n, modulus) != 1:
        return None
    # The primitive inducer at a unit of its conductor is evaluated by any
    # lift which is also a unit of the original, possibly larger modulus.
    lift = next(t for t in units(q) if (t-n) % modulus == 0)
    return int(character.chi_exponent(lift))


def check_coefficients():
    pairs = [(n, prime_base(n)) for n in range(2, 84)]
    powers = [(n, p) for n, p in pairs if p is not None]
    checked = ramified = parity_checked = 0
    for q in range(1, 49):
        group = units(q)
        order = int(dirichlet_group(q).exponent())
        cyclotomic = fmpz_poly.cyclotomic(order)
        characters = [dirichlet_char(q, j) for j in group]
        for r in group:
            inv_phases = [-int(chi.chi_exponent(r)) for chi in characters]
            # The two projections are supported precisely on the residues ±1.
            for a in (0, 1):
                counts = [0]*order
                for character, exponent in zip(characters, inv_phases):
                    if int(character.parity()) == a:
                        counts[exponent % order] += 2
                target = len(group)*(int((r-1) % q == 0) + (-1)**a*int((r+1) % q == 0))
                counts[0] -= target
                assert not (fmpz_poly(counts) % cyclotomic)
                parity_checked += 1
            for n, p in powers:
                counts = [0]*order
                for chi, exponent in zip(characters, inv_phases):
                    phase = primitive_phase(chi, q, n)
                    if phase is not None:
                        counts[(exponent + phase) % order] += 1
                part, other = part_at(q, p)
                weight = fmpq(int((r-n) % other == 0), fmpz(part).euler_phi())
                expected_sum = weight * len(group)
                assert expected_sum.denominator == 1
                counts[0] -= int(expected_sum)
                assert not (fmpz_poly(counts) % cyclotomic)
                checked += 1
                ramified += int(part > 1)
    return dict(moduli="1..48", prime_powers="2..83", exact_packet_checks=checked,
                ramified_checks=ramified, exact_parity_checks=parity_checked)


def check_signed_products():
    samples = [(1, 1), (1, 2), (2, 1), (4, 4), (8, 9), (15, 35),
               (18, 45), (50, 20), (77, 49), (75, 75), (125, 5), (48, 35)]
    tests = off_diagonal = 0
    for q in range(1, 49):
        members = units(q)
        exponent = int(dirichlet_group(q).exponent())
        relation = fmpz_poly.cyclotomic(exponent)
        characters = [dirichlet_char(q, j) for j in members]
        for u, v in samples:
            rest = q
            while gcd(rest, u*v) > 1:
                rest //= gcd(rest, u*v)
            for b in (0, 1):
                coeff = [0]*exponent
                for chi in characters:
                    pu, pv = primitive_phase(chi, q, u), primitive_phase(chi, q, v)
                    if pu is not None and pv is not None:
                        parity_phase = int(chi.chi_exponent(q-1 if q>1 else 1))
                        coeff[(pu-pv+b*parity_phase) % exponent] += 1
                diff = (-1)**b*u-v
                expected = fmpq(len(members)*int(diff % rest == 0), fmpz(q//rest).euler_phi())
                assert expected.denominator == 1
                coeff[0] -= int(expected)
                assert not (fmpz_poly(coeff) % relation)
                tests += 1
                off_diagonal += int(diff != 0 and expected != 0)
    return {"checks":tests, "nonzero_off_diagonals":off_diagonal}



def odd_arch_mass(center, eps):
    last = 81
    lower = arb(0)
    for m in range(1, last+1, 2):
        t = arb(m)
        # P(-m)=(m^2-1/4)m(m+1).
        term = (t*t-fmpq(1, 4))*t*(t+1)*(-t*center).exp()*( (t/16).sinh()/(t/16) )**16 / 10000
        lower += term * arb(1).union((t*eps).cosh())
    first = last+2
    rate = (-arb(center-1-eps)).exp()
    # P(-m) <= 2m^4; also each box transform costs <= exp(m/16).
    head = fmpq(2, 10000)*first**4*rate**first
    ratio = fmpq(first+2, first)**4*rate**2
    assert ratio < 1
    return lower + arb(0).union((head/(1-ratio)).upper())


def check_example(profile):
    q = 5
    rows = []
    characters = [dirichlet_char(5, j) for j in units(5)]
    roots = [acb(1), acb(0,1), acb(-1), acb(0,-1)]
    for center in profile.centers:
        _, previous = profile.prime_side(center)
        numbers = sorted(map(int, previous["prime_terms"]))
        terms = {n: arb(prime_base(n)).log()*profile.mollified_profile(arb(n).log(), center)
                 for n in numbers}
        even = profile.trivial_zero_mass(center)[0]
        odd = odd_arch_mass(center, profile.epsilon)
        individual = {}
        for chi in characters:
            total = -acb(even if int(chi.parity()) == 0 else odd)
            for n in numbers:
                phase = primitive_phase(chi, 5, n)
                if phase is not None:
                    total -= roots[phase % 4]*terms[n]
            individual[int(chi.number())] = total
        spaces = {}
        for r in units(q):
            via_fourier = sum((roots[(-int(chi.chi_exponent(r))) % 4]*individual[int(chi.number())]
                               for chi in characters), acb(0))/4
            plus, minus = int(r == 1), int(r == 4)
            direct = -(plus+minus)*even/2-(plus-minus)*odd/2
            for n, term in terms.items():
                ppart, other = part_at(q, prime_base(n))
                if (r-n) % other == 0:
                    direct -= term / fmpz(ppart).euler_phi()
            assert via_fourier.imag.contains(0) and via_fourier.real.overlaps(direct)
            spaces[r] = str(direct)
        quartic = individual[2]
        assert not quartic.imag.contains(0)
        for value in individual.values():
            assert value.real.rad() < fmpq(1, 10**12) and value.imag.rad() < fmpq(1, 10**12)
        rows.append(dict(center=str(center), full_trace_by_conrey_character={k:str(v) for k,v in individual.items()},
                         full_trace_by_angular_residue=spaces, even_arch=str(even), odd_arch=str(odd)))
    return rows


def main():
    point = Path(sys.argv[1]).resolve(strict=True)
    spec = importlib.util.spec_from_file_location("original_fixed_profile", point)
    profile = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(profile)
    result = {"exact":check_coefficients(), "mixed":check_signed_products(), "modulus_five":check_example(profile), "precision_bits":ctx.prec}
    Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(result["exact"])
    for row in result["modulus_five"]:
        print("center",row["center"],"chi(2)=i",row["full_trace_by_conrey_character"][2],
              "r=2",row["full_trace_by_angular_residue"][2])


if __name__ == "__main__":
    main()
