"""Check the expanding Poisson product and archimedean constants with interval arithmetic."""
import json
from math import comb
from pathlib import Path
from flint import arb, acb, fmpq, ctx

ctx.prec = 256
pi = arb.pi()
phase = {
    "zeta": (1,),
    "chi4": (0, 1, 0, -1),
    "chi5": (0, 1, acb(0, 1), acb(0, -1), -1),
}


def logder_bounds(s, char, cutoff=64):
    values = phase[char]
    terms = [acb(values[j % len(values)]) * (-s*arb(j).log()).exp()
             for j in range(1, cutoff + 1)]
    value = sum(terms, acb(0))
    deriv = -sum((v * arb(j).log() for j, v in enumerate(terms, 1)), acb(0))
    nr = arb(cutoff)
    r0 = nr**(1-s) / (s-1)
    r1 = r0 * (nr.log() + 1/(s-1))
    assert abs(value) > r0
    e = r1/(abs(value)-r0) + abs(deriv)*r0/(abs(value)*(abs(value)-r0))
    return (deriv/value).real + arb(0, e.upper())


def arithmetic(b):
    s = b + fmpq(1, 2)
    polar = 1/s + 1/(s-1)
    even = -pi.log()/2 + (s/2).digamma()/2
    odd = -pi.log()/2 + ((s+1)/2).digamma()/2
    half_conductor4 = arb(4).log()/2
    half_conductor5 = arb(5).log()/2
    l0, l4, l5 = [logder_bounds(s, c) for c in ("zeta", "chi4", "chi5")]
    gaussian = b * (half_conductor4 + polar - (2*pi).log() + s.digamma() + l0 + l4)
    zeta = b * (polar + even + l0)
    chi4 = b * (half_conductor4 + odd + l4)
    chi5 = b * (half_conductor5 + odd + l5)
    assert (gaussian-zeta-chi4).contains(0)
    return {"Q": zeta, "chi4": chi4, "chi5": chi5, "Q(i)": gaussian}


def main_term(b, degree, conductor, constant):
    return b * (degree * (b/(2*pi)).log() + arb(conductor).log())/2 + constant


def coeff(n, j):
    return fmpq((-1)**j * n * comb(2*n-1, n-1) * comb(n-1, j), n+j)


def kernels(a, n, coeffs):
    scales_squared = [fmpq((n+j)*a*a, n) for j in range(n)]
    count = 0
    for y in (fmpq(0), fmpq(3, 2), fmpq(a, 16), fmpq(a), fmpq(32*a), fmpq(100*a)):
        for offset in (fmpq(0), fmpq(1, 5), fmpq(1, 2)):
            z = acb(y, offset)
            product = acb(1)
            direct = acb(0)
            reflected = arb(0)
            for c, b2 in zip(coeffs, scales_squared):
                value = acb(b2) / (acb(b2) + z*z)
                product *= value
                direct += c*value
                b = arb(b2).sqrt()
                reflected += c * b/2 * sum(((b+d)/((b+d)**2+arb(y)**2)
                                            for d in (offset,-offset)), arb(0))
            assert (product-direct).contains(0)
            assert (product.real-reflected).contains(0)
            assert product.real > 0
            count += 1
    return count


examples = {"Q": (1, 1, fmpq(7,4)), "chi4": (1, 4, fmpq(1,4)),
            "chi5": (1, 5, fmpq(1,4)), "Q(i)": (2, 4, 2)}
rows = []
for n in range(1, 10):
    a = 16**n
    coeffs = [coeff(n, j) for j in range(n)]
    assert sum(coeffs) == 1 and sum(abs(c) for c in coeffs) < 8**n
    count = kernels(a, n, coeffs)
    errs = {key:arb(0) for key in examples}
    for j, c in enumerate(coeffs):
        b = a * arb(fmpq(n+j, n)).sqrt()
        scalars = arithmetic(b)
        for key, (d, q, const) in examples.items():
            errs[key] += c*(scalars[key]-main_term(b, d, q, const))
    assert all(abs(x) < arb(2)**(-n) for x in errs.values())
    rows.append({"n":n, "a":a, "positive_kernel_cases":count,
                 "sum_abs_coefficients":str(sum(abs(c) for c in coeffs)),
                 "composite_errors":{key:str(val) for key,val in errs.items()}})
out = {"arithmetic_sources":["finite real Dirichlet sums with integral tails",
                             "digamma at positive real arguments"],
       "fields":["Q principal", "odd quadratic mod 4", "odd quartic mod 5", "Q(i) principal"],
       "precision_bits":ctx.prec, "rows":rows}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2), encoding="utf-8")
print("cases", sum(row["positive_kernel_cases"] for row in rows), "arithmetic comparisons", 4*len(rows))
for row in rows:
    print(row["n"],row["composite_errors"]["Q"][:27],row["composite_errors"]["chi5"][:27])
