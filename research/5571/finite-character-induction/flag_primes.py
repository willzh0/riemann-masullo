"""Check Trinks' rational-prime Euler denominators over actual fields. Needs SymPy."""
from collections import Counter
from itertools import combinations
from math import lcm
from sympy import Matrix, Poly, QQ, ZZ, prod, primerange, resultant, symbols, zeros

x, t, T = symbols("x t T")
f = Poly(x**7 - 7*x + 3, x, domain=ZZ)
assert f.discriminant() == 3**8 * 7**8 and f.count_roots() == 3

# Eigenvalues of the additive third compound are all 35 distinct triple sums.
# The Fano lines are the unique orbit of size seven on those triples.
triples = list(combinations(range(7), 3))
comp = zeros(7)
for j in range(6):
    comp[j + 1, j] = 1
for i in range(7):
    comp[i, 6] = -f.nth(i)
compound = zeros(len(triples))
for j, triple in enumerate(triples):
    for k, v in enumerate(triple):
        for i in range(7):
            if not comp[i, v]:
                continue
            target = triple[:k] + (i,) + triple[k+1:]
            if len(set(target)) < 3:
                continue
            swaps = sum(a > b for a, b in combinations(target, 2))
            compound[triples.index(tuple(sorted(target))), j] += (-1)**swaps * comp[i, v]
triples_poly = Poly(compound.charpoly(x).as_expr(), x)
factors = sorted(triples_poly.factor_list()[1], key=lambda part: part[0].degree())
assert [(h.degree(), e) for h, e in factors] == [(7, 1), (28, 1)]
g = factors[0][0]
assert g.as_expr() == x**7 + 14*x**4 - 42*x**2 - 21*x + 9

# An unordered point pair specifies a flag. Ordered pairs of points or of
# lines give the two quadratic covers of the same flag field.
def resultant_poly(h, y):
    return Poly(resultant(h.as_expr(), h.as_expr().subs(x, y), x), t, domain=QQ)


sums = resultant_poly(f, t-x)
diagonal = Poly(2**7 * f.as_expr().subs(x, t/2), t, domain=QQ)
square = sums.exquo(diagonal)
unit, factors = square.factor_list()
assert unit == 1 and len(factors) == 1 and factors[0][1] == 2
base = factors[0][0].set_domain(ZZ)


def difference_poly(h):
    res = resultant_poly(h, x-t)
    return res.exquo(Poly(t**7, t, domain=QQ)).monic().set_domain(ZZ)


a, b = difference_poly(f), difference_poly(g)
assert base.degree() == 21 and a.degree() == b.degree() == 42
assert a.is_irreducible and b.is_irreducible
assert [h.count_roots() for h in (base, a, b)] == [5, 6, 6]
print("flag field defining polynomial:", base.as_expr())


def degrees(h, p):
    red = h.set_modulus(p)
    if not red.gcd(red.diff()).is_one:
        return None
    return sorted(d.degree() for d, e in red.factor_list()[1] for _ in range(e))


def denominator(ds):
    return Poly(prod(1-T**d for d in ds), T, domain=ZZ)


def wanted_den(order):
    return Poly({1: (1-T)**21, 2: (1-T)*(1-T**2)**10, 3: (1-T**3)**7,
                 4: (1+T)*(1-T**4)**5, 7: (1-T**7)**3}[order], T, domain=ZZ)


# The printed comparison table in Serre, Duke 54 (1987), section 5.5.
serre = {2: 7, 5: 7, 11: 7, 13: 4, 17: 3, 19: 3, 23: 3, 29: 7, 31: 7, 37: 4}
for p, o in serre.items():
    assert lcm(*degrees(f, p)) == o
print("Serre's ten good-prime Frobenius orders reproduced:", sorted(serre.items()))

# Squarefree reduction of each of the three defining polynomials guarantees
# that Dedekind factorization computes the actual residue degrees of the field.
remaining = {1, 2, 3, 4, 7}
for p in primerange(2, 20000):
    if p in (3, 7):
        continue
    if remaining == {1}:
        if sum((pow(i, 7, p) - 7*i + 3) % p == 0 for i in range(p)) != 7:
            continue
    o = lcm(*degrees(f, p))
    if o not in remaining:
        continue
    patterns = [degrees(h, p) for h in (base, a, b)]
    if None in patterns:
        continue
    den_f, den_a, den_b = [denominator(ds) for ds in patterns]
    assert den_a.exquo(den_f) == den_b.exquo(den_f) == wanted_den(o)
    print(f"p={p} Frob order={o} residue degrees (degree:multiplicity) in F, Ea, Eb:",
          [dict(sorted(Counter(ds).items())) for ds in patterns])
    remaining.remove(o)
    if not remaining:
        break
assert not remaining, remaining