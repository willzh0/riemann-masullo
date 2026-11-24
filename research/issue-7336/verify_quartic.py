"""Certify a primitive quartic field, its fundamental unit, and a box of Hecke characters.

Run with Python 3 and SymPy. Logarithms and angles are enclosed by rational
series with explicit remainders. The only number-field approximation is root
isolation by SymPy, which returns disjoint rational rectangles.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from math import ceil, floor, isqrt

from sympy import Poly, Rational, isprime, oo, resultant, symbols
from sympy.polys.numberfields import galois_group


x, y = symbols("x y")
f = Poly(x**4 + x + 1, x)


def pair_products(a, b, c):
    """Polynomial with roots r_i r_j, i < j, for x^4+a*x^3+b*x^2+c*x+1."""
    h = a*c - 1
    return Poly(y**6 - b*y**5 + h*y**4 - (c*c + a*a - 2*b)*y**3
                + h*y**2 - b*y + 1, y)


def check_field_and_unit():
    assert f.discriminant() == 229 and isprime(229) and f.count_roots(-oo, oo) == 0
    assert f.set_modulus(2).is_irreducible
    factors3 = f.set_modulus(3).factor_list()[1]
    assert sorted((t.degree(), e) for t, e in factors3) == [(1, 1), (3, 1)]
    assert f.eval(1) == 3
    assert galois_group(f)[0].order() == 24
    assert Q(3, 2) * 16 / 9 < 3  # Minkowski, using sqrt(229)<16 and pi>3.
    exact_g = 27*y**4 - 108*y**3 + 330*y**2 - 85*y + 27
    assert Poly(resultant(f.as_expr(), 3*y - (1-x)**4, x), y) == Poly(3*exact_g, y)

    # If theta = +/-eta^n with n >= 2, house(eta)^2 < 6/5.
    house_poly = pair_products(0, 0, 1)
    assert house_poly.count_roots(Rational(36, 25), oo) == 0
    candidates = 0
    for a, b, c in product(range(-4, 5), range(-7, 8), range(-5, 6)):
        h = Poly(x**4 + a*x**3 + b*x**2 + c*x + 1, x)
        disc = int(h.discriminant())
        if disc <= 0 or disc % 229 or isqrt(disc // 229)**2 != disc // 229:
            continue
        if not h.is_irreducible or h.count_roots(-oo, oo):
            continue
        candidates += 1
        pairs = pair_products(a, b, c)
        assert pairs.eval(Rational(6, 5)) != 0
        assert pairs.count_roots(Rational(6, 5), oo) > 0
    assert candidates == 22
    print("disc=229, S4, signature=(0,2), class number 1, p=3 has degrees 1 and 3")
    print(f"theta is a fundamental unit: {candidates} possible quartics ruled out exactly")


GRID = 10**18


@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q

    def __add__(self, other):
        other = interval(other)
        return enclosure(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-interval(other))

    def __rsub__(self, other):
        return interval(other) + (-self)

    def __mul__(self, other):
        other = interval(other)
        corners = [r*t for r in (self.lo, self.hi) for t in (other.lo, other.hi)]
        return enclosure(min(corners), max(corners))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = interval(other)
        assert other.lo > 0 or other.hi < 0
        return self * enclosure(1/other.hi, 1/other.lo)


def interval(point):
    if isinstance(point, Interval):
        return point
    return Interval(Q(point), Q(point))


def enclosure(lo, hi):
    assert lo <= hi
    return Interval(Q(floor(lo*GRID), GRID), Q(ceil(hi*GRID), GRID))


def atan_small(r):
    assert abs(r) < 1
    terms = 44
    approx = sum((-1)**k * r**(2*k+1)/(2*k+1) for k in range(terms))
    error = abs(r)**(2*terms+1)/(2*terms+1)
    return enclosure(approx-error, approx+error)


PI = 16*atan_small(Q(1, 5)) - 4*atan_small(Q(1, 239))


def atan_positive(arg):
    assert arg.lo > 0
    z = (arg-1)/(arg+1)
    return PI/4 + enclosure(atan_small(z.lo).lo, atan_small(z.hi).hi)


def log_point(r):
    assert r > 0
    z = (r-1)/(r+1)
    terms = 44
    approx = 2*sum(z**(2*k+1)/(2*k+1) for k in range(terms))
    error = 2*abs(z)**(2*terms+1) / ((2*terms+1)*(1-z*z))
    return enclosure(approx-error, approx+error)


def log_interval(arg):
    return enclosure(log_point(arg.lo).lo, log_point(arg.hi).hi)


def character_coordinates():
    real_intervals, rectangles = f.intervals(eps=Rational(1, 2**66), all=True)
    assert not real_intervals
    upper_roots = []
    for (lower, upper), multiplicity in rectangles:
        assert multiplicity == 1
        x_lo, y_lo = lower.as_real_imag()
        x_hi, y_hi = upper.as_real_imag()
        if y_lo > 0:
            upper_roots.append((enclosure(Q(x_lo), Q(x_hi)), enclosure(Q(y_lo), Q(y_hi))))
    assert len(upper_roots) == 2
    (x1, y1), (x2, y2) = sorted(upper_roots, key=lambda r: -r[0].lo)
    assert 0 < x1.lo <= x1.hi < 1 and x2.hi < 0
    # A = log|sigma_1(g)| / log|sigma_1(theta)|,  g=(1-theta)^4/3.
    ltheta = log_interval(x1*x1 + y1*y1)/2
    lg = 2*log_interval((1-x1)*(1-x1) + y1*y1) - log_point(Q(3))
    A = lg/ltheta
    theta_arg1 = atan_positive(y1/x1)
    theta_arg2 = PI - atan_positive(y2/(-x2))
    g_arg1 = -4*atan_positive(y1/(1-x1))
    g_arg2 = -4*atan_positive(y2/(1-x2))
    return A, (g_arg1-A*theta_arg1)/PI, (g_arg2-A*theta_arg2)/PI


def certify_character_box(bound=50):
    # Integer check of every distance to Z using certified outer endpoints.
    scale = 10**14
    centers, errors = [], []
    for a in character_coordinates():
        c = floor((a.lo+a.hi)*scale/2)
        e = ceil(max(abs(a.lo*scale-c), abs(a.hi*scale-c)))
        centers.append(c)
        errors.append(e)
    smallest = scale
    witness = None
    for k, u, v in product(range(-bound, bound+1), repeat=3):
        if k == u == v == 0:
            continue
        r = (k*centers[0] + u*centers[1] + v*centers[2]) % scale
        margin = min(r, scale-r) - abs(k)*errors[0] - abs(u)*errors[1] - abs(v)*errors[2]
        if margin < smallest:
            smallest, witness = margin, (k, u, v)
    assert smallest > 0
    print(f"coordinate centers / {scale}: {centers}")
    print(f"coordinate error radii / {scale}: {errors}")
    print(f"nonzero triples certified: {(2*bound+1)**3-1}")
    print(f"uniform distance to Z >= {smallest}/{scale}; least certificate at {witness}")


if __name__ == "__main__":
    check_field_and_unit()
    certify_character_box()
