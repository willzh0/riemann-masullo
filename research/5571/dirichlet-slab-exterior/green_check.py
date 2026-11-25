"""Historical finite-height inputs, signed inverse-square tails, and shifted Green kernels.

Run with Python 3 and python-flint 0.9.0. No zero table is needed.
"""
import argparse
import json
from fractions import Fraction

from flint import acb, arb, ctx, dirichlet_char


def bmor_upper(q, height):
    """Both signs, with multiplicity. BMOR, Theorem 1.1."""
    pi = arb.pi()
    ell = (q * (height + 2) / (2 * pi)).log()
    assert height > 1 and ell > arb('1.567')
    envelope = arb('0.22737') * ell + 2 * ell.log1p() - arb(1) / 2
    log_slope = arb('0.22737') + 2 / (1 + ell)
    center = ((q * height / (2 * pi)).log() + 1) / (pi * height)
    return center + (2 * envelope + log_slope / 2) / height**2


def platt_height(q):
    """Platt, Math. Comp. 85 (2016), Thm. 10.1. Parity refers to q."""
    a = 37_500_000 if q % 2 else 75_000_000
    return max(arb(100_000_000) / q, arb(a) / q + 200)


def primitive_census(limit):
    """Remove characters induced from proper divisors using phi(q)=sum_{d|q} prim(d)."""
    counts = list(range(limit + 1))
    for p in range(2, limit + 1):
        if counts[p] == p:
            for n in range(p, limit + 1, p):
                counts[n] -= counts[n] // p
    for d in range(1, limit + 1):
        primitive = counts[d]
        if primitive:
            for n in range(2*d, limit + 1, d):
                counts[n] -= primitive
    assert counts[1:3] == [1, 0] and not any(counts[2::4])
    return {"with_conductor_one": sum(counts), "conductors_at_least_three": sum(counts[3:])}


def shifted_kernel_certificates():
    """Exact rational inequalities used in the all-height pair comparison."""
    a = Fraction(4, 5)
    b = Fraction(5, 2)
    # For X >= 16 and B <= 5/2 the lower comparison is hardest at X=16, B=5/2.
    linear_coefficient = 1 + 3 * a**2 - b
    lower_endpoint = 16 * linear_coefficient - (a**2 + b) * (a**2 + b - 1)
    assert linear_coefficient == Fraction(21, 50)
    assert lower_endpoint == Fraction(1, 2500)
    # atanh(u) <= u/(1-u^2) bounds the single kernel by 3d/(x^2+2).
    # Here B=9/4+d^2 >= 9/4, 9d^2 <= 9/4, and |x|>=4-a>3.
    right_b = Fraction(9, 4) - Fraction(9, 4) / ((4-a)**2 + Fraction(9, 4))
    assert right_b > 2
    upper_coefficient = 2 - 3 * a**2
    assert upper_coefficient == Fraction(2, 25)
    return {"offset": str(a), "lower_affine_slope": str(linear_coefficient),
            "lower_margin_at_gamma_four": str(lower_endpoint),
            "upper_quadratic_margin": str(upper_coefficient)}


def calculation(bits):
    ctx.prec = bits
    height = arb(3_000_175_332_800)
    pi = arb.pi()
    zeta_center = ((height / (2*pi)).log() + 1) / (pi * height)
    # Brent, Platt and Trudgian, JNT 238 (2022), Cor. 1 and Lemma 2:
    # positive-ordinate count error <= .28 log t; take both signs.
    zeta_radius = arb('0.28') * (4 * height.log() + 1) / height**2
    zeta_upper = zeta_center + zeta_radius
    green_zeta = 3 * zeta_upper / 4
    reference_zeta = (pi**2 / 12).log()
    assert zeta_center - zeta_radius > arb('2.95924051212e-12')
    assert zeta_upper < arb('2.95924051214e-12')
    assert green_zeta < arb('2.21943038411e-12')
    assert reference_zeta > arb('-0.195446878089201')
    assert reference_zeta + green_zeta < arb('-0.195446878086980')

    by_conductor = {}
    for q in (5, 399_999, 400_000):
        h = platt_height(q)
        upper = bmor_upper(q, h)
        by_conductor[q] = {"height": str(h), "two_sided_tail_upper": str(upper),
                           "green_upper": str(3*upper/4)}
    odd = bmor_upper(399_999, platt_height(399_999))
    even = bmor_upper(400_000, platt_height(400_000))
    assert even < odd < arb('0.01943960003927')
    assert 3*odd/4 < arb('0.01457970002945')
    assert 3*even/4 < arb('0.01119477824955')
    census = primitive_census(400_000)
    assert census['conductors_at_least_three'] == 29_565_923_837

    s = acb(2, arb(4)/5)
    shifted_pole = (arb(116)/41).log()/2
    shifted_zeta = abs(s.zeta()).log() - shifted_pole
    quartic = dirichlet_char(5, 2)
    shifted_quartic = (abs(s.dirichlet_l(quartic)).log()
                       + abs(s.conjugate().dirichlet_l(quartic)).log())/2
    quartic_green = 3*bmor_upper(5, platt_height(5))/4
    assert arb('-0.233213402692283') < shifted_zeta
    assert shifted_zeta + green_zeta < arb('-0.233213402690062')
    assert arb('-0.014438996889053') < shifted_quartic
    assert shifted_quartic + quartic_green < arb('-0.014438787009759')

    return {"bits": bits, "zeta_verified_height": str(height),
            "zeta_two_sided_tail_main": str(zeta_center),
            "zeta_two_sided_tail_error": str(zeta_radius),
            "zeta_two_sided_tail_upper": str(zeta_upper),
            "zeta_green_upper": str(green_zeta),
            "zeta_log_mean_lower": str(reference_zeta),
            "zeta_log_mean_upper": str(reference_zeta + green_zeta),
            "conductor_endpoints": by_conductor,
            "primitive_census_through_400000": census,
            "shifted_zeta_pole": str(shifted_pole),
            "shifted_zeta_log_mean_lower": str(shifted_zeta),
            "shifted_zeta_log_mean_upper": str(shifted_zeta + green_zeta),
            "paired_quartic_log_mean_lower": str(shifted_quartic),
            "paired_quartic_log_mean_upper": str(shifted_quartic + quartic_green),
            "symmetric_translate_certificates": shifted_kernel_certificates()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bits', type=int, choices=(128, 192), required=True)
    print(json.dumps(calculation(parser.parse_args().bits), indent=2))
