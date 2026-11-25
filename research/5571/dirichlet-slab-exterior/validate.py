"""Verify the simultaneous finite-conductor bounds in README.md with Arb.
Requires Python 3.11 or later and python-flint 0.9.0.
"""
from argparse import ArgumentParser
import json
from flint import arb, ctx

MAX_CONDUCTOR = 400_000
BOX_COUNT = 172


def primitive_counts(limit):
    """All characters modulo n are induced by one primitive character."""
    totient = list(range(limit + 1))
    for p in range(2, limit + 1):
        if totient[p] == p:
            for multiple in range(p, limit + 1, p):
                totient[multiple] -= totient[multiple] // p
    primitive = totient.copy()
    for divisor in range(1, limit + 1):
        count = primitive[divisor]
        for multiple in range(2 * divisor, limit + 1, divisor):
            primitive[multiple] -= count
    assert min(primitive) == 0 and primitive[1] == 1
    assert all(primitive[n] == 0 for n in range(2, limit + 1, 4))
    return primitive


def platt_height(q):
    return max(arb(100_000_000) / q,
               arb(75_000_000 if q % 2 == 0 else 37_500_000) / q + 200)


def dirichlet_tail(q, height, power):
    """BMOR Theorem 1.1, two signs of ordinate, including multiplicities."""
    assert q >= 2 and power >= 2
    ell = (q * (height + 2) / (2 * arb.pi())).log()
    assert ell > arb("1.567")
    envelope = arb(".22737") * ell + 2 * (1 + ell).log() - arb(1) / 2
    slope = arb(".22737") + 2 / (1 + ell)
    main_log = (q * height / (2 * arb.pi())).log()
    main = height**(1-power) * (main_log / (power-1)
                                + arb(1) / (power-1)**2) / arb.pi()
    return main + (2 * envelope + slope / power) / height**power


def zeta_tail(height, power):
    """Stieltjes integral with |Q(t)| <= .28 log(t), positive ordinates doubled."""
    assert height >= 2 * arb.pi() * arb(1).exp() and power >= 2
    main_log = (height / (2 * arb.pi())).log()
    main = height**(1-power) * (main_log / (power-1)
                                + arb(1) / (power-1)**2) / arb.pi()
    envelope = arb(".28") * height.log()
    return main + 2 * (2 * envelope + arb(".28") / power) / height**power


def window(height):
    """Certify the first sidelobe of sinc and the normalized radial prefactor."""
    k = BOX_COUNT
    a = arb(3) / (2 * k)
    h = a * height
    assert arb.pi() / 2 < h < arb.pi()
    stationary_lower = arb("4.4934094579090")
    assert arb.pi() < stationary_lower < 3 * arb.pi() / 2 < 5 < 2 * arb.pi()
    assert stationary_lower * stationary_lower.cos() - stationary_lower.sin() < 0
    first = abs(h.sin()) / h
    sidelobe = 1 / (1 + stationary_lower**2).sqrt()
    sinc_upper = max(first, sidelobe, arb(1) / 5)
    c = (sinc_upper**2 + ((a/2).sinh()/h)**2).sqrt()
    assert c < arb(".21725")
    d = (a/2).cosh() / a
    # g is an even probability on [-1,1], so G(1/4) >= 1 and
    # every new box transform is also >= 1 at the real reference 1/4.
    reference_lower = arb(3) * (arb(3)/4).exp() / 64
    radial_constant = (arb(2).exp() * (1+1/(4*height**2)).sqrt()
                       * (1+1/(2*height**2)) / reference_lower)
    # The actual quadratic-box base G uses radii 1/(j(j+1)). Keep the six
    # inverse powers of |t| from G; the next ten original boxes are also
    # smaller than one throughout the certified high range.
    shape = (1 + 1/(4*height**2)).sqrt() * (1 + 1/(2*height**2))
    base_constant = (arb(3)/2).exp() * shape / reference_lower
    for index in range(1, 17):
        radius = arb(1) / (index * (index + 1))
        factor = (radius/2).cosh() / radius
        base_constant *= factor if index <= 6 else factor / height
    # The independent remaining symmetric law has support in [-1/17, 1/17].
    base_constant *= (arb(1)/34).cosh()
    return first, sidelobe, c, d, radial_constant, base_constant


def calculation(bits):
    ctx.prec = bits
    primitive = primitive_counts(MAX_CONDUCTOR)
    count = sum(primitive)
    minimum_height = arb(1175) / 4
    assert minimum_height <= platt_height(MAX_CONDUCTOR-1)
    assert minimum_height <= platt_height(MAX_CONDUCTOR)
    first, sidelobe, stop, d, radial, base_constant = window(minimum_height)
    # A certified common height for all q>1 is enough for this simple bound.
    uniform_green = arb(3) / 4 * dirichlet_tail(MAX_CONDUCTOR,minimum_height,2)
    odd_worst = arb(3)/4 * dirichlet_tail(399_999,platt_height(399_999),2)
    even_worst = arb(3)/4 * dirichlet_tail(400_000,platt_height(400_000),2)
    zeta_height = arb(3_000_175_332_800)
    zeta_green = arb(3)/4 * zeta_tail(zeta_height,2)
    keep = 6
    power = keep - 3
    window_factor = radial * stop**(BOX_COUNT-keep) * d**keep
    simple_bound = window_factor * ((count-1) * dirichlet_tail(
        MAX_CONDUCTOR,minimum_height,power) + zeta_tail(zeta_height,power))
    # Sum the primitive characters in bins. Each bin uses its largest actual
    # conductor and least Platt height in its own parity.
    grouped_bound = zeta_tail(zeta_height,power) * window_factor
    for lo in range(2, MAX_CONDUCTOR+1, 1024):
        hi = min(lo+1023, MAX_CONDUCTOR)
        for parity in (0,1):
            top = hi if hi % 2 == parity else hi-1
            bottom = lo if lo % 2 == parity else lo+1
            if top < bottom:
                continue
            number = sum(primitive[bottom:top+1:2])
            if not number:
                continue
            height = platt_height(top)
            tail = dirichlet_tail(top,height,power)
            grouped_bound += number * window_factor * tail
    base_factors = base_constant * stop**BOX_COUNT
    sharpened_simple = (simple_bound / window_factor) * base_factors
    sharpened_grouped = (grouped_bound / window_factor) * base_factors
    assert count == 29_565_923_838
    assert odd_worst < arb(".014579700030") and even_worst < arb(".01119477825")
    assert zeta_green < arb("2.219430385e-12")
    assert simple_bound < arb("3e-90") and grouped_bound < arb("1e-90")
    assert sharpened_simple < arb("6.299e-104") and sharpened_grouped < arb("3.70e-104")
    return dict(
        precision_bits=bits, primitive_total_including_zeta=count,
        primitive_total_excluding_zeta=count-1,
        height_common=str(minimum_height), zeta_verified_height=int(zeta_height.unique_fmpz()),
        worst_odd_green=str(odd_worst),worst_even_green=str(even_worst),
        uniform_green=str(uniform_green),zeta_green=str(zeta_green),
        box_width=str(arb(3)/(2*BOX_COUNT)), box_count=BOX_COUNT,
        first_lobe_upper=str(first), first_sidelobe_upper=str(sidelobe),
        strip_box_upper=str(stop), inverse_power_box_constant=str(d),
        normalized_profile_constant=str(radial),
        whole_family_simple_bound=str(simple_bound),
        whole_family_binned_bound=str(grouped_bound),
        quadratic_base_constant=str(base_constant), all_box_factor=str(base_factors),
        fixed_probe_simple_bound=str(sharpened_simple),
        fixed_probe_binned_bound=str(sharpened_grouped))


if __name__ == "__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--bits",type=int,default=192)
    options=parser.parse_args()
    assert options.bits >= 96
    print(json.dumps(calculation(options.bits),indent=2))
