"""Count the Gaussian invariant rows and certify their common all-height trace bound.

Requires python-flint 0.9.0. The sister directory dirichlet-slab-exterior supplies
the fixed radial profile and historical bounds used in the original calculation.
"""
import argparse
import importlib.util
import json
from pathlib import Path

from flint import arb, ctx

from check_cyclotomic import mesh_bound

directory = Path(__file__).resolve().parent
prior = directory.parent / "dirichlet-slab-exterior" / "validate.py"
spec = importlib.util.spec_from_file_location("slab", prior)
slab = importlib.util.module_from_spec(spec)
spec.loader.exec_module(slab)


def independent_primitive(limit):
    """Use multiplicativity and the count of primitive characters at prime powers."""
    smallest = list(range(limit+1))
    p = 2
    while p*p <= limit:
        if smallest[p] == p:
            for n in range(p*p, limit+1, p):
                if smallest[n] == n:
                    smallest[n] = p
        p += 1
    values = [0, 1]
    for n in range(2, limit+1):
        p = smallest[n]
        m = n
        pk = 1
        while m % p == 0:
            m //= p
            pk *= p
        local_count = p-2 if pk == p else pk//(p*p)*(p-1)**2
        values.append(values[m]*local_count)
    return values


def selected(q, limit):
    if q % 2:
        return 4*q <= limit
    if q % 4:
        return False
    return q <= limit


def common_radial(precision):
    ctx.prec = precision
    common = arb(1175)/4
    _, _, stop, inv_const, _, _ = slab.window(common)
    coefficients = {0: arb(1)}
    for n in range(1, 49):
        radius = arb(1)/(n*(n+1))
        coefficients[n] = coefficients[n-1]*(radius/2).cosh()/radius
    normalizer = 3*(arb(3)/4).exp()/64
    def factor(height):
        # Six original boxes supply |gamma|^-6. Choose further *original*
        # boxes up to n=48 whose inverse-ordinate bound improves at this H.
        n = 6
        while n < 48 and (n+1)*(n+2) < height:
            n += 1
        base = coefficients[n] * (arb(1)/(2*(n+1))).cosh() / height**(n-6)
        shape = (1+1/(4*height**2)).sqrt()*(1+1/(2*height**2))
        single = min(stop, inv_const/height)
        return (arb(3)/2).exp()/normalizer * shape*base*single**172
    return factor


def calculate(bits, binsize):
    factor = common_radial(bits)
    mesh, _ = mesh_bound(6_200, 14_400, 16)
    assert mesh < arb('3.990e-114')
    limit = 400_000
    primitive = slab.primitive_counts(limit)
    assert independent_primitive(limit) == primitive
    odd_pairs = sum(primitive[1:limit//4+1:2])
    even_rational_rows = sum(primitive[8:limit+1:8])
    assert even_rational_rows % 2 == 0
    equal_pairs = even_rational_rows//2
    rows = odd_pairs+equal_pairs
    rational_total = sum(primitive[q] for q in range(1,limit+1) if selected(q,limit))
    assert rational_total == 2*rows
    inside_discriminant_bound = odd_pairs+sum(primitive[8:200_001:8])//2
    assert rows == 2_463_841_722 and inside_discriminant_bound == sum(primitive[:100_001]) == 1_847_865_075
    zeta_height = arb(3_000_175_332_800)
    total = factor(zeta_height)*slab.zeta_tail(zeta_height, 3)
    correlated = min(mesh,factor(zeta_height))*slab.zeta_tail(zeta_height,3)
    for lo in range(2, limit+1, binsize):
        hi = min(limit, lo+binsize-1)
        for parity in (0,1):
            candidates = [q for q in range(lo+(parity-lo)%2,hi+1,2)
                          if selected(q,limit) and primitive[q] != 0]
            if not candidates:
                continue
            q0 = candidates[-1]
            h = slab.platt_height(q0)
            assert h >= arb(775)/2
            count_tail = sum(primitive[q] for q in candidates)*slab.dirichlet_tail(q0,h,3)
            uncoupled = factor(h)
            total += count_tail*uncoupled
            correlated += count_tail*min(mesh,uncoupled)
    full_previously = arb("3.70e-104")
    assert 0 < correlated < total < full_previously
    if binsize == 128:
        assert mesh < arb('2.754e-117') and correlated < arb('9.562e-113')
    return dict(precision=bits, conductor_ceiling=limit, bin_width=binsize,
                odd_conductor_pairs=odd_pairs, same_even_conductor_pairs=equal_pairs,
                gaussian_invariant_rows=rows, rational_factors=rational_total,
                all_invariant_rows_of_absolute_conductor_norm_at_most_ten_billion=inside_discriminant_bound,
                separate_box_upper=str(total), uniform_mesh_upper=str(mesh),
                all_height_original_absolute_sum_upper=str(correlated))


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--bits", type=int, default=192)
    ap.add_argument("--bin", type=int, default=128)
    args = ap.parse_args()
    assert args.bits >= 96 and args.bin >= 1
    print(json.dumps(calculate(args.bits, args.bin),indent=2))
