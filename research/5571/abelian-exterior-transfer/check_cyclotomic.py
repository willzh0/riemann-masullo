"""Independent finite estimates for the fixed d095ce5 radial on two cyclotomic towers.

Run with python-flint 0.9.0. Only the *bounds* on the common R change with height.
"""
from argparse import ArgumentParser
import json
from math import isqrt, prod

from flint import acb, arb, ctx, dirichlet_char


K = 172


def factor(n):
    result = {}
    for p in range(2, isqrt(n) + 1):
        while n % p == 0:
            result[p] = 1 + result.get(p, 0)
            n //= p
    if n > 1:
        result[n] = 1
    return result


def bmor(q, h, k):
    ell = (q * (h + 2) / (2 * arb.pi())).log()
    assert ell > arb("1.567") and h > 1
    error = arb(".22737") * ell + 2 * ell.log1p() - arb(1)/2
    slope = arb(".22737") + 2/(1 + ell)
    return (h**(1-k) / arb.pi() * ((q*h/(2*arb.pi())).log()/(k-1) + arb(1)/(k-1)**2)
            + (2*error + slope/k)/h**k)


def zeta_tail(h, k):
    return (h**(1-k) / arb.pi() * ((h/(2*arb.pi())).log()/(k-1) + arb(1)/(k-1)**2)
            + 2*arb(".28")*(2*h.log() + arb(1)/k)/h**k)


def radial_shape(h):
    norm_lower = 3 * (arb(3)/4).exp() / 64
    shape = (1+1/(4*h*h)).sqrt() * (1+1/(2*h*h))
    return (arb(3)/2).exp() * shape / norm_lower


def first_sidelobe(h, a):
    u = a*h
    lower = arb("4.4934094579090")
    assert arb.pi()/2 < u < arb.pi() < lower < 3*arb.pi()/2 < 5 < 2*arb.pi()
    assert lower*lower.cos()-lower.sin() < 0
    maximum = (1/(1+lower**2).sqrt()).max(abs(u.sin())/u).max(arb(1)/5)
    return (maximum**2 + ((a/2).sinh()/u)**2).sqrt()


def raw_high_bound(h, m, stop):
    """Six original boxes supply the inverse powers; the next m-6 use the actual height."""
    v = radial_shape(h) * stop**K * (arb(1)/(2*(m+1))).cosh()
    for n in range(1, m+1):
        r = arb(1)/(n*(n+1))
        v *= (r/2).cosh() / (r if n <= 6 else r*h)
    return v


def mesh_bound(first, last, denominator, m=32):
    """Upper bound on |R(x+it)| |t|^3 throughout a rational mesh and beyond its last height."""
    low = arb(first)/denominator
    high = arb(last)/denominator
    a = arb(3)/(2*K)
    step = arb(1)/denominator
    half = step/2
    factors = []
    for n in range(1, m+1):
        r = arb(1)/(n*(n+1))
        factors.append((r,(r/2).cosh(),(r/2).sinh()**2))
    density_tail = (arb(1)/(2*(m+1))).cosh()
    stop_tail = (a/2).cosh()/(a*high)
    tail = raw_high_bound(high,16,stop_tail)
    peak = arb(0)
    peak_left = None
    a_sinh2 = (a/2).sinh()**2
    for k in range(first,last):
        left = arb(k)/denominator
        middle = left+half
        def numerator(r,sinh_sq):
            sin_sup = (abs((r*middle).sin())+r*half).min(1)
            return (sin_sup**2+sinh_sq).sqrt()
        new = numerator(a,a_sinh2)/(a*left)
        upper = radial_shape(left) * density_tail * new**K
        for n,(r,cosh,sinh_sq) in enumerate(factors,start=1):
            if n<=6:
                upper *= numerator(r,sinh_sq)/r
            else:
                upper *= (numerator(r,sinh_sq)/(r*left)).min(cosh)
        if upper > peak:
            peak_left = k
        peak = peak.max(upper)
    return peak.max(tail), dict(mesh_start=str(low),mesh_end=str(high),step=str(step),
                               original_factors=m,largest_cell_left_numerator=peak_left,
                               finite_grid_bound=str(peak),infinite_tail_bound=str(tail))


def level(q):
    return (arb(100_000_000)/q).max(arb(37_500_000)/q+200)


def calculate(bits):
    ctx.prec = bits
    assert bits >= 128
    qz = arb(3_000_175_332_800)
    tz3 = zeta_tail(qz,3)
    tz2 = zeta_tail(qz,2)
    a = arb(3)/(2*K)
    p = next(n for n in range(400_000,2,-1) if factor(n) == {n:1})
    factors = factor(p-1)
    assert p==399_989 and factors=={2:2,19:2,277:1}
    degrees = sorted(d for d in range(1,p) if (p-1)%d==0)
    assert len(degrees)==prod(ex+1 for ex in factors.values())==18
    h = level(p)
    assert 293.75 < h
    b = bmor(p,h,3)
    row = (p-2)*b + tz3
    common_c = first_sidelobe(h,a)
    common_w = raw_high_bound(h,16,common_c)
    # Mesh begins just below H_p and ends in the trivial inverse-ordinate stop band.
    denominator = 16
    mesh_first = 4700
    mesh_last = 900*denominator
    assert arb(mesh_first)/denominator < h
    w,mesh = mesh_bound(mesh_first,mesh_last,denominator)
    h5 = level(5)
    assert h5 == 20_000_000
    m5 = (isqrt(1+4*20_000_000)-1)//2
    assert m5==4471 and m5*(m5+1)<=h5<(m5+1)*(m5+2)
    b5 = bmor(5,h5,3)
    combined5 = 3*b5+tz3
    c5 = (a/2).cosh()/(a*h5)
    w5 = raw_high_bound(h5,m5,c5)
    reference = (abs(acb(2).zeta()) * abs(acb(2).dirichlet_l(dirichlet_char(5,4)))
                 * abs(acb(2).dirichlet_l(dirichlet_char(5,2)))**2 / 2).log()
    green5 = arb(3)/4*(3*bmor(5,h5,2)+tz2)
    quadratic = dirichlet_char(5,4)
    quartic = dirichlet_char(5,2)
    assert quadratic(2)==-1 and quartic(2)==acb(0,1)
    real_principal = (abs(acb(2).zeta()) * abs(acb(2).dirichlet_l(quadratic)) / 2).log()
    real_sign = 2 * abs(acb(2).dirichlet_l(quartic)).log()
    principal_green = arb(3)/4 * (bmor(5,h5,2)+tz2)
    sign_green = arb(3)/2 * bmor(5,h5,2)
    assert row*common_w < arb('8.519931413e-109')
    assert w < arb('3.989561711e-114') and row*w < arb('5.190169594e-113')
    assert w5*combined5 < arb('7.656587073e-4747') and green5 < arb('6.296400984e-7')
    assert reference > arb('-.604816151440950') and reference+green5 < arb('-.604815521800850')
    return dict(precision=bits,p=p,degree=p-1,p_minus_one=factors,all_degrees=degrees,
                large=dict(height=str(h),row_T3=str(b),zeta_T3=str(tz3),summed_T3=str(row),
                           strip_sinc=str(common_c),uniform_bound=str(row*common_w),
                           mesh_bound=str(row*w),divisor_sites_weight=str(w),mesh=mesh,
                           quadratic_K_principal=str((b+tz3)*w),quadratic_K_each_nonprincipal=str(2*b*w)),
                small=dict(height=str(h5),row_T3=str(b5),summed_T3=str(combined5),
                           original_factors=m5,strip_sinc=str(c5),fixed_radial_bound=str(w5*combined5),
                           green_upper=str(green5),poisson_mean_lower_endpoint=str(reference),
                           poisson_mean_upper_endpoint=str(reference+green5),
                           real_K_principal_exterior=str(w5*(b5+tz3)),
                           real_K_nonprincipal_exterior=str(w5*2*b5),
                           real_K_principal_green=str(principal_green),real_K_nonprincipal_green=str(sign_green),
                           real_K_principal_mean=[str(real_principal),str(real_principal+principal_green)],
                           real_K_nonprincipal_mean=[str(real_sign),str(real_sign+sign_green)]))


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--bits',type=int,required=True)
    print(json.dumps(calculate(p.parse_args().bits),indent=2))
