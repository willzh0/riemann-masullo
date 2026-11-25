"""Independent check of the common-height bound using the Hadamard sum for zeta.

Run with Python 3 and python-flint 0.9.0, passing the desired precision in bits.
"""
import json
import sys

from flint import arb, ctx


def nonprincipal_census(limit):
    phi = list(range(limit + 1))
    primitive = [0] * (limit + 1)
    for p in range(2, limit + 1):
        if phi[p] == p:
            for n in range(p, limit + 1, p):
                phi[n] -= phi[n] // p
    for d in range(1, limit + 1):
        primitive[d] += phi[d]
        for n in range(2*d, limit + 1, d):
            primitive[n] -= primitive[d]
    return sum(primitive[2:])


def calculate(bits):
    ctx.prec = bits
    conductor = 400_000
    height = arb(1175)/4
    a = arb(3)/344
    u = a*height
    root_lower = arb("4.4934094579090")
    assert arb.pi()/2 < u < arb.pi() < root_lower < 3*arb.pi()/2 < 5 < 2*arb.pi()
    assert root_lower*root_lower.cos() - root_lower.sin() < 0
    sidelobe = 1/(1+root_lower**2).sqrt()
    assert max(u.sin()/u, arb(1)/5) < sidelobe
    box = (sidelobe**2+((a/2).sinh()/u)**2).sqrt()
    count = nonprincipal_census(conductor)
    assert count == 29_565_923_837

    ell = (conductor*(height+2)/(2*arb.pi())).log()
    envelope = arb(".22737")*ell + 2*(1+ell).log() - arb(1)/2
    slope = arb(".22737") + 2/(1+ell)
    log_main = (conductor*height/(2*arb.pi())).log()
    tail = (log_main/2+arb(1)/4)/(arb.pi()*height**2) + (2*envelope+slope/3)/height**3

    # The Hadamard sum of Re(1/rho + 1/(1-rho)) over ALL nontrivial zeros
    # equals 2+EulerGamma-log(4*pi). Each summand is at least 1/(1+gamma^2).
    hadamard_sum = 2+arb.const_euler()-(4*arb.pi()).log()
    zeta_tail = (1+1/height**2)*hadamard_sum/height
    total_tail = count*tail + zeta_tail
    assert total_tail < arb("961634.675")

    shape = (1+1/(4*height**2)).sqrt()*(1+1/(2*height**2))
    normalization = 3*(arb(3)/4).exp()/64
    radial = (arb(3)/2).exp()*shape*(arb(1)/34).cosh()/normalization
    for n in range(1, 17):
        radius = arb(1)/(n*(n+1))
        radial *= (radius/2).cosh()/radius
        if n > 6:
            radial /= height
    absolute_sum_bound = radial*box**172*total_tail
    assert absolute_sum_bound < arb("6.299e-104")
    return dict(bits=bits, nonprincipal=count, strip_box=str(box),
                zeta_inverse_cube_upper=str(zeta_tail),
                family_inverse_cube_upper=str(total_tail),
                absolute_sum_upper=str(absolute_sum_bound))


if __name__ == "__main__":
    print(json.dumps(calculate(int(sys.argv[1])), indent=2))
