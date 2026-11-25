# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint==0.8.0"]
# ///
"""Interval ledger for QUARTIC_LINEAR_HEIGHT.md. Requires python-flint 0.8.0."""

import flint
from flint import acb, acb_series, arb, ctx, fmpq


def check(condition, label):
    if not condition:
        raise ArithmeticError(label)


def complex_log_derivative(s, quadratic):
    z = acb_series([s, 1])
    values = (1, -1, -1, 1) if quadratic else (1, acb(0, 1), acb(0, -1), -1)
    # The pole 1/(s-1) cancels exactly because both characters have zero mean.
    hurwitz = sum(a * z.zeta(fmpq(r, 5), deflate=True) for r, a in enumerate(values, 1))
    jet = (-arb(5).log() * z).exp() * hurwitz
    check(abs(jet[0]) > 0, "nonzero L-value")
    return jet[1] / jet[0]


def log_derivative(s, quadratic):
    return complex_log_derivative(s, quadratic).real


def h(u):
    return (arb(2)**(1-u)-1)/(1-u)


def verify(bits):
    ctx.prec = bits
    ctx.cap = 2
    log2 = arb(2).log()
    half = arb(1)/2
    c1, c2 = (log_derivative(j, False) for j in (1, 2))
    e1, e3 = (log_derivative(j, True) for j in (1, 3))
    shared = (arb(5)/arb.pi()).log() - arb.const_euler()
    b_chi = shared + 2*c1
    b_eta = shared - 2*log2 + 2*e1
    # Elementary residual is log(x)/2 - a + (3log(x)/4 + b)/x + T(x).
    a = log2 - c1 + e1
    b = arb(9)/8 - log2 - arb(3)/2*(-half+c2-e3)
    chi_mass = h(half)*b_chi
    eta_mass = 2*h(half/2)*b_eta
    odd = (arb(4).log() * (arb(3)/4)*h(arb(1)/3)
           / (1-arb(11)**(-arb(2)/3)))
    check(0 < chi_mass < fmpq(16836, 100000), "critical quartic mass")
    check(chi_mass > fmpq(168354, 10**6), "lower bound on replaced coarse quartic term")
    check(0 < eta_mass < fmpq(28465, 100000), "critical quadratic mass")
    check(0 < odd < fmpq(11483, 10000), "odd proper powers")
    check(odd/100 > fmpq(11482, 10**6), "lower bound on the replaced odd term at 10^12")
    check(fmpq(136296, 100000) < a < fmpq(136297, 100000), "constant at zero")
    check(fmpq(130150, 100000) < b < fmpq(130151, 100000), "constant at minus one")

    # All t>=H>=exp(16) satisfy ell(t)<=log(t) and the BMOR error <=log(t).
    h_min = arb(16).exp()
    h_max = arb(20_000_000)
    check(5*(h_min+2)/(2*arb.pi()) < h_min, "ell(t) <= log t")
    check((5*h_min/(2*arb.pi())).log() > fmpq(1567, 1000), "BMOR threshold")
    check(fmpq(22737, 100000)*16 + 2*arb(17).log()-half < 16, "BMOR value at 16")
    check(fmpq(22737, 100000) + arb(2)/17 < 1, "BMOR derivative for log(t)>=16")
    delta = (arb(5)/(2*arb.pi())).log()+half
    check(delta > 0, "normalized main tail correction")
    ratio = (1+delta/16)/(2*arb.pi()) + (2+arb(1)/48)/h_min
    tail_bound = arb(16)/h_min**2 / 6
    check(ratio < fmpq(1, 6), "all heights H>=exp(16)")
    check(tail_bound < fmpq(1, 10**12), "unscaled all-height tail")
    tail_hmax = ((h_max.log()+delta)/(2*arb.pi()*h_max**2)
                 + (2*h_max.log()+arb(1)/3)/h_max**3)
    check(tail_hmax < fmpq(68, 10**16), "published Platt height")

    # The two affine terms divided by sqrt(x). The first magnitude has its
    # positive maximum at log(x)=2(1+a), or a larger negative endpoint at 11.
    x = arb(11)
    small_gamma = (max((-1-a).exp().upper(), ((a-x.log()/2)/x.sqrt()).upper())
                   + (3*x.log()/4+b)/x**(arb(3)/2) + arb(7)/(12*x**(arb(5)/2)))
    check(small_gamma < fmpq(19, 100), "elementary terms for x>=11")
    small_total = chi_mass + eta_mass/x**(arb(1)/4) + small_gamma + 12*tail_bound
    check(small_total < fmpq(52, 100), "11 <= x < 1331")
    check((arb(11)+arb(3)/2)*tail_bound < fmpq(5, 8), "x <= 11, isolated primary tail")

    x = arb(11)**3
    check(x.log() > 2+2*a, "first affine term decreases for x>=1331")
    check(3*x.log()/4+b > half, "second affine term decreases")
    large_gamma = ((x.log()/2-a)/x.sqrt() + (3*x.log()/4+b)/x**(arb(3)/2)
                   + arb(7)/(12*x**(arb(5)/2)))
    large_total = (chi_mass + eta_mass/x**(arb(1)/4)
                   + large_gamma + odd/x**(arb(1)/6) + 12*tail_bound)
    check(large_total + arb(3)/2*tail_bound < fmpq(6231, 10000), "x >= 1331")
    print(f"{bits} bits. Bchi={b_chi.str(15)}, Beta={b_eta.str(15)}")
    print(f"  a={a.str(15)}, b={b.str(15)}, odd-power coefficient={odd.str(15)}")
    print(f"  coefficient masses: chi={chi_mass.str(15)}, eta={eta_mass.str(15)}")
    print(f"  cubic tail H=20m: {tail_hmax.str(15)}; normalized tail cap {ratio.str(15)}")
    print(f"  x in [11,1331): {small_total.str(15)}; x>=1331: {large_total.str(15)}")
    for lower, target in ((10**8, fmpq(226, 1000)), (10**12, fmpq(181, 1000))):
        x = arb(lower)
        gamma = ((x.log()/2-a)/x.sqrt() + (3*x.log()/4+b)/x**(arb(3)/2)
                 + arb(7)/(12*x**(arb(5)/2)))
        total = chi_mass + eta_mass/x**(arb(1)/4) + odd/x**(arb(1)/6) + gamma + 12*tail_bound
        check(total < target, "large-x saving")
        if lower == 10**12:
            check(total < fmpq(180134, 10**6), "rounded coefficient before the low-root replacement")
        print(f"  x>={lower}: {total.str(15)}")


if __name__ == "__main__":
    check(flint.__version__ == "0.8.0", "requires python-flint 0.8.0")
    for precision in (128, 192):
        verify(precision)
