# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint==0.8.0"]
# ///
"""Outward interval ledger for the signed prefixes of the fixed annular Q."""

from flint import arb, ctx, fmpq
import flint
from verify_quartic_linear_height import complex_log_derivative


def q(n, d=1):
    return arb(fmpq(n, d))


def require(flag, message):
    if not flag:
        raise ArithmeticError(message)


def verify(bits):
    ctx.prec = bits
    ctx.cap = 2
    pi, rt2 = arb.pi(), q(2).sqrt()
    h = q(20_000_000)
    width = 4 / h
    width_cap = q(1, 10**6)
    h0 = q(1001, 1000).log()
    eta, schur = q(55, 100), q(6287, 10000)
    stretch = q(1001, 1000)
    start = q(10)**30
    large_cutoff = q(10)**12
    # For Z standard normal and a>=0,
    # E |Z|^k exp(a|Z|) <= sqrt((2k-1)!! * 2exp(2a^2)).
    def tilted(k, a):
        moment = 1
        for i in range(1, 2*k, 2):
            moment *= i
        return (2 * moment * (2*a**2).exp()).sqrt()

    # Bounds hold for every 0 < delta <= width_cap.
    a = rt2 * width_cap
    abs_third = 2 * (2/pi).sqrt()
    kink = ((2*rt2 - 2 + width_cap**2/2)*abs_third
            + 2*rt2*a*tilted(4, a))/3
    variation = 4 + (2+2*rt2)*width_cap*tilted(3, a)
    crossing = (6*q(2).log()).sqrt()
    total_variation = 1 + 2*((crossing/2).erfc() - 2*(crossing/rt2).erfc())
    tilted_variation = (total_variation + width_cap**2
                        + (2+rt2)*width_cap*tilted(1, a))
    require(kink < q(442, 1000), "weighted odd kink")
    imbalance = width_cap/2*(width_cap**2/2).exp()
    one_kink = (kink+imbalance)/2
    require(one_kink < q(221,1000), "maximum one-sided weighted kink")
    require(variation < q(41, 10), "unweighted kink variation")
    require(tilted_variation < q(114, 100), "tilted total variation")
    require(h0/a > 700, "distant prime crossings")
    # Every coefficient below works with the elementary theta(X) <= 2X.
    # For r=2,3 and b<=4, the tail polynomial moment is <=
    # (2+2^(r/2))*sqrt(2)*sqrt(tilted(2r,2*b*a))*e^(-h0^2/(8 cap^2)).
    tail_ratio = q(1000)*(-h0**2/(8*width_cap**2)).exp()
    for r in (2, 3):
        elem = (2+rt2**r)*rt2*tilted(2*r, 8*a).sqrt()
        require(elem < 1000, "polynomial moment in discarded Gaussian tail")
    require(tail_ratio < q(1, 10**100), "distant Gaussian tail")
    require((q(10)**43).sqrt()*10*tail_ratio < q(1, 10**45), "far-prime allowance")
    # Two actual real residue classes, p=1,4 modulo 5.
    require(1/(80*large_cutoff.log()) < q(5, 10000), "BMOR progression error")
    min_y = stretch*start/2
    require(min_y.sqrt() > large_cutoff, "lower endpoint of theta integral")
    mass_ratio = q(5005, 10000) - q(4995, 20000)*(1-1/min_y)
    require(mass_ratio < q(251, 1000), "weighted sum p log p on the two classes")

    def u(t, m):
        k = m-1
        logt = t.log()
        return ((logt/k + q(1, k*k))/(pi*t**k)
                + eta*(2*logt+q(1, m))/t**m)

    def damped_s(t):
        y = width*t
        m = 6 + 2*y*y
        k = m-1
        l = t.log()
        main = (l*l/k + 2*l/k**2 + 2/k**3)/pi
        error = eta/t * (2*l*l + 2*l/m + 2/m**2)
        return (-y*y).exp()/t**5 * (main+error)

    d1 = 1/(q(28, 5)*(q(15, 2)*h).log())
    d0 = 1/(q(28, 5)*(15*h).log())
    amp = q(2001, 1000) + q(1001, 1000)*(-((width*h)**2)/2).exp()
    require(2*(width**2/2).exp() < q(2001, 1000), "first Gaussian amplitude")
    require((width**2).exp() < q(1001, 1000), "second Gaussian amplitude")
    u2, u3 = u(h, 2), u(h, 3)
    # Monotonicity of the increasing terms below follows from 0<d0,d1<1/2.
    require(0 < d0 < q(1, 2) and 0 < d1 < q(1, 2), "zero-free exponents")

    def physical(jmax):
        first = q(251, 1000)*stretch**2*jmax.sqrt()*q(442, 1000)*width**3
        endpoints = q(501, 1000)*stretch*q(41, 10)*width**2/start.sqrt()
        return (first+endpoints)/2 + q(1, 10**45)

    def energy(jmax):
        inner = ((1+2**d1)**2*jmax**(1-2*d1)*damped_s(h)
                 + 4*jmax*damped_s(3*h/2))
        return amp*(3*schur*inner).sqrt()/4

    def signed(jmax):
        return (jmax.sqrt()/4 *
                ((1+2**d0)*jmax**(-d0)*u(h, 4) + 2*u(3*h, 4)))

    def low(coefficient):
        return q(214, 200)*(
            (coefficient + 3*u3)*(q(2, 3)+1/start)
            + (q(5, 8)-coefficient)*(large_cutoff/start)**q(3, 2))

    def sampling():
        return 4*(u2/start.sqrt()+u3/start**q(3, 2))

    print(f"{bits} bits, python-flint {flint.__version__}")
    print("  kink, variation, tilted mass:", *(v.str(17) for v in (kink, variation, tilted_variation)))
    print("  S_delta(H), S_delta(1.5H):", *(v.str(17) for v in (damped_s(h), damped_s(3*h/2))))
    for jmax, coefficient, target in (
            (q(10)**41, q(62,1000), q(27,100)),
            (q(10)**42, q(62,1000), q(71,100)),
            (2*q(10)**42, q(62,1000), q(98,100)),
            (q(10)**42, q(181,1000), q(80,100)),
            (q(17,10)*q(10)**42, q(181,1000), q(99,100))):
        terms = [physical(jmax), energy(jmax), signed(jmax), low(coefficient), sampling()]
        total = sum(terms, q(0))
        print(f"  J<={jmax.str(4)}, cL={coefficient.str(4)}",
              "kinks, energy, signed, low, mesh =", *(v.str(12) for v in terms),
              "sum", total.str(14))
        require(total < target, "uniform terminal interval total")

    def directed_low(coefficient, initial):
        return q(114,100)*((coefficient+3*u3)*(q(2,3)+1/start)
                            +(initial-coefficient)*(large_cutoff/start)**q(3,2))

    def smooth_mean(jmax):
        return amp*(-q(8)).exp()*jmax.sqrt()*u(h,4)/2

    for jmax, target in ((2*q(10)**42,q(904,1000)),
                         (q(24,10)*q(10)**42,q(99,100))):
        # Each directed kink has at most .221 delta^3 weighted mass and
        # 2.05 delta^2 variation; the same physical() is an upper bound.
        terms = [physical(jmax),energy(jmax),smooth_mean(jmax),
                 directed_low(q(62,1000),q(5,8)),sampling()]
        total = sum(terms, q(0))
        require(total < target, "directed interpolation estimate")
        print("  directed",jmax.str(4),*(v.str(12) for v in terms),"sum",total.str(14))

    # Complex modulus of the same prime observable. The additional imaginary
    # elementary term is bounded using the actual quartic log derivatives.
    im1 = abs(complex_log_derivative(1,False).imag)
    im2 = abs(complex_log_derivative(2,False).imag)
    require(im1 < 1 and im2 < 1, "imaginary gamma residue constants")
    odd_all = q(4).log()*q(9,8)*(2**q(2,3)-1)/(1-2**q(-2,3))
    require(odd_all < q(25,10),"all-prime odd proper powers")
    # The real large-T envelope after both low quartic and real odd powers
    # are subtracted, plus their complex replacements.
    complex_coefficient = (q(180134,10**6)-q(168354,10**6)
                           -q(11482,10**6)+q(49502,10**6)
                           +odd_all/large_cutoff**q(1,6)
                           +(im1+q(3,2)*im2/large_cutoff)/large_cutoff.sqrt())
    require(complex_coefficient < q(75,1000), "large-x complex remainder")
    for jmax, target in ((q(10)**41,q(73,100)),(q(19,10)*q(10)**41,q(99,100))):
        terms = [4*physical(jmax),2*energy(jmax),
                 directed_low(q(75,1000),q(2_000_001)),sampling()]
        total = sum(terms, q(0))
        require(total < target,"full complex absolute prefix estimate")
        print("  complex",jmax.str(4),*(v.str(12) for v in terms),"sum",total.str(14))


if __name__ == "__main__":
    require(flint.__version__ == "0.8.0", "python-flint version")
    for prec in (128, 192):
        verify(prec)
