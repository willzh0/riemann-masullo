# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint==0.8.0"]
# ///
"""Outward interval calibration of the unsmoothed quartic high-zero signed prefix."""
from flint import arb, ctx, fmpq


def q(n, d=1):
    return arb(fmpq(n, d))


def run(bits):
    ctx.prec = bits
    H = q(20_000_000)
    L = H.log()
    pi = arb.pi()
    eta = q(55, 100)
    # BMOR error / log(t) decreases beyond H after replacing ell by log(t).
    bmor_ratio = q(22737, 100000) + (2 * (1 + L).log() - q(1, 2)) / L
    assert bmor_ratio < eta
    # Local Schur estimate. For h<=1 bound kernel-integral correction by 2,
    # for h>=1 by (2/pi)h^-3/2 + 1.10 h^-5/2, safely below 6 total.
    local = 1 / (2 * q(2).sqrt()) + eta / 2 + 6/(H.sqrt()*L)
    assert local < q(6287, 10000)
    s_ratio = 1/(5*pi) * (1 + q(2,5)/L + q(2,25)/L**2)
    s_ratio += eta/H*(2 + 1/(3*L) + 1/(18*L**2))
    assert s_ratio < q(652,10000)
    def S(t):
        return q(652,10000) * t.log()**2 / t**5
    def U(m):
        k = m - 1
        return ((L/k+q(1,k*k))/(pi*H**k)
                + eta*(2*L+q(1,m))/H**m)
    d = 1/(q(28,5)*(15*H).log())
    def energy(J, use_kadiri=True):
        if use_kadiri:
            inside = (1 + 2**d)**2 * J**(1-2*d) * S(H) + 4*J*S(3*H)
        else:
            inside = 4*J*S(H)
        return (3*q(6287,10000)*inside).sqrt()/4
    def other(Jlower, Jupper):
        return (3*U(3) + Jupper.sqrt()*U(4)/2 +
                q(3,2)*U(2)/Jlower.sqrt() + q(3,2)*U(3)/Jlower**q(3,2))
    cutoff = q(10)**20
    small = q(5,8) + energy(cutoff) + other(q(1),cutoff)
    assert small < q(626,1000)
    floor = q(10)**12
    def low(X,c):
        return c*(q(2,3)+1/X)+(q(5,8)-c)*(floor/X)**q(3,2)
    def large(maximum,c, use_kadiri=True):
        return low(cutoff,c) + energy(maximum,use_kadiri) + other(cutoff,maximum)
    assert energy(q(10)**30) < q(2,1000)
    assert large(q(10)**30,q(181,1000)) < q(626,1000)
    print("precision",bits,"BMOR relative",bmor_ratio,"Schur local",local,"S relative",s_ratio)
    print("d",d,"small",small,"U2,3,4",*[U(m) for m in (2,3,4)])
    for scale in (q(10)**35, q(10)**36, q(124,100)*q(10)**36):
        total = large(scale,q(181,1000))
        print("J",scale,"energy",energy(scale),"signed/left/discrete",other(cutoff,scale),"total",total)
    assert large(q(10)**35,q(181,1000),False) < q(66,100)
    assert large(q(10)**36,q(181,1000)) < q(91,100)
    assert large(q(124,100)*q(10)**36,q(181,1000)) < 1
    # A separate first-thirteen-zero audit gives the optional, stronger low
    # mass: for x>=10^12 .180134-.168354+.049502<.062. The subtracted
    # number is a lower bound on the coarse component in the earlier ledger.
    for scale in (q(10)**36, q(15,10)*q(10)**36):
        print("13-zero calibrated",scale,large(scale,q(62,1000)))
    assert large(q(15,10)*q(10)**36,q(62,1000)) < q(1)


if __name__ == "__main__":
    for bits in (128,192):
        run(bits)
