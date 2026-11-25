"""Certify a nonreal pole of every fixed real phase projection of the quartic dilation.

Requires python-flint. Every comparison below is an interval inequality.
"""
from fractions import Fraction
from flint import acb, arb, ctx, dirichlet_char, fmpq


def ball(x):
    return arb(fmpq(x.numerator, x.denominator))


def verify(precision):
    ctx.prec = precision
    quadratic = dirichlet_char(5, 4)
    quartic = dirichlet_char(5, 2)
    conjugate = dirichlet_char(5, 3)
    assert quartic(2) == acb(0,1) and conjugate(2) == acb(0,-1)
    assert [quadratic(n) for n in range(1,5)] == [1,-1,-1,1]

    def quadratic_hardy(t):
        s = acb(arb(1)/2, ball(t))
        value = (arb(5)/arb.pi())**(s/2) * (s/2).gamma() * quadratic.l_function(s)
        assert value.imag.contains(0)
        return value.real

    left, right = Fraction(6), Fraction(7)
    assert quadratic_hardy(left) > 0 and quadratic_hardy(right) < 0
    for _ in range(64):
        mid = (left+right)/2
        val = quadratic_hardy(mid)
        if val > 0:
            left = mid
        else:
            assert val < 0
            right = mid
    mid, radius = (left+right)/2, (right-left)/2
    gamma = arb(ball(mid), ball(radius))
    s = acb(arb(1)/4, gamma/2)

    def hurwitz(z, char):
        return acb(5)**(-z) * sum(char(a) * z.zeta(arb(a)/5) for a in range(1,5))

    l1 = hurwitz(s,quartic)
    l2 = hurwitz(s,conjugate)
    for char, val in ((quartic,l1),(conjugate,l2)):
        assert val.overlaps(char.l_function(s))
        assert abs(val)>0
        v3=hurwitz(3*s,char)
        assert v3.overlaps(char.l_function(3*s)) and abs(v3)>0
    assert abs(l1) - abs(l2) > arb(3)/2
    amplitude=abs(abs(l1)-abs(l2))/(4*abs(s*(s+1)))
    print("bits",precision,"gamma",gamma,"|Lchi|",abs(l1),"|Lbar|",abs(l2),"residue lower bound",amplitude)
    assert amplitude > arb(317)/10000


if __name__ == "__main__":
    for prec in (128,192):
        verify(prec)
