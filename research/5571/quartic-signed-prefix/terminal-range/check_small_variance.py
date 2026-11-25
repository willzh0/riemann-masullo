# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint==0.8.0"]
# ///
"""Outward interval bounds for the small-variance prime and spectral errors."""

import flint
from flint import arb, ctx, fmpq


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def dec(text):
    return arb(text)


def damped_tail(t, width):
    z2 = (width*t)**2
    k = 2+z2
    ledger = (t.log()/k + 1/k**2)/arb.pi() + dec(".55")/t*(2*t.log()+1/(k+1))
    return (-z2/2).exp()*ledger/t**2


def narrow_terms(x_lower, z, cells_per_width, split="5", band="1.5", kadiri=True):
    H = arb(20_000_000)
    v0 = (dec(split)/H)**2
    sigma = dec(z)/H
    w = sigma**2
    step = sigma/cells_per_width
    radius = 100*sigma
    logx = x_lower.log()
    require(w >= v0 and w < fmpq(1, 10**12), "widths")
    require(logx+(step/10).log()-radius > 1, "all Brun-Titchmarsh intervals exceed q")
    density = (logx+radius)/(2*(logx+(step/10).log()-radius))
    # Apply this bin factor to the positive physical defect on each log side.
    defect = dec(".440660")*sigma**3 - dec(".440659")*arb(2)/5*v0**(arb(3)/2)
    variation = dec("4.1")*step*(w+v0/2)
    far = dec("1e-500")*sigma**3
    physical = density*radius.exp()*(defect+variation) + far
    width_factor = 2*(w/2).exp() + w.exp()*(-(H*sigma)**2/2).exp()
    base = damped_tail(H,sigma)
    if kadiri:
        b = dec(band)
        d = 1/(dec("5.60")*(5*b*H).log())
        high = width_factor*((1+arb(2)**d)/2*(-d*logx).exp()*base
                             + damped_tail(b*H,sigma))
    else:
        high = width_factor*base
    return v0*physical, v0*high


def row(x_power, z, cells_per_width, target_e34, kadiri):
    physical, high = narrow_terms(arb(10)**x_power, z, cells_per_width, kadiri=kadiri)
    coefficient = physical+high
    require(coefficient < dec(target_e34)*dec("1e-34"), "reported linear coefficient")
    print(f"  x>=1e{x_power}, sigma*H={z}, sigma/step={cells_per_width}, Kadiri={kadiri}")
    print(f"    integrated physical={physical.str(14)}, high={high.str(14)}, total={coefficient.str(14)}")


def verify(bits):
    ctx.prec = bits
    H = arb(20_000_000)
    v0 = (5/H)**2
    max_variance = dec("1e-12")
    m3 = 2*(2/arb.pi()).sqrt()
    m5 = 4*m3
    leading = (2*arb(2).sqrt()-2)*m3/3
    lower = (((2*arb(2).sqrt()-1)*(-max_variance/2).exp()-1)*m3/3)
    tail = 2*arb(2)**(arb(5)/2)*m5*max_variance/120/(1-2*max_variance/7)
    require(lower > dec(".440659") and leading+tail < dec(".440660"), "kink masses")
    require(48*dec("1e-12")*(-arb(1250)).exp() < dec("1e-500")*(5/H)**3, "far prime crossings")
    hp = dec("6.8e-15")
    low = dec("1.14")*(dec(".062")+3*hp) + 3*(dec(".625")-dec(".062"))*dec("1e-6")
    require(v0*low < dec("4.42e-15"), "anchor low spectrum at x>=1e24")
    old = dec("1.14")*(dec(".625") + H.log()/(6*H**2)*dec("1e12"))
    require(v0*old < dec("4.51e-14"), "small terminal cutoff")
    # Independently check the global envelope from the historical raw proof.
    width = dec("2.9e-7")
    old_b = dec("2.022e-21") + (dec("2.731")*width**3 + 3*dec("18.1")*width**4)/3
    old_c = 17*dec("2.8")*width
    old_a = (dec(".16900")+dec(".014632")+(12+37*dec("1e-24"))*dec("1e-12")
             +dec("1.5")*dec("4.002")*dec("4.1")*width**2+old_c)
    require(old_b < dec("2.43e-20") and old_c < dec(".000014") and old_a < dec(".184"),
            "historical global linear and square-root clauses")
    require(dec("1.14")*v0*dec("2.43e-20") < dec("1.732e-33"), "historical averaged coefficient")
    print(f"{bits} bits: kink coefficient {leading.str(16)}, anchor square-root {str(v0*low)}")
    print(f"  historical raw: a={old_a.str(12)}, c={old_c.str(12)}, b={old_b.str(12)}")
    row(24, "5.29", 600, "3.56", False)
    row(24, "5.20", 600, "3.32", True)
    row(36, "5.20", 1200, "2.63", True)
    row(48, "5.17", 1500, "2.32", True)
    row(60, "5.13", 1500, "2.13", True)
    row(66, "5.11", 1500, "2.06", True)


if __name__ == "__main__":
    require(flint.__version__ == "0.8.0", "requires python-flint 0.8.0")
    for precision in (128, 192):
        verify(precision)
