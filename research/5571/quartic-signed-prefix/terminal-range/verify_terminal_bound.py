# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint==0.8.0"]
# ///
"""Check all-real-x bounds for the original quartic terminal integrals and grids."""

import json
from pathlib import Path

import flint
from flint import acb, arb, ctx, fmpq

from check_small_variance import narrow_terms, require, verify as verify_narrow


def integrated_gaussian_moment(a):
    a = arb(a)
    return 1 / (4-a**2/2) + 1 / (arb("4.5")-a**2/2) + 1 / (arb("4.5")-a**2)


def prime_cutoff_error(x):
    result = arb(0)
    for c, a in [(1/arb(8).sqrt(), arb(8).sqrt()), (arb(1)/3, arb(3)),
                 (1/arb(18).sqrt(), arb("4.5").sqrt())]:
        mellin = (1-arb(2)**(1-a)) / ((a-1)*a*(a+1))
        result += arb(4).log()*c*mellin*a/(a-1)*x**(2-a)
    return result


def integrated_multiplier(g):
    """Integral majorant for |Phi_v| against exp(-4v) from zero onward."""
    return 1/(4+g/2) + 1/(arb("4.5")+g/2) + 1/(arb("4.5")+g)


def critical_mass(precision):
    path = Path(__file__).resolve().parent.parent / f"low-spectrum-{precision}.json"
    brackets = json.loads(path.read_text(encoding="utf-8"))["rational_ordinate_brackets"]
    require(len(brackets) == 13, "original two-sided quartic ledger")
    mass = arb(0)
    for left, right in brackets:
        a, b = arb(fmpq(left)), arb(fmpq(right))
        ordinate = a.union(b)
        require(abs(ordinate) > 4, "verified first ordinate")
        rho = acb(arb("0.5"), ordinate)
        kernel = (acb(2)**(1-rho)-1) / ((1-rho)*rho*(1+rho))
        mass += abs(kernel)*integrated_multiplier(ordinate**2-arb(".25"))
    remaining = (1+arb(2).sqrt())*arb(".001430297")*integrated_multiplier(arb(22)**2-arb(".25"))
    return mass+remaining


def high_moment(t, a):
    answer = arb(0)
    for u, r in [(arb("3.5"), arb(".5")), (arb(4), arb(".5")), (arb("3.5"), arb(1))]:
        m = 5+2*a*r*t**2
        exponent = m-1
        log_t = t.log()
        counting = (log_t/exponent+1/exponent**2)/arb.pi()
        counting += arb(".55")/t*(2*log_t+1/m)
        answer += (-(u+r*t**2)*a).exp()*counting/r
    return answer/t**4


def wide_band_upper(x, H, variance, b):
    d = 1 / (arb("5.60")*(5*b*H).log())
    local = (1+arb(2)**d)*x**(arb(".5")-d)*high_moment(H, variance)/2
    return local+x.sqrt()*high_moment(b*H, variance)


def run(bits):
    ctx.prec = bits
    H = arb(20_000_000)
    small_u3 = arb("6.90e-15")
    quartic_mass = critical_mass(bits)
    derivative = (-arb(1)/2).exp() + arb(3)/4*(2+arb(2).sqrt())*(2/arb.pi()).sqrt()
    mesh = derivative*arb(4).log()/4
    require(mesh < arb(".92"), "global grid error")
    print(f"{bits} bits; weighted quartic mass {quartic_mass.str(14)}; mesh {mesh.str(14)}")

    # For x^2<=10 the second cutoff ceil(x^2) also contains no real-row prime.
    for xmin, local_mesh, cap in [
        (arb(10).sqrt(), derivative*arb(209).log()/40, ".71"),
        (arb(5), mesh, ".90"),
    ]:
        total = (arb(".625")*integrated_gaussian_moment(".5")
                 +arb("6.8e-15")*10**12*integrated_gaussian_moment(1)
                 +(prime_cutoff_error(xmin)+local_mesh)/xmin.sqrt())
        require(total < arb(cap), "small-x critical-scale bound")
        print(f"  small range starts {xmin.str(8)}; upper {total.str(16)}")

    # Parent curve bounds all larger x, with every increasing term at xmax and
    # every decreasing factor at xmin. Both cutoffs include all p <= x^2 here.
    ranges = [
        ("1e24", "1e48", "5", "5.20", 600, ".00775"),
        ("1e48", "1e60", "5", "5.17", 1500, ".00784"),
        ("1e60", "1e66", "5", "5.13", 1500, ".23"),
        ("1e66", "2e67", "5", "5.11", 1500, ".96"),
        ("2e67", "2.30e67", "5.04", "5.11", 2800, ".996"),
        ("2.30e67", "2.32e67", "5.04", "5.11", 2800, "1"),
    ]
    for first, last, split, anchor, bins, ceiling in ranges:
        xmin, xmax, b = arb(first), arb(last), arb("1.235")
        variance = (arb(split)/H)**2
        physical, anchor_high = narrow_terms(xmin, anchor, bins, split=split, band="1.235")
        narrow = variance*(arb("1.14")*(arb(".062")+3*small_u3)+3*arb(".563e-6"))
        narrow += (physical+anchor_high)*xmax.sqrt()
        wide = wide_band_upper(xmax, H, variance, b)
        lower_spectrum = quartic_mass+arb(".75")*(arb(".28465")/xmin**arb(".25")+15*small_u3)
        elementary = 3*integrated_gaussian_moment(0)/xmin.sqrt()
        elementary += 2*integrated_gaussian_moment(arb(1)/3)/xmin**(arb(1)/6)
        discretization = (prime_cutoff_error(xmin)+mesh)/xmin.sqrt()
        total = narrow+wide+lower_spectrum+elementary+discretization
        require(total < arb(ceiling), f"whole terminal bound on [{first},{last}]: {total}")
        print(f"  {first} <= x <= {last}; split={split}, anchor={anchor}, bins={bins}")
        print("    physical, anchor high, wide high, low, elementary, finite, total =")
        for value in (physical*xmax.sqrt(),anchor_high*xmax.sqrt(),wide,lower_spectrum,
                      elementary,discretization,total):
            print(f"      {value.str(17)}")
    require(arb("2.32e67").log() < 6**4, "near-linear cutoff is ceil(x^2) on this range")

    gap_factor = arb("1.0197")
    band = arb("1.01")
    d = 1/(arb("5.60")*(5*band*H).log())
    require((1-gap_factor*(1-2*d))*H**2 > 1, "cofinal cutoff, inner ordinate band")
    require((band**2-gap_factor)*H**2 > 1, "cofinal cutoff, outer ordinate band")
    xmin = arb("1e24")
    # For the sublinear prime prescription the earlier omission bound is <=6,
    # or <=6 sqrt(pi)/x when its smaller cutoff is active.
    tail_grid = (arb(6)+mesh)/xmin.sqrt()
    wide_exterior = arb("2.25")*small_u3
    remainder = (quartic_mass+arb(".75")*(arb(".28465")/xmin**arb(".25")+15*small_u3)
                 +3*integrated_gaussian_moment(0)/xmin.sqrt()
                 +2*integrated_gaussian_moment(arb(1)/3)/xmin**(arb(1)/6))
    cofinal = wide_exterior+remainder+tail_grid
    require(cofinal < arb(".00775"), "all-height cropped finite and grid bound")
    slope = 1/(gap_factor*H**2)
    print(f"  all-height normalized ceiling {cofinal.str(17)} from x=1e24; slope {slope.str(17)}")

    path = Path(__file__).resolve().parent.parent / f"low-spectrum-{bits}.json"
    roots = json.loads(path.read_text(encoding="utf-8"))["rational_ordinate_brackets"]
    ordinates = [abs(arb(fmpq(lo)).union(arb(fmpq(hi)))) for lo, hi in roots]
    least = [t for t in ordinates if t < 5]
    require(len(least) == 1 and all(t < 5 or t > 6 for t in ordinates), "unique least pair")
    g0 = least[0]**2-arb(".25")
    unknown_inner = 1-d-slope*(H**2-(1-d)**2)/2
    unknown_outer = 1-slope*((band*H)**2-1)/2
    require(unknown_inner < arb(".499971") and unknown_outer < arb(".499971"), "unknown quartic gap")
    eta_high = arb(".5")-slope*(H**2-1)/8
    alpha = arb(".5")-slope*g0/2
    require(alpha > arb(".49999999999997") and eta_high < arb(".378"), "dominant first-pair gap")
    largest_slope = arb(".01")
    last_alpha = arb(".5")-largest_slope*g0/2
    require(last_alpha > arb(".415") and last_alpha > arb(1)/3+largest_slope/18,
            "proper powers for all fixed slopes through .01")
    print("  least ordinate", least[0].str(14), "unknown bounds", unknown_inner.str(14), unknown_outer.str(14))
    print("  exponent decrement at first slope", (slope*(4+g0/2)).str(14),
          "exponent at slope .01", (last_alpha-4*largest_slope).str(14))
    rho0 = acb(arb(".5"),least[0])
    amplitude = abs((acb(2)**(1-rho0)-1)/((1-rho0)*rho0*(1+rho0)))
    frequency, decay = least[0]/2, 4+g0/2
    minimum = amplitude*2/frequency*(-2*arb.pi()*decay/frequency).exp()
    maximum = amplitude/decay
    require(minimum > arb("1.22e-18") and maximum < arb(".002529"), "positive periodic profile")
    print("  periodic profile: lower bound", minimum.str(12), "upper bound", maximum.str(12))


if __name__ == "__main__":
    require(flint.__version__ == "0.8.0", "python-flint 0.8.0 is required")
    for precision in (128, 192):
        verify_narrow(precision)
        run(precision)
