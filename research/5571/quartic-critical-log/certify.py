"""An upper integral of log |L(1/2+it, chi)| using intervals and finite Taylor models."""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import platform
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
if (HERE / "vendor").is_dir():
    sys.path.insert(0, str(HERE / "vendor"))
import flint
from flint import acb, acb_series, arb, ctx, dirichlet_char

SCALE = 1 << 60
ORIENTATION = (acb(0), acb(1), acb(0, 1), acb(0, -1), acb(-1))


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def scaled_bound(x, upper):
    """Return an exact integer ceiling of the upper endpoint, or floor of the lower."""
    endpoint = x.upper() if upper else x.lower()
    if not endpoint.is_finite() or not endpoint.is_exact():
        raise ArithmeticError("A finite exact dyadic endpoint is required.")
    mantissa, exponent = map(int, endpoint.man_exp())
    exponent += SCALE.bit_length()-1
    if exponent >= 0:
        return mantissa << exponent
    denominator = 1 << -exponent
    return -((-mantissa)//denominator) if upper else mantissa//denominator


def endpoints(x):
    return [scaled_bound(x, False), scaled_bound(x, True)]


def lower_decimal(n, places=14):
    v = (Fraction(n, SCALE)*10**places).__floor__()
    sign = "-" if v < 0 else ""
    k, r = divmod(abs(v), 10**places)
    return f"{sign}{k}.{r:0{places}d}"


def upper_decimal(n, places=14):
    v = (Fraction(n, SCALE)*10**places).__ceil__()
    sign = "-" if v < 0 else ""
    k, r = divmod(abs(v), 10**places)
    return f"{sign}{k}.{r:0{places}d}"


def set_context(prec, order):
    ctx.prec = prec
    ctx.cap = order
    ctx.threads = 1


def character():
    chi = dirichlet_char(5, 2)
    assert all(chi(i) == v for i, v in enumerate(ORIENTATION))
    assert chi.order() == 4 and chi.conductor() == 5
    return chi


def hurwitz_value(s):
    """Use the four nonzero residue classes. This works for acb and acb_series."""
    a = [acb(i)/5 for i in range(1,5)]
    hz = [s.zeta(x) for x in a]
    return (-s * arb(5).log()).exp() * ((hz[0]-hz[3]) + acb(0, 1)*(hz[1]-hz[2]))


def jet(t, order, chi, engine):
    # The formal variable is a real height displacement when evaluated on the real axis.
    s = acb_series([acb(arb(1)/2, t), acb(0, 1)], prec=order)
    v = s.dirichlet_l(chi) if engine == "dirichlet" else hurwitz_value(s)
    return [v[k] for k in range(order)]


def half_block(payload):
    j0, j1, prec, order, fine, coarse, engine = payload
    set_context(prec, order)
    chi = character()
    # A coarse interval [j/4,(j+1)/4] is centered at (2j+1)/8.
    pi = arb.pi()
    rows = []
    for j in range(j0, j1):
        center = arb(2*j+1)/8
        poly = jet(center, order, chi, engine)
        # Cauchy on the height disk of radius 3/8, evaluated within radius 1/8.
        remainder = arb(18*(abs(2*j+1)+8))/(8*3**order)
        # Dyadic refinements depend only on the preassigned height, never on function values.
        lv = (1 + abs(2*j+1)//8).bit_length()-1
        bits = max(coarse, fine-lv)
        den = 1 << bits
        count = den//4
        halfstep = arb(1)/(2*den)
        subtotal = arb(0)
        for k in range(count):
            index = j*count + k
            offset = arb((2*k+1-count))*halfstep
            u = arb(offset, halfstep)
            value = poly[-1]
            for c in reversed(poly[:-1]):
                value = value*u+c
            # abs_upper is an outward upper bound for every value of the polynomial on the cell.
            upper = value.abs_upper() + remainder
            assert upper > 0
            # Exact Cauchy probability of the cell via atan subtraction, valid on either half-axis.
            weight = (arb(6*den)/(9*den*den+4*index*(index+1))).atan()/pi
            subtotal += weight*upper.log()
        rows.append((j, bits, count, *endpoints(subtotal)))
    return rows


def reference_and_controls(T, prec, order):
    set_context(prec, order)
    chi = character()
    N = 10000
    # The summands are complex rationals; outward Arb encloses their finite sum.
    rr, ii = arb(0), arb(0)
    for n in range(1, N, 5):
        rr += arb(1)/(n*n)-arb(1)/((n+3)*(n+3))
        ii += arb(1)/((n+1)*(n+1))-arb(1)/((n+2)*(n+2))
    partial = acb(rr, ii)
    err = arb(2).sqrt()/(N*N)
    lower = (partial.abs_lower()-err).log()
    upper = (partial.abs_upper()+err).log()
    evaluated = acb(2).dirichlet_l(chi)
    assert (evaluated-partial).abs_upper() < err
    assert lower < abs(evaluated).log() and abs(evaluated).log() < upper
    controls = []
    # Predetermined ordinary evaluation points independently check the character orientation,
    # both signs of height, the Taylor variable i*x and the four-residue Hurwitz formula.
    for j in sorted({-4*T, -65, -2, -1, 0, 1, 63, 4*T-1}):
        t = arb(2*j+1)/8
        z = acb(arb(1)/2,t)
        native, alternate = z.dirichlet_l(chi), hurwitz_value(z)
        assert native.overlaps(alternate)
        p = jet(t, order, chi, "dirichlet")
        other = jet(t, order, chi, "hurwitz")
        assert all(x.overlaps(y) for x, y in zip(p, other))
        for x in [arb(-3)/32, arb(5)/64]:
            a = p[-1]
            for c in reversed(p[:-1]):
                a = a*x+c
            exact = hurwitz_value(acb(arb(1)/2, t+x))
            rem = arb(18*(abs(2*j+1)+8))/(8*3**order)
            assert (a-exact).abs_upper() < rem
        controls.append(j)
    return {"N":N, "log_lower_computed_enclosure":endpoints(lower),
            "log_upper_computed_enclosure":endpoints(upper),
            "native_log_modulus_enclosure":endpoints(abs(evaluated).log()),
            "two_formula_control_centers_j":controls}


def finish(rows, T, prec, order, fine, coarse, engine, runtime, dest, workers):
    set_context(prec, order)
    assert [r[0] for r in rows] == list(range(-4*T,4*T))
    assert all(2**r[1] == 4*r[2] and r[3] <= r[4] for r in rows)
    with (dest/"cells.csv").open("w",encoding="ascii",newline="") as handle:
        out=csv.writer(handle,lineterminator="\n")
        out.writerow(("quarter_index","subdivision_bits","subcells","majorant_lower_scaled","majorant_upper_scaled"))
        out.writerows(rows)
    pos = [sum(r[i] for r in rows if r[0]>=0) for i in (3,4)]
    neg = [sum(r[i] for r in rows if r[0]<0) for i in (3,4)]
    cen = [pos[k]+neg[k] for k in (0,1)]
    ref = reference_and_controls(T,prec,order)
    # Direct periodic Dirichlet bound |L| <= 5 sqrt(|t|) applies for |t|>=100.
    constant = arb(5) if T >= 100 else (2*(1+arb(5)/T).sqrt() + 2*arb(2).sqrt()*(1+arb(1)/(4*T*T)).sqrt())
    elementary = (arb(3)/(arb.pi()*T))*(constant.log()+(arb(T).log()+1)/2)
    mass = 2*(arb(3)/(2*T)).atan()/arb.pi()
    # Optional: the independent period/Plancherel tail-energy theorem.
    energy = arb(20)/arb(T).sqrt()
    jensen = (mass/2)*(energy/mass).log()
    elem, m, eng, je = map(endpoints,(elementary,mass,energy,jensen))
    reference_lower = ref["log_lower_computed_enclosure"][0]
    g1 = cen[1] + elem[1] - reference_lower
    g2 = cen[1] + je[1] - reference_lower
    rec = {"scale":SCALE,"T":T,"precision_bits":prec,"taylor_terms":order,
      "fine_bits":fine,"coarse_bits_min":coarse,"engine":engine,
      "quarter_centers":len(rows),"subcells":sum(r[2] for r in rows),
      "majorant_negative_scaled":neg,"majorant_positive_scaled":pos,"majorant_compact_scaled":cen,
      "compact_integral_upper_decimal":upper_decimal(cen[1]),
      "tails":{"elementary_upper_formula_scaled":elem,"jensen_upper_formula_scaled":je,
       "pointwise_sqrt_height_constant_scaled":endpoints(constant),"cauchy_tail_mass_scaled":m,"energy_bound_scaled":eng,
       "elementary_upper_decimal":upper_decimal(elem[1]),"jensen_upper_decimal":upper_decimal(je[1])},
      "reference":ref,"reference_log_lower_decimal":lower_decimal(reference_lower),
      "G_elementary_upper_numerator":g1,"G_elementary_upper_decimal":upper_decimal(g1),
      "G_jensen_upper_numerator":g2,"G_jensen_upper_decimal":upper_decimal(g2),
      "runtime_seconds_before_final_io":round(time.monotonic()-runtime,3),"workers":workers,
      "python":sys.version.split()[0],"platform":platform.platform(),"python_flint":flint.__version__,
      "FLINT":flint.__FLINT_VERSION__,"script_sha256":sha(Path(__file__)),
      "cells_sha256":sha(dest/"cells.csv")}
    (dest/"receipt.json").write_text(json.dumps(rec,indent=2)+"\n",encoding="utf8")
    print("T",T,"cells",rec["subcells"],"compact upper",rec["compact_integral_upper_decimal"],
          "reference lower",rec["reference_log_lower_decimal"],"elementary G upper",rec["G_elementary_upper_decimal"],
          "Jensen G upper",rec["G_jensen_upper_decimal"],"seconds",rec["runtime_seconds_before_final_io"],flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--T",type=int,default=2048)
    ap.add_argument("--prec",type=int,default=96)
    ap.add_argument("--order",type=int,default=20)
    ap.add_argument("--fine",type=int,default=14)
    ap.add_argument("--coarse",type=int,default=5)
    ap.add_argument("--engine",choices=["dirichlet","hurwitz"],default="dirichlet")
    ap.add_argument("--workers",type=int,default=4)
    ap.add_argument("--out",type=Path,required=True)
    a=ap.parse_args()
    if a.T<1 or a.prec<40 or a.order<4 or not 2<=a.coarse<=a.fine or a.workers<1:
        raise ValueError("Require positive T and workers, at least four Taylor coefficients and dyadic subcells.")
    dest=a.out if a.out.is_absolute() else HERE/a.out
    dest.mkdir(exist_ok=True,parents=True)
    start=time.monotonic()
    blocks=[(j,min(j+64,4*a.T),a.prec,a.order,a.fine,a.coarse,a.engine) for j in range(-4*a.T,4*a.T,64)]
    if a.workers==1:
        parts=list(map(half_block,blocks))
    else:
        with ProcessPoolExecutor(max_workers=a.workers) as pool:
            parts=list(pool.map(half_block,blocks,chunksize=1))
    finish([r for block in parts for r in block],a.T,a.prec,a.order,a.fine,a.coarse,a.engine,start,dest,a.workers)


if __name__=="__main__":
    main()