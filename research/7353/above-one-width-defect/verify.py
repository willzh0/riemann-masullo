"""Independent 300-bit check with zero counting and a finite-difference B-spline."""
from fractions import Fraction
from math import comb
from pathlib import Path
import json

from flint import acb, acb_series, arb, ctx, fmpq

ctx.prec = 300
here = Path(__file__).parent
certificate = json.loads((here / "certificate.json").read_text())
def q(text):
    v = Fraction(text)
    return fmpq(v.numerator, v.denominator)

intervals = [(q(l), q(u)) for l, u in certificate["positive_sign_brackets"]]
log_pi = arb.pi().log()
def xi_sign(t):
    s = acb(fmpq(1, 2), t)
    value = s * (s-1) / 2 * (-s*log_pi/2).exp() * (s/2).gamma() * s.zeta()
    assert value.imag.contains(0) and not value.real.contains(0)
    return 1 if value.real > 0 else -1

def xi_log_derivative(k):
    s = acb(2, k)
    jet = acb_series([s, 1], prec=2).zeta()
    return (1/s + 1/(s-1) - log_pi/2 + (s/2).digamma()/2 + jet[1]/jet[0]).real

assert int(arb(64).zeta_nzeros().unique_fmpz()) == 14
zeros = [acb.zeta_zero(j) for j in range(1, 17)]
for z, (left, right) in zip(zeros, intervals):
    assert left < z.imag and z.imag < right
    assert z.real == fmpq(1, 2) and xi_sign(left) == -xi_sign(right)

exact_max = arb(0)
ext_brackets = intervals + [(-u,-l) for l,u in intervals]
for k in range(65):
    saved = sum(arb(6)/(9+4*max(abs(k-l),abs(k-u))**2) for l,u in ext_brackets)
    remaining = xi_log_derivative(k) - saved
    exact_max = max(exact_max,remaining)
assert exact_max < arb(certificate["largest_cell_budget_upper"])

def finite_difference(z, c):
    d = fmpq(1,16)
    coefficients = [(-1)**j*comb(16,j) for j in range(17)]
    shifted = sum(v*((c+(16-2*j)*d)*z).exp() for j,v in enumerate(coefficients))
    four_roots = (z+fmpq(1,2))*(z-fmpq(1,2))*z*(z-1)
    return four_roots * shifted/(2*d*z)**16

tol = arb(fmpq(1, 2**32))
known = [z for z in zeros if z.imag < 64]
report = []
for row in certificate["trace_enclosures"]:
    center = q(row["center"])
    parts = [finite_difference(z,center) for z in known]
    exact_low = 2*sum(v.real for v in parts)
    assert arb(row["low_without_mollification_unscaled"]).contains(exact_low)
    # A real even mollifier eliminates its first moment; this improves the
    # error for the reference check to order epsilon^2.
    smooth = sum(abs(v)*tol**2*abs(z)**2*(tol/2).exp() for z,v in zip(known,parts))
    assert smooth < arb(row["mollification_error_upper_unscaled"])
    # Use the true centered log derivative and the exact degree-4 norms.
    logder_bound = 2*xi_log_derivative(0)
    assert logder_bound < 3
    scale = (arb(16)*arb(fmpq(3,64)).cosh())**16
    horiz = (1+arb(fmpq(5,256))**2)**2
    tail = (logder_bound*horiz*scale/arb(64)**10
            * (fmpq(3,4)*(arb(center)+tol)).exp())
    assert tail < arb(row["uncounted_tail_upper_unscaled"])
    lo,hi = (exact_low-smooth-tail)/10000,(exact_low+smooth+tail)/10000
    assert arb(row["trace_lower"]) < lo and hi < arb(row["trace_upper"])
    report.append({"center":str(center),"independent_lower":str(lo.lower()),
                   "independent_upper":str(hi.upper())})
first_z = zeros[0]
first_value = abs(finite_difference(first_z,fmpq(7,4)))/10000
first_err = tol**2*abs(first_z)**2*(tol/2).exp()/2
first_lower=first_value*(1-first_err)
assert first_lower > arb(certificate["first_coefficient_modulus_lower"])
assert first_lower > fmpq(11364,10000)

summary={"first_coefficient_independent_lower":str(first_lower.lower()),"precision_bits":ctx.prec,"direct_zero_count_64":14,"checked_positive_brackets":16,
         "direct_xi_signs":32,"direct_xi_logder_cells":65,"max_exact_cell_remainder":str(exact_max),
         "reciprocal_square_sum_upper":str(logder_bound.upper()),"enclosures":report}
Path(__file__).with_suffix(".json").write_text(json.dumps(summary,indent=2)+"\n")
print(json.dumps(summary))
