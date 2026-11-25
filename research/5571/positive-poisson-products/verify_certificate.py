"""Verify the single product certificate with independent direct xi evaluations."""
import json
from pathlib import Path
from flint import acb, acb_series, arb, ctx, fmpq

ctx.prec = 300
report = json.loads(Path(__file__).with_name("finite_certificate.json").read_text())
logpi = arb.pi().log()
def q(x):
    parts = x.split("/")
    return fmpq(int(parts[0]), int(parts[1]) if len(parts) > 1 else 1)
def xi(s):
    return s*(s-1)/2*( -s*logpi/2).exp()*(s/2).gamma()*s.zeta()
def sign(y):
    v = xi(acb(fmpq(1, 2), y))
    assert v.imag.contains(0)
    assert v.real > 0 or v.real < 0
    return 1 if v.real > 0 else -1
brackets = [(q(l), q(u)) for l,u in report["refined_brackets"]]
assert len(brackets) == 112 and all(sign(l)*sign(u) == -1 for l,u in brackets)
assert all(a < b and b <= c for (a,b),(c,d) in zip(brackets, brackets[1:]))
widths_squared = list(map(q,report["scale_squares"]))
widths = [arb(v).sqrt() for v in widths_squared]
coeffs = list(map(q,report["rational_weights"]))
def direct_logder(s):
    v = acb_series([s, 1],prec=2).zeta()
    return (1/s+1/(s-1)-logpi/2+(s/2).digamma()/2+v[1]/v[0]).real
scalar = sum(c*b*direct_logder(acb(b+fmpq(1,2))) for c,b in zip(coeffs,widths))
def K(y):
    prod = arb(1)
    for s in widths_squared:
        prod *= arb(s)/(arb(s)+y*y)
    return prod
U = scalar - 2*sum(K(arb(u)) for _,u in brackets)
assert arb(report["arithmetic_scalar"]).contains(scalar)
assert arb(report["remainder_upper"]).contains(U)
assert U < arb(fmpq(324779,10**13))
for size, height in ((2,173),(4,189)):
    T = arb(height)
    den = arb(1)
    for s in widths_squared:
        den *= arb(s)/(arb(s)+T*T+fmpq(1,4))
    phase = sum((1/(2*b)).asin() for b in widths)
    assert U < size * phase.cos()*den
audit={"bits":ctx.prec, "independent_direct_xi_endpoint_signs":len(brackets)*2,
       "direct_xi_log_derivative_points":len(widths),
       "true_remainder_upper_from_bracket_endpoints":str(U),
       "verified_reflection_pair_height":173,"verified_quartet_height":189}
Path(__file__).with_suffix(".json").write_text(json.dumps(audit, indent=2))
print(json.dumps(audit))
