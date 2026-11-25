"""Certify a finite rational zero-free box using one unshifted product test."""
import json
from math import comb
from pathlib import Path
from flint import arb, acb, fmpq, ctx

ctx.prec = 224
# Each seed names the quarter interval [k/4,(k+1)/4]. The code proves
# opposite endpoint signs for every interval. Omitting an interval reduces
# the certified line mass and would only weaken the final upper bound.
quarter_starts = [
    56, 84, 100, 121, 131, 150, 163, 173, 192, 199, 211, 225,
    237, 243, 260, 268, 278, 288, 302, 308, 317, 331, 338, 349,
    355, 369, 378, 383, 395, 405, 414, 421, 428, 444, 447, 457,
    464, 475, 485, 491, 497, 510, 518, 524, 533, 539, 552, 558,
    564, 572, 584, 589, 600, 603, 612, 624, 630, 635, 644, 652,
    662, 668, 676, 679, 693, 699, 705, 713, 719, 728, 739, 742,
    748, 757, 768, 772, 781, 787, 792, 805, 809, 816, 821, 831,
    838, 846, 853, 858, 864, 876, 882, 885, 896, 899, 909, 917,
    925, 927, 934, 946, 951, 958, 964, 971, 976, 988, 992, 998,
    1004, 1012, 1021, 1025,
]
brackets = [(fmpq(k,4), fmpq(k+1,4)) for k in quarter_starts]
M = 771
order = 4
a = 16
ncut = 771
iterations = 32
d = 3**M
weights = [None]*M
tail = 0
for j in range(M,0,-1):
    tail += comb(M,j)*2**j
    weights[j-1] = fmpq(tail if j % 2 else -tail,d)
logs = [arb(j).log() for j in range(1, M+1)]
amps = [arb(c)/arb(j).sqrt() for j,c in enumerate(weights,1)]
log_pi = arb.pi().log()
zeta_error = (arb(2).sqrt()+1)*(arb.pi()*fmpq(513,2)).cosh().sqrt()/d

# The uniform error is the Mellin integral bound for the 771-term binomial
# approximation, divided by the smallest modulus of 1-2^(1-s) on the line.
def sign(t):
    t = arb(t)
    v = sum((amp*acb(0,-t*u).exp() for amp,u in zip(amps,logs)), acb(0))
    v /= 1-arb(2).sqrt()*acb(0,-t*logs[1]).exp()
    angle = acb(fmpq(1,4),t/2).lgamma().imag -t*log_pi/2
    z = (acb(0,angle).exp()*v).real
    if z > zeta_error:
        return 1
    if z < -zeta_error:
        return -1
    raise ArithmeticError(("undetermined sign",str(t),str(z)))

refined = []
for left,right in brackets:
    sl = sign(left)
    assert sl == -sign(right)
    for _ in range(iterations):
        mid = (left+right)/2
        if sign(mid) == sl:
            left = mid
        else:
            right = mid
    refined.append((left,right))
assert all(h1 <= l2 for (_,h1),(l2,_) in zip(refined,refined[1:]))
sq = [fmpq(a*a*(order+j),order) for j in range(order)]
cs = [fmpq((-1)**j*order*comb(2*order-1,order-1)*comb(order-1,j),order+j) for j in range(order)]
assert sum(cs) == 1
# Ordinary Dirichlet partial sums enclose zeta and its derivative. The
# (positive) tails use the integral test at these four real arguments.
def scaled_log_derivative(b2):
    b = arb(b2).sqrt()
    s = b+fmpq(1,2)
    v = [(-s*log_m).exp() for log_m in logs[:ncut]]
    Z = sum(v,arb(0))
    W = sum((u*term for u,term in zip(logs,v)), arb(0))
    k = arb(ncut)
    r0 = k**(1-s)/(s-1)
    r1 = r0*(k.log()+1/(s-1))
    e = r1/(Z-r0)+abs(W)*r0/(Z*(Z-r0))
    return b * (1/s + 1/(s-1) - log_pi/2 + (s/2).digamma()/2 - W/Z + arb(0,e.upper()))

scalar = sum((c*scaled_log_derivative(b2) for c,b2 in zip(cs,sq)), arb(0))
def kernel_central(t):
    v = arb(1)
    for b2 in sq:
        v *= arb(b2)/(arb(b2)+arb(t)**2)
    return v
# K(t) decreases for positive real t, so use the upper bracket endpoint.
submass = 2*sum((kernel_central(hi) for _,hi in refined),arb(0))
budget = scalar-submass
assert budget > 0
cos_margin = sum(((arb(1)/(2*arb(b2).sqrt())).asin() for b2 in sq),arb(0)).cos()
def per_zero(t):
    v = cos_margin
    for b2 in sq:
        v *= arb(b2)/(arb(b2)+t*t+fmpq(1,4))
    return v
heights = {k:max(t for t in range(0,257) if budget<k*per_zero(t)) for k in (2,4)}
answers = {"a":a,"factors":order,"rational_weights":list(map(str,cs)),"scale_squares":list(map(str,sq)),
           "sign_brackets":len(refined),"bisections_per_bracket":iterations,"integer_bases":M,
           "positive_kernel_cosine_margin":str(cos_margin),"arithmetic_scalar":str(scalar),
           "central_mass_lower":str(submass),"remainder_upper":str(budget),
           "integer_exclusion_heights":heights,
           "two_site_bound":str(2*per_zero(heights[2])),"four_site_bound":str(4*per_zero(heights[4])),
           "refined_brackets":[[str(lo),str(hi)] for lo,hi in refined]}
Path(__file__).with_suffix(".json").write_text(json.dumps(answers,indent=2),encoding="utf-8")
print({k:v for k,v in answers.items() if k!="refined_brackets"})

