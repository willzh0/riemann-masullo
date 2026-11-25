"""Verify the quartic annular prime bound in FINITE-QUARTIC.md.

Uses python-flint 0.9.0. The small grid uses a sieve and integer interval
arithmetic. The large-argument proof consists of inequalities valid on
whole real intervals. No prime sum at the largest cutoff is enumerated.
"""
import argparse
import json
from math import isqrt, prod
from pathlib import Path
from flint import acb_series, arb, ctx, dirichlet_char, fmpq


def sieve(n):
    table = bytearray([1]) * (n+1)
    table[:2] = bytes(2)
    for p in range(2,isqrt(n)+1):
        if table[p]:
            table[p*p::p] = bytes((n-p*p)//p+1)
    return table


def check_grid(limit, scale_bits=80):
    scale = 1 << scale_bits
    primes = sieve(limit)
    logs = {}
    for p in range(2,limit+1):
        if primes[p] and p % 5:
            v = (arb(p).log() * scale).floor().unique_fmpz()
            assert v is not None
            logs[p] = int(v)
    # Each prefix holds sum log(p), p*log(p), log(p)/p, separately
    # for real and imaginary parts. Integer weights mean scaled floors.
    whole = [[0,0,0],[0,0,0]]
    half = [[0,0,0],[0,0,0]]
    def extend(prefix,p):
        ell = logs.get(p)
        if ell is None:
            return
        residue = p % 5
        a = prefix[int(residue in (2,3))]
        sign = 1 if residue in (1,2) else -1
        a[0] += sign*ell
        a[1] += sign*p*ell
        a[2] += sign*(ell//p)
    best_num,best_den,best_j = 0,1,0
    for j in range(1,limit+1):
        extend(whole,j)
        m = j//2
        if j % 2 == 0:
            extend(half,m)
        uncertainty = j**3+6*j**2
        nums = []
        for c in (0,1):
            aj,bj,cj = whole[c]
            ah,bh,ch = half[c]
            mid = j*j*(cj-ch)-2*j*aj+4*j*ah+bj-4*bh
            nums.append(abs(mid)+uncertainty)
        num = nums[0]**2 + nums[1]**2
        den = 4*j**3*scale**2
        assert num < den, j
        if num*best_den > best_num*den:
            best_num,best_den,best_j=num,den,j
    assert best_num * 1000000**2 < best_den * 169460**2
    bound = (arb(fmpq(best_num,best_den))).sqrt()
    return {"last":limit,"sieved_primes":sum(primes),
            "integer_log_scale_bits":scale_bits,"largest_bound_at":best_j,
            "largest_certified_ratio_upper":str(bound)}


def constants():
    d = arb("0.00000029")
    v = d*d
    H = arb(20000000)
    Y0,Y1,Y2 = map(arb,(10**6,10**24,10**39))
    # Hadamard and affine-residue inputs for the actual odd quartic.
    ch = dirichlet_char(5,2)
    def ld(s):
        expansion = acb_series([s,1],prec=2).dirichlet_l(ch)
        return (expansion[1]/expansion[0]).conjugate()
    finite = (arb(5)/arb.pi()).log()-arb.const_euler()
    B = finite+2*ld(1).real
    a0 = finite-arb(2).log()+ld(1)
    a1 = finite-arb(2).log()+1+ld(2)
    assert 0 < B < arb(".204") and abs(a0) < 1 and abs(a1) < 1
    assert 12*((1+(-v/2).exp())*(v/2).exp()+(-v/2).exp()*v.exp()) < 37
    # Absolute Gaussian moments for a centered N(0,(rδ)^2).
    # e^(a s) <= 1+a*s*e^(a s), followed by Cauchy-Schwarz.
    def absolute_normal(k):
        return arb(2)**(arb(k)/2)*((arb(k)+1)/2).gamma()/arb.pi().sqrt()
    def moment(k,a):
        def row(r):
            sd = r*d
            rem = (arb(2)*prod(range(1,2*k+3,2))).sqrt()
            return sd**k*(absolute_normal(k)+a*sd*rem*(a*a*sd*sd).exp())
        return 2*row(arb(1))+row(arb(2).sqrt())
    assert moment(1,1) < arb("2.8")*d
    assert moment(2,2) < arb("4.1")*v
    assert moment(3,2) < arb("7.8")*d**3
    assert moment(4,2) < arb("18.1")*d**4
    R = arb
    logqH=(5*H).log()
    # BMOR, Math. Comp. 2021, Corollary 1.2.
    S3=((5*H/(2*R.pi())).log()+R(1)/2)/(2*R.pi()*H**2)
    S3+=(2*(R("0.298")*logqH+R("4.358"))+R("0.298")/3)/H**3
    assert S3 < R("6.81e-15")
    c=(-v/2).exp()
    high=3*S3*((1+c)*(v*(1-H**2)/2).exp()+c*(v*(1-H**2)).exp())
    # Bound the low multiplier by comparison with x(1+c-c*x), x=e^(-v t²/2).
    b=(v/2).exp()
    low_multiplier=1+(2+b+1)*(b-1+b*d)  # valid for 0 <= beta <= 1
    assert low_multiplier < R("1.00001")
    low=R(".204")*2*(R(2).sqrt()-1)*low_multiplier
    power_sqrt=R("1.001102")*R(4)/3*(R(2).sqrt()-1)
    power_cube=3*R(9)/8*(R(2)**(R(2)/3)-1)
    curvature_small=(2*moment(3,2)*Y1.sqrt()+R("1.5")*moment(2,2)/Y0.sqrt())*(2*Y1).log()
    curvature_small+=2*moment(4,2)*Y1.sqrt()+R("1.5")*moment(3,2)/Y0.sqrt()
    remainders=(12+37/Y0)/Y0.sqrt()
    mid=low+power_sqrt+power_cube/Y0**(R(1)/6)+remainders+curvature_small+high*Y1.sqrt()

    X0=R(8*10**9)
    # Signed square and remaining proper powers in the high range.
    high_powers=R("1.001102")*X0/Y1.sqrt()+1/(40*X0.log())+Y1.log()/Y1**(R(1)/6)
    cutoff=4/Y1**(R(1)/4)
    assert cutoff < R(".00001")
    assert R(3)/4-R(5).log()/Y1.log() > R(".72")
    assert R(2).sqrt()/(2*R(".72")) < 1
    assert 2*(8*cutoff.exp()+R("1.5")*cutoff/Y1.sqrt()) < 17
    # Exact cubic moment of the absolute signed density; its sign changes once
    # on the positive half-line, at crossing_radius standard deviations.
    crossing_radius=2*(arb(2).sqrt()*(1+c)/c).log().sqrt()
    def tail_third(t):
        return 2*(t*t+2)*(-t*t/2).exp()/(2*R.pi()).sqrt()
    m3=(1+c-c*2*arb(2).sqrt())*absolute_normal(3)+2*(
        c*2*arb(2).sqrt()*tail_third(crossing_radius/arb(2).sqrt())-
        (1+c)*tail_third(crossing_radius))
    assert 0 < m3 < R("2.731")
    def large_bound(ymax):
        curvature=(d**3*m3+3*moment(4,2))*ymax.sqrt()/3
        curvature+=17*moment(1,1)*(1+ymax.log())
        curvature+=R("1.5")*R("4.002")*moment(2,2)
        return curvature,low+high_powers+(12+37/Y1)/Y1.sqrt()+curvature+high*ymax.sqrt()
    high_curve,large=large_bound(Y2)
    _,through38=large_bound(R(10**38))
    assert mid<R(".933") and through38<R(".428") and large<R(".951")
    cap=R(5*10**39)
    affine=low+high_powers+(12+37/Y1)/Y1.sqrt()+17*moment(1,1)*(1+cap.log())
    affine+=R("1.5")*R("4.002")*moment(2,2)
    linear=high+(d**3*m3+3*moment(4,2))/3
    # Sum sqrt(j) by its trapezoids using concavity, and sum j exactly.
    cumulative=R(".933")*(Y1/Y2)**(R(3)/2)+affine*(R(2)/3+1/(2*Y2))
    cumulative+=linear*cap.sqrt()*(1+1/Y2)/2
    assert cumulative < R(".980")
    return {"delta":str(d),"quartic_B":str(B),"abs_a0":str(abs(a0)),"abs_a1":str(abs(a1)),"zero_height":int(H.unique_fmpz()),"upper_cutoff":"10^39","abs_density_cubic_moment":str(m3),
            "low_zero_coefficient":str(low),"high_zero_coefficient":str(high),
            "BMOR_cubic_tail":str(S3),"middle_band":"10^6 to 10^24",
            "middle_pointwise_bound":str(mid),"full_norm_cumulative_through_5e39":str(cumulative),"large_band":"10^24 to 10^39","large_bound_through_10_38":str(through38),
            "large_pointwise_bound":str(large),"large_prime_power_bound":str(high_powers),
            "large_smoothing_error_bound":str(high_curve)}


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--bits",type=int,default=160)
    parser.add_argument("--limit",type=int,default=1_000_000)
    args=parser.parse_args()
    ctx.prec=args.bits
    data={"working_precision_bits":args.bits,"small_grid":check_grid(args.limit),
          "analytic_intervals":constants()}
    target=Path(__file__).with_name("quartic-bound-"+str(args.bits)+".json")
    target.write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(data))
