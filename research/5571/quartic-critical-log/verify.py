"""Recombine the outward cell ledger and certify the reference and tail with rational arithmetic."""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from fractions import Fraction as Q
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run the verifier without Python optimization.")

HERE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def unit_log(x, terms=42):
    """Bound ln(x), 1 <= x <= 2, by the positive inverse-hyperbolic-tangent series."""
    assert 1 <= x <= 2
    u = (x-1)/(x+1)
    power = u
    total = Q(0)
    for j in range(terms):
        total += 2*power/(2*j+1)
        power *= u*u
    return total, total+2*power/((2*terms+1)*(1-u*u))


LOG2 = unit_log(Q(2))


def log_bound(x):
    assert x>0
    k = 0
    while x>=2:
        x /= 2
        k += 1
    while x<1:
        x *= 2
        k -= 1
    low, high = unit_log(x)
    return low+k*LOG2[k<0], high+k*LOG2[k>=0]


def atan_bound(x, terms=30):
    assert 0<x<1
    total, value = Q(0), x
    for j in range(terms):
        total += value/(2*j+1)
        value *= -x*x
    next_sum = total+value/(2*terms+1)
    return min(total,next_sum), max(total,next_sum)


def sqrt_down(x, bits=125):
    if x<0:
        raise ValueError("A negative number has no real square root.")
    s=1<<bits
    return Q(math.isqrt((x.numerator*s*s)//x.denominator),s)


def reference():
    N, scale = 10000, 1<<100
    rlo = rhi = ilo = ihi = 0
    for n in range(1,N+1):
        n2 = n*n
        low, high = scale//n2, -((-scale)//n2)
        a=n%5
        if a==1: rlo+=low; rhi+=high
        elif a==4: rlo-=high; rhi-=low
        elif a==2: ilo+=low; ihi+=high
        elif a==3: ilo-=high; ihi-=low
    # The two rational coordinates are positive; each lower endpoint contributes to a norm lower.
    assert 0 < rlo <= rhi and 0 < ilo <= ihi
    norm_lower=sqrt_down(Q(rlo*rlo + ilo*ilo,scale*scale))
    # At a complete period, the omitted tail is at most sqrt(2)/N² < 3/(2N²).
    return log_bound(norm_lower - Q(3,2*N*N))[0]


def upwards(n, places=16):
    integer=math.ceil(n*10**places)
    s="-" if integer<0 else ""
    k,r=divmod(abs(integer),10**places)
    return f"{s}{k}.{r:0{places}d}"


def downwards(n, places=16):
    integer=math.floor(n*10**places)
    s="-" if integer<0 else ""
    k,r=divmod(abs(integer),10**places)
    return f"{s}{k}.{r:0{places}d}"


def check(path):
    receipt=json.loads((path/"receipt.json").read_text(encoding="utf8"))
    T,scale=receipt["T"],receipt["scale"]
    assert T>=100 and scale==1<<60
    assert receipt["script_sha256"]==digest(HERE/"certify.py")
    assert receipt["cells_sha256"]==digest(path/"cells.csv")
    quart_count=0; total_cells=0; signed=[[0,0],[0,0]]
    with (path/"cells.csv").open(encoding="ascii",newline="") as io:
        data=csv.reader(io)
        assert next(data)==["quarter_index","subdivision_bits","subcells","majorant_lower_scaled","majorant_upper_scaled"]
        for row in data:
            j,bits,count,lo,hi=map(int,row)
            expected=-4*T+quart_count
            assert j==expected and lo<=hi
            level=(1+abs(2*j+1)//8).bit_length()-1
            assert bits==max(receipt["coarse_bits_min"],receipt["fine_bits"]-level)
            assert count*4==2**bits
            signed[j>=0][0]+=lo; signed[j>=0][1]+=hi
            total_cells+=count; quart_count+=1
    assert quart_count==8*T and total_cells==receipt["subcells"]
    assert signed[0]==receipt["majorant_negative_scaled"] and signed[1]==receipt["majorant_positive_scaled"]
    upper=Q(signed[0][1]+signed[1][1],scale)
    a,b=atan_bound(Q(1,5));c,d=atan_bound(Q(1,239))
    pi_low,pi_high=16*a-4*d,16*b-4*c
    assert pi_low>Q(314159,100000) and pi_high<Q(314160,100000)
    tail=Q(3,T)/pi_low*(log_bound(Q(5))[1]+(log_bound(Q(T))[1]+1)/2)
    al,ah=atan_bound(Q(3,2*T))
    mu_low,mu_high=2*al/pi_high,2*ah/pi_low
    energy_upper=20/sqrt_down(Q(T))
    log_ratio_upper=log_bound(energy_upper/mu_low)[1]
    assert log_ratio_upper>0 and mu_low>0
    jensen=mu_high*log_ratio_upper/2
    log_ref=reference()
    primary=upper+tail-log_ref
    second=upper+jensen-log_ref
    dref=Q(receipt["reference"]["log_lower_computed_enclosure"][0],scale)
    assert 0<dref-log_ref<Q(1,10**8)
    # Independent low/high comparisons account for the final dyadic rounding in the ledger.
    assert abs(tail-Q(receipt["tails"]["elementary_upper_formula_scaled"][1],scale))<Q(1,10**15)
    assert abs(jensen-Q(receipt["tails"]["jensen_upper_formula_scaled"][1],scale))<Q(1,10**15)
    assert abs(primary-Q(receipt["G_elementary_upper_numerator"],scale))<Q(1,10**8)
    return {"T":T,"subcells":total_cells,"quarter_cells":quart_count,
            "ledger_upper":upwards(upper),"reference_lower":downwards(log_ref),
            "elementary_tail_upper":upwards(tail),"jensen_tail_upper":upwards(jensen),
            "elementary_G_upper":upwards(primary),"jensen_G_upper":upwards(second),
            "elementary_below_0.005":primary<Q(1,200),"jensen_below_0.005":second<Q(1,200),
            "input_file":str(path.name),"cells_sha256":digest(path/"cells.csv"),
            "receipt_sha256":digest(path/"receipt.json"),"verifier_sha256":digest(__file__)}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input",type=Path)
    args=parser.parse_args()
    p=(HERE/args.input).resolve()
    proof=check(p)
    (p/"rational-check.json").write_text(json.dumps(proof,indent=2)+"\n",encoding="utf8")
    print(json.dumps(proof,indent=2))
