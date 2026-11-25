"""Finite Gaussian ray class at 7 and a prime distinguishing the two inverse L-series."""
from fractions import Fraction
from math import isqrt
import json


def mul(x,y):
    a,b=x
    c,d=y
    return ((a*c-b*d)%7,(a*d+b*c)%7)


def orbit(x):
    a,b=x
    return min((u%7,v%7) for u,v in ((a,b),(-b,a),(-a,-b),(b,-a)))


def is_prime(n):
    return n>1 and all(n%d for d in range(2,isqrt(n)+1))


def calculate():
    g=(2,1)
    powers=[(1,0)]
    for j in range(48):
        powers.append(mul(powers[-1],g))
    assert powers[-1]==(1,0) and len(set(powers[:-1]))==48
    assert [(a,-b%7) for a,b in powers[:-1]]==[powers[(7*k)%48] for k in range(48)]
    assert len({orbit(x) for x in powers[:12]})==12
    assert orbit(powers[12])==orbit((1,0))
    target=orbit(powers[2])
    nearby = [(a*a+b*b,a,b) for a in range(1,50) for b in range(1,50)
              if is_prime(a*a+b*b) and orbit((a,b))==target]
    p,a,b=min(nearby)
    assert p%4==1 and p!=7 and orbit((a,-b))==target
    # z=(2+i)^4/|2+i|^4 gives the first unramified angular character.
    assert (Fraction(-7,25)**2 + Fraction(24,25)**2)==1
    return dict(modulus=7,unit_generator=g,unit_order=48,ray_order=12,
                conjugation_on_exponents=7,selected_indices=[1,11,7,5],
                split_prime=p,gaussian_generator=[a,b],two_prime_ideal_classes=[2,2],
                first_angular_value=["-7/25","24/25"])


if __name__=="__main__":
    print(json.dumps(calculate(),indent=2))
