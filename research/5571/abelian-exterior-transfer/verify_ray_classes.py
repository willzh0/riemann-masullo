"""Independent finite-ring checks for conjugation-invariant Gaussian ray classes."""
from collections import Counter
from math import gcd
from pathlib import Path
import json


def units_orbit(m, a, b):
    return frozenset((x % m,y % m) for x,y in ((a,b),(-b,a),(-a,-b),(b,-a)))


def actual_counts(m):
    """The class group of Z[i] is trivial. Divide the units mod m by the four units."""
    classes = set()
    for a in range(m):
        for b in range(m):
            if gcd(a*a+b*b,m) == 1:
                classes.add(min(units_orbit(m,a,b)))
    # For a finite abelian group, the fixed dual and the fixed group have
    # the same size: kernel and cokernel of c-1 have equal order.
    fixed = sum(min(units_orbit(m,a,-b)) == (a,b) for a,b in classes)
    return len(classes),fixed


def factorization(n):
    p = 2
    factors = Counter()
    while p*p <= n:
        while n%p == 0:
            factors[p] += 1
            n //= p
        p += 1
    if n > 1:
        factors[n] += 1
    return factors


def character_count(m):
    result = 1
    for p,k in factorization(m).items():
        result *= p**(k-1)*(p-1)
    return result


def primitive(m):
    result = 1
    for p,k in factorization(m).items():
        result *= p-2 if k==1 else p**(k-2)*(p-1)**2
    return result


def check(last):
    complete = []
    examples = {}
    for m in range(1,last+1):
        classes, fixed = actual_counts(m)
        phi = character_count(m)
        d = 4*(2*m)//gcd(4,2*m)
        assert fixed == phi == character_count(d)//2
        assert sum(primitive(h) for h in range(1,m+1) if m%h==0) == fixed
        if m>=3:
            numerator = 1
            for p,k in factorization(m).items():
                eps = 0 if p==2 else (1 if p%4==1 else -1)
                numerator *= p**(k-1)*(p-eps)
            assert 4*classes == fixed*numerator
        if classes==fixed:
            complete.append(m)
        if m<=12:
            examples[m] = {"all_ray_characters":classes,"invariant":fixed,"cyclotomic_modulus":d}
    assert complete == [1,2,3,4,5]
    return dict(last_modulus=last,all_characters_invariant=complete,examples=examples)


if __name__ == "__main__":
    print(json.dumps(check(100), indent=2))
