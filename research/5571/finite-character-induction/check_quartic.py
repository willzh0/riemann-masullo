"""Exact checks for the quartic 3-division field and its two quadratic Borel characters."""
from collections import Counter
from itertools import product
import json

from sympy import Poly, Rational, ZZ, discriminant, resultant, symbols

x = symbols("x")
division = Poly(3*x**4-6*x**2+12*x-1, x, domain=ZZ)
radicand = Poly(x**3-x+1, x, domain=ZZ)
lines = ((1, 0), (0, 1), (1, 1), (1, 2))
ident = (1, 0, 0, 1)


def mm(g, h):
    a,b,c,d = g
    e,f,j,k = h
    return ((a*e+b*j)%3,(a*f+b*k)%3,(c*e+d*j)%3,(c*f+d*k)%3)


def det(g):
    a,b,c,d = g
    return (a*d-b*c)%3


def inv(g):
    a,b,c,d = g
    v = det(g)
    return (d*v%3,-b*v%3,-c*v%3,a*v%3)


def act(g, v):
    a,b,c,d = g
    e,f = v
    return ((a*e+b*f)%3,(c*e+d*f)%3)


def normalize(v):
    a,b = v
    divisor = a or b
    return (a*divisor%3,b*divisor%3)


def eigenvalue(g, v):
    w = act(g, v)
    assert normalize(w) == v
    return w[0] if v[0] else w[1]


def sign(a):
    assert a in (1, 2)
    return 1 if a == 1 else -1


def euler(g):
    used = set()
    den = [[1],[1]]
    for v in lines:
        if v in used:
            continue
        w = v
        power = ident
        length = 0
        while w not in used:
            used.add(w)
            w = normalize(act(g,w))
            power = mm(g,power)
            length += 1
        assert w == v
        a = eigenvalue(power,v)
        for i, value in enumerate((a,det(power)*a%3)):
            old = den[i]
            out = old+[0]*length
            for k,c in enumerate(old):
                out[k+length] -= sign(value)*c
            den[i] = out
    return tuple(den[0]),tuple(den[1])


def mod_shape(prime):
    f=Poly(division.as_expr(),x,modulus=prime)
    _, factors=f.factor_list()
    assert all(mult==1 for _,mult in factors)
    return sorted(int(v.degree()) for v,mult in factors)


def v_p(n,p):
    if n == 0:
        return None
    n=abs(int(n))
    value=0
    while n % p == 0:
        n//=p
        value+=1
    return value


def legendre(n,p):
    val=pow(int(n)%p,(p-1)//2,p)
    return -1 if val==p-1 else val


def main():
    G = {g for g in product(range(3),repeat=4) if det(g)}
    H = {g for g in G if g[2]==0}
    A = {g for g in H if g[0]==1}
    B = {g for g in H if g[3]==1}
    assert (len(G),len(H),len(A),len(B))==(48,12,6,6)
    def conjugate(g,S):
        return {mm(mm(g,h),inv(g)) for h in S}
    assert {g for g in G if conjugate(g,H)==H}==H
    assert not any(conjugate(g,A)==B for g in G)
    assert all(any(conjugate(g,S).isdisjoint({h}) for g in G)
               for S in (A,B) for h in G-{ident})
    sample = Counter()
    for g in G:
        a,b=euler(g)
        assert a==b
        sample[a]+=1
    shapes={p:mod_shape(p) for p in (5,7,19,41)}
    assert shapes[5]==[4] and shapes[7]==[1,3] and shapes[19]==[1,1,1,1]
    assert all(mm(mm(g,g),mm(g,g))==(2,0,0,2) for g in G
               if len({normalize(act(g,v)) for v in lines})==4
               and not any(normalize(act(mm(g,g),v))==v for v in lines))
    assert division.eval(24)%41==0 and radicand.eval(24)%41==25 and (-3*25)%41==7
    assert (legendre(25,41),legendre(7,41))==(1,-1)
    assert int(resultant(division.as_expr(),radicand.as_expr(),x))==-23**2
    assert int(discriminant(division.as_expr(),x))==-27*368**2
    assert [int(v) for v in reversed(division.shift(1).all_coeffs())]==[8,12,12,12,3]
    reversed_polynomial=Poly(x**4-12*x**3+6*x**2-3,x,domain=ZZ)
    assert all(c%3==0 for c in reversed_polynomial.all_coeffs()[1:]) and reversed_polynomial.TC()%9
    assert v_p(division.eval(13),23)==1 and v_p(division.eval(7),23)>=1
    bad23=Poly(3*(x-7)*(x-13)**3,x,modulus=23)
    assert bad23==Poly(division.as_expr(),x,modulus=23)
    assert legendre(radicand.eval(7),23)==-1 and legendre(39,23)==1
    assert [int(v) for v in reversed(radicand.shift(13).all_coeffs())]==[2185,506,39,1]
    assert Rational(-6912,23).q==23
    print(json.dumps({
        "division_polynomial":str(division.as_expr()),"D":str(radicand.as_expr()),
        "division_discriminant":int(discriminant(division.as_expr(),x)),
        "resultant_with_D":int(resultant(division.as_expr(),radicand.as_expr(),x)),
        "factor_degrees":shapes,"group_order":len(G),"borel_order":len(H),
        "normalizer_order":len(H),"quadratic_kernels_conjugate":False,
        "distinct_verified_rational_Euler_polynomials":len(sample),
        "Euler_histogram_constant_term_first":[[list(k),v] for k,v in sorted(sample.items())],
        "prime_41":{"x_mod_41":24,"D_mod_41":25,"minus_3D_mod_41":7,"signs":[1,-1]},
        "local_input":{"p2_shift_coefficients":[8,12,12,12,3],
                       "p3_reciprocal":"Y^4-12Y^3+6Y^2-3","p23_residue_roots":[7,13],
                       "p23_D_at_13_shift":[2185,506,39,1]}
    },indent=2))


if __name__=="__main__":
    main()
