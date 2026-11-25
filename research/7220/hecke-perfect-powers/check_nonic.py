"""Replay the finite arithmetic of an optimal cubic power, using Python 3 and SymPy.

The input that the nonic has splitting group UT_3(F_3) is Breen, Varma and
Voight, Remark 5.4.9, https://jvoight.github.io/articles/clyclic-100921.pdf#page=23
(preprint https://arxiv.org/abs/1910.00449). The discriminants, modular
factorizations and cubic norm identity below are computed from the polynomials.
The interpretation of the conductors uses the conductor-discriminant formula
and Artin induction, as in https://math.stanford.edu/~conrad/JLseminar/refs/Knappintro.pdf .
Run with: python check_nonic.py
"""

from math import isqrt

from sympy import Poly, ZZ, discriminant, rem, resultant, symbols


x, u = symbols("x u")
f = x**9 - 3*x**8 - 21*x**7 + 63*x**6 + 141*x**5 - 435*x**4 - 273*x**3 + 996*x**2 - 192*x - 64
h9 = u**3 - 3*u + 1
h37 = u**3 - 4*u**2 - 7*u - 1
g = x**3 - (1 + u)*x**2 - (7 + u)*x + 4*u**2 + 8*u


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def factors_at(expr, variable, p):
    return Poly(expr, variable, modulus=p).factor_list()[1]


def pattern(factors):
    """List of pairs (irreducible factor degree, multiplicity)."""
    return sorted((factor.degree(), exponent) for factor, exponent in factors)


def check_index_prime_to(expr, variable, p):
    # Dedekind's index criterion. Here every repeated factor is linear. At
    # its root r the product of the lifted factors is 0, so test f(r)/p.
    for factor, exponent in factors_at(expr, variable, p):
        if exponent > 1:
            require(factor.degree() == 1, f"nonlinear repeated factor at {p}")
            root = -int(factor.nth(0)) % p
            require(int(expr.subs(variable, root)) % (p*p) != 0,
                    f"index criterion fails at {p}, residue {root}")


def check_discriminants():
    require(all(Poly(h, u).is_irreducible for h in (h9, h37)), "reducible cubic")
    shifted = Poly(f.subs(x, x + 1), x).all_coeffs()
    require(all(a % 3 == 0 for a in shifted[1:]) and shifted[-1] % 9 != 0,
            "nonic is not Eisenstein after the shift at 3")
    require(discriminant(h9, u) == 9**2 and discriminant(h37, u) == 37**2,
            "wrong cubic polynomial discriminant")
    check_index_prime_to(h9, u, 3)
    check_index_prime_to(h37, u, 37)
    poly_disc = int(discriminant(f, x))
    require(poly_disc == 2**12 * 3**16 * 37**4 * 991**2, "wrong nonic discriminant")
    check_index_prime_to(f, x, 3)
    check_index_prime_to(f, x, 37)

    # Use Hensel lifting to check that the remaining candidate primes are
    # unramified. At 2 the two simple irreducible cubics split over the
    # unramified cubic extension. The scaled polynomial gives three more
    # distinct roots there, all reducing to 0 before scaling.
    require(pattern(factors_at(f, x, 2)) == [(1, 3), (3, 1), (3, 1)], "bad mod-2 pattern")
    scaled = Poly(f.subs(x, 4*x), x, domain=ZZ).exquo_ground(64)
    require(pattern(factors_at(scaled.as_expr(), x, 2)) == [(3, 1)], "bad mod-2 lift")

    # At 991 the seven simple roots lift directly. The double root 12
    # has two distinct lifts in Q_991 after x = 12 + 991*t.
    factors = factors_at(f, x, 991)
    require(pattern(factors) == [(1, 1)] * 7 + [(1, 2)], "bad mod-991 pattern")
    require(Poly(x - 12, x, modulus=991) in [a for a, e in factors if e == 2],
            "wrong repeated root at 991")
    scaled = Poly(f.subs(x, 12 + 991*x), x, domain=ZZ).exquo_ground(991**2)
    require(pattern(factors_at(scaled.as_expr(), x, 991)) == [(1, 1)] * 2, "bad 991 lifts")
    field_disc = poly_disc // (2**12 * 991**2)
    require(field_disc == 80676485676081, "field discriminant disagrees with the published nonic")
    print(f"disc(E_9)=81, disc(E_37)=1369, disc(K_0)={field_disc}=3^16*37^4")
    print(f"disc(f)={poly_disc}, index [O_K0 : Z[root]]={2**6 * 991}")
    return field_disc


def check_cubic_extension():
    # K_0/E_9 is a cyclic cubic. An irreducible cubic has cyclic splitting
    # group when its discriminant is a square. Irreducibility follows already
    # at the prime (37, u-5) below. Norm(g)=f identifies the root field.
    require(resultant(h9, g, u).expand() == f, "incorrect norm of the relative cubic")
    square_root = 23*u**2 + 4*u - 49
    require(rem(discriminant(g, x) - square_root**2, h9, u) == 0, "bad relative discriminant")
    require(pattern(factors_at(f, x, 3)) == [(1, 9)], "unexpected behavior at 3")
    require(pow(3, 12, 37) == 10, "unexpected Frobenius of 3 in E_37")
    require([r for r in range(37) if h9.subs(u, r) % 37 == 0] == [5, 9, 23],
            "incorrect primes of E_9 above 37")
    for r, expected in ((5, [(3, 1)]), (9, [(1, 3)]), (23, [(1, 3)])):
        require(pattern(factors_at(g.subs(u, r), x, 37)) == expected, f"bad factor at u={r}")
    require(pattern(factors_at(f, x, 37)) == [(1, 3), (1, 3), (3, 1)], "wrong mod-37 behavior")
    print("K_0/E_9 above 37: (37,u-5) is inert; (37,u-9) and (37,u-23) are ramified.")
    print("Orient mu by arithmetic Frobenius at (37,u-5) = zeta_3.")
    print("Its induced Euler factor at 37 is 1/(1-zeta_3*T), with T=37^(-s).")


def frobenius_orientation(p, residue_u):
    # For any root t of g, the other roots r,s satisfy
    # g'(t)(r-s) = +/-sqrt(disc(g)). This compares their cyclic order across
    # residue fields, using the same global square root in E_9.
    cubic = Poly(g.subs(u, residue_u), x, modulus=p)
    require(cubic.is_irreducible, "orientation requires a prime inert in the cubic")
    t = Poly(x, x, modulus=p)
    other = t**p % cubic
    difference = cubic.diff() * (2*other + t + cubic.nth(2)) % cubic
    local_root = Poly(23*residue_u**2 + 4*residue_u - 49, x, modulus=p)
    require(difference == local_root or difference == -local_root, "invalid cyclic orientation")
    return 1 if difference == local_root else -1


def check_conductors(field_disc):
    # For the two conjugate cubic characters of K_0/E_9 the relative
    # discriminant is f_mu^2. For the bi-cubic field K the eight nontrivial
    # Dirichlet conductors are 9,9,37,37,333,333,333,333.
    norm_disc = field_disc // 81**3
    norm_mu = isqrt(norm_disc)
    require(field_disc == 81**3 * norm_mu**2, "non-square relative discriminant norm")
    conductor_rho = 81 * norm_mu
    disc_K = 9**2 * 37**2 * 333**4
    norm_lambda = conductor_rho**3 // disc_K
    require((norm_mu, conductor_rho, norm_lambda) == (12321, 998001, 729), "wrong conductors")
    require(conductor_rho**3 == disc_K * norm_lambda, "conductor identity fails")
    print(f"Norm(f_mu)={norm_mu}, Q_rho={conductor_rho}, Norm(f_lambda)={norm_lambda}")
    print("3^12 mod 37 = 10; K has one prime over 3, of e=f=3.")


def check_good_primes():
    # Splitting in K detects central Frobenius. Complete splitting in the
    # root field additionally detects identity because its action is faithful.
    samples = [(5, False, [3, 3, 3]), (17, False, [1, 1, 1, 3, 3]),
               (73, True, [3, 3, 3]), (179, True, [1] * 9)]
    for p, expected_split, expected_degrees in samples:
        split = p % 9 in (1, 8) and pow(p, 12, 37) == 1
        factors = factors_at(f, x, p)
        degrees = sorted(a.degree() for a, _ in factors)
        require(all(e == 1 for _, e in factors), f"ramified polynomial at sample {p}")
        require((split, degrees) == (expected_split, expected_degrees), f"bad sample at {p}")
        label = "noncentral"
        if split:
            label = "identity" if degrees == [1] * 9 else "nonidentity central"
        print(f"p={p}: splits in K={split}, nonic degrees={degrees}, Frobenius={label}")
    anchors = [r for r in range(73) if h9.subs(u, r) % 73 == 0]
    require(anchors == [39, 48, 59], "incorrect E_9 residues at 73")
    orientation_37 = frobenius_orientation(37, 5)
    require(all(frobenius_orientation(73, r) == -orientation_37 for r in anchors),
            "wrong central orientation at 73")
    print("Relative to the normalization at 37, L_73(rho,T)=1/(1-zeta_3^2*T)^3.")


if __name__ == "__main__":
    disc = check_discriminants()
    check_cubic_extension()
    check_conductors(disc)
    check_good_primes()
