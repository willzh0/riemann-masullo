# Uniform zero multiplicities and cyclic descent

Masullo, Proposition 10.2.2.2, pp. 446–447 (erratum I277). The project asks whether on each fixed number field $F$ one integer bounds the orders of every zero of every unitary Hecke character, at every height and conductor. There are two partial results. [Issue #7220 and the library statement](https://github.com/mccorvie/riemann-masullo/issues/7220)

1. **It suffices to bound characters with trivial stabilizer under field automorphisms.** This is an equivalence for the original assertion over all number fields, and has a fixed-field version involving only the finitely many subfields reachable by cyclic descent. It applies to infinite-order unitary characters and to all ramified primes. A cyclic norm transfer writes the full divisor of each descended character as a sum of lower-field divisors with their true multiplicities. [Reduction and proof](DESCENT.md)
2. **Every prescribed power occurs in the complete zero divisor of one finite-order Hecke character.** For every $n\ge2$ there is a field of degree $n^2$ and a character on it whose ordinary Hecke function is exactly the $n$th power of one primitive Hecke function of degree $n$. The identity persists under every rational Dirichlet twist. Degree $n^2$ is optimal even if one assumes just this equality of the two full divisors above some fixed absolute height. In general a constituent of a finite-order induced character on a fixed field occurs at most the square root of the number of double cosets in the field's embedding action. This controls structural repetition. Individual zero orders and coincidences between different factors can still be large. [Optimality, construction and degree bound](POWERS.md) · [Sharp value for every abelian field](ABELIAN.md)

On any prescribed abelian field with group $C_n\times C_n$, some finite-order character attains the $n$th power. More generally if the abelian Galois group has invariant factors $d_1\mid\cdots\mid d_r$, the maximum forced by representation multiplicity is exactly $d_{r-1}d_{r-3}\cdots$. A finite-order character on that very field attains it. [Classification of the bicyclic characters](BICYCLIC.md) · [General abelian proof](ABELIAN.md)

For $n=3$ there is an explicit optimal example. Take the compositum $F$ of the real cyclic cubic fields of conductors 9 and 37. On this degree-nine field there is a cubic character $\lambda$ with
$$
 L_F(s,\lambda\cdot(\xi\circ N_{F/\mathbb Q}))
   =L_E(s,\mu\cdot(\xi\circ N_{E/\mathbb Q}))^3,
 \qquad E=\mathbb Q(\zeta_9)^+,
$$
for every primitive Dirichlet character $\xi$. The cubic root has rational conductor $998001$ before twisting. Its Euler factors at 37 and 73 identify the character up to an explicitly fixed convention. The two conjugate choices of $\lambda$, together with the characters coming from $\mathbb Q$, exhaust every Galois-invariant unitary character on $F$ up to rational norm twists. On either of the two cubic families, a simple zero of the lower character already gives a triple zero upstairs. [The historical nonic, local factors and the three classes](NONIC.md) · [Arithmetic verifier](check_nonic.py)

The degree varies in the general construction. For each one of the fields the existence of a finite uniform bound remains open. Likewise the degree-nine calculation gives necessary consequences of the proposed finite abscissae in [#7453](https://github.com/mccorvie/riemann-masullo/issues/7453) and [#7485](https://github.com/mccorvie/riemann-masullo/issues/7485). It does not exhibit an off-critical zero. The earlier $S_3$ construction detects a degree-two factor with multiplicity two inside a product. [Earlier cubic construction](https://github.com/mccorvie/riemann-masullo/issues/7453#issuecomment-7146306492)

Run the arithmetic verifier with Python and SymPy. The other two scripts use only the Python standard library. They check the induction identities and the radicals of alternating pairings in representative small groups.

~~~sh
python check_nonic.py
python check_heisenberg.py
python check_pairings.py
~~~
