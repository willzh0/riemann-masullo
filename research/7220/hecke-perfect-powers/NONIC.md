# An explicit cubic root over the nonic field of conductor 333

Let $E=\mathbb Q(u)$ with $u^3-3u+1=0$, the real cyclic cubic field of conductor 9. Let $E_{37}$ be the cyclic cubic field of conductor 37, with polynomial $X^3-4X^2-7X-1$. Put $F=EE_{37}$, the degree-nine real abelian field whose two generating characters have these conductors. The conductor of $F$ is $333$ and its field discriminant is $333^6$ by the conductor-discriminant formula.

## The degree-27 normal closure

Breen, Varma and Voight identify the splitting field $L$ of the following polynomial as a Galois extension of degree 27 with nonabelian group of exponent three:
$$
 f(X)=X^9-3X^8-21X^7+63X^6+141X^5-435X^4-273X^3+996X^2-192X-64.
$$
They give $3^{16}37^4$ for the discriminant of the nonnormal degree-nine root field $K_0$. The group $G$ is the order-27 Heisenberg group. Its commutator subgroup is its cyclic center $Z$. The exponent-three abelian extension $L^Z$ is unramified at finite primes outside 3 and 37. By the cyclotomic description of abelian extensions of $\mathbb Q$, the maximal such abelian extension of exponent three is $EE_{37}$: cubic Dirichlet characters at 3 have conductor dividing 9, and those at 37 have conductor dividing 37. Both fields have degree nine, proving $F=L^Z$. All these fields are totally real since the Galois group has odd order. [Breen–Varma–Voight, *On unit signatures and narrow class groups of odd degree abelian number fields*, Remark 5.4.9](https://jvoight.github.io/articles/clyclic-100921.pdf#page=23) · [Number-field record for $K_0$](https://www.lmfdb.org/NumberField/9.9.80676485676081.1)

The stabilizer $X$ of a root of $f$ is noncentral of order three. Let $P=ZX$, an abelian group of order nine. Its fixed field is cyclic cubic and lies in $K_0$. The cube of its discriminant must divide $d_{K_0}$, so it cannot ramify at 37: a cyclic cubic ramified there already has $37^2$ in its discriminant. Thus $L^P=E$. In particular $K_0/E$ is cyclic cubic. An explicit defining polynomial is
$$
 g(T)=T^3-(1+u)T^2-(7+u)T+4u^2+8u .
$$
Its norm to $\mathbb Q$ is $f(T)$, and its discriminant is $(23u^2+4u-49)^2$ in $E$. [Exact polynomial checks](check_nonic.py)

Take a nontrivial cubic class-field character $\mu$ of $K_0/E$, inflated from $P/X$ to $P$. Its restriction to $Z$ is faithful and defines a cubic Hecke character $\lambda$ of $L/F$. The [induction calculation](POWERS.md) gives $\operatorname{Ind}_Z^G\lambda=3\operatorname{Ind}_P^G\mu$, with an irreducible degree-three representation on the right before multiplication. For every primitive Dirichlet $\xi$,
$$
 L_F(s,\lambda\cdot(\xi\circ N_{F/\mathbb Q}))
    = L_E(s,\mu\cdot(\xi\circ N_{E/\mathbb Q}))^3 .
$$
Both functions have standard completed versions satisfying the same identity. In the project's normalization the two fields are totally real, so the same equality holds there, too, as meromorphic functions in normal form away from polar conventions and, in particular, on the entire open strip. Every zero of every one of these upper characters has multiplicity three times its actual lower multiplicity. Passing to the complex conjugates gives the second family.

## Untwisted local arithmetic

The finite conductor of $\mu$ has norm $3^2 37^2=12321$, since $K_0/E$ is cyclic cubic and $d_{K_0}=d_E^3 N(\mathfrak f_\mu)^2$. The rational Artin conductor of $\operatorname{Ind}_P^G\mu$ is $d_E N(\mathfrak f_\mu)=998001$. By the same induction formula for $\lambda$ the third power of that integer is $d_F N(\mathfrak f_\lambda)$. This gives $N(\mathfrak f_\lambda)=3^6=729$. There is a unique prime of $F$ above 3, of ramification index and residue degree both three. Indeed $3^{12}=10\bmod37$ shows that 3 is inert in the conductor-37 cubic. The relative conductor of $\lambda$ is the square of this unique prime, and its Euler factor there is one.

At 37, $E$ splits with residues $u=5,9,23$. The relative cubic $g$ is irreducible at $u=5$ and has one triple root at each other prime. The latter two primes are ramified, as the verified index of the integer generator of $K_0$ is prime to 37. Orient $\mu$ by assigning $\omega=e^{2\pi i/3}$ to the arithmetic Frobenius at the inert prime $(37,u-5)$. The rational Euler factor of the lower function is $(1-\omega T)^{-1}$ at $T=37^{-s}$, and the upper factor is its cube. For a good-prime comparison, at 73 the three lower primes all have the opposite Frobenius orientation, and the lower factor is $(1-\omega^2 T)^{-3}$ for $T=73^{-s}$. At 179 the normal closure splits completely. The verifier checks these comparisons, the two cubic discriminants and the nonic defining order's index $63424$. The published Galois group identification is an input. [Reproducible arithmetic](check_nonic.py)

## Which rows of the project this covers

There are exactly three classes of $A=\operatorname{Gal}(F/\mathbb Q)$-invariant continuous unitary characters modulo rational norm twists. They are the rational pullbacks themselves and the cosets of $\lambda$ and $\lambda^{-1}$. This follows from [cyclic descent and the order-three class calculation](BICYCLIC.md). It can also be checked directly in this instance: for any invariant row descend to a character $\nu$ on $E$. Its three possible descents are $\nu\kappa^a$, where $\kappa$ generates the characters of $F/E$. For a generator $\sigma$ of $\operatorname{Gal}(E/\mathbb Q)$, the ratio $\nu^\sigma/\nu$ equals $\kappa^j$. This $j$ is independent of the lift. If $j=0$ the row comes from $\mathbb Q$. The nonic gives the other two possibilities since the three conjugates of $\mu$ on $P$ are distinct. The same upper character admits a single Hecke cubic root over each of the four cyclic cubic subfields of $F$.

- **#7220.** Any proposed field bound $B_F$ satisfies $B_F\ge3$, and it would bound every root order in both twist families by $\lfloor B_F/3\rfloor$, independently of conductor and ordinate. The root Hecke functions have infinitely many zeros in the open strip.
- **#7453.** For any one twist, the bounded-height-representative hypothesis on its upper component forces the real parts of **all** its lower zeros in $1/2<\Re s<1$ into a finite set. Each lower zero, including a simple one, gives a multiple zero upstairs; a compact rectangle of representatives then contains only finitely many sites. The hypothesis allows the finite set to depend on the twist.
- **#7485.** Apply the finite-cover criterion to the fixed $F$. If the issue holds, there is a finite abscissa set $S$ and a finite exceptional set of norm-one components. Outside those components every right-half zero of both cubic-root twist families has its real part in $S$. Exactly nine primitive Dirichlet labels lie above each occupied component, since the kernel of rational norm pullback is $\widehat A$ and finite-order characters trivial on $C_F^1$ are trivial on $C_F$. The two conjugate families have disjoint components. Rational imaginary norm twists preserve the real parts. Thus $e$ exceptional components account for at most $9e$ labelled pairs across the two families together. Combining #7453 with #7485 absorbs the finitely many remaining labels into the abscissa set. Whether there are any right-half zeros is open. [Finite-cover proof](https://github.com/mccorvie/riemann-masullo/pull/7504) · [Earlier conductor-uniform cubic comparison](https://github.com/mccorvie/riemann-masullo/issues/7485#issuecomment-7148696977)

The $S_3$ example already on these issues gives an irreducible degree-two factor occurring twice in a product with other factors. In this degree-nine field the complete upper function is a cube, and the two cubic character classes above exhaust the Galois-invariant rows that do not descend to $\mathbb Q$.
