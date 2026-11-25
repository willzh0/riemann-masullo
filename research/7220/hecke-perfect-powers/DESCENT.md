# A reduction for every unitary Hecke character by cyclic descent

For a number field $P$ write $m_P(\nu,z)$ for the positive zero multiplicity of the project's completed Hecke continuation of a continuous unitary idèle-class character $\nu$. Set it to zero at an ordinary nonzero point. Every positive zero lies in $0<\Re z<1$, including after imaginary norm twists. A norm-one character has precisely the one-parameter family of extensions obtained by twisting any representative by $|\cdot|^{it}$. This moves zeros vertically with multiplicity. Hence a uniform order bound in the language of the chosen basepoints of #7220 is the same bound on $m_P(\nu,z)$ for all unitary $\nu$ and all $z$ in the open strip. [Library zero confinement](https://github.com/mccorvie/riemann-masullo/blob/9c791d74a81f1191d900e6d96f1270acee9b033e/RiemannMasullo/Ch03_IdelicZeta/Sec2.lean#L5634) · [Issue report on basepoint changes](https://github.com/mccorvie/riemann-masullo/issues/7220#issuecomment-7125493621)

Let $\mathcal E(F)$ consist of $F$ and the subfields $E\subset F$ reachable by a tower of cyclic extensions of prime degrees from $F$ down to $E$. There are finitely many, since a normal closure of $F/\mathbb Q$ has a finite Galois group. Define $A(E)$ to be the supremum of $m_E(\nu,z)$ for characters with trivial stabilizer in $\operatorname{Aut}_{\mathbb Q}(E)$, taking zero for an empty supremum. Write $M(F)$ for the corresponding supremum over all unitary characters. Suprema are in the extended nonnegative reals. Then
$$
 \max_{E\in\mathcal E(F)} A(E)
 \ \le\ M(F)\ \le\
 \max_{E\in\mathcal E(F)} [F:E]\,A(E).
$$
In particular the original assertion over every number field is equivalent to the assertion over every field restricted to characters with trivial automorphism stabilizer. On a fixed field one needs the indicated bounds on the reachable subfields. When $F/\mathbb Q$ is abelian all subfields are reachable.

### The cyclic step, including infinite order and ramification

Suppose $P/E$ is cyclic with generator $\sigma$ and group $C$. The idèle norm on classes has kernel
$$
 \ker(N:C_P\longrightarrow C_E)=(\sigma-1)C_P.
$$
One proof uses $C_P^C=C_E$ (Hilbert 90 on $P^\times$) and $\widehat H^{-1}(C,C_P)=0$, the cyclic instance of the first class-field cohomology theorem. Equivalently, if the norm of an idèle is principal, its generating element is a local norm everywhere, hence a global norm by the cyclic Hasse norm theorem. Divide out by that principal norm and use cyclic Hilbert 90 on idèles. The local preimages can be chosen to be units outside finitely many primes. Global reciprocity identifies the open finite-index quotient $C_E/N(C_P)$ with $C$. [Milne, *Class Field Theory*, VII, Theorem 5.1 and the proof of VIII, Theorem 3.1](https://www.jmilne.org/math/CourseNotes/CFT.pdf#page=243) · [Global reciprocity](https://www.jmilne.org/math/CourseNotes/CFT.pdf#page=220)

If $\lambda$ is $\sigma$-invariant, it kills this kernel. The norm map is open onto its image by the open mapping theorem for locally compact groups with $\sigma$-compact domain. The induced continuous character on $N(C_P)$ extends to a unitary character $\nu$ on $C_E$: extend algebraically to the finitely many cosets using roots in the circle, and continuity follows on the open subgroup. Exactly $|C|$ such extensions occur, namely $\nu\kappa$ as $\kappa$ runs over $\widehat C$ via reciprocity. Thus $\lambda=\nu\circ N_{P/E}$. No finiteness assumption on the image of $\lambda$ is used.

For every continuous unitary $\nu$ on $C_E$ the ordinary **primitive** Hecke functions satisfy
$$
 L_P(s,\nu\circ N_{P/E})=\prod_{\kappa\in\widehat C} L_E(s,\nu\kappa).
$$
Here is the local verification, which also handles a twist ramified at the same prime as the extension. Fix a finite $v$ of $E$. Write $I\subset D\subset C$ for inertia and decomposition, $e=|I|$, $f=|D/I|$ and $g=|C|/(ef)$. The $g$ primes upstairs have the same factor. If $\nu$ is nontrivial on norms of local units upstairs, the left side at $v$ is one and each twist on the right is ramified. Otherwise $\nu$ on units factors through $I$ by local reciprocity. Choose $\kappa_0\in\widehat C$ clearing that restriction; characters of a subgroup of a finite abelian group extend. The unramified twists are exactly $\nu\kappa_0\kappa'$ with $\kappa'$ trivial on $I$. If $\pi_v$ is a uniformizer and $a=(\nu\kappa_0)(\pi_v)$, their values at $\pi_v$ are $a$ times the $f$th roots of unity, each $g$ times. This follows by evaluating the characters of $C/I$ at the uniformizer class of order $f$. Also $a^f=(\nu\circ N)(\pi_w)$ because $N\pi_w$ has $v$-valuation $f$ and $\kappa_0$ kills norms. Thus both local inverse Euler factors are $(1-a^f(Nv)^{-fs})^g$. The argument uses one consistent character convention; changing arithmetic to geometric Frobenius inverts all the corresponding values. [Tate, *Number theoretic background*, §§2.3–3.3 and 3.5, pp. 12–17](https://ncatlab.org/nlab/files/TateNumberTheory.pdf#page=12) · [Artin's induction identity, formula (18)](https://doi.org/10.1007/BF02941010)

Continuation gives the following exact identity at each $z$ in the open strip:
$$
 m_P(\nu\circ N,z)=\sum_{\kappa\in\widehat C}m_E(\nu\kappa,z).
$$
All the summands are nonnegative. The project's gamma factors are regular and nonzero there, so its choice of a factor of $1/2$ at each complex place has no effect on these orders. More precisely, the project's product of completed lower functions differs from the upper function by a constant: the upper equals $2^{[P:E]r_2(E)-r_2(P)}$ times the lower product. Here a complex archimedean factor in the project is half the standard $\Gamma_{\mathbb C}$, and this completion omits the standard conductor exponential. The conductor-discriminant formula cancels those exponentials in induction. Absolute values of norms satisfy $|Nx|_E=|x|_P$.

### Iteration and its converse

If a unitary character on $P$ has nontrivial stabilizer, that finite group contains an element of prime order. Its fixed field $E$ gives a cyclic prime-degree extension $P/E$. Descend the character as above and replace its divisor by the sum of the $[P:E]$ genuine divisors on $E$. Repeat separately on the resulting rows. The field degree decreases at every replacement, so the process stops with a finite list of characters whose stabilizers are trivial in their own fields. Repetitions count. At every zero argument $z$ this is an equality of zero orders. The sum over all leaves of their absolute field degrees stays equal to $[F:\mathbb Q]$. Hence the order upstairs is bounded by
$$
 \sum_{\rm leaves} A(E)\ \le\
 \max_{E\in\mathcal E(F)} [F:E]A(E).
$$
Conversely a character on any reachable $E$ can be pulled up the tower by norms. At each step its original divisor occurs as one of the nonnegative summands. Therefore its order at any site is bounded by the order of the final character on $F$, whence $A(E)\le M(F)$. The same argument gives $M(E)\le M(F)$ for all those $E$.

Checking stabilizers only on norm-one classes gives the same result. If a field automorphism $a$ satisfies $\lambda^a=\lambda|\cdot|^{it}$, then $a$ preserves the norm. Raising the action to its finite order forces $t=0$. This matters because the statement in the repository allows each norm-one component to choose its own representative.

The factor $[F:E]$ can be attained in the divisor equality. In the [degree-nine example](NONIC.md) $[F:E]=3$ and each positive order downstairs is exactly tripled. More generally, for any $n\ge2$, choose a prime $\ell\nmid n$, let $E=\mathbb Q(\zeta_{n^2})$, and take $L=E(\ell^{1/n^2})$ and $F=E(\ell^{1/n})$. Eisenstein over $E$ gives $\operatorname{Gal}(L/E)=C_{n^2}$. For a faithful character $\theta$ of this group, the $n$ factors descending $\theta\circ N_{F/E}$ are $\theta^{1+jn}$ for $0\le j<n$. Each $1+jn$ is a unit modulo $n^2$ and comes from a cyclotomic automorphism of $E$ extending to $L$ while fixing the real radical. These factors therefore have identical primitive Hecke functions. The character $\theta$ itself has trivial rational stabilizer on $E$. This is sharpness of the divisor coefficient. It does not assert equality between supremum bounds for complete fields.

The remaining analytic task is a genuine multiplicity bound for the characters with trivial stabilizer. Even over $\mathbb Q$ that includes a height-independent multiplicity bound for the zeros of $\zeta$. No such bound is assumed in the reduction.
