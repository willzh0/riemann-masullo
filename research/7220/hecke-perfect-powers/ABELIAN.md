# The exact representation multiplicity on a fixed abelian field

Let $F/\mathbb Q$ be abelian, $A=\operatorname{Gal}(F/\mathbb Q)$, and write $A=C_{d_1}\times\cdots\times C_{d_r}$ in invariant factors, $d_1\mid\cdots\mid d_r$. Set
$$
 D(A)=d_{r-1}d_{r-3}d_{r-5}\cdots
$$
with empty product one. This is the exact largest multiplicity of any irreducible constituent of any finite-order Hecke character of $F$ induced to $\mathbb Q$. Every such constituent multiplicity **divides** $D(A)$. There is an invariant finite-order character on this specific $F$ with every nontrivial zero order divisible by $D(A)$. In particular a fixed-field bound in #7220 is at least $D(A)$. The number measures representation-theoretic repetition; it does not bound analytic multiplicity.

## Calculation for one character

Work in a finite Galois extension $L/\mathbb Q$ through which the character $\lambda$ and all its conjugates factor. Let $H=\operatorname{Gal}(L/F)$, $G=\operatorname{Gal}(L/\mathbb Q)$ and let $I\subset A$ stabilize $\lambda$. In the preimage of $I$, the kernel of $\lambda$ is normal, and $H/\ker\lambda$ is central. Define
$$
 b(i,j)=\lambda([\tilde i,\tilde j]) \qquad (i,j\in I),
$$
where tildes denote lifts. This is a well-defined alternating bicharacter. Let $R$ be its radical. The finite abelian group $I/R$ has a nondegenerate alternating pairing. It is a product of pairs of cyclic groups of equal order: in each primary part take a maximal-order element, pair it with an element giving a root of unity of that full order, then take the orthogonal complement of this nondegenerate pair and iterate. In particular there is a subgroup $P$ between $R$ and $I$ with $P=P^\perp$, where perpendicular is in $I$, and
$$
 [I:P]=[P:R]=h=\sqrt{|I/R|}.
$$

Let $\widetilde P$ be the preimage of $P$ in $G$. Modulo $\ker\lambda$ it is abelian, so $\lambda$ extends to it, with $|P|$ extensions. Conjugation by $I$ acts on these extensions through the pairing; the stabilizer of each is precisely $P$ in $I$. No element outside $I$ can stabilize one or carry it to another extension of $\lambda$, by restriction to $H$. Since $\widetilde P$ is normal in $G$, inducing an extension to $G$ gives an irreducible representation (use the restriction to $\widetilde P$ and Frobenius reciprocity). Distinct extensions give the same irreducible exactly within an orbit of $I/P$. Induction in stages from $H$ now gives exactly $|R|$ distinct irreducibles, **each with multiplicity $h$** and degree $[A:I]h$.

For $K=F^P$, choose one Hecke character $\theta_j$ on $K$ from each of these $|R|$ orbits. Artin induction gives the actual identity
$$
 L_F(s,\lambda)=\left(\prod_{j=1}^{|R|} L_K(s,\theta_j)\right)^h .
$$
Every $\theta_j$ has trivial stabilizer on the abelian field $K$. All lower factors are ordinary Hecke functions, holomorphic on the open strip. This gives the same equality of zero orders and requires no holomorphy conjecture for general Artin representations. The underlying irreducible representation of the group above the stabilizer is the classical Heisenberg representation attached to an alternating character. [Zink, *Ramification in Local Galois Groups — the Second Central Step*, §1, Proposition 1.1](https://doi.org/10.4310/PAMQ.2009.v5.n1.a9)

## Upper bound and attainment on the prescribed field

For each prime $p$, the descending list of elementary-divisor exponents of the subquotient $I/R$ is coordinatewise at most the corresponding list for $A$. For a subgroup, the number of exponents at least $k$ is the dimension of $p^{k-1}(I[p^k])$ in the primary part, and this vector space embeds in the one for $A$. For a quotient, use the surjection on $p^{k-1}I/p^k I$. Since the exponents for $I/R$ occur in equal adjacent pairs, $v_p(h)$ is at most the sum of the second, fourth and subsequent even-position exponents of $A$ in descending order. This holds prime by prime, so $h\mid D(A)$.

To see that $D(A)$ occurs, pair adjacent cyclic factors of $A$ starting from the largest. On $C_s\times C_t$, $s\mid t$, use the determinant pairing $\exp(2\pi i(xy'-yx')/s)$, reducing the larger coordinate modulo $s$. Its nondegenerate quotient is $C_s^2$. Leave the last unpaired cyclic factor, if any, in the radical. The resulting pairing has $h=D(A)$.

This pairing is realized by an invariant finite-order Hecke character of $F$. Use the five-term inflation–restriction exact sequence for $1\to G_F\to G_{\mathbb Q}\to A\to1$ with trivial discrete coefficients $\mathbb Q/\mathbb Z$. Transgression maps $\operatorname{Hom}_{\mathrm{cont}}(G_F,\mathbb Q/\mathbb Z)^A$ onto $H^2(A,\mathbb Q/\mathbb Z)$ because $H^2(G_{\mathbb Q},\mathbb Q/\mathbb Z)=0$ by Tate. Since the coefficient group is divisible, $H^2(A,\mathbb Q/\mathbb Z)$ is the dual of $\bigwedge^2 A$. Its alternating pairing is evaluation on lift commutators up to a uniform sign. Choose a preimage of the prescribed class, changing its sign if necessary. This is a continuous character from a compact profinite group to a discrete group, hence has finite image. Global reciprocity supplies the desired finite-order Hecke character. Its full stabilizer is $I=A$, and the factorization above proves divisibility at every interior zero. [Calegari–Mazur, proof of Theorem 5.4, p. 136](https://www.math.uchicago.edu/~fcale/papers/ordinary.pdf#page=38) · [Milne, *Arithmetic Duality Theorems*, Corollary I.4.17](https://www.jmilne.org/math/Books/ADTnot.pdf#page=71)

For cyclic $F/\mathbb Q$, $D(A)=1$, so every finite-order induction is multiplicity-free. For $A=(C_p)^r$ it is $p^{\lfloor r/2\rfloor}$, and for $A=C_n^2$ it is $n$. The [bicyclic proof](BICYCLIC.md) describes exactly which invariant characters are related by rational norm twists and, in the maximal case, produces a single lower Hecke root over every cyclic direct-factor fixed field.

## The single-character bounded-height question

The same factorization gives an exact test for the #7453 assertion on every finite-order row over an abelian base. Fix $\lambda$, with the calculated $h$, and its finitely many lower characters $\theta_j$. In the open right half-strip a site is a multiple zero upstairs precisely as follows.

- If $h>1$, it is a zero of at least one lower factor. Every simple lower zero already contributes a multiple upper zero.
- If $h=1$, either one of the lower factors has a multiple zero there or two distinct lower factors both vanish there.

Thus, for $h>1$, a bounded-height representative for each upper multiple-zero line exists if and only if the real parts of **all** right-half zeros of the lower factors form a finite set. For $h=1$, the equivalent condition is finiteness of the abscissae of their multiple zeros together with those of their pairwise common zeros. Indeed bounded-height representatives live in a compact rectangle containing finitely many zeros of the fixed upper function. Conversely finitely many lines admit finitely many representatives. Imaginary norm twists translate the pictured sites without changing their abscissae. This separates the arithmetic remaining for a single row from the uniform assertion across components on #7485. [Precise issue #7453](https://github.com/mccorvie/riemann-masullo/issues/7453)
