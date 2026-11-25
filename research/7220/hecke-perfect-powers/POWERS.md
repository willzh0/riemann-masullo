# The sharp structural multiplicity bound

Fix a number field $F$ and a finite-order primitive Hecke character $\lambda$ on its idèle classes. Choose a finite normal extension $L/\mathbb Q$ containing $F$ and the abelian field cut out by $\lambda$. Put $G=\operatorname{Gal}(L/\mathbb Q)$ and $H=\operatorname{Gal}(L/F)$. Use the reciprocity convention sending a character to its corresponding linear Galois character. Write $V=\operatorname{Ind}_H^G\lambda$. The integer
$$
 r(F)=\#(H\backslash G/H)
$$
depends just on $F$. It counts the orbits of the stabilizer of one embedding of $F$ on all the embeddings, and is unchanged on passing to a larger $L$.

## A bound independent of conductor

If an irreducible $\rho$ occurs in $V$ with multiplicity $m_\rho$, Frobenius reciprocity gives $m_\rho\le\dim\rho$. Mackey's formula gives the sharper collective bound
$$
 \sum_\rho m_\rho^2=\langle V,V\rangle
 =\sum_{HgH}\dim\operatorname{Hom}_{H\cap gHg^{-1}}
          (\lambda,\lambda^g)\ \le\ r(F)\ \le [F:\mathbb Q].
$$
Indeed each Hom space between linear characters has dimension zero or one. This holds simultaneously for every finite conductor of $\lambda$. For example, if the embedding action is doubly transitive, $r(F)=2$ and each constituent occurs at most once. The same multiplicity-free conclusion holds for rank three. The arithmetic order at a site can also reflect repeated zeros within a factor or simultaneous zeros of different factors. The inequality bounds the representation multiplicities in the Artin factorization. It gives no unconditional uniform upper bound on analytic zero orders. [Artin formalism](https://doi.org/10.1007/BF02941010)

Suppose the **full zero divisor** of $\lambda$ equals $n$ times the full divisor of one finite-order primitive Hecke character $\mu$ over some number field $E$, for $n\ge2$. It suffices that this hold above some fixed absolute height. Put $V_\mu=\operatorname{Ind}_{\operatorname{Gal}(L/E)}^G\mu$ in a larger common normal field if necessary. The logarithmic-derivative and Chebotarev argument for the finite-order divisor criterion gives $V=nV_\mu$ as characters. That argument works unchanged with different base fields: the gamma exponents, conductor constants and principal pole flags were already allowed to vary. Conversely $V=nV_\mu$ gives the stated identity at every interior point by induction. Equality of the ordinary Hecke functions as the $n$th power also suffices. [Proof of the full-divisor criterion, including finite exceptions](https://github.com/willzh0/riemann-masullo/blob/a9c5d2d0721ba771c96be60b79253cd5eb716013/research/5571/finite-character-induction/DIVISORS.md)

A constituent of $V_\mu$ must then occur at least $n$ times in $V$. Consequently
$$
 n^2\ \le\ r(F)\ \le\ [F:\mathbb Q].
$$
If $[F:\mathbb Q]=n^2$ then $r(F)=[G:H]$, so every coset is its own $H$-orbit, $H$ is normal and $F/\mathbb Q$ is Galois. Also $V_\mu$ must be a single irreducible character of dimension $n$, since $\sum m_\rho^2=n^2$ and $V$ has dimension $n^2$. In this case $\rho|_H$ consists of $n$ copies of $\lambda$, and character orthogonality forces $\operatorname{tr}\rho=0$ off $H$. If the irreducible root is itself $\operatorname{Ind}_{H'}^G\mu$, every $h\in H$ acts by a scalar on that representation and therefore fixes all cosets of $H'$. Hence $H$ is contained in the core of $H'$, $E\subset F$, and $\mu|_H=\lambda$. In field language $\lambda=\mu\circ N_{F/E}$. Thus an actual Hecke root at the degree minimum descends to a subfield. The hypothesis about the second Hecke divisor is substantive: numerical divisibility of the zero orders by $n$ alone is a different condition.

## Attainment over $\mathbb Q$ for every $n$

Let $G$ be the finite group of triples $(x,y,z)$ modulo $n$ with product
$$
 (x,y,z)(x',y',z')=(x+x',y+y',z+z'+xy').
$$
Its center is $Z=\{(0,0,z)\}$, and $P=\{(0,y,z)\}$ is abelian and normal. Let $\zeta=e^{2\pi i/n}$, $\lambda(0,0,z)=\zeta^z$, and $\mu(0,y,z)=\zeta^z$. The $n$ extensions of $\lambda$ to $P$ are exactly the conjugates of $\mu$ by the elements $(x,0,0)$. Their distinctness holds also for composite $n$ since the central character is faithful. Hence $\rho=\operatorname{Ind}_P^G\mu$ is irreducible of dimension $n$, by Frobenius reciprocity and its restriction to the normal subgroup $P$. Transitivity of induction gives
$$
 \operatorname{Ind}_Z^G\lambda=n\rho.
$$
Equivalently the trace of $\rho$ is $n\zeta^z$ on the center and zero otherwise. Exact enumeration checks these formulas also at composite orders. [Finite group verifier](check_heisenberg.py)

This is a nilpotent group and thus solvable. Shafarevich's theorem realizes $G$ as $\operatorname{Gal}(L/\mathbb Q)$ for a number field $L$. Take $F=L^Z$ and $E=L^P$. Their degrees are $n^2$ and $n$. Class field theory identifies $\lambda$ and $\mu$ with finite-order primitive Hecke characters over $F$ and $E$. For every rational Dirichlet character $\xi$, tensor the representation identity by $\xi$ in a common normal extension. Artin induction, including the invariant subspaces at ramified primes, gives
$$
 L_F(s,\lambda\cdot(\xi\circ N_{F/\mathbb Q}))
       = L_E(s,\mu\cdot(\xi\circ N_{E/\mathbb Q}))^n .
$$
The induced lower representation remains irreducible of dimension $n>1$, so neither of the displayed Hecke characters can be trivial: a trivial inducing character would give a rational trivial constituent. Both are entire in the standard completed convention. The equality also holds for the standard completions by conductor and local gamma induction. Across different fields the project's completion can introduce a nonzero constant. In every convention the same multiplicity identity holds in the open strip. [Schmidt–Wingberg, *Šafarevič's theorem on solvable groups as Galois groups*](https://arxiv.org/abs/math/9809211) · [Artin, induction identity (18)](https://doi.org/10.1007/BF02941010)

The lower function has infinitely many interior zeros. For example, one can use the Hecke zero count for a class character, or note that a pole-cleared entire function of order at most one with finitely many zeros is a polynomial times an exponential of a linear polynomial. Its gamma factors give an $s\log s$ term in its growth on the positive real axis, whereas its ordinary $L(s)$ tends to one. This rules out finitely many zeros; each compact substrip rectangle has only finitely many. Thus a uniform bound at this particular $F$, if it exists, must be at least $n$. Varying $n$ varies $F$. The bound in #7220 may depend on $F$. Related classical results give infinitely many multiple zeros for Dedekind zeta functions of nonabelian extensions. The identity here accounts for every zero of one individual Hecke character. [Hu–Kaneko–Martin–Schildkraut, Theorems 1.1–1.2](https://arxiv.org/abs/2107.03269)

The [fixed abelian field calculation](ABELIAN.md) also attains this bound on every field with Galois group $C_n^2$, by a class-field argument on that prescribed field. For $n=2$, the dihedral splitting field $\mathbb Q(i,\sqrt[4]{2})$ gives $F=\mathbb Q(i,\sqrt2)$ and a pure square. For $n=3$ the [nonic example](NONIC.md) gives a specific field, ray characters and ramified factors. A second explicit construction at every $n$ (without the optimal-degree assertion) appears at the end of the [cyclic descent proof](DESCENT.md).
