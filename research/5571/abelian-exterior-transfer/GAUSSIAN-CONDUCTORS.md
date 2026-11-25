# The conjugation-invariant rows of the Gaussian field

Let $K=\mathbb Q(i)$, $c$ its nontrivial automorphism, and $\epsilon=\chi_{-4}$. For Masullo, Theorem 12.5.1.1, pp. 519–520, one normalized physical test has **absolute** omitted sum below $9.562\cdot10^{-113}$ on 2,463,841,722 distinct conjugation-invariant Hecke characters at once. The sum runs over all heights for **every** $\alpha>0$, including the two edges. The test selects exactly the characters whose two primitive rational lifts have conductor at most 400,000. It includes every conjugation-invariant normalized Gaussian character of true conductor norm at most $10^{10}$.

## Descent and the true conductor

Every normalized unitary $\Psi$ on $C_K$ invariant under $c$ is finite order. Indeed $x\,c(x)=\iota(Nx)$, so $\Psi^2=(\Psi\circ\iota)\circ N$, where $\iota:C_{\mathbb Q}\to C_K$ is diagonal. Any rational unitary character is a finite-order character times $|\cdot|^{it}$. On the chosen positive section of $K$, $\Psi=1$, $|N x|_{\mathbb Q}=|x|_K$, and the finite-order character kills the connected section. Thus $t=0$. Even if invariance is assumed only on the norm-one classes, the ratio $\Psi^c/\Psi$ is a norm power; conjugation both fixes and inverts this ratio. A norm character on the positive reals with square one is trivial.

Class field theory identifies $\Psi$ with an invariant finite character of the absolute Galois group $G_K$. Complex conjugation has order two in $G_\mathbb Q$ and gives the semidirect product $G_\mathbb Q=G_K\rtimes\langle c\rangle$. The invariant character therefore extends in exactly two ways, assigning $c$ the two signs. Under norm–restriction compatibility these are the primitive rational characters $\chi$ and $(\chi\epsilon)^*$ and both pull back to $\Psi$ by the idèlic norm. The star takes the primitive character inducing the product and retains each of its primitive Euler factors. [Tate, (1.2.2), p. 4](https://www.math.ias.edu/~goresky/pdf/3-01Tate.pdf#page=2) · [Artin reciprocity and Hecke characters, Knapp, §5](https://math.stanford.edu/~conrad/JLseminar/refs/Knappintro.pdf#page=20)

Let $q_1,q_2$ be the two primitive rational conductors, and $\mathfrak f_\Psi$ the Gaussian conductor ideal. Induction splits as the sum of the two rational characters. Conductors multiply in a direct sum, while the induction formula contributes the discriminant $4$ of $K$. Therefore
$$
 q_1 q_2=4\,N\mathfrak f_\Psi .
$$
The two characters agree locally up to an unramified twist away from $2$. At $2$, conductor exponent zero is interchanged with exponent two, since the only primitive character of conductor four is $\epsilon$. Every exponent $a\ge3$ is preserved under a twist of conductor four, as is seen on the last nontrivial principal-unit subgroup. Exponent one cannot occur for a primitive rational character. The full list, with $t$ odd, is
$$
 (q_1,q_2)=(t,4t),\quad \mathfrak f_\Psi=t\,\mathbb Z[i],
 \qquad\text{or}\qquad
 (q_1,q_2)=(q,q),\quad 8\mid q,\quad \mathfrak f_\Psi=(q/2)\mathbb Z[i].
$$
To identify the ideal, its invariance pairs the two primes at a split rational prime. At an inert prime and at the unique prime over two its norm fixes its exponent. This recovers the displayed rational integer ideal at all primes. [Artin conductor under induction, Cogdell, p. 15, (iii)](https://people.math.osu.edu/cogdell.1/Artin-www.pdf#page=15)

## Ray groups and exact counts

Let $P(q)=(\mu*\varphi)(q)$ denote the number of primitive Dirichlet characters of conductor $q$, including $P(1)=1$. For a rational modulus $m$, the invariant Gaussian characters of conductor dividing $m\mathbb Z[i]$ are exactly the restrictions to $G_K$ of the rational characters of modulus
$$
 D_m=\operatorname{lcm}(4,2m).
$$
Indeed the conductor table tests the two rational lifts prime by prime. All such extensions are the characters of $\operatorname{Gal}(\mathbb Q(\zeta_{D_m})/\mathbb Q)$, and restriction has kernel $\{1,\epsilon\}$. Thus the invariant group is the character group of $\operatorname{Gal}(\mathbb Q(\zeta_{D_m})/K)$ and has order $\varphi(D_m)/2=\varphi(m)$. Möbius inversion shows that the number with **exact** Gaussian conductor $h\mathbb Z[i]$ equals $P(h)$ at every $h$. This identity counts characters of exact conductor. Their group structures need not coincide with those of rational unit groups.

Since $\mathbb Z[i]$ has class number one, its full ray class group at $m\mathbb Z[i]$ is $(\mathbb Z[i]/m)^\times$ modulo the four global units. For $m\ge3$ those units have distinct images. Splitting of the odd primes and ramification at two give the index of the invariant character group:
$$
 \frac{\#\{\text{all finite ray characters}\}}{\#\{\text{invariant ray characters}\}}
   =\frac m4\prod_{p\mid m}\left(1-\frac{\epsilon(p)}p\right).
$$
For odd $p$ the local factor in four times this index is $p^{a-1}(p-\epsilon(p))$ for $p^a\Vert m$. It is at least four, with equality only for $p^a=3$ or $5$. The two-power factor is $2^{v_2(m)}$. Hence every finite ray character is covered exactly at the moduli $m=1,2,3,4,5$; at $1$ and $2$ the ray groups are trivial. As a direct independent check, the accompanying finite-ring program constructs the Gaussian units modulo each integer through 100, quotients by $\{\pm1,\pm i\}$, and counts conjugation-fixed classes. For a finite abelian group the fixed dual has the same cardinality as the fixed group, by kernel–cokernel counting. [Finite-ring calculation](verify_ray_classes.py) · [Output for all 100 moduli](ray-classes.json)

For $Q=400{,}000$, the number of different lift pairs is
$$
 \sum_{\substack{t\le Q/4\\t\ {\rm odd}}}P(t)
 +\frac12\sum_{\substack{q\le Q\\8\mid q}}P(q)
 =1{,}642{,}538{,}901+821{,}302{,}821=2{,}463{,}841{,}722 .
$$
These pairs contain 4,927,683,444 distinct primitive rational factors. The subfamily with $N\mathfrak f_\Psi\le10^{10}$ has $\sum_{h\le100000} P(h)=1{,}847{,}865{,}075$ characters. Two independent integer sieves agree for all 400,000 individual values of $P(q)$.

## The actual exterior sum

For each selected $\Psi$, include the summand $V_K^{-1}\overline{\Psi(x)}f(\log|x|_K)$ in the test, using the [same normalized $f$](../dirichlet-slab-exterior/README.md) throughout. Each distinct character enters once. The physical test vanishes on norm-one classes and has Mellin value one at $w=1/4$ on every selected row. The primitive factorization $L_K(s,\Psi)=L_\mathbb Q(s,\chi)L_\mathbb Q(s,(\chi\epsilon)^*)$ gives an exact equality of its absolute omitted sum with the sum over the selected rational factors, also when they have common zeros. [Proof at all finite primes and for arbitrary norm sections](README.md)

The odd selected conductors are at most 100,000 and the even ones are at most 400,000. Their published verified heights are therefore all at least $387.5$. Within each consecutive interval of 128 conductors and each parity, let $q_0$ be the largest selected conductor. Compute the two-sided inverse-cube upper $T_3(q_0,H_{q_0})$ for all those rational rows using their least verified height, and use the separate zeta tail at conductor one. On $387.5\le |t|\le900$, the [fixed radial transform](CYCLOTOMIC.md) satisfies $|R(x+it)|\,|t|^3<2.754\cdot10^{-117}$ for $|x|\le1/2$. This follows by enclosing the sines in the same 32 original boxes and all 172 extra boxes on every closed interval of length $1/16$. The estimate for $|t|\ge900$ is smaller. For each conductor group we may also bound the first six original boxes by inverse powers of $|t|$, use up to 42 further original boxes at that group's own height, and use the smaller of the common bound and the inverse-ordinate bound on each extra box. Taking the better of these two valid bounds gives
$$
 \sum_{\text{selected }\Psi}\ \sum_{|\Re\rho-1/2|\ge\alpha}
        m_{\Psi}(\rho)|R(\rho-1/2)| < 9.562\cdot10^{-113},\qquad \alpha>0.
$$
The 128- and 192-bit enclosures agree. For reproducibility run the programs in this directory with Python and python-flint 0.9.0, using the sibling directory containing the pinned rational verifier. [Gaussian verifier](verify_gaussian.py) · [128-bit result](gaussian-128.json) · [192-bit result](gaussian-192.json)

Keeping $f$ fixed while letting the paired rational conductor cutoff increase, and shrinking $\alpha=1/n$, gives a nondecreasing sequence of sums of norms. Every rational character eventually occurs together with its twist by $\epsilon$. Each possible off-line zero then remains in the sequence with a fixed positive coefficient. Hence a cofinal upper tending to zero in this Gaussian invariant family is equivalent to criticality of **all** primitive Dirichlet functions. The conductor estimate above gives a finite member of that sequence.
