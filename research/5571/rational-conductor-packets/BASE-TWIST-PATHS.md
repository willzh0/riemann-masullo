# The limiting path of the actual prime deficits under conductor twists

Masullo, Theorem 12.5.1.1, pp. 519–520. Fix a number field $F$ and a unitary Hecke character $\chi$ normalized on the chosen norm section. Use the actual coefficients of $-L'/L$ and twist $\chi$ by the norm pullbacks of primitive rational Dirichlet characters $\xi$. Write $X=J^4$. All the statements below hold for primitive conductors up to $C$ when $\log C/\log J\to\infty$, or at each individual prime conductor $\ell$ when $\log\ell/\log J\to\infty$. For statements about the cells, independently sample a uniform ordered pair of auxiliary primes in $(J^{12},2J^{12}]$. The same limits hold with distinct pairs. [Set-up, local factors and moment bounds](BASE-TWISTS.md) · [Project cell conventions](https://github.com/mccorvie/riemann-masullo/pull/7627)

## The covariance constant for any number field

Factor the finite étale algebra $F\otimes_{\mathbb Q}F=\prod_i E_i$. Write $\alpha_i,\beta_i:F\to E_i$ for its two structure maps. Identify both target copies of $F$ in the relative norms with the original $F$, and set
$$
 \vartheta_i=(\chi\circ N_{E_i/F,\alpha_i})
                 \overline{(\chi\circ N_{E_i/F,\beta_i})},
 \qquad
 m_\chi=\#\{i:\vartheta_i=1\}.
$$
The multiplication map $F\otimes F\to F$ supplies one factor with $\vartheta_i=1$. Each factor has positive degree over $F$ and the sum of these degrees is $[F:\mathbb Q]$. Thus $1\le m_\chi\le[F:\mathbb Q]$. For a Galois field this is the number of automorphisms fixing $\chi$. In particular $m_\chi=2$ for the principal character of $\mathbb Q(i)$ and $m_\chi=1$ for the character on principal ideals $(z)$ given by $(z/|z|)^4$, or its inverse under the local uniformizer convention. [Genuine Gaussian angular character in Lean](https://github.com/mccorvie/riemann-masullo/pull/7678)

Let $a_\chi(p)$ denote the actual coefficient at rational norm $p$. At all but finitely many primes,
$$
 \frac{|a_\chi(p)|^2}{\log p}
 =\log p\sum_i\sum_{\substack{\mathfrak P\subset E_i\\ N\mathfrak P=p}}
                  \vartheta_i(\mathfrak P).
$$
Indeed, degree-one primes above $p$ correspond to $\mathbb F_p$-points of the reduction of the integer algebra. Ordered pairs of such points are the $\mathbb F_p$-points of its tensor square. Away from finitely many primes that tensor square is the product of the reductions for $E_i$. The relative norms of a degree-one prime in either copy give the two primes of the pair. The coefficients at rational norm $p$ are precisely the sums of the corresponding unramified character values times $\log p$.

For every positive real scalar idèle at infinity the two relative norms agree after identifying the two copies of $F$. Their values under $\chi$ therefore cancel. Each $\vartheta_i$ is trivial on this positive scalar subgroup of $E_i$. A pure norm twist with this property is trivial. The prime ideal theorem for a fixed Hecke character hence gives main term $x$ for $\vartheta_i=1$ and $o(x)$ for the other terms, after weighting by log norm. Primes with residue degree at least two cost $O_{E_i}(\sqrt{x}\log x)$. This proves
$$
 \sum_{p\le x}\frac{|a_\chi(p)|^2}{\log p}\sim m_\chi x,\qquad
 \frac1{X\log X}\sum_{p\le X}|a_\chi(p)|^2\delta_{p/X}
       \ \Longrightarrow\ m_\chi\,du\quad\text{on }[0,1].
$$
The second assertion is partial summation. In particular $\sum_{p\le x}(x-p)^2|a_\chi(p)|^2\sim m_\chi x^3\log x/3$. The initial norm section can be arbitrary since the positive scalar cancellation takes place between the two norms. [Lagarias and Neshveyev, Theorem 3.1 and (3.1), p. 6](https://arxiv.org/pdf/1211.3256#page=6)

## A joint law across the entire interval of cutoffs

On $0\le t\le1$ put
$$
 P_J(t)=\frac{\Re\sum_{p\le X}(Xt-p)_+a_\chi(p)\xi(p)}
                       {J^6\sqrt{\log J}}.
$$
For a sign cell $c$, write $P_{J,c}$ for the same path with its fourfold mask. In the space of continuous real paths with the uniform norm,
$$
 (P_{J,c})_{c=1}^4\ \Longrightarrow\
 (G_c)_{c=1}^4,\qquad
 G_c(t)=2\sqrt{2m_\chi}\int_0^t(t-u)\,dB_c(u)
       =2\sqrt{2m_\chi}\int_0^t B_c(u)\,du ,
$$
where the four $B_c$ are independent standard Brownian motions. The unrestricted path converges jointly to $G=\frac14\sum_cG_c$, which has the law of $\sqrt{2m_\chi}\int_0^t B(u)\,du$. For instance
$$
 \operatorname{Cov}(G(s),G(t))=
 2m_\chi\int_0^{\min(s,t)}(s-u)(t-u)\,du .
$$
In particular samples at different cutoffs are correlated.

For finite-dimensional convergence, first replace $\xi(p)$ by independent uniform phases $Z_p$. Any finite real linear combination of evaluations has bounded deterministic profile $g(p/X)$, piecewise linear on $[0,1]$. Its largest normalized prime summand tends to zero by $|a_\chi(p)|\le[F:\mathbb Q]\log p$. The independent-phase triangular array has a Gaussian limit with the covariance above. The factor $2$ in the unrestricted covariance combines the real-part variance $1/2$ with $\log X/\log J=4$. Bounded independent summands give convergence of each fixed moment. Over a single sufficiently large prime modulus, character orthogonality matches every fixed mixed moment to that model once the integer products fit below the modulus. Over varying primitive conductors use the off-diagonal $O_r(X^r/C)$ normalized estimate in the companion note. Removing the primes up to $\sqrt X$ costs $o(1)$ in mean square. The diagonal probability that any of at most $r$ remaining primes divides the primitive conductor is $O_r(X^{-1/2})$. This proves finite-dimensional convergence by real linear combinations, including zero-variance combinations. The bounded bad-prime and pole terms are controlled below. [Primitive moment computation](BASE-TWISTS.md#sharp-means-in-the-rational-family)

For the four cells apply the auxiliary-prime second moment to $\gamma_p=|a_\chi(p)|^2 g(p/X)^2$ for each of the finitely many profiles in the linear combination. Its mean square error in the signed weight is $O_{F,g}(\log(2X)\sum_{p\le X}(\log p)^4+(\log 2)^4)=o((X\log X)^2)$. Thus each cell receives one quarter of its corresponding squared profile mass in probability. Polarization gives the cross-time covariance within each cell. The four cells have disjoint supports. Conditional on a typical auxiliary pair, the character moment calculation for the finite collection therefore has the four independent Gaussian limits displayed above. The moment error estimates are uniform in the masks. In fact, after division by $(X\log X)^2$, the displayed mask error is $O_{F,g}(\log^2 X/X)$. This is summable in $J$ at $X=J^4$. Borel–Cantelli on a countable dense class of continuous profiles shows that the covariance measures converge almost surely along any coupling of the auxiliary pairs across $J$. The conditional path law therefore holds for almost every such sequence when the base twist is sampled independently. Restricting to distinct pairs loses probability $1/|U|=o(1)$. [Auxiliary estimate and normalization](BASE-TWISTS.md#sharp-means-in-the-rational-family)

For tightness, the primitive large sieve or single-modulus orthogonality gives, even conditional on an arbitrary choice of auxiliary pair,
$$
 \mathbb E_\xi |P_{J,c}(t)-P_{J,c}(s)|^2
 \ll_F\frac{X^2|t-s|^2}{J^{12}\log J}
             \sum_{p\le X}|a_\chi(p)|^2
 \ll_F |t-s|^2 .
$$
All paths start at zero. The continuous-path tightness criterion with moment exponent two gives tightness in the uniform norm. The unrestricted prime path is the mean of the four masked paths. Removing finitely many bad prime Euler factors changes a complete path by $O_{F,\chi}(X\log(2X)/(J^6\sqrt{\log J}))$. All proper prime powers contribute $O_F(X^{3/2}/(J^6\sqrt{\log J}))=o(1)$ uniformly over the cutoff and the cell. Among all primitive conductors only $O_F(1)$ labels can have the actual pole. Their proportion is $O_F(C^{-2})$. At large individual prime conductor there are none. Thus the same law applies to the *actual complete, true-pole-centered paths* with the sign convention reversed when forming losses. Those pole labels also cost $o(1)$ in any fixed normalized moment in these conductor regimes.

## Consequences for the actual cumulative deficits

Sample at $t=(j/J)^4$ and normalize the sum by $J^7\sqrt{\log J}$. For the unrestricted deficit the limiting law is that of
$$
 \int_0^1(-G(v^4))_+\,dv.
$$
For one specified complete cell replace $G$ by $G_c$. For the best choice among a nonempty set $A$ of cells allowed to change at each sample, the limiting law is
$$
 L_A=\int_0^1 \min_{c\in A}(-G_c(v^4))_+\,dv .
$$
All these laws hold jointly. Replacing the upper integration endpoint by $s$ gives the law of the whole cumulative prefix process, uniformly for $0\le s\le1$ after linear interpolation. Brownian scaling multiplies each of the three prefix means by $s^7$. Clipping and taking finite minima are Lipschitz operations in the uniform norm. On compact sets of continuous paths the corresponding Riemann sums converge uniformly. The second moment bound ensures uniform integrability for expectations. Hence all three rational mean constants in the companion note are multiplied by $\sqrt{m_\chi}$ for general $F,\chi$. The means concern cumulative deficits and the cell means average over the auxiliary pair. [Rational constants and antecedents](BASE-TWISTS.md#sharp-means-in-the-rational-family)

There is also a lower bound in probability even for the best choice among **all four** cells. Almost surely $L_A>0$. At any prescribed $t>0$ the probability of $G_c(t)<0$ for every $c\in A$ is $2^{-|A|}$. Existence of simultaneous negativity at arbitrarily small positive times is a germ event for the Brownian motions. Its probability is at least $2^{-|A|}$ by continuity from above of the events of simultaneous negativity somewhere before $1/n$. Blumenthal's zero-one law makes that probability one. Continuity then gives a nonempty interval of strict negativity. Positive small-ball probabilities of Brownian motion yield arbitrarily small values of $L_A$ with positive probability. Neighborhoods of a common linear path $B_c(t)=-K t$ yield arbitrarily large values, and varying $K$ shows that the support is $[0,\infty)$. The same assertions hold for the unrestricted and single-cell laws.

Consequently, for every $\eta_J\downarrow0$, the fraction of twist/pair choices for which *even the best complete deficit* is at most $\eta_J J^7\sqrt{\log J}$ tends to zero. Equivalently, all but a vanishing proportion of base characters have a vanishing exceptional fraction of auxiliary pairs at that threshold (with a vanishing tolerance chosen by Markov). For each fixed $0<\delta<1$ there are $a_\delta>0$, $M_\delta$ and $J_\delta$ depending on $F,\chi,\delta$ such that this fraction at threshold $a_\delta J^7\sqrt{\log J}$ is at most $\delta$ for all $J\ge J_\delta$ and $C\ge J^{M_\delta}$, or all prime $\ell\ge J^{M_\delta}$. Otherwise a diagonal sequence with unbounded conductor exponent and threshold tending to zero would contradict the preceding limit. These estimates allow the exceptional set to depend on height. The bound required in #5571 for one prescribed character at every large height remains open. [Fixed-base formulation](https://github.com/mccorvie/riemann-masullo/pull/7636) · [Rational all-pairs high moments and exceptional set in Lean](https://github.com/mccorvie/riemann-masullo/pull/7672) · [Related prime-product moment comparison, Harper (1.4), pp. 11–12](https://arxiv.org/pdf/2301.04390#page=11)

The [arithmetic check](path_check.py) verifies 360 finite cross-time and cross-cell real second moments over all 261 primitive characters modulo 263, using 160-bit Arb enclosures. At prime cutoff one million the computed first Riesz energies relative to the rational principal are 1.99726 and 0.99743 for the Gaussian principal and fourth angular character, respectively. These finite computations check the normalization. [Numerical receipt](path_check.json)
