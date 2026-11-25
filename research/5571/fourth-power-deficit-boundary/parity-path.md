# The full-prefix law of the rational complete parity deficit

Let $h\ge2$ be fixed. Draw an ordered tuple of $h$ distinct primes from $U=(J^{12},2J^{12}]\cap\mathbb P$. Retain twice the complete rational von Mangoldt Riesz mass on integers whose product of the $h$ auxiliary Jacobi signs is $-1$. Write $H_h(J)$ for its cumulative deficit with the true centers $j^8/2$, $1\le j\le J$, and $H'_h(J)$ for the corresponding prime-only deficit. For $h=2$ the selected mass is the arithmetic mean of the two fourfold mixed cell masses in mlyle’s comparison. At $p=2$ every auxiliary sign is $+1$, and every even power has positive parity. [Mlyle’s four classes](https://github.com/mccorvie/riemann-masullo/pull/7627) · [Distinct-prime parity union and the $6h$-th absolute moment](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7154774282)

There is an unconditional prime-character process behind this statistic. If rational RH holds, it gives the joint full-prefix law
$$
 \left(\frac{H_h(J)}{J^7\sqrt{\log J}},
       \frac{H'_h(J)-H_h(J)}{J^{19/3}}\right)
 \ \Longrightarrow\
 \left(\int_0^1 Y(u)_+\,du,\
       \frac34\int_0^1 u^{16/3}1_{\{Y(u)>0\}}\,du\right),
 \qquad
 Y(u)=2\int_0^{u^4} W(s)\,ds ,
$$
where $W$ is standard real Brownian motion. The arrow means that for every bounded continuous test function the limsup, as $J\to\infty$, of the absolute difference of the two expectations tends to zero as $h\to\infty$. In particular, the limiting expectations in the two coordinates are
$$
  \frac{2}{7\sqrt{6\pi}}=0.0658084094\ldots,\qquad \frac9{152}.
$$

The support of the joint limiting law is $[0,\infty)\times[0,9/76]$. For every fixed $t,\varepsilon>0$, all sufficiently large fixed $h$ then have a positive lower limiting proportion of tuples satisfying both
$$
 H_h(J)<tJ^7\sqrt{\log J},\qquad
 H'_h(J)-H_h(J)>(9/76-\varepsilon)J^{19/3}.
$$
The lower limiting proportion above the same deficit threshold is positive as well. If rational RH fails, the proportion below it tends to zero uniformly for $2\le h\le |U|/2$. This yields a lower-tail distinction for the actual complete sums at the prescribed coupled auxiliary scale. The unconditional upper bound needed in #5571 remains open.

## Moments over all ordered distinct auxiliary tuples

Put $Q=J^{12}$. Partition $U$ uniformly at random into $h$ labeled blocks $U_i$ of fixed sizes differing by at most one. Then choose $q_i$ independently and uniformly from $U_i$. Averaging over the partitions gives exactly the uniform measure on ordered distinct tuples by permutation symmetry. The estimates below are uniform in every such partition.

For a real coefficient sequence $b_p$ supported on odd $p\le x$, write
$$
 B=\sum b_p^2,\quad W_0=\max|b_p|,\quad
 Z=\sum_p b_p\prod_{i=1}^h(q_i/p).
$$
For squarefree odd $n$ put $\mu_i(n)=|U_i|^{-1}\sum_{q\in U_i}(q/n)$. Conditional on the partition, the expected sign of a term in $Z^m$ equals $\prod_i\mu_i(n)$, where $n$ is the squarefree kernel of the product of the term's $m$ prime bases. For a subfamily $I$ of $k$ blocks, $\prod_{i\in I}\mu_i(n)$ has the form $\sum_D a_D(D/n)$ on squarefree odd $D\le(2Q)^k$. For each product $D$ its factor from every prescribed block is uniquely determined. Therefore $\sum_D|a_D|^2=\prod_{i\in I}|U_i|^{-1}\ll_h(\log Q/Q)^k$.

Write $a=\lfloor h/2\rfloor, b=h-a$. Apply Heath-Brown's quadratic large sieve to the products from each group of blocks, followed by Cauchy–Schwarz over $n$. For every fixed $\delta>0$ and $L\ge1$ this gives
$$
 \sum_{\substack{n\le L\\ n\ {\rm odd,\ squarefree}}}
       \left|\prod_{i=1}^h\mu_i(n)\right|
 \ll_{h,\delta} (L(2Q)^b)^\delta (\log Q)^{h/2}
        \sqrt{(1+L/Q^a)(1+L/Q^b)} .
$$
The sieve uses $(D/n)$ in precisely this order. The bound holds even when $L$ exceeds the size of a subfamily's products. [Heath-Brown, Theorem 1, p. 237](https://doi.org/10.4064/aa-72-3-235-275)

Given a kernel $n$ with $s$ distinct prime factors, the total absolute coefficient of that kernel in $Z^m$ is at most $C_m W_0^s B^{(m-s)/2}$. Designate one occurrence of each kernel prime. Pair equal primes in the remaining slots and sum over the finitely many ways of choosing slots and pairings. Each free pair costs at most $\sum_p b_p^2$. The empty kernel has exactly the moment of the same polynomial in independent symmetric signs.

Take first $x=j^4$, $\sqrt J\le j\le J$ and $b_p=(x-p)_+\log p$. Then $W_0/\sqrt B\ll x^{-1/2}\sqrt{\log x}$, $B\sim x^3\log x/3$, and $x^3\le Q\le x^6$. In the sum over nonempty kernels with $s$ factors choose $L=x^s$. After normalization by $B^{m/2}$ the power of $x$, apart from logarithms and the arbitrary sieve loss, is
$$
 -\frac{s}{2}+\frac{(s-3a)_++(s-3b)_+}{2}.
$$
It is at most $-1/2$ for every $1\le s\le m<3h$. Indeed its three possible expressions are $-s/2$, $-3a/2$ and $(s-3h)/2$. Choosing $\delta<1/[8(m+6b)]$ leaves a power saving. For the empty kernel the odd moments vanish, and the normalized even moments are $(m-1)!!+O_m(W_0^2/B)$ by pairing and bounding repeated pairs. Thus the first $3h-1$ moments converge uniformly to the Gaussian moments on these samples. For $h=2$ this includes the fifth moment. [Four-moment fixed-pair argument and positive-part estimates](product-moments.md)

## The path and the true Riesz sums

With $0\le u\le1$ put
$$
 Z_{h,J}(u)=\frac{1}{J^6\sqrt{\log J}}
  \sum_{p\ {\rm odd}}(u^4 J^4-p)_+\log p\,\prod_{i=1}^h(q_i/p).
$$
Take any fixed finite real linear combination of evaluations at $u_1,\ldots,u_k$. Writing $x=J^4$ and $f(s)=\sum c_i(u_i^4-s)_+$, its unnormalized coefficients are $b_p=x f(p/x)\log p$. The weighted PNT gives $B/(J^{12}\log J)\to 4\int_0^1 f(s)^2\,ds$. This follows from $\sum_{p\le xt}\log^2p\sim xt\log x$ for each fixed $t>0$ and from continuity of $f$. If the integral is zero, $f$ vanishes identically. Otherwise $W_0/\sqrt B\ll_f x^{-1/2}\sqrt{\log x}$, so the same kernel bound and its power saving apply. Consequently the limiting Gaussian covariance is
$$
 \operatorname{Cov}(Y(u),Y(v))
 =4\int_0^{\min(u^4,v^4)}(u^4-s)(v^4-s)\,ds .
$$
Integration by parts for a deterministic linear kernel identifies this Gaussian process with the integrated Brownian motion stated above.

To see tightness on $C[0,1]$, condition on $q_1,\ldots,q_{h-1}$. The final prime is uniform on $U$ with $h-1$ elements removed. The nonnegative mean-square bound over $U$ increases by at most $|U|/(|U|-h+1)$. The coefficients of an increment have magnitude at most $4J^4|u-v|\log p$. Since $\sum_{p\le J^4}\log^2p\ll J^4\log J$, the Selberg-square estimate gives $\mathbb E|Z_{h,J}(u)-Z_{h,J}(v)|^2\ll|u-v|^2$ with an absolute constant whenever $h\le |U|/2$ and $J$ is large. All paths are continuous and vanish at zero. The usual moment criterion for tightness now applies. [Prime-supported mean-square estimate](prime-sieve.md)

Here is a precise use of the two limits. If an iterated convergence claim for bounded continuous path tests failed, take $h_n\to\infty$ along a failing subsequence. For each $n$ choose a failing $J_n$ arbitrarily large after the fixed-$h_n$ moment errors are at most $1/n$ for the first $n$ rational finite-dimensional linear forms and orders up to $\min(n,3h_n-1)$. Tightness gives a subsequential path limit. Arbitrarily high fixed even moments ensure uniform integrability of each fixed moment along that subsequence. The Gaussian law is moment determinate, so all rational linear forms have the displayed Gaussian limits. These forms determine a measure on continuous paths. Thus every such limit is the law of $Y$, a contradiction.

For the positive parts, the unrestricted odd-prime mass is $P_o(x)=\sum_{p\ {\rm odd}}(x-p)_+\log p$. The complete parity mass equals $P_o$ minus the unnormalized product twist plus the nonnegative correction
$$
 C_h(x)=\sum_{\substack{p\ {\rm odd}\\k\ge3\ {\rm odd}}}
       (x-p^k)_+\log p\,\Big(1-\prod_i(q_i/p)\Big).
$$
Uniformly in the tuple, $0\le C_h(x)\ll x^{4/3}$ by Chebyshev. Rational RH gives $x^2/2-P_o(x)=O(x^{3/2})$ by the absolutely convergent first Riesz explicit formula. Hence the normalized sum of the true complete deficits differs from the mean of $Z_{h,J}(j/J)_+$ by $O(1/\sqrt{\log J})$. On tight sets of continuous functions, the Riemann sums converge to the integral uniformly.

To evaluate the gain, take a fixed $\eta>0$ and $\eta J\le j\le J$. For the cube weights $a_p=(j^4-p^3)_+\log p$, the final-prime mean-square estimate gives variance about the unrestricted cube mass $\ll j^{28/3}\log(2j)$ uniformly for fixed $h$; the same bound holds uniformly for $h\le|U|/2$. The unrestricted mass is $(3/4+o(1))j^{16/3}$ by the PNT. The remaining odd powers contribute $O(j^{24/5}\log(2j))$. Chebyshev's inequality summed over $j\ge\eta J$ shows that $C_h(j^4)=(3/4+o(1))j^{16/3}$ simultaneously with probability tending to one. For instance use a relative tolerance $J^{-1/16}$. The gain at a sample is exactly the smaller of this nonnegative correction and the positive part of $j^8/2-P_o(j^4)+J^6\sqrt{\log J}\,Z_{h,J}(j/J)$. Away from $|Z_{h,J}|\le\delta$, it therefore agrees with the whole correction on the positive side and vanishes on the negative side for all large $J$. For each $u>0$ the Gaussian $Y(u)$ is nondegenerate. By Fubini its zero set has Lebesgue measure zero almost surely. Uniform path convergence along a convergent realization therefore gives convergence of the weighted sign Riemann sums, by bounding a shrinking neighborhood of that zero set. The discarded prefix $j<\eta J$ costs $O(\eta^{19/3})$ in normalized gain. Let $\eta\downarrow0$. This proves joint convergence.

The first coordinates are uniformly integrable under RH by the mean-square bound and Minkowski's inequality over $j$; the normalized gains are uniformly bounded. Since $\operatorname{Var}Y(u)=4u^{12}/3$ and $\Pr(Y(u)>0)=1/2$ for $u>0$, integration gives the two claimed expectations. Brownian motion assigns positive probability to a uniform neighborhood of the zero path, and to a uniform neighborhood of $W(s)=Ls$ for each fixed $L>0$. Applying these two events to the continuous first functional gives the positive lower and upper tails for arbitrary $t>0$. These support facts also follow by splitting $[0,1]$ into finitely many intervals and requiring Brownian increments and their bridges to stay near the prescribed linear path.

For the joint support, fix $0<\tau<1$ and $K>0$. The deterministic path $W(s)=K(3s^2-2\tau s)/2$ gives $Y(u)=Ku^8(u^4-\tau)$. Its second coordinate is $(9/76)(1-\tau^{19/12})$ and varies over $(0,9/76)$. Its first coordinate can be set to any prescribed positive value by adjusting $K$. The functionals are continuous at this path since the zero set is finite. Every uniform neighborhood of the path has positive Brownian probability by the same support argument, and taking the closure gives the entire stated rectangle. The open-set inequality under weak convergence gives the simultaneous tail claim. For each $t>0$ the first coordinate has no atom at $t$. Indeed, conditional on the Brownian bridge $W(s)-s W(1)$, the first coordinate is the integral of $[g(u)+u^8 W(1)]_+$ for fixed $g$ and an independent standard normal $W(1)$. This integral is strictly increasing as a function of $W(1)$ wherever its value is positive. Consequently the iterated probabilities strictly below or above $t$ converge to the corresponding probabilities for the stated first coordinate.

If rational RH fails, mlyle’s every-prefix result gives $D(J)\gg J^{7+\delta}$ for some fixed $\delta>0$. Conditioning on the last distinct prime, the same Selberg estimate yields $\|H_h-D(J)\|_2\ll J^7\sqrt{\log J}+J^{19/3}$ by positive-part Lipschitz continuity, uniformly for all $2\le h\le |U|/2$. Restoring $p=2$ costs $O(J^5)$. Hence $H_h/D(J)\to1$ in $L^2$ uniformly in this range. This proves the asserted alternative. [Mlyle’s rational fourth-power exponent](https://github.com/mlyle/riemann-masullo/blob/255d2b1531f3534cd35ea5dd9eb379fadd2c1104/research/5571/rational-fourth-power-deficit.md) · [Once-integrated formula and all-field transfer](README.md)

## Unconditional correction to the mean

The Gaussian calculation also evaluates the effect of averaging parity on the actual complete deficit around the unrestricted arithmetic $D(J)$, without any hypothesis on the zeros. Set $L_J=J^6\sqrt{\log J}$, $r_j=(j^8/2-P_o(j^4))/L_J$, $\sigma_j=2(j/J)^6/\sqrt3$. For the standard normal density $\phi$ and distribution function $\Phi$, put
$$
 g(r,\sigma)=\sigma\phi(|r|/\sigma)-|r|\Phi(-|r|/\sigma)
 \quad(\sigma>0).
$$
Then
$$
 \lim_{h\to\infty}\limsup_{J\to\infty}
 \left|\frac{\mathbb E H_h(J)-D(J)}{J^7\sqrt{\log J}}
        -\frac1J\sum_{j\le J}g(r_j,\sigma_j)\right|=0 .
$$
In particular the limiting upper excess is at most $2/(7\sqrt{6\pi})$ and the limiting lower excess is nonnegative at this scale. The formula retains the true signed Riesz errors in its individual terms.

Indeed, for every real $r$ and standard normal $N$, $\mathbb E[r+\sigma N]_+-[r]_+=g(r,\sigma)$, with $0\le g(r,\sigma)\le\sigma/\sqrt{2\pi}$. Uniformly over grid samples in the same iterated sense, the Wasserstein-1 distance from the law of $Z_{h,J}(j/J)$ to that of $Y(j/J)$ tends to zero. Otherwise choose a failing sequence with $j/J$ convergent by compactness and with all the fixed-moment errors tending to zero as in the path proof. Tightness and continuous evaluation give weak convergence of the marginals, and their uniformly bounded second moments upgrade it to Wasserstein-1 convergence. The functions $z\mapsto[r+z]_+-[r]_+$ are all $1$-Lipschitz. Thus the approximation holds even when the true $r_j$ grow without bound. The total discarded odd powers cost $O(J^{19/3})$, and using the unrestricted $D(J)$ in place of its odd-prime version costs $O(J^5)$. Summing the expectation estimates establishes the formula.

The [finite verifier](verify_product_moments.py) exhausts the balanced labeled partitions of seven genuine auxiliary primes into three and four blocks. It checks uniform enumeration of every ordered distinct tuple and unique factorization of the block products.
