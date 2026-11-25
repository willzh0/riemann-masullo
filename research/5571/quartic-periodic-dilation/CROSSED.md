# Conjugating only the periodic dilation selects the zeros unique to the quartic character

Let $\chi(2)=i$ be the primitive quartic character modulo 5, let $\xi=\bar\chi$, and put

$$S_\chi(x)=\sum_p\chi(p)(x-p)_+\log p,\qquad
 C(x)=\sum_{n\ge1}\xi(n)n S_\chi(x/n),\qquad
 C_N(x)=\sum_{n\ge1} W(n/N)\xi(n)n S_\chi(x/n) .$$

Use the same $W$ and $N=x^{21/100}$ as in the matched periodic convolution. With $m_\chi(\rho)$ denoting multiplicity, the crossed row has the unconditional expansion

$$C_N(x)=-\sum_{\rho} \frac{m_\chi(\rho)L(\rho,\bar\chi)}
  {\rho(1+\rho)}x^{1+\rho}+o_\chi(x^{3/2}).\tag{1}$$

The coefficients are absolutely summable, and the sum ranges over distinct nontrivial zeros of $L(s,\chi)$. Common zeros vanish even when their multiplicities differ. At every surviving point the conjugate point is absent from the surviving spectrum. The certified simple critical zero of $\chi$ near $-4.13i+1/2$ survives because the first positive ordinate of this same character exceeds 6.18. [Quartic zero certificate](https://github.com/willzh0/riemann-masullo/blob/53cac8a4461b84ad1d9c96ea2305f48e82ba4a31/PROOF.md).

## Proof of the physical expansion

First dilate the full von Mangoldt Riesz sum $\Psi_{1,\chi}(u)$. Its odd primitive explicit formula for $u\ge1$ consists of the zero terms $-m_\chi(\rho)u^{1+\rho}/[\rho(1+\rho)]$ and

$$E(u)=a_0u+1+\log u-a_1-\sum_{k\ge1}\frac{u^{-2k}}{2k(2k+1)}.$$

The finite sum of $n\xi(n)E(x/n)$ over $n\le x$ is $O_\chi(x\log(2x))$. The affine part uses bounded periodic partial sums, and $n\mapsto n\log(x/n)$ on $[1,x]$ has total variation $O(x)$. For each trivial-zero term, $n(n/x)^{2k}$ is increasing to $x$, uniformly in $k$, and the scalar coefficients are summable. [Exact odd-character residues including the endpoint at one](https://github.com/mlyle/riemann-masullo/tree/3f90b6c75f2e36f52c2c9cb427155a556bcee9d8/research/5571/quartic-mod-five-deficit).

The finite dilation of the absolutely convergent zero sum gives the proposed series with $L(\rho,\xi)$ temporarily replaced by $\sum_{n\le x}\xi(n)n^{-\rho}$. Here is a uniform justification of that replacement. Write $A(t)=\sum_{n\le t}\xi(n)$ for its bounded periodic partial sum, and remove its period mean. The resulting function has a bounded primitive. Partial summation once and integration against this primitive once more give, for $0<\beta=\Re s<1$,

$$\left|\sum_{n>x}\xi(n)n^{-s}\right|
 \ll_\chi x^{-\beta}\left(1+\frac{(1+|s|)^2}{x}\right).$$

Indeed the mean of $A$ contributes a bounded multiple of $x^{-s}$ and the remaining integral is bounded using $\int_x^\infty t^{-\beta-2}\,dt\le x^{-\beta-1}$. For zeros with $|\gamma|\le x$, multiply this error by $x^{1+\beta}/|\rho(1+\rho)|$ and sum multiplicities. The result is $O_\chi(x\log(2x))$, by absolute summability of the squared-denominator coefficients and $N_\chi(x)\ll x\log(2x)$.

For the remaining finite Dirichlet-polynomial tail, $\sum_{n\le x}n^{-\beta}\le 1+x^{1-\beta}\log(2x)$ and $\sum_{|\gamma|>x}m_\chi(\rho)/|\rho(1+\rho)|\ll_\chi\log(2x)/x$, giving $O_\chi(x\log^2(2x))$. For the target $L$-value tail use the standard convexity estimate $|L(\beta+i\gamma,\xi)|\ll_{\chi,\epsilon}(1+|\gamma|)^{(1-\beta)/2+\epsilon}$, following from the functional equation, Stirling's formula, and the three-lines principle. On $H<|\gamma|\le2H$,

$$x^{1+\beta}H^{(1-\beta)/2}\le \max\{x^2,x\sqrt H\}.$$

The dyadic denominator sum is $O_\chi(\log(2H)/H)$. Sum the first bound from $H=x$ through $x^2$ and the second above $x^2$, to get $O_{\chi,\epsilon}(x^{1+\epsilon})$ after decreasing the exponent in convexity to absorb logarithms. The same convexity and dyadic zero count give $\sum_\rho m_\chi(\rho)|L(\rho,\xi)|/|\rho(1+\rho)|<\infty$.

To return to the prime sum, put $A_\xi(v)=\sum_{n\le v}\xi(n)(v-n)$. Its slope is bounded and it is $O_\chi(v)$. An omitted prime power $p^k$ contributes $\chi(p)^k\log p\,p^k A_\xi(x/p^k)$, of modulus $O_\chi(x\log p)$. Exponents $k\ge3$ together cost $O_\chi(x^{4/3}\log^2(2x))$. For $k=2$ write $y=\sqrt x$ and $g(v)=v^2 A_\xi(v^{-2})$. The normalized square contribution is

$$y^{-1}\sum_{p\le y}\chi(p)^2\log p\,g(p/y)=o(1).$$

Indeed $g$ is bounded, piecewise smooth and $g'(v)=O_\chi(1/v)$. For any fixed $\delta>0$, primes $p<\delta y$ cost $O_\chi(\delta)$ after division by $y$, by Chebyshev. On $[\delta,1]$ use partial summation and the fixed-modulus prime number theorem for the nonprincipal character $\chi^2$. Then let $\delta$ decrease to zero. This proves (1) for the complete arithmetic dilation $C(x)$.

Finally the cutoff proof at $N=x^{21/100}$ gives $C_N(x)-C(x)=O_{\chi,W,\epsilon}(x^{1.48+\epsilon})$ exactly as for the matched case: the integration by parts uses the bounded periodic primitives of the dilation character $\xi$, with Fourier coefficients $O_\chi((1+|k|)^{-2})$. The reciprocal-prime sum uses the separate factor $\chi(p)$; both hypotheses hold unchanged here. The dyadic cutoffs and exponents are identical. Choosing $\epsilon<0.02$ proves (1) for the prescribed short row. [Mlyle’s full cutoff proof and dyadic ledger](https://github.com/mlyle/riemann-masullo/blob/c2eb094fffef928fdb72c2e180c255092e819347/research/5571/fourth-power-prime-curvature/spectral-interpolation-periodic-prime-convolution.md).

## A lower bound for both signs at every terminal index

Set $\Theta_\times$ to the larger of $1/2$ and the supremum of the real parts of χ zeros absent from $\bar\chi$. For **every** choice of unit phases $z_J$, common to the samples within each prefix, and either sign,

$$\lim_{J\to\infty}\frac{\log\left(1+\sum_{j\le J}
 [\pm\Re(\bar z_J C_{j^{0.84}}(j^4))]_+\right)}{\log J}
 =5+4\Theta_\times .\tag{2}$$

There are $\lambda_\chi,c_\chi\in(0,1)$ such that the corresponding sum on $\lambda_\chi J<j\le J$ exceeds $c_\chi J^7$ for every sufficiently large $J$, uniformly in the angle and sign. If $\Theta_\times=1/2$, the prefix is also $O_\chi(J^7)$ in every direction. If a surviving exterior zero has real part $\beta$, the same interval gives a lower bound $\gg_\rho J^{5+4\beta}$ upon fixing the compact window as in the companion note.

For the proof write $a(\rho)=-m_\chi(\rho)L(\rho,\bar\chi)/[\rho(1+\rho)]$. Whenever $a(\rho)\ne0$, $\rho$ is a χ zero but $\bar\rho$ is not. The projected coefficient is $\bar z_J a(\rho)/2$ in one orientation and its complex conjugate in the other. Its modulus equals $|a(\rho)|/2$ independently of $z_J$. If an exterior zero survives, the bounded compact annihilator and the single divided transform in the companion note give one-sided integrated lower bounds $\gg_\rho\exp((\beta-1/2)y)$ uniformly in angle in every fixed log window of sufficient length. If none survives, (1) is a uniformly almost-periodic critical series plus $o(1)$ after normalization, by dominated convergence. Every real projection has mean zero and a nonzero coefficient at the certified asymmetric critical ordinate. Compactness of directions gives uniform positive and negative integrals on each sufficiently long fixed interval, as in the companion note.

For discrete transfer use the complete $C$ first. Its coefficient at $m$ is identically zero when $5\mid m$, and otherwise equals $\xi(m)\sum_{p\mid m}\chi(p)^2\log p$, of modulus at most $\log m$. Thus the elementary chord estimate for each fourth-power cell still costs $O(J^6\log J)$, which the growing exterior signal absorbs. In the bounded critical case normalized uniform almost-periodicity gives $o(1)$ interpolation error per cell. The powers $x^{1.48+\epsilon}$ cost $o(J^7)$ after summing their physical samples. Finally, absolute summability gives $|C_N(x)|\ll_\chi x^{1+\Theta_\times}$. These upper and lower bounds prove (2).

In the original matched dilation $B_{\chi,N}$, all critical and exterior coefficients vanish, giving $o(J^7)$ upon summation. The crossed row provably has a critical floor in every sufficiently late terminal shell. The lower bound is forced by an actual certified zero with no partner, without assuming an exterior counterexample. The two rows use the same weight, cutoffs and true primitive character on the primes. The crossing distinguishes absence of a conjugate zero from a mismatch in the multiplicities of two existing zeros, which the optimized naked statistic in the companion note measures.


At the certified unpaired zero $\rho$ near $1/2-4.13i$, interval arithmetic bounds $|L(\rho,\bar\chi)|/[2|\rho(1+\rho)|]>0.05389$ independently at 128 and 192 bits. The real-axis Mellin argument and fourth-power interpolation used for logarithmic dilators therefore give, for each fixed unit $z$ and each sign,

$$

 \limsup_{j\to\infty}\frac{[\pm\Re(\bar z C_{j^{0.84}}(j^4))]_+}{j^6}\ge0.05389 .

$$

The constant here is for a fixed phase and a subsequence of samples. The earlier shell estimate is uniform for one phase chosen anew at each terminal prefix. [Signed Mellin argument](weighted-probes.md) · [Two-precision certificate](verify_quartic_log_dilators.py)
