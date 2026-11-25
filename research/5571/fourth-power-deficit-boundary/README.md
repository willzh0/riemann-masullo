# Rightmost zeros and the fourth-power Hecke prime deficit

For Theorem 12.5.1.1, pp. 519–520, fix a number field $F$ and a unitary idele-class character $\chi$ trivial on the chosen norm section. Use mlyle’s degree-one arithmetic statistic
$$
 a_\chi(p)=(\log p)\!\sum_{\substack{v\mid p,\ f_v=1\\\chi_v\ \mathrm{unramified}}}
       \chi_v(\varpi_v),\qquad
 S_\chi(x)=\sum_{p\le x}(x-p)\Re a_\chi(p)-\delta_\chi x^2/2,
 \quad D_\chi(J)=\sum_{j=1}^{J}[-S_\chi(j^4)]_+ ,
$$
where $\delta_\chi=\mathbf1_{\chi=1}$ and $[v]_+=\max(v,0)$. A field-ramified rational prime is included whenever its indicated local character is unramified. Write $\eta=\sup(\{1/2\}\cup\{\Re\rho\})$, with nontrivial completed zeros counted with multiplicity, and $s=4\eta+5$. All implicit constants may depend on the individual field and normalized character.

The [single-subsequence proof](subsequence.md) strengthens the all-field limsup statement below to an ordinary clamped limit and obtains a constant-factor lower bound from each individual exterior zero on every sufficiently large prefix.

The [joint Lean verification](verification.md) covers the precise all-field, all-character cumulative epsilon criterion in both directions.

## The boundary distinguishes three cases

If $1/2<\eta\le1$, then the following hold.

1. If no zero attains $\eta$, $D_\chi(J)=o(J^s)$.
2. If all zeros on $\Re z=\eta$ consist of the real zero $\eta$, of multiplicity $m>0$, then
   $$
      \frac{D_\chi(J)}{J^s}\longrightarrow\frac{m}{\eta(1+\eta)s}.
   $$
   Other zero real parts may approach $\eta$ from below.
3. If there is a nonreal zero on $\Re z=\eta$, then
   $$
      0<\liminf_{J\to\infty}D_\chi(J)/J^s
        <\limsup_{J\to\infty}D_\chi(J)/J^s<\infty .
   $$

Thus, above the critical line, the normalized deficit has a positive lower bound at every sufficiently large cutoff precisely when some zero attains the supremum. A positive ordinary limit characterizes the real-only case. These assertions require no density estimate for zeros near the boundary.

For arbitrary normalized $\chi$, no zero strictly to the right of $b$ is equivalent both to $D_\chi(J)=O(J^{4b+5})$ and to the bounds $O_\epsilon(J^{4b+5+\epsilon})$ for every $\epsilon>0$, $1/2\le b\le1$. If $q_\chi=\limsup_{J\to\infty}\log(1+D_\chi(J))/\log J$, it follows that $\max(7,q_\chi)=4\eta+5$. For the principal character of **every** number field, $q_\chi=4\eta+5$ including $\eta=1/2$. At that critical endpoint $D_\chi(J)\asymp_F J^7$. For a general character at $\eta=1/2$, the upper estimate gives $D_\chi(J)=O_{F,\chi}(J^7)$.

Mlyle proved the large-deficit implication from any zero strictly right of $1/2$ and the all-field converse from the cumulative bound. His earlier written argument includes the $O(x^{3/2})$ first-Riesz upper bound at the critical endpoint. His rational principal result proves the stronger **ordinary** logarithmic-exponent limit, using Ingham’s rational density bound, and gives the explicit rational Fourier multiplier and logarithmic mean $2/21$. For arbitrary fields in the unattained case we use his all-field **limsup** lower bound. [Cumulative theorem and rational update](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7153546171) · [Joined Lean proof](https://github.com/mlyle/riemann-masullo/blob/fe3a0369549a312fade55dfffb8860882e0f16f4/RiemannMasullo/Ch13_ZerosHecke/HeckePrimeLowerBound.lean#L274) · [Earlier Hecke upper bound](https://github.com/mlyle/riemann-masullo/blob/5ad05be8123d3a4fe79b0b4838ea44caca607c65/research/5571/lower-hecke-riesz-grid.md) · [Rational fourth-power result](https://github.com/mlyle/riemann-masullo/blob/255d2b1531f3534cd35ea5dd9eb379fadd2c1104/research/5571/rational-fourth-power-deficit.md)

## Absolute first-Riesz formula

Use the intrinsic finite Hecke $L$-function $L(s,\chi)$ and
$$
 R_\chi(x)=\sum_{\substack{v,\ k\ge1\\ \chi_v\ \mathrm{unramified}}}
 \chi_v(\varpi_v)^k\log Nv\,(x-(Nv)^k)_+ .
$$
When all critical zeros have $\Re\rho\le b<1$, the unitary functional equation and conjugation reflect a zero of this same character to $1-\bar\rho$, hence $1-b\le\Re\rho\le b$. Put $c=(1-b)/2>0$. On $\Re z=2$, triangular Mellin inversion gives $R_\chi(x)$ as the vertical integral of $-(L'/L)(z,\chi)x^{z+1}/[z(z+1)]$, divided by $2\pi i$. The weight is continuous and vanishes at the upper cutoff, including integral $x$.

Shift to $\Re z=c$. The kernel poles and the archimedean gamma poles have real part at most zero. The normalization puts the sole possible pole right of the line at $1$, for $\chi=1$. The fixed-character count in a unit-height slab is $O_{F,\chi}(\log(3+|t|))$. Subtracting the Hadamard logarithmic-derivative expansion at $2+it$ leaves $O(\log(3+|t|))$ after excluding the zeros with $|\Im\rho-t|\le1$. Indeed the distant-zero difference is bounded by a constant times $\sum_{|\gamma-t|>1}m_\rho/(1+|\gamma-t|)^2$, and Stirling bounds the gamma terms. Choose positive and negative heights separated by $\gg 1/\log(3+|t|)$ from nearby ordinates. The horizontal logarithmic derivatives are $O(\log^2(3+|t|))$; the vertical line is horizontally separated from all zeros and has bound $O(\log(3+|t|))$. The horizontal integrals vanish and the shifted integral is absolutely convergent. Consequently
$$
 R_\chi(x)=\delta_\chi x^2/2
 -\sum_\rho \frac{m_\rho x^{1+\rho}}{\rho(\rho+1)}
 +O_{F,\chi,b}(x^{1+c}),\qquad
 \sum_\rho\frac{m_\rho}{|\rho(\rho+1)|}<\infty .
$$
The sum is over distinct zeros, with $m_\rho$ supplying multiplicity. The unit-slab bound proves the displayed summability, including finitely many real and low zeros. For unitary characters of infinite order the requisite Hecke product, gamma factors and zero-count estimates are classical. [Rajan, §§1–2, pp. 281–284](https://bibliotekanauki.pl/articles/1390724.pdf#page=3)

For every $p^k,\ k\ge2$, the total omitted coefficient has modulus at most $[F:\mathbf Q]\log p$. The Chebyshev bound for higher prime powers therefore costs $O_F(x^{3/2})$ in the Riesz weight. This yields $|S_\chi(x)|\ll x^{1+b}$, **including zeros on $b$**. Summing at $x=j^4$ gives $D_\chi(J)\ll J^{4b+5}$; the case $b=1$ follows already from the degree-one Chebyshev bound. Pairing with mlyle’s lower implication proves the equivalences and the clamped formula above. At $\eta=1$ the classical fixed-character prime ideal theorem gives $\sum_{p\le x}\Re a_\chi(p)=\delta_\chi x+o(x)$ after removing higher norms. Integrating gives $S_\chi(x)=o(x^2)$, hence $D_\chi(J)=o(J^9)$. Hecke nonvanishing on the one-line excludes attainment there. [Degree-one transfer, PR #7587](https://github.com/mccorvie/riemann-masullo/pull/7587) · [Infinite-order characters, Rajan, Theorem 1](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/85/3/110150/distribution-of-values-of-hecke-characters-of-infinite-order) · [Prime ideal theorem and real exceptional case, Maynard, Lemmas 4.3–4.5](https://arxiv.org/pdf/1507.05080)

## The all-character endpoint profile

Assume $1/2<\eta<1$. With $b=\eta$ the higher-prime-power error becomes $o(x^{1+\eta})$. Divide the absolutely convergent first-Riesz formula by $x^{1+\eta}$. For $x\ge1$, every summand with $\Re\rho<\eta$ is dominated by $m_\rho/|\rho(\rho+1)|$ and tends to zero individually. Thus
$$
  -S_\chi(x)/x^{1+\eta}=E(\log x)+o(1),\qquad
  E(u)=\Re\!\sum_{\Re\rho=\eta}
         \frac{m_\rho e^{i\Im\rho\,u}}{\rho(\rho+1)} .
$$
This proves little-$o$ in the unattained case. Otherwise $E$ is a uniformly almost-periodic real function. The mean is $m_\chi(\eta)/[\eta(1+\eta)]$, with zero multiplicity taken as zero. For each $\gamma>0$ the coefficient of $e^{i\gamma u}$ in the real series is
$$
 \frac{m_\chi(\eta+i\gamma)+m_\chi(\eta-i\gamma)}
 {2(\eta+i\gamma)(\eta+1+i\gamma)}.
$$
The real projection therefore retains every nonreal ordinate present on the boundary, even when $\chi$ is complex. Its boundary profile cannot vanish identically if the boundary is attained.

Write $f=[E]_+$ and define
$$
 P(u)=\int_0^\infty e^{-s v} f(u-4v)\,dv .
$$
Then
$$
 \frac{D_\chi(J)}{J^s}=P(4\log J)+o(1).
$$
Indeed $[\,\cdot\,]_+$ is 1-Lipschitz. After the substitutions $j=Jt$ and $t=e^{-v}$, the normalized sum is a right Riemann sum for $\int_0^1 t^{s-1}f(4\log J+4\log t)\,dt$. This convergence is uniform in the translating argument: on any $[a,1]$ the bounded uniformly continuous $f$ gives a common modulus of continuity, and both omitted pieces on $[0,a]$ are $O(a^s+J^{-1})$. Summing the little-$o$ terms costs $o(J^s)$ by splitting off a fixed finite prefix.

The clipping of an almost-periodic function is almost periodic, by polynomial approximation on its bounded real range. Integration against $e^{-sv}$ preserves almost periodicity and continuity. If an attained boundary has no real zero and has a nonreal zero, $E$ has mean zero and a nonzero Fourier coefficient. It must be positive somewhere: a nonpositive nonzero almost-periodic function is strictly negative on recurrent intervals of uniform width and bounded gaps, which forces strictly negative mean. If there is a real zero, its positive mean likewise implies positivity somewhere. Uniform almost periodicity follows by approximating with finite trigonometric polynomials and the compactness of their torus orbit closures.

Thus $f$ is bounded below by a positive constant on a relatively dense family of intervals of some fixed positive width. Every integration in $P(u)$ then sees such an interval within a fixed lookback, so $\inf_{\mathbb R} P>0$. A real-only rightmost zero makes $P$ constant with the value claimed. In the nonreal case $E$ and therefore $f$ are nonconstant. The identity $4P'=f-sP$, from the integral definition and continuity, makes $P$ nonconstant. Finally $4\log(J+1)-4\log J\to0$; recurrence at arbitrarily large arguments and uniform continuity imply that the sampled liminf and limsup equal $\inf P$ and $\sup P$. This proves the three cases.

## Principal characters at the critical line

Let $\chi=1$ and $\eta=1/2$. The prime ideal theorem shows that the total $\log Nv$ of degree-one places with $Nv\le y$ is $y+o(y)$, since higher-degree places contribute $O_F(\sqrt y\log y)$. Their squares alone therefore contribute
$$
 \sum_{v:\, f_v=1}\log Nv\,(x-(Nv)^2)_+
   =\int_0^x\sum_{\substack{f_v=1\\Nv\le\sqrt t}}\log Nv\,dt
   =(2/3+o(1))x^{3/2}.
$$
Every other omitted full-Riesz term is nonnegative. The normalized signed deficit is consequently bounded below by $2/3+E(\log x)+o(1)$, where $E$ is the critical-line series above and has mean $4m_{1/2}/3\ge0$. The same recurrence and sampling proof applied to $[2/3+E]_+$ gives $D_\chi(J)\gg_F J^7$. The upper bound follows from the full first-Riesz estimate. The value $2/3$ is a lower contribution for a general field, since degree-two places can contribute at the same order. Signed nonprincipal local coefficients do not provide this positivity. Johnston established the rational continuous sign criterion in 2022; mlyle’s cited paper proof gives the finer rational asymptotic. [Johnston, Theorem 1.2 and Lemma 2.6](https://arxiv.org/pdf/2201.06184) · [Mlyle’s rational calculation](https://github.com/mlyle/riemann-masullo/blob/255d2b1531f3534cd35ea5dd9eb379fadd2c1104/research/5571/rational-fourth-power-deficit.md)

More generally, the finite-order square calculation in #7578 gives an exact critical-line classification. Choose a common Galois closure with group $G$, let $H$ fix $F$, and put $\pi=\operatorname{Ind}_H^G\chi$, using the finite reciprocity character. Set
$$
 \kappa_\chi=|G|^{-1}\sum_{g\in G}\operatorname{tr}\pi(g^2).
$$
This is the real Frobenius–Schur indicator of the representation, possibly reducible. At rational primes unramified in the closure the $p^2$ coefficient divided by $\log p$ is $\operatorname{tr}\pi(\operatorname{Frob}_p^2)$; it includes degree-one squares and first powers of degree-two places. The finitely many ramified $p^2$ terms cost $O(x)$. The Chebyshev estimate for total exponents at least three is $O_F(x^{4/3}\log(2x))$. Chebotarev and the same integral for the square part therefore give $(2\kappa_\chi/3+o(1))x^{3/2}$ for the real omitted term. [Mlyle’s finite-order square coefficient and its two local sources](https://github.com/mlyle/riemann-masullo/tree/9f5ab57df8a162769faaa951ca3332d755055bcb/research/5571/hecke-square-shell) · [PR #7578](https://github.com/mccorvie/riemann-masullo/pull/7578)

At $\eta=1/2$ the preceding sampling formula now holds with $s=7$ and $f=[2\kappa_\chi/3+E]_+$. If $\sup(2\kappa_\chi/3+E)\le0$, then $D_\chi(J)=o(J^7)$. Otherwise $0<\liminf D_\chi(J)/J^7<\limsup D_\chi(J)/J^7<\infty$: there is a nonreal critical zero by the fixed-character zero-count asymptotic, so the series is nonconstant, and taking a positive part with positive supremum preserves nonconstancy. In particular the latter alternative holds whenever $\kappa_\chi+2m_\chi(1/2)\ge0$, since the uncut series then has nonnegative mean. For principal $\chi$, $\pi$ is a transitive permutation representation, $\operatorname{tr}\pi(g^2)=\#\operatorname{Fix}(g^2)\ge\#\operatorname{Fix}(g)$, and Burnside gives $\kappa_\chi\ge1$. Thus the normalized prefix has distinct positive lower and upper limits for every principal field satisfying its own critical-line hypothesis.

The separate finite certificate uses Büthe’s unconditional bounds for $x-\vartheta(x)$ and rational enclosures at seven small anchors. For all $1\le J\le56,234$ in the rational principal case it gives
$$
 \frac1{30}\sum_{j\le J}j^6+\frac{7J}{15}
 \ \le D(J)\le\ \frac{13}{10}\sum_{j\le J}j^6 .
$$
The continuum estimate comes from Büthe’s theorem. The standard-library script verifies the small anchors and both integer cutoff inequalities. The eventual critical upper bound for the actual all-field deficits remains open. [Run the finite certificate](buthe_fourth_power_deficits.py) · [Büthe, Theorem 2, (1.6)–(1.7)](https://arxiv.org/pdf/1511.02032#page=2)
