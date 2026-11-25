# A specified stage of the original finite ideal grid

For the actual primitive quartic $\chi(2)=i$ at disk exponent five, the argument $U_n$ of the original [#7707 polynomial grid](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/AppB_AnalyticNT/HeckeFiniteHardyGreen.lean) at $n=15,999,999$ satisfies
\[
 U_n<0.864938490,\qquad G_\chi\le-\tfrac12\log(1-U_n)<1.001012486.
\]
This is a bound for the specified finite expression. It uses an admissible rational coordinate and an analytic estimate for the entire [canonical ideal-norm row](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/AppB_AnalyticNT/FiniteHardyIdealTable.lean#L343). The smaller fresh period row through $256$ was directly evaluated at two precisions. The interval proof below bounds the much larger original row collectively. The period-based [Dirichlet trial](README.md) gives a sharper all-height bound for $G_\chi$.

## Canonical row error with an explicit onset

Write $m$ for the requested row degree, $v=6(m+1)$ for its precision input, $j=\lfloor\log_2(v+2)\rfloor+1$ and $u=2^j$. The squared Euler pole filter in the actual table is $G(s)=(1-2^{1-s})^2 L(s,\chi)$. The moving-disk parameter for the rational field is $D=5$. The repository's elementary two-disk extrapolation proves, from a bound $|G|\le(2u)^{5u}$ on all circles with center $c=4u+1/2+it_0$, $|t_0|\le u$, and radius $8u$, that the error in the corrected analytic function throughout $|s-(4u+1/2)|\le4u$ is at most $(2+\mathrm{Mass})2^{-3(j+1)u}$. Here $\mathrm{Mass}$ sums absolute corrected Dirichlet coefficients at exponent two. The definitions include the terms $a_n$, $-4a_{n/2}$ and $4a_{n/4}$ with their divisibility conditions, hence $\mathrm{Mass}\le(1+1+1/4)\zeta(2)<9/2$. [Original extrapolation inequality](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/AppB_AnalyticNT/FiniteHardyIdealTable.lean#L30)

For this specific character the needed disk bound already holds whenever $u\ge2^{20}$. Indeed $|1-s|\le13u$, $|s|\le14u$ and $\Re s\ge1/2-4u$ on these disks. For $\sigma\ge-1/2$ let $a_0=(3+i)/5$ be the period mean of the unweighted character summatory function and integrate $S(x)-a_0$ once from $1$. This gives a bounded five-periodic primitive $B$, $|B|\le10$. Abel summation and continuation yield $L(s)=a_0+s(s+1)\int_1^\infty B(x)x^{-s-2}dx$. Hence $|L(s)|\le1+20|s||s+1|$ there and $|1-2^{1-s}|^2<16$.

For $\sigma\le-1/2$, the functional equation for the primitive odd character, followed by the gamma reflection and duplication formulas, gives
\[
 |L(s,\chi)|=\frac{\sqrt5}{\pi}\left(\frac{2\pi}{5}\right)^\sigma
    |\Gamma(1-s)\cos(\pi s/2)L(1-s,\bar\chi)|.
\]
The prefactor is at most one and $|L(1-s,\bar\chi)|\le\zeta(3/2)\le3$. Put $x=1-\sigma\ge3/2$ and $h=|\Im s|$. Rotating the integral for $\Gamma(x+i h)$ by $\alpha=\arctan(h/x)$ gives $|\Gamma(x+i h)|\le e^{-\alpha h}(\cos\alpha)^{-x}\Gamma(x)$. Also $h(\pi/2-\alpha)\le x$ and $|\cos(\pi s/2)|\le e^{\pi h/2}$. The upper Stirling inequality $\Gamma(x)\le3x^{x-1/2}e^{-x}$ at $x\ge3/2$ follows from the first remainder bounded by $1/(12x)$. Therefore $|\Gamma(1-s)\cos(\pi s/2)|\le3 |1-s|^x$. The squared Euler factor is bounded by $4\cdot4^x$. Together these estimates give
\[
 |G(s)|\le36(52u)^{4u+1}\le(2u)^{5u}.
\]
In the last step $52^4/(32u)\le1/4$ and $36\cdot52u\le4^u$ once $u\ge2^{20}$. The elementary positive-side polynomial estimate above is smaller than the same bound. [Primitive functional equation](https://dlmf.nist.gov/25.15.E5) · [Gamma identities](https://dlmf.nist.gov/5.5) · [Real Stirling remainder](https://dlmf.nist.gov/5.11.ii)

At $|z|\le1/5$, $s=(2+z)/(1-z)$ lies in the disk used for the error and $\Re s\ge3/2$. Removing the squared pole filter and multiplying by $((1-z)/3)^5$ amplifies the extrapolation error by at most $(1-2^{-1/2})^{-2}<12$. Thus its error at the nodes $|z|=1/8$ is at most $78\,2^{-3(j+1)u}\le2^{-v}$ at our stage. The true normalized function has modulus at most one on $|z|\le1/5$, by the [independent quarter-plane bound](FINITE-COEFFICIENTS.md). Extracting coefficient $h\le m$ at the $12(m+1)$ equidistant nodes incurs error at most
\[
 8^h\big(2^{-6(m+1)}+(8/3)(5/8)^{12(m+1)}\big)\le 4^{-m}.
\]
This is the geometric Cauchy aliasing bound used by the original table. It applies to every requested index and both real and imaginary components through their complex norm. [Finite Fourier inequality](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/ForMathlib/Analysis/Complex/DiskFiniteFourier.lean#L107)

## The literal grid

Here $m=2n+1=31,999,999$, $v=192,000,000$ and $u=268,435,456$. The denominator $10,000$ of the zero-padded degree-ten trial divides $(n+1)^3$. Its weighted cost $\sum_{j=0}^{10}(j+1)^2|p_j|^2=14,122,607.25810284$ is below $n+1=16,000,000$, so the exact [grid index](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/ForMathlib/Analysis/InnerProductSpace/HardyPolynomialGrid.lean#L31) admits it. Its full genuine residual is bounded by the square root of the [192-bit receipt](coefficient-256-192.json). The visible norm on the canonical row is at most that bound plus $\sqrt{m+1}\sum_j|p_j|\,4^{-m}$. The true grid minimum $b_n$ is no larger than this candidate norm. Substitution in the specified original equation
\[
 U_n=(b_n+2\sqrt{(n+1)(m+1)}\,4^{-m}+32/(9\sqrt{n+1}))^2
\]
gives the quoted numerical upper. The [replay](certify_canonical_grid.py) conservatively replaces $4^{-m}$ by $10^{-40}$ throughout.

The genuine Hardy distance is at most the row expression by its visible/hidden tail proof at derivative bound $16/9$, obtained directly at scalar one and exponent five in the [quartic normalization](FINITE-COEFFICIENTS.md). The numerical conclusion needs the observed growth and derivative inputs for this exponent. It makes no identification of a noncanonically chosen all-field threshold. Proving arbitrarily small residuals remains the open arithmetic problem.

```sh
python certify_canonical_grid.py --trial trial256.json --receipt coefficient-256-192.json --out replay-canonical.json
```

[Canonical-grid interval receipt](canonical-grid-receipt.json)
