# An explicit finite Taylor row for the quartic Hardy function

Let $s=(2+z)/(1-z)$ and $F(z)=((1-z)/3)^5 L(s,\chi)$ for the primitive quartic $\chi(2)=i$ modulo five. Consider its actual Hardy coefficients $c_j=[z^j]F$. The following arithmetic algorithm encloses all $0\le j\le M$, with explicit constants starting at $M=1$. The finite table in this calculation uses the period of the actual character. The [companion calculation](CANONICAL-STAGE.md) identifies a literal feasible stage for the distinct original finite ideal table in #7707.

## Choice of a fixed normalization

Put $a=(1+i)/2$. The partial character sums $S(x)=\sum_{n\le x}\chi(n)$ satisfy $|S(x)-a|=1/\sqrt2$. Abel summation gives, for $\sigma=\Re s>0$,
\[
 L(s)=a+s\int_1^\infty(S(x)-a)x^{-s-1}\,dx.
\]
With $t=|s|$ and $\sigma\ge1/4$, $|L(s)|\le(1+4t)/\sqrt2$ and $|s+1|^2\ge t^2+3/2$. The tangent inequality for $x^{3/2}$ at $2$ gives $\sqrt2(t^2+3/2)^{3/2}\ge 3t^2+5/2>1+4t$. Thus the actual quarter-plane bound holds with leading constant one and exponent three. This supplies the individual data of the disk derivative estimate at exponent five and gives $|F|\le1$ on the disk. On $\sigma\ge1/2$, direct differentiation under the integral gives
\[
 |L|\le(1+2t)/\sqrt2,\quad |L'|\le(2+4t)/\sqrt2,\quad
 |L''|\le(8+16t)/\sqrt2.
\]
Writing $w=1-z$, one has $|w|\le2$, $t\le|s+1|=3/|w|$ and
\[
 F''(z)=\big(20w^3L-24w^2L'+9wL''\big)/243,\qquad
 |F''|\le1984/(243\sqrt2)<6 .
\]
Parseval on interior circles, followed by their monotone limit, gives $\sum_{j\ge2}j^2(j-1)^2|c_j|^2\le36$. The distance from one to the Hardy polynomial span of $F$ has square $1-e^{-2G_\chi}$ by the Szegő and actual boundary-log identities. The outer factor $(s+1)^{-5}$ contributes zero logarithmic gap. For the one-sided bounds below it also suffices to divide by every finite right-zero Blaschke product. [Szegő (1920)](https://doi.org/10.1007/BF01199955) · [Actual boundary log in #7696](https://github.com/mccorvie/riemann-masullo/pull/7696)

## Finite coefficient formula

For $x=e^{-t}$ the exponential generating series for $\chi(n)$ is $h(x)/d(x)$, where
\[
 h(x)=x+(1+i)x^2+x^3,\qquad d(x)=1+x+x^2+x^3+x^4.
\]
For $0\le x\le1$ we have $|1-d(x)/3|\le2/3$ and $|h(x)/d(x)|\le4x$. Replace this quotient by the polynomial
\[
 H_J(x)=\frac{h(x)(3^J-(3-d(x))^J)}{3^Jd(x)}
       =\sum_{k=1}^{4J-1}b_kx^k,\qquad J=8(M+1).
\]
Its coefficients are exact Gaussian rationals. The standard gamma integral, applied termwise for $\sigma>1$, gives
\[
 \left|L(s)-\sum_{k=1}^{4J-1} b_k k^{-s}\right|
 \le4(2/3)^J\Gamma(\sigma)/|\Gamma(\sigma+i\Im s)|.
\]
On $|z|\le1/5$, $\sigma\ge3/2$ and $|\Im s|\le5/8$. Euler's product for gamma bounds the logarithm of the ratio by $(\Im s)^2(\sigma^{-2}+\sigma^{-1})/2<\log2$. Cauchy's estimate on that circle, using $|(1-z)/3|^5\le1$, gives the simultaneous complex-norm error
\[
 \eta_M=8\cdot 5^M(2/3)^{8(M+1)}\le4^{-M}.
\]
The finite coefficients follow by expanding $k^{-s}=k^{-2}\exp(-3z\log k/(1-z))$. Its $z^j$ coefficient is $k^{-2}L_j^{(-1)}(3\log k)$. This is used as a recurrence with $L_0=1$, $L_1=-x$ and $(j+1)L_{j+1}=(2j-x)L_j-(j-1)L_{j-1}$. Multiplication by $(1-z)^5/243$ is a finite convolution. [Gamma integral and product](https://dlmf.nist.gov/5.8) · [Laguerre generating function, DLMF 18.12.13](https://dlmf.nist.gov/18.12.E13)

For $M=256$ the calculation uses 8,223 positive integer bases and $\eta_M<6.249\cdot10^{-183}$. Row summation uses exact integer and Gaussian-rational coefficients with Arb enclosures for logarithms and recurrences. An independent complete-period check reaches derivative order eight using the original ordinary Dirichlet series at $2$. For $N$ a multiple of five beyond the maximum of $x^{-2}\log^\ell x$, Abel summation bounds the remaining $\ell$th derivative by $\sqrt2\log^\ell(N+1)/(N+1)^2$. Expanding the original series at $s=2$ compares the two coefficient formulas. [Independent check](coefficient-period-check.json)

## The supplied polynomial

The 11 Gaussian-rational coefficients, in constant-first order, are in [the trial file](trial256.json). For its polynomial $p=\sum_{\ell=0}^{d}p_\ell z^\ell$ and $M>d$ let $V$ be the norm of the visible residual in degrees zero through $M$ using the finite arithmetic row. With $A=\sum|p_\ell|$,
\[
 \|1-pF\|_{H^2}^2
 \le\left(V+\sqrt{M+1}A\eta_M\right)^2+
 \left(6\sum_{\ell=0}^{d}\frac{|p_\ell|}{(M-\ell)(M-\ell+1)}\right)^2.
\]
The visible error is the triangle inequality for convolution. For the invisible coefficient tail after a shift by $\ell$, all contributing indices $j$ satisfy $j\ge M-\ell+1$, so Parseval's derivative bound gives the displayed denominator. Visible and invisible coordinates are orthogonal. The interval checks at 128 and 192 requested output bits give the same enclosures to the 25 printed significant digits, with squared bound $<0.863285910$ and $G_\chi<0.994931733$. The [direct character-sum trial](README.md) provides a sharper upper for the same Green sum.

The finite selector uses floating-point estimates only to search for a polynomial. The verifier works from the listed integers and recomputes the coefficient row with interval arithmetic. Python-FLINT 0.9.0 was used for these runs. Run from this directory

```sh
python certify_hardy.py --trial trial256.json --bits 128 --out replay-128.json
python certify_hardy.py --trial trial256.json --bits 192 --out replay-192.json
python check_coefficients_by_period.py --cutoff 100000 --order 8 --bits 144 --out replay-coef-period.json
```

[128-bit receipt](coefficient-256-128.json) · [192-bit receipt](coefficient-256-192.json) · [Finite coefficient program](quartic_coeffs.py)
