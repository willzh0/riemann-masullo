# Finite Hardy certificates for the quartic Dirichlet character modulo five

For the primitive character $\chi(2)=i$, the exact 512-term Dirichlet polynomial in this directory proves
\[
 1-e^{-2G_\chi}<0.076414365217,\qquad G_\chi<0.039745877564 .
\]
Here $G_\chi=\sum_{\Re\rho>1/2}m_\rho\log|(\rho+1)/(2-\rho)|$ includes every ordinate of this character and the full multiplicity. Two integer programs agree on the complete finite part of the residual. They bound the infinite remainder analytically with different constants. Both inputs to the certificate are finite arithmetic. This branch gives a written proof and executable checks for Theorem 12.5.1.1, pp. 519–520. [Actual Green identity in #7696](https://github.com/mccorvie/riemann-masullo/pull/7696)

A second calculation certifies a trial directly in the Taylor-coefficient model for the same Hardy distance. It uses 8,223 positive integer bases to enclose 257 actual coefficients. The original [#7707 finite ideal grid](https://github.com/mccorvie/riemann-masullo/pull/7707) also has a specified successful finite stage. [Coefficient certificate](FINITE-COEFFICIENTS.md) · [Original finite grid stage](CANONICAL-STAGE.md)

At **every** original grid index $n\ge10^{1200}$ the same character satisfies $U_n<0.076415386910838$. A radial approximation transfers the 512-term trial into admissible original polynomial coordinates with an explicit truncation and rounding budget. [Uniform bound on all late original rows](COFINAL-CANONICAL.md)

At the original rows $n\ge2^{600000}$ an independently explicit clipped-predictor proof bounds $0\le U_n-(1-e^{-2G_\chi})<10^{-19}$, even before using any zero count. The verified-height result then bounds these actual rows by $4.1975849790140\cdot10^{-7}$. The same proof supplies a fixed-character rate shape over every number field. [Clipped outer prediction and explicit tail](CLIPPED-OUTER.md)

A separate written argument constructs a convergent sequence of finite Gram-matrix bounds over arbitrary number fields. Its arithmetic inputs and convergence statement are given on their own page. [All-field Gram construction](../finite-ideal-gram/README.md)

The quartic bound obtained independently from Platt's verified zeros and the two-sided zero-count tail is $G_\chi<2.09879293\cdot10^{-7}$. The following calculation uses the period of $\chi$ and the ordinary coefficients. Establishing $G_\chi=0$ remains open. [Verified-height calibration](https://github.com/willzh0/riemann-masullo/tree/da8d5a8b3252c16120606b0b513d445e88cfbd0f/research/5571/quartic-green-calibration)

## Exact physical residual

Take $s=\tfrac12+it$, $z=(s-2)/(s+1)$ and $d\mu=3\,dt/(2\pi|s+1|^2)$. Under this Cayley map $d\mu$ is Haar probability on the disk boundary. For a finite trial $p(s)=\sum_r a_r r^{-s}$ with $r\ge1$, set
\[
 B_m=\sum_{j=1}^m j\chi(j),\qquad
 T_p(x)=1-\sum_r r a_r B_{\lfloor x/r\rfloor}.
\]
Then
\[
 1-e^{-2G_\chi}
 \ \le\ \int_\mathbb R|1-p(s)L_\chi(s)|^2d\mu(t)
 \ =\ 3\int_1^\infty |T_p(x)|^2\,\frac{dx}{x^4}.
\]
For $\Re s>1$ the Mellin transform of $x^{-1}T_p(x)$ on $x\ge1$ is $(1-p(s)L_\chi(s))/(s+1)$ by absolute summation. The period estimates below imply $T_p(x)=O_p(x)$, so the inverse function belongs to the weighted $L^2$ spaces on every line $\Re s\ge1/2$ with a uniform bound. Fourier–Laplace Plancherel on $\log x\ge0$ gives the displayed norm and the analytic Hardy representative on $\Re s>1/2$. Uniqueness on the Euler half-plane identifies the continuation. In the disk this makes $pL_\chi$ an $H^2$ function. It vanishes to full order at each right-hand zero. For every finite multiset $J$ of those sites, $pL_\chi$ belongs to $B_JH^2$ for their finite Blaschke product. The squared distance from one to that subspace is $1-|B_J(0)|^2$. Taking the supremum over such $J$ gives the first inequality. This is the Hilbert-space argument behind classical Beurling–Nyman criteria. [Delaunay, Fricain, Mosaki and Robert, Theorems 2.2, 2.4 and §7.2](https://arxiv.org/abs/1101.1199) · [Burnol, Theorem 3.2](https://arxiv.org/pdf/math/0001013#page=15)

The trial's dilations are the integers $1,\dots,512$. Its real and imaginary numerators are specified entry by entry with common denominator 100,000. For a rational common dilation denominator $q$, the formula also works with $r=d/q$. On each half-open cell $[n/q,(n+1)/q)$, $n\ge q$, the step function is constant. Its squared norm contribution is $q^3 |T_p(n/q)|^2(n^{-3}-(n+1)^{-3})$. The arithmetic progression verifier computes the increments using the four nonzero character values and rounds **up** at 96 fractional bits before dividing by the exact coefficient scale. It covers all cells through $n=5,000,000$, inclusive.

For the period proof set $S_m=\sum_{j\le m}\chi(j)$. In residue order $r=0,1,2,3,4$ the lists are
\[
 S_r=(0,1,1+i,1,0),\qquad B_r=(0,1,1+2i,1-i,-3-i).
\]
Every whole period has zero character sum and first moment $-3-i$. Thus
\[
 B_{5u+r}=u(-3-i+5S_r)+B_r .
\]
The progression verifier uses $|B_m|\le\sqrt2\,m$. Indeed $S_j$ is at distance $1/\sqrt2$ from $(1+i)/2$ for every $j$ including $0$. Write $B_m=mS_m-\sum_{j=0}^{m-1}S_j$ and subtract that center in both terms. An upper bound $(3/2)\sum_r(|\Re a_r|+|\Im a_r|)$ on the resulting slope gives $1-e^{-2G_\chi}<0.079532629678$ and $G_\chi<0.041436863358$. [First exact receipt](dilates-1-512-receipt.json)

The second program uses the full periods to evaluate every cell independently. Write $B_m=m\lambda_r+\eta_r$ where $\lambda_r=(-3-i+5S_r)/5$, $\eta_r=B_r-r\lambda_r$. The maxima of $|\lambda_r|$ and $|\eta_r|$ are $\sqrt{20}/5$ and $\sqrt{10}/5$. Consequently $|T_p(x)|\le D+Ex$ with
\[
 D=1+\tfrac{633}{1000}\sum_r r|a_r|,\qquad E=\tfrac{179}{200}\sum_r |a_r|.
\]
The code rounds each coefficient modulus upward by an integer square root. For the remainder starting at $X=(n_\mathrm{last}+1)/q$, direct integration yields $D^2/X^3+3DE/X^2+3E^2/X$. The two integer evaluations give exactly the same rational answer for all five million finite cells. This sharper tail gives the bounds at the top. Both logarithm conversions use finitely many terms of $-\log(1-u)$ with a positive geometric remainder. [Second exact receipt](dilates-1-512-period-receipt.json)

## Replay

The certificate consists of the supplied [integer coefficient list](dilates-1-512.json), the two verifiers and their receipts. The first program uses Python's standard library. The independent check uses NumPy for bounded 64-bit vector operations, with an explicit overflow check, and Python arbitrary-precision integers for the accumulated rational upper. Both programs are deterministic. From this directory run

```sh
python certify_dilates.py --trial dilates-1-512.json --cutoff 5000000 --bits 96 --out replay-progressions.json
python certify_periods.py --trial dilates-1-512.json --receipt replay-progressions.json --out replay-periods.json
```

The optional least-squares [trial selector](select_dilates.py) used a floating-point Gram matrix, selected candidates with different diagonal penalties and rounded the coefficients. Both independent verifiers start from the supplied integers. To repeat the search, use mesh one, reach 512, training height 12,000 and tail scale 5,000,000.

An [effective finite-conductor accuracy theorem](CONDUCTOR-GRID.md) gives the same exponent and certified finite-grid error below $2\cdot10^{-19}$ for all primitive characters through conductor 400,000, including the principal character. A growing-conductor schedule gives one finite maximum per index and a uniform accuracy bound without a preliminary zero calculation.
