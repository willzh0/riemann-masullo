# Effective accuracy of one finite Hardy grid for all primitive characters of bounded conductor

For each primitive Dirichlet character $\chi$ with conductor $q\le400000$, including the principal character of conductor one, let $G_\chi$ be the pole-corrected half-plane Green sum from the reference point two. Use the original finite ideal grid $U_{\chi,N,n}$ with **the same exponent $N=70$** for every character. At **every $n\ge2^{750000}$**,
\[
 0\le U_{\chi,70,n}-(1-e^{-2G_\chi})<2\cdot10^{-19}.
\]
The input consists of the ordinary Dirichlet coefficients and classical inequalities. There are no inputs about zeros or zero counts. The formula bounds the true error of the finite measurements without enumerating the grids at these indices. An arithmetic upper tending to zero would be needed to prove exterior cancellation. [Original finite grid](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/AppB_AnalyticNT/HeckeFiniteHardyGreen.lean) · [Half-plane identity](https://github.com/mccorvie/riemann-masullo/pull/7696) · [Exact rational receipt](conductor-grid-receipt.json)

## Common analytic and finite-row bounds

Take a conductor cap $Q\ge3$. Write $A_\chi(s)=((s-1)/s)^\delta L(s,\chi)$ with $\delta=1$ for the primitive principal character and zero otherwise. For a nonprincipal character the period sum vanishes, so $|S(x)|=|\sum_{n\le x}\chi(n)|\le q$. Abel summation gives $L(s)=s\int_1^\infty S(x)x^{-s-1}\,dx$ in $\Re s>0$. For the principal character,
\[
 A_1(s)=1-(s-1)\int_1^\infty\{x\}x^{-s-1}\,dx
\]
by partial summation, including the removable value at one. In $\Re s\ge1/4$ these formulas give $|A_\chi(s)|\le 4Q|s+1|$, since $|s|\le|s+1|$, $|s-1|\le |s+1|+2$ and $|s+1|\ge5/4$. Choose $N\ge3$ with $(5/4)^{N-3}\ge 4Q$. Then $|A_\chi(s)|\le |s+1|^{N-2}$ on this quarter-plane. The normalized Cayley function $F(z)=A_\chi(s)/(s+1)^N$, $s=(2+z)/(1-z)$, has disk sup norm at most one and derivative bound $16/9$. The quarter-radius Cauchy estimate for $A_\chi(s)/(s+1)^{N-2}$ also shows that $F$ extends continuously at the missing boundary point. [Disk estimates](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/AppB_AnalyticNT/HeckeFiniteHardyGreen.lean#L98)

The canonical extrapolation uses $m=2n+1$, $v=6(m+1)$, $j=\lfloor\log_2(v+2)\rfloor+1$, $u=2^j$, and $D=5$ for the rational field. To check its actual row approximation uniformly, bound $G(s)=(1-2^{1-s})^2 L(s,\chi)$ on each disk of radius $8u$ about $4u+1/2+it_0$, $|t_0|\le u$. Here $|1-s|\le13u$, $|s|\le14u$, and $\Re s\ge1/2-4u$. We prove $|G(s)|\le(2u)^{5u}$ for every $u\ge2^{20}Q^4$.

For $\Re s\ge-1/2$, the $q$-periodic summatory function of a nonprincipal input has mean $a$, $|a|\le q$. The function $B(x)=\int_1^x(S(t)-a)\,dt$ is $q$-periodic with $|B|\le2q^2$. A second partial summation gives $L(s)=a+s(s+1)\int_1^\infty B(x)x^{-s-2}\,dx$. Thus $|L(s)|\le Q+4Q^2|s(s+1)|$. For the principal input apply the same argument to $\eta(s)=(1-2^{1-s})\zeta(s)$ with its alternating coefficients of period two. In this half-plane $|1-2^{1-s}|<4$, so both cases give $|G(s)|\le16(Q+4Q^2|s(s+1)|)\le16000u^4$ at the stated threshold.

For $\sigma=\Re s\le-1/2$, put $x=1-\sigma$. The primitive functional equation, reflection, and duplication for gamma give
\[
 |L(s,\chi)|\le 2Q^x|\Gamma(1-s)|
 e^{\pi|\Im s|/2}\zeta(3/2).
\]
Indeed the exact conductor prefactor is $(\sqrt q/\pi)(2\pi/q)^\sigma=(2/\sqrt q)(q/(2\pi))^x$ and the trigonometric factor is sine or cosine according to parity. For $h=|\Im s|$, rotate the gamma integral by $\arctan(h/x)$ with the sign of the imaginary part. This bounds $|\Gamma(x+ih)|$ by $\Gamma(x)e^{-h\arctan(h/x)}(1+(h/x)^2)^{x/2}$. Use $\Gamma(x)\le3x^{x-1/2}e^{-x}$ for $x\ge3/2$ and $h(\pi/2-\arctan(h/x))\le x$. The product with $e^{\pi h/2}$ is at most $3|1-s|^x$. Since $\zeta(3/2)\le3$, the squared Euler filter costs at most $4\cdot4^x$ and $x\le4u+1$, we get $|G(s)|\le72(52Qu)^{4u+1}$. At $u\ge2^{20}Q^4$ one has $(52Q)^4\le8u$ and $72\cdot52Qu\le4^u$, giving the claimed disk bound. [Primitive functional equation, DLMF (25.15.5)](https://dlmf.nist.gov/25.15.E5) · [Gamma reflection and duplication](https://dlmf.nist.gov/5.5) · [Positive-axis Stirling remainder](https://dlmf.nist.gov/5.11.ii)

The absolute mass of the corrected coefficients at two is at most $(1+1+1/4)\zeta(2)<9/2$. The two-disk extrapolation gives error at most $(2+9/2)2^{-3(j+1)u}$ throughout the target disk. At $|z|\le1/5$ the image lies in that disk with $\Re s\ge3/2$, and division by the squared Euler filter costs less than $12$. The normalizer and principal pole factor have modulus at most one there. The norm error of the node values is therefore at most $2^{-v}$. The finite Fourier alias estimate proves complex error $\le4^{-m}$ for each of the original canonical coefficients through $m$. In particular this holds for all $n\ge2^{20}Q^4$. The calculation recovers the hypotheses of the grid upper for the prescribed $N$. [Two-disk inequality](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/AppB_AnalyticNT/FiniteHardyIdealTable.lean#L30) · [Finite Fourier estimate and its numerical expression](CANONICAL-STAGE.md)

## A computable common accuracy index

For $I_j=[j-1/2,j+1/2]$ consider the ordinary disk of radius $1.9$ around $2+ij$, where $\Re s\ge0.1$. The Abel formulas bound $|A_\chi|\le B_j=50Q(|j|+2)$ there. At the center $|A_\chi(2+ij)|>1/4$ by the absolutely convergent reciprocal Euler product and $|(1+ij)/(2+ij)|\ge1/2$. Write $A_j=\log(4B_j)$ and $Y_\chi(t)=-\log|F(z(t))|$ at the finite boundary coordinate $s=1/2+it$. All disk zeros have finite orders. Jensen on radius $1.9$ gives at most $20 A_j$ zeros through radius $1.8$, since $\log(19/18)>1/20$. Removing their local finite Blaschke factors on a zero-free circle of radius between $1.75$ and $1.8$ and applying Harnack on the central segment gives
\[
 | \{t\in I_j:Y_\chi(t)>(24+N)A_j+y\} |
 \le160 A_j e^{-y/(20A_j)}\qquad (y>0).
\]
Indeed $|1/2+it-(2+ij)|\le\sqrt{5/2}<1.6$ on the segment. Each Blaschke factor is at least its distance to that zero divided by four. The last normalization contributes $N\log|3/2+it|\le N A_j$. This argument also covers the principal character because $A_1$ is analytic throughout and has the same boundary modulus as $\zeta$. [Local sublevel proof](CLIPPED-OUTER.md)

For accuracy $0<\epsilon\le1$, let $J\ge2$ and $A=\log(600QJ)$, and take the first integer $J$ with $4(3224+N)(A^2+2A+2)/J\le\epsilon/32$. This terminates as $J\to\infty$. The Cauchy density is bounded by one on $I_0$, by $2/j^2$ off it, and the sum of all interval bounds is below nine. On $|j|\le J$, $A_j\le A$. On the remaining blocks the sublevel bound gives $\int_{I_j} Y_\chi(t)\,dt\le(3224+N)A_j^2$. Integration of the decreasing function $\log^2(600Qx)/x^2$ from $J$ bounds their total contribution by the displayed choice of $J$. Thus the mean $e_H=\int(Y_\chi-H)_+$, against Cauchy probability of scale $3/2$, satisfies
\[
 e_H\le9\cdot3200 A^2e^{-(H-(24+N)A)/(20A)}
       +4(3224+N)(A^2+2A+2)/J,\qquad H\ge(24+N)A.
\]
Choose $H=(24+N)A+20A\log(10^6 A^2/\epsilon)$. The finite predictor construction with smoothing tolerance $\epsilon/64$ contributes at most $2(e_H+\epsilon/64)$ to squared error before truncation. All truncation, grid rounding and true ideal row errors cost at most $12/\sqrt n$ in norm. Its untruncated squared residual is at most one, and the distance is always a lower bound after the grid's own correction. Consequently $0\le U_{\chi,N,n}-(1-e^{-2G_\chi})\le\epsilon$ at every
\[
 n\ \ge\ \max\!\big\{2^{20}Q^4,\ 20e^{4H},\ (1000/\epsilon)^2\big\}.
\]
The result makes the common parameter, the coefficient onset and an approximation modulus effective for each finite conductor bound. [Clipped predictor, Hardy truncation and finite rounding](CLIPPED-OUTER.md)

## Rational replay at conductor 400,000

Set $Q=400000$, $N=70$, $J=2^{100}$, $H=125000$ and smoothing tolerance $10^{-24}$. Here $(5/4)^{67}>4Q$, $\log(600QJ)<90$ and $(H-94\cdot90)/(20\cdot90)>64$. The previous near and far block bounds, rounding $e$ down to $2.7$ in the negative exponential, give $e_H<5.772\cdot10^{-20}$. For every $n\ge2^{750000}$ the ellipsoid admits the predictor and the finite norm error is below $10^{-24}$. Exact rational arithmetic gives squared error below $1.15423\cdot10^{-19}$ (rounded upward), hence the simpler displayed bound. [Standard-library verifier](certify_conductor_grid.py) · [Rational output](conductor-grid-receipt.json)

## One finite maximum for growing conductors

Take an integer $k\ge2$ and put $Q_k=2^k$, $N_k=20k$, $J=2^{20k}$, $H=8000k^2$ and $n_k=2^{48000k^2}$. For every primitive $\chi$ through conductor $Q_k$ and every $n\ge n_k$ the actual row satisfies
\[
 0\le U_{\chi,N_k,n}-(1-e^{-2G_\chi})<2^{-k}.
\]
Indeed $(5/4)^4>2$ gives the common quarter-plane exponent, and $n_k\ge2^{20}Q_k^4$. In the clipping estimate use $A=\log(600Q_kJ)\le25k$, since $\log600<7$. Then $(24+20k)A\le800k^2$ and $(H-(24+20k)A)/(20A)\ge14k$. The contribution of $|j|\le J$ is bounded by $18\,000\,000\, k^2\,2^{-19k}$, as $e^{14}>2^{19}$. The remainder is at most $4\cdot1632\cdot651\, k^3\,2^{-20k}$. Each expression is below $2^{-k}/16$ for $k=2$, and this persists by the geometric growth of the denominator. Finally $50e^{4H}\le n_k$ and $12/\sqrt{n_k}<2^{-k}/64$. Choosing smoothing tolerance $2^{-k}/64$ proves the stated error bound. [Rational base and growth checks](certify_conductor_grid.py)

Let $M_k$ be the maximum of $U_{\chi,20k,n_k}$ over the finite set of primitive characters with conductor at most $2^k$. All its entries are functions of the finite ordinary ideal coefficients, with the Gaussian-rational grid from the original definition. As $k$ grows,
\[
 \lim_{k\to\infty} M_k=\sup_{\chi\ {\rm primitive}}(1-e^{-2G_\chi}).
\]
The finite maxima of the true squared distances increase to their supremum, and the common error tends to zero. Consequently all primitive Dirichlet functions have their nontrivial zeros on the critical line if and only if $M_k\le2^{-k}$ at every $k\ge2$, or equivalently at arbitrarily large $k$. A single rigorous $M_k>2^{-k}$ would certify that some primitive input of conductor at most $2^k$ has a right-hand zero. These maxima have not been evaluated at the indicated stages. The full upper comparison remains open. [Earlier qualitative aggregation over normalized Hecke characters](https://github.com/mccorvie/riemann-masullo/pull/7683)
