# Both signs at every terminal point through $2.32\cdot10^{67}$

For either primitive quartic character modulo five, both signed terminal integrals in the [one-terminal criterion](../ADAPTIVE-WIDTHS.md#one-prescribed-terminal-sample-using-only-primes-up-to-its-square), and both prescribed left-endpoint grids for each sign, satisfy
$$
             {\cal A}_\pm(x)<\sqrt x
             \qquad (2\le x\le 2.32\cdot10^{67}).
$$
Here $x$ is real. For $10^{24}\le x\le10^{60}$ the coefficient is below $0.00784$. The sufficient upper at the final interval is $0.999674$. This is a finite result for the entire variance integral. The portion with $v\ge a\log x$, $a=(1.0197H^2)^{-1}$, has a separate unconditional all-height asymptotic. The remaining cofinal estimate for the entire integral is open. [All-height separation](MOVING-VARIANCE.md)

Let $H=20{,}000{,}000$, $\chi(2)=i$, $K(u)=\int_1^2(1-uv)_+\,dv$, and $Q(y)=\sum_p\chi(p)(\log p)K(p/y)$. The other quartic has the same real row. Write $c=e^{-v/2}$, $\nu_{\sqrt v}=(1+c)N(0,v)-cN(0,2v)$, $q_v(x)=\Re\int Q(xe^h)d\nu_{\sqrt v}(h)$. The statistic integrates the positive part of either sign up to $v=\log x$ with weight $W=e^{-4v}$ and cutoff $N=x^2$, or $W=e^{-4v-v^2}$ and $N=\lceil\min(x^2,x\exp(6(\log x)^{3/4}))\rceil$. In the range of the theorem the second cutoff is $\lceil x^2\rceil$. The proof allows the extra prime this ceiling can include. Mlyle’s historical fixed-quartic calibration is for the triangular weight at fourth powers. The annular input here comes from the earlier two-knot proof, its independent interpolation audit, and the thirteen-zero calculation. [Quartic fourth-power proof](https://github.com/mlyle/riemann-masullo/tree/3f90b6c75f2e36f52c2c9cb427155a556bcee9d8/research/5571/quartic-mod-five-deficit) · [Earlier raw annular result](https://github.com/willzh0/riemann-masullo/tree/842ce30ef40dfa1e2a9138d37ebb1960d37b9315/research/5571/quartic-annular-bound) · [Signed annular proof](../README.md)

## Finite primes and the prescribed grid

Both weights are bounded by $e^{-4v}$. Integrating the absolute Gaussian majorant $(1+c)N(0,v)+cN(0,2v)$ against this weight gives the density $\sum c_j e^{-a_j|h|}$, with
$$
 (c_j,a_j)=(1/\sqrt8,\sqrt8),\ (1/3,3),\ (1/\sqrt{18},\sqrt{9/2}).
$$
For $p>N\ge x^2$ only $h\ge\log(p/x)>0$ contributes. Substitution $u=(p/x)e^{-h}$ gives $c_j(x/p)^{a_j}M(a_j)$ exactly for each positive majorant, where $M(s)=(2^{1-s}-1)/[(1-s)s(1+s)]$. By $\vartheta(y)\le(\log4)y$ and partial summation,
$$
       T(x)=(\log4)\sum_j c_j M(a_j)\frac{a_j}{a_j-1}x^{2-a_j}
$$
bounds the omitted prime contribution to either signed positive integral. Every term decreases. We bound the finite integral by the full-prime absolute estimates on the retained variance interval plus $T(x)$. Extending an upper for its nonnegative majorant to all $v\ge0$ also covers the variance endpoint. [Chebyshev bound and annular transform](../QUARTIC_LINEAR_HEIGHT.md)

The grid evaluates at the left endpoints $\delta=k/\lceil N\rceil$, where $v=\delta^2$, with the exact $W\,dv$ mass of each cell up to the final endpoint. Because $0\le K\le1$ and $|(K(e^r))'|\le3/4$, the Lipschitz constant in $\delta$ for one compensated prime weight is
$$
    D=e^{-1/2}+\tfrac34(2+\sqrt2)\sqrt{2/\pi}.
$$
Differentiate $F_1+c(F_1-F_{\sqrt2})$ for $F_t=\mathbb E K((p/x)e^{-t\delta Z})$, $Z\sim N(0,1)$. The difference obeys $|F_1-F_{\sqrt2}|\le1$. Thus the grid error is bounded by $D\vartheta(N)/(4\lceil N\rceil)\le D\log4/4<0.919$. It remains valid for either sign and for a portion of the integral if a cut cell is assigned its exact partial weight with its original left-endpoint evaluation.

For all $y>0$ the older unsmoothed real estimate gives $|\Re Q(y)|\le(5/8)\sqrt y+6.8\cdot10^{-15}y$. Its positive Gaussian majorant integrates the $y^t$ moment to $x^t{\cal J}(t)$, where
$$
 {\cal J}(t)=(4-t^2/2)^{-1}+(9/2-t^2/2)^{-1}+(9/2-t^2)^{-1}.
$$
For $5\le x\le10^{24}$, even including $T(x)$ and the grid, the normalized total is $<0.890$. At $2\le x\le\sqrt{10}$ neither finite cutoff includes a prime with nonzero real character. From $\sqrt{10}$ to 5 the only possible real primes are 11 and 19, and the mesh denominator is at least 10, giving grid error $D\log(209)/40$ and a normalized total $<0.688$. This checks real nonintegral cutoffs and the last partial cell. [Raw real upper](../QUARTIC_LINEAR_HEIGHT.md)

## Narrow and wide variances

For $x\ge10^{24}$ split at $u=(k/H)^2$, around $6.3\cdot10^{-14}$. On $0\le v\le u$, compare the two original prime knots with a nearby anchor width $\sigma$, $H\sigma\approx5.1$. The signed knot error $D_v(r)$ increases with variance for $r>0$ and is odd in $r$. The mass of the difference is therefore the difference of its unsigned masses. For either real direction only one residue class contributes positively on each side of each knot. An explicit one-class Brun–Titchmarsh bound, integrated across $v$, gives the narrow prime term. The anchor itself is bounded by the smoothed explicit formula. Directly shifting the earlier raw pointwise bound gives a weaker narrow term and verifies the starting scale. [Ordering proof, prime intervals, anchor, and tails](SMALL-VARIANCE.md) · [Montgomery and Vaughan, Theorem 2](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf#page=3)

For the rest of the integral first separate the right-hand primary zeros above $H$. For a zero $\rho=\beta+i\gamma$, the Gaussian multiplier is
$$
 \Phi_v(\rho)=e^{v\rho^2/2}+e^{v(\rho^2-1)/2}-e^{v(\rho^2-1/2)}.
$$
Against $e^{-4v}$ the three absolute terms are bounded by $e^{-v(h+r\gamma^2)}$, with $(h,r)$ respectively $(7/2,1/2),(4,1/2),(7/2,1)$. Their integrals from $u$ are bounded by $e^{-u(h+r\gamma^2)}/(r\gamma^2)$. For $T\ge H$ define
$$
 Z_u(T)=T^{-4}\sum_{h,r}\frac{e^{-u(h+rT^2)}}r
 \left\{\frac{\log T/(m-1)+(m-1)^{-2}}{\pi}
       +\frac{0.55}{T}(2\log T+1/m)\right\},
 \qquad m=5+2urT^2
$$
using the indicated $m$ in each summand. The two-sided zero count and $z^2\ge1+2\log z$ for $z\ge1$ show that $Z_u(T)$ bounds the sum of the integrated multiplier times $|\gamma|^{-3}$ over all $|\gamma|>T$. This follows by partial summation against the published counting function, as in the inverse-moment formula, which holds for every real $m>1$. [Bennett, Martin, O’Bryant and Rechnitzer, Theorem 1.1](https://arxiv.org/pdf/2005.02989#page=2) · [Inverse-moment calculation](../CUMULATIVE.md)

Take $b=1.235,\ d=1/[5.60\log(5bH)]$. The functional equation reflects each right zero to a left zero at the same signed ordinate. Kadiri bounds $\beta\le1-d$ on $H<|\gamma|\le bH$, and $x^\beta(1+2^{1-\beta})$ increases in $\beta$ for $x\ge2$. The integrated right-hand contribution divided by $\sqrt x$ is therefore at most
$$
  \tfrac12(1+2^d)x^{1/2-d}Z_u(H)+\sqrt x Z_u(bH).
$$
Both signs of the ordinate and all multiplicities are counted. [Platt, Theorem 7.1 in the preprint and 10.1 in the published version](https://arxiv.org/pdf/1305.3087#page=14) · [Kadiri, Theorem 1.1](https://www.cs.uleth.ca/~kadiri/articles/explicit_zerofree_regions_for_dirichlet_l_functions.pdf#page=1)

The exact real formula contains the primary $-M(\rho)x^\rho$, the secondary $+\tfrac12M(\rho_\eta/2)x^{\rho_\eta/2}$ for $\eta=\chi^2$, and the gamma and odd proper-power remainder. The prime five always has zero coefficient. For all $y>0$ the latter remainder is bounded by $3+2y^{1/3}$. For $y\ge2$ this follows from the gamma bound in equation (3) and odd-power bound (6), using $(\log y)/(2y^{1/3})\le3/(2e)$ and $(\log y)/y\le1/e$. For $0<y\le2$, the prime row vanishes and the two absolute coefficient sums bound its discrepancy with the zero series by $1$. Hence the integrated normalized elementary cost is at most $3{\cal J}(0)/\sqrt x+2{\cal J}(1/3)x^{-1/6}$. [Actual prime and proper-power identity](../QUARTIC_LINEAR_HEIGHT.md)

For the verified critical primary terms put $g=\gamma^2-1/4$ and
$$
 C(g)=(4+g/2)^{-1}+(9/2+g/2)^{-1}+(9/2+g)^{-1}.
$$
Summing $|M(1/2+i\gamma)|C(g)$ over the 13 isolated two-sided brackets through 22, and bounding the remaining verified coefficient mass by $(1+\sqrt2)(0.001430297)$ with $C(22^2-1/4)$, gives $<0.007601$. The verified secondary terms add at most $(3/4)(0.28465)x^{-1/4}$. The left or critical primary high terms and all secondary high terms add at most $(3/4)(15U_3(H))$ with $U_3(H)<6.90\cdot10^{-15}$. Here $|\Phi_v|\le3$ since each original ordinate has magnitude greater than 2. [Certified low-zero brackets](../low-spectrum-192.json) · [Secondary and high bounds](../QUARTIC_LINEAR_HEIGHT.md)

The positive powers in the combined upper are evaluated at each upper endpoint, the decreasing terms at each lower endpoint. The small-variance proof uses the supplied lower endpoint for the logarithm in the prime-class bound and for the anchor’s $x^{-d}$ factor. The following are outward upper bounds including the grid error.

| Range of $x$ | Upper in units of $\sqrt x$ |
|---|---:|
| $10^{24}$ to $10^{48}$ | 0.007743 |
| $10^{48}$ to $10^{60}$ | 0.007836 |
| $10^{60}$ to $10^{66}$ | 0.223079 |
| $10^{66}$ to $2\cdot10^{67}$ | 0.937393 |
| $2\cdot10^{67}$ to $2.30\cdot10^{67}$ | 0.995726 |
| $2.30\cdot10^{67}$ to $2.32\cdot10^{67}$ | 0.999674 |

In the last interval the directed physical prime error costs $0.835099\sqrt x$, the high zeros of the narrow anchor $0.141760\sqrt x$, and the integrated wide high terms $0.015216\sqrt x$. The physical majorant takes positive parts at each knot and prime interval. The true signed prime differences can cancel. A fixed $H\sigma$ yields a knot area of order $H^{-3}$. Integrating a width band of length comparable to $H^{-2}$ leaves an $xH^{-5}$ cost in this method. The numerical endpoint is an accepted uniform upper, with no claim that any true value reaches $\sqrt x$ beyond it.

## Independent finite-grid calibration

The grid entries are rounded to the last displayed digit. The continuous intervals are rounded outwards. At $x=8$ the 93 grid left endpoints include 62 positive, 30 negative, and one zero. At $x=32$ all 1,907 left endpoints are positive, and the actual finite real row exceeds $0.4929709$ on the entire variance interval.

| $x$ | $W(v)$ | Positive grid | Negative grid | Positive integral | Negative integral |
|---:|---|---:|---:|---:|---:|
| 8 | $e^{-4v}$ | 0.003537598122 | 0.001080774860 | [0.00368123, 0.00368153] | [0.00107865, 0.00107909] |
| 8 | $e^{-4v-v^2}$ | 0.002290164806 | 0.001062454552 | [0.00240551, 0.00240575] | [0.00106165, 0.00106209] |
| 32 | $e^{-4v}$ | 0.146021741746 | 0 | [0.14597024, 0.14598433] | 0 |
| 32 | $e^{-4v-v^2}$ | 0.133998312586 | 0 | [0.13394811, 0.13396086] | 0 |

The computation uses every prime through $x^2$, the actual Gaussian formula on each piece of $K$, and the exact mass of the partial final grid cell. The continuous enclosures use a separate step $1/4096$ in $\delta$, with a rigorous linear-interpolation error from the global second-derivative bound. Both precision settings reproduce every grid sign and continuous enclosure.

    uv run verify_terminal_bound.py
    uv run verify_terminal_grid.py --precision 128
    uv run verify_terminal_grid.py --precision 192

[Uniform-bound verifier](verify_terminal_bound.py) · [Small-variance verifier](check_small_variance.py) · [Uniform-bound receipt](terminal-bound-receipt.txt) · [Grid and continuum verifier](verify_terminal_grid.py) · [128-bit grid receipt](terminal-grid-128.json) · [192-bit grid receipt](terminal-grid-192.json)
