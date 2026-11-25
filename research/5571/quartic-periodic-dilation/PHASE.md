# A phase chosen separately at every terminal cutoff measures the asymmetric zero divisor

Let χ be the primitive quartic character modulo 5 with χ(2)=i. Put

$$S(x)=\sum_{p\le x}\chi(p)\log p\,(x-p),\qquad
 T(J)=\min_{|z|=1}\sum_{j\le J}[\Re(\bar z S(j^4))]_+.$$

The minimum exists by continuity. The direction may change freely with the terminal index $J$ and is common to the samples within that prefix. Put $m(\rho)=\operatorname{ord}_\rho L(s,\chi)$ in the critical strip, with value zero at regular nonzeros, and

$$\Theta_\Delta=\max\!\left(\tfrac12,\ \sup_{m(\rho)\ne m(\bar\rho)}\Re\rho\right).$$

Then

$$\lim_{J\to\infty}\frac{\log(1+T(J))}{\log J}=5+4\Theta_\Delta.$$

Moreover, some $\lambda_\chi\in(0,1)$ and $c_\chi>0$ satisfy, at every sufficiently large $J$, for every terminal phase $z$ and both signs,

$$\sum_{\lambda_\chi J<j\le J}[\pm\Re(\bar z S(j^4))]_+\ge c_\chi J^7.$$

If an asymmetric exterior zero has real part β, the right side can be replaced by $c_{\chi,\rho}J^{5+4\beta}$, on a fixed shell shared by all such zeros sufficiently close to the asymmetric supremum. In particular $T(J)\asymp_\chi J^7$ exactly when $L(s,\chi)/L(s,\bar\chi)$ has no zero or pole in $1/2<\Re s<1$. A critical-sized upper bound along any unbounded sequence already implies this condition. A common exterior zero of equal multiplicity cancels in the quotient.

## The actual spectrum and its coefficients

The integrated explicit formula for the primitive character gives

$$F(y)=e^{-3y/2}S(e^y)
  =-\sum_\rho\frac{m(\rho)e^{(\rho-1/2)y}}{\rho(1+\rho)}+o(1).$$

The sum is over distinct zeros and its coefficients are absolutely summable. The unramified squares contribute $o(x^{3/2})$, by the fixed-modulus PNT for the nonprincipal $\chi^2$ and partial summation. Powers of exponent at least three cost $O(x^{4/3}\log^2(2x))$, and the elementary terms are $O(x\log(2x))$. On the positive real axis $\Re L(s,\chi)=\sum_{k\ge0}((5k+1)^{-s}-(5k+4)^{-s})>0$. There is no zero-frequency term. Seven simple negative versus six simple positive ordinates in $|\Im\rho|\le22$ certify a critical ordinate $\gamma_0$ for which $m(1/2+i\gamma_0)\ne m(1/2-i\gamma_0)$. [Explicit formula for the actual quartic](https://github.com/mlyle/riemann-masullo/tree/3f90b6c75f2e36f52c2c9cb427155a556bcee9d8/research/5571/quartic-mod-five-deficit) · [Certified zeros and normalization](https://github.com/willzh0/riemann-masullo/blob/53cac8a4461b84ad1d9c96ea2305f48e82ba4a31/PROOF.md).

For $F_z=\Re(\bar z F)$, union the divisor with its conjugate. The coefficient at $\rho-1/2$ is

$$c_z(\rho)=-\frac{\bar z\,m(\rho)+z\,m(\bar\rho)}{2\rho(1+\rho)}.$$

At an asymmetric zero, $|c_z(\rho)|\ge|m(\rho)-m(\bar\rho)|/(2|\rho(1+\rho)|)$, uniformly on the circle. At $z=i$ only the differences of multiplicities remain. Consequently $|\Im S(x)|\ll_\chi x^{1+\Theta_\Delta}$, and $T(J)\ll_\chi J^{5+4\Theta_\Delta}$.

## A uniform lower bound from any asymmetric exterior zero

Fix $1/2<\sigma<\beta=\Re\rho_0$ for such a zero. Montgomery's fixed-conductor density estimate implies that the sum of $1/|\Im\rho|$ over distinct points $\Re\rho>\sigma$ in the union divisor is finite. Indeed the counting exponent $3(1-\sigma)/(2-\sigma)<1$; dyadic summation suffices. For each conjugate pair in this region, with $w=b+i\gamma=\rho-1/2$, $\gamma>0$, take two positive masses at $0,d=\pi/\gamma$ with ratio $e^{bd}:1$. The law of their independent sum has bounded support and bilateral transform zero at every $w,\bar w$. Convolve with a smooth nonnegative probability of compact support to produce a density $K$ supported in an interval $I$. Convolve once more with a wide uniform interval law to get a bounded probability density $P$ positive and constant on $I$, still killing the same points. [Montgomery, *Zeros of L-functions*, Theorem 1](https://doi.org/10.1007/BF01404638) · [Mlyle’s compact annihilator and primitive](https://github.com/mlyle/riemann-masullo/blob/69f6639d0e53c2a04aa3b5f8487a1be237274b97/research/5571/square-prefix-fixed-window-count/README.md).

For $w_0=\rho_0-1/2$, divide $\widehat K(w)$ by the full power of $w-w_0$ at its zero. A bounded, complex inverse transform $L$ is supported in $I$. Each division uses the right-tail primitive $e^{-w_0t}\int_t^\infty e^{w_0v}K(v)\,dv$; its zero moment makes it vanish to the left of $I$ as well. Thus $|L|\le C P$, $\widehat L(w_0)\ne0$, and all other selected terms vanish. Integrating $F_z(y+v)$ against $P$ costs $O(e^{(\sigma-1/2)y})$, uniformly in $z$, while integration against $L$ gives $c_z(\rho_0)\widehat L(w_0)e^{w_0y}$ plus an error of that size. The absolute convergence and compact supports justify both assertions. The modulus of the isolated term is bounded below uniformly in $z$. Use $2[f]_\pm=|f|\pm f$ and the bounded density $P$ to infer

$$\int_{I'}[\pm F_z(y+v)]_+\,dv \gg_{\rho_0} e^{(\beta-1/2)y}$$

for a fixed interval $I'$ containing the support of $P$. The support is independent of $\rho_0$ above the fixed threshold $\sigma$; constants can depend on this zero.

## The critical floor if every exterior pair has equal multiplicities

Write $R=\Re F,\ I_1=\Im F$. In this case $I_1(y)=A(y)+o(1)$, where $A$ is a bounded real uniformly almost-periodic trigonometric series, with mean zero and a nonzero coefficient at $\gamma_0$. Indeed the exterior terms cancel, the strictly interior terms decay by dominated convergence and the critical series converges uniformly. A nonzero real uniformly almost-periodic function of mean zero has values above and below positive fixed margins at relatively dense translates. Otherwise a signed version is nonnegative with mean zero, impossible because a positive interval recurs relatively densely. Uniform continuity also supplies a conserved interval width at such peaks.

When no exterior zero exists, the same trigonometric description holds for the whole complex $F$. Each projected limit has a nonzero coefficient at $\gamma_0$, uniformly bounded below by the displayed coefficient inequality. For each fixed direction both one-sided integrals have positive lower bounds on every sufficiently long interval. A neighborhood of that direction shares those lower bounds, because the vector series is uniformly bounded. Compactness of the direction circle yields one length and two uniform positive bounds.

Otherwise choose one exterior pair with real part $\beta$, choose $1/2<\sigma<\beta$, and take $\sigma-1/2<t<\beta-1/2$. Write $F_z=aR+bI_1$ with $a^2+b^2=1$. For $|a|\ge e^{-ty}$, use the compact construction above on $R$ at $\rho_0$, whose coefficient is nonzero. In the $P$ and $L$ averages the $bI_1$ term is bounded, while the other errors are $O(|a|e^{(\sigma-1/2)y})$. Thus each one-sided integral is $\gg |a|e^{(\beta-1/2)y}\gg e^{(\beta-1/2-t)y}$ uniformly in the indicated directions.

For $|a|\le e^{-ty}$ use the binary law convolved with a sufficiently narrow nonnegative smooth bump to get a bounded density $K_0$. It annihilates the exterior points above $\sigma$ and satisfies $\widehat K_0(i\gamma_0)\ne0$. Each binary factor has unequal positive atom weights and so is nonzero at every purely imaginary point; the product is nonzero there because its deviations from 1 are bounded by $|\gamma_0|d$, a summable series. A sufficiently narrow bump keeps its transform nonzero too. Then $\int K_0(v)A(u+v)\,dv$ has the same nonzero frequency, zero mean and recurrent positive and negative margins. On $u=y+O(1)$, the averaged real term times $a$ is $O(e^{-(t-\sigma+1/2)y})$, uniformly. Choose the two appropriate centers a bounded distance from $y$, use $|b|=1-o(1)$, and use positivity and boundedness of $K_0$. Both one-sided integrals of $F_z$ on one fixed enlarged interval exceed an absolute positive constant for every such direction.

## Passing the one-sided integrals to every terminal prefix

Translate a fixed log interval to lie strictly inside $(4\log(\lambda_\chi J),4\log J)$, with room for neighboring fourth powers. Inside a cell $[d,e]=[j^4,(j+1)^4]$ its prime ramps with $p\notin(d,e)$ are affine. All others give an interpolation error in the unnormalized $S$ of absolute value at most

$$(e-d)\sum_{d<p\le e}\log p\ll J^6\log J.$$

The log length of a cell is $O(1/J)$. Applying convexity of the positive part to the linear interpolant at the two endpoints gives for either sign

$$\int [\pm F_z]_+\ll J^{-7}\sum_{\lambda_\chi J<j\le J}
 [\pm\Re(\bar zS(j^4))]_+ + O(\log J).$$

This error is negligible for every growing signal above, including the large-$|a|$ case, where the signal grows by a fixed power. For the bounded critical-floor case the error sharpens to $o(1)$. On the critical line $F$ is a bounded uniformly continuous almost-periodic function plus $o(1)$, so normalized values vary by $o(1)$ per cell, uniformly in direction. With paired exterior and small $|a|$, use the chord estimate for the $aR$ component, giving $O(|a|\log J)=o(1)$, and uniform almost-periodicity plus $o(1)$ for the $bI_1$ component. More explicitly, use the unnormalized common linear interpolant for both components; for the $I_1$ piece the varying factors $e^{3u/2}$ change by $1+O(1/J)$ within one cell, so it has normalized interpolation error $o(1)$. This proves the discrete shell conclusions. It uses the elementary chord estimate even in the unbounded cases. [Actual signed curvature identity in PR 7653](https://github.com/mccorvie/riemann-masullo/pull/7653).

Taking the asymmetric exterior abscissae towards $\Theta_\Delta$ proves the logarithmic exponent. With no asymmetric exterior point, the uniform critical floor and the imaginary upper prove $T(J)\asymp J^7$. All assertions concern actual prime samples. For independent angles at the individual indices within a prefix it is possible to make every projected summand zero by selecting its perpendicular, so that ordering of the quantifiers matters.

## Additive shifts at each individual cutoff

For $5\nmid h$, let $A_h(x)=\sum_p(\chi(p+h)+\chi(p-h))(x-p)_+\log p$ and put $\eta=\chi^2$. Checking the five residue classes, including $p=5$, gives exactly

$$A_h=-\tfrac12 S+\eta(h)(\tfrac12+i)\overline S,\qquad
  S=\tfrac12 A_h+\eta(h)(\tfrac12+i)\overline{A_h}.$$

For $S=X+iY$, $A_1=Y+i(X-Y)$ and $A_2=-X-Y-iX$. Both real-linear matrices have determinant $-1$ and singular values $(\sqrt5\pm1)/2$. Thus a single symmetric additive shift recovers the whole original complex sample exactly. In particular $[-\Re S]_+=[\Im A_2]_+$ at every cutoff. The additive transformations and the asymmetric-divisor exponent concern a different statistic from the power-short *multiplicative* convolution, whose multiplier vanishes at the zeros of $L(s,\chi)$. [Mlyle’s periodic dilation](https://github.com/mlyle/riemann-masullo/blob/c2eb094fffef928fdb72c2e180c255092e819347/research/5571/fourth-power-prime-curvature/spectral-interpolation-periodic-prime-convolution.md).
