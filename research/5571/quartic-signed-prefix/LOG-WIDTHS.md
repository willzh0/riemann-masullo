# An exact transition for logarithmic smoothing variances

Use the actual quartic annular prime sum $Q$, its compensated Gaussian smoothing $Q_\delta$, and the real signed prefixes defined in the [samplewise width theorem](ADAPTIVE-WIDTHS.md). Let $\rho=\beta+i\gamma$ run over the nontrivial zeros of the fixed quartic, with the conjugate points included when taking real parts. All these ordinates satisfy $|\gamma|>2$. Define
$$
 d_*=\max_{\beta>1/2}\frac{2(\beta-1/2)}{\gamma^2-\beta^2},
 \qquad
 m(d)=\max_\rho\left(\beta-\frac d2(\gamma^2-\beta^2)\right),\quad d>0.
$$
The first maximum is taken to be zero when there are no exterior zeros. When there are exterior zeros it is attained and $0<d_*<1/(H^2-1)$ for the verified height $H=20,000,000$. Each maximum defining $m(d)$ is attained since the displayed terms tend to $-\infty$ with $|\gamma|$.

For $\delta_j^2=d\log j$ and fixed $0<d<3$ the actual filtered rows obey the following alternatives.

- If $0<d<d_*$, then $m(d)>1/2$, and both $E_\pm(J;\delta)\asymp_{\chi,d}J^{1+m(d)}$.
- If $d=d_*>0$, then $m(d)=1/2$, and both signed sums are of exact order $J^{3/2}$.
- If $d_*<d<3$, there is an $\epsilon>0$ such that $|Q_{\delta_j}(j)|\ll_{\chi,d}j^{1/2-\epsilon}$ for every $j$. This is an upper for the full complex prime sum.

In particular, the critical-line hypothesis for this quartic is equivalent to obtaining a cofinal critical-exponent upper for one signed row at every member of some sequence $d_n\downarrow0$. A single sufficiently large $d$ already gives a strictly subcritical bound unconditionally. For example, **any** samplewise choices in $\log j\le\delta_j^2\le2\log j$ satisfy $|Q_{\delta_j}(j)|\ll_\chi j^{1/35}$. The final section proves this stronger example directly from the prime coefficients.

## The actual spectral expansion

Write $\eta=\chi^2$ for the primitive quadratic character modulo five, and $M(s)=(2^{1-s}-1)/[(1-s)s(s+1)]$. The true complex prime sum has the representation, on $t>0$,
$$
 Q(t)=-\sum_{\rho_\chi} M(\rho_\chi)t^{\rho_\chi}
     +\frac12\sum_{\rho_\eta}M(\rho_\eta/2)t^{\rho_\eta/2}
     +O(1+t^{1/3}).
$$
All divisor sums in this formula include multiplicities. The subtraction $-L'/L(s,\chi)-(-L'/L)(2s,\eta)$ removes all even powers. All remaining odd proper powers are bounded in complex norm by a constant times $t^{1/3}$ using $p\ge2$ and Chebyshev. The elementary Archimedean residues are $O(1+\log t)$ for $t\ge2$, and the discrepancy on $0<t\le2$ is bounded by absolute convergence since the true prime sum there vanishes. All coefficients at powers of five vanish in both Euler series. Each zero with $|\gamma|\le H$ is on the critical line and contributes $1/(\tfrac14+\gamma^2)$ to a positive sum bounded by $B_\chi<.203222$ or $B_\eta<.156557$. Thus $|\gamma|>2$ for both characters, including both signs of the ordinates. [Prime-power and elementary residues](QUARTIC_LINEAR_HEIGHT.md) · [Complex modulus and the imaginary residues](README.md) · [Platt’s finite verification](https://arxiv.org/abs/1305.3087)

Set $v=\delta^2$. If $v=d\log x+u$, the smoothed monomial is exactly
$$
 \begin{split}
 x^s\Phi_v(s)={}&
 e^{us^2/2}x^{F_d(s)}
 +e^{u(s^2-1)/2}x^{F_d(s)-d/2}\\
 &-e^{u(s^2-1/2)}x^{F_d(s)+d(s^2-1)/2},\qquad
 F_d(s)=s+ds^2/2 .
 \end{split}
$$
For $u\in[0,U]$ the three coefficients have modulus at most one at every primary or halved quadratic zero, since $\Re(s^2)<0$. The last two exponents at each point have strictly smaller real parts than $F_d(s)$. The secondary quadratic leading exponents are uniformly below $1/2$ for fixed $d>0$, since $\Re s<1/2$ and $\Re(s^2)=(\beta_\eta^2-\gamma_\eta^2)/4<-3/4$. The true arithmetic remainder after smoothing is
$$
 O_U(1+x^{1/3+d/18}).
$$
Indeed for $0\le a\le1$ the total variation of the signed Gaussian law satisfies $\int e^{ah}\,d|\nu_{\sqrt v}|(h)\le3e^{a^2v/2}$. This also justifies exchange of the absolutely convergent zero sums and the Gaussian averaging. Thus the proper powers and affine terms lie below the critical exponent throughout $0<d<3$.

For any fixed $d>0$ only finitely many primary terms can lie above a given real exponent, since $\beta-d(\gamma^2-\beta^2)/2\to-\infty$. The absolute coefficient sum turns a strict gap in exponents into a power saving for the whole remainder. At a maximizing primary exponent $m(d)\ge1/2$ the leading real row at $u=0$ is consequently a finite real trigonometric polynomial in $\log x$, scaled by $x^{m(d)}$, plus $O(x^{m(d)-\epsilon})$. Each projected coefficient is $-\tfrac12(m_\chi(\rho)+m_\chi(\bar\rho))M(\rho)\ne0$, and $\Im F_d(\rho)=\gamma(1+d\beta)\ne0$. On the right half-plane $F_d(s)=F_d(t)$ implies $s=t$, because the alternative $s+t=-2/d$ has negative real part. Hence even at crossings of the real exponents the distinct surviving frequencies cannot cancel identically. Mean testing at any one such frequency gives a uniformly positive absolute integral on every sufficiently long fixed log interval. The ordinary mean tends to zero, so the same holds for both one-sided integrals. The leading trigonometric polynomial has bounded derivative in $\log x$. Its sampled values on each fixed terminal shell have the same lower order by Riemann summation, while the pointwise remainder is smaller by a fixed power. This proves the first two alternatives. In the third, the maximum over the primary zeros is strictly below $1/2$ and the same absolute-sum bound gives the asserted power saving.

## Independent adjustments of each variance

Suppose $0<d<d_*$. Away from a locally finite set of $d$ there is a unique maximizing pair $\rho,\bar\rho$ in the real projection. Indeed on every compact interval $0<a\le d\le b$ only finitely many affine functions of $d$ can maximize. Two are identical only for the same $(\beta,|\gamma|)$. Fix such a nonexceptional $d$, let $G=\gamma^2-\beta^2$, $\alpha=m(d)$, $\omega=\gamma(1+d\beta)$ and $k=\beta\gamma$ with $\gamma>0$. At **every** integer $j$ and uniformly for $0\le u\le U$, the actual real row has the expansion
$$
 q_{\sqrt{d\log j+u}}(j)
 =2|b_\rho|j^\alpha e^{-Gu/2}
       \cos(\omega\log j+\arg b_\rho+ku)
       +O_{\chi,d,U}(j^{\alpha-\epsilon}).
$$
The constant and gap do not depend on the sample, its phase or $u$. In particular:

- If $U<\pi/k$, every possible independently chosen $u_j\in[0,U]$ retains both signed lower bounds of order $J^{1+\alpha}$ on every sufficiently large terminal prefix. Each sign has an open arc of initial phases for which the whole adjustment interval has that sign with a fixed margin. Taking a closed subarc, every terminal shell spanning two full log periods contains $\gg J$ integers in it. The positive damping on $[0,U]$ has a fixed lower bound.
- If $U=\pi/k$, every initial phase permits a zero of the leading cosine in the closed interval, possibly at an endpoint. Choosing that width for each $j$ makes the actual real sample $O(j^{\alpha-\epsilon})$, so both signed prefixes gain a fixed power relative to $J^{1+\alpha}$. This estimate can remain above the critical exponent.
- If $U>\pi/k$, every initial phase allows one strictly positive and one strictly negative leading cosine. Compactness in the initial phase supplies fixed margins, and the damping remains positive. The actual real sample therefore takes both signs as $u$ varies for each sufficiently large $j$. Continuity supplies a choice $u_j$ with $q_{\sqrt{d\log j+u_j}}(j)=0$ exactly. This statement concerns the real output. A complex zero would require an additional condition on its imaginary part.

This is a sharp transition at fixed $d$ even though every allowed schedule has the same limiting variance ratio $\delta_j^2/\log j\to d$. The hypotheses explicitly identify the maximizer and its ordinate; the existence or value of such a genuine exterior pair is unknown.

## Comparison with the Green exponent

The fixed quartic’s largest right-hand Green logarithm is $g_{\max}=\max_{\beta>1/2}\log|(\rho+1)/(2-\rho)|$, with zero for the empty divisor. Its total over all right-hand zeros is less than $2.09879293\cdot10^{-7}$ by the independent quartic calibration. At each exterior point put $b=\beta-1/2>0$ and $t=|\gamma|>H$. Then
$$
 g_\rho=\tfrac12\log\left(1+\frac{6b}{t^2+(2-\beta)^2}\right),\qquad
 \frac{3b}{t^2+(1+\beta)^2}\le g_\rho
       \le\frac{3b}{t^2+(2-\beta)^2}.
$$
These inequalities follow from $z/(1+z)\le\log(1+z)\le z$. Consequently
$$
 \frac23g_{\max}\ \le\ d_*\ \le\
          \frac23\left(1+\frac5{H^2-1}\right)g_{\max}.
$$
The upper factor follows from $(1+\beta)^2+\beta^2<5$. The critical variance slope of the true smoothed arithmetic row thus measures the largest individual Green logarithm to this relative precision. The finite bound on the total Green mass leaves its vanishing open. [Quartic Green calibration](https://github.com/willzh0/riemann-masullo/tree/da8d5a8b3252c16120606b0b513d445e88cfbd0f/research/5571/quartic-green-calibration) · [Signed arithmetic Green exponent](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7160910045)

## A strictly subcritical bound from the prime coefficients

More generally let $0<d\le D<\infty$. For every independent choice $d\log j\le\delta_j^2\le D\log j$ one has the unconditional bound
$$
                         |Q_{\delta_j}(j)|\ll_{\chi,d,D}j^{1/(35d)} .
$$
To prove it, truncate Möbius inversion of the prime Dirichlet series at $n\le N$. With $A_\xi=-L'/L(\cdot,\xi)$ the comparison series is $\sum_{n\le N}\mu(n)A_{\chi^n}(ns)$. All nonzero terms involve primitive nonprincipal conductor-five characters because $\mu(n)=0$ whenever $4\mid n$. For each unramified $p$, the difference on $p^m$ vanishes for $m\le N$ by the divisor identity $\sum_{n\mid m}\mu(n)=\mathbf1_{m=1}$. At $m>N$ its coefficient magnitude is at most $m\log p$. Prime five is absent throughout. The residual after weighting by $K(p^m/x)$ is $O_N(x^{1/(N+1)})$ for $x\ge1$, since $p^m\ge p^{N+1}2^{m-N-1}$ and $\sum_{p\le y}\log p\ll y$. The resulting geometric sum in $m$ converges.

For each fixed $n$ the logarithmic-derivative term has zero contributions $-M(\rho/n)x^{\rho/n}/n$, and the remaining terms are $O_n(1+\log x)$ on $x\ge1$. To see this, shift the Mellin line for $A_{\chi^n}(ns)M(s)x^s$ to $\Re s=-1/(2n)$. Only nontrivial zeros and the possible pole of order at most two at zero intervene. The constant and logarithmic residues at zero depend on the fixed character and $n$. The functional equation bounds the logarithmic derivative on the shifted line by $O_n(\log(2+|\Im s|))$. On horizontal contours one uses heights avoiding the ordinates of these finitely many scaled divisors by $\gg_N1/\log T$. The fixed-strip bounds and cubic decay of $M$ give convergence, as in the [quartic explicit formula](QUARTIC_LINEAR_HEIGHT.md). All zero coefficients are absolutely summable for fixed $n$. On $0<x<1$ the original sums vanish and the zero series are bounded. The global residual after retaining the finitely many zero families is therefore $O_N(1+x^a)$ with $a=1/(N+1)$. Smoothing costs $O_N(1+j^{a+Da^2/2})$.

For every zero of the three characters put $G=\gamma^2-\beta^2$. Below $H$, $\beta=1/2$ and $\tfrac14+\gamma^2\ge1/B$ for $B=.203222$, giving
$$
 \frac{\beta^2}{2G}\le\frac{B}{4(2-B)}<\frac1{35}.
$$
Above $H$ use $\beta^2/(2G)\le1/[2(H^2-1)]<1/35$. For each scaled point and $d_j=\delta_j^2/\log j\in[d,D]$, completion of the square gives
$$
 \Re F_{d_j}(\rho/n)=\frac{\beta}{n}-\frac{d_jG}{2n^2}
        \le\frac{\beta^2}{2d_jG}<\frac1{35d}.
$$
Both other Gaussian exponents are strictly smaller. Choose fixed $N$ so $a+Da^2/2<1/(35d)$, then sum the absolute zero coefficients of the finite family. For $d=1,D=2$ one can use $N=40$ since $1/41+1/41^2<1/35$. The sample $j=1$ has width zero and vanishes. This arithmetic upper for the genuine smoothed row is compatible with an original quartic exterior zero. The unsmoothed cofinal upper remains the missing input.
