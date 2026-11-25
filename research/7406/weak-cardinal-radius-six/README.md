# A radius-six Gram criterion for the geometric blocks at zero strip width

For Masullo, Theorem 10.4.3.5(2), p. 472, take $\alpha=0$ and $2<s\le3$. The finite-subset trace-norm bound of #7406 for every compact Bruhat test is equivalent to a polynomial bound on one **finite positive quadratic form per zero**. Its entries use only the distinct same-character zero ordinates within distance **six** of that zero. Multiple zeros still contribute just the value jet throughout this range, including $s=3$ under the repository's boundary convention. Positive widths and the required global arithmetic growth bound remain open. [Open statement](https://github.com/mccorvie/riemann-masullo/issues/7406) · [Merged one-jet block calculation](https://github.com/mccorvie/riemann-masullo/pull/7481)

Fix the field and $a>0$. Normalize Haar measure on its compact norm-one group to probability for the Fourier coordinates. The original Haar normalization gives a fixed scalar. Choose a smooth norm splitting and use the associated normalized lift of each character $\omega$. Write $Z_\omega$ for the **distinct** ordinates of the actual completed function on $\Re s=a$. Write $\ell_\omega$ for the torus frequency of $\omega$ on a fixed compact Lie quotient of the norm-one group. For another basepoint $\chi_\omega$, an index $t$ has physical ordinate $w$ determined by $\chi_\omega|\cdot|^{it}=\widetilde\omega|\cdot|^{iw}$ in this splitting. Both the zero orders and the distances within a component are preserved. With arbitrary basepoints the height in the polynomial bound below is $|w|$, which can differ from $|t|$ by a component-dependent shift. [Basepoint shift in Lean](https://github.com/mccorvie/riemann-masullo/blob/9c791d74a81f1191d900e6d96f1270acee9b033e/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L8664)

Put $\theta=s/2$. For $b>0$, $r>1/2$ and a finite set $E$ let
$$
 G_{b,r}(E)_{uv}=\frac1{2\pi}\int_{\mathbb R} e^{i(u-v)\xi}(b+\xi^2)^{-r}\,d\xi .
$$
At $w\in Z_\omega$ use $E=Z_\omega\cap[w-6,w+6]$ and solve $G_{1,\theta}(E)c=e_w$. Define
$$
 W_E(w)=c^*G_{1,\theta+1}(E)c .
$$
The criterion is that **on each fixed finite level** there exist $C,N$ such that $W_E(w)\le C(1+|w|+\|\ell_\omega\|)^N$ for all its $\omega,w$. It includes tests seeing infinitely many torus frequencies on that level. Constants may depend on the level, the field, $a$ and $s$. In fact this condition implies $\sum_{\omega,w}\|R_{\omega,w}(\varphi)\|_1<\infty$ for each test. Conversely, even the uniform singleton bound for every test implies the stated polynomial estimate.

K-ieren proved the exact first-moment identity in Proposition 3. Their Theorem 5 proves necessity of polynomial weak growth and gives sufficiency with an extra lower bound on nearest-neighbor gaps. The higher moments below give sufficiency for arbitrary site configurations. The radius-six comparison then replaces the infinite cardinal by a finite computation. Theorem 4 in the same note concerns blocks grouped between cuts. Here one may select each zero independently. [Earlier first-moment identity, necessity, and grouped sums](https://github.com/mccorvie/riemann-masullo/issues/7406#issuecomment-7156058239) · [Earlier spacing-based bound](https://github.com/mccorvie/riemann-masullo/issues/7406#issuecomment-7158392940)

## The weak norm and all finite block sums

On the Mellin line let $H^r$ have squared norm $(2\pi)^{-1}\int\langle\xi\rangle^{2r}|\widehat f(\xi)|^2d\xi$, where $\langle\xi\rangle=(1+\xi^2)^{1/2}$. For the locally finite set $Z=Z_\omega$ the value cardinal $h_w$ is the least-$H^\theta$-norm function equal to $1$ at $w$ and $0$ at the other sites. A bump near $w$ makes the constraints feasible. The zero-data subspace $V$ is closed because evaluation is continuous. The project's common-kernel theorem identifies it with the geometric subspace. The line density in the original log-norm variable is $(1+y^2)^\theta$. Biorthogonality and the orthogonal lift identify the cardinal for any of the basis data in #7406. If $\lambda_\omega$ is the multiplier of the test, the geometric projection of $\lambda_\omega h_w$ is $(\lambda_\omega-\lambda_\omega(w))h_w$. Its product with evaluation at $w$ is the single geometric block. The norm of evaluation is $\sqrt{G_{1,\theta}(\{w\})_{ww}}$, independent of the character and the ordinate in the chosen normalization. [Sobolev density](https://github.com/mccorvie/riemann-masullo/blob/9c791d74a81f1191d900e6d96f1270acee9b033e/RiemannMasullo/Ch09_HardySobolev/Sec2.lean#L3066) · [Common kernel in Lean](https://github.com/mccorvie/riemann-masullo/blob/9c791d74a81f1191d900e6d96f1270acee9b033e/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L6596) · [Project block formula](https://github.com/mccorvie/riemann-masullo/pull/7481)

**Moment estimate.** Put $X=x-w$. For every integer $k\ge1$ there is $C_{\theta,k}$, independent of the sites, such that
$$
 \|X^k h_w\|_{H^\theta}\le C_{\theta,k}\|h_w\|_{H^{\theta-1}}.
$$
First take a finite site set $A\ni w$. The Fourier transform $H$ of the cardinal in centered coordinates is a finite exponential sum divided by $m(\xi)=(1+\xi^2)^\theta$. Its derivatives of all orders are $O_A(\langle\xi\rangle^{-2\theta})$. Thus all polynomial multiples are in $H^\theta$. Orthogonality to $X^{2k}h_w$, which vanishes at all sites, gives, after $k$ integrations by parts,
$$
 0=\int \overline{(mH)^{(k)}}\,H^{(k)}.
$$
The boundary terms vanish since the derivatives of $mH$ are bounded and those of $H$ decay. Expand the product derivative and use Cauchy–Schwarz. If $A_k=\|\sqrt m\,H^{(k)}\|_2$, one obtains
$$
 A_k\le\sum_{j=1}^k\binom{k}{j}
       \|m^{-1/2}m^{(j)}H^{(k-j)}\|_2 .
$$
Since $|m^{(j)}|/\sqrt m\le C_{\theta,j}\langle\xi\rangle^{\theta-j}$, the term $j=k$ costs at most the weak norm times a constant. The other terms are bounded by the preceding $A_{k-j}$. This proves the assertion by induction. For an exhaustion by finite sets containing $w$, the finite cardinals converge strongly in $H^\theta$ to the full one. Indeed they are its orthogonal projections onto the increasing spans of the corresponding evaluation kernels, whose closed union is $V^\perp$. Their weak Sobolev norms therefore converge too. Weak compactness for $X^k h_w$ and distributional convergence give the same moment estimate on $Z$.

For $k=1$ integration by parts once more yields k-ieren's precise identity, with the Fourier measure $d\xi/(2\pi)$:
$$
 \|Xh_w\|_{H^\theta}^2=\tfrac12\int m''(\xi)|H(\xi)|^2\,\frac{d\xi}{2\pi},\qquad
 \sqrt\theta\,\|h_w\|_{H^{\theta-1}}
 \le\|Xh_w\|_{H^\theta}
 \le\sqrt{\theta(2\theta-1)}\,\|h_w\|_{H^{\theta-1}} .
$$
For infinite $Z$, $(e^{iuX}-1)h_w$ belongs to the zero-data subspace, so its squared strong norm is $\|e^{iuX}h_w\|_{H^\theta}^2-\|h_w\|_{H^\theta}^2$. Average the identities at $u$ and $-u$ and divide by $u^2$. On the left the two difference quotients tend in $H^\theta$ to $\pm iXh_w$, since $Xh_w\in H^\theta$ and modulation is strongly continuous there. On the right the centered second differences of $m$, divided by $2u^2$, tend to $m''/2$ and are dominated for $|u|\le1$ by $C_\theta\langle\xi\rangle^{2\theta-2}$. [First-moment identity](https://github.com/mccorvie/riemann-masullo/issues/7406#issuecomment-7156058239)

**From weak growth to the geometric bound.** Write $T=1+|w|+\|\ell_\omega\|$. A fixed smooth compact test has rapidly decreasing multipliers, with all derivatives, jointly in the physical ordinate and the torus frequency on its finite level. This follows by integration by parts on the torus and in log norm. Let $\eta(X/T)$ be a smooth cutoff equal to one for $|X|\le T/4$ and zero for $|X|\ge T/2$. On its support the difference quotient $(\lambda_\omega(w+X)-\lambda_\omega(w))/X=\int_0^1\lambda'_\omega(w+uX)\,du$, and its first two derivatives are $O_{\varphi,L}(T^{-L})$ for every $L$. Multiplication by a $W^{2,\infty}$ coefficient is bounded on $H^\theta$ by interpolation between $L^2$ and $H^2$. The near part is therefore bounded by $C_{\varphi,L}T^{-L}\|Xh_w\|_{H^\theta}$. On the complementary part use the bounded multiplier $\lambda_\omega(w+X)-\lambda_\omega(w)$ and the multiplier $(1-\eta(X/T))/X^k$, whose $W^{2,\infty}$ norm is $O_k(T^{-k})$. Apply the $k$th moment estimate. Polynomial weak norms thus make the individual trace norms decrease faster than any inverse power of $T$. The joint polynomial count on the finite level makes their sum finite. [Joint count for the actual Hecke zeros](https://github.com/mccorvie/riemann-masullo/pull/7273)

**From geometric bounds to weak growth.** Choose a nonnegative smooth log-norm bump $\psi$, positive on an interval inside $(1,2)$, and let $\lambda_0(X)=\int\psi(u)e^{iuX}du$. It has $\lambda'_0(0)\ne0$ and $|\lambda_0(X)|<\lambda_0(0)$ for $X\ne0$, by strictness in the triangle inequality. Put $b(X)=\lambda_0(X)-\lambda_0(0)$. For a cutoff $\zeta_R$ supported on $|X|\le2R$ and equal to one on $|X|\le R$, the smooth multiplier $\zeta_R X/b(X)$ has bounded derivatives. Consequently
$$
 \|Xh_w\|_{H^\theta}\le C_R\|bh_w\|_{H^\theta}
            +C R^{-1}\|X^2h_w\|_{H^\theta}.
$$
Use the lower first-moment inequality and the upper second-moment estimate. Fixing $R$ sufficiently large in terms of $\theta$ gives $\|h_w\|_{H^{\theta-1}}\le C_\theta\|b h_w\|_{H^\theta}$ in centered coordinates. To realize this multiplier at $w$, project onto $\omega$ with a character and modulate the same physical bump by the ordinate $w$, choosing the signs in the given Mellin convention. The support and finite level stay fixed, and every order-$j$ smooth seminorm is $O_j(T^j)$. On this fixed-support, fixed-level Fréchet test space the single-block maps into the trace class are continuous linear maps. Pointwise boundedness follows by taking singleton subsets in #7406. Uniform boundedness supplies one finite seminorm bound for all the singleton maps. Applying it to the modulated bumps gives polynomial weak growth. [Fixed-level modulation and uniform boundedness in the related spectral bound](https://github.com/mccorvie/riemann-masullo/issues/7455#issuecomment-7156962249)

## Why a window of radius six suffices

Let $h_E$ be the minimum-norm cardinal on the complete set of local sites $E=Z\cap[w-R,w+R]$, and $h_Z$ its full counterpart. Take $\eta(y)=(1-y^2)^2$ for $|y|\le1$ and zero elsewhere. Then $\eta(X/R)h_E$ has all the required full-site values. Both it and $h_Z$ have the prescribed local data, and $h_E$ is orthogonal to their differences from $h_E$. By Pythagoras and the full minimum property,
$$
 \|h_Z-h_E\|_{H^\theta}\le \|(1-\eta(X/R))h_E\|_{H^\theta}.
$$
The function $A(y)=(1-\eta(y))/y$, extended at zero, is $2y-y^3$ inside and $1/y$ outside. Its first derivative is continuous at both ends. Its value, first derivative, and weak second derivative have supremum bounds $9/8$, $2$, $6$. For $a_R(X)=A(X/R)/R$, the $H^2$ multiplier norm is at most
$$
 B_R=\frac9{8R}+\frac2{R^2}+\frac6{R^3}.
$$
Indeed $(1-\partial^2)(a_R f)=a_R(1-\partial^2)f-2a_R'f'-a_R''f$, and $2\|f'\|_2\le\|f\|_{H^2}$. Interpolation with the $L^2$ bound gives the same upper on $H^\theta$. Since $(1-\eta(X/R))h_E=a_RXh_E$, at $R=6$ this proves
$$
 \|h_Z-h_E\|_{H^\theta}\le \delta\,\|h_E\|_{H^{\theta-1}},\qquad
 \delta=\frac{13\sqrt3}{48}<\frac12 .
$$
In particular $(1-\delta)\|h_E\|_{H^{\theta-1}}\le\|h_Z\|_{H^{\theta-1}}\le(1+\delta)\|h_E\|_{H^{\theta-1}}$. The error is relative to the computed finite cardinal. Every site on either endpoint can be included. This argument is uniform in all interior and exterior gaps.

The reproducing kernels at the sites of $E$ have strictly positive Gram matrix by linear independence of the distinct exponentials. The minimum-norm interpolant is their linear combination with coefficients $c$. Plancherel gives $\|h_E\|_{H^{\theta-1}}^2=W_E(w)$ exactly. Equivalently $W_E=\theta^{-1}\partial_b[G_{b,\theta}(E)^{-1}]_{ww}|_{b=1}$, since $\partial_bG_{b,\theta}=-\theta G_{b,\theta+1}$. The positive quadratic form needs one finite solve. On each fixed finite level the number of ordinates in this fixed window is bounded by the standard local zero count. The foregoing criterion also works without any estimate for the number of sites in a particular window.

**A second computation using mass differences.** For a finite set or the full set let $m_A(b)$ be the minimum squared interpolation energy with weight $(b+\xi^2)^\theta$. Put $W=\|h_{1,A,w}\|_{H^{\theta-1}}^2$. For every $t>0$,
$$
 [1-(1+t)^{-\theta}]W\le m_A(1+t)-m_A(1)
 \le \max\{\theta t,(1+t)^\theta-1\}W.
$$
In $H_1^\theta$ let $P$ have multiplier $(1+\xi^2)^{-1}$, set $Q=(I+tP)^\theta$, and let $h$ be the mass-one cardinal. Every competitor is $h+v$ with $v\perp h$. Testing $v=0$ bounds the energy increase above by $\langle(Q-I)h,h\rangle$. Completing the square $\|Q^{1/2}(h+v)-Q^{-1/2}h\|^2$ bounds it below by $\langle(I-Q^{-1})h,h\rangle$. The displayed constants follow from the scalar secants for $0\le P\le I$ and $\langle Ph,h\rangle=W$. For a finite set $m_E(b)=[G_{b,\theta}^{-1}]_{ww}$. This also gives a two-mass version of the radius-six criterion. Arbitrarily truncating $E$ can change the result in either direction. The guaranteed comparison uses all the sites in the window.

## Certified comparison on the zeta line

In the rational component at $a=1/2$, the first positive zeta zero lies at ordinate $14.1347\ldots$ and the next at $21.0220\ldots$. Its radius-six set is a singleton. At $s=3$, $G_{1,3/2}(0)=1/\pi$ and $G_{1,5/2}(0)=2/(3\pi)$, so $W_E=2\pi/3$. The full weak norm at this actual zero thus lies between $(1-\delta)\sqrt{2\pi/3}$ and $(1+\delta)\sqrt{2\pi/3}$. This finite calibration supplies no uniform bound at arbitrarily large heights. [Arb's historical zero-isolation and counting routines](https://arblib.org/acb_dirichlet.html#riemann-zeta-function-zeros)

For the first 128 positive zeta zeros the largest finite $W_E$ is exactly $2\pi/3$ at the first zero. For Lehmer's pair, indices 6709 and 6710, the finite squared norms exceed $21.45$ and $23.25$. The local set at both centers consists of all 14 indexed zeros from 6703 to 6716. The radius-six comparison therefore proves bounds on the **full** $H^{1/2}$ norms, including the influence of every zero outside the windows:

| Actual zeta centers | Full weak norm |
|---|---:|
| Each of the first 128 positive zeros | $<2.13$ |
| Zero 6709 | $>2.45$ |
| Zero 6710 | $>2.55$ |

Two direct Gram calculations at 128 and 192 bits certify the indexed zero counts and the enclosures for every reported quadratic form. A separate 144-bit program uses only order-one Bessel kernels and the energy differences at masses $1$ and $1+2^{-24}$. It independently proves the three strict inequalities in the table. The historical zero-isolation routines certify the locations and counts with interval arithmetic. These computations witness variation among the actual Hecke sites of one character. Growth at arbitrarily large heights remains the arithmetic question. [Details and historical sources](ZETA-CALIBRATION.md) · [Independent mass-difference verifier](verify_mass_secants.py) · [Mass-difference output](mass-secants-144.json)
