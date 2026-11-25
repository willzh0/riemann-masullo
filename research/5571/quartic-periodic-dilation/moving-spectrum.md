# A nonzero mean forces supercritical signed mass in every late terminal shell

Keep the true primitive quartic $\chi\bmod 5,\ \chi(2)=i$ on the primes. Let $G_a(x)$ denote the genuine short periodic row with $N=x^\kappa,\ 0<\kappa<1$, and let $\mu_a=\tfrac15\sum_{r=1}^5 a(r)$ be the mean of its five-periodic dilator. Fix once and for all a smooth real $W$ equal to one on $[0,1]$, zero on $[2,\infty)$, and between zero and one. There is no monotonicity assumption on $W$.

For each fixed $M<\infty,\ \delta>0$, there are $0<\lambda<1$ and $c>0$ such that for every sufficiently large $J$, simultaneously for all five-periodic $a$ with $\|a\|_2\le M,\ |\mu_a|\ge\delta$, and for both signs,

$$

 \sum_{\lambda J<j\le J}
      [\pm\Re G_a(j^4)]_+\ \ge\ c J^{7+2\kappa}.

$$

Thus the entire weight and one common output phase may be chosen anew at each terminal $J$. The constants may depend on the fixed cutoff and its exponent. The exponent exceeds seven because the growing cutoff moves genuine critical frequencies to real part $(1+\kappa)/2$. At mlyle’s $\kappa=21/100$ this gives $J^{371/50}=J^{7.42}$. The pole of the nontruncated constant-density component at one cancels exactly.

For each fixed weight of nonzero mean and each fixed output phase there is also an explicit pointwise subsequence constant $0.000617\,|\mu_a|$ at exponent $j^{6+2\kappa}$. Its derivation via two certified low zeros, including the two-frequency positivity check for all allowed $W$, is given separately. The every-large-shell constant above is qualitative. [Two-frequency certificate and fixed-phase bounds](moving-mean.md) · [Mlyle’s matched power-short formula](https://github.com/mlyle/riemann-masullo/blob/c2eb094fffef928fdb72c2e180c255092e819347/research/5571/fourth-power-prime-curvature/spectral-interpolation-periodic-prime-convolution.md)

## Removing the continuous part of the periodic dilation

Write $P_\chi(s)=\sum_p\chi(p)\log p\,p^{-s}$, $R_\chi(s)=P_\chi(s)/[s(s+1)]$, and $M_a(s)=5^{-s}\sum_{r=1}^5a(r)\zeta(s,r/5)$. The full periodic dilation is

$$

 B_a(x)=\sum_{n\ge1}a(n)nS_\chi(x/n).

$$

Subtract the following continuous tail, a finite sum in $p<x^{1-\kappa}$:

$$

 I(x)=\sum_p\chi(p)\log p\int_0^\infty
       [W(t/N)-1](x-pt)_+\,dt .

$$

At $\kappa=21/100$, for each $\epsilon>0$,

$$

 G_a(x)=B_a(x)+\mu_a I(x)+O_{W,\epsilon}\bigl(\|a\|_2 x^{37/25+\epsilon}\bigr).

$$

Indeed, extend $a$ periodically to the integers. The difference on the left is the tail in mlyle’s calculation with its periodic measure replaced by

$$

       d\nu_a(t)=\sum_{n\in\mathbb Z}a(n)\delta_n(t)-\mu_a\,dt.

$$

This measure has total mass zero in a half-open period. Its first periodic primitive is bounded and piecewise linear, with jumps $a(n)$; choose its additive constant to give period mean zero. Its second periodic primitive has Fourier coefficients $O(\|a\|_2/(1+|k|)^2)$ for $k\ne0$, since the nonconstant Fourier coefficients of the measure are $O(\|a\|_2)$. Choose that primitive with zero mean as well, so its next primitive is bounded. The tail function $t\mapsto[W(t/N)-1](x-pt)_+$ vanishes near the origin. Periodic integration by parts gives the same single endpoint term $p[W(x/(pN))-1]$ times the second primitive at $x/p$, and regular derivative terms bounded in total by $O_W(\|a\|_2 x^2/N^3)$. Endpoint signs depend on which difference is taken and are immaterial in the error bound. The nonzero Fourier modes in the boundary term have frequencies $kx/(5p)$. Their $O(\|a\|_2/(1+|k|)^2)$ coefficients multiply the same fixed $\chi(p)\log p$, the same weights of bounded variation and the same dyadic ranges as mlyle’s reciprocal-prime calculation. Applying its exponent bounds gives $O_{W,\epsilon}(\|a\|_2 x^{37/25+\epsilon})$. This argument retains the constant Fourier coefficient of the measure in the separate term $\mu_a I$. [Original integration by parts, reciprocal-prime estimates and exponent ledger](https://github.com/mlyle/riemann-masullo/blob/c2eb094fffef928fdb72c2e180c255092e819347/research/5571/fourth-power-prime-curvature/spectral-interpolation-periodic-prime-convolution.md)

An elementary physical estimate covers $1/5\le\kappa<1$. The absolute boundary estimate is $O_W(\|a\|_2(x/N)^2)$ by Chebyshev, the sum of the $p\log p$ over $p\le x/N$. With the preceding regular error, this is $o(x^{(3+\kappa)/2})$ whenever $\kappa>1/5$. At $\kappa=1/5$, set $Y=x/N=x^{4/5}$. The boundary below $Y/D$, for any fixed $D>1$, is $O_W(\|a\|_2 Y^2/D^2)$. Partition $p\in[Y/D,Y]$ into blocks of length $Y^{7/10}$. The second primitive is globally Lipschitz with constant $O(\|a\|_2)$, since its first derivative is the bounded first primitive. On each block $p[W(x/(pN))-1]U_2(x/p)$ varies by $o_{D,W}(\|a\|_2Y)$: the phase argument varies by $O_D(xY^{7/10}/Y^2)=O_D(x^{-1/25})$. The fixed-modulus short-interval prime number theorem gives a uniform $o_D(Y^{7/10})$ bound for the signed quartic log-prime mass on each full block. The final partial block costs $O_W(\|a\|_2Y^{1+7/10}\log(2x))=o(\|a\|_2Y^2)$. Freezing the multiplier on each full block and then summing the absolute variation against Chebyshev gives $o_{D,W}(\|a\|_2Y^2)$. Letting $D\to\infty$ proves the endpoint. [Fixed-modulus short-interval prime number theorem](https://arxiv.org/pdf/2108.10878#page=3)

For the shell theorem every $0<\kappa<1$ works. There is a stronger elementary estimate after any fixed smooth log average. For $\mathcal K\in C_c^\infty(\mathbb R)$, $D_a=G_a-B_a-\mu_a I$, and every integer $m\ge2$,

$$

 \left|\int\mathcal K(h)D_a(Xe^h)\,dh\right|
      \ll_{\mathcal K,W,\kappa,m}\|a\|_2 X^{2-m\kappa}.

$$

In particular the error is smaller than every fixed negative power of $X$, for each fixed smooth test. Smoothness in this assertion is in the **logarithm of the terminal cutoff**. The matched zero-mean row itself agrees to the same accuracy with its full dilation after such a test. This bound uses only Chebyshev’s prime estimate.

To prove it put $V_0(u)=\mathcal K(\log u)/u$, supported in an interval $[c_0,C_0]\subset(0,\infty)$. After setting $u=e^h,\ r=t/X^\kappa,\ \ell=pX^{\kappa-1}$, the test function for prime $p$ against $d\nu_a(t)$ is $XH_\ell(r)$, where

$$

 H_\ell(r)=\int_{\ell r}^{\infty} V_0(u)
        [W(r/u^\kappa)-1](u-\ell r)\,du .

$$

It vanishes on $r\le c_0^\kappa$, with the zero extension to negative $r$. Only $\ell\le C_0/c_0^\kappa$ contribute. On $0\le r\le2C_0^\kappa$, repeated differentiation under the integral, including the endpoint, gives bounded derivatives of every fixed order uniformly for these $\ell$; the integrand is zero near $u=0$. Above this range $H_\ell(r)=-J(\ell r)$, where $J(v)=\int V_0(u)(u-v)_+du$, $J''=V_0$. Therefore the tail $L^1$-norm of its $m$-th derivative is bounded by $\ell^{m-1}\|V_0^{(m-2)}\|_1$. The centered periodic measure $\nu_a$ has a bounded periodic $m$-th primitive of norm $O_m(\|a\|_2)$, by its Fourier coefficients or repeated zero-mean integration. Integrating by parts $m$ times gives the bound $O(\|a\|_2 X X^{-(m-1)\kappa})$ for each contributing prime. Chebyshev gives $\sum_{p\ll X^{1-\kappa}}\log p\ll X^{1-\kappa}$, as required. All sums in the computation are finite for each $X$.

The estimate applies to the normalized row $f_a(y)=e^{-(1+\sigma_*)y}\Re G_a(e^y)$, $\sigma_*=(1+\kappa)/2$, by replacing the test by its product with $e^{-(1+\sigma_*)h}$ and extracting $X^{-(1+\sigma_*)}$. It also follows with a fixed power saving from the zero-free Mellin remainder after the two explicit residues are removed. [Two-residue Mellin continuation](moving-mean.md)

## Both primary zero spectra

Let $\widehat W(z)=z^{-1}+\int_1^2W(v)v^{z-1}dv$, the meromorphic Mellin transform. On $\Re z<0$ it also equals $\int_0^\infty[W(v)-1]v^{z-1}dv$. For any $d>1$, Mellin inversion gives

$$

 B_a(x)=\frac1{2\pi i}\int_{\Re s=d}M_a(s)R_\chi(s)x^{1+s}ds,\qquad
 I(x)=\frac{x^{1+\kappa}}{2\pi i}
   \int_{\Re s=d}\widehat W(1-s)R_\chi(s)(x^{1-\kappa})^sds .

$$

For the second identity put $t=Nv$ and take the Mellin transform of $\int_0^\infty(W(v)-1)(1-yv)_+dv$ in $y=p/x^{1-\kappa}$. Absolute integration on $d>1$ gives $\widehat W(1-s)/[s(s+1)]$. The pole of $M_a(s)$ at 1 has residue $\mu_a$. The pole of $\widehat W(1-s)$ there has residue $-1$. The two $x^2$ terms are consequently $\mu_a P_\chi(1)x^2/2$ and its negative. At real one $P_\chi$ is regular by the fixed-modulus prime number theorem or the prime-power logarithmic derivative identity below.

Let $Z_\chi$ be the distinct nontrivial zeros of $L(s,\chi)$, with multiplicities $m_\chi$, and set $s_\rho=\kappa+(1-\kappa)\rho,\ \sigma_*=(1+\kappa)/2$. After the above cancellation, define $H_a=B_a+\mu_a I$. For every $0<\kappa<1$,

$$

 \begin{split}
 H_a(x)={}&-\sum_{\rho\in Z_\chi}\frac{m_\chi(\rho) M_a(\rho)}
                      {\rho(1+\rho)}\,x^{1+\rho}\\
 &-\mu_a\sum_{\rho\in Z_\chi}
            \frac{m_\chi(\rho)\widehat W(1-\rho)}
                      {\rho(1+\rho)}\,x^{1+s_\rho}
          +o_{W,M}(x^{1+\sigma_*}) .
 \end{split}

$$

Both coefficient series are absolutely summable, uniformly on $\|a\|\le M$. Coincident exponents are added before taking a real projection. For $1/5\le\kappa<1$ the same pointwise expansion holds for $G_a$. At every $0<\kappa<1$, testing its normalized difference from $H_a$ against any fixed smooth compact log kernel costs exponentially little by the preceding argument.

For details, use $P_\chi(s)=-(L'/L)(s,\chi)+(L'/L)(2s,\chi^2)+R_3(s)$, where $R_3$ is absolutely convergent and bounded on $\Re s\ge2/5$. On that line $M_a(s)\ll_\epsilon\|a\|(2+|\Im s|)^{1/2+\epsilon}$, by the finite character decomposition, and $\widehat W(1-s)$ decays faster than every power by integration by parts against $W'$. After accounting for the pole at one, the two integrals with $R_3$ contribute $O(\|a\|x^{7/5})$ and $O_W(|\mu_a|x^{1+\kappa+(1-\kappa)2/5})$. Each exponent is strictly below $1+\sigma_*$.

For the two logarithmic derivatives shift separately to $\Re s=-1/10$, using the functional equations, good horizontal ordinates, and the fixed-conductor unit-slab zero count. The convexity bound for the finite combination $M_a$ there is $O_\epsilon(\|a\|(2+|\Im s|)^{3/5+\epsilon})$, integrable after division by $s(s+1)$. The second transform has arbitrarily rapid vertical decay. The polar terms at the origin and the left contour are of lower order in both evaluations. The direct and moved quadratic contributions at $z=\rho_\eta/2$, $\eta=\chi^2$, occur with weights $m_\eta(\rho_\eta)/2$ and the same two multipliers. They have absolutely summable coefficients. Each has exponent below $1+\sigma_*$, since $\Re\rho_\eta<1$. Dominated convergence gives their joint little-oh even if their real parts approach one. The two displayed primary sums and the claimed uniform error follow. [Contour bounds with the same quartic characters](secondary-spectrum.md) · [Dirichlet function estimates](https://link.springer.com/book/10.1007/978-1-4757-5927-3)

## Signed mass at every terminal prefix

For $y=\log x$ work first with $h_a(y)=e^{-(1+\sigma_*)y}\Re H_a(e^y)$ and group equal projected exponents in the two primary spectra, adjoining conjugates. Each coefficient $c_s(a)$ is real-linear in $a$ and $\sum_s\|c_s\|<\infty$. There is no real frequency since $\Re L(u,\chi)>0$ for $u>0$. Above every fixed $\sigma>\sigma_*$, the exterior exponents have a summable reciprocal-ordinate series. For the direct channel this follows from the fixed-conductor density theorem at $\sigma>1/2$. In the moved channel the required original threshold is $(\sigma-\kappa)/(1-\kappa)>1/2$, and rescaling the ordinate multiplies its reciprocal by a constant. [Fixed-conductor zero-density theorem](https://doi.org/10.1007/BF01404638)

At one of the two certified moved central exponents $s_{\rho_i}$, in the compact frequency set independent of $a$, the projected coefficient has modulus at least $0.000617|\mu_a|$. Indeed the shifted point is regular for the direct row and its reflection. The moved reflected quartic zero is absent. This leaves half the modulus of the single moved coefficient in every fixed orientation. The positive two-frequency cutoff test in the companion proof gives the stated lower. [Cutoff test and pole enclosures](moving-mean.md)

Apply the finite-dimensional compact-window argument at the critical value $\sigma_*$. More explicitly take the real space of all five-periodic weights, let $K=\bigcap_{\Re s>\sigma_*}\ker c_s$, and decompose $a=u+v$ with $u\in K,\ v\in K^\perp$. Finitely many exterior coefficients bounded below by a constant times $\|v\|$ suffice on the complement. For $\|v\|\ge e^{-ty}$, the divided test for one of these exponents dominates the error on the same fixed interval, exactly as in the centered theorem, with $1/2$ there replaced everywhere by $\sigma_*$. For smaller $\|v\|$, the positive exterior-annihilating kernel leaves $o(1)$ from $v$; for large $y$, $|\mu_u|\ge\delta/2$ and $\|u\|\le M$. Choose its smoothing bump nonzero at the two certified frequencies. The cropped $u$-series is an almost-periodic real function of mean zero with at least one such frequency. Compactness of $\{u\in K:\|u\|\le M,|\mu_u|\ge\delta/2\}$ gives fixed signed margins and common recurrence intervals. This gives positive lower integrals for each sign on one fixed log window for all allowed $a$. The cases $K=0$ and $K^\perp=0$ simply use the applicable one of the two cases. All the tests used here are smooth and compactly supported. The density $P_0$ starts with a smooth compact bump, the plateau density is a convolution of it with a uniform interval, and the divided tests are iterated compact smooth primitives. For each of these finitely many fixed tests, the normalized value on $G_a$ differs from the value on $H_a$ by $o(1)$ uniformly in $a$. This also holds for their bounded translates and for the real projections tested by complex densities, by conjugating the test where needed. Thus the bound $\int P |f_a|\ge|\int L_i f_a|/C_i$, and the two one-sided estimates using $P,P_0$, apply to the actual $f_a(y)=e^{-(1+\sigma_*)y}\Re G_a(e^y)$. [Complete compact-window proof](adaptive-weights.md)

Finally, on $X\le x\le X+H,\ X=j^4,\ H=(j+1)^4-j^4$, the total variation of the atomic part of $G_a''$ is $O(M(H+1)\log(2X))$. Indeed at a product $m=np$ its coefficient is bounded by $M\|W\|_\infty\sum_{p\mid m}\log p\le M\log m$. The regular part from differentiating $W$ has pointwise modulus $O_W(M)$ by Chebyshev: its weights are $O_W(1/X)$ and $O_W(1/X^2)$, supported at $n\asymp X^\kappa$, and $\sum_{n\asymp X^\kappa}1/n=O(1)$. The error from the linear chord is therefore $O_W(M H(H+1)\log(2X))=o(X^{1+\sigma_*})$. Convexity of the positive part and the cell's log-length $O(1/J)$ convert the signed integral to $\gg J^{1+4(1+\sigma_*)}=J^{7+2\kappa}$ up to a fixed constant, completing the proof on the genuine fourth-power samples.
