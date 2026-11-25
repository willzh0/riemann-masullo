# A single nonnegative annulus and a criterion using only primes up to the terminal index

For the primitive quartic character $\chi\bmod5$, $\chi(2)=i$, define for $y\ge1$

$$

 K(u)=
 \begin{cases}
 1-\frac32u,&0\le u\le 1/2,\\[2pt]
 (1-u)^2/(2u),&1/2<u\le1,\\
 0,&u>1,
 \end{cases}
 \qquad
 Q_\chi(y)=\sum_{p\le y}\chi(p)\log p\,K(p/y).

$$

The arithmetic deficit uses $\Re Q_\chi$. Its two sums involve only $p\equiv1$ and $p\equiv4\pmod5$, with opposite signs. The weight of every prime before its character sign is nonnegative and rational at integer arguments. For $E_\pm(J)=\sum_{j\le J}[\pm\Re Q_\chi(j)]_+$, and $\Theta_\chi=\sup_{\rho:L(\rho,\chi)=0}\Re\rho$ over nontrivial zeros,

$$

       \lim_{J\to\infty}\frac{\log(1+E_\pm(J))}{\log J}=1+\Theta_\chi .

$$

Each genuine zero with real part $\beta>1/2$ forces $E_\pm(J)\gg_\rho J^{1+\beta}$ at **every** sufficiently large $J$, already on a fixed-ratio terminal shell. The critical-line case gives $E_\pm(J)\asymp J^{3/2}$, with the lower on a fixed terminal shell. At an attained exterior abscissa the exact order is $J^{1+\Theta_\chi}$, and at an unattained one $E_\pm(J)=o(J^{1+\Theta_\chi})$ with the stated logarithmic exponent. Thus $E_-(J)\le J^{3/2+o(1)}$ along any unbounded sequence is equivalent to the critical-line hypothesis for this fixed character. Only primes $p\le J$ enter this finite prefix. The cofinal upper for the actual difference of these two residue classes remains open.

## The exact fourth-power arithmetic identity

Let $x=j^4,\ N=j^3$. Give the integer endpoints of $[N,2N]$ half weight, and give the other integers weight one. Define the single positive annular dilation

$$

 A(j)=\sum_{N\le n\le2N}^{\rm trap} nS_\chi(x/n),
 \qquad S_\chi(t)=\sum_p\chi(p)\log p\,(t-p)_+ .

$$

It has the exact identity

$$

 A(j)=j^7 Q_\chi(j)+
 \frac12\sum_{j/2<p<j}\chi(p)\log p\,p
       \left\{\frac{j^4}{p}\right\}
       \left(1-\left\{\frac{j^4}{p}\right\}\right).

$$

The correction is $O(j^2)$ by Chebyshev. In particular, after division by $j^7$, the discrepancy is $O(j^{-5})$. Summing the absolute discrepancies over all $j$ costs $O(1)$. The upper and lower criteria for $Q_\chi$ therefore also apply to the normalized actual annular samples.

Indeed $K(u)=\int_1^2(1-uv)_+dv$. The integral of $(j^4-pt)_+$ over $N\le t\le2N$ is exactly $j^7K(p/j)$. The unit trapezoids integrate every affine piece without error. Only the interior cell containing $v=j^4/p$ can have an error, and its two one-sided triangles give $p\{v\}(1-\{v\})/2$. An integer knot has zero correction. Summing the identity with the genuine factors $\chi(p)\log p$ proves the formula, including both endpoints and ramification at five. [Exact rational coefficient verifier](verify_linear_cutoffs.py)

## Why the averaging retains every right-hand zero

For every $y$, $Q_\chi(y)=\int_1^2(v/y)S_\chi(y/v)\,dv$. The once-integrated explicit formula for this odd quartic character is absolutely convergent:

$$

 S_\chi(t)=-\sum_{\rho}\frac{m_\chi(\rho)t^{1+\rho}}{\rho(1+\rho)}
                 +o_\chi(t^{3/2}) .

$$

Here $\rho$ runs over distinct nontrivial zeros. The prime squares contribute $o(t^{3/2})$ by the prime number theorem for the nonprincipal $\chi^2$. Higher prime powers cost $O(t^{4/3}\log^2(2t))$, and the gamma and trivial terms are $O(t\log(2t))$. There is no principal pole in the quartic row. Uniformity for $t\in[y/2,y]$ and absolute summability give

$$

 Q_\chi(y)= -\sum_\rho
     \frac{m_\chi(\rho)h(\rho)}{\rho(1+\rho)}\,y^\rho+o(y^{1/2}),
 \qquad h(s)=\int_1^2 v^{-s}dv=\frac{2^{1-s}-1}{1-s}.

$$

Since $0<\Re\rho<1$, $|2^{1-\rho}|>1$; hence $h(\rho)\ne0$ at **every** nontrivial zero. In the real projection, the coefficient at a point of the divisor or its reflection equals

$$

    -\frac{[m_\chi(\rho)+m_\chi(\bar\rho)]h(\rho)}
                 {2\rho(1+\rho)} .

$$

Thus the two multiplicities add at coincident frequencies. The absolute coefficient series bounds $Q_\chi(y)=O(y^{\Theta_\chi})$, with little-oh at an unattained supremum. The uniform sampling step is particularly simple: $K$ is continuously differentiable on the positive axis with bounded derivative. Chebyshev gives $|Q'_\chi(y)|\ll y^{-2}\sum_{p\le y}p\log p\ll1$, so replacing a real argument by a neighboring integer costs $O(1)$. [Actual quartic explicit formula and prime-power removal](PHASE.md) · [Mlyle’s quartic arithmetic calibration](https://github.com/mlyle/riemann-masullo/tree/3f90b6c75f2e36f52c2c9cb427155a556bcee9d8/research/5571/quartic-mod-five-deficit)

For each exterior zero use the compact positive annihilator and its divided test at the specified point, on $\Re\rho>\sigma$, $1/2<\sigma<\beta$, applied to $y^{-1/2}\Re Q_\chi(y)$ on the logarithmic variable. The fixed-conductor density theorem supplies the summable reciprocal-ordinate condition. The coefficient displayed above survives at the target. The positive-test integral is $O(y^{\sigma-1/2})$, and the divided test isolates a term of modulus $\gg_\rho y^{\beta-1/2}$ up to the same error. Domination of the divided test by the positive one gives both signed integrals on a fixed log window. Returning to $y\in[\lambda J,J]$ and applying the $O(1)$ interpolation loss gives both signed sampled sums $\gg_\rho J^{1+\beta}$. A single $\sigma$ and one shell suffice for $\beta$ near an exterior supremum. If there are no exterior zeros, the normalized series is real, uniformly almost periodic and has mean zero: the real part of $L(s,\chi)$ is positive for real $s>0$. At least one actual critical coefficient is nonzero. Its positive and negative fixed margins recur with bounded gaps, proving both $J^{3/2}$ lower bounds in this case. These lower bounds, the absolute upper and dominated convergence give all the asserted regimes. [Proof of the compact one-sided test](adaptive-weights.md) · [Finite quartic zero certificate](https://github.com/willzh0/riemann-masullo/blob/53cac8a4461b84ad1d9c96ea2305f48e82ba4a31/PROOF.md)

## A smooth annulus at any fixed power scale

For $0<\kappa<1$ write $N=x^\kappa$. Choose a nonnegative smooth $V$ supported strictly inside $(1,2)$ such that $\widehat V(z)=\int V(v)v^{z-1}dv\ne0$ on $\Re z>0$. An explicit construction takes $V(e^t)$ to be the density of $\tfrac12\log2+\sum_{n\ge1}U_n$, where independent $U_n$ are uniform on $[-a_n,a_n]$, $a_n=2^{-n-3}\log2$. The radii sum to $(\log2)/8$. The transform is $e^{z\log2/2}\prod_n\sinh(a_nz)/(a_nz)$, zero-free off $\Re z=0$ by local normal convergence of the product and $\sum_n a_n^2<\infty$. On the imaginary axis its first $m$ factors give $O_m((1+|t|)^{-m})$ for every fixed $m$. Fourier inversion gives the smooth compact density. Multiplication by a fixed positive scalar can place $V$ below one. This elementary compact convolution uses mlyle’s dyadic zero-free test principle, with its interval rescaled in logarithmic coordinates. [Mlyle’s compact profile](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7149073962) · [Translated Gevrey profile](https://github.com/mccorvie/riemann-masullo/pull/7571)

Take $A_\kappa(x)=\sum_n V(n/N)nS_\chi(x/n)$ on the genuine integers. The proof by log testing the centered integer comb applies with $V$ in place of $W-1$. Equivalently choose a smooth cutoff equal to a constant strictly between zero and one on the support of $V$, then perturb by a sufficiently small positive multiple of $V$ and subtract the two cutoff identities. The primary direct terms cancel and the moved coefficient in the real projection is exactly

$$

 -\frac{[m_\chi(\rho)+m_\chi(\bar\rho)]\widehat V(1-\rho)}
              {2\rho(1+\rho)}
 \quad\hbox{at }\quad s=\kappa+(1-\kappa)\rho .

$$

All quartic zeros are visible. Compact selection as above gives the lower exponent $5+4[\kappa+(1-\kappa)\Theta_\chi]$ for either sign of the actual sampled prefix $\sum_{j\le J}[\pm\Re A_\kappa(j^4)]_+$, already on a fixed terminal shell. The critical order when $\Theta_\chi=1/2$ is $J^{7+2\kappa}$. The matching upper holds on the untested physical row since $|S_\chi(t)|\ll t^{1+\Theta_\chi}$ and $n\asymp x^\kappa$, also for $\Theta_\chi=1$. An unattained supremum gives $o(x^{1+\kappa+(1-\kappa)\Theta_\chi})$ by the same true-prime bound with little-oh, uniformly on that annulus. This proves an exact all-prefix exponent while using only prime cutoffs $x/(2N)<x/n<x/N$. At every fixed $\beta>1/2$ from a zero the individual lower order is $J^{5+4[\kappa+(1-\kappa)\beta]}$ at every sufficiently large prefix. [Tested physical expansion and fourth-power sampling](moving-spectrum.md)

The normalized triangular prime kernel in the first part is a sharp-annulus version available at $\kappa=3/4$. It requires no infinite convolution or numerical evaluation of a smooth kernel to compute its finite values.
