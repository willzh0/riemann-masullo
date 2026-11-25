# A prime-side check and a local prime-power limit

Masullo, §12.3, p. 514, and Theorem 12.5.1.1, pp. 519–520. Work on the rational principal angular row. As in the adjacent README, divide each logarithmic profile by the norm-one Haar volume to realize it as an idèle-class test. The center in the first two sections is zero. Write $m_\rho$ for the multiplicity of a zero of the completed zeta function and $d_\rho$ for the number of jets lost on restriction from half-width $\beta$ to $\alpha$. An equality with a Hilbert-space trace uses the actual nuclear convolution hypotheses of [#7630](https://github.com/mccorvie/riemann-masullo/pull/7630). The scalar calculations use the displayed weights.

## The two fixed translates

For the full pair $\alpha=0,\ \beta\ge1$, every nontrivial zero is strictly inside the larger strip. There are no positive-order zeros of the completed zeta function on the narrower line. Thus $d_\rho=m_\rho$ for every site. For a real test $H$ compactly supported in $x>0$, write $\widehat H(z)=\int H(x)e^{zx}\,dx$. The classical explicit formula gives
$$
 \sum_\rho m_\rho\widehat H(\rho)=
 \widehat H(1)-\sum_{n\ge2}\Lambda(n)H(\log n)
 -\int_0^\infty \frac{H(x)}{e^{2x}-1}\,dx .
$$
Indeed the distributional derivative of $\psi(e^x)$ is the sum of point masses at the logarithms of prime powers. In the von Mangoldt formula the derivative of $-\frac12\log(1-e^{-2x})$ is $-1/(e^{2x}-1)$. Equivalently one can shift the smoothed contour for $-\zeta'/\zeta$. The transform decay gives absolute convergence of the resulting nontrivial zero sum. [Connes and Marcolli, *Noncommutative Geometry, Quantum Fields and Motives*, Chapter 2, §2, equation (2.19)](https://www.math.fsu.edu/~marcolli/bookweb.pdf)

The profile in the adjacent README has $\widehat H(1)=0$. Its two translates at $c=7/4,\,2$ involve, respectively, 8 and 11 prime powers. At the first center these are $3,4,5,7,8,9,11,13$. The second also sees $16,17,19$. The enclosed full zero sums are $2.837245912148697$ and $-2.530845768779735$, each with error below $6\cdot10^{-16}$, uniformly in the allowed even smoothing density.

The calculation evaluates derivatives of the sixteen-box spline before smoothing from its truncated-power formula. Evenness bounds the smoothing error in each local value by $\epsilon^2/2$ times the supremum of its second derivative on the smoothing interval. For the last integral, sum $\widehat H(-2k)$ through $k=40$. Its positive tail is at most
$$
  10^{-4}\sum_{k>40}24 k^4 e^{-2k(c-1-\epsilon)} .
$$
Every term and the geometric tail majorant is evaluated by Arb in the accompanying script. The prime-side function takes no zero ordinates, counts, or values of zeta as input.

The same two translates have opposite signs simultaneously at every fixed $0\le\alpha<1/2\le\beta$ and $s>1$, including $\beta=1/2$. The fourteen positive low sites of the zero-side certificate are simple and central. The narrow width retains none and the wide width retains each one, at the boundary because $0<(s-1)/2$. At any height $0\le d_\rho\le m_\rho$. Replacing the bound $\Re\rho\le3/4$ in the high-tail proof by the full $0<\Re\rho<1$ gives
$$
 3(1+(3/(2T))^2)^2 e^{c+\epsilon}(16\cosh(1/16))^{16} T^{-10},\qquad T=64,
$$
before multiplication by $10^{-4}$. The uniform enclosures are $[2.8087,2.8658]$ and $[-2.5675,-2.4942]$. The separate prime calculation applies to the full pair. [Project jet count at the boundary](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L733)

## Recovering each prime power at arbitrarily short support

Fix $0\le\alpha<1/2<\beta$, a common $s>1$, a location $c>0$, and $g\in C_c^\infty(\mathbb R)$ supported on $[-1,1]$. Let $P(z)=(z^2-\tfrac14)z(z-1)$. For bounded real $t$ and $0<\eta<1$ use the uniformly bounded profile
$$
 H_{\eta,t}(x)=\eta^4 P(-\partial_x)g\big((x-c-\eta t)/\eta\big).
$$
For small $\eta$ its support lies above norm one. It kills all four moments $-1/2,0,1/2,1$. Define $\lambda(c)=\log p$ if $c=\log(p^k)$, $k\ge1$, and $0$ otherwise. Then
$$
 \sum_\rho d_\rho\,\widehat H_{\eta,t}(\rho)
   =-\lambda(c)g^{(4)}(-t)+O(\eta^\nu).
$$
Choose $1/2<\sigma_0\le3/4$ with $\sigma_0-1/2\le\min(1/2-\alpha,\beta-1/2)$. Every $0<\nu<1-3(1-\sigma_0)/(2-\sigma_0)$ works. All other parameters are fixed, and the constant is uniform for bounded $t$.

For the full zero sum apply the displayed explicit formula. The support eventually sees only the prime-power site at $c$, if there is one, and
$$
 H_{\eta,t}(c)=g^{(4)}(-t)+\eta g'''(-t)-\tfrac14\eta^2 g''(-t)-\tfrac14\eta^3 g'(-t).
$$
The smooth integral is $O(\eta^5)$ by moving the four-term differential operator onto $(e^{2x}-1)^{-1}$ on a fixed compact positive interval. For the lost jets, the missing weights $0\le m_\rho-d_\rho\le m_\rho$ vanish whenever $|\Re\rho-1/2|<\sigma_0-1/2$, since such sites lie in the wide interior and outside the narrow strip. By reflection about the critical line, conjugation, and Ingham's zero-density theorem, the remaining multiplicities up to height $T$ total $O(T^{3(1-\sigma_0)/(2-\sigma_0)}\log^5(2T))$ for $T\ge2$. Integration by parts in the compact base profile gives, for every $A$,
$$
 |\widehat H_{\eta,t}(z)|\ll_A\eta(1+\eta|\Im z|)^{-A}
 \qquad (0\le\Re z\le1).
$$
Indeed the transformed derivative multiplier $\eta^4P(z)$ costs at most a fixed multiple of $(1+\eta|\Im z|)^4$, absorbed by taking four further integrations in the base transform. Sum first up to $1/\eta$, then over dyadic height intervals. This bounds the absolute missing mass by $O(\eta^\nu)$ and proves the formula. For the recorded widths $1/4,3/4$ any $\nu<2/5$ with $\nu>0$ works. [Ingham, *On the estimation of N(σ,T)*, Quarterly Journal of Mathematics (1940), pp. 201–202](https://doi.org/10.1093/qmath/os-11.1.201) · [Explicit form with its multiplicity convention (2025), Introduction](https://arxiv.org/abs/2507.15184)

For instance choose $g(u)=\exp(-1/(1-u^2))$ for $|u|<1$ and zero outside. It has $g^{(4)}(0)=-12/e$ and $g^{(4)}(1/2)=(70144/6561)e^{-4/3}>0$. At the logarithm of *any* prime power the two translates $t=0,1/2$ therefore have strictly opposite signs for sufficiently small $\eta$. Their separation is $\eta/2$. This argument requires neither a numerical low-zero list nor a simplicity assumption.

## The centered exterior sum

For the actual rational principal row of Theorem 12.5.1.1, fix any $\alpha>0$. Here the summation criterion is $|\Re\rho-1/2|\ge\alpha$, including equality, and the Mellin argument is $\rho-1/2$. Use the same normalized $H_{\eta,t}$ on log norm. Its norm-one invariance selects the principal angular row, and its support ensures the required vanishing on norm one. The same transform bound holds on $-1/2\le\Re z\le1/2$. Directly applying the density bound with $\sigma_0-1/2\le\alpha$ gives
$$
 \sum_{|\Re\rho-1/2|\ge\alpha}m_\rho\,|\widehat H_{\eta,t}(\rho-1/2)|\ll\eta^\nu .
$$
This is an absolute estimate for a shrinking family of prescribed tests on one character and each fixed width. Issue #5571 asks for exact cancellation at every individual admissible test and every character. [Literal exterior-zero statement](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch12_TraceGeometric/Sec5.lean#L98)


One can see the underlying regularity directly. Put $w_\rho=\rho-1/2$. The function
$$
 B_\alpha(x)=\sum_{|\Re w_\rho|\ge\alpha}m_\rho\, e^{w_\rho x}/w_\rho
$$
converges absolutely and uniformly on each compact real interval. The same dyadic count bounds its modulus of continuity there by $O(|h|^\nu)$: below height $1/|h|$ each difference after division by $w_\rho$ costs $O(|h|)$; above it each costs $O(1/|w_\rho|)$. The distributional derivative $B_\alpha'$ is the centered exterior distribution. Consequently, if it is represented by a measure on an open log-norm interval, that measure has no atoms there. An open interval on which exact vanishing is available is a much stronger input and already has a separate arithmetic detection argument. [Earlier local equivalence for prime-free intervals](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7146104165)

