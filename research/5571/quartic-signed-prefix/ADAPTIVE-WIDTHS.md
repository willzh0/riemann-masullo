# A different smoothing width at each prime sample

For either primitive quartic character $\chi\bmod5$, let $Q(x)=\sum_p\chi(p)\log p\,K(p/x)$ with $K(t)=\int_1^2(1-tv)_+dv$. Write $q_\delta(x)=\Re Q_\delta(x)$ for the compensated Gaussian smoothing in the [fixed-prefix proof](README.md), with $Q_0=Q$. Let $\Theta$ be the supremum of the real parts of the nontrivial zeros of $L(s,\chi)$. Given a sequence of widths $\delta_j$, set
$$
 E_\pm(J;\delta)=\sum_{j=1}^J[\pm q_{\delta_j}(j)]_+ .
$$

1. **Every polynomial decay rate preserves the criterion.** If $0\le\delta_j\ll j^{-\kappa}$ for any fixed $\kappa>0$, then both signed prefixes have ordinary logarithmic exponent $1+\Theta$. Each exterior zero of real part $\beta$ forces both signed prefixes to be $\gg J^{1+\beta}$ at every sufficiently large $J$. Consequently a cofinal $J^{3/2+o(1)}$ upper for even one sign is equivalent to the critical-line hypothesis for this quartic.
2. **At an attained supremum**, every bounded sequence of widths converging to a fixed width has $E_\pm(J;\delta)\asymp J^{1+\Theta}$. The same holds for bounded sequences satisfying $\sup_{\lambda J\le j\le J}|\delta_j-\delta_J|\to0$ for every fixed $0<\lambda<1$.
3. **At an unattained supremum**, each nondegenerate interval $I\subset[0,\infty)$ of squared widths contains a zero of $v\mapsto q_{\sqrt v}(x)$ for every sufficiently large real $x$. The resulting independent choices can satisfy $\delta_j\to0$ and $\delta_{\lfloor tj\rfloor}/\delta_j\to1$ uniformly for $t$ in each compact subinterval of $(0,\infty)$, while $q_{\delta_j}(j)=0$ for every sufficiently large integer $j$. The widths may be chosen to decay more slowly than any one prescribed function tending to zero. Their values inside each narrow band may depend on the sample. The squared-width annihilator and its collision argument were independently derived and checked against the genuine projected divisor.

Thus the existence of **some** vanishing width schedule with a cofinal critical-exponent upper for one sign is equivalent to the alternative that $\Theta=1/2$ or $\Theta$ is unattained. In particular, permitting arbitrarily slow and sample-dependent shrinkage loses the ability to detect nonattainment. The mathematical status of the actual quartic zeros remains open. The independent [logarithmic-variance calculation](LOG-WIDTHS.md) treats growing widths and a sharp threshold for bounded per-sample adjustments.

## Uniform expansion and polynomial shrinkage

Use the actual prime formula
$$
 q_0(x)=\sum_{\rho\in{\cal Z}_\chi\cup\overline{{\cal Z}_\chi}}
    b_\rho x^\rho+e(x),\qquad
 b_\rho=-\frac{m_\chi(\rho)+m_\chi(\bar\rho)}2
             \frac{2^{1-\rho}-1}{(1-\rho)\rho(1+\rho)},\qquad e(x)=o(\sqrt x).
$$
The sum is over distinct points. Conjugate coincidences add multiplicities, and every displayed $b_\rho$ is nonzero. The ramified prime five contributes zero. The proper-power and gamma terms are included in $e$. The coefficient series is absolutely summable by the cubic kernel and the two-sided zero count $N(T)\ll T\log(2T)$. The supremum $\Theta$ is unchanged on adjoining the conjugated divisor. [Prime expansion and terminal shell bounds](https://github.com/willzh0/riemann-masullo/blob/b61df9f867cec621a23ea9cfc7a5ff9c8b7f8622/research/5571/quartic-periodic-dilation/linear-prime-cutoffs.md) · [Bennett et al., zero counts](https://arxiv.org/abs/2005.02989)

For bounded $v=\delta^2\ge0$ the multiplier is
$$
 \Phi_v(s)
   =e^{vs^2/2}+e^{v(s^2-1)/2}-e^{v(s^2-1/2)},\qquad
 1-\Phi_v(s)=(1-e^{vs^2/2})(1-e^{v(s^2-1)/2}).
$$
It commutes with conjugation. The smoothed remainder is uniformly $o(\sqrt x)$ on every compact width range. Indeed $e(t)$ is bounded on $0<t<1$. Split the Gaussian shift at $h=-(\log x)/2$. After division by $\sqrt x$, the lower part is $O_\Delta(x^{-1/4})$ and the upper part is $O_\Delta(\sup_{t\ge\sqrt x}|e(t)|/\sqrt t)$, for widths up to $\Delta$. Also $\sup_{\delta\le\Delta,\ 0<\Re s<1}|\Phi_{\delta^2}(s)|<\infty$. [Uniform remainder calculation](README.md)

For $0<\delta\le1$ at a divisor point $s=\beta+i\gamma$ the product identity gives
$$
 |1-\Phi_{\delta^2}(s)|\ll\min\{1,\delta^4(1+|\gamma|)^4\}.
$$
For the second bound use $|e^z-1|\le |z|\max(1,e^{\Re z})$. Multiply by the cubic coefficient bounds, including the multiplicities. Summing up to $1/\delta$ costs $O(\delta^4(1/\delta)^2\log(2/\delta))$, and the remaining inverse-cube tail costs $O(\delta^2\log(2/\delta))$. Hence, uniformly at each sample,
$$
 |q_\delta(x)-q_0(x)|
 \ll x^\Theta\delta^2\log(2/\delta)+o(\sqrt x).
$$
For $\delta_j\ll j^{-\kappa}$ the first term is $O(j^{\Theta-2\kappa}\log(2j))$, with the evident convention at width zero. If $\Theta>1/2$, choose a zero with $\beta>\max(1/2,\Theta-2\kappa)$. The true unsmoothed terminal-shell lower at that zero dominates the summed error. For each other exterior zero one may use the same argument at a zero of at least its real part, strictly above the error exponent. A sequence of zeros tending to $\Theta$ gives the lower logarithmic exponent, and absolute summability gives the upper. Under the critical-line hypothesis the summed difference is $o(J^{3/2})$, and the true unsmoothed signed lower is $\gg J^{3/2}$. These arguments compare each summand with its own width.

## The attained case

For bounded widths, divide by $x^\Theta$. Dominated convergence in the absolutely summable divisor series gives, uniformly in $\delta$,
$$
 x^{-\Theta}q_\delta(x)=A_\delta(\log x)+o(1),\qquad
 A_\delta(t)=\sum_{\Re\rho=\Theta} b_\rho\Phi_{\delta^2}(\rho)e^{i\gamma t}.
$$
Choose a fixed boundary point. Its coefficient modulus has a positive minimum on any compact width range since $\Phi_v(\rho)$ never vanishes there. Indeed, with $z=e^{v\rho^2/2}$, $\Phi_v=z(1+e^{-v/2}-e^{-v/2}z)$ and $|z|<e^{v/2}<1+e^{v/2}$ for $v>0$. At $v=0$ the multiplier is one. There are no zero ordinates on this boundary. The historical critical-line verification and positive completed zero sum exclude such ordinates everywhere in this example. [Low zero masses and verified heights](QUARTIC_LINEAR_HEIGHT.md)

Mean integrals of $A_\delta$ on intervals of length $L$ tend to zero as $L\to\infty$, uniformly in their starting point and in $\delta$. Mean integrals of $e^{-i\gamma_0 t}A_\delta$ tend uniformly to the coefficient at the chosen boundary ordinate $\gamma_0$. To verify both statements first keep finitely many terms, then use the uniform absolute tail. The modulus integral therefore has a uniform positive lower mean, and $2[u]_\pm=|u|\pm u$ gives the same conclusion for both signs. A single fixed log-window length suffices. Conversion to integer cutoffs on $[\lambda J,J]$ costs $O_\Delta(J)$ for a fixed width by the uniform derivative bound from the earlier proof.

The map $\delta\mapsto A_\delta$ is uniformly continuous into the supremum norm on each compact width range, again by the absolute tail. Replacing $\delta_J$ by the separate $\delta_j$ on that shell costs $o(J^{1+\Theta})$ under the hypothesis of conclusion 2. This proves both lower bounds and the matching upper. In particular it applies to every sequence converging to any finite width.

## The unattained case and the positive test in squared width

Assume $\Theta$ is unattained. Then $\Theta>1/2$, since the quartic has certified critical zeros. Fix an interval $I$ of positive length in the nonnegative squared-width axis. For any $\sigma>1/2$, fixed-conductor zero density gives
$$
 \sum_{\Re\rho>\sigma,\ \gamma>0}(\beta\gamma)^{-1}<\infty.
$$
The conjugated divisor added above costs at most a factor two. Montgomery's density bound has exponent $3(1-\sigma)/(2-\sigma)<1$ at fixed conductor, with a harmless power of $\log T$. Dyadic summation gives the displayed convergence. As $\sigma$ increases to an unattained $\Theta$, the sum tends to zero by dominated convergence. [Montgomery, Theorem 12.1](https://doi.org/10.1007/BFb0060851)

For each remaining high point take its three width exponents
$$
 w_1(\rho)=\rho^2/2,\qquad w_2(\rho)=(\rho^2-1)/2,\qquad
 w_3(\rho)=\rho^2-1/2.
$$
Their positive imaginary parts are $\beta\gamma,\beta\gamma,2\beta\gamma$. Use mlyle’s positive two-atom factor for $w=a+it$ at $0,\pi/t$, with masses in the ratio $e^{a\pi/t}$ to $1$, normalized to total one. Its bilateral Laplace transform vanishes at $w$ and $\bar w$. The infinite convolution $\mu$ exists on $[0,L]$ as the law of a sum of independent bounded nonnegative variables, where
$$
 L\le(5\pi/2)\sum_{\Re\rho>\sigma,\ \gamma>0}(\beta\gamma)^{-1}.
$$
Thus choose $\sigma<\Theta$ so close that $3L<|I|$. Arbitrarily negative real parts of the $w_i$ leave the masses positive and the support bound intact. The transform of the full compact probability vanishes at all the named exponents. [Mlyle’s compact positive test and division](https://github.com/mlyle/riemann-masullo/blob/69f6639d0e53c2a04aa3b5f8487a1be237274b97/research/5571/square-prefix-fixed-window-count/README.md)

Pick one projected point $\rho_0=\beta_0+i\gamma_0$ with $\beta_0>\sigma,\gamma_0>0$. Let $w=w_1(\rho_0)$. The entire transform of $\mu$ is nonzero at zero, so its zero at $w$ has some finite order $m$. Divide by $(s-w)^m$ to get the transform of a nonzero bounded complex density $V$ on $[0,L]$. For one division take the negative of $e^{-wt}\int_{(-\infty,t]}e^{wu}d\mu(u)$ and integrate by parts. It vanishes past $L$ since the transform at $w$ is zero. Repeat for the remaining order. The quotient still vanishes at every other named point, including $\bar w$. The density $P=\mu*\mathbf1_{[-L,L]}$ annihilates all of them and equals one on $[0,L]$ up to immaterial endpoints. Hence $|V|\ll P$. Translate both tests together so their supports lie inside $I$.

The only upper-half-plane divisor points that can contribute at the selected width exponent are
$$
 \rho_0 \quad (w_1),\qquad s_2=\sqrt{\rho_0^2+1}\quad(w_2),\qquad
 s_3=s_2/\sqrt2\quad(w_3)
$$
with the root in the first quadrant. Negative ordinates give negative imaginary parts. The three real parts are distinct. Setting $r=(\Re s_2/\beta_0)^2$ gives
$$
      1=\beta_0^2(r-1)+\gamma_0^2(1-1/r).
$$
The right side increases with $r$, is zero at 1 and exceeds 1 at 2 since $|\gamma_0|>H=20,000,000$. Therefore $\Re s_3<\beta_0<\Re s_2$. Among the actual contributors with real part above $\sigma$, the one of largest real part is unique and has nonzero coefficient. In particular no opposite-ordinate multiplicity can cancel it.

Integrate the true function $v\mapsto q_{\sqrt v}(x)$ against the two tests. The integral against $P$ is $O_I(x^\sigma)$. The integral against $V$ consists of the finite collision group at $w$ plus $O_I(x^\sigma)$. Its modulus is $\gg_I x^{\beta_0}$ for every sufficiently large $x$ by the strict ordering. All the remaining infinitely many points with $\Re\rho\le\sigma$ have uniformly bounded total coefficients on the compact width interval, and the smoothed remainder is $o_I(\sqrt x)$. Consequently $\int P|q_{\sqrt v}(x)|\,dv\gg_I x^{\beta_0}$. Both signs have positive integrals for all sufficiently large $x$. Continuity in $v$ follows from the representation by one standard Gaussian per component and $|Q(t)|\ll t$. The intermediate value theorem supplies an exact zero in $I$ for each such $x$.

For a slowly vanishing schedule use the squared-width intervals whose square roots are $[(1-1/n)/n,(1+1/n)/n]$, $n\ge2$. Choose increasing integer starting points $X_n$ beyond the individual onsets with $X_{n+1}\ge e^nX_n$. On each $[X_n,X_{n+1})$ choose any exact root within its band. If $g(j)\to0$ is prescribed, also choose $X_n$ so $|g(j)|\le n^{-2}$ for $j\ge X_n$. The resulting positive widths satisfy $g(j)/\delta_j\to0$. For large $j$, multiplying $j$ by a factor in a fixed compact positive interval crosses at most one block boundary, and ratios between widths in neighboring bands tend uniformly to one. The choice inside a band can oscillate. Monotone vanishing widths in the unattained case require a separate argument.

## Bounded widths without a required limit

There always exists a bounded per-sample schedule making the real row exactly zero for every sufficiently large integer. In the unattained case this follows already in any prescribed nondegenerate width interval. For an attained $\Theta$, choose on the boundary a pair of least absolute ordinate $\gamma_0>0$. Its projected coefficient is nonzero. With $v=\delta^2\to\infty$ the multiplier at $\rho_0=\Theta+i\gamma_0$ is $e^{v\rho_0^2/2}(1+o(1))$. After division by its modulus the absolute sum of the contributions from all the other boundary pairs tends to zero, by dominated convergence using $|\gamma|>\gamma_0$ and the absolute coefficient bound. For $k=0,1,2$ use the three fixed squared widths $v_k=A+2\pi k/(3\Theta\gamma_0)$. For sufficiently large fixed $A$, after each output is divided by its own positive damping factor, the three dominant cosines are spaced by $120$ degrees up to an arbitrarily small error. At every log position at least one cosine is $\ge1/2$ and one is $\le-1/2$. The normalized subboundary and true prime remainders tend to zero for these three fixed widths. For every sufficiently large $x$ the actual three real values therefore include both signs, and continuity gives an exact root in $[v_0,v_2]$. Three fixed choices suffice to suppress either prescribed sign. This case may require a character-dependent interval of large widths.

## One prescribed terminal sample using only primes up to its square

For $x\ge2$ define
$$
 {\cal A}_\pm(x)=\int_0^{\log x} e^{-4v}\left[\pm\Re
 \sum_{p\le x^2}\chi(p)\log p\int_{\mathbb R}
      K\!\left(\frac{p}{xe^h}\right)d\nu_{\sqrt v}(h)\right]_+dv .
$$
This uses finitely many primes at one terminal input. For both signs,
$$
  \lim_{x\to\infty}\frac{\log(1+{\cal A}_\pm(x))}{\log x}=\Theta .
$$
Each exterior zero of real part $\beta$ forces $\mathcal A_\pm(x)\gg_{\chi,\rho}x^\beta$ at every sufficiently large real $x$. If $\Theta$ is attained, both quantities are $\asymp x^\Theta$, including at $\Theta=1/2$. At an unattained supremum both are $o(x^\Theta)$. Thus along any prescribed unbounded sequence $x$, an upper $\mathcal A_-(x)\le x^{1/2+o(1)}$ is equivalent to the fixed quartic’s critical-line hypothesis. Proving this upper at any unbounded sequence remains open.

For the proof first integrate the true $[\pm q_{\sqrt v}(x)]_+$ over $0\le v<\infty$ against $e^{-4v}dv$. Under nonattainment, the positive-test proof gives $\int_I[\pm q_{\sqrt v}(x)]_+dv\gg_{\rho,I}x^\beta$ on any fixed width interval, by choosing $\sigma$ above the requested $\beta$ and still close enough to $\Theta$ for the support bound. Under attainment, the three sign witnesses above have uniformly positive normalized margins at their respective widths. Uniform continuity of the family $A_{\sqrt v}$ into the supremum norm on that compact interval gives a subinterval of fixed positive length around each witness on which half its margin persists, for every log position. The uniform normalized true remainder vanishes. Integrating therefore gives the attained lower of order $x^\Theta$ at every sufficiently large $x$. These compact intervals have a fixed positive minimum weight $e^{-4v}$.

On the entire positive axis $|Q(t)|\ll t^\Theta$ by the absolute explicit formula, and $Q(t)=0$ below 2. Hence for $x\ge1$,
$$
 x^{-\Theta}|Q_{\sqrt v}(x)|\ll\int e^{\Theta h}d|\nu_{\sqrt v}|(h)
                        \le3e^{v/2}.
$$
This majorant is integrable against $e^{-4v}dv$. At an unattained $\Theta$ the normalized series tends to zero for each fixed width. Dominated convergence proves the upper and little-oh claims for the infinite integral.

To truncate the primes at $N=x^2$, note that a prime beyond $N$ can appear only for $xe^h>N$. Chebyshev and $0\le K\le1$ give a total weighted absolute loss at most
$$
 2\frac{x^2}{N}\int_0^\infty e^{-4v}\!\int e^{2h}\,d|\nu_{\sqrt v}|(h)\,dv
 \le 2\frac{x^2}{N}\int_0^\infty(2e^{-2v}+e^{-v/2})\,dv=6 .
$$
The truncation in $v$ beyond $\log x$ costs at most $(12/7)x^{-5/2}$, since $|Q_{\sqrt v}(x)|\le 6xe^{v/2}$ by the same elementary estimate for all primes. Apply the variance truncation to the full row first, and then the prime truncation on the retained variance interval. The positive part is 1-Lipschitz, so both errors apply to each signed integral separately. This proves the finite-input theorem.

The continuous width integral can itself be replaced by a **finite sum** with error at most 3. Put $N=x^2$, $n=\lceil N\rceil$, and partition $0\le\delta\le\sqrt{\log x}$ at multiples of $1/n$, including the final endpoint. Evaluate the signed positive part at each left endpoint, with exact weight $\int_{\delta_l^2}^{\delta_r^2}e^{-4v}dv$. For $k(r)=K(e^r)$ one has $0\le k\le1$ and $|k'|\le1$ on the whole real axis by the two-knot formula. If $Z$ is standard normal, each finite-prime Gaussian weight is $(1+c)\mathbb E k(r-\delta Z)-c\mathbb E k(r-\sqrt2\delta Z)$. Its derivative in $\delta$ has absolute value at most $2+(2+\sqrt2)\mathbb E|Z|<6$, including the limiting right derivative at zero. Thus the finite row is $6\sum_{p\le N}\log p\le12N$ Lipschitz. The total quadrature weight is at most $1/4$, giving error at most $3N/n$. All prime weights at positive widths have explicit formulas in terms of the ordinary Gaussian tail on the three pieces of $K$. This finite sum has the same exponent and cofinal criterion.

A second, fixed positive weight gives an asymptotically smaller prime cutoff if desired. Use $e^{-4v-v^2}$ and $N=\lceil\min(x^2,x\exp(6(\log x)^{3/4}))\rceil=x^{1+o(1)}$. All compact lower tests remain positive, and the variance and mesh errors have the same bounds. For $x\ge e$, set $a=(\log x)^{1/4}\ge1$ and $L=6(\log x)^{3/4}$. For primes above $xe^L$ the expected absolute loss is bounded by
$$
 6x e^{-aL}\int_0^\infty e^{-v^2+(1+a)^2v}\,dv
 \le 6\sqrt\pi\, x\exp(-aL+(1+a)^4/4)\le6\sqrt\pi/x .
$$
Here $h>L$ is necessary for a prime crossing. Use $e^h\le e^{-aL}e^{(1+a)h}$ there, and $(1+a)^4/4\le4a^4$. When the smaller cutoff is $x^2$, the preceding bound 6 continues to hold. The corresponding mesh with $n=N$ uses $O(N\sqrt{\log x})$ widths and has elementary Gaussian interval weights. One can therefore use a genuine finite list of prime inputs bounded by $x^{1+o(1)}$ at each prescribed terminal point.

For an arithmetic check at $x=4$, among the primes through 16 only 11 has nonzero real character. The two Gaussian laws can be integrated explicitly on the three pieces of $K$. The variance interval $[0.49,0.50]$ contributes more than $3.36\cdot10^{-5}$ to the negative terminal quantity, and $[1.19,1.20]$ contributes more than $1.75\cdot10^{-6}$ to the positive quantity. The true unsmoothed real sample there vanishes. A second check at $x=2$, with variance $\log2$, bounds the full complex prime sample by summing through 4096 and bounding the omitted complex modulus by $5.395\cdot10^{-6}$. Run the verification program with uv at both embedded precisions. [Reproducible interval check](verify_adaptive_widths.py) · [Replay output](adaptive-width-receipts.txt)
