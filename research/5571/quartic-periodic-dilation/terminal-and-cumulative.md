# A terminal obstruction for the genuine quartic dilation and a cumulative recovery bound

Fix the quartic character $\chi\pmod5$ with $\chi(2)=i$, put $\eta=\chi^2$, and use mlyle’s smooth $W$ and $N=x^{21/100}$. For a function vanishing below 1 define

$$

 (\mathcal D_\psi S)(x)=\sum_{n\ge1}\psi(n)nS(x/n),\qquad
 (\mathcal D_{\psi,N}S)(x)=\sum_{n\ge1}W(n/N)\psi(n)nS(x/n).

$$

Mlyle’s actual quartic dilations are $O(x^{3/2}e^{-c\Phi(\log x)})$, with full/truncated difference $O_\epsilon(x^{1.48+\epsilon})$. The quadratic dilation has the displayed square drift in that note. [Definitions and measured bounds](https://github.com/mlyle/riemann-masullo/blob/c2eb094fffef928fdb72c2e180c255092e819347/research/5571/fourth-power-prime-curvature/spectral-interpolation-periodic-prime-convolution.md)

**Terminal statement.** Given an initial cutoff, there is a fixed subset $\mathcal P_*$ of the genuine primes containing every initial prime and having relative density one. Put $S_\psi^*(x)=\sum_{p\in\mathcal P_*}\psi(p)\log p\,(x-p)_+$. All four progression masses are positive measures, with the genuine signs, primes and log weights. They obey the signed short-interval estimates below and the one-progression curvature estimate in [PR #7653](https://github.com/mccorvie/riemann-masullo/pull/7653). Nevertheless infinitely many integers $j$ satisfy

$$

 -\Re S_\chi^*(j^4)\gg (j^4)^{84/55}.

$$

Both $\mathcal D_\chi S_\chi^*$ and $\mathcal D_{\chi,N}S_\chi^*$ are $O(x^{37/25})$. For $\eta$ both dilations equal $-\frac23L(1/2,\eta)x^{3/2}+O(x^{37/25})$. This also gives the measured centered component variance and the power-saving full/truncated difference. The modified model omits primes of relative density zero. Its exact full identity uses the log radical restricted to retained primes, since the unmodified identity for every $m$ determines the original prime coefficients by Dirichlet inversion.

**Cumulative statement.** Suppose only that the genuine $L(s,\chi)$ has no zero in $\Re s>b$, where $1/2\le b<1$. For any complex prime coefficients $|a_p|\le\log p$, take $S(x)=\sum_pa_p(x-p)_+$. If $\mathcal D_\chi S(x)=O(x^{1+b})$, then

$$

        \sum_{j\le J}|S(j^4)|\ll_{\epsilon,S,\chi} J^{5+4b+\epsilon}
          \qquad(\epsilon>0).

$$

Thus a physical model satisfying the full quartic size bound and violating the *cumulative* exponent by a fixed power would itself imply a genuine exterior zero. The terminal statement gives no such cumulative claim.

## A forcing function focused at a terminal fourth power

Choose a large fourth power $X=J^4$, put $M=\lfloor X^{1/11}\rfloor$, $Y=X/(2M)$, $w=X/(20M^2)$, and $a=37/25$. Then $M\asymp Y^{1/10}$. Fix $\phi\in C_c^\infty((-1,1))$ with $\phi(0)=1$. Set

$$

 B_X(y)=Y^a\sum_{M\le m\le2M}\overline{\mu(m)\chi(m)}
                       \phi((y-X/m)/w),\qquad
 F_X(t)=\sum_m\mu(m)\chi(m)m B_X(t/m).

$$

Consecutive centers differ by more than $2w$, including the adjacent unused centers. The forcing is supported in $[Y/2,3Y]$, and has $|B_X^{(r)}|\ll_rY^{a-r}M^r$. All dilation sums are locally finite, so Möbius inversion gives $\mathcal D_\chi F_X=B_X$ exactly. At $X$ only the prescribed centers contribute and

$$

       F_X(X)=Y^a\sum_{M\le m\le2M}m\mu^2(m)|\chi(m)|^2
              \gg Y^a M^2\asymp X^{84/55}.

$$

The squarefree integers prime to 5 have positive natural density, as follows by expanding $\mu^2(n)=\sum_{d^2\mid n}\mu(d)$. No spectral zero enters this construction.

Take an infinite sequence of packets with $Y_{i+1}>10X_i$; the first starts beyond the given cutoff. Choose each packet’s sign so that the absolute real part at its terminal $X_i$, including earlier packets, is at least $F_{X_i}(X_i)$. Later packets vanish there. One global sign then produces infinitely many negative terminals of this order. Write $F$ for the signed sum. Its full dilation is the signed sum of disjoint forcings, hence $O(x^{37/25})$.

To bound its truncated dilation, differentiating on the band $m\asymp t/Y$ gives, for $t\ge Y/2$,

$$

      |(t\partial_t)^k F_X(t)|\ll_k t^2Y^{a-2}M^k.

$$

The same holds with any ordinary $t^r\partial_t^r,\ r\le k$. Integrate the smooth tail test $v(1-W(v/N))F_X(x/v)$ against a bounded, order-$k$ periodic primitive of the mean-zero lattice distribution $\sum\chi(n)\delta_n$. Its $k$-th derivative has $L^1$ norm $O_k(x^2Y^{a-2}(M/N)^k)$, by differentiating $v^{-1}$-scale factors and integrating $v^{-1-k}$ above $N$. Cutoff derivatives satisfy the same bound on $[N,2N]$. For active packets $M\ll x^{1/10}$, so $k=6$ gives $O(x^{1.34}Y^{a-2})$. As $a<2$, the sum of those packet factors converges. Consequently $\mathcal D_{\chi,N}F-\mathcal D_\chi F=O(x^{1.34})$.

The signed curvature has $|F''(t)|\ll e^{-c\sqrt{\log(2+t)}}$. For a packet the direct bound is $O(Y^{a-2}M^2)\ll Y^{-0.32}$. For $Y\le\sqrt t$, use $F_X''(t)=\sum_m\mu(m)\chi(m)m^{-1} B_X''(t/m)$ and integrate by parts against $\sum_{m\le v}\mu(m)\chi(m)\ll v e^{-c\sqrt{\log(2v)}}$. Its interval in $m$ has scale $t/Y$, and one derivative of the amplitude costs one extra $M$. The result is $O(Y^{-0.22}e^{-c'\sqrt{\log(2+t)}})$. Summing the older packets and then summing $Y^{-0.32}$ for the lacunary $Y>\sqrt t$ proves the claim. The fixed-modulus Möbius estimate follows from Perron for $1/L(s,\chi)$ with $T=\exp(c_1\sqrt{\log v})$ and the classical zero-free strip $1-c_2/\log(2+T)$. On a narrower strip $1/L\ll\log^C(2+T)$ by the standard log-$L$ estimate. The quartic has no exceptional real character term. [Classical fixed-conductor zero-free strip](https://arxiv.org/pdf/2210.06457#page=3)

**Parameter range.** The same construction approaches terminal exponent $8/5$ while preserving all measured bounds. Fix $a<3/2$ arbitrarily close to $3/2$ and $0<\kappa<1/4$ arbitrarily close to $1/4$. Take $M=\lfloor X^{\kappa/(1+\kappa)}\rfloor$, so $M\asymp Y^\kappa$. The terminal exponent is $(a+2\kappa)/(1+\kappa)$. The tail in the short dilation vanishes unless $x/N\ge Y/2$; on its support $M/N\ll x^{(79\kappa-21)/100}$, a fixed power saving even at $\kappa=1/4$. Choosing enough integrations makes the full/truncated difference $O(x^{1.48})$. The full forcing $O(x^a)$ meets the quartic stretched-log envelope. For curvature split at $Y=\exp(c_0\sqrt{\log t})$. Later packets contribute a geometrically summable $O(Y^{a-2+2\kappa})$ with a strictly negative exponent. Each earlier packet costs $O(Y^{\max(0,a-2+3\kappa)}e^{-c\sqrt{\log t}})$ by the same Möbius estimate; taking $c_0>0$ small absorbs the extra power and the $O(\log t)$ packet count. This retains the stated local rate. Thus for every fixed $\nu<8/5$ there is a profile with infinitely many negative terminal values $\gg X^\nu$. If both quartic convolutions are required to be $O(x^{37/25})$, keep $a=37/25$ and allow $\kappa<13/50$; then $79\kappa<21$, $a-2+2\kappa<0$, and every $\nu<100/63$ is attainable. These statements give a profile for each exponent.

## Realizing the profile by thinning actual primes

Choose $D(t)$ smooth, zero at small $t$, and equal to $-2t^{3/2}/3$ for large $t$. Then $D''(t)=O(t^{-1/2})$ at infinity. For each of the four residue labels use the real correction

$$

       v_r(t)=\tfrac12\Re(\overline{\chi(r)}F''(t))+
                         \tfrac14\eta(r)D''(t).

$$

Finite character orthogonality gives $\sum_r\chi(r)v_r=F''$, $\sum_r\eta(r)v_r=D''$, and $\sum_r v_r=0$. For large $t$ the corrections are uniformly small. An arbitrary scalar density, the same in each class, leaves both signed projections fixed.

Use consecutive blocks $I=[z,z+L)$ with $L=z^\theta,\ \theta=16/25$, starting sufficiently far out. Write $u=(t-z)/L$. The fixed-modulus short-interval PNT gives

$$

 L^{-1}\!\!\sum_{\substack{p\in I\\p\equiv r(5)}}(\log p)\,u(p)^k
      =\frac1{4(k+1)}+o(1),\qquad 0\le k\le2.

$$

For example take a fixed Riemann partition and use the PNT on its constituent intervals, then refine. Every fixed subsample length here exceeds $z^{7/12+\delta}$ for some $\delta>0$. This estimate is uniform over the four labels. [Thorner–Zaman, Theorem 1.1 and Remark 1.2](https://arxiv.org/pdf/2108.10878#page=1)

On each block choose a common reserve $\delta_I\downarrow0$ in the sense $\delta_I\to0$, dominating the displayed moment errors and $\max_r\|v_r\|_{\infty,I}$ by an arbitrarily large fixed factor. One can take the square root of the sum of their absolute sizes plus $1/\log z$. Target the densities $(1-\delta_I)/4+v_r(t)$. They are nonnegative for large $z$. Starting with fractional prime weights $1-\delta_I$ times $\log p$, correct the multiplier on each residue by an affine function $\alpha+\beta u(p)$ to match the target total mass and its first moment in $u$ exactly. The normalized linear system has Gram matrix converging to $\frac14\left(\begin{smallmatrix}1&1/2\\1/2&1/3\end{smallmatrix}\right)$ and right-hand side $o(\delta_I)$ by the choice of reserve. Thus after increasing the starting cutoff every fraction lies in $[0,1]$ and equals $1+o(1)$, uniformly on each block.

Replace those fractions $v_p$ by 0 or 1 in each true residue class. With fractional mass owed $b$, retain the next prime $p$ if $b+v_p\log p\ge\log p$, subtract its $\log p$ if retained, and carry the result forward. The discrepancy remains in $[0,\log p)$ by monotonicity of $\log p$. This gives a fixed set $\mathcal P_*$, and an initial interval of primes may all be retained. Fractional deleted log mass is $o(x)$ since $v_p\to1$; rounding changes it by $O(\log x)$ per residue, so the set of deleted primes has relative natural density zero by partial summation.

For either nontrivial projection the continuous target first Riesz profile is $F$, $\overline F$, or $D$, up to an affine term from the finite start. Each completed block has exact zeroth and first moments before rounding. Only the block containing $x$ can contribute a matching error. Its mass is $O(x^\theta)$, and its ramp length is $O(x^\theta)$. The rounding contributes $O(\log x)$ to the derivative and $O(x\log x)$ to its integral. Thus the discrete target error satisfies

$$

             |E(x)|\ll x^{2\theta},\qquad |E'(x)|\ll x^\theta

$$

for $x\ge2$, the derivative almost everywhere. Initial terms of size $O(x)$ and $O(1)$ are absorbed. In particular over $x<t\le x+h,\ h\le x/2$, the modified quartic prime sum has modulus

$$

       \ll h e^{-c\sqrt{\log x}}+x^\theta .

$$

The quadratic gains an additional $O(hx^{-1/2})$. For every fixed interval exponent above $2/3$, this supplies the signed stretched-log local bound used in the preceding reports. Inclusion in the genuine primes with unchanged retained weights preserves the one-sided progression curvature inequality exactly.

The short dilation of the error costs $O(x^{2\theta}N^{2-2\theta})=O(x^{1.4312})$. To bound the full dilation use absolute summation up to $K=x^{(1-\theta)/(2-\theta)}$. Above $K$, Abel summation against the bounded partial sums of the true nonprincipal $\psi$ uses
$(vE(x/v))'=E(x/v)-(x/v)E'(x/v)$. Its endpoint and integrated variation are $O(x(x/K)^\theta+x)$, since $2\theta\le1+\theta$. The full bound is consequently $O(x^{2/(2-\theta)})=O(x^{25/17})$, below $x^{37/25}$. The terminal perturbation $O(X^{2\theta})$ is negligible compared with $X^{84/55}$.

Finally, the full dilation of $D$ equals $-2L(1/2,\eta)x^{3/2}/3+O(x)$. For $n\le x/C$ the main expression is exact and the ordinary character tail is $O((x/C)^{-1/2})$. The remaining transition $n\asymp x$ costs $O(x)$ by one Abel summation. The smooth truncated multiplier equals $L(1/2,\eta)+O_{k,W}(N^{1/2-k})$ by repeated integration against the same periodic primitives; for large $x$ its support $n\le2N$ does not reach the small-$t$ transition. This gives the claimed quadratic drift and all stated errors.

## Why cumulative excess would force a genuine zero

For $\sigma>b$ put

$$

     \widehat B(s)=\int_1^\infty \mathcal D_\chi S(x)\,x^{-s-2}\,dx .

$$

This converges absolutely and is holomorphic there. For $\Re s>1$, direct substitution gives $\widehat B(s)=L(s,\chi)\widehat S(s)$ with the same Mellin convention. Writing $B=\mathcal D_\chi S$, its prime convolution coefficients satisfy

$$

       |b_m|=\Big|\sum_{p\mid m}\chi(m/p)a_p\Big|
                 \le\sum_{p\mid m}\log p\le\log m .

$$

Thus $B$ is absolutely continuous and $|B'(x)|\ll x\log(2x)$ off the integer breakpoints.

It suffices to choose $b<\sigma<1$. Set $d=\sigma-b>0$ and extend $f(y)=e^{-(1+\sigma)y}B(e^y)$ by zero on $y<0$. Then $|f(y)|\ll e^{-dy}$, and $|f'(y)|\ll(1+y)e^{(1-\sigma)y}$ for $y\ge0$. These imply some strictly positive fractional $L^2$ regularity, with an elementary proof. For $0<h<1/2$ split at $T=\frac12\log(1/h)$. The derivative estimate on $y<T$ and the size bound on $y\ge T$ give

$$

 \|f(\cdot+h)-f\|_2^2
 \ll h^{2-(1-\sigma)}(1+|\log h|)^3+h^{d}.

$$

The negative endpoint is harmless since $B=0$ near $x=1$. Multiply by $h^{-1-2a}$ and integrate over $0<h<1$ for $0<a<\min(d,1)/2$. Plancherel, together with the substitution $v=h|t|$ in $\int_0^1|e^{iht}-1|^2h^{-1-2a}dh$, gives

$$

       \int_{\mathbb R}(1+|t|)^{2a}|\widehat B(\sigma+it)|^2dt<\infty .

$$

The zero-free hypothesis gives $|1/L(v+it,\chi)|\ll_{\epsilon,\sigma}(2+|t|)^\epsilon$ uniformly on $\sigma\le v\le 2$. To see this, choose $b<v_0<\sigma$. The analytic logarithm, normalized at 2, is $O_{v_0}(\log(2+|t|))$ on $v=v_0$ by Borel–Carathéodory in slightly larger zero-free discs centered at $2+it$, using the polynomial vertical bound for $L$. On $v=2$ it is bounded by absolute Euler-product convergence. Apply three-lines to $\log L(s,\chi)\exp((s-it)^2)$; on $v\ge\sigma$ this improves $\log(2+|t|)$ to a fixed power strictly less than one. Exponentiating proves the assertion.

It follows that $\widehat B/L$ on $\Re s=\sigma$ belongs to $L^2(dt)$. This is the Fourier transform of $e^{-(1+\sigma)y}S(e^y)$ in distributions. For clarity, start with Fourier inversion in duality with a smooth, compactly supported test in $y$ on the absolute line $\Re s=2$. Move the contour to $\sigma$ for $\widehat B/L$, including the exponential reweighting in the test transform. The test transform decays faster than any power vertically uniformly on this bounded strip, $\widehat B$ is uniformly bounded there, and $1/L$ satisfies the preceding bound. This proves the identity and hence the weighted $L^2$ estimate by Plancherel.

At each $x=j^4,\ J/2\le j\le J$, average on the symmetric interval of radius $h=cJ^3$ for a small fixed $c>0$ so the intervals have bounded overlap and lie within a constant factor of $J^4$. The affine tangent cancels. The remaining ramps change the average by $O(h(h+1)\log(2J))$, since there are at most $2h+1$ integers in the interval and $|a_p|\le\log p$. By Cauchy on the logarithmic variable, the weighted $L^2$ bound gives $\int_{c'J^4}^{C'J^4}|S(t)|dt\ll_\sigma (J^4)^{2+\sigma}$. Therefore

$$

       \sum_{J/2\le j\le J}|S(j^4)|
          \ll_\sigma J^{5+4\sigma}+J^7\log(2J).

$$

Summing dyadic shells and taking $\sigma\downarrow b$ proves the cumulative result. This argument uses a genuine zero-free premise, irrespective of how the physical prime weights are chosen.


## Sharp conditional upper exponent for an individual terminal sample

The same $L^2$ conclusion gives an upper bound at every sufficiently large real $X$. For $1\le h\le X/2$, a symmetric average cancels the affine part of every prime ramp outside $[X-h,X+h]$. The remaining ramps contribute $O(h(h+1)\log(2X))$ in total. Cauchy–Schwarz and the weighted $L^2$ estimate above give

$$

 |S(X)|\ll_{\sigma,S,\chi} h^{-1/2}X^{3/2+\sigma}+h^2\log(2X).

$$

Indeed the logarithmic weight translates to $t^{-3-2\sigma}\,dt$ on the physical axis, and $t\asymp X$ throughout this average. Taking $h=X^{(3+2\sigma)/5}$ and then $\sigma\downarrow b$ gives

$$

 |S(X)|\ll_{\epsilon,S,\chi}X^{(6+4b)/5+\epsilon}.

$$

In particular, conditional on the critical-line hypothesis for this one quartic $L$-function, the exponent $8/5$ is sharp for this class of retained-prime weights subject to the measured full dilation. Every exponent below $8/5$ occurs as a one-sided lower along infinitely many fourth powers for a suitable fixed profile constructed above. The original cumulative deficit uses the unthinned prime set.
