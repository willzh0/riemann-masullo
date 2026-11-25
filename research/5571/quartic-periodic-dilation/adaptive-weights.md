# Centered periodic weights chosen anew at each terminal prefix

Fix the genuine quartic character $\chi\bmod 5$, $\chi(2)=i$, on the primes. Let $W$ and $G_b$ be the short physical dilation at scale $x^{21/100}$ from the four-zero theorem. To use one representative of each centered weight modulo the matched row, take the real vector space

$$

 V=\left\{b\in\mathbb C^5:\ \sum_{r=1}^5b(r)=0,\quad b(1)=0\right\}

$$

with its Euclidean norm. It has real dimension six. A complex output phase can be absorbed in $b$. There are constants $c>0,\ 0<\lambda<1$ such that for every sufficiently large integer $J$, simultaneously for every $b\in V$, $\|b\|=1$, and for either sign,

$$

 \sum_{\lambda J<j\le J} [\pm\Re G_b(j^4)]_+ \ \ge\ cJ^7 .

$$

The same $b$ applies to all samples in that shell. It can depend on the terminal $J$. If $b_J+t_J\chi$ is used, any bounded sequence $t_J$ preserves the estimate with a possibly smaller constant, by mlyle’s pointwise bound for the matched row. [Definition, four-zero certificate and sample interpolation](RIGIDITY.md) · [Mlyle’s original periodic dilation](https://github.com/mlyle/riemann-masullo/blob/c2eb094fffef928fdb72c2e180c255092e819347/research/5571/fourth-power-prime-curvature/spectral-interpolation-periodic-prime-convolution.md)

There is also an exact exponent. Put $A_b(\rho)=m_\chi(\rho)M_b(\rho)$, where $M_b(s)=5^{-s}\sum_r b(r)\zeta(s,r/5)$ and multiplicity is zero at a regular point. For a point of the quartic zero divisor or its reflected divisor put

$$

 c_\rho(b)=-\frac{A_b(\rho)+\overline{A_b(\bar\rho)}}{2\rho(1+\rho)},\quad
 \vartheta(b)=\max\left\{\tfrac12,\sup_{c_\rho(b)\ne0}\Re\rho\right\},
 \quad \vartheta_*=\min_{\substack{b\in V\\\|b\|=1}}\vartheta(b).

$$

On the canonical unit sphere the smaller signed prefix across all centered choices satisfies

$$

 \lim_{J\to\infty}\frac{\log\bigl(1+\min_{\|b\|=1,\ b\in V}
       \sum_{j\le J}[\Re G_b(j^4)]_+\bigr)}{\log J}
 =5+4\vartheta_* .

$$

The minimum on the left is continuous optimization at each finite $J$. In particular, a critical-exponent upper along any unbounded sequence, with adaptive normalized centered residues, holds if and only if a **single** normalized $b\in V$ annihilates every exterior projected coefficient. In that case both the optimal prefix and the optimal terminal shell above have order $J^7$. Determining whether that exterior kernel is nontrivial requires information about the actual quartic divisor.

## Uniform expansion on a finite-dimensional family

Since each $b$ has zero period mean, its partial sums are bounded. The physical explicit formula in the crossed-row proof applies with its periodic $\bar\chi(n)$ replaced by $b(n)$. In the two partial summations only the bounded periodic primitives enter. The dilator series in the zero coefficient is then $M_b(s)$. Its fixed-conductor convexity bound follows by writing $b$ on the four reduced classes as a combination of the characters modulo five and treating $b(5)\sum_{5\mid n}n^{-s}$ separately. The coefficient of $\zeta(s)$ in this decomposition has its pole at one canceled by the zero-mean condition. The estimates for proper prime powers still use $\chi^2$ and its fixed-modulus prime number theorem. Mlyle’s short-cutoff comparison likewise uses bounded periodic primitives in $n$ and the separate fixed prime character in the reciprocal-prime estimate. Consequently, with $y=\log x$,

$$

 f_b(y):=e^{-3y/2}\Re G_b(e^y)=
 \sum_\rho c_\rho(b)e^{(\rho-1/2)y}+o(1).

$$

The union of zero divisors here is a set of distinct points. The coefficient functionals are real-linear, and $\sum_\rho\|c_\rho\|<\infty$. Both the summability and the $o(1)$ are uniform on $\|b\|\le1$, by taking any fixed real basis. There is no zero of positive real argument. At the four certified unpaired critical zeros, the maximum coefficient modulus is at least $10653\|b\|/20000000$. [Crossed physical expansion and its estimates](CROSSED.md) · [Four-zero verification](RIGIDITY.md)

Let $K$ be the intersection of the real kernels of $c_\rho$ over all $\Re\rho>1/2$, and decompose $b=u+v$ orthogonally with $u\in K,\ v\in K^\perp$. For $u\in K$, $f_u(y)=A_u(y)+o(1)$, where $A_u$ is the uniformly convergent critical trigonometric series with coefficients $c_\rho(u)$. It is real, bounded and almost periodic, with mean zero. The interior sum tends to zero by dominated convergence, uniformly on the unit ball. For nonzero $u$ a certified critical coefficient survives.

## One shell for the entire sphere

If $K^\perp\ne0$, choose finitely many exterior points $\rho_1,\ldots,\rho_l$ and $c_1>0$ such that $\max_i |c_{\rho_i}(v)|\ge c_1\|v\|$ on $K^\perp$. A finite subfamily of the real and imaginary linear functionals spans the annihilator of $K$, and compactness gives the inequality. Write $\beta_*=\min_i\Re\rho_i>1/2$. Choose $1/2<\sigma<1/2+t<\beta_*$.

At this fixed $\sigma$ the sum of the reciprocal positive ordinates over the exterior pairs with $\Re\rho>\sigma$ is finite by the fixed-conductor zero-density theorem. Use mlyle’s compact positive probability measure annihilating all these pairs: the factor for $w=\rho-1/2=b_0+i\gamma,\ \gamma>0$, has atoms at 0 and $d=\pi/\gamma$ with mass ratio $e^{b_0d}:1$. The sum of these $d$ is finite. Each factor has nonzero transform everywhere on the imaginary axis because its atom masses differ, and the infinite product remains nonzero there since the deviations from 1 are at most $|\operatorname{Im}w|d$ on that axis. Convolve with a sufficiently narrow nonnegative smooth probability so its transform stays nonzero at the **four specified** critical frequencies. Denote the resulting density by $P_0$. A further convolution with a long uniform interval gives a bounded probability density $P$, constant positive on the support of $P_0$ after translating the interval if necessary. For each selected $w_i$, divide the transform of $P_0$ by its full zero factor at $w_i$ using successive compact tail primitives. The resulting bounded complex density $L_i$ has transform nonzero at $w_i$, still vanishes at the other selected exterior points, and satisfies $|L_i|\ll_i P$. Both $P$ and the $L_i$ have fixed compact support. [Positive compact annihilator and division](https://github.com/mlyle/riemann-masullo/blob/69f6639d0e53c2a04aa3b5f8487a1be237274b97/research/5571/square-prefix-fixed-window-count/README.md) · [Fixed-conductor density estimate](https://doi.org/10.1007/BF01404638)

If $\|v\|\ge e^{-ty}$, choose an $i$ attaining the finite evaluation bound. Testing $f_b(y+\cdot)$ against $L_i$ gives a term of absolute size $\gg\|v\|e^{(\beta_*-1/2)y}$ with error $O(1+\|v\|e^{(\sigma-1/2)y})$. The constant bounds the entire $u$ contribution. Testing against $P$ gives only that error. Since $|L_i|\ll P$, the identity $2[h]_\pm=|h|\pm h$ gives a growing lower bound for the integrals of both signs against $P$. In particular their unweighted integrals exceed a fixed positive constant on one bounded window.

If $\|v\|<e^{-ty}$, the integral against $P_0$ of $f_v(y+\cdot)$ tends uniformly to zero since the remaining terms are $O(\|v\|e^{(\sigma-1/2)y})+o(1)$. The filtered $A_u$ retains a certified nonzero frequency. For each $u$ on the unit sphere of $K$, this real, mean-zero almost-periodic function has positive and negative fixed margins on relatively dense translates. Otherwise recurrence of a nonzero signed interval would contradict the zero mean. The series depends continuously on $u$ in the uniform norm. Finitely many neighborhoods cover the sphere, giving common margins and one interval length for both signs. Here $\|u\|\to1$, so the same bounds apply at some centers a bounded distance from $y$. Positivity and boundedness of $P_0$ give both unweighted one-sided lower integrals. When $K=V$, this compact almost-periodic argument applies directly. When $K=0$, only the first case occurs for large $y$.

Translate the resulting fixed log window inside $4\log(\lambda J)<y<4\log J$, with room on both sides for adjacent fourth powers. On each cell the short-row interpolation error is $o(j^6)$ uniformly over $\|b\|=1$, by the four-zero theorem’s signed short-interval estimate. The positive part is convex and the cell has log-length $O(1/J)$. Thus each of the two integral lower bounds yields the asserted discrete terminal-shell lower bound. [Physical short-row interpolation](RIGIDITY.md)

## The minimum exponent

The function $\vartheta$ is lower semicontinuous on the sphere since $\{\vartheta>d\}$, for $d\ge1/2$, is a union of open conditions $c_\rho(b)\ne0$. It attains its minimum. For a minimizing fixed $b$, summability in the expansion gives the upper $O(J^{5+4\vartheta_*})$. When $\vartheta_*>1/2$, fix $1/2<\beta<\vartheta_*$. The evaluation kernels for $\Re\rho>\beta$ have trivial intersection. Extract a finite family with $\max_i|c_{\rho_i}(b)|\gg_\beta1$ uniformly on the whole sphere and $\Re\rho_i>\beta$. The preceding selected integrals now give the lower $\gg_\beta J^{5+4\beta}$, since the full vector is detected with a constant margin. The same shell can be fixed for $\beta$ near $\vartheta_*$, using one positive mask at any fixed $\sigma\in(1/2,\vartheta_*)$ below those $\beta$. Letting $\beta\uparrow\vartheta_*$ proves the limit. When $\vartheta_*=1/2$, the unit-sphere shell theorem supplies the lower bound at order $J^7$, and the minimizing row lies in $K$.
