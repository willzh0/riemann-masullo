# Recovering the horizontal reach from locally finite signed samples

Use the notation of the [tower theorem](README.md). Fix a stage and write $W$ for the set of centered sites in its closed exterior with positive multiplicity. If $W$ is empty, all sums vanish. Otherwise put $\sigma=\sup_{w\in W}\Re w$. The functional equation and conjugation reflect $\rho$ to $1-\bar\rho$ with its full order. In particular $\sigma=\sup_{w\in W}|\Re w|\ge a_n>0$, including when this supremum is approached at unbounded ordinates. [Hecke reflection in the project](https://github.com/mccorvie/riemann-masullo/blob/8ee044ded1adfcda4af6f2962dc68d8e1c56b9e8/RiemannMasullo/Ch01_Introduction/Sec4_HeckePoisson.lean#L129)

## The fixed radial function and its derivative bound

Let $g$ be the infinite convolution of uniform probabilities on $[-r_j,r_j]$, $r_j=1/(j(j+1))$. Its smooth probability density has support in $[-1,1]$. With $G(w)=\prod_{j\ge1}\sinh(r_jw)/(r_jw)$, take $h(x)=g'''(x-3)-g'(x-3)/4$. Its bilateral Mellin transform is
$$
 M(w)=-e^{3w}w(w^2-1/4)G(w).
$$
Each factor of $G$ is nonzero for $\Re w\ne0$, and the locally uniform product has no further zeros there since $\sum r_j^2<\infty$. This is a real admissible profile supported in $[2,4]$. [Quadratic box profile in Lean](https://github.com/willzh0/riemann-masullo/blob/cf9f1a91b91ec900f93cb152daa3412bf466f59c/RiemannMasullo/ForMathlib/Analysis/Fourier/QuadraticBoxLaplace.lean) · [Translated profile](https://github.com/mccorvie/riemann-masullo/pull/7571)

Uniformly on $|\Re w|\le1/2$, the $j$th factor is bounded by $e^{r_j/2}\min(1,1/(r_j|w|))$. This follows from the integral over the interval and the elementary modulus bound on the hyperbolic sine. For $|w|\ge4$ and $j\le\sqrt{|w|}/2$ one has $r_j|w|\ge2$. Consequently $|G(w)|\le 2e^{1/2}\exp(-(\log2)\sqrt{|w|}/2)$ there. For an appropriate fixed $c>0$ absorb the polynomial multiplier into the exponential to obtain $|M(w)|\le C e^{-c\sqrt{|w|}}$ throughout the centered closed strip.

Write $a_w=b_n(w)M(w)$ and $S(t)=\sum_{w\in W}a_we^{tw}$. Every $a_w$ is nonzero since $b_n(w)$ is a positive integer at such a site. The fixed finite collection of Hecke functions has $O_n((T+2)\log(T+2))$ zeros counted with multiplicity up to height $T$. Hence there are constants $C_n,D>0$ with
$$
 |S^{(j)}(t)| \le C_n e^{\sigma t}D^j(j!)^2,\qquad t\ge0,\quad j\ge0.
$$
Indeed $\sum b_n(w)e^{-c\sqrt{|w|}/2}<\infty$, and for $j>0$ the supremum of $x^j e^{-c\sqrt{x}/2}$ on the positive real axis is $(4j/(ce))^{2j}\le(16/c^2)^j(j!)^2$. Normal convergence on compact real intervals justifies differentiation.

## Signed growth on the half-line

The triangle inequality gives $\limsup_{t\to\infty}t^{-1}\log(1+|S(t)|)\le\sigma$. If the inequality were strict, choose $\beta$ strictly between the two sides. The Laplace transform of $S$ would then be holomorphic for $\Re z>\beta$. For $\Re z>1/2$, absolute convergence and integration of each exponential identify it with
$$
 P(z)=\sum_{w\in W}\frac{a_w}{z-w}.
$$
The union of the finitely many zero divisors is locally finite in the whole complex plane. Absolute summability of the coefficients gives normal convergence off that set and a simple pole of residue $a_w$ at each $w\in W$. By the identity theorem and the definition of the supremum there is an incompatible pole in $\Re z>\beta$. This proves exact equality of the growth rate with $\sigma$. It also covers rightmost real parts that have no maximizing zero. The residue at a collision is the common nonzero Mellin sample times the positive sum of all contributing orders. [Earlier single-character rational translation criterion](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7128949260) · [Weighted translated defects](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7148602651)

## Quadratic sampling

For integer $k\ge2$, the rational grid $\mathcal Q_k$ has mesh $h_k=k^{-2}$ on $[k-1,k+2]$. For $t\in[k,k+1]$ choose a closest grid point $x$ and interpolate on the $2m+1$ points $x+jh_k$, $|j|\le m$. Choose $m=\lfloor\epsilon k\rfloor$ with a sufficiently small fixed $\epsilon>0$. For large $k$ all points lie in $\mathcal Q_k$. In grid coordinates $y=(t-x)/h_k$ satisfies $|y|\le1/2$.

At $y=0$ the central interpolation weight is one and all others vanish. Otherwise the absolute Lagrange weight for index $j$ is
$$
 \frac{|y|\prod_{\ell=1}^m(\ell^2-y^2)}
 {|y-j|(m+j)!(m-j)!}.
$$
Since $(m!)^2\le(m+j)!(m-j)!$, the central weight is at most one and the others are at most $1/(2|j|-1)$. The sum of the absolute weights is $O(\log(m+2))$ even as the degree grows.

For $p=2m+1$, the absolute node product in the interpolation remainder is at most $h_k^p(m!)^2\le h_k^p p!$. Apply the ordinary real interpolation remainder to the real and imaginary parts on the interval spanned by the nodes. The resulting error has the bound
$$
 2 C_n e^{\sigma(t+1)}(D p^2/k^2)^p .
$$
Choose $\epsilon$ so that $D p^2/k^2\le1/2$ for large $k$. Then the error is $O_n(e^{(\sigma-\delta)t})$ for a fixed $\delta>0$. If the limsup from the samples had value $\beta<\sigma$, choose $\beta'$ with $\beta<\beta'<\sigma$. The interpolant is $O_n(\log(k+2)e^{\beta'(t+1)})$, since all its nodes lie within one of $t$. The interpolant and error together would give a continuous growth exponent strictly below $\sigma$, contradicting the half-line result.

This proves exact recovery on the locally finite grid. Each test parameter is rational, and the number of samples in a bounded interval is finite. The argument gives the same grid for all fields, characters, positive widths and finite packets. It establishes an asymptotic identity. A finite sampling run does not decide the value of a growth exponent. The [exact verifier](verify.py) checks the central interpolation bounds at rational points, separately from the proof for all real arguments.