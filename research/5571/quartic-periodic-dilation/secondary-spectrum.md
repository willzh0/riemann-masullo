# What the full quartic dilation measures after the quartic poles cancel

Let $\chi$ be the primitive character modulo five with $\chi(2)=i$ and $\eta=\chi^2$. Write $Z(\psi)$ for the multiset of nontrivial zeros of $L(s,\psi)$ and $m_\psi(s)$ for its multiplicity at $s$ (zero away from the divisor). Take the genuine, untruncated prime dilation
$$
 B_\chi(x)=\sum_n \chi(n)n S_\chi(x/n)
          =\sum_{m\le x}\chi(m)(x-m)\log\operatorname{rad}(m).
$$
Mlyle established the second expression and the unconditional upper $B_\chi(x)\ll x^{3/2}\exp[-c\Phi(\log x)]$. The next spectral terms of this physical observable can be determined exactly. [Mlyle’s periodic convolution and upper bound](https://github.com/mlyle/riemann-masullo/blob/c2eb094fffef928fdb72c2e180c255092e819347/research/5571/fourth-power-prime-curvature/spectral-interpolation-periodic-prime-convolution.md)

The full dilation satisfies
$$
 B_\chi(x)=
 \sum_{\substack{z:\ 2z\in Z(\eta)\\\text{or }3z\in Z(\bar\chi)}}
 \frac{L(z,\chi)}{z(z+1)}
 \left(\frac{m_\eta(2z)}2+\frac{m_{\bar\chi}(3z)}3\right)
 x^{1+z}
 +O(x^{6/5}).
$$
The sum uses each distinct $z$ just once and its coefficients are absolutely summable. In the complex dilation the two multiplicities add. The scaled zero contributes if and only if $L(z,\chi)\ne0$.

Define $\alpha$ as the supremum of $\Re z$ over the nonzero coefficients. Then $\alpha\ge1/4$ and
$$
 B_\chi(x)=O(x^{1+\alpha}),\qquad
 \limsup_{j\to\infty}\frac{\log(1+|B_\chi(j^4)|)}{\log j}=4(1+\alpha).
$$
If the supremum is unattained, the upper bound is little-oh. If the quartic critical-line hypothesis holds, then $\alpha=\Theta_\eta/2$, where $\Theta_\eta=\sup_{\rho\in Z(\eta)}\Re\rho$. In that case $B_\chi(j^4)=O(j^5)$ if and only if the quadratic companion satisfies its own critical-line hypothesis.

Irrespective of either hypothesis, for **every fixed** real phase $\phi$ the actual fourth-power values satisfy
$$
 \limsup_{j\to\infty}\frac{\Re(e^{-i\phi}B_\chi(j^4))}{j^5}\ge0.0317,\qquad
 \liminf_{j\to\infty}\frac{\Re(e^{-i\phi}B_\chi(j^4))}{j^5}\le-0.0317 .
$$
A single verified quadratic zero gives the same constants for every fixed phase. These conclusions concern the full dilation. Mlyle’s bound $O_\epsilon(x^{1.48+\epsilon})$ for replacing it by his short sum exceeds $x^{5/4}$.

## Mellin calculation

On $\Re s>1$ put $P_\chi(s)=\sum_p\chi(p)\log p\,p^{-s}$. The Möbius identity over prime powers gives
$$
 P_\chi(s)=-\sum_{k\ge1}\mu(k)\frac{L'}{L}(ks,\chi^k).
$$
Indeed the contribution of $p^\ell$ in the sum with the negative logarithmic derivatives is $\chi(p)^\ell\log p\sum_{k\mid\ell}\mu(k)$. Thus the Mellin transform $\int_1^\infty B_\chi(x)x^{-s-2}\,dx$ has numerator
$$
 L(s,\chi)P_\chi(s)
 =-L'(s,\chi)+L(s,\chi)
 \left[\frac{L'}{L}(2s,\eta)+\frac{L'}{L}(3s,\bar\chi)+R(s)\right]
$$
and denominator $s(s+1)$. Here $\mu(4)=0$ and $R(s)$ is the sum of the $k\ge5$ terms. It converges absolutely, locally uniformly and boundedly on each $\Re s\ge1/5+\epsilon$, since the logarithmic derivatives have absolutely convergent prime-power expansions there. For any sufficiently small fixed $\epsilon>0$, shift the Perron integral for $L(s,\chi)R(s)$ to this line; fixed-conductor convexity bounds give an integrable vertical majorant after division by $s(s+1)$. Its contribution is $O_\epsilon(x^{6/5+\epsilon})$.

The $\epsilon$ in this last estimate can be removed on the arithmetic side. Expand the absolutely convergent tail first on $\Re s>1$. The inverse transform of its product with $L(s,\chi)$ equals a sum over $p^e\le x$, $e\ge5$, with a coefficient of modulus at most $\tau(e)\log p$. Each dilator sum has the factor $p^e\sum_{n\le x/p^e}\chi(n)(x/p^e-n)$, of modulus $O_\chi(x)$ by the bounded partial sums of $\chi$. Chebyshev gives $O_\chi(x^{6/5})$ for $e=5$. For $6\le e\le\log_2 x$ the total is $O_\chi(x^{7/6}(1+\log x)^2)$, which is also $O_\chi(x^{6/5})$. This proves the stated endpoint remainder.

The inverse transform of $-L'(s,\chi)$ is the first Riesz sum of $\chi(m)\log m$, which is $O(x\log(2x))$ by partial summation and periodicity. For each $k=2,3$ move the separate line for $L(s,\chi)(L'/L)(ks,\chi^k)$ to $\Re s=-1/10$. The functional equation on this line gives $L(s,\chi)\ll(2+|\Im s|)^{3/5}$ and $(L'/L)(ks,\chi^k)\ll\log(2+|\Im s|)$ off the finitely many low ordinates. The left integral is absolutely convergent. Good horizontal ordinates for each of the finitely many functions avoid ordinates of zeros by $\gg1/\log T$, using the fixed-conductor unit-slab zero count $O(\log(2+T))$. The local partial fraction expansion then bounds the logarithmic derivatives by $O(\log^2 T)$. Convexity, or the functional equation and Phragmén–Lindelöf, bounds $L(s,\chi)$ by $O_\epsilon(T^{3/5+\epsilon})$ on these horizontal segments. Consequently their integrals tend to zero. The origin contributes $O(x\log(2x))$, including the possible trivial zero of the even quadratic character. There are no other crossed trivial zeros. The nontrivial residues are exactly the displayed ones, with the factor $1/k$ from the chain rule. The coefficients are absolutely summable by $L(\rho/k,\chi)\ll_\epsilon(2+|\Im\rho|)^{1/2+\epsilon}$, the two inverse powers and the unit-slab count. [Classical Dirichlet $L$-function estimates, Davenport, Chapters 9 and 12–16](https://link.springer.com/book/10.1007/978-1-4757-5927-3)

## An actual pole visible in every phase

There is a zero of $L(s,\eta)$ at $1/2+i\gamma$ with
$$
 \gamma=6.6484533447277147161\ldots .
$$
Parametrize the completed function there by $(5/\pi)^{(1/2+it)/2}\Gamma((1/2+it)/2)L(1/2+it,\eta)$. This is real on the critical line by the functional equation and the quadratic root number one. The [interval verifier](verify_secondary_pole.py) bisects the opposite strict signs at $6$ and $7$ through 64 dyadic steps. It then evaluates the full enclosing ball at $z=1/4+i\gamma/2$, by both the finite Hurwitz-zeta representation and the Dirichlet routine. At both 128 and 192 bits it certifies
$$
 \begin{aligned}
 |L(z,\chi)|&=2.32004475726632947\ldots,\\
 |L(z,\bar\chi)|&=0.81799624152394296\ldots,\\
 L(3z,\chi)L(3z,\bar\chi)&\ne0,\qquad
 \frac{\big||L(z,\chi)|-|L(z,\bar\chi)|\big|}{4|z(z+1)|}>0.0317 .
 \end{aligned}
$$
Existence of a zero in this interval suffices. Let its multiplicity be $m\ge1$. For $F_\phi(x)=\Re(e^{-i\phi}B_\chi(x))$ the Mellin residue there is
$$
 r_\phi=\frac{m}{4z(z+1)}
 \left(e^{-i\phi}L(z,\chi)+e^{i\phi}L(z,\bar\chi)\right).
$$
Thus $|r_\phi|>0.0317$ for every fixed phase, by the reverse triangle inequality. The calculation certifies a pole of the actual arithmetic transform below the canceled quartic zero ordinates. It uses no infinite-height zero-location assumption. [FLINT Dirichlet and Hardy routines](https://flintlib.org/doc/acb_dirichlet/index.html)

On the real axis $L(s,\eta)>0$ for $s>0$. In each modulo-five block its series groups as the difference of the first and third consecutive drops of the strictly decreasing convex function $t^{-s}$. Similarly $\Re L(s,\chi)>0$ since each difference $(5n+1)^{-s}-(5n+4)^{-s}$ is positive. These convergent block sums agree with the $L$-functions for every real $s>0$. The continuation above therefore has no real pole for $s\ge1/4$ in either fixed real projection.

For clarity let $\sigma_0=1/4$. If $F_\phi(x)+A x^{1+\sigma_0}$ is eventually nonnegative, its Mellin transform on $\Re s>1$ equals that of $F_\phi$ plus $A/(s-\sigma_0)$ up to an entire correction from a bounded interval. Landau’s theorem for nonnegative Mellin transforms and real-axis regularity imply convergence on every real $\sigma>\sigma_0$. One elementary proof of the theorem expands at any real point to the right of the abscissa of convergence. Nonnegativity makes the derivatives with the signs removed positive moments of $\log x$; Taylor convergence across the real abscissa would, by monotone convergence, give convergence there to the left as well. At $\sigma=\sigma_0+v$, $v>0$, the transform of the nonnegative tail in modulus at $\sigma+i\gamma/2$ is at most its value at $\sigma$. Multiply by $v$ and let $v\downarrow0$. The two limits give $|r_\phi|\le A$. The same argument applied to $-F_\phi$ proves the two signed continuum bounds.

## Fourth-power sampling and the upper exponent

Off integer breakpoints $B_\chi'(x)$ is the full $\sum_{m\le x}\chi(m)\log m=O(\log(2x))$ minus
$$
 \sum_{k\ge2}\sum_{p^k\le x}\chi(p)^k\log p\,
                   A_\chi(x/p^k),\qquad A_\chi(u)=\sum_{n\le u}\chi(n).
$$
The step function $A_\chi$ is bounded. The terms $k\ge3$ total $O(x^{1/3}\log(2x))$ by Chebyshev. For $k=2$ put $y=\sqrt x$. The primes $p\le y/M$ cost $O(y/M)$ for any fixed $M>1$. On $[y/M,y]$ the factor $A_\chi(x/p^2)$ is constant on finitely many subintervals whose endpoints are fixed multiples of $y$, up to endpoint terms $O_M(\log y)$. Each $\eta$-twisted log-prime sum is $o_M(y)$ by the fixed-modulus prime number theorem. Letting $M\to\infty$ proves $B_\chi'(x)=o(\sqrt x)$ uniformly off the breakpoints. Since $B_\chi$ is continuous piecewise linear and $(j+1)^4-j^4=O(j^3)$, its oscillation within that cell is $o(j^5)$. This transfers the signed continuum bounds to the stated fourth-power samples.

The absolutely summable zero series gives $B_\chi(x)=O(x^{1+\alpha})$. When the supremum is unattained, the terms after normalization tend separately to zero, and dominated convergence gives the little-oh statement. To see sharpness for $\alpha>1/4$, suppose the discrete logarithmic upper exponent were smaller than $4(1+\alpha)$. The cell estimate gives a continuum bound $O(x^{1+b})$ for some $1/4<b<\alpha$. Its Mellin transform is holomorphic on $\Re s>b$, although a visible scaled zero gives an actual pole there. At $\alpha=1/4$ the certified signed lower already proves sharpness. Finally if $\chi$ satisfies its critical-line hypothesis, so does its conjugate, and no $z=\rho_\eta/2$ is a zero of $L(z,\chi)$, since $0<\Re z<1/2$. The cubic channel is at real part $1/6$. This proves the claimed companion criterion.
