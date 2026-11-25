# Four certified zeros determine the only period-five short dilation with a vanishing real projection

Let $\chi$ be the primitive quartic character modulo 5 with $\chi(2)=i$. Fix $\kappa=21/100$ and a real smooth $W$, one on $[0,1]$, zero on $[2,\infty)$, with $0\le W\le1$. For an arbitrary complex five-periodic vector $a=(a_1,\ldots,a_5)$, including nonzero mean, set

$$G_a(x)=\sum_{n\ge1} W(n/x^\kappa)a(n)n
  \sum_p\chi(p)\log p\,(x/n-p)_+,\qquad
 v=(a_r-a_1\chi(r))_{r=2}^5.$$

For every fixed unit complex $z$, if $v\ne0$, then

$$\limsup_{j\to\infty}\frac{[\pm\Re(\bar zG_a(j^4))]_+}{j^6}
 \ \ge\ \frac{10653}{20000000}\,\|v\|_2
 \ =\ 0.00053265\,\|v\|_2$$

for both signs. Each signed cumulative prefix also satisfies

$$\limsup_{J\to\infty}J^{-7}\sum_{j\le J}[\pm\Re(\bar zG_a(j^4))]_+
 \ge \frac{10653}{280000000}\|v\|_2> \frac{\|v\|_2}{28000}.$$

In particular $\mathbf C\chi$ is the exact kernel of critical-scale decay in even one prescribed real projection, including one-sided decay. The matched row for $a\in\mathbf C\chi$ is $o(x^{3/2})$. The lower bounds refer to subsequences for each sign and direction. [Mlyle’s matched power-short dilation](https://github.com/mlyle/riemann-masullo/blob/c2eb094fffef928fdb72c2e180c255092e819347/research/5571/fourth-power-prime-curvature/spectral-interpolation-periodic-prime-convolution.md).

## Certificate

Let $H_r(s)=5^{-s}\zeta(s,r/5)$ and $M_a=\sum a_rH_r$. Four simple critical zeros $\rho_i=1/2+i\gamma_i$, near $-19.72905,-16.99590,-14.11546,-11.28290$ in ordinate, give the complex matrix $A=(H_r(\rho_i))_{1\le i\le4,\ 2\le r\le5}$. The accompanying Arb replay at 128 and 192 bits proves

$$|\det A|>3.487,\qquad \sigma_{\min}(A)>10653/12500=0.85224.$$

The four initial dyadic brackets come from the [earlier zero calibration](https://github.com/willzh0/riemann-masullo/blob/53cac8a4461b84ad1d9c96ea2305f48e82ba4a31/PROOF.md). Each is narrowed to two consecutive multiples of $2^{-48}$; the script again evaluates Hardy signs at both final endpoints with the exact radical root number. It bounds $L'$ away from zero across each interval and certifies positivity of its projection on the mean-point derivative, giving monotonicity of an appropriate real linear functional of $L$ on the interval. In addition $|L(\bar\rho_i,\chi)|>0.69$ in all four cases. The real leading principal minors of $A^*A-(10653/12500)^2I$ are enclosed about $2.8379137,2.9389104,1.5677404,0.0000612468$, all strictly positive. Sylvester's criterion supplies the singular-value bound at the actual roots, without floating-point eigenvalue assumptions. Since $M_\chi(\rho_i)=0$,

$$\max_i |M_a(\rho_i)|=\|Av\|_\infty\ge \|Av\|_2/2
 > (10653/25000)\|v\|_2\qquad (v\ne0).$$

The receipt also proves $|\rho_i(1+\rho_i)|<400$ and nonvanishing of both character factors and the quadratic factor at the extra locations needed below. Replay with Python, python-flint 0.8.0 and the command written in the receipt directory's script invocation below.

## Mellin continuation for the actual shortened row, including its mean

Put $\mu=5^{-1}\sum a_r$, $\eta=\chi^2$, $P_\chi(s)=\sum_p\chi(p)\log(p)p^{-s}$, $R_\chi(s)=P_\chi(s)/(s(s+1))$, and $\widetilde G(s)=\int_1^\infty G_a(x)x^{-s-2}\,dx$. The weight transform $\widehat W(w)=\int_0^\infty W(u)u^{w-1}du$ has a single pole at zero, of residue one. Its continuation decays rapidly on vertical lines by integrating against the compactly supported derivative. Starting at $1.1<\Re s<1.2$, Mellin inversion on $\Re w=1/5$ yields

$$\widetilde G(s)=\frac1{2\pi i}\int_{(1/5)}
 \widehat W(w)M_a(s+(1-\kappa)w)\,R_\chi(s-\kappa w)\,dw.$$

Indeed substitute $x=nu$ in each triangular prime sum. Both Dirichlet series converge absolutely in the initial region. Move the contour to $\Re w=-4$ there, crossing $0$ and $(1-s)/(1-\kappa)$. This gives

$$\widetilde G(s)=M_a(s)R_\chi(s)
 +\frac{\mu}{1-\kappa}\widehat W\!\left(\frac{1-s}{1-\kappa}\right)
 R_\chi\!\left(\frac{s-\kappa}{1-\kappa}\right)+E(s).$$

The new integral $E$ is holomorphic on $0.49<\Re s<1.25$: its prime series there is absolutely convergent, the Hurwitz factors have polynomial vertical growth on compact strips and the weight transform has rapid decay. The two apparent residues at the real point $s=1$ are opposite. In particular the mean cannot simply be dropped termwise.

In $\Re u>1/3$, $P_\chi(u)=-L'(u,\chi)/L(u,\chi)+L'(2u,\eta)/L(2u,\eta)$ plus a holomorphic prime-power series supported on exponents at least three. For real $u>0$, $\Re L(u,\chi)>0$ by pairing classes 1 and 4. Also $L(u,\eta)>0$: with $f(t)=t^{-u}$, each block is $(f(5k+1)-f(5k+2))-(f(5k+3)-f(5k+4))>0$ by strict convexity. Therefore the continuation and its conjugate counterpart are regular at every real $s\ge1/2$; at and above $1.25$ one uses the original convergence.

At $s=\rho_i$ the second argument $u_i=(\rho_i-\kappa)/(1-\kappa)$ has real part $29/79>1/3$. Arb verifies $L(u_i,\chi),L(u_i,\bar\chi),L(2u_i,\eta),L(2\rho_i,\eta)\ne0$, as well as $L(\rho_i,\bar\chi)\ne0$. For $g_z(x)=\Re(\bar zG_a(x))$, its Mellin transform is therefore regular on the above real interval and has residue

$$r_i=-\frac{\bar z M_a(\rho_i)}{2\rho_i(1+\rho_i)}$$

at $\rho_i$ whenever $M_a(\rho_i)\ne0$. The conjugated part is regular. The bounds give $\max_i|r_i|>(10653/20000000)\|v\|_2$.

## Two-sided oscillation and fourth-power sampling

For completeness, if $g_z(x)\le Kx^{3/2}$ eventually, its eventually nonnegative complement $h=Kx^{3/2}-g_z$, after deleting a finite initial interval, has Mellin transform $K/(s-1/2)-\widetilde g_z(s)$ plus an entire function. Landau's theorem for nonnegative Mellin transforms implies convergence on $\Re s>1/2$, since a finite abscissa of convergence there would be a real singularity. Then $|\widetilde h(\rho_i+\epsilon)|\le\widetilde h(1/2+\epsilon)$, and multiplication by $\epsilon\downarrow0$ gives $|r_i|\le K$. Apply this to $g_z$ and $-g_z$. This argument only uses projected residues; it does not presume any discrete spectral expansion of the mean term.

The passage to prescribed fourth powers uses the genuine signed short-interval PNT for the fixed character. Specifically, uniformly for $u^{0.67}\le h\le u$ one has $|\sum_{u<p\le u+h}\chi(p)\log p|\ll_\chi h/\log^3 u$. This follows from the fixed-modulus density and Vinogradov–Korobov estimates in the cited derivation, taking the truncation height $u^\alpha$ with $0.33<\alpha<1/3$; ordinary prime-power removal costs $O(\sqrt u\log^2 u)$. [Signed-interval derivation](https://github.com/mlyle/riemann-masullo/blob/c2eb094fffef928fdb72c2e180c255092e819347/research/5571/fourth-power-prime-curvature/spectral-interpolation-mod4-shallow-runs.md) · [Ramaré, Theorem 1.1](https://ramare-olivier.github.io/Maths/DensityEstimate-34.pdf) · [Khale, Theorem 1.1](https://arxiv.org/pdf/2210.06457).

Let $[b,c]=[j^4,(j+1)^4]$, $X=b$, $d=c-b\asymp X^{3/4}$. Write $w_n(x)=W(n/x^\kappa)$, $T_n(x)=\sum_p\chi(p)(x-np)_+\log p$. In the second derivative of $w_nT_n$, the two ordinary terms are $2w_n'T_n'+w_n''T_n$. They sum with coefficients $a(n)$ to $o_{a,W}(1)$, uniformly on the cell: $w_n^{(k)}=O_W(X^{-k})$ on $n\asymp X^\kappa$ for $k=1,2$, and the ordinary fixed-character PNT gives $|T_n'|=o(X/n)$, $|T_n|=o(X^2/n)$ uniformly there. Their total contribution to linear interpolation is $o(d^2)$.

The distributional remainder on the open cell is the signed measure with atoms $a(n)\chi(p)\log p\,w_n(np)$ at $np$. Its chord Green function on $[b,c]$ has supremum $O(d)$ and total variation $O(d)$; the same bounds hold after multiplication by $w_n$. Put $L=X^{0.745}$. For $n\le3X^\kappa$, every prime prefix starting at $b/n$ on a subinterval of length $\ell/n$ with $L\le\ell\le d$ is covered by the short-interval PNT, because $0.745-0.21-0.67(1-0.21)>0$. For $\ell<L$ trivial integer counting gives $O((L/n+1)\log X)$. Partial summation in each $n$, then absolute summation over $n$, bounds the singular error by

$$O_{a,W}\!\left(d^2/\log^2 X+dL\log^2 X+dX^\kappa\log X\right)=o(X^{3/2}).$$

Thus $G_a(x)$ agrees with its endpoint linear interpolant up to $o(X^{3/2})$ uniformly. Since $c/b\to1$, a one-sided upper bound on $g_z(j^4)/j^6$ transfers to the same asymptotic upper bound on all real cutoffs. This proves the pointwise limsups.

For the prefix claim write $u_j=[g_z(j^4)]_+$, and suppose $\sum_{j\le J}u_j\le KJ^7$ eventually. Put $I_\pm(s)=\int_1^\infty [\pm g_z(x)]_+x^{-s-2}\,dx$ where convergent. With $s=1/2+\epsilon$, convexity applied to the endpoint linear interpolant and the preceding error give

$$I_+(1/2+\epsilon)
 \le (4\sum_j u_j j^{-7-4\epsilon})+O(1)+o(1/\epsilon)
 \quad(\epsilon\downarrow0).$$

Indeed each endpoint weight integrates to half the cell width, and $x^{-5/2-\epsilon}\le j^{-10-4\epsilon}$ on the cell. After reindexing, the two weights for $u_j$ together have coefficient at most $(4+O(1/j))j^{-7-4\epsilon}$, uniformly for $0<\epsilon\le1/4$. The $O(1/j)$ errors are summable under the prefix bound. Partial summation gives $\limsup_{\epsilon\downarrow0}\epsilon I_+(1/2+\epsilon)\le7K$. In particular $I_+$ is absolutely convergent for real $s>1/2$. The continuation $I_- = I_+-\widetilde g_z$ is regular on that real interval; positivity and Landau give absolute convergence there also. At its left endpoint, $I_-(1/2+\epsilon)=I_+(1/2+\epsilon)+O(1)$ because $\widetilde g_z$ is regular at $1/2$. Therefore

$$|r_i|=\lim_{\epsilon\downarrow0}\epsilon|\widetilde g_z(\rho_i+\epsilon)|
 \le \limsup_{\epsilon\downarrow0}\epsilon(I_++I_-)(1/2+\epsilon)
 \le14K.$$

Let $K$ decrease to the prefix limsup and repeat for $-g_z$. This proves the stated $1/28000$ margin.

Reproduce the certificate with the following command after installing the pinned Python package.

    python rank4.py --output rank4.receipt.json
