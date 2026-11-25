# A single subsequence of fourth-power Hecke deficits

For Theorem 12.5.1.1, pp. 519–520, fix a number field and a unitary Hecke character trivial on the chosen norm section. Use the [degree-one statistic and notation](README.md)
$$
 S_\chi(x)=\sum_{p\le x}(x-p)\Re a_\chi(p)-\mathbf 1_{\chi=1}x^2/2,\qquad
 A_\chi(j)=[-S_\chi(j^4)]_+,\qquad D_\chi(J)=\sum_{1\le j\le J}A_\chi(j).
$$
Every nontrivial zero $\rho_0$ with $\beta_0=\Re\rho_0>1/2$ supplies constants $c,C>0$ such that, at **every** sufficiently large integer $J$,
$$
 D_\chi(J)\ \ge\ c\,J^{4\beta_0+5}\exp\{-C(\log\log J)^2\}.
$$
Combining this bound with the [rightmost-boundary classification](README.md) removes the subpower loss for each target.
$$
 D_\chi(J)\gg_{F,\chi,\rho_0}J^{4\beta_0+5}\qquad(J\text{ sufficiently large}).
$$
In fact, if $\beta_0<\eta$, the ratio tends to $+\infty$. Choose another zero of real part $\beta_1>\beta_0$. The factor $J^{4(\beta_1-\beta_0)}$ dominates $\exp(C(\log\log J)^2)$. If $\beta_0=\eta$, the supremum is attained and the boundary-profile proof gives a strictly positive lower limit. The constants and starting index may depend on the individual field, character and zero.

Here $\eta=\sup(\{1/2\}\cup\{\Re\rho\})$. Consequently
$$
 \lim_{J\to\infty}\max\!\left(7,\frac{\log(1+D_\chi(J))}{\log J}\right)=4\eta+5 .
$$
Above $1/2$ this is the ordinary limit without the maximum. The same holds at $1/2$ for every principal field by the principal-character endpoint proof. For every $1/2\le b\le1$, a single unbounded sequence $J_k$ with $D_\chi(J_k)\le J_k^{4b+5+o(1)}$ therefore excludes all zeros strictly to the right of $b$. Conversely, exclusion gives the no-loss upper bound $D_\chi(J)=O_{F,\chi,b}(J^{4b+5})$ at all sufficiently large $J$.

Mlyle proved the all-field large-deficits theorem and the ordinary rational exponent. His rational proof uses Ingham’s zeta zero-density bound to obtain the constant-factor estimate from one fixed compact annihilating test. Here the test varies with the cutoff and its logarithmic support length is $O((\log\log x)^2)$. The only zero-count input is the classical fixed-character count in a unit-height slab. The resulting subpower loss suffices for the all-field limit. [Mlyle’s rational proof, including the positive and signed probes](https://github.com/mlyle/riemann-masullo/blob/255d2b1531f3534cd35ea5dd9eb379fadd2c1104/research/5571/rational-fourth-power-deficit.md) · [All-field fourth-power chord estimate, #7603](https://github.com/mccorvie/riemann-masullo/pull/7603)

## The signed series and its real zeros

Write $F(y)=-e^{-3y/2}S_\chi(e^y)$. Uniformly for $y\ge1$, the once-integrated explicit formula and degree-one transfer give
$$
 F(y)=\sum_{z\in Z}c_z e^{z y}+O_{F,\chi}(1),\qquad
 |\Re z|\le\tfrac12,\qquad \sum_{z\in Z}|c_z|<\infty.
$$
Here $z=\rho-1/2$ and conjugate frequencies are included when taking the real part. At a nonreal $\rho=\beta+i\gamma$ the coefficient is
$(m_\chi(\beta+i\gamma)+m_\chi(\beta-i\gamma))/(2\rho(\rho+1))$.
At a real zero $\beta$ it is $m_\chi(\beta)/(\beta(1+\beta))>0$. The intrinsic Euler factors exclude ramified local characters. The only principal term is $\mathbf1_{\chi=1}x^2/2$, as the character is normalized.

For completeness the explicit formula holds even when $\eta=1$. Shift the triangular Perron kernel $-(L'/L)(u,\chi)x^{u+1}/[u(u+1)]$ from $\Re u=2$ to $-1/4$. The functional equation, Stirling and the absolutely convergent Euler logarithmic derivative at $5/4$ bound the left line by $O_{F,\chi}(\log(2+|\Im u|))$ before applying the kernel. Horizontal sides at good heights vanish as in the [absolute first-Riesz formula](README.md#absolute-first-riesz-formula). The finite uncompleted Hecke function has at most finitely many trivial-zero locations on the imaginary axis for fixed archimedean parameters. They contribute $O(x)$ away from zero. A possible collision with the Perron pole at zero contributes $O(x\log(2x))$ because the logarithmic derivative has at worst a simple pole. All other gamma poles have real part at most $-1/2$. The shifted integral is $O(x^{3/4})$. The remaining residues give the principal pole and the displayed absolutely summable nontrivial-zero coefficients. The $O_F(x^{3/2})$ transition to the actual signed prime statistic gives the stated bounded error in $F(y)$. [Hecke gamma factors, order-one product and slab count, Rajan, §§1–2](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/85/3/110150/distribution-of-values-of-hecke-characters-of-infinite-order) · [Mlyle’s degree-one comparison, #7587](https://github.com/mccorvie/riemann-masullo/pull/7587)

## A pair of growing compact tests

Use $\widehat K(z)=\int e^{zv}\,dK(v)$. Put $z_0=\rho_0-1/2$, choose $0<a<\Re z_0$, and fix $G>2|\Im z_0|+2$. Call a frequency exterior here if $\Re z>a$. There are finitely many exterior frequencies with $|\Im z|\le G$, including all real ones.

For each conjugate pair $\alpha\pm i\gamma$, $\gamma>0$, the probability measure with masses in the ratio $e^{\alpha d}:1$ at $0,d$, where $d=\pi/\gamma$, kills both frequencies. Use one such factor per distinct pair. Convolve the factors for the low nonreal exterior frequencies. The resulting probability is supported on some $[0,W]$. Convolution with the uniform probability density on $[0,W+3]$ yields a compact probability density $P_0$ that still kills those pairs and is constant and strictly positive on $[W,W+3]$ (the interior suffices).

Choose a smooth complex density $L_0$ in the interior of that interval whose transform kills every low exterior frequency other than $z_0$, including the remaining real ones, and is nonzero at $z_0$. Explicitly, take a nonnegative smooth bump $\phi$ with small enough support to have $\widehat\phi(z_0)\ne0$ and apply $\prod_{\zeta\ne z_0}(-d/dv-\zeta)$ over the indicated finite set. Integration by parts multiplies its transform by $\prod_{\zeta\ne z_0}(z-\zeta)$. Thus $|L_0|\le C_0 P_0$. This construction also works when the target is real.

For $N=\lceil y\rceil>G$, let $B_N$ be the convolution of the same binary factors for all distinct exterior conjugate pairs with $G<\gamma\le N$. Its support is in $[0,W_N]$, where
$$
 W_N=\pi\sum_{\text{selected pairs}}\gamma^{-1}
       \ll_{F,\chi}(1+\log^2(2+N)).
$$
The usual $O_{F,\chi}(\log(2+k))$ count in $[k,k+1]$ proves this and also $\sum_{\gamma>G}\gamma^{-2}<\infty$. At the chosen target $|\widehat B_N(z_0)|$ is bounded below by a constant independent of $N$. Rotate each two-point expectation through $-\Im(z_0)d/2$. Its real part is at least $\cos(|\Im z_0|d/2)$ because $\Re z_0>0$ and both support points are nonnegative. The product of these cosines has a positive lower bound by the square-summability above. At arbitrary $z$ in the strip $|\widehat B_N(z)|\le e^{W_N/2}$.

Let $H_N$ be the law of the sum of $N$ independent uniform variables on $[-8/N,8/N]$. Its support lies in $[-8,8]$ and
$$
 \widehat H_N(z)=\left(\frac{\sinh(8z/N)}{8z/N}\right)^N,\qquad
 \sup_{\substack{|\Re z|\le1/2\\|\Im z|\ge N}}|\widehat H_N(z)|\le e^4\,8^{-N}.
$$
Indeed $|\sinh w|\le e^{|\Re w|}$ and $|8z/N|\ge8$ on that set. At the fixed $z_0$ the individual factor is $1+O_{z_0}(N^{-2})$, so $\widehat H_N(z_0)\to1$.

Finally put $P_N=P_0*B_N*H_N$, $L_N=L_0*B_N*H_N$. The first is a probability density with $\|P_N\|_\infty\le\|P_0\|_\infty$. The pointwise bound $|L_N|\le C_0P_N$ persists. Both supports are in $[-8,W_N+O(1)]$, and $\inf_{N\gg1}|\widehat L_N(z_0)|>0$.

## The lower bound on every prefix

Absolute convergence permits termwise integration against either probe over its finite support. The frequencies of real part at most $a$ contribute $O(e^{ay+O(W_N)})$. The frequencies of height greater than $N$ contribute $O(e^{y/2+O(W_N)}8^{-N})$. The bounded error of $F$ contributes $O(1)$ uniformly in $N$. The sum of these three errors is $o(e^{(\Re z_0)y})$.

Every nonreal exterior frequency of height at most $N$ is killed by $P_N$. Its remaining exterior real-zero terms are nonnegative. Thus $\int F(y+v)P_N(v)\,dv$ is bounded below by minus the stated error. In the signed test only the target survives among the low-height exterior frequencies. Hence
$$
 \left|\int F(y+v)L_N(v)\,dv\right|\gg e^{(\Re z_0)y},\qquad
 \int [F(y+v)]_+P_N(v)\,dv\gg e^{(\Re z_0)y}.
$$
The last step uses $2[F]_+=|F|+F$ and $|L_N|\le C_0P_N$.

On $x\in[j^4,(j+1)^4]$, the prime weights up through $j^4$ interpolate linearly and the quadratic centering is concave. Each intervening term has coefficient of magnitude at most $[F:\mathbf Q]\log((j+1)^4)$ and chord error at most $(j+1)^4-j^4$. Counting the intervening integers therefore gives
$$
 [-S_\chi(x)]_+\le A_\chi(j)+A_\chi(j+1)+O_F(x^{3/2}\log(2x)).
$$
Every grid cell meeting the support of the probes has logarithmic length $4\log(1+1/j)\ll e^{-y/4}$ since $x\ge e^{y-8}$. Choose $y=4\log J-C_1(1+\log\log J)^2$ with $C_1$ large enough that the full support is below $4\log(J-1)$. Then $x^{-3/2}\ll e^{-3y/2}$ there. The density bound for $P_N$ and the fact each endpoint occurs at most twice give
$$
 \int [F(y+v)]_+P_N(v)\,dv
 \ll_{F,\chi,\rho_0} e^{-7y/4}D_\chi(J)+1+y+W_N .
$$
Combining the inequalities yields $D_\chi(J)\gg e^{(\beta_0+5/4)y}$, which proves the claimed loss $e^{-C(\log\log J)^2}$. Letting $\beta_0$ approach $\eta$ gives the ordinary exponent above the critical line. The upper bound is the absolute first-Riesz estimate. The implication concerns an upper bound on a single unbounded subsequence for each character. Producing those bounds arithmetically remains the unresolved step.
