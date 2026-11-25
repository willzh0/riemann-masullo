# Direct finite ideal Gram matrices for the ordinary Hecke Green mass

The following is a written implication for Theorem 12.5.1.1, pp. 519–520. It uses the actual ordinary normalized Hecke continuation and its pole-clearing factor from [#7696](https://github.com/mccorvie/riemann-masullo/pull/7696), the quarter-plane growth and true Hardy prediction distance from [#7707](https://github.com/mccorvie/riemann-masullo/pull/7707), and Mellin–Plancherel. The arithmetic inequality at the end is open. The classical distance method goes back to Nyman and Beurling. Delaunay, Fricain, Mosaki and Robert prove a general Dirichlet-series criterion and give explicit Dirichlet examples in Theorems 2.2/2.4 and Section 7.2. Their proof also uses the Mellin image of causal dilates. Burnol identifies the Hecke Blaschke factor. [Delaunay et al.](https://arxiv.org/abs/1101.1199) · [Burnol, Theorem 3.2](https://arxiv.org/pdf/math/0001013#page=15)

Let $F$ be a number field and let $\chi$ be a unitary character trivial on the chosen positive norm section. Write $a_m$ for its ordinary ideal-norm coefficients and let $\delta$ be $1$ for the principal character and $0$ otherwise. Put
\[
 A(s)=((s-1)/s)^\delta L_\chi(s),\qquad
 F_k(s)=A(s)/(s+1)^k,\qquad z=(s-2)/(s+1).
\]
Use the removable analytic value at $s=1$. Under the inverse Cayley map $s=(2+z)/(1-z)$ the boundary is the line $\Re s=1/2$, with Haar probability represented by the Cauchy density $3/(2\pi|s+1|^2)$. Let $G_\chi\ge0$ be the full right-hand Green sum from #7696 and $d_\chi^2=1-\exp(-2G_\chi)$.

For stage $k\ge1$ define $X=2^{k^2}$, $r=1+1/k^2$, $r_j=r^j$ for $0\le j\le k$, and $m=k+1$. A stage can use any $X$ in the finite definition. The convergence proof uses this specified $X$.

## Finite arithmetic

For $y\ge1$, put $w=\log y$ and
\[
 h_k(y)=\frac{w^k}{y k!},\qquad h_{k,\delta}(y)
 =h_k(y)-\delta\Big(1-\frac1y\sum_{\ell=0}^k\frac{w^\ell}{\ell!}\Big).
\]
Set both kernels to zero for $0<y<1$. Define the $m$ functions on $1\le x\le X$ by
\[
 v_j(x)=\sum_{1\le n\le x/r_j}a_n h_{k,\delta}(x/(r_j n)),\qquad v_*(x)=x^{-1}.
\]
Every needed norm is at most $\lfloor X\rfloor$. In the inner product $3\int_1^X\overline f g\,dx/x^2$, form $K_{ij}=\langle v_i,v_j\rangle$ and $b_i=\langle v_i,v_*\rangle$. Put $c=1-X^{-3}$, $t=12/(5\sqrt X)$, and form the nonnegative finite number
\[
 U_k=\min\{1,\ c+t-b^*(K+tmI)^{-1}b\}.
\]
The positive multiple of the identity ensures a unique Hermitian solve. Equivalently take the minimum over complex coefficient vectors $w$ of the integrated finite squared residual plus $t(1+m\|w\|_2^2)$, then cap it at one. The exact entries use only finite arithmetic, logarithms at positive rational arguments and the given ideal coefficients. Splitting at the points $r_j n$ gives elementary antiderivatives of products of log polynomials times integer powers of $x$. No ordinary or completed $L$-value is a measurement input.

Then, for every fixed normalized $\chi$,
\[
 d_\chi^2\le U_k \quad\hbox{at all sufficiently large stages},\qquad
 U_k\longrightarrow d_\chi^2.
\]
Consequently $U_k<1$ eventually and $-\tfrac12\log(1-U_k)$ is an eventual upper for $G_\chi$ converging to it. The map from the ideal coefficients and the principal indicator to $U_k$ contains no field-dependent exponent, initial stage or growth constant. The proof of the stage from which the upper holds can depend on $\chi$. If $|A(s)|\le |s+1|^k$ for every $\Re s\ge1/4$ already at a specified stage, it holds there. The absolute original exterior sum at any positive width $\alpha$, including both edges, is bounded there by $3W_{\chi,\varphi}[-\log(1-U_k)]/(4\alpha)$ whenever $U_k<1$. The remaining assertion is that every character permits arbitrarily small values of this particular finite statistic at arbitrarily late stages.

## Proof

1. For $\Re s>1$, the Mellin transform $\int_1^\infty h_k(y)y^{-s}\,dy/y$ equals $(s+1)^{-k-1}$. The transform of $\int_1^y h_k(u)\,du/u$ is $s^{-1}(s+1)^{-k-1}$ and the elementary incomplete gamma integral gives the displayed polar correction. The Dirichlet series of the actual ideal-norm coefficients converges absolutely on this half-plane. Thus $v_j$ has transform $r_j^{-s}F_k(s)/(s+1)$ and $v_*$ has transform $1/(s+1)$.

2. By the quarter-plane polynomial bound, there exist $C_\chi,M_\chi$ such that $|A(s)|\le C_\chi|s+1|^{M_\chi}$ on $\Re s\ge1/4$. Since $|s+1|\ge5/4$, all sufficiently large $k$ have $|F_k(s)|\le1$ throughout this half-plane. For $p(s)=\sum_j w_j r_j^{-s}$, put $B=\sum_j|w_j|$ and $v_p=v_*-\sum_jw_jv_j$. The analytic function $(1-pF_k)/(s+1)$ belongs to the Hardy space of $\Re s>1/4$, since on every line there its magnitude is at most $(1+B)/|s+1|$. The half-plane Paley–Wiener isometry gives a single causal inverse under the Fourier–Laplace transform and its line Plancherel formulas. The inverse agrees with the above $v_p$ by uniqueness on the ordinary Euler line. In particular
\[
 \int_1^\infty |v_p(x)|^2 x^{-1/2}\,dx/x
 \le\frac1{2\pi}\int_\mathbb R\frac{(1+B)^2\,dt}{(5/4)^2+t^2}
 =\frac25(1+B)^2.
\]
One may also take $\sigma\downarrow1/4$ after the interior Plancherel identities by monotone convergence on $x\ge1$. On the critical line the full squared residual in disk Haar norm is exactly $3\int_1^\infty|v_p(x)|^2 dx/x^2$. Its tail past $X$ is at most $6(1+B)^2/(5\sqrt X)$, hence at most $t(1+m\|w\|_2^2)$. This proves the finite upper on every actual trial.

3. Every $pF_k$ in this Hardy space is divisible in $H^2$ by every finite Blaschke product for a finite multiset of its right-hand zeros, with multiplicities. The distance from the constant one to $B_JH^2$ is $\sqrt{1-|B_J(0)|^2}$. Take the supremum over finite submultisets. Their product deficits increase to $1-e^{-2G_\chi}$. This proves the lower bound $d_\chi^2$ for every feasible certified upper and for one.

4. The true Szegő predictor from #7707 says that for sufficiently large fixed $k_0$, complex disk polynomials $P(z)F_{k_0}$ approximate one up to distance $d_\chi$. For a fixed such $P$, expand $P(1-3/(s+1))F_{k_0}$ as a finite linear combination of $F_h$ with fixed $h\ge k_0$. We approximate each summand in a *single* matrix stage. Put $\tau=\log r$. For $k\ge h$ use the polynomial in the available shifts
\[
 p_{k,h}(s)=\tau^{-(k-h)}(1-e^{-\tau(s+1)})^{k-h}
 =\tau^{-(k-h)}\sum_{j=0}^{k-h}{k-h\choose j}(-1)^j r^{-j} r_j^{-s}.
\]
Then
\[
 p_{k,h}F_k
 =\left[\int_0^1 e^{-u\tau(s+1)}\,du\right]^{k-h}F_h
 \longrightarrow F_h
\]
in the true boundary Hardy norm. Indeed the bracket has magnitude at most one on the critical line, and its difference from one has magnitude at most $\tau|s+1|/2$. Since $k\tau\to0$, its $(k-h)$th power tends to one at every finite $s$. Dominated convergence applies to $4|F_h|^2$ in the Cauchy boundary measure. The coefficient $\ell^1$ norm is at most $(2/\tau)^{k-h}$, bounded by $(4k^2)^k$. For a fixed finite combination the same bound holds with a fixed prefactor. The additional ridge cost is at most a fixed multiple of $2^{-k^2/2}(1+(k+1)(4k^2)^{2k})$, which tends to zero. The finite-window squared residual is at most the full norm. Taking the upper limit and then the infimum over $P$ yields the convergence. Only $k+1$ rational shifts occur and the largest $r_k$ tends to one. Exponential cancellations inside the very small finite differences can make numerical solves ill-conditioned. Certified input intervals or exact finite expressions are appropriate.

## Fixed-character principal cases and comparison

The normalization, constant $3$ in the norm change, and principal correction are present for every field; choosing $h_{k,0}$ for a principal character would give an incorrect pole term. For simplicity one may feed a trial vector with rational real and imaginary parts into the primal expression to certify a true upper instead of subtracting two close matrix quantities. Upper verification using the true integer character period in the primitive-quartic example is independent of this variable-order construction.

No zero-free window, simplicity assumption, prior cutoff verification or strip trace enters the finite formulas. The all-field quarter-plane growth and full boundary Jensen identity supply the analytic deductions. No signed arithmetic upper tending to zero has been established.
