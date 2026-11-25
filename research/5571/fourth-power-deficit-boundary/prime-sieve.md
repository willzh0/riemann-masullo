# A mean-square bound over the actual auxiliary primes

For $Q\to\infty,\ U=(Q,2Q]\cap\mathbb P,\ x\le Q^{1/3}$ and arbitrary complex $a_p$ supported on the odd primes up to $x$, let $B=\sum |a_p|^2$. Then uniformly in $x$ and the coefficients,
$$
 \frac1{|U|}\sum_{q\in U}\left|\sum_{p\le x}a_p(q/p)\right|^2
 \le (6+o(1))B. \tag{1}
$$
The bound concerns the actual primes with no loss of $\log Q$. Conditioning a pair to be distinct costs at most $|U|/(|U|-1)$ in a nonnegative expectation.

Choose $R=\lfloor Q^{1/6}/(\log Q)^2\rfloor$. Write $\mu$ for the Möbius function and $G=\sum_{r\le R}\mu^2(r)/\varphi(r)$. Selberg's optimizing square weights are supported on squarefree $d\le R$ and have the explicit values
$$
 \lambda_d=\frac{\mu(d)d}{G\varphi(d)}
   \sum_{\substack{m\le R/d\\(m,d)=1}}\frac{\mu^2(m)}{\varphi(m)}.
$$
Here $\lambda_1=1$. Because $d/\varphi(d)=\sum_{a\mid d}1/\varphi(a)$ for squarefree $d$, every resulting $am$ is squarefree, at most $R$, and unique by coprimality to $d$ of $m$. Thus $|\lambda_d|\le1$.

In the quadratic form write $(d,e)=\sum_{r\mid d,e}\varphi(r)$. Möbius inversion of the formula for $\lambda_d$ gives $\sum_{r\mid d,\ d\le R}\lambda_d/d=\mu(r)/(G\varphi(r))$. Therefore
$$
 \sum_{d,e}\frac{\lambda_d\lambda_e}{[d,e]}=1/G.
$$
For completeness $G=\log R+O(1)$. Set $f(n)=\mu^2(n)n/\varphi(n)=1*h(n)$ in Dirichlet-convolution notation, meaning $f=\mathbf1*h$. The multiplicative $h$ has $h(p)=1/(p-1)$, $h(p^2)=-p/(p-1)$, and $h(p^k)=0$ for $k>2$. Its Dirichlet series is absolutely convergent for real part greater than $1/2$, and $\sum h(m)/m=1$ because every Euler factor there is one. Summing $h(m)/m$ against the harmonic numbers $H_{\lfloor R/m\rfloor}=\log(R/m)+\gamma+O(m/R)$ proves the formula, with bounded error by absolute convergence (for example at $3/4$).

Now $W(n)=(\sum_{d\mid n}\lambda_d)^2$ equals one at every prime $q\in U$ and is nonnegative everywhere. Counting multiples of $[d,e]$ gives
$$
        \sum_{Q<n\le2Q}W(n)=Q/G+O(R^2).
$$
Use $W$ to majorize the nonnegative squared character polynomial at the primes. Its diagonal contributes at most $B\sum W(n)$, since every character has modulus at most one.

For different odd primes $p,r$, their Legendre product $\chi_{pr}$ is primitive modulo $pr$. After expanding the divisor square, for $\ell=[d,e]$ the inner multiple sum factors as
$$
 \sum_{\substack{Q<n\le2Q\\\ell\mid n}}\chi_{pr}(n)
 =\chi_{pr}(\ell)\sum_{Q/\ell<m\le2Q/\ell}\chi_{pr}(m).
$$
The Pólya–Vinogradov bound is $O(\sqrt{pr}\log(2pr))$, uniformly in the interval by subtracting partial sums. This also follows by Gauss sum completion and the harmonic bound for geometric sums; it holds when a common prime divides $\ell$, in which case the left side vanishes. [Hildebrand’s primitive character estimate (1988)](https://doi.org/10.4153/CMB-1988-050-1)

As $\sum_d|\lambda_d|\le R$ and $(\sum_p|a_p|)^2\le xB$, the absolute off-diagonal contribution is
$$
 \ll R^2 x^2\log(2x) B\ll QB/(\log Q)^3.
$$
The ordinary prime number theorem yields $|U|\sim Q/\log Q$, while $\log Q/\log R\to6$. Dividing the majorant by $|U|$ proves (1).

**Uniform cubes down to any growing cutoff.** For odd cube weights $a_p=(x-p^3)_+\log p$, (1) removes the factor $\log Q$ from the cube variance in the [fixed-pair proof](product-moments.md). Uniformly in $j\le J$ the probability of a discrepancy exceeding $\eta j^{16/3}$ from the unrestricted odd cube mass is $O(\eta^{-2}j^{-4/3}\log(2j))$. This applies also to the product twist by conditioning. Hence for any integer cutoff $K=K(J)\le J$ with $K\to\infty$, one single exceptional event of probability $O(K^{-1/6}\log(2K))$ suffices for
$$
       C_s(j^4)=(3/4+o(1))j^{16/3}
       \quad\text{for every }K\le j\le J
       \text{ and every nonidentity }s .
$$
Indeed set $\eta=K^{-1/12}$ and sum $j^{-4/3}\log(2j)$ to infinity. The PNT error on $j\ge K$ is uniformly $o(1)$, and the total contribution of powers $k\ge5$ has smaller order uniformly there.

**All-field transfer.** At $Q=J^{12},\ x=j^4$, (1) plus the established Hecke bound $\sum|b_p|^2\ll_F x^3\log(2x)$ gives each single twist $L^2$-norm $O_F(j^6\sqrt{\log(2j)})$. To treat the product twist condition on one prime and insert its signs into the coefficients. The prime 2 contributes $O_F(x)$. The absolute error for every adapted fourfold sign cell is at most the sum of the absolute three twists. Summing by Minkowski gives $O_F(J^7\sqrt{\log(2J)})$ in $L^2$, including on distinct pairs. The resulting transfer cost at fraction $\delta$ is $O_F(J^7\sqrt{\log(2J)}\,\delta^{-1/2})$, in addition to the existing uniform complete-to-prime error. [Actual class definitions and elementary second-moment transfer](https://github.com/mccorvie/riemann-masullo/pull/7627)

**Rational principal fixed class.** Use the notation from the [fixed-pair proof](product-moments.md). Under rational RH let $R_x=x^2/2-P=O(x^{3/2})$. For either fixed opposite-sign class, symmetry and positive-part convexity show $\mathbb E H_s\ge\mathbb E H_{\rm par}$ even for the complete masses. In the reverse direction, at each sample its deficit is at most
$$
       |R_x|+Z_+ + (\pm(S_q-S_d))_+ .
$$
The last difference has a symmetric distribution. Sampling without replacement gives
$$
 \mathbb E(\pm(S_q-S_d))_+
 \le\tfrac12\sqrt{\frac{2|U|}{|U|-1}\operatorname{Var}_U S_q}
 \le(\sqrt3+o(1))\sqrt B.
$$
The companion moment calculation gives $\mathbb E Z_+\le(1/2+o(1))\sqrt B$ for $j\ge J^{1/2}$, and the smaller prefix costs $O(J^{9/2})$. Thus the actual mean of each original fixed mixed complete class satisfies
$$
 \frac1{21}\le
 \liminf\frac{\mathbb E H_s}{J^7\sqrt{\log J}}\le
 \limsup\frac{\mathbb E H_s}{J^7\sqrt{\log J}}\le
 \frac{2+1/\sqrt3}{7}
 \qquad\text{on rational RH}.
$$
Under failure of rational RH, mlyle's every-prefix result instead gives $D(J)\gg J^{7+\delta}$ for some $\delta>0$. The unconditional all-field estimate and the uniform $O(J^{19/3})$ cost of the higher powers imply $H_s/D(J)\longrightarrow1$ in $L^2$ uniformly over choices of the three cells, including adapted selections. In particular the arithmetic $\mathbb E H_s\asymp D(J)+J^7\sqrt{\log J}$ for each fixed mixed class holds unconditionally. This estimate alone leaves the critical upper bound in #5571 open.

The [finite verifier](verify_product_moments.py) checks the weights, the quadratic identity, and the majorant by exact rational arithmetic at radius $30$. The pre-existing elementary and sixth-moment transfers are stated in [PR #7648](https://github.com/mccorvie/riemann-masullo/pull/7648).
