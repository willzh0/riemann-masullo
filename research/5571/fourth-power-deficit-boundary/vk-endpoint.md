# A Vinogradov–Korobov bound for the first prime Riesz mean

For the rational principal character put
$$
P(x)=\sum_{p\le x}(x-p)\log p,\qquad
D(J)=\sum_{j\le J}[j^8/2-P(j^4)]_+,\qquad
V(x)=\frac{(\log x)^{3/5}}{(\log\log x)^{1/5}}.
$$
If $R$ is the denominator in an asymptotic Vinogradov–Korobov zero-free region, set
$$
 c_R=\left(\frac{5^6}{3^4R^3}\right)^{1/5},\qquad C_R=4^{3/5}c_R.
$$
Then, unconditionally,
$$
 |P(x)-x^2/2|=o(x^2e^{-c_R V(x)}),\qquad
 D(J)=o(J^9e^{-C_R V(J)}).
$$
The constants $(c_R,C_R)$ are approximately $(0.2801957911,0.6437208886)$ with $R=48.1588$, and $(0.2804999389,0.6444196367)$ with $R=48.0718$. They come from the two factors in the first Riesz kernel. These are asymptotic bounds. [Mossinghoff–Trudgian–Yang, Theorem 1.2](https://arxiv.org/pdf/2212.06867#page=2) · [Bellotti, Theorem 1.3](https://arxiv.org/pdf/2306.10680#page=3)

## Explicit formula and zero density

Write $L=\log x,\ v=V(x)$. For $u\ge u_0>1$ in the proved zero-free range put
$$
 h(u)=\frac{1}{R u^{2/3}(\log u)^{1/3}},\qquad
 W_2(L)=\min_{u\ge u_0}\{2u+Lh(u)\}.
$$
The first Riesz mean of the von Mangoldt function satisfies
$$
 \frac{\sum_{n\le x}(x-n)\Lambda(n)-x^2/2}{x^2}
 =-\sum_\rho\frac{x^{\rho-1}}{\rho(\rho+1)}+O(x^{-1}).
$$
The sum runs over all nontrivial zeros with multiplicity and converges absolutely. Replacing the complete sum by $P(x)$ costs $O(x^{3/2})$ before normalization, since $\sum_{m\ge2}\vartheta(x^{1/m})\ll\sqrt{x}+x^{1/3}\log x\ll\sqrt{x}$ by Chebyshev's bound. [Billington–Cheng–Schettler–Suriajaya, (10)–(11), citing Ingham, Chapter IV, Theorem 28](https://arxiv.org/pdf/2306.09102#page=5) · [Grenié–Molteni, (1.2)–(1.3a) for real $x$](https://arxiv.org/pdf/1312.4465#page=2)

Choose a fixed $K>2(c_R+1)$. Put $T=e^{Kv}$ and $\delta=Kv/L$. For $\beta\le1-\delta$, the normalized absolute zero sum is $O(e^{-Kv})$, since $\sum_\rho|\rho(\rho+1)|^{-1}<\infty$. The contribution from $|\gamma|>T$ is $O((\log T)/T)$ by dyadic summation of $N(t)\ll t\log t$. The finitely many zeros with $|\gamma|<e^{u_0}$ contribute $O(x^{-\epsilon})$ for some fixed $\epsilon>0$. Every remaining zero has $u=\log|\gamma|\ge u_0$, and its absolute contribution is at most
$$
 \exp[-2u-Lh(u)]\le e^{-W_2(L)}.
$$
Ford's uniform estimate near one gives
$$
 N(1-\delta,T)\ll T^{58.05\delta^{3/2}}(\log T)^{15}\ll_K v^{15}.
$$
Indeed $\delta^{3/2}\log T=K^{5/2}(\log L)^{-1/2}$. Ford counts all zeros in $\sigma\le\Re\rho\le1,\ |\Im\rho|\le T$. Therefore
$$
 |P(x)-x^2/2|/x^2
 \ll v^{15}e^{-W_2(L)}+v e^{-Kv}+x^{-\epsilon'}.
$$
Ford's density estimate covers $\sigma\in[0.9,1]$, which contains $1-\delta$ for all sufficiently large $x$. [Ford, p. 2, application (iii)](https://www.ford126.web.illinois.edu/wwwpapers/zetabd.pdf#page=2) · [Johnston, (2.9) and its range](https://arxiv.org/pdf/2411.13791#page=4)

Alternatively, classical Ingham density at any fixed $0<\delta<1/4$ bounds the number in $e^{s-1}\le|\gamma|<e^s,\ \beta>1-\delta$ by $O_\delta(s^5e^{d_\delta s})$ with $d_\delta=3\delta/(1+\delta)$. Each weight is at most $e^2e^{-2s-Lh(s)}$. For $a<2-d_\delta$ retain $s^5e^{-(2-d_\delta-a)s}$ as a summable majorant, and minimize $as+Lh(s)$. Letting $\delta\downarrow0$ proves the bounds for every strict $c<c_R,\ C<C_R$. [Ingham, *On the estimation of $N(\sigma,T)$*](https://doi.org/10.1093/qmath/os-11.1.201)

## The saddle and the exact leading constant

Set $\ell=\log L,\ H=(\log\ell)/\ell,\ b=(5/3)^{1/3}/R$. With $u=zv$, uniformly on any fixed compact subinterval of $0<z<\infty$,
$$
 \frac{au+Lh(u)}{v}
 =f_a(z)+\frac{b z^{-2/3}}9H+O_{a,R}(1/\ell),
 \qquad f_a(z)=az+bz^{-2/3}.
$$
This follows by expanding $\log(zv)=3\ell/5-(\log\ell)/5+\log z$. The minimizers lie in a fixed compact subinterval for all large $L$. Indeed $au$ excludes $u\ge Mv$ for sufficiently large $M$, and monotonicity of $h$ excludes $u\le mv$ for sufficiently small fixed $m>0$. The minimum of $f_a$ is attained at $z_0=(2b/(3a))^{3/5}$, where $b z_0^{-2/3}=3az_0/2$. Thus
$$
 \min f_a=\tfrac52 az_0,\qquad (\min f_a)^5=\frac{5^6a^2}{4\cdot3^4R^3}.
$$
The coefficient of $H$ at $z_0$ is $(\min f_a)/15$. On the compact interval $f_a(z)-f_a(z_0)\gg(z-z_0)^2$, and the coefficient $b z^{-2/3}/9$ is Lipschitz. The perturbation of the minimum beyond substituting $z_0$ therefore costs $O(H^2)=O(1/\ell)$. Taking $a=2$ yields
$$
 W_2(L)=c_R v\left(1+\frac{\log\ell}{15\ell}+O_R(1/\ell)\right).
$$
The positive secondary term dominates $15\log v$. To translate it to $x=j^4$, write $\ell_j=\log\log j$. Then
$$
 V(j^4)=4^{3/5}V(j)\left(1-\frac{\log4}{5\ell_j}+O(\ell_j^{-2})\right),\qquad
 \log\log(j^4)=\ell_j+\log 4.
$$
Consequently
$$
 W_2(4\log j)=C_RV(j)
 \left(1+\frac{\log\ell_j}{15\ell_j}+O_R(1/\ell_j)\right).
$$
The term $V(j)\log\ell_j/\ell_j$ tends to infinity faster than $\log V(j^4)$. It follows that $[j^8/2-P(j^4)]_+=o(j^8e^{-C_RV(j)})$. The latter majorant is eventually increasing since $dV(j)/d\log j=o(1)$. Splitting off finitely many samples and summing proves the claim for $D(J)$.

## Actual optimized complete deficits

Let $U_J=(J^{12},2J^{12}]\cap\mathbb P$. The marginal comparison and sixth moment in the companion note give $H_*(q,d;J)\le D(J)+\min\{B_J(q),B_J(d)\}$ and $\|B_J\|_6\ll_\varepsilon J^{7+\varepsilon}$ for uniform $q\in U_J$. Set $E_J=\{q:B_J(q)>\tfrac12 J^9e^{-C_RV(J)}\}$. Then
$$
 |E_J|\ll_\varepsilon J^{6\varepsilon}e^{6C_RV(J)},\qquad
 H_*(q,d;J)\le J^9e^{-C_RV(J)}\quad ((q,d)\notin E_J^2)
$$
for every sufficiently large $J$. In particular $|E_J|\ll_\nu J^\nu$ for every fixed $\nu>0$, since one may take $\varepsilon<\nu/12$. This establishes the one-sided bound with the exact $C_R$ above. The $J^{7+o(1)}$ full-prefix scale remains open. [Marginal comparison and definitions](actual-complete-deficits.md) · [Repository sixth-moment calculation](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7154774282)

The absolute Riesz explicit formula and the method of estimating zero counts near one are classical. Billington and coauthors give the same Riesz formula in their Goldbach analysis. Johnston's related unsmoothed PNT theorem uses $\min_u(u+Lh(u))$; the factor $2u$ above comes directly from $|\rho(\rho+1)|^{-1}$. Neither source states the rational Jacobi-class deficit assertion. [Billington and coauthors, §2](https://arxiv.org/pdf/2306.09102#page=5) · [Johnston, Theorem 2.1](https://arxiv.org/pdf/2411.13791#page=3)
