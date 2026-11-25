# A bound at every sufficiently late original Hardy grid, with explicit onset

Keep the primitive quartic character $\chi(2)=i$ and disk exponent five. For the actual finite ideal grid $U_n$ of [#7707](https://github.com/mccorvie/riemann-masullo/pull/7707),
\[
 n\ge 10^{1200}\quad\Longrightarrow\quad
 U_n<0.076415386910838,\qquad
 -\tfrac12\log(1-U_n)<0.039746430677.
\]
The proof starts from the [512 specified rational Dirichlet coefficients](dilates-1-512.json) and their [exact squared residual upper](dilates-1-512-period-receipt.json). It constructs an admissible polynomial for **every** grid in the stated range and bounds all of its ideal entries through the proven canonical row error. The calculation certifies upper bounds for the minima without enumerating their coordinates. The threshold serves to make every constant explicit. Producing an upper tending to zero for the unrestricted original row remains open.

## A high-frequency bound from the period

Let $B_m=\sum_{j\le m}j\chi(j)$, with $|B_m|\le\sqrt2\,m$ as shown in the [period proof](README.md). Put $q(u)=e^{-3u/2}B_{\lfloor e^u\rfloor}$ for $u\ge0$ and $q=0$ otherwise. Use $\widehat q(t)=\int q(u)e^{-itu}du$. Absolute summation on an Euler line, followed by analytic continuation of the absolutely convergent integral to the critical line, gives $\widehat q(t)=L(1/2+it,\chi)/(3/2+it)$. Hence $\|L\|_{L^2(d\mu)}^2=3\|q\|_2^2\le6$, where $d\mu=3\,dt/(2\pi((3/2)^2+t^2))$.

For $X\ge1$, truncate $q$ at $\log X$. The jumps up to that point have total magnitude at most $\sum_{n\le X}n^{-1/2}\le2\sqrt X$. The continuous derivative has absolute integral at most $(3/2)\sqrt2\int_0^\infty e^{-u/2}du=3\sqrt2$. The final jump is at most $\sqrt2/\sqrt X$. The resulting total variation is at most $8\sqrt X$, so the modulus of the Fourier transform of the truncation is at most $8\sqrt X/|t|$. The discarded function has squared $L^2$ norm at most $2/X$. By Plancherel and the triangle inequality, then taking $X=\sqrt T$, this proves for $T\ge1$
\[
 \|1_{\{|t|>T\}}L(1/2+it,\chi)\|_{L^2(d\mu)}
 \le \sqrt{192/\pi}\sqrt{X/T}+\sqrt{6/X}<11T^{-1/4}.
\]

## A genuine polynomial from the Dirichlet trial

Write $p(s)=\sum_{d=1}^{512}a_d d^{-s}$. Its coefficient sum obeys $A=\sum|a_d|\le55.5936<56$. Put $s(z)=(2+z)/(1-z)$, $F(z)=((1-z)/3)^5L(s(z),\chi)$ and $H(z)=(3/(1-z))^5p(s(z))$. For $T=10^{36}$, $\tau=10^{-88}$ and $\lambda=1-\tau$ compare $H(\lambda z)F(z)$ with $p(s)L(s,\chi)$ on the boundary. Their scalar multiplier difference before $L(s,\chi)$ is
\[
 p(s(\lambda z))\big[(1-z)/(1-\lambda z)\big]^5-p(s(z)).
\]
For $|z|=1$, write $w=1-z$, $w_\lambda=1-\lambda z$. The identity $|w_\lambda|^2=(1-\lambda)^2+\lambda|w|^2$ gives $|w/w_\lambda|\le\lambda^{-1/2}$. The multiplier difference everywhere has norm at most $3A$. For $|\Im s|\le T$,
\[
 |s(\lambda z)-s(z)|\le\tau(T+2)^2,\qquad |w/w_\lambda-1|\le\tau(T+2).
\]
Both points and their joining line segment have real part at least $1/2$, where $|p'|\le A\log512<400$. Since $\lambda\ge0.99$ the difference of fifth powers has norm at most $6|w/w_\lambda-1|$. Multiplying the central bound by $\|L\|_2\le\sqrt6$ gives a central error of at most $3000\tau(T+2)^2$. The high-frequency error is at most $3\cdot56\cdot11\,T^{-1/4}=0.000001848$.

The function $H(\lambda z)$ has modulus at most $M=56(6/\tau)^5<10^{446}$ on the circle of radius $1+\tau/2$ because $|\lambda z|<1$ there. Truncate its Taylor series at degree $D=10^{92}$. The polynomial $P$ has coefficients of modulus at most $M$. The uniform disk error is at most $(2M/\tau)e^{-2500}<10^{-500}$, by $\log(1+\tau/2)\ge\tau/4$. The true normalized $F$ is bounded by one. The entries of $P$ can also be written directly from the elementary expansions of the finite functions $d^{-s(z)}$ and $(1-z)^{-5}$, with the factor $\lambda^j$ on coefficient $j$.

For each $n\ge10^{1200}$, round every real and imaginary component of $P$ toward zero to denominator $(n+1)^3$. Its weighted coefficient cost decreases under rounding and was at most $M^2(D+1)^3<10^{1200}$ beforehand. Thus the zero-padded rounded polynomial belongs to the exact finite grid. The extra uniform norm is at most $2(D+1)/(n+1)^3$.

Finally, by the [explicit canonical row estimate](CANONICAL-STAGE.md), every entry through $m=2n+1$ has norm error at most $4^{-m}$. The extra visible perturbation is at most $\sqrt{m+1}\,M(D+1)4^{-m}$. Add the original row correction $2\sqrt{(n+1)(m+1)}\,4^{-m}+32/(9\sqrt{n+1})$ and square the resulting norm. The exact rational [verification](certify_cofinal.py) starts from the sharper physical period receipt and rounds every displayed contribution outward. It uses $4^{2n+1}\ge(n+1)^2$ to bound errors uniformly on the specified tail of stages. [Numerical receipt](cofinal-grid-receipt.json)

## Transfer with a variable precision

The same argument applies to each fixed finite Dirichlet trial for this character, with its own explicit coefficient mass and largest norm. For every $\theta<1/117$ it gives
\[
 \sqrt{U_n}\le\|1-pL_\chi\|_{L^2(d\mu)}+O_{p,\theta}(n^{-\theta}).
\]
For $0<\theta<1/117$ take $9\theta<a<1/13$, $\tau=n^{-a}$ and $T=\tau^{-4/9}$. The central and high-frequency errors are $O_p(\tau^{1/9})$. Truncating $H((1-\tau)z)$ at $D=\lceil C\tau^{-1}\log n\rceil$ with sufficiently large $C$ makes the uniform truncation error $O_p(n^{-1})$. The grid cost is $O_p(\tau^{-13}\log^3 n)=o(n)$, and the rounding, row and original-grid errors are of smaller order. This rate compares with each supplied trial's genuine norm. A resulting rate to zero would need a family of sufficiently good trials with controlled coefficients.
