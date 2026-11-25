# Verified heights, tails over both signs, and Green sums

For $q>1$ put $A_q=75{,}000{,}000$ if $q$ is even and $A_q=37{,}500{,}000$ if $q$ is odd. Platt verified criticality of every primitive Dirichlet $L$-function of conductor $q\le400{,}000$ to height
$$
 H_q=\max(10^8/q,\,200+A_q/q).
$$
The parity in this formula refers to the modulus. The verification for the conjugate character covers negative ordinates for a complex character. The primitive census gives 29,565,923,837 nonprincipal characters and one additional character at conductor one. No conductor congruent to two modulo four supports a primitive character. The common lower height $H_*=1175/4$ follows by taking the largest odd and even conductors separately. At conductor one, Platt and Trudgian verified $\zeta$ to $H_\zeta=3{,}000{,}175{,}332{,}800$. [Platt, published Theorem 10.1, p. 3026](https://www.ams.org/journals/mcom/2016-85-302/S0025-5718-2016-03077-X/S0025-5718-2016-03077-X.pdf#page=18) · [Preprint Theorem 7.1 and census, p. 14](https://arxiv.org/pdf/1305.3087#page=14) · [Platt and Trudgian, Theorem 1](https://arxiv.org/pdf/2004.09765#page=2)

## Weighted tails over all nontrivial zeros

Let $S_k(\chi,H)=\sum_{|\gamma|>H}m_\rho|\gamma|^{-k}$ for $k>1$, counting both signs for the same character. Write $L=\log(qH/(2\pi))$, $\ell=\log(q(H+2)/(2\pi))$, $E=0.22737\ell+2\log(1+\ell)-1/2$ and $d=0.22737+2/(1+\ell)$. For $q>1$, $H\ge5/7$ and $\ell>1.567$,
$$
 S_k(\chi,H)\le T_k(q,H)
 =\frac{H^{1-k}}{\pi}\left(\frac L{k-1}+\frac1{(k-1)^2}\right)
    +H^{-k}\left(2E+\frac d k\right).
$$
Indeed the counting main term has derivative $\pi^{-1}\log(qt/(2\pi))$. Write the counting error as $R(t)$. Integration by parts on $(H,\infty)$ contributes $-H^{-k}R(H)+k\int_H^\infty R(t)t^{-k-1}\,dt$ beyond the integrated main term. The error envelope at $t\ge H$ is at most $E+d\log(t/H)$ by concavity in the logarithm and $(t+2)/(H+2)\le t/H$. This gives the formula, also at a zero ordinate by using right-continuous counts. [Bennett, Martin, O’Bryant and Rechnitzer, Theorem 1.1](https://arxiv.org/pdf/2005.02989#page=2)

At fixed $H$, $T_k(q,H)$ increases with $q$. In particular $2E+d/k$ has derivative $2(0.22737)+4/(1+\ell)-2/[k(1+\ell)^2]>0$ with respect to $\ell$. In each conductor interval and each parity use the verified height of the largest modulus $q_0$ in that parity. The historical height is nonincreasing within each parity, so the common bound in the interval is $T_k(q_0,H_{q_0})$. This argument compares actual tails before bounding them. At conductor one, the positive-ordinate counting error for $t>2\pi e$ is at most $0.28\log t$. Doubling for the two signs gives
$$
 S_k(1,H)\le
 \frac{H^{1-k}}{\pi}\left(\frac{\log(H/(2\pi))}{k-1}+\frac1{(k-1)^2}\right)
       +2H^{-k}\left(0.56\log H+\frac{0.28}{k}\right).
$$
Right limits of the published half-weight count give the required endpoint convention. For an arbitrary compact test whose Mellin coefficient satisfies $|M(\rho-1/2)|\le W_k|\gamma|^{-k}$ on this range, the absolute sum of the exterior terms in any positive half-width is bounded by $W_k S_k(\chi,H)$ whenever the row has been verified through $H$. [Brent, Platt and Trudgian, p. 2 and §2](https://arxiv.org/pdf/2009.13791#page=2)

## The Green sum and the critical-line mean

For a right-hand zero write $b=\beta-1/2>0$ and
$$
 g_b(x)=\frac12\log\frac{(3/2+b)^2+x^2}{(3/2-b)^2+x^2},\qquad
 G_\chi(t)=\sum_{\beta>1/2}m_\rho g_b(\gamma-t).
$$
In particular $g_b(\gamma)=\log(|1+\rho|/|2-\rho|)\le3b/\gamma^2$ by $\log(1+y)\le y$. The functional equation and conjugation pair right and left zeros at the same ordinate for the same character, with equal multiplicity. Thus $0\le G_\chi(0)\le(3/4)S_2(\chi,H)$ for a verified row. The right side bounds a whole-line integral as well. With $P(u)=(3/2)/[\pi((3/2)^2+u^2)]$, one has
$$
 \int_{\mathbb R}P(u)\log|L(1/2+iu,\chi)|\,du
 =\log|L(2,\chi)|-\mathbf1_{\chi=1}\log 2+G_\chi(0).
$$
The finite-height inputs above yield $G_\chi(0)<0.014579700030$ for odd $q>1$, $G_\chi(0)<0.011194778250$ for even $q$, and $G_\zeta(0)<2.219430385\cdot10^{-12}$. For $\zeta$, the critical-line integral itself lies in $(-0.195446878089201,-0.195446878086980)$. The small conductor-five bound is recorded separately. [Whole-line identity in the project](https://github.com/mccorvie/riemann-masullo/pull/7696) · [Quartic calculation](https://github.com/willzh0/riemann-masullo/tree/da8d5a8b3252c16120606b0b513d445e88cfbd0f/research/5571/quartic-green-calibration) · [Independent interval verifier](green_check.py)

## Two shifted means measure the height-weighted displacement

Put $a=4/5$ and suppose the row has been verified through $H\ge4$. If $0\le b\le1/2$ and $|\gamma|\ge4$, then
$$
 \frac{3b}{1+\gamma^2}\le\frac{g_b(\gamma-a)+g_b(\gamma+a)}2\le\frac{3b}{\gamma^2}.
$$
To see this, set $u=3b/(x^2+9/4+b^2)$. Then $g_b(x)=\operatorname{atanh}(u)$, between $u$ and $u/(1-u^2)$. For $|x|\ge3$, these inequalities place $g_b(x)$ between $3b/(x^2+5/2)$ and $3b/(x^2+2)$. For the upper bound use $9/4+b^2-9b^2/(x^2+9/4+b^2)\ge2$. Averaging $(x^2+c)^{-1}$ at $x=\gamma\pm a$ gives $(X+a^2+c)/[(X+a^2+c)^2-4a^2X]$, with $X=\gamma^2$. For $c=5/2$, comparison from below with $(1+X)^{-1}$ reduces to $(21/50)X-16799/2500\ge0$, which holds for $X\ge16$. For $c=2$, comparison from above with $X^{-1}$ reduces to $(2-3a^2)X+(2+a^2)^2\ge0$.

Consequently, with $D_\chi=\sum_{\beta>1/2}m_\rho b/(1+\gamma^2)$ and $\overline G_\chi=(G_\chi(a)+G_\chi(-a))/2$,
$$
 3D_\chi\le\overline G_\chi\le3(1+H^{-2})D_\chi.
$$
A test with $|M|\le W/(1+\gamma^2)$ at the zeros therefore has absolute exterior sum at most $2W\overline G_\chi/(3\alpha)$ at half-width $\alpha>0$, by pairing the two wings. With no shifted measurement, the unshifted bound for $0<\alpha\le1/2$ is
$$
 \frac{2W}{3\alpha}\left(1+\frac{5/4+\alpha^2}{1+H^2}\right)G_\chi(0).
$$
Indeed $g_b$ increases in $b$, and $g_\alpha(\gamma)\ge3\alpha/(\gamma^2+9/4+\alpha^2)$. For both shifted means the classical half-plane Poisson–Jensen formula at $2+it$ supplies the same identity with translated Poisson density and boundary center. The simple pole of $\zeta$ contributes $-\frac12\log((4+t^2)/(1+t^2))$ to the integral relative to $\log|\zeta(2+it)|+G_\zeta(t)$. At $t=\pm4/5$ the subtracted quantity is $\frac12\log(116/41)$. The interval receipts check this correction and the rational kernel comparisons independently. [Half-plane factorization, Burnol, Theorem 3.2](https://arxiv.org/pdf/math/0001013#page=14) · [128-bit Green receipts](green-128.json) · [192-bit Green receipts](green-192.json)
