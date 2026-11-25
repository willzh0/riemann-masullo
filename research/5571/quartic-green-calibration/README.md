# A bound at all heights for the quartic Green mass

For Masullo, Theorem 12.5.1.1, pp. 519–520, consider the primitive quartic Dirichlet character modulo five with $\chi(2)=i$. Count each nontrivial zero $\rho=\beta+i\gamma$ with its multiplicity $m_\rho$. The nonnegative scalar in the project's critical-line integral satisfies

$$
0\le G_\chi=\sum_{\beta>1/2}m_\rho\log\frac{|\rho+1|}{|2-\rho|}
<2.09879293\cdot10^{-7}.
$$

The sum includes zeros of every height. Vanishing of this mass would exclude all right-hand zeros for this character. Each summand can be arbitrarily small when the ordinate is large. [All-field Green identity in #7696](https://github.com/mccorvie/riemann-masullo/pull/7696)

## From the verified height to a bound for the entire sum

Platt verified the critical line through $H=20{,}000{,}000$ for both primitive quartic characters modulo five. This gives both signs of the ordinate for the specified character. For a remaining right-hand zero,
$$
0<\log\frac{|\rho+1|}{|2-\rho|}
=\frac12\log\!\left(1+\frac{6(\beta-1/2)}{(2-\beta)^2+\gamma^2}\right)
\le\frac{3}{2\gamma^2}.
$$
The functional equation and complex conjugation pair $\beta+i\gamma$ with $1-\beta+i\gamma$ for the **same character** and with equal multiplicities. Consequently the sum of $m_\rho/\gamma^2$ on the right half above $H$ uses at most half the two-sided tail over all nontrivial zeros. Zeros on the critical line can contribute to the latter tail. [Platt, Theorem 7.1, p. 14](https://arxiv.org/pdf/1305.3087#page=14) · [Bennett, Martin, O'Bryant and Rechnitzer, functional equation (2.1)](https://arxiv.org/pdf/2005.02989#page=4)

Write $L=\log(5H/(2\pi))$, $\ell=\log(5(H+2)/(2\pi))$, $E=0.22737\ell+2\log(1+\ell)-1/2$, and $d=0.22737+2/(1+\ell)$. Apply the two-sided zero-count theorem to $N(t,\chi)$, including multiplicities and both signs of the ordinate. Stieltjes integration on $(H,\infty)$ against $t^{-2}$ gives
$$
\sum_{|\gamma|>H}m_\rho\,\gamma^{-2}
 \le \frac{L+1}{\pi H}+\frac{2E+d/2}{H^2}
 <2.7983905732\cdot10^{-7}.
$$
Indeed the continuous main term has derivative $\log(5t/(2\pi))/\pi$. The boundary error has size at most $E/H^2$. The integral error has size at most $E/H^2+d/(2H^2)$, since the error envelope satisfies $E(t)\le E+d\log(t/H)$ for $t\ge H$. This formula also covers a zero at the verified endpoint. Multiplying the tail bound by $3/4$ gives the stated upper bound for $G_\chi$. [Zero-count theorem 1.1](https://arxiv.org/pdf/2005.02989#page=2) · [Quartic fourth-power tail calculation](https://github.com/willzh0/riemann-masullo/tree/0b8885bf2d52f23cd32dafff1a77680db475bbd0/research/5571/quartic-fixed-prime-prefix)

## The whole-line logarithmic integral

Set $P(t)=(3/2)/(\pi((3/2)^2+t^2))$. The ordinary finite $L$-function has no pole for this character. The half-plane Green identity gives
$$
\int_{\mathbb R}P(t)\log|L(1/2+it,\chi)|\,dt=\log|L(2,\chi)|+G_\chi .
$$
In particular
$$
-0.030764312543<
\int_{\mathbb R}P(t)\log|L(1/2+it,\chi)|\,dt
<-0.030764102663 .
$$
As another consequence, the squared Hardy-space distance in #7707 is $1-e^{-2G_\chi}<4.1975850\cdot10^{-7}$. These bounds apply to the limiting quantities for this character and its conjugate. Bounding a particular finite ideal table still requires its own approximation error. [Boundary integral in #7696](https://github.com/mccorvie/riemann-masullo/pull/7696) · [Hardy distance in #7707](https://github.com/mccorvie/riemann-masullo/pull/7707)

Run `uv run --no-project --with python-flint==0.9.0 python check_green.py --bits 128` in this directory and repeat at 192 bits. The verifier computes $\log|L(2,\chi)|$ by rigorous complex interval arithmetic. It independently sums complete periods of $\chi(n)/n^2$ through $N=10^6$. At a multiple of five, the absolute value of every subsequent partial sum of the character is at most $\sqrt2$. Partial summation bounds the omitted complex tail by $\sqrt2/(N+1)^2$. The direct value lies inside that elementary enclosure. For the conjugate character the modulus at two agrees and reflection of the integral variable preserves its value. [Verification script](check_green.py) · [128-bit output](green-128.json) · [192-bit output](green-192.json)
