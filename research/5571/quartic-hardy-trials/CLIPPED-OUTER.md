# Quantitative accuracy of the original Hardy prediction grid

For the primitive quartic character of conductor five with $\chi(2)=i$, take the actual [#7707 finite ideal grid](https://github.com/mccorvie/riemann-masullo/pull/7707) at disk exponent five. The written proof below gives, simultaneously at **every** $n\ge2^{600000}$,
\[
 0\le U_n-(1-e^{-2G_\chi})<10^{-19}.
\]
This accuracy estimate uses the period of the character, its Euler product on the line at two and the [explicit coefficient error of its canonical ideal row](CANONICAL-STAGE.md). Including the independently established $G_\chi<2.09879293\cdot10^{-7}$ from verified zeros and their inverse-square tail then gives
\[
 U_n<4.1975849790140\cdot 10^{-7},\qquad
 -\tfrac12\log(1-U_n)<2.0987929300002\cdot10^{-7}
 \qquad(n\ge2^{600000}).
\]
The bound refers to the original finite arithmetic minima at the stated indices. Their pointwise values were bounded by an admissible function and a rounding argument. The finite-conductor zero verification is used only to specialize the limit on the right of the accuracy estimate. The open assertion asks for upper bounds arbitrarily close to **zero**. [Independent verified-height Green estimate](https://github.com/willzh0/riemann-masullo/tree/da8d5a8b3252c16120606b0b513d445e88cfbd0f/research/5571/quartic-green-calibration) · [Outward rational receipt](clipped-outer-receipt.json)

## A bounded analytic predictor from a clipped modulus

Use disk Haar probability and let $F$ be bounded by one and analytic in the unit disk, continuous on its closure, nonzero at zero, with Lipschitz boundary values of constant $L_0$. Assume $\log|F|$ is integrable. Denote $J=\int\log|F|-\log|F(0)|$ and $d^2=1-e^{-2J}$. Szegő's theorem gives this squared distance from one to the closed span of the polynomial multiples of $F$. For the normalized ordinary Hecke disk function the boundary identity of #7696 gives $J=G_\chi$. For the quartic $F=(s+1)^{-5}L_\chi(s)$ and $L_0\le16/9$. [Szegő (1920)](https://doi.org/10.1007/BF01199955) · [Hecke boundary identity](https://github.com/mccorvie/riemann-masullo/pull/7696)

For $H>0$ write $f=\log\max(|F|,e^{-H})$, $e_H=\int(f-\log|F|)$. Values at its null set of zeros do not affect the integral. Then $-H\le f\le0$ and the circle Lipschitz constant of $f$ is at most $L_0e^H$. For any $\eta>0$, take a Fejér mean $v$ with $\|v-f\|_\infty\le\eta$. This preserves its mean and Lipschitz bound. In fact the order-$M$ Fejér kernel with coefficients $1-|j|/M$ has Haar mean one and integrates $|1-e^{i\theta}|^2$ to $2/M$, so $M\ge2L_0^2e^{2H}/\eta^2$ suffices. If $v$ has coefficients $v_j$, set
\[
 P(z)=v_0+\eta+2\sum_{j>0}v_j z^j,\quad O(z)=e^{P(z)},\quad
 \Phi=F/O,\quad q=\overline{\Phi(0)}/O .
\]
The real part of $P$ on the circle is $v+\eta\ge f\ge\log|F|$. The maximum principle gives $|\Phi|\le1$, $|q|\le e^H$. Finite Parseval gives $\|P'\|_{H^2}^2=2\|\partial_\theta v\|_{L^2}^2\le2L_0^2e^{2H}$. Hence $\|q'\|_{H^2}\le\sqrt2 L_0e^{2H}$. The mean of $\Phi$ is its value at zero, giving
\[
 \|1-qF\|_2^2
 =1-2|\Phi(0)|^2+|\Phi(0)|^2\|\Phi\|_2^2
 \le 1-e^{-2(J+e_H+\eta)}\le d^2+2(e_H+\eta).
\]
This finite construction avoids selecting an inner factor. For $L_0\le16/9$ the actual weighted Taylor coefficient energy satisfies
\[
 \sum_{j\ge0}(j+1)^2|q_j|^2\le2\|q\|_2^2+2\|q'\|_2^2\le20e^{4H}.
\]

If $20 e^{4H}\le n+1$, truncate at degree $n$ and round real and imaginary parts toward zero at the canonical denominator $(n+1)^3$. This decreases the weighted coefficient cost. Its true $H^2$ truncation error is at most $1/\sqrt{n+1}$ and the uniform rounding error is at most $2/(n+1)^2$. The rounded trial has coefficient $\ell^1$ norm at most $\sqrt{2(n+1)}$ by Cauchy–Schwarz. If the original row through $m=2n+1$ has entry errors at most $4^{-m}$, its visible residual is bounded by the true residual plus the preceding errors and $2(n+1)4^{-m}$. Add the original formula's own $2\sqrt{(n+1)(m+1)}4^{-m}+32/(9\sqrt{n+1})$. The combined correction to the norm is at most $12/\sqrt n$ because $4^{2n+1}\ge(n+1)^2$. The initial squared residual is at most one, so a norm error $\Delta$ costs at most $2\Delta+\Delta^2$ in the squared bound. The reverse inequality $d^2\le U_n$ is the grid's weighted-coefficient tail inequality under this same verified row error.

## Explicit quartic clipping at all heights

For integer $j$, consider $I_j=[j-1/2,j+1/2]$ and the disk of radius $19/10$ centered at $2+ij$. The [periodic Abel formula](FINITE-COEFFICIENTS.md) gives the upper $B_j=50(|j|+2)$ for $|L_\chi|$ on this disk, since $\Re s\ge1/10$. At its center the Euler product gives $|L_\chi(2+ij)|\ge1/\zeta(2)>1/2$. Put $A_j=\log(2B_j)$. Jensen's disk inequality at $19/10$ bounds the number of zeros of modulus at most $9/5$ in centered coordinates by $20A_j$, with multiplicity, since $\log(19/18)>1/20$. The critical segment has distance at most $\sqrt{5/2}<8/5$ from the disk center.

Choose a radius $R$ between $7/4$ and $9/5$ meeting no zero. Divide out its finite Blaschke product with multiplicities. The remaining function $h$ has modulus at most $B_j$ and $|h(0)|>1/2$. The nonnegative harmonic function $\log(B_j/|h|)$ is at most $24A_j$ on the segment by the disk Harnack inequality. In centered coordinates, each Blaschke factor for a zero $a$ has modulus at least $|w-a|/(R+8/5)\ge|w-a|/4$. If $y>0$ and $\log^-|L_\chi|>24A_j+y$, some zero lies within $4e^{-y/(20A_j)}$ of the point. When the disk has no zero this exceptional set is empty. Covering by its intervals gives a length bound of $160A_j e^{-y/(20A_j)}$.

On $I_j$, the exponent-five normalization adds $5\log|3/2+it|\le5A_j$ to $-\log|L_\chi|$. Thus with $Y=-\log|F|$ the local integral of $Y$ is at most $29A_j+3200 A_j^2\le3300 A_j^2$. For $H\ge29A_j$ the sharper upper for $\int_{I_j}(Y-H)_+\,dt$ is
\[
 3200 A_j^2 \exp\big(-(H-29A_j)/(20A_j)\big).
\]
These bounds follow by integrating the length estimate in $y$. Haar probability here is the Cauchy measure $3\,dt/(2\pi((3/2)^2+t^2))$. Its density is at most $1$ on $I_0$ and at most $2/j^2$ on $I_j$ for $j\ne0$, so the sum of the interval suprema is at most nine.

Take $H=100000$ and $J_0=2^{96}$. On the blocks $|j|\le J_0$, one has $A_j\le\log(300J_0)<73$, so their total clipped error is at most $9\cdot3200\cdot73^2 e^{-67}$. The remaining blocks cost at most
\[
 13200\sum_{j>J_0}\log^2(300j)/j^2
 \le13200(73^2+146+2)/J_0
\]
by integration of a decreasing function. The [rational verifier](certify_clipped_outer.py) gives $e_H<2.839\cdot10^{-21}$. Take $\eta=10^{-24}$. For $n\ge2^{600000}$ one has $20e^{4H}\le n$ and $12/\sqrt n<10^{-24}$. The [canonical row error](CANONICAL-STAGE.md) applies throughout this range. Substitution proves the stated accuracy. The posted $G_\chi$ enclosure then gives the two numerical bounds using the alternating Taylor upper for $1-e^{-2G_\chi}$ and an outward logarithm series.

## Every fixed number field and normalized character

For the all-field canonical grid, fix a sufficiently large exponent $N$ as in #7707. It gives $\|F\|_\infty\le1$, $L_0\le16/9$ and its original row error eventually. On the critical line, where the pole-clearing factor has unit modulus, the normalized $-\log|F|$ differs from $-\log|L_\chi|$ by $N\log|3/2+it|$. The integrated tail for the ordinary logarithm from [#7709](https://github.com/mccorvie/riemann-masullo/pull/7709) is $O_\chi(e^{-c_\chi\sqrt H})$. The added height logarithm has an exponentially decaying integrated tail under the Cauchy probability. The elementary inequality $(a+b-H)_+\le(a-H/2)_++(b-H/2)_+$ transfers the bound to $e_H$. Set $H=\log(n+1)/8$ and $\eta=(n+1)^{-1}$. The preceding construction yields
\[
 0\le U_n-(1-e^{-2G_\chi})\le C_{\chi,N}e^{-c_{\chi,N}\sqrt{\log(n+1)}}
 \quad\hbox{for all sufficiently large } n .
\]
Since $1-e^{-2G_\chi}<1$, the same rate, with fixed-character constants, applies to the logarithmic Green upper $-\log(1-U_n)/2-G_\chi$. This rate proof is mathematical. The general constants and the onset are existential; the quartic constants above are independently explicit. Finding a cofinal arithmetic upper that forces $G_\chi=0$ remains open.
