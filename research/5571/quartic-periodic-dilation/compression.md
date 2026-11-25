# Removing a growing initial segment of the dilators

Let $\chi$ be the primitive quartic character modulo five with $\chi(2)=i$, let $S_\chi(x)=\sum_p\chi(p)(x-p)_+\log p$, and take the real cutoff $0\le W\le1$ of mlyle’s theorem, equal to one on $[0,1]$ and zero on $[2,\infty)$. Write $a=21/100$ and $\Phi(L)=L^{3/5}(\log L)^{-1/5}$. His pointwise prime-dilation estimate gives a fixed $c>0$ such that
$$
 B_W(t)=\sum_{n\ge1}W(n/t^a)\chi(n)n S_\chi(t/n)
       \ll_{\chi,W} t^{3/2}e^{-c\Phi(\log t)}
$$
at every sufficiently large real $t$. The constants below refer to this individual character and cutoff. [Mlyle’s power-short estimate and periodic identity](https://github.com/mlyle/riemann-masullo/blob/c2eb094fffef928fdb72c2e180c255092e819347/research/5571/fourth-power-prime-curvature/spectral-interpolation-periodic-prime-convolution.md) · [Formal full-dilation upper bound](https://github.com/mccorvie/riemann-masullo/pull/7668)

For any fixed $0<\kappa<2c$, put $Y=\lfloor\exp(\kappa\Phi(\log x))\rfloor$. For every $c'<c-\kappa/2$ with $c'>0$, the actual short sums satisfy, at **every** sufficiently large $x$,
$$
 S_\chi(x)+
 \sum_{Y<m\le2x^aY^{1-a}}
        b_{x,Y}(m)\,\chi(m)m\,S_\chi(x/m)
 \ \ll_{\chi,W,\kappa,c'} x^{3/2}e^{-c'\Phi(\log x)},
 \qquad
 b_{x,Y}(m)=\sum_{\substack{d\mid m\\d\le Y}}\mu(d)
     W\!\left(\frac{m}{x^a d^{\,1-a}}\right).
$$
Here the inequality bounds the complex modulus. At $x=j^4$ all remaining prime cutoffs are at most $j^4/(Y+1)$, and there are at most $j^{0.84+o(1)}$ possible dilator indices. This reduces the largest prime cutoff by a factor growing like $\exp(\kappa\Phi(\log(j^4)))$. The estimate applies to each prescribed sample, including phases selected separately at each $j$.

Indeed, multiply $B_W(x/d)$ by $\mu(d)\chi(d)d$ and sum for $d\le Y$. Grouping $m=dn$ gives the displayed coefficient exactly. If $1\le m\le Y\le x^a$, every weight in $b_{x,Y}(m)$ is one. Thus $b_{x,Y}(1)=1$ and all others in this range vanish by the divisor identity for $\mu$. If $m>2x^aY^{1-a}$ all weights vanish. On the measured side,
$$
 \sum_{d\le Y}d|B_W(x/d)|
 \ll x^{3/2}\sum_{d\le Y}d^{-1/2}
   e^{-c\Phi(\log(x/d))}
 \le x^{3/2}\exp\{[-c+\kappa/2+o(1)]\Phi(\log x)\}.
$$
The estimate is uniform over $d\le Y$ because $\log Y=o(\log x)$, and $\sum_{d\le Y}d^{-1/2}\le2\sqrt{Y}$. The positive part of a real projection is $1$-Lipschitz, so for $Z(x)$ denoting the residual sum over $m>Y$ one has, for any phase $\theta$,
$$
 \big|[-\Re(e^{-i\theta}S_\chi(x))]_+
       -[\Re(e^{-i\theta}Z(x))]_+\big|
 \ll x^{3/2}e^{-c'\Phi(\log x)} .
$$
At $x=j^4$, summing over $j\le J$ gives $O(J^7e^{-c''\Phi(\log J)})$ for some $c''>0$, by a fixed fractional-power split or eventual monotonicity. The sign correlations among the remaining prime sums still have to be estimated.

## Forced coefficients and the loss in separate estimates

This elimination has a cost even when the filter is optimized. Let $\sum_{d\le Y}a_d\chi(d)dB_W(x/d)$ be any finite linear filter with $a_1=1$ that eliminates each individual dilator $2\le m\le Y$ for which $5\nmid m$. For those $m$, the exact coefficient is $\sum_{d\mid m}a_d$. Divisor inversion forces $a_d=\mu(d)$ for every $d\le Y$ coprime to five. At the critical power $t^{3/2}$ the exact normalized operator norm for *independently bounded complex input errors* is
$$
 \sum_{\substack{d\le Y\\5\nmid d}}\frac{|\mu(d)|}{\sqrt d}
 \sim\frac{10}{\pi^2}\sqrt Y .
$$
Indeed the density of squarefree integers coprime to five is $(6/\pi^2)\,5/6=5/\pi^2$ by the square-divisor identity. Partial summation gives the stated asymptotic. Choosing the input phases to align gives equality for the norm even if the final result is projected onto one prescribed real direction. Thus treating the measured errors only by their separate envelopes entails this loss. For $Y=x^\delta$, $\delta>0$, it would convert the available stretched-log saving into a power loss.

There is an independent constraint on treating the surviving prime sums as unrelated. For every prime $Y<p\le x^a$ other than five, its only eligible divisor is 1, so $b_{x,Y}(p)=1$ for **every** such filter. Normalize each shorter input by $(x/p)^{3/2}$ and the output by $x^{3/2}$. The squared coefficient norm of these prime dilators alone is
$$
 \sum_{Y<p\le x^a}\frac1p
    =\log\log(x^a)-\log\log Y+o(1)
    =(2/5+o(1))\log\log x .
$$
Mertens’ prime reciprocal formula proves the first equality. The omitted $p=5$ is eventually below $Y$. In particular an independent mean-zero, unit-variance model on these normalized inputs has a diverging output variance. This calculation uses the actual coefficients of the fixed quartic filter and no conjecture about zeros. Signed dependence between the genuine shorter samples is essential to any bounded critical-scale inversion on this norm.

There is a power-saving version if a fixed strip is known for the **quadratic** companion. Write $\Theta_\eta=\sup_{\rho:L(\rho,\chi^2)=0}\Re\rho$ over nontrivial zeros. The [full physical spectrum](secondary-spectrum.md) and mlyle’s $O_\nu(t^{37/25+\nu})$ truncation error give
$$
 |B_W(t)|\ll_\nu t^{A+\nu},
 \qquad A=\max(37/25,\,1+\Theta_\eta/2).
$$
The other spectral channel has exponent at most $1+1/3<37/25$. If $A<3/2$, replace $Y$ by $x^\delta$ for fixed $0<\delta<(3/2-A)/(2-A)$. The same proof gives $O_\nu(x^{A+(2-A)\delta+\nu})$ per sample, a strict saving over $x^{3/2}$. The remaining arguments are at most $x^{1-\delta}$. The condition $\Theta_\eta\le24/25$ permits every $\delta<1/26$. This corollary assumes a strip for $\eta$ and imposes no critical-line hypothesis on the quartic character.
