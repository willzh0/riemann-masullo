# A positive quartic theta kernel retaining one oriented critical frequency

For the character and the normalized actual Riesz sum $F$ of the accompanying note, write $a=\pi/5$ and

$$k(t)=2e^{3t/2}\sum_{n\ge1}n\chi(n)e^{-a n^2 e^{2t}}.$$

Its bilateral transform is $\Lambda(1/2+z,\chi)$, by the gamma integral and continuation. Odd-character Poisson summation gives $k(-t)=\varepsilon_\chi\overline{k(t)}$. The calibrated root number has its argument in $(0,\pi/4)$. [Functional equation and root-number calibration](https://github.com/willzh0/riemann-masullo/blob/53cac8a4461b84ad1d9c96ea2305f48e82ba4a31/PROOF.md).

For $t\ge0$, after dividing out the positive first term, the sum of absolute remaining terms is at most

$$\sum_{n\ge2}n e^{-3(n^2-1)/5}\le2e^{-9/5}+(3+5/6)e^{-24/5}<3/8.$$

Use the monotone integral for the terms starting at 4. The exponential Taylor polynomial gives $e^{9/5}>6,\ e^{24/5}>100$. Thus $|\arg k(t)|\le\arcsin(3/8)<\pi/8$ there, and the reflected equation puts the values for all real $t$ in a common sector of width strictly below $\pi/2$.

Let $K=k*\bar k$, where the bar is pointwise complex conjugation. Substitution $u\leftrightarrow t-u$ makes $K$ real. The sector inequality gives $K(t)\ge c(|k|*|k|)(t)>0$ for one $c>0$. Its transform is $\Lambda(1/2+z,\chi)\Lambda(1/2+z,\bar\chi)$. It decays as $O(\exp(-c' e^{|t|}))$: each factor decays as $O(\exp(-c''e^{2|t|}))$, and at least one convolution argument has modulus at least $|t|/2$; save half the two exponential decays to control the remaining integral.

Choose a certified simple critical zero $1/2+i\gamma_0$ of this χ with no χ zero at the opposite ordinate. For example the closest negative bracket lies near $-4.13$, while the first positive bracket starts above $6.18$. Put

$$v(t)=e^{-i\gamma_0t}\int_t^\infty e^{i\gamma_0u} k(u)\,du,\qquad V=v*\bar k.$$

The zero moment gives the opposite left-tail representation. Then $|v|\ll|k|$: on the right, $|k(t)|\asymp e^{3t/2-a e^{2t}}$ and its positive comparison envelope integrates from $t$ to infinity to at most a constant multiple of its value at $t$; reflect the left tail. Thus $|V|\le C K$. Integration by parts yields

$$\widehat V(z)=
 \frac{\Lambda(1/2+z,\chi)\Lambda(1/2+z,\bar\chi)}{z-i\gamma_0}.$$

This transform retains just the indicated simple point of the χ divisor; $\widehat{\bar V}$ kills its whole divisor because the opposite ordinate is absent. For fixed sufficiently small $\delta>0$, all

$$K_\phi=K+\delta\Re(e^{i\phi}V)$$

are positive and satisfy $K/2\le K_\phi\le3K/2$. The genuine explicit formula with zero square drift gives, uniformly in the angle,

$$\int K_\phi(t)F(y+t)\,dt
    =d\,e^{i(\gamma_0 y+\phi)}+o(1),\qquad d\ne0.$$

Absolute summability and the tail bound justify termwise evaluation; for $y+t<0$ the actual prime sum vanishes while the absent spectral expansion grows at most $O(e^{|y+t|/2})$. Only the selected term survives. The coefficient is $-\delta\widehat V(i\gamma_0)/(2\rho_0(1+\rho_0))$. In particular the averaged vector can be steered into any prescribed direction at every sufficiently large terminal center solely by rotating an explicitly positive weight.

With $B=\log(C y)$, $C$ sufficiently large, the tails $|t|>B$ contribute $o(1)$, since $|F(y+t)|\ll e^{(y+|t|)/2}$ for $y+t\ge0$. Positivity gives a fixed disk in the convex hull of the continuous sampled vector on $[y-B,y+B]$. For physical fourth powers, the existing fixed-modulus signed short-interval PNT gives an $o(x^{3/2})$ interpolation error at real cutoffs between adjacent fourth powers: for $d=O(x^{3/4})$, split lengths at $x^{0.70}$, use the elementary integer bound below that threshold and the signed PNT above it, then integrate the signed counting error. This is the same argument for the real and imaginary parts of any fixed nonprincipal character. Consequently every late shell $[cJ/\sqrt{\log J},J]$ has the same qualitative disk conclusion for the actual $j^{-6}S(j^4)$. The fixed-ratio, cumulative theorem in the accompanying note uses a separate compact argument and only an elementary arithmetic interpolation bound. [Short-interval interpolation proof for the signed prime statistic](https://github.com/mlyle/riemann-masullo/blob/c2eb094fffef928fdb72c2e180c255092e819347/research/5571/fourth-power-prime-curvature/spectral-interpolation-mod4-shallow-runs.md).
