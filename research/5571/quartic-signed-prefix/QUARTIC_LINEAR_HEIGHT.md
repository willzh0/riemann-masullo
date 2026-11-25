# A finite-height bound for the quartic prime statistic with a sharp annulus

Let $\chi(2)=i$ modulo $5$, $\eta=\chi^2$, $K(u)=\int_1^2(1-uv)_+\,dv$, and $Q(x)=\sum_p\chi(p)\log p\,K(p/x)$. Put

$$
h(s)=\int_1^2v^{-s}\,dv=\frac{2^{1-s}-1}{1-s},
\quad M(s)=\frac{h(s)}{s(s+1)},\qquad
R_H(x)=-\sum_{\rho_\chi:\,|\Im\rho_\chi|>H} M(\rho_\chi)x^{\rho_\chi}.
$$

Zeros are counted with multiplicity. For $H=20{,}000{,}000$, and also for every $e^{16}\le H\le20{,}000{,}000$, every real $x\ge1$ satisfies

$$
\boxed{\ |\Re(Q(x)-R_H(x))|\le\frac58\sqrt{x}\ },\qquad
\boxed{\ |\Re Q(x)|\le\frac58\sqrt{x}+
                \frac{x\log H}{6H^2}\ }.                         \tag{1}
$$

Only the indicated high zeros of the quartic character have been subtracted in the first inequality. Its right side improves to $0.226\sqrt x$ for $x\ge10^8$ and to $0.181\sqrt x$ for $x\ge10^{12}$. In particular it supplies a pointwise remainder for a separate cumulative bound on $R_H$. Mlyle established the triangular Perron formula for the same quartic character, checked its endpoint constants, and bounded proper powers in the unsmoothed triangular statistic. The present calculation applies the annular multiplier, subtracts the entire even-power series before bounding any proper powers, and uses the extra inverse ordinate in the high-zero tail. [Mlyle's quartic calculation](https://github.com/mlyle/riemann-masullo/blob/3f90b6c75f2e36f52c2c9cb427155a556bcee9d8/research/5571/quartic-mod-five-deficit/README.md).

## The exact prime-power and gamma terms

Write $A_\xi=-L'/L(\cdot,\xi)$. For $\Re s>1$, the Euler series of $A_\chi(s)-A_\eta(2s)$ contains exactly the odd powers of each prime with coefficient $\chi(p)^k\log p$. Both characters are primitive of conductor five. All powers of $5$ have coefficient zero in both series. For odd $k$, $\Re\chi(p)^k=\Re\chi(p)$, so the remaining proper powers contribute

$$
 O_{\rm odd}(x)=\sum_{p\equiv1,4\ (5)}\Re\chi(p)\log p
       \sum_{k=3,5,\ldots}K(p^k/x).
$$

The Mellin transform of $K$ is $M$. Shifting the Mellin integral of $[A_\chi(s)-A_\eta(2s)]M(s)x^s$ gives, for $x>2$,

$$
\Re Q(x)= -\Re\sum_{\rho_\chi}M(\rho_\chi)x^{\rho_\chi}
 +\frac12\sum_{\rho_\eta}M(\rho_\eta/2)x^{\rho_\eta/2}
 +G(x)-O_{\rm odd}(x).                                          \tag{2}
$$

The second sum is real by conjugation. Its coefficient is $+1/2$ because the pole of $A_\eta(2s)$ at $s=\rho_\eta/2$ has residue $-1/2$ per zero. Both series converge absolutely. To justify the shift, choose horizontal heights avoiding the ordinates of the quartic and halved quadratic zeros by $\gg1/\log T$, using the unit-interval zero count. The local partial-fraction estimate for each logarithmic derivative is then $O(\log^2 T)$ on fixed vertical strips, where $M(s)\ll(1+|t|)^{-3}$ there. Shift left on half-integer real parts, avoiding the two sets of trivial zeros. The functional equations and Stirling's formula bound the logarithmic derivatives there by $O(\log(2+|s|))$. The exponential factor in $h(s)x^s$ tends to zero on the left for $x>2$. [Koukoulopoulos, Lemma 11.4 and Theorem 11.3](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf).

For a real argument $r$ write $\ell_\xi(r)=\Re\!\big(L'(r,\xi)/L(r,\xi)\big)$. Define

$$
 a=\log2-\ell_\chi(1)+\ell_\eta(1),\qquad
 b=\frac98-\log2-\frac32\{-\tfrac12+\ell_\chi(2)-\ell_\eta(3)\}.
$$

The elementary contribution is exactly

$$
 G(x)=\tfrac12\log x-a+\frac{\tfrac34\log x+b}{x}+T(x),\qquad
 T(x)=\frac12\sum_{k=2}^\infty
   \frac{(-1)^kh(-k)x^{-k}}{k(k-1)}.                            \tag{3}
$$

Here $a=1.3629621218\ldots$ and $b=1.3015022840\ldots$. To check the poles, the functional equation gives

$$
 A_\xi(s)=\log(5/\pi)+\tfrac12\psi((s+a_\xi)/2)
            +\tfrac12\psi((1-s+a_\xi)/2)
            +\frac{L'}L(1-s,\bar\xi),
$$

where $a_\chi=1,\ a_\eta=0$. At zero, the difference of the two logarithmic derivatives has polar term $1/(2s)$ and real constant $\ell_\chi(1)-\ell_\eta(1)$. The expansion of $M(s)x^s$ there is $1/s+\log x-2\log2+O(s)$. This gives the first two terms of (3).

At $-1$ their difference has polar term $-1/[2(s+1)]$ and real finite part $C=-1/2+\ell_\chi(2)-\ell_\eta(3)$. Since $h(-1)=3/2,\ h'(-1)=3/4-2\log2$, the product residue is $x^{-1}[(h(-1)(1+\log x)+h'(-1))/2-h(-1)C]$. At $-k$, $k\ge2$, the even quadratic contributes $+1/2$ at every integer, and the odd quartic contributes $-1$ at odd integers. This yields the alternating series $T$. For $x\ge2$, its absolute term sizes decrease by the integral formula for $h$, so $0\le T(x)\le7/(12x^2)$.

## Bounds for all other terms in (2)

For each primitive character $\xi$ here, put $B_\xi=2\Re\!\big(\Lambda_\xi'(1)/\Lambda_\xi(1)\big)$. The completed Hadamard identity and the same-ordinate reflection $\rho\mapsto1-\bar\rho$ give $B_\xi=2\sum_\rho\Re(1/(1-\rho))$, a sum of positive terms. On the critical line a term equals $1/|\rho|^2$. The gamma factors give

$$
 B_\chi=\log(5/\pi)-\gamma_E+2\ell_\chi(1)<0.203222,\quad
 B_\eta=\log(5/\pi)-\gamma_E-2\log2+2\ell_\eta(1)<0.156557.
$$

Platt's Theorem 7.1 applies to $\chi,\bar\chi,\eta$ through original ordinate $20{,}000{,}000$. In his Theorem 3.2 the count uses $|\Im\rho|\le t_0$ including both signs. The corresponding disk in ordinate for the moved point $\rho_\eta/2$ reaches $10{,}000{,}000$. No symmetry in the sign of the quartic ordinate is required. The low quartic contribution costs $h(1/2)B_\chi\sqrt x<0.16836\sqrt x$. The low quadratic contribution is at most $2h(1/4)B_\eta x^{1/4}<0.28465 x^{1/4}$, since $1/(2|(\rho/2)(1+\rho/2)|)\le2/|\rho|^2$. [Platt, Theorem 7.1](https://arxiv.org/pdf/1305.3087#page=14) · [Platt, Theorem 3.2](https://arxiv.org/pdf/1305.3087#page=5) · [Hadamard identity and zero sums in Rubinstein and Sarnak, §4.3](https://www.math.uwaterloo.ca/~mrubinst/publications/Chebyshev.pdf).

Let $N_\xi(t)$ count zeros at both signs up to height $t$. Bennett, Martin, O'Bryant and Rechnitzer give
$$
 \left|N_\xi(t)-\frac t\pi\log\frac{5t}{2\pi e}
                     +\frac{\xi(-1)}4\right|\le \log t
 \qquad(t\ge e^{16}).
$$
Indeed their upper bound is $0.22737 u+2\log(1+u)-0.5$ with $u=\log(5(t+2)/(2\pi))\le\log t$. At $\log t=16$ the inequality is strict, and the derivative of the bound in $\log t$ is smaller than one thereafter. Stieltjes integration gives, for either character,

$$
 \sum_{|\Im\rho|>H}|\Im\rho|^{-3}\le U_H=
 \frac{\log(5H/(2\pi))+1/2}{2\pi H^2}
 +\frac{2\log H+1/3}{H^3}<\frac{\log H}{6H^2}.                 \tag{4}
$$

The constant parity term cancels between $-N_\xi(H)/H^3$ and $3\int_H^\infty N_\xi(t)t^{-4}dt$. The normalized upper $U_H H^2/\log H$ is below $0.161857$ for $H\ge e^{16}$, and $U_{20{,}000{,}000}<6.8\cdot10^{-15}$. [Bennett, Martin, O'Bryant and Rechnitzer, Theorem 1.1](https://doi.org/10.1090/mcom/3599).

The high quadratic contribution is at most $12U_H\sqrt x$, because $|h(\rho/2)|\le6/|\gamma|$ and the denominator with its factor $1/2$ costs at most $2/\gamma^2$. For the quartic tail, $|M(\rho)|\le(1+2^{1-\beta})/|\gamma|^3$. Average the numerator times $x^\beta$ over the reflected pair of the same ordinate. Convexity at $\beta=0,1$ gives $x^\beta+x^{1-\beta}\le x+1$ and $2(x/2)^\beta+2(x/2)^{1-\beta}\le x+2$, so

$$
                  |R_H(x)|\le (x+3/2)\,U_H\qquad(x\ge1).       \tag{5}
$$

For the odd proper powers, the least prime with nonzero real character value is $11$. Hence $O_{\rm odd}(x)=0$ on $1\le x\le11^3$. For $k=3+2j$ use $p^k\ge p^3 11^{2j}$ and the monotonicity of $K$. The elementary inequality $\vartheta(u)\le(\log4)u$ and partial summation give

$$
 \sum_p(\log p)K((p/U)^3)
 \le (\log4)U\int_0^1K(v^3)\,dv
 =(\log4)U\,\tfrac34 h(1/3).
$$

Summing the geometric series over $j$ yields

$$
 |O_{\rm odd}(x)|\le
 \frac{(\log4)(9/8)(2^{2/3}-1)}{1-11^{-2/3}}\,x^{1/3}
 <1.1483\,x^{1/3}.                                               \tag{6}
$$

For completeness, the theta bound follows by induction on integers. The product of the primes in $(m,2m]$ divides $\binom{2m}{m}<2^{2m}$. The product in $(m+1,2m+1]$ divides $\binom{2m+1}{m}\le2^{2m}$, since the two middle binomial coefficients agree. This proves the bound for even and odd integer arguments using the induction hypothesis, and taking floors gives the real version.

## The numerical inequalities

For $1\le x<11$ the actual real prime statistic vanishes. Formula (5) bounds its difference from the isolated high tail by less than $10^{-11}\sqrt x$. For $11\le x<1331$, the odd proper powers vanish. The supremum of the positive part of $(\tfrac12\log x-a)/\sqrt x$ is $e^{-1-a}$, and the greatest negative magnitude in this range is at $11$. The remaining upper bounds from (3), divided by $\sqrt x$, decrease from $11$. Adding the low quartic, all quadratic and elementary bounds costs less than $0.506\sqrt x$.

For $x\ge1331$, the bound for $|G(x)|/\sqrt x$ decreases from its value at $1331$, because $\log(1331)>2+2a$ and all the indicated terms are positive before taking the maximum for $T$. The quadratic low and odd proper-power bounds relative to $\sqrt x$ also decrease. The combined coefficient at $1331$, with the quadratic high error for every allowed $H$, is below $0.623060$. This proves the first part of (1). There is room to absorb $(3/2)U_H$ into $5\sqrt x/8$ when adding (5), yielding the second part. For $x<11$ it holds directly.

The same decreasing envelope evaluated at $10^8$ and $10^{12}$ is below $0.226$ and $0.181$, respectively. For example, at $10^{12}$ the low quartic contribution is below $0.16836$, the low quadratic below $0.000285$, the odd powers below $0.011483$, and the elementary terms below $0.000013$, in units of $\sqrt x$. The high quadratic error is below $12\cdot10^{-12}$ in these units. These savings retain the entire primary high tail $R_H$ separately.

Run the accompanying interval ledger with Python and python-flint 0.8.0.

    python verify_quartic_linear_height.py

It checks the four logarithmic derivatives by deflated Hurwitz zeta jets, the zero masses, both gamma constants, the uniform height inequality, and the two spatial ranges at 128 and 192 bits.
