# Quartic logarithmic dilations produce signed critical-size fourth-power data

Use the primitive quartic character $\chi\bmod5$ with $\chi(2)=i$. Put $S_\chi(x)=\sum_p\chi(p)(x-p)_+\log p$. Fix the smooth cutoff $W$ of mlyle’s periodic convolution, supported on $[0,2]$ on the positive half-line and equal to one on $[0,1]$. For $N=x^{21/100}$, define

$$

 B_{w,N}(x)=\sum_n W(n/N)\chi(n)n w(n)S_\chi(x/n),\qquad
 B_w(x)=\sum_n\chi(n)n w(n)S_\chi(x/n).

$$

For every fixed real output phase $\phi$, write $Y_j=\Re(e^{i\phi}B_{w,N}(j^4))$, using $N=j^{0.84}$ at that sample. For each weight in the table,

$$

 \limsup_{j\to\infty}Y_j/j^6\ge c_w,\qquad
 \liminf_{j\to\infty}Y_j/j^6\le-c_w,\qquad
 \limsup_{J\to\infty}J^{-7}\sum_{j\le J}[\pm Y_j]_+\ge c_w/14.

$$

| Dilator weight $w(n)$ | Certified $c_w$ |
|---|---:|
| $\log n$ | $0.03047$ |
| $(\log n)^2$ | $0.0399$ |
| $a\log n+b(\log n)^2,\ a,b\in\mathbb R$ | $0.01019\sqrt{a^2+b^2}$ |
| $n^{\,i}$ | $0.03711$ |

These are unconditional statements on every prescribed orientation of the true complex prime data. The table gives limit superiors for the two signs, which may use different subsequences. Mlyle’s unweighted $B_{1,N}$ in the notation $w\equiv1$ is $o(x^{3/2})$. Adding an arbitrary constant to any polynomial weight in the table therefore preserves all displayed conclusions. No estimate of the naked fixed-character $D_\chi(J)$ follows from these lower bounds. [Mlyle’s c2eb094 calculation](https://github.com/mlyle/riemann-masullo/blob/c2eb094fffef928fdb72c2e180c255092e819347/research/5571/fourth-power-prime-curvature/spectral-interpolation-periodic-prime-convolution.md) · [Finite character certificate used to locate the test interval](https://github.com/willzh0/riemann-masullo/blob/53cac8a4461b84ad1d9c96ea2305f48e82ba4a31/PROOF.md)

## Exact factors, coefficients and the coherent cancellation

Let $P_\chi(s)=\sum_p\chi(p)\log p\,p^{-s}$ initially for $\Re s>1$, and $M_w(s)=\sum_n\chi(n)w(n)n^{-s}$. With the unnormalized Riesz kernel,

$$

 {\cal M}_w(s):=\int_1^\infty B_w(x)x^{-s-2}\,dx
 =\frac{M_w(s)P_\chi(s)}{s(s+1)} .

$$

For $w(n)=n^{i\tau}(\log n)^k$, $M_w(s)=(-1)^kL^{(k)}(s-i\tau,\chi)$. On $\Re s>1/2$, $P_\chi=-L'/L-H$, with $H=\sum_{p,r\ge2}\chi(p)^r\log p\,p^{-rs}$ holomorphic there. Removing the entire even-power part gives continuation through the target on the critical boundary:

$$

 P_\chi(s)=A_\chi(s)-A_{\eta}(2s)-
       \sum_{p,\ r\ge3\ {\rm odd}}\chi(p)^r\log p\,p^{-rs},
 \quad A_\xi=-L'/L(\,\cdot\,,\xi),\quad\eta=\chi^2 .

$$

The last series converges absolutely for $\Re s>1/3$. The quadratic character $\eta$ is nonprincipal, and $L(1+it,\eta)\ne0$. In particular there is no deterministic square drift at $s=1/2$. More generally, if $\chi^2$ were principal, the square pole contributes $-\tfrac23M_w(1/2)x^{3/2}$ before accounting for any primary zero at the same point. The pole of $A_{\chi^2}(2s)$ has residue $1/2$. For this order-four character $4\mid d$ forces $\mu(d)=0$, so no principal pole enters any finite Möbius prime-power extraction.

At an exterior zero $\rho$ of multiplicity $m$, the residue before division by $s(s+1)$ is $-mM_w(\rho)$. A derivative of order $k<m$ leaves it removable at $\tau=0$, whereas order $k=m$ gives the nonzero $(-1)^{m+1}mL^{(m)}(\rho,\chi)$. For the first log weight it is $mL'(\rho)$; for the second it is $-mL''(\rho)$. A fixed relative ordinate shift $\tau$ gives $-mL(\rho-i\tau,\chi)$. Outside a countable set of real shifts this is nonzero at every exterior zero, because the zeros of a nonzero entire function are discrete. Thus a square-root upper bound for generic shifted complex data would already exclude every exterior zero of this particular $L$-function.

For first and second dilator logs the physical arithmetic coefficients at $m$ are, with $\ell_p=\log p$ and $R_k(m)=\sum_{p\mid m}\ell_p^k$,

$$

 \chi(m)\{\log m\,R_1(m)-R_2(m)\},\qquad
 \chi(m)\{(\log m)^2R_1(m)-2\log m\,R_2(m)+R_3(m)\}.

$$

These follow by writing $n=m/p$ in the exact finite prime sum. In particular both dilator logs have zero coefficient at $n=1$.

If prime weights are changed as well, a factor $p^{i\omega}$ shifts the prime part to $P_\chi(s-i\omega)$, and only $\tau-\omega$ enters the multiplier at its poles. In particular the coherent phase $\tau=\omega$ preserves all original primary cancellations. In log variables let $B_{a,b}$ use $(\log n)^a(\log p)^b$ in addition to the base prime $\log p$. Its numerator is $(-1)^{a+b}L^{(a)}P_\chi^{(b)}$. At a simple primary zero the residues for $B_{1,0},B_{0,1}$ are $+L'$, $-L'$. For $B_{2,0},B_{1,1},B_{0,2}$ the respective coefficients of the double and simple poles are $(0,-L'')$, $(L',L'')$, $(-2L',-L'')$. They cancel in $B_{2,0}+2B_{1,1}+B_{0,2}$. All these principal parts refer to numerators. Hence differentiating the controlled coherent family gives identities between lifted terms. It supplies no separate upper estimate for their difference.

The coherent terms do retain an unconditional bound. If $v(t)=t^{i\tau}(\log t)^k$, multiplying the full unweighted coefficients at $m$ by $v(m)$ gives

$$

 v(x)B_{1}(x)+\int_1^x\big((x-t)v''(t)-2v'(t)\big)B_{1}(t)\,dt ,

$$

where $B_{1}$ here means $w\equiv1$. This is twice-integrated partial summation. Splitting at $\sqrt x$ in mlyle’s quartic estimate for $B_1$, and using $|v^{(r)}(t)|\ll_{k,\tau}t^{-r}(\log(2t))^k$, bounds the result by $O_{k,\tau}(x^{3/2}e^{-c'(\log x)^{3/5}(\log\log x)^{-1/5}})$ for some $c'>0$. In particular the prime-log and dilator-log terms individually have a certified oscillation which cancels in their controlled sum.

## The square spectrum and a power remainder

For each fixed $w(n)=n^{i\tau}(\log n)^k$, there is an unconditional formula with an error below the critical size,

$$

 B_w(x)=-\sum_{\rho_\chi}
  \frac{M_w(\rho_\chi)x^{1+\rho_\chi}}{\rho_\chi(1+\rho_\chi)}
 +\frac12\sum_{\rho_\eta}
  \frac{M_w(\rho_\eta/2)x^{1+\rho_\eta/2}}
       {(\rho_\eta/2)(1+\rho_\eta/2)}
 +O_{k,\tau}(x^{4/3}).

$$

The two sums count nontrivial zeros with multiplicity and converge absolutely for fixed $x$. To bound the omitted odd powers put $A_w(y)=\sum_{n\le y}\chi(n)w(n)(y-n)$. Then $A_w(y)\ll_{k,\tau}y$. For a direct proof, cut the function $(y-t)_+w(t)$ off below $t=1/2$, preserving its values at all positive integers, and integrate twice against a bounded periodic second primitive of the mean-zero character lattice measure. The endpoint contributes $O(|w(y)|)$, compact-cutoff derivatives contribute $O(y)$, and the interior absolute second derivative costs $O(y\int_1^\infty (\log(2t))^k t^{-2}\,dt+\int_1^y(\log(2t))^k t^{-1}\,dt)=O_{k,\tau}(y)$. The odd $r\ge3$ contribution thus costs $O_{k,\tau}(x\sum_{r\ge3,\ {\rm odd}}\vartheta(x^{1/r}))=O_{k,\tau}(x^{4/3})$.

For the two displayed complete factors $M_w(s)A_\chi(s)$ and $M_w(s)A_\eta(2s)$, move the Riesz contour to $\Re s=-1/8$. The functional equations and Stirling give $M_w(-1/8+it)\ll_{k,\tau,\nu}(1+|t|)^{5/8+\nu}$ and $A_\xi(d(-1/8+it))\ll\log(2+|t|)$ for $d=1,2$. The new contour is absolutely convergent. One can choose simultaneous horizontal heights away by $\gg 1/\log T$ from the ordinates of either scaled divisor, using their $O(\log T)$ local counts. There the logarithmic derivatives are $O(\log^2T)$ from their partial fractions, so the horizontal integrals tend to zero. The residues at zero cost $O_{k,\tau}(x\log(2x))$, including the trivial zero at zero of the even $\eta$. The leading poles give the displayed signs and the $1/2$ Jacobian. For the absolute convergence of the zero sums, standard convexity and Cauchy on fixed-width circles bound $M_w(s)\ll(1+|t|)^{1/2+\nu}$ throughout the closed critical strip for any fixed $\nu>0$. [Functional equations](https://dlmf.nist.gov/25.15#E5) · [Explicit logarithmic derivative and local zero-count inputs for fixed primitive characters](https://arxiv.org/pdf/1305.3087)

In particular an $O(x^{3/2})$ complex bound for $B_w(x)$ is equivalent to $M_w(\rho)=0$ at every exterior zero of $\chi$. Necessity follows from the Mellin integral on $\Re s>1/2$. For sufficiency the absolutely summable remaining primary terms are $O(x^{3/2})$, and the entire secondary series is $O(x^{3/2})$. Under simultaneous bounds for all $1\le k\le r$, this criterion excludes exactly the exterior zeros of multiplicity at most $r$. In particular the first logarithm tests simple exterior zeros, while the actual boundary oscillations below hold unconditionally.

## The short cutoff

For these same fixed $k,\tau$, the short version satisfies

$$

 B_w(x)-B_{w,N}(x)=O_{k,\tau,W,\varepsilon}(x^{1.48+\varepsilon}).

$$

Here is the additional check needed to transfer mlyle’s published reciprocal-prime estimate. Let $h=1-W,\ g(t)=w(t)h(t/N)$. In the double periodic integration against the mean-zero $U_2$, the endpoint at $x/p$ is $p\,g(x/p)U_2(x/p)$. Integrating the ordinary term once more against $U_3$ costs

$$

 O_{k,\tau,W}\big((\log(2x))^k(x/N^2+p/N)\big)

$$

for each $p\le x/N$. Indeed $|w^{(r)}(t)|\ll_{k,\tau}t^{-r}(\log(2t))^k,\ r\le3$, and after integration the regular derivative is $(x-pt)g'''(t)-3p g''(t)$. Integrals on $[N,2N]$ and $[2N,x/p]$, and the endpoint $p g'(x/p)$, obey the displayed bound. Thus the total regular error is $O(x^2N^{-3}(\log(2x))^k)$. In each boundary prime block $[P,2P]$, the sup norm and total variation of $p\,g(x/p)$ are $O_{k,\tau,W}(P(\log(2x))^k)$. Mlyle’s uniform reciprocal-prime partial sums and all his exponent inequalities then apply verbatim up to this logarithmic factor, absorbed in the arbitrary $\varepsilon$. [Original reciprocal-prime lemma and exact cutoff exponent ledger](https://github.com/mlyle/riemann-masullo/blob/c2eb094fffef928fdb72c2e180c255092e819347/research/5571/fourth-power-prime-curvature/spectral-interpolation-periodic-prime-convolution.md)

## The certified unpaired zero and signed oscillation

The interval $I=[-69338619,-69338618]/2^{24}$ has opposite Hardy endpoint signs. The verifier computes these signs directly from $5^{-s}\sum_{a=1}^4\chi(a)\zeta(s,a/5)$, the odd gamma factor and the exact quartic root number. At every $s=1/2+it,\ t\in I$, it checks $|L_\chi(\bar s)|>1.97$, and its two Taylor coefficients enclose $v_1=L_\chi'(s)$ and $v_2=-L_\chi''(s)$. There is a simple zero $\rho$ on this interval, its mirror is regular, and the verifier checks the four lower bounds

$$

 \frac{|v_1|}{2|\rho(\rho+1)|}>0.03047,\quad
 \frac{|v_2|}{2|\rho(\rho+1)|}>0.0399,\quad
 \frac{|\Im(v_2\bar v_1)|}{2|\rho(\rho+1)|\sqrt{|v_1|^2+|v_2|^2}}>0.01019,\quad
 \frac{|L_\chi(\rho-i)|}{2|\rho(\rho+1)|}>0.03711 .

$$

The determinant divided by the Frobenius norm bounds the least singular value of the real two-column matrix from below. This yields the bound for every real linear combination of the two log weights. The proof uses one simple zero and an independently checked mirror value. It does not require a count of other zeros. [Two-precision Arb verifier](verify_quartic_log_dilators.py) · [Bracket’s original arithmetic certificate](https://github.com/willzh0/riemann-masullo/blob/53cac8a4461b84ad1d9c96ea2305f48e82ba4a31/receipt.json)

For $H(x)=\Re(e^{i\phi}B_w(x))$, the real-projected Mellin transform is

$$

 F(s)=\tfrac12\big(e^{i\phi}{\cal M}_w(s)+e^{-i\phi}\overline{{\cal M}_w(\bar s)}\big).

$$

At $\rho$ its residue $r=-e^{i\phi}M_w(\rho)/(2\rho(1+\rho))$ has the modulus certified above. The transform is regular at every real $s\ge1/2$. Indeed $\Re L_\chi(s)=\sum_{l\ge0}[(5l+1)^{-s}-(5l+4)^{-s}]>0$ for real $s>0$, and $L_\eta(2s)\ne0$ for $2s\ge1$.

If eventually $H(x)\le M x^{3/2}$, the Mellin transform of $Mx^{3/2}-H(x)$, after dropping any finite initial segment, converges for real $s>1/2$ by Landau’s theorem for nonnegative Mellin integrals. Otherwise its real convergence abscissa would be a singularity despite the displayed meromorphic continuation being regular there. The inequality between its transform modulus at $\rho+u$ and its transform at $1/2+u$, multiplied by $u>0$ and passed to $u\downarrow0$, gives $|r|\le M$. Applying the same argument to $-H$ gives the signed continuous assertions. No hypothesis on zeros to the right is needed.

One direct proof of the real-abscissa fact expands the transform about a real $b$ just to the right of the convergence abscissa. The Taylor coefficients in $z=b-s$ are nonnegative log moments. Holomorphy through the real boundary makes the disk of convergence contain a positive $z$ beyond that boundary. Monotone convergence of the Taylor series under the integral then gives convergence of the defining integral there, a contradiction.

## Fourth-power sampling and cumulative lower bounds

Write $a_w(m)=\chi(m)\sum_{p\mid m}\log p\, w(m/p)$. For $X=j^4,\ H_0=(j+1)^4-j^4\asymp X^{3/4}$ and any $A>0$,

$$

 \sup_{0\le h\le H_0}\left|\sum_{X<m\le X+h}a_w(m)\right|
 \ll_{k,\tau,A}\frac{H_0}{(\log X)^A}.

$$

For $h\le H_0/(\log X)^{A+k+3}$ use $|a_w(m)|\ll(\log(2X))^{k+1}$ and at most $h+1$ integers. For larger $h$ split $n=m/p$ at $X^{1/3}$. When $n>X^{1/3}$, sum first over $n$ in the single resulting interval for each $p\le2X^{2/3}$. The partial sums of $\chi(n)$ are bounded, and the sup norm plus total variation of $w$ on this interval is $O_{k,\tau}((\log(2X))^k)$. Chebyshev bounds this part by $O_{k,\tau}(X^{2/3}(\log(2X))^k)$. For $n\le X^{1/3}$, set $y=(X+h)/n,\ H=h/n$. Uniformly $H\ge y^{3/5}$ for all sufficiently large $X$, since the minimum of $(3/4-b)/(1-b)$ on $0\le b\le1/3$ is $5/8$. The fixed-modulus short-interval progression PNT at exponent $7/12+\epsilon<3/5$ gives $\sum_{y-H<p\le y}\chi(p)\log p\ll_D H/(\log X)^D$ for arbitrary $D$, by summing its four reduced classes. The small fixed exponent gap absorbs all required powers of $\log y$. Sum $(\log(2n))^k/n$ up to $X^{1/3}$. This proves the claim. [Thorner–Zaman, §1.2, short-interval formula on p. 3](https://arxiv.org/pdf/2108.10878#page=3)

Since $B_w(x)=\sum a_w(m)(x-m)_+$, the last estimate bounds the change in its derivative inside this cell. Consequently $B_w$ differs from the linear interpolation of its endpoint values by $O_A(H_0^2/(\log X)^A)=o(X^{3/2})$, uniformly in the cell. This transfers the real continuous signed limsup and liminf bounds to $j^4$ without losing the residue constant. The pointwise short-cutoff error is also $o(j^6)$.

For completeness let $g(t)=H(t^4)$ and $P_+(U)=\int_1^U[g(t)]_+\,dt$. If the positive-part sampled prefix has finite normalized limsup $M$, the chord bound implies $\limsup P_+(U)/U^7\le M$. Indeed $(t^4-j^4)/H_0=(t-j)+O(1/j)$ uniformly on $j\le t\le j+1$. The sum of the two integrated chord weights adjacent to each interior sample is $1+O(1/j)$, and the integrated cell errors contribute $o(U^7)$. The endpoint weights are at most one. For nonintegral $U$ use the next integer. Adding back the short-cutoff errors also costs $o(U^7)$.

The positive Mellin integral then converges for $s>1/2$. The negative-part transform, initially its difference with $F$, converges there also by the same real-abscissa argument. Since $F$ is regular at real $1/2$, its real-axis contribution vanishes after multiplication by $u\downarrow0$. By the triangle inequality on the pole line,

$$

 |r|\le2\limsup_{u\downarrow0}4u\int_1^\infty[g(t)]_+t^{-7-4u}\,dt\le14M.

$$

The second inequality is partial integration using $P_+(T)\le(M+o(1))T^7$. Replacing $H$ by $-H$ yields the other sign. This proves the cumulative lower bounds in the table.
