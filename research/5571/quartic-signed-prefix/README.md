# Signed prefixes of the quartic annular prime sum

For either primitive quartic character modulo five let
$$
 K(u)=\int_1^2(1-uv)_+\,dv,\qquad
 Q(x)=\sum_p\chi(p)\log p\,K(p/x),\qquad
 E_\pm(J)=\sum_{j=1}^J[\pm\Re Q(j)]_+ .
$$
Conjugation leaves both real prefixes unchanged. For every positive integer $J$ in the indicated range,
$$
 \begin{array}{ll}
 E_\pm(J)<0.903\,J^{3/2} & (J\le 2\cdot10^{42}),\\
 E_\pm(J)<0.985\,J^{3/2} & (J\le 2.4\cdot10^{42}),\\
 \displaystyle\sum_{j\le J}|Q(j)|< J^{3/2} & (J\le 1.9\cdot10^{41}).
 \end{array}
$$
The absolute complex bound permits a different phase at every sample. The real signed upper coefficient through $10^{42}$ is $0.702$. The interval $10^{30}\le J\le10^{41}$ has the smaller real coefficient $0.254$. Using the completed logarithmic derivative for all low zeros in place of the explicit 13-zero refinement still gives $E_\pm(J)<0.986J^{3/2}$ through $1.7\cdot10^{42}$.

The finite verification height is $H=20,000,000$, from Platt for the primitive conductor-five characters. It applies to both signs of the ordinate. The earlier unfiltered fourth-power estimates by mlyle use the triangular prime weight at $j^4$. The present result uses the fixed nonnegative annular weight at $j$ and controls both genuine real signs. The all-height upper for any unbounded sequence remains open. [Platt, Theorem 10.1](https://www.ams.org/journals/mcom/2016-85-302/S0025-5718-2016-03077-X/S0025-5718-2016-03077-X.pdf#page=18) · [Mlyle’s triangular prime sums](https://github.com/mlyle/riemann-masullo/tree/3f90b6c75f2e36f52c2c9cb427155a556bcee9d8/research/5571/quartic-mod-five-deficit) · [Earlier finite annular proof](https://github.com/willzh0/riemann-masullo/tree/842ce30ef40dfa1e2a9138d37ebb1960d37b9315/research/5571/quartic-annular-bound)

The compensated Gaussian and its two reproduced exponential moments come from the earlier finite annular proof. An independent interpolation audit established the directed half-wave identity below. The physical obstruction in the final paragraph comes from the same team’s analysis of the loss on taking positive parts before summing over the four prime classes. Mlyle’s earlier quartic calibration and the separate extension through 27,173,860 prefixes concern the triangular prime statistic. [Unrestricted fourth-power certificate](https://github.com/willzh0/riemann-masullo/tree/0b8885bf2d52f23cd32dafff1a77680db475bbd0/research/5571/quartic-fixed-prime-prefix)

The four programs use Python 3.11 or newer and python-flint 0.8.0. Each includes its dependency specification for the following replay commands.

    uv run verify_quartic_linear_height.py
    uv run verify_cumulative.py
    uv run verify_combined.py
    uv run verify_quartic_low_spectrum.py --precision 128
    uv run verify_quartic_low_spectrum.py --precision 192

The first three run both precision settings. [Interval output](constant-ledgers.txt) · [128-bit low-zero coverage and brackets](low-spectrum-128.json) · [192-bit low-zero coverage and brackets](low-spectrum-192.json)

## The odd error at one knot

Fix $0<\delta\le10^{-6}$, set $c=e^{-\delta^2/2}$, and let $\nu=(1+c)N(0,\delta^2)-cN(0,2\delta^2)$. It fixes $1,e^r,e^{-r}$ under convolution. Write $Q_\delta(x)=\int Q(xe^h)\,d\nu(h)$.
Put $f(r)=2(\cosh r-1)$, $F(r)=f(r)\mathbf1_{r>0}$, $D=\nu*F-F$. Then
$$
 K(e^r)=1-\tfrac32e^r+F(r+\log2)-\tfrac12F(r).
$$
Each integer prime/sample knot is valid in this identity, since $F(0)=F'(0)=0$. The signed Gaussian is even, and $F(r)+F(-r)=f(r)$, so $D$ is odd. For $r>0$,
$$
 D(-r)=\int_{h>r}f(h-r)\,d\nu(h)\le0 .
$$
Indeed the Gaussian density of $\nu$ on the positive half-line changes sign once from positive to negative, by the strictly decreasing ratio of the narrower Gaussian to the wider one. Its $f$-weighted integral there is zero. The ratio $f(h-r)\mathbf1_{h>r}/f(h)$ is nondecreasing, since $f'/f=\coth(h/2)$ decreases. Multiplying the signed density by this ratio proves the inequality.

For $T(h)=h\cosh h-\sinh h$ and a standard normal $Z$, Fubini gives exactly
$$
 I:=\int_{\mathbb R} e^{-r}|D(r)|\,dr
   =c\,\mathbb E T(\sqrt2\delta|Z|)
          -(1+c)\mathbb ET(\delta|Z|)<0.442\,\delta^3 .
$$
The inner integral is $\int_0^h2\cosh r\,f(h-r)dr=2T(h)$. For $h\ge0$, $h^3/3\le T(h)\le h^3e^h/3$ follows by integrating $r\sinh r$. With $a=\sqrt2\cdot10^{-6}$,
use $e^u\le1+ue^u$, $\mathbb E|Z|^3=2\sqrt{2/\pi}$ and
$\mathbb E|Z|^k e^{a|Z|}\le\sqrt{(2k-1)!!\,2e^{2a^2}}$.
The upper coefficient is below $0.440679$. The same one-sided expression for $D(-r)$, differentiated and integrated in $r$, gives
$$
 \operatorname{Var}|D|\le \int f(|h|)\,d|\nu|(h)
 \le\int h^2e^{|h|}\,d|\nu|(h)<4.1\delta^2 .
$$
There is no jump at $r=0$. Integrals of $e^{h/2}$ and $e^{-h}$ against $d|\nu|$ are both below $1.14$. For the last claim the mass of $|2g_1-g_{\sqrt2}|$, in standard normal coordinates, is exactly
$$
 1+2\{\operatorname{erfc}(z_0/2)-2\operatorname{erfc}(z_0/\sqrt2)\},
 \qquad z_0=\sqrt{6\log2} ,
$$
where $g_s$ denotes the centered Gaussian density of standard deviation $s$. Passing from 1 to $c$ costs at most $2(1-c)\le\delta^2$, and a tilt $e^{th}$, $|t|\le1$, costs at most $\int |h|e^{|h|}(2g_\delta+g_{\sqrt2\delta})\,dh$. The combined upper is below $1.132928$.

## Summing the shifted prime terms first

For $a=1,2$ the defect row has exactly the weights $\tfrac12,1$ in absolute value. For fixed $p$, $G(t)=|D(\log(ap/t))|$ has variation at most $4.1\delta^2$ on $t>0$. On each closed cell $[j-1,j]$, with $G(0)=0$ by continuity,
$$
 G(j)\le\int_{j-1}^jG(t)dt+\operatorname{Var}_{[j-1,j]}G.
$$
Summing from $1$ to $J$ includes the rightmost sample. Additivity of variation and $t=ap e^{-r}$ give $\sum_{j=1}^JG(j)\le apI+4.1\delta^2$.

Take $J\ge10^{30}$, $k=1.001$, and $Y=kJ/a$. Only the actual classes $C=\{1,4\}$ contribute to $\Re Q$, and $p=5$ contributes zero. Write $\theta_C(t)=\sum_{p\le t,\ p\bmod5\in C}\log p$. The explicit progression estimate gives $.4995t\le\theta_C(t)\le.5005t$ for $t\ge10^{12}$, since each reduced class differs from $t/4$ by less than $t/(160\log t)$. On $[\sqrt Y,Y]$ these inequalities apply. Stieltjes partial summation, including a possible prime at $Y$, yields
$$
 \sum_{p\le Y,\ C}p\log p
 =Y\theta_C(Y)-\int_0^Y\theta_C(t)\,dt
 \le .5005Y^2-.4995(Y^2-Y)/2<.251Y^2.
$$
Also $\theta_C(Y)<.501Y$. These are bounds for the true logarithms of the primes. The scale shift changes the prime cutoff through $Y=kJ/a$. The coefficient sums obey $1/2+1/2=1$ after division by $a$. [Bennett, Martin, O’Bryant and Rechnitzer, explicit progression estimates](https://arxiv.org/abs/1802.00085)

For $p>Y,\ j\le J$, put $r=\log(ap/j)>\log k=:h_0$. From the positive-side defect formula, $|D(r)|\le\int_{h>r}h^2e^{|h|}\,d|\nu|(h)$. At fixed $j,h$ such primes satisfy $p<je^h/a$. Since $\sum_{p\le x}\log p\le2x$, their total cost at this $j$ is bounded by $(2j/a)\int_{h>h_0}h^2e^{2h}\,d|\nu|(h)$. Cauchy–Schwarz, $\Pr(|Z|\ge v)\le2e^{-v^2/2}$, and the tilted moment above bound this integral by $1000\delta^2e^{-h_0^2/(8\delta^2)}<10^{-100}\delta^2$. This estimates the infinite shifted prime tail, including every prime above $J$. Combining the two knots, the normalized half-absolute interpolation cost is at most
$$
 {\cal P}(J)=\tfrac12\left[.251 k^2 \sqrt J\, (.442\delta^3)
 +.501 k(4.1\delta^2)/\sqrt J\right]+10^{-45}
 \quad (10^{30}\le J\le10^{43}).
$$

## The right-hand zero sum

Hereafter $\delta=4/H$. Write $M(s)=(2^{1-s}-1)/[(1-s)s(s+1)]$.
Among the quartic zeros above $|\gamma|=H$ let ${\cal R}=\{\rho=\beta+i\gamma:\beta>1/2,\ |\gamma|>H\}$, with multiplicities,
$$
 R(x)=-\sum_{\rho\in{\cal R}}M(\rho)x^\rho,\qquad
 \phi(s)=(1+c)e^{\delta^2s^2/2}-ce^{\delta^2s^2},\qquad
 R_\delta(x)=-\sum_{\rho\in{\cal R}}M(\rho)\phi(\rho)x^\rho .
$$
The latter identity follows by absolute convergence and Gaussian exponential integrability. Write $L=Q-R$. From the [prime-power and endpoint computation](QUARTIC_LINEAR_HEIGHT.md), for every $x\ge1$ the low coefficient of $|\Re L(x)|/\sqrt x$ is at most $5/8+3U_3(H)$, improving to $b+3U_3(H)$ at $x\ge T=10^{12}$. Here $b=.181$, or $b=.062$ using the 13 certified low quartic zeros. The latter follows from $.180134-.168354+.049502<.062$, with $.168354$ a lower bound on the exact coarse primary coefficient at $T$. For $0<x<1$, $Q=0$ and $|R(x)|\le(3/2)U_3(H)\sqrt x$. The quadratic zero sum, prime powers, conductor and gamma terms are already included in the low coefficient. [Independent low spectrum verifier](verify_quartic_low_spectrum.py)

Here are the requisite whole-divisor moments and local right-divisor bound, proved by partial summation and the functional equation in the [unsmoothed prefix proof](CUMULATIVE.md). With $\eta=.55,\ c_0=.6287,\ t\ge H,\ Z=\log t$,
$$
 \begin{split}
 U_m(t)&=\frac{Z/(m-1)+(m-1)^{-2}}{\pi t^{m-1}}
       +\frac{\eta(2Z+1/m)}{t^m}\ \ge\sum_{|\gamma|>t}|\gamma|^{-m},\\
 \sum_{\rho'\in{\cal R}}\frac1{2+(\gamma-\gamma')^2}&\le c_0\log|\gamma| \quad(\rho\in{\cal R}).
 \end{split}
$$
Reflection across the critical line at the same signed ordinate gives half the full ordinate mass as an upper bound for the right-hand divisor. The count uses the fixed character at both signed ordinates. [Bennett et al., Theorem 1.1](https://arxiv.org/abs/2005.02989)

Define $y=\delta t,\ m=6+2y^2,\ k_1=m-1$, and
$$
 S_\delta(t)=\frac{e^{-y^2}}{t^5}
 \left[\frac{Z^2/k_1+2Z/k_1^2+2/k_1^3}{\pi}
 +\frac{\eta}{t}\{2Z^2+2Z/m+2/m^2\}\right].
$$
This bounds $\sum_{|\gamma|>t}|\gamma|^{-6}\log|\gamma|\,e^{-\delta^2\gamma^2}$. Indeed, for $v\ge1$, $v^2\ge1+2\log v$. Use $e^{-y^2}t^{2y^2}u^{-m}\log u$ as the test majorant at $u\ge t$. The smooth zero-count derivative is at most $\log u/\pi$. The signed counting error at $t$ costs at most $\eta t^{-m}Z^2$ before the prefactor. The derivative-integral error is at most $\eta t^{-m}(Z^2+2Z/m+2/m^2)$, by dropping the negative term in $-d(u^{-m}\log u)/du$.

For all $\rho\in{\cal R}$, $|\phi(\rho)|\le A e^{-\delta^2\gamma^2/2}<1$, $A=2.001+1.001e^{-8}$. With $d_1=1/(5.60\log(7.5H))$, Kadiri's zero-free region yields $\beta\le1-d_1$ when $H<|\gamma|\le1.5H$. For $J\ge2$, $(1+2^{1-\beta})J^\beta=J^\beta+2(J/2)^\beta$ increases with $\beta$. Apply the local bound to the Gram kernel $3/[(b_1+id)(3-b_1-id)]$, $b_1=\beta+\beta',\ d=\gamma-\gamma'$, arising from the weight $1$ on $u\le0$ and $e^{-3u}$ on $u>0$ for $R_\delta(Je^u)$. Its modulus is at most $3/(2+d^2)$. Cauchy–Schwarz on $u\le0$, and the right/full half count, then give
$$
 \frac1{2J^{3/2}}\int_0^J|R_\delta(x)|dx
 \le {\cal B}(J)=\frac A4\sqrt{3c_0\{(1+2^{d_1})^2 J^{1-2d_1}S_\delta(H)
                                      +4J S_\delta(1.5H)\}} .
$$
The derivation with the same weight and both factors of $1/\sqrt2$ is in the [Gram calculation](CUMULATIVE.md). No separation between neighboring ordinates is required. [Kadiri, Theorem 1.1](https://www.cs.uleth.ca/~kadiri/articles/explicit_zerofree_regions_for_dirichlet_l_functions.pdf#page=1)

The complex signed mean of the unsmoothed right-hand part has another inverse-ordinate factor from integrating $x^\rho$. With $d_0=1/(5.60\log(15H))$, splitting at $3H$ as above gives
$$
 (2J^{3/2})^{-1}\left|\int_0^J R(x)dx\right|
 \le {\cal M}(J)=\frac{\sqrt J}4
       [(1+2^{d_0})J^{-d_0}U_4(H)+2U_4(3H)] .
$$
For integer sampling, $|R'(x)|,|R_\delta'(x)|\le(3/2)U_2(H)$ on $x\ge1$ and $|R(x)|,|R_\delta(x)|\le(3/2)U_3(H)$ on $0\le x\le1$. The derivative estimate follows after cancelling the factor $\rho$ in $M$. Use the cells $[j-1,j]$ from $j=2$ to $J$. For the modulus, the missed bottom integral is nonnegative and the $j=1$ sample costs at most $(3/2)U_3(H)$. For the signed comparison, retain both $\int_0^1R$ and $R(1)$, costing at most $3U_3(H)$. The two half-comparisons together cost at most
$$
 {\cal D}(J)=4(U_2(H)/\sqrt J+U_3(H)/J^{3/2}).
$$

## Combining the estimates

Use $2[u]_\pm=|u|\pm u$. Inside the absolute sum write
$Q=(Q-Q_\delta)+L_\delta+R_\delta$ and inside the signed sum use $Q=L+R$. Both the original and the smoothed low remainders can be summed through the threshold $T$ by $\sum_{j\le J}\sqrt j\le(2/3)J^{3/2}+\sqrt J$ and $\sum_{j\le A}\sqrt j\le A^{3/2}$ for real $A\ge0$. For the smoothed threshold the latter sum has $A=Te^{-h}$, giving the tilt $e^{h/2}e^{-3h/2}=e^{-h}$. The unsmoothed tilt is 1. The combined normalized upper is
$$
 {\cal P}(J)+{\cal B}(J)+{\cal M}(J)+{\cal D}(J)
 +1.07\{(b+3U_3(H))(2/3+1/J)+(5/8-b)(T/J)^{3/2}\}.
$$
On $10^{30}\le J\le J_*$, the powers with positive exponent are bounded at $J_*$ and all decreasing terms at $10^{30}$. At the largest claimed $J_*=2\cdot10^{42}$ the contributions from interpolation, Gram energy, signed mean, the low part and sampling, respectively, are bounded above by $0.628839,0.226712,0.072504,0.044227,2\cdot10^{-21}$.
For $J<10^{30}$, the [direct unsmoothed calculation](CUMULATIVE.md) gives $<.626J^{3/2}$ throughout. Its global bound applies up to $10^{20}$. Between $10^{20}$ and $10^{30}$ its increasing energy evaluated at $10^{30}$ is below $0.002$. Every horizon and threshold is inclusive. [128/192-bit interval ledger](verify_combined.py)

## Directed interpolation and the complex modulus

An independent check of the Gaussian interpolation supplied a second exact knot identity. Since $D$ is odd and positive on the positive axis,
$$
 2\int_0^\infty\sinh(r)\,D(r)\,dr
     =\delta^2(e^{\delta^2/2}-1).
$$
Indeed $\int_0^h \sinh r\,(\cosh(h-r)-1)dr=h\sinh h/2-\cosh h+1$. Inserting the two Gaussian densities, their $\cosh h-1$ integrals cancel. The remaining difference follows from $\mathbb E[X\sinh X]=s^2e^{s^2/2}$ for $X\sim N(0,s^2)$. The larger of the two half-wave masses $\int e^{-r}[\pm D(r)]_+dr$ equals $(I+\delta^2(e^{\delta^2/2}-1))/2$, below $0.221\delta^3$. Each half-wave has at most half the variation bound, $2.05\delta^2$, since they are mirror images supported on opposite sides of their common zero. Subadditivity before summation over primes and both knots shows that ${\cal P}(J)$ also bounds the **whole one-sided** normalized cost $\sum_{j\le J}[\pm\Re(Q-Q_\delta)(j)]_+/J^{3/2}$. The sign attached to each actual prime merely chooses one of the two half-waves. The discarded positive prime tail still satisfies the stronger $10^{-100}\delta^2$ estimate above.

Now decompose $Q_\delta=L_\delta+R_\delta$ directly in the positive part. The directed high part costs ${\cal B}(J)$ plus a signed mean and mesh. The smoothed signed mean has upper coefficient $A e^{-8}\sqrt J\,U_4(H)/2$, by the bound on $\phi$ at the first unverified ordinate. Both half-mesh comparisons are still covered by ${\cal D}(J)$. Only one low row remains, with coefficient
$$
 1.14\{(b+3U_3(H))(2/3+1/J)+(5/8-b)(T/J)^{3/2}\}.
$$
At $2\cdot10^{42}$ the combined normalized upper is below $0.902778$. At $2.4\cdot10^{42}$ it is below $0.984017$. This proves the two signed bounds in the opening display.

For the full complex modulus use all four reduced classes. Each of the two complementary pairs has the same upper bounds $.251Y^2$ and $.501Y$ on its near-prime masses. The unsigned interpolation cost is therefore at most $4{\cal P}(J)$. The high absolute sum costs $2{\cal B}(J)+{\cal D}(J)$.
For the low part the quartic zero sum still costs at most $0.049502\sqrt x$ in complex norm, and the quadratic contribution is real. In the two elementary residues the additional imaginary magnitude is bounded by $|\Im(L'/L)(1,\chi)|+(3/2x)|\Im(L'/L)(2,\chi)|$, with each derivative magnitude in this expression below one from the same deflated Hurwitz jets as the real calculation. For the remaining odd proper powers use $p\ge2$ for every prime. The real calculation's geometric coefficient is replaced by
$$
 A_{\rm odd}=
 \frac{(\log4)(9/8)(2^{2/3}-1)}{1-2^{-2/3}}<2.5 .
$$
At $T=10^{12}$ the actual coarse quartic and real odd summands removed from the former envelope are greater than $0.168354$ and $0.011482$, respectively. Their complex replacements are $0.049502$ and $A_{\rm odd}T^{-1/6}$. Add at most $(1+3/(2T))/\sqrt T$ from the imaginary residues. All decreasing secondary terms may be bounded at $T$, giving $b_{\mathbb C}=.075$. Thus for $x\ge T$, $|L(x)|\le(b_{\mathbb C}+3U_3(H))\sqrt x$. At $1\le x<T$ the elementary bound $|Q(x)|\le2x$ and $|R(x)|\le(3/2)U_3(H)x$ give an initial coefficient $2,000,001$. The same coefficient covers $0<x<1$. Use the sole smoothed low row with $b=b_{\mathbb C}$ and this initial coefficient. On $10^{30}\le J\le1.9\cdot10^{41}$, the total coefficient is below $0.975194$. The already-certified full complex estimate at the smaller prefixes completes the stated unit bound. [Earlier full complex bound](https://github.com/willzh0/riemann-masullo/blob/842ce30ef40dfa1e2a9138d37ebb1960d37b9315/research/5571/quartic-annular-bound/FINITE-QUARTIC.md)

## Conditional obstruction for bandwidths chosen at each terminal prefix

Let $0\le\delta\le\Delta<\infty$, with $Q_0=Q$. Suppose the fixed quartic has a zero $\rho_0=\beta+i\gamma$ with $\beta>1/2$. For some $\lambda,c_*>0$ with $\lambda<1$, and for all sufficiently large integer $J$,
$$
     \inf_{0\le\delta\le\Delta}
     \sum_{\lambda J<j\le J}[\pm\Re Q_\delta(j)]_+
                      \ge c_* J^{1+\beta}.
$$
For each $0<\delta_{\min}\le\Delta$ the same statement holds, over $[\delta_{\min},\Delta]$, for $Q-Q_\delta$. One bandwidth serves every summand of the prefix. It may depend on $J$. The proof does not permit independent bandwidth choices at individual samples.

To see this, write the **real** explicit formula
$$
 \Re Q(t)=\sum_{\zeta\in{\cal Z}_\chi\cup\overline{{\cal Z}_\chi}}
       b_\zeta t^\zeta + e(t),\qquad
 b_\zeta=-\tfrac12(m_\chi(\zeta)+m_\chi(\bar\zeta))M(\zeta),\quad
 \sum |b_\zeta|<\infty,\quad e(t)=o(\sqrt t).
$$
Here the union consists of distinct points and the missing multiplicity is zero. The coefficient is nonzero at every member of the divisor, since $2^{1-\zeta}$ has modulus exceeding one. In particular a coincidence of conjugate ordinates adds their multiplicities. For $t<1$, $e(t)$ is bounded because $Q=0$ and the coefficient series is absolute. [Actual prime expansion](https://github.com/willzh0/riemann-masullo/blob/b61df9f867cec621a23ea9cfc7a5ff9c8b7f8622/research/5571/quartic-periodic-dilation/linear-prime-cutoffs.md)

The multipliers for the two filtered real outputs are $\Phi_\delta=\phi_\delta$ and $\Phi_\delta=1-\phi_\delta$. They respect conjugation. They are uniformly bounded on $0\le\Re s\le1$ for $0\le\delta\le\Delta$, because $\Re(s^2)\le1$. Thus the filtered coefficient series is uniformly absolutely summable. Define $r(y)=\sup_{t\ge y}|e(t)|/\sqrt t\to0$. For $x\ge1$ split the error convolution at $h=-(\log x)/2$. Above the split the normalized error is bounded by $r(\sqrt x)\int e^{h/2}d|\nu_\delta|$. Below it, if $xe^h\ge1$ the bound is $r(1)x^{-1/4}$, and if $xe^h<1$ it is $O(x^{-1/2})$, integrated against uniformly bounded mass. Consequently the normalized filtered remainder is $O_\Delta(r(\sqrt x)+x^{-1/4})=o(1)$, uniformly over this entire bandwidth interval. The unsmoothed error in the difference satisfies the same conclusion.

For $z=e^{\delta^2s^2/2}$, $\phi_\delta=z(1+c-cz)$ and $1-\phi_\delta=(1-z)(1-cz)$. If $0<\Re s<1$, $|z|<e^{\delta^2/2}<1+e^{\delta^2/2}$ for $\delta>0$, so $\phi_\delta(s)\ne0$. At $\delta=0$ it equals 1. Every exterior zero has $|\gamma|>H$, so $|z|<1$ there when $\delta>0$, and also $1-\phi_\delta(\rho_0)\ne0$. Compactness in the specified bandwidth ranges now gives a **fixed** positive lower bound for $|b_{\rho_0}\Phi_\delta(\rho_0)|$.

For clarity, fix $1/2<\sigma<\beta$. The fixed-conductor density theorem gives $\sum_{\Re\zeta>\sigma}|\Im\zeta|^{-1}<\infty$. Mlyle's positive compact annihilator therefore supplies bounded compactly supported $P\ge0,L_0$, independent of $\delta$, with $|L_0|\le CP$. The transform of $P$ vanishes at all $\zeta-1/2$ with $\Re\zeta>\sigma$. The transform of $L_0$ vanishes at every one except $\rho_0-1/2$, where it is nonzero. One construction convolves for each positive-ordinate pair the two masses at $0,\pi/|\Im\zeta|$ with ratio $e^{(\Re\zeta-1/2)\pi/|\Im\zeta|}:1$. The total support length is finite. Convolve with a smooth nonnegative bump, divide the resulting entire transform by its full zero at $\rho_0-1/2$ via compact tail primitives to make $L_0$, and convolve the undivided bump-measure with a sufficiently large interval to make $P$ bounded below on the support of those primitives. The full order of the zero is finite since the nonzero compact transform is entire. This division preserves the zero at the conjugate point. [Montgomery, Theorem 12.1](https://doi.org/10.1007/BFb0060851) · [Mlyle’s compact annihilator](https://github.com/mlyle/riemann-masullo/blob/69f6639d0e53c2a04aa3b5f8487a1be237274b97/research/5571/square-prefix-fixed-window-count/README.md)

Set $f_\delta(u)=e^{-u/2}\Re Q_\delta(e^u)$, or use the corresponding difference. Testing $f_\delta(v+\cdot)$ with $L_0$ gives the single selected term of modulus $\gg e^{(\beta-1/2)v}$ plus $O_\Delta(e^{(\sigma-1/2)v})+o_\Delta(1)$. Testing with $P$ gives only that latter bound. Indeed every frequency with $\Re\zeta>\sigma$ other than the chosen one was removed exactly, even if its real part approaches $\beta$ or exceeds it. The contribution from the full remaining infinite set is bounded by its uniform absolute coefficient mass times $O(e^{(\sigma-1/2)v})$, on the common compact support. Thus a single sufficiently large $v$ works for every $\delta$. The inequality $\int P|f_\delta|\ge|\int L_0f_\delta|/C$, followed by $2[u]_\pm=|u|\pm u$, gives a uniform lower bound for both signs on this fixed window. Translating the window inside $\lambda J<x<J$ converts $du=dx/x$ and the normalizing $x^{-1/2}$ into $J^{3/2}$ on that shell. Finally $|Q'|\ll1$ by Chebyshev and the bounded derivative of $K$, and $|Q'_\delta|\ll\int e^h\,d|\nu_\delta|\ll_\Delta1$. The integer sampling loss is $O_\Delta(J)$, absorbed by $J^{1+\beta}$. The same shell and onset work at all allowed bandwidths.

There are quantitative variants at the two ends of the bandwidth scale. Continue to assume the exterior zero $\rho_0$ exists, and write $G_0=\gamma^2-\beta^2>0$. For each $d<2(\beta-1/2)/(1+G_0)$, and $0\le\delta^2\le d\log J$, the smoothed row has both lower bounds
$$
 \sum_{\lambda J<j\le J}[\pm\Re Q_\delta(j)]_+
       \gg_{\rho_0,d} J^{1+\beta}e^{-G_0\delta^2/2}.
$$
In fact $|\phi_\delta(\rho_0)|\ge e^{-G_0\delta^2/2}$ since $|z|\le1$ and $|1+c-cz|\ge1$. On the entire strip $|\phi_\delta|\le3e^{\delta^2/2}$. The bounds on $\int e^{h/2}d|\nu_\delta|$ and $\int e^h d|\nu_\delta|$ are also at most $3e^{\delta^2/2}$. As $|e(t)|\ll1+\sqrt t$ on the whole positive half-line, the normalized convolution error is $O(e^{\delta^2/2})$ on the shell. Thus the tested error is $O(J^{\sigma-1/2}e^{\delta^2/2})$. Choose $1/2<\sigma<\beta-d(1+G_0)/2$. Its ratio to the selected mode tends to zero uniformly, and the mesh $O(Je^{\delta^2/2})$ is absorbed as well. In particular, a critical-scale upper for this smoothed row along an unbounded sequence would require
$\liminf\delta_J^2/\log J\ge2(\beta-1/2)/(1+G_0)$ along that sequence.

For a vanishing bandwidth in $0<\delta\le\Delta$, the complementary multiplier has the exact small-width limit
$$
 \lim_{\delta\downarrow0}\frac{1-\phi_\delta(\rho_0)}{\delta^4}
                 =\rho_0^2(\rho_0^2-1)/4\ne0 .
$$
It follows that $|1-\phi_\delta(\rho_0)|\gg_{\rho_0,\Delta}\delta^4$ on that interval. If $\delta\ge aJ^{-\kappa}$ with $a>0$, $\kappa\ge0$ and $4\kappa<\beta-1/2$, take $1/2<\sigma<\beta-4\kappa$ in the same proof. Both signed shell sums of the true correction then exceed a fixed multiple of $\delta^4 J^{1+\beta}$. The uniform bound for the original, unscaled error suffices because it is smaller than this main term. In particular a critical-scale bound for the correction along a bounded-bandwidth sequence requires $\liminf(-\log\delta_J)/\log J\ge(\beta-1/2)/4$, with the convention $-\log0=+\infty$.

There is also an unconditional arithmetic cost for discarding cancellation in the physical correction. Fix any $\delta>0$ and put $V(u)=\int K(ue^h)d\nu(h)-K(u)$. Its integral on $u>0$ is zero by the $e^{-h}$ moment, while $I_V=\int_0^\infty|V(u)|du>0$. Gaussian convolution smooths the two logarithmic knots, where the original kernel has a second-derivative jump. The kernel difference is bounded and decays faster than any power at infinity. The prime number theorem in the four reduced residue classes applied to $V_+$ and $V_-$ gives, uniformly in $\theta$,
$$
 \sum_p\log p\,[\Re(e^{i\theta}\chi(p))V(p/y)]_+
 =\frac{yI_V}{4}(|\cos\theta|+|\sin\theta|)+o(y).
$$
Uniformity follows because the formula uses finitely many scalar class estimates with multipliers of magnitude at most one. Partial summation or truncation with the elementary theta bound justifies the tails. For a phase chosen separately at each sample the unsigned termwise cost is consequently at least $(I_V/8+o(1))J^2$. On each residue class the signed leading coefficient is zero since $\int V=0$. This is a statement about the positive termwise majorant. Cancellation in the genuine signed sum is still available.
