# A nonzero periodic mean forces larger fourth-power oscillations in the shortened quartic prime row

Let $\chi$ be the primitive quartic character modulo $5$ with $\chi(2)=i$, and let $b(n)$ have arbitrary complex period-five values and mean $\mu=\frac15\sum_{r=1}^5b(r)$. Fix $0<\kappa<1$. Let $W$ be real and smooth on $[0,\infty)$, with $0\le W\le1$, equal to one on $[0,1]$ and zero on $[2,\infty)$. For $x\ge1$ put

$$
S_\chi(x)=\sum_p\chi(p)\log p\,(x-p)_+,\qquad
G_b(x)=\sum_{n\ge1}b(n)nW(n/x^\kappa)S_\chi(x/n).
$$

For every fixed unit complex $z$, put $g(x)=\Re(\bar zG_b(x))$. If $\mu\ne0$, each sign satisfies

$$
\limsup_{j\to\infty}\frac{[\pm g(j^4)]_+}{j^{6+2\kappa}}
 \ \ge\ \frac{617}{10^6}|\mu|,\qquad
\limsup_{J\to\infty}\frac{\sum_{j\le J}[\pm g(j^4)]_+}{J^{7+2\kappa}}
 \ \ge\ \frac{617}{2(7+2\kappa)10^6}|\mu|.
$$

Both are subsequential statements for each fixed phase and sign. The constants apply to every admissible cutoff. Each $W$ and $b$ can have its own subsequences. These exponents are lower bounds. At $\kappa=21/100$ the exponents are $321/50,371/50$, and the prefix constant is $617/14840000>1/25000$. Mlyle introduced the matched short periodic dilation in the fourth-power calibration. Its character multiplier has mean zero. [Mlyle, spectral interpolation by periodic prime convolution](https://github.com/mlyle/riemann-masullo/blob/c2eb094fffef928fdb72c2e180c255092e819347/research/5571/fourth-power-prime-curvature/spectral-interpolation-periodic-prime-convolution.md).

## The Mellin term from the moving upper cutoff

Write $\eta=\chi^2$,

$$
 M_b(s)=5^{-s}\sum_{r=1}^5 b(r)\zeta(s,r/5),\quad
 P_\chi(s)=\sum_p \chi(p)(\log p)p^{-s},\quad
 R(s)=\frac{P_\chi(s)}{s(s+1)},\quad
 \widehat W(w)=\int_0^\infty W(u)u^{w-1}du .
$$

In the initial half-plane $\Re s>1$, $R(s)=\int_1^\infty S_\chi(x)x^{-s-2}dx$, and the corresponding transform $F_b$ of $G_b$ converges absolutely. Write $b_*=(1+\kappa)/2$, take $e=(1-\kappa)/12$, and choose $A>(1-b_*+e)/\kappa$ and $0<d<(1-\kappa)A/3$. For $1+d<\Re s<1+2d$, substitute $x=nu$ and apply Mellin inversion to $W(n^{1-\kappa}/u^\kappa)$. Absolute convergence at $h=d/(2\kappa)$ gives

$$
 F_b(s)=\frac1{2\pi i}\int_{(h)}
   \widehat W(w)M_b(s+(1-\kappa)w)R(s-\kappa w)\,dw.
$$

Shift to $\Re w=-A$. The two poles crossed are $w=0$ and $w=(1-s)/(1-\kappa)$, with the second removable if $\mu=0$. The result is

$$
 F_b(s)=M_b(s)R(s)+\frac{\mu}{1-\kappa}
 \widehat W\!\left(\frac{1-s}{1-\kappa}\right)
 R\!\left(\frac{s-\kappa}{1-\kappa}\right)+E(s).                 \tag{1}
$$

Here $E$ is holomorphic throughout $b_*-e<\Re s<1+2d$. On the new contour the prime series converges absolutely, and the Hurwitz factors are evaluated strictly to the left of their pole. These factors have polynomial vertical growth on compact strips, and $\widehat W$ has rapid decay there by integrating against $W'$. The apparent residues at $s=1$ cancel, since $M_b$ has residue $\mu$ and $\widehat W$ has residue one at zero.

With $A_\psi=-L'/L(\cdot,\psi)$, the exact prime-power subtraction in $\Re s>1/3$ is

$$
 P_\chi(s)=A_\chi(s)-A_\eta(2s)-
 \sum_p\sum_{\substack{\ell\ge3\\\ell\ {\rm odd}}}
 \chi(p)^\ell(\log p)p^{-\ell s}.
$$

The last sum converges normally. For real $s>0$, the real part of $L(s,\chi)$ is positive by pairing the residues $1,4\bmod5$. Also $L(s,\eta)>0$, since each block for $f(n)=n^{-s}$ equals
$(f(5m+1)-f(5m+2))-(f(5m+3)-f(5m+4))>0$ by strict convexity. Thus $F_b$ and its reflected conjugate are regular at every real $s\ge b_*$. The lower edge $b_*-e$ maps under $s\mapsto(s-\kappa)/(1-\kappa)$ to $5/12>1/3$.

## Two shifted poles and a uniform lower bound for their residues

Take the two simple critical zeros $\rho_j=1/2+i\gamma_j$ with ordinates in the signed dyadic brackets beginning at $-69338619/2^{24}$ and $103743227/2^{24}$, each of width $2^{-24}$. They have $\gamma_1\approx-4.132904,\ \gamma_2\approx6.183578$. At $s_j=\kappa+(1-\kappa)\rho_j$, the direct term $M_b(s_j)R(s_j)$ is regular, and $F_b$ is regular at $\bar s_j$. Each $s_j,\bar s_j$ lies strictly to the right of the critical line, at height less than $6.19$. The finite mod-five certificate counts all 13 zeros of $L(\cdot,\chi)$ in the closed range $|\Im s|\le22$ and places each on the critical line. This excludes direct and reflected poles for every $0<\kappa<1$. The factor $L(2s_j,\eta)$ is nonzero by its Euler product, as $\Re(2s_j)=1+\kappa$. The accompanying verifier also proves the whole moving-segment exclusion independently below. It checks $L(\bar\rho_j,\chi)\ne0$ and $L(2\rho_j,\eta)\ne0$ on the original brackets. At $\kappa=21/100$ it checks that all five values

$$
 L(\bar\rho_j,\chi),\quad L(s_j,\chi),\quad L(\bar s_j,\chi),
 \quad L(2\rho_j,\eta),\quad L(2s_j,\eta)
$$

are nonzero. For the real character $\eta$ this includes the conjugate points. Thus only the moving-mean term in (1) contributes a residue to $\widetilde g(s)=(\bar zF_b(s)+z\overline{F_b(\bar s)})/2$ at $s_j$. [Finite completeness in the closed range, including both signs of the ordinate](https://github.com/willzh0/riemann-masullo/blob/53cac8a4461b84ad1d9c96ea2305f48e82ba4a31/PROOF.md).

$$
 r_j=-\frac{\bar z\,\mu\,\widehat W(1-\rho_j)}
                  {2\rho_j(1+\rho_j)}.                         \tag{2}
$$

The change of variable in $R$ cancels $1/(1-\kappa)$ in (1). The two simple critical zeros and the required exclusions are checked on the whole input intervals, using the Hurwitz representation and the standard odd-character functional equation. The Hardy function used here is the real part of

$$
 \bar{\epsilon}^{\,1/2}
 \frac{\Gamma(3/4+it/2)}{|\Gamma(3/4+it/2)|}
 (5/\pi)^{it/2} L(1/2+it,\chi),\qquad
 \epsilon=\sqrt{(5+\sqrt5)/10}+i\sqrt{(5-\sqrt5)/10}.
$$

The expression is real on the critical line by the functional equation and this radical value of the odd quartic Gauss sum. The script verifies opposite endpoint signs, a nonzero derivative and a strictly positive projection of the derivative on its midpoint direction. The last check gives uniqueness in each bracket. [Functional equation and Gauss sum conventions](https://dlmf.nist.gov/25.15#ii) · [Earlier mod-five zero calibration and initial brackets](https://github.com/willzh0/riemann-masullo/blob/53cac8a4461b84ad1d9c96ea2305f48e82ba4a31/PROOF.md).

For the independent segment check, write $s(k)=\rho+k(1-\rho)$, $0\le k\le1$. The partial sums $A(t)=\sum_{n\le t}\chi(n)$ satisfy $|A(t)|\le\sqrt2$. Differentiating $L(s,\chi)=s\int_1^\infty A(t)t^{-s-1}dt$ gives $|L'|<43,\ |L''|<170$ on $\Re s\ge1/2,\ |s|\le7$, since the integrals with weights $1,\log t,(\log t)^2$ are $1/\sigma,1/\sigma^2,2/\sigma^3$. Partition $[0,1]$ into 1,024 equal cells. On a cell, a midpoint evaluation of $L$ or $L'$ changes by at most $43d$ or $170d$, respectively, with $d=|1-\rho|/2048$. On $k\le1/32$ the projection of $L'(s(k))$ onto the unit direction of the derivative at the center of the input zero bracket exceeds $0.66$ for both roots. Integrating $L'$ along the straight segment proves $L(s(k))\ne0$ for $0<k\le1/32$. On the rest of both segments the lower bound for $|L(s(k))|$ exceeds $0.053$, and the lower bound for $|L(\bar s(k))|$ over both complete reflected segments exceeds $0.037$. All midpoint evaluations enclose the uncertainty in the input zero bracket. The verifier removes the common Hurwitz pole before evaluating near $s=1$.

Set $g_j=|\gamma_j|$, $z_j=\tfrac12+ig_j$, $L=\log 2$, $\lambda_1=7-2i,\ \lambda_2=-4+5i$. The following two-frequency inequality is valid throughout $0\le v\le L$:

$$
 p(v)=\Re\sum_{j=1}^2\lambda_j e^{ig_jv}
 =7\cos(g_1v)+2\sin(g_1v)-4\cos(g_2v)-5\sin(g_2v)>\tfrac1{100}.
$$

The verifier encloses each trigonometric function on each of 8,192 closed intervals covering the full range, using the original whole zero brackets. The smallest certified lower bound exceeds $0.0187$. It also verifies

$$
 B=\Re\sum_{j=1}^2\lambda_j/z_j>0.47638,\qquad
 D=\sum_{j=1}^2 2|\lambda_j|\,|z_j(1+z_j)|<772.02,\qquad
 B/D>617/10^6 .
$$

Since $\widehat W(z_j)=1/z_j+\int_0^L W(e^v)e^{v/2}e^{ig_jv}dv$,

$$
 \Re\sum_j\lambda_j\widehat W(z_j)
   =B+\int_0^L W(e^v)e^{v/2}p(v)\,dv\ \ge B .
$$

Reality of $W$ gives $|\widehat W(z_j)|=|\widehat W(1-\rho_j)|$. By (2) and the triangle inequality, $\max_j|r_j|\ge|\mu|B/D>617|\mu|/10^6$. This proof uses only nonnegativity of $W$ on its transition interval.

## Passage from residues to signed fourth-power prefixes

First consider a continuous one-sided bound $\pm g(x)\le K x^{1+b_*}$ for large $x$. After deleting a finite initial interval, the complement $h(x)=Kx^{1+b_*}\mp g(x)$ is nonnegative. Its continued Mellin transform on the real axis to the right of $b_*$ is $K/(s-b_*)\mp\widetilde g(s)$ plus an entire function. Landau's positivity theorem implies convergence of the defining integral throughout $\Re s>b_*$. Indeed, at a finite real abscissa of convergence, a regular continuation would permit Taylor expansion about a nearby real point to its right. The positive Taylor terms for a displacement to the left sum under the integral by monotone convergence, giving convergence across the abscissa. Hence

$$
 |\widetilde h(s_j+u)|\le\widetilde h(b_*+u),\qquad u>0 .
$$

Multiply by $u\downarrow0$. Real regularity of $\widetilde g$ at $b_*$, and its residue of modulus $|r_j|$ at $s_j$, give $K\ge |r_j|$ for either sign.

For the fourth-power grid, let $X=j^4,\ H=(j+1)^4-j^4\asymp X^{3/4}$. Uniformly on $[X,X+H]$, $G_b$ differs from its linear endpoint interpolant by $O_{b,W,\kappa}(H^2\log X)$. To see this, write $w_n(x)=W(n/x^\kappa)$ and $T_n(x)=\sum_p\chi(p)\log p\,(x-np)_+$. The ordinary part of $G_b''$ is $\sum_n b(n)(2w_n'T_n'+w_n''T_n)$. The weight derivatives of orders $r=1,2$ are $O_{W,\kappa}(X^{-r})$ and supported on $n\asymp X^\kappa$. Chebyshev's bound gives $T_n'\ll X/n,\ T_n\ll X^2/n$, so the ordinary part is $O_{b,W,\kappa}(1)$. The remaining second derivative is atomic at $m=np$. Its total variation on the cell is at most $\|b\|_\infty\sum_{X\le m\le X+H}\sum_{p\mid m}\log p\ll_b(H+1)\log X$. The chord interpolation kernel is bounded by $H$. As $1+b_*=3/2+\kappa/2>3/2$, this error is $o(X^{1+b_*})$. An eventual grid bound transfers to the same continuous bound up to $o(X^{1+b_*})$, because $(X+H)/X\to1$. This proves the first limsup.

For the cumulative claim put $q=5+4b_*=7+2\kappa$, $u_j=[g(j^4)]_+$, and suppose that $\sum_{j\le J}u_j\le KJ^q$ eventually. Let $I_\pm(s)=\int_1^\infty[\pm g(x)]_+x^{-s-2}dx$ where convergent. Convexity of the positive part, the chord estimate and integration over the adjacent cells yield, uniformly for $0<u\le1/4$,

$$
 I_+(b_*+u)\le4\sum_{j\ge1}u_jj^{-q-4u}+O_{b,W,K}(1).
$$

Indeed each affine endpoint weight integrates to half its cell width before insertion of $x^{-b_*-u-2}$; the combined weight of node $j$ is $(4+O(j^{-1}))j^{-q-4u}$. The $O(j^{-1})$ error is summable under the assumed prefix bound, and the chord error integrates absolutely already at $u=0$. Partial summation gives $\limsup_{u\downarrow0}u I_+(b_*+u)\le qK$. In particular $I_+$ is holomorphic in $\Re s>b_*$. The continuation $I_-=I_+-\widetilde g$ is regular at all real points to the right of $b_*$. Positivity gives convergence there as before. At the real boundary the difference $I_-(b_*+u)-I_+(b_*+u)$ is bounded. Consequently

$$
 |r_j|\le\limsup_{u\downarrow0}u\big(I_+(b_*+u)+I_-(b_*+u)\big)\le2qK .
$$

Take $K$ down to the positive prefix limsup and apply the same argument to $-g$. This gives the claimed constants for both signs.

## An independent qualitative compactness check

The larger, four-node set provides an additional proof that some residue stays uniformly positive. Use the preceding two zeros together with the critical zeros of ordinates near $8.457229,-9.442931$, whose brackets and nonvanishing tests are also replayed by the script. For any admissible $W$, the entire function

$$
 E_W(z)=z\widehat W(z)=1+z\int_0^{L}W(e^v)e^{zv}\,dv
$$

is real under conjugation, satisfies $E_W(0)=1$, and has
$|E_W(z)|\le(1+|z|L)e^{L\max(\Re z,0)}$. The eight points $1-\rho_j,1-\bar\rho_j$ are distinct; their pair radii are bounded above respectively by $4.2,6.3,8.5,9.5$. If all eight were zeros, Jensen's formula at radius $36$ would give

$$
 13.3<2\log\!\left(\frac{36^4}{4.2\cdot6.3\cdot8.5\cdot9.5}\right)
 \le\log(1+36L)+36L/\pi<11.3 .
$$

A radius approaching $36$ handles any boundary zero. If the maximum of the four transform moduli could approach zero along cutoffs, their entire functions $E_W$ would have a locally uniformly convergent subsequence by the common envelope. The limit would have the same envelope, value one at zero and all eight prescribed zeros, contradicting Jensen again. This supplies a uniform strictly positive lower bound independently of the explicit two-frequency test.

Run the accompanying verifier with Python and python-flint 0.8.0.

    python verify_moving_mean.py

It checks both 128-bit and 192-bit precision, with outward-rounded balls throughout. The only input specific to a zero is an integer bracket endpoint. Computing the Hurwitz zeta values, derivatives, Hardy signs, reflected values and interval inequalities forms part of each replay.
