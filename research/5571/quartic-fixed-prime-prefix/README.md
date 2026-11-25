# An unrestricted complex quartic prime prefix through 27,173,860

Let $\chi$ be the primitive character modulo five with $\chi(2)=i$. Its unsmoothed triangular prime sum satisfies
$$
R(x)=\sum_p\chi(p)(x-p)_+\log p,\qquad
\boxed{\ \sum_{j=1}^J |R(j^4)|<J^7\quad(1\le J\le 27{,}173{,}860).\ }
$$
The modulus is taken separately at each sample, so the maximizing phase may change with $j$. Complex conjugation gives the same bound for $\bar\chi$. The normalized upper bound at the final integer is $0.999999979753299$. Every prime below $j^4$ enters this triangular sum. The separate compact annular statistic $Q_\chi(j)$ has its own finite-range estimates. The cofinal bound for this fixed character remains open.

Michael Lyle established the same inequality through $8{,}000{,}000$. His proof supplies the direct complex prime table, the triangular explicit formula, and the choice of phase in the physical interpolation. The extension below uses the quadratic signs of the prime squares, a mean-one kernel with sharply localized Mellin frequencies and an explicit integral of the Brun–Titchmarsh error. A separate lognormal calculation below reaches $15{,}354{,}595$ with the same original observable. [Mlyle’s pinned proof, code and receipts](https://github.com/mlyle/riemann-masullo/tree/3f90b6c75f2e36f52c2c9cb427155a556bcee9d8/research/5571/quartic-mod-five-deficit) · [Original issue report](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7155477595)

## The complex explicit formula and the signed squares

Write $\rho=b+i\gamma$ for a nontrivial zero of $L(s,\chi)$, counted with multiplicity, and put
$$
T(y)=\sum_\rho \frac{y^{1+\rho}}{\rho(1+\rho)},\qquad H=20{,}000{,}000.
$$
Platt verifies $b=1/2$ for $|\gamma|\le H$. The completed logarithmic derivative gives
$$
B=\log(5/\pi)-\gamma_E+2\Re\frac{L'(1,\chi)}{L(1,\chi)}
  =2\sum_\rho\Re\frac1{1-\rho}=0.20322143257953435\ldots .
$$
For the verified zeros, $|\rho(1+\rho)|^{-1}\le|\rho|^{-2}=2\Re(1/(1-\rho))$, so their coefficient mass is at most $B$. For $|\gamma|>H$, reflection $b+i\gamma\mapsto1-b+i\gamma$ within the same character gives $\sum(1+\gamma^2)^{-1}\le B$ on that set. Indeed $2(1-b)/((1-b)^2+\gamma^2)\ge 2(1-b)/(1+\gamma^2)$ and the reflected pair has summed numerator two. Thus the high coefficient mass is at most $2B$. Both estimates count the positive and negative ordinates of this one nonreal character. [Pinned Hadamard and residue calculation](https://github.com/mlyle/riemann-masullo/blob/3f90b6c75f2e36f52c2c9cb427155a556bcee9d8/research/5571/quartic-mod-five-deficit/README.md#the-unrestricted-smoothed-estimate) · [Platt, Theorem 7.1](https://arxiv.org/pdf/1305.3087#page=14)

The square term has real coefficients $\chi^2(p)$ with signs $+,-,-,+$ in the four reduced residue classes. Set $t_0=8\cdot10^9$ and $A(t)=\sum_{p\le t}\chi^2(p)\log p$. For $t\ge t_0$, the four main terms $t/4$ cancel. The error in each class is at most $t/(840\log t)$, so $|A(t)|\le t/(210\log t_0)$. For $t<t_0$ use $|A(t)|\le(\log4)t$. Consequently, for every $y>0$,
$$
\left|\sum_p\chi^2(p)(y-p^2)_+\log p\right|
=\left|\int_0^{\sqrt y} 2t A(t)\,dt\right|
\le C_0+c_s y^{3/2},\qquad
C_0=\tfrac23(\log4)t_0^3,\quad c_s=(315\log t_0)^{-1}.
$$
These estimates include the conductor prime with $\chi(5)=0$. [Bennett–Martin–O’Bryant–Rechnitzer, *Explicit bounds for primes in arithmetic progressions*, Theorem 1.2 and (1.10)–(1.12)](https://personal.math.ubc.ca/~andrewr/pubs/EBPAP.pdf#page=5)

For $y>1$ the triangular Perron formula for $-L'/L$ gives the sum over all prime powers as $-T(y)$ plus the affine and trivial-zero residues. In the pinned proof, their combined norm is at most $4y+8$. One obtains this by bounding the two complex logarithmic-derivative constants in the residues at $0,-1$ by one. The absolute weight at exponents at least three is at most $11y^{4/3}$ by Chebyshev’s bound $\vartheta(u)\le(\log4)u$. For $y\le1$ the prime sum is zero and $|T(y)|\le3By$. We therefore have, for the full complex quantity,
$$
|R(y)+T(y)|\le C_0+c_s y^{3/2}+11y^{4/3}+4y+8\qquad(y>0).
$$
[Complex residue and proper-power bounds](https://github.com/mlyle/riemann-masullo/blob/3f90b6c75f2e36f52c2c9cb427155a556bcee9d8/research/5571/quartic-mod-five-deficit/README.md#full-complex-norm-with-a-different-phase-at-each-sample)

## A mean-one multiplier on the full strip

Choose $K=19{,}998{,}000$, $\sigma=1/200$ and $g(s)=\cos(\pi s/K)\mathbf1_{|s|\le K/2}$. For the unitary Fourier transform $\widehat g(z)=(2\pi)^{-1/2}\int e^{-isz}g(s)\,ds$, let $p(z)=|\widehat g(z)|^2/\|g\|_2^2$. This is an even probability density. The endpoint values of $g$ vanish, so extension by zero preserves its square-integrable first derivative. Plancherel and autocorrelation give
$$
V=\int z^2p(z)\,dz=\frac{\|g'\|_2^2}{\|g\|_2^2}=\frac{\pi^2}{K^2},\qquad
\phi(t)=\int e^{itz}p(z)\,dz,\qquad |\phi(t)|\le1,\quad \phi(t)=0\ (|t|>K).
$$

Give $Z$ the density $D^{-1}e^{-z/2-z^2/(2\sigma^2)}p(z)$ and set $Y=e^Z$. By evenness, $\mathbb E Y=1$. Inside the integral defining $D$ we may replace $e^{-z/2}$ by $\cosh(z/2)$, yielding $D\ge d_0=1-V/(2\sigma^2)>0$. For real $r$, completing the square bounds $\mathbb E Y^r$ by $M_r=d_0^{-1}e^{(r-1/2)^2\sigma^2/2}$.

For $a=b+1/2$ and the centered normal density $\eta(t)=\sigma e^{-\sigma^2t^2/2}/\sqrt{2\pi}$, Fourier inversion gives
$$
\mathbb E Y^{1+\rho}
=\frac{e^{a^2\sigma^2/2}}D\int_{\mathbb R}\eta(t)e^{-ia\sigma^2t}\phi(\gamma+t)\,dt .
$$
At $b=1/2$ its modulus is at most $M_{3/2}$. For $0\le b\le1$ and $|\gamma|>H$, all contributing $t$ lie in one Gaussian tail at distance at least $H-K$. The exponential Markov bound gives
$$
|\mathbb E Y^{1+\rho}|\le M_{\rm hi}
=d_0^{-1}\exp\bigl(9\sigma^2/8-\sigma^2(H-K)^2/2\bigr).
$$
The zero series may be integrated term by term since its coefficient masses are summable and $(xY)^{1+b}\le xY+(xY)^2$.

The physical estimates use three further moments. With
$$
A_1=\sqrt V\,e^{\sigma^2/8}/d_0,\qquad
C_2=e^{9\sigma^2/8}/d_0,\qquad
C_3=\sigma\sqrt{2/e}\,e^{9\sigma^2/4}/d_0 ,
$$
we have $\mathbb E|Z|\le A_1$, $\mathbb E(Y-1)^2\le VC_2$, and $\mathbb E[(Y-1)^2|Z|]\le VC_3$. For the first estimate use Cauchy–Schwarz for $p$ and the supremum of $e^{-z/2-z^2/(2\sigma^2)}$. For the other two use $|e^z-1|\le |z|e^{\max(z,0)}$ and $2\max(z,0)-z/2\le3|z|/2$. For the mixed moment, $\sup |z|e^{-z^2/(4\sigma^2)}=\sigma\sqrt{2/e}$ and $\sup e^{3|z|/2-z^2/(4\sigma^2)}=e^{9\sigma^2/4}$. This retains the factor $\int z^2p(z)\,dz=V$.

## Returning to each physical prime sum

At each $x=j^4$ with $j>m\ge2$ choose $|u_j|=1$ such that $-\Re(u_jR(x))=|R(x)|$. The convex, nonnegative interpolation error at a prime is
$$
h_p=(xY-p)_+-(x-p)_+-(xY-x)\mathbf1_{p<x}.
$$
The tangent term has zero expectation. On the side of $x$ toward $xY$, the error is $(d-|p-x|)_+$ with $d=x|Y-1|$. On the other side it vanishes. Thus $|R(x)|$ is at most $|\mathbb E R(xY)|$ plus the expected sum of $h_p\log p$ weighted by the positive parts of $\Re(u_j\chi(p))$. Across the four classes these weights add to at most $\sqrt2$ for every $j$.

Fix one reduced class and let $n(t)$ count its primes within distance $t$ on the relevant side, $0<t\le d$. The integer $x=j^4$ is composite, so $n(t)\le t$. For $t>5$ the Brun–Titchmarsh interval estimate gives $n(t)\le t/[2\log(t/5)]$ up to endpoints of measure zero. The intervals to the left start at $x-t>0$ since $xY>0$. The logarithms of all counted primes are at most $\log x+|Z|$. Hence the one-class triangular cost is bounded by $(\log x+|Z|)\int_0^d n(t)\,dt$. [Montgomery–Vaughan, *The large sieve*, Theorem 2, (1.10)](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf#page=3)

Set $s=x^\beta$, $r=\lambda x^{3/4}$, and $\ell_u=\log(u/5)$, with the choices below ensuring $5e<s<r$. For $s\le t\le r$ put $w=\log(r/t)$. The exact identity
$$
1/\ell_t=1/\ell_r+w/\ell_r^2+w^2/(\ell_t\ell_r^2)
$$
bounds the excess over $1/\ell_r$ by $w/\ell_r^2+w^2/(\ell_s\ell_r^2)$. For $t\ge r$ the excess is nonpositive. Integrating the two corrections uses $\int_0^r t\log(r/t)\,dt=\int_0^r t\log^2(r/t)\,dt=r^2/4$. Together with $n(t)\le t$ below $s$, this gives the uniform bound
$$
\int_0^d n(t)\,dt\le
\frac{s^2}{2}+\frac{r^2}{8\ell_r^2}\left(1+\frac1{\ell_s}\right)
+\frac{d^2}{4\ell_r}.
$$

## Summing the prefix

For $N\le J\le U$ write $P(k)=1/(k+1)+1/N$. An integral comparison gives $\sum_{j\le J}j^k\le P(k)J^{k+1}$ for $k\ge0$. Let $L_m=4\log m$, $a_s=\beta-\log5/L_m$ and $a_r=3/4+\log(\lambda/5)/L_m$. For $j>m$, $\ell_s\ge a_s\log x$, $\ell_r\ge a_r\log x$. The first $m$ samples cost at most $0.930294(m/N)^7$ by mlyle’s complex certificate. All displayed values of $m$ lie between $100{,}000$ and $8{,}000{,}000$.

The contributions below bound $\sum_{j\le J}|R(j^4)|/J^7$ uniformly on each interval. Summing nonnegative contributions up to $J$ also bounds the sums starting at $m+1$. The derivative test $(8\beta-6)(4\log N+A_1)+4<0$ makes $(4\log J+A_1)J^{8\beta-6}$ decrease for $J\ge N$.

| Contribution | Upper bound |
| --- | --- |
| Inherited prefix | $0.930294(m/N)^7$ |
| Low zeros | $B M_{3/2}P(6)$ |
| Signed squares | $c_s M_{3/2}P(6)+C_0/N^6$ |
| Higher prime powers | $11 M_{4/3}P(16/3)N^{-2/3}$ |
| Affine terms | $4P(4)/N^2+8/N^6$ |
| High zeros | $2B M_{\rm hi}P(8)U^2$ |
| Short curvature | $\sqrt2(4\log N+A_1)P(8\beta)N^{8\beta-6}/2$ |
| Middle curvature | $\sqrt2\lambda^2(1+A_1/L_m)(1+1/(a_sL_m))P(6)/(8a_r^2L_m)$ |
| Bulk curvature | $\sqrt2 V(C_2+C_3/L_m)P(8)U^2/(4a_r)$ |

The first interval uses $(N,m,\beta,\lambda)=(8{,}000{,}000,2{,}350{,}000,7/11,15/4)$. Its upper bound through $U=27{,}100{,}000$ is $0.996153635007$, and through $27{,}154{,}480$ it is $0.999999935480$. The second uses $(26{,}000{,}000,7{,}500{,}000,9/14,15/4)$. Its upper bound through $27{,}160{,}000$ is $0.999020507364$, and through $27{,}173{,}860$ it is $0.999999979753299$. The two intervals overlap. At the next integer the second majorant exceeds one, which determines the endpoint for these fixed constants. [128-bit receipt](receipt-128.txt) · [192-bit receipt](receipt-192.txt)

## A lognormal check using the actual high-zero count

The sharper count of high zeros independently extends the original lognormal argument. Write $N_\chi(t)=F(t)+R_\chi(t)$ with $F(t)=t(\log(5t/(2\pi))-1)/\pi+1/4$. For $t\ge H$, the two-sided zero count in Bennett–Martin–O’Bryant–Rechnitzer gives $|R_\chi(t)|\le E(t)$ for $\ell(t)=\log(5(t+2)/(2\pi))$ and $E(t)=0.22737\ell(t)+2\log(1+\ell(t))-0.5$. Put $L=\log(5H/(2\pi))$, $d_H=0.22737+2/(1+\ell(H))$. Then $E'(t)\le d_H/t$. [*Counting zeros of Dirichlet L-functions*, Theorem 1.1](https://personal.math.ubc.ca/~bennett/BeMaObRe-MathComp-2021.pdf#page=2)

For $a\ge0$ integrate $f(t)=t^{-2}e^{-a(t/H)^2}$ over $(H,\infty)$ against $dN_\chi$. Stieltjes integration bounds the counting error by $2f(H)E(H)+\int_H^\infty fE'$. In particular the sign convention at a zero exactly on $H$ is fixed by the boundary term $-f(H)R_\chi(H)$. Using $(t/H)^2\ge1+2\log(t/H)$ bounds $f(t)$ by $e^{-a}H^{-2}(H/t)^{2+2a}$. Integrating this majorant against $F'$ gives
$$
\sum_{|\gamma|>H}\frac{e^{-a(\gamma/H)^2}}{\gamma^2}
\le G(a)= e^{-a}\left[
 \frac{L/(1+2a)+(1+2a)^{-2}}{\pi H}
 +\frac{2E(H)+d_H/(2+2a)}{H^2}
\right].
$$
At $a=0$ the main integral is exact. Bounding the error on both sides yields
$$
2.7983896642\cdot10^{-7}
<\sum_{|\gamma|>H}\gamma^{-2}
<2.7983905732\cdot10^{-7}.
$$

Take $v=c^2/J^2$, $Z$ normal with mean $-v/2$ and variance $v$, and $v_0=c^2/N^2$. Then $\mathbb E Y=1$ and $\mathbb E Y^{1+\rho}=\exp(v\rho(1+\rho)/2)$. The low bound is $M_{3/2}=e^{3v_0/8}$, and $M_{4/3}=e^{2v_0/9}$. For high ordinates, convexity in $b$ bounds the mean of $x^{1+b}e^{vb(1+b)/2}$ on the reflected pair $b,1-b$ by $(x+x^2e^{v_0})/2$. Thus the normalized high contribution is at most
$$
\tfrac12 G\bigl(c^2H^2/(2U^2)\bigr)
\bigl[N^{-2}P(4)+e^{v_0}U^2P(8)\bigr].
$$
The short and middle curvature bounds use $A_1=\sqrt{v_0+v_0^2/4}$. In bulk replace $VC_2 U^2$ and $VC_3 U^2$ by $1.0001c^2$ and $3c^2\sqrt{v_0}$ respectively. Indeed $\mathbb E(Y-1)^2=e^v-1\le1.0001v$, and $\mathbb E(Y-1)^4=e^{6v}-4e^{3v}+6e^v-3\le4v^2$ on this interval. Cauchy–Schwarz with $\mathbb E Z^2=v+v^2/4$ gives the mixed bound. The script checks the second-derivative condition $108v_0e^{6v_0}+6e^{v_0}<8$ for the fourth moment. For $(N,m,\beta,\lambda,c)=(8{,}000{,}000,2{,}340{,}000,7/11,73/20,4.13)$ the normalized bound is below $0.999999918277$ through $15{,}354{,}595$.

## Limitation of a fixed positive smoothing kernel

For each reduced residue class $a\bmod5$, put $F_a(x)=\sum_{p\equiv a(5)}(x-p)_+\log p$. The prime number theorem in arithmetic progressions gives $F_a(x)=x^2/8+o(x^2)$ by integrating $\vartheta(t;5,a)\sim t/4$. Also $0\le F_a(t)\le(\log4)t^2$ for every $t>0$. For any fixed, nonconstant positive random variable $Y$ with $\mathbb EY=1$ and $\mathbb EY^2<\infty$, dominated convergence gives the following exact leading term for the positive tangent remainder in that class.
$$
C_a(x)=\mathbb E F_a(xY)-F_a(x)=\tfrac18\operatorname{Var}(Y)x^2+o(x^2).
$$
The tangent vanishes in expectation. There are four classes, so the error is uniform in every unit phase $u$ after multiplication by the positive projected weights. The sum of those weights is $|\Re u|+|\Im u|\ge1$. Thus for any choices $|u_j|=1$ the positive-class cost used above satisfies
$$
\liminf_{J\to\infty}J^{-9}
  \sum_{j\le J}\sum_{a\bmod5}[\Re(u_j\chi(a))]_+C_a(j^4)
\ \ge\ \operatorname{Var}(Y)/72 .
$$
This uses $\sum_{j\le J}j^8\sim J^9/9$. The estimate identifies where a fixed positive-class majorant loses the critical exponent. The signed physical interpolation error may cancel, and a kernel varying with $J$ has different quantifiers. [Bennett–Martin–O’Bryant–Rechnitzer, Theorem 1.2](https://personal.math.ubc.ca/~andrewr/pubs/EBPAP.pdf#page=5)

## Replay

With Python 3 and python-flint 0.9.0, run these commands in this directory.

```sh
python check_prefix.py --bits 128
python check_prefix.py --bits 192
python check_cosine_crossings.py
```

Both runs check the same three endpoint crossings against their successor integers with outward-rounded Arb arithmetic. To reproduce the inherited eight-million segment, the original directory supplies its integer logarithm table, C++ segmented sieve and independent small-sample check. [Executable calculation](check_prefix.py) · [Mlyle’s pinned reproduction commands](https://github.com/mlyle/riemann-masullo/tree/3f90b6c75f2e36f52c2c9cb427155a556bcee9d8/research/5571/quartic-mod-five-deficit#reproduction)

We rebuilt the original complex prime table from its rational log table and segmented sieve. The sieve counted 203,280,221 primes through $256^4$. All 256 complex interval rows agreed byte for byte with the pinned table after LF normalization (SHA-256 `ebb943248405e1f046d65da3ae47ddcb1256a6d40d0576e2efcd62135222cfc3`). The original interval calculation at 128 and 192 bits reproduced its two larger-range bounds, $0.490482$ and $0.930294$ rounded up. Its separate direct integer check covered the first 32 samples. [Pinned direct and smoothed calculations](https://github.com/mlyle/riemann-masullo/tree/3f90b6c75f2e36f52c2c9cb427155a556bcee9d8/research/5571/quartic-mod-five-deficit)

An independent 180-bit audit obtained $B$ from digamma and generalized Stieltjes coefficients of the four arithmetic-progression Hurwitz series. It enclosed $B$ at $0.203221432579534352948989600680057717392319291708658$ with radius below $3.3\cdot10^{-52}$ and independently reproduced both cosine endpoint crossings and their successors. The accompanying second implementation uses the same Hurwitz expansion and solves the scalar quadratic in $U$ directly. Its final upper bound was $0.999999979753298732979$ at $27{,}173{,}860$ and $1.000000050440330549988$ at the next integer. The crossing concerns the upper bound used in this proof. [Independent-formula verifier](check_cosine_crossings.py) · [180-bit receipt](receipt-180.txt)
