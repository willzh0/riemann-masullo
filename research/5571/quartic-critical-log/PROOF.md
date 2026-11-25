# A critical-line upper bound for the quartic character modulo five

For the primitive Dirichlet character $\chi$ with $\chi(2)=i$, the 144-bit, 22-term Hurwitz ledger proves the all-height estimates

$$
\boxed{G_\chi<0.00311647}\quad\text{by a pointwise periodic tail bound},\qquad
\boxed{G_\chi<0.00195327}\quad\text{by a tail energy bound}.
$$

Both estimates use the same directly measured critical-line logarithm. The second applies the public conductor-five Abel–Plancherel theorem to the unmeasured tails. Neither estimate requires zero locations or zero counts. [144-bit ledger](hurwitz-2048/cells.csv.gz) · [Native receipt](hurwitz-2048/receipt.json) · [Independent rational check](verify_both.py) · [Tail theorem, #7716](https://github.com/mccorvie/riemann-masullo/pull/7716)

Here $G_\chi$ is the complete sum over zeros of the ordinary $L(s,\chi)$ in $\Re s>1/2$, counted with multiplicity. With $a=3/2$ and $p(t)=a/[\pi(a^2+t^2)]$, the Green identity at $s=2$ gives

$$
G_\chi=
\sum_{\Re\rho>1/2} \operatorname{ord}_\rho L\,
 \log\left|\frac{\rho+1}{2-\rho}\right|
=\int_{\mathbb R}p(t)\log|L(1/2+it,\chi)|\,dt-\log|L(2,\chi)|.
$$

The character is nonprincipal, so the reference has no pole correction. The one-sided form needed for this computation also follows directly from Jensen's disk formula, as shown below. [Green identity, #7696](https://github.com/mccorvie/riemann-masullo/pull/7696)

## The measured quantities

The cutoff is $T=2048$. Each entry rounds outwards. The Dirichlet and Hurwitz runs used the same fixed geometric grid and both signs of height. The different Taylor orders give slightly different upper sums.

| Operand | 104-bit Dirichlet, 20 terms | 144-bit Hurwitz, 22 terms |
|---|---:|---:|
| Compact log integral, upper | −0.0304089255878960 | −0.0304090254342073 |
| Euler reference at 2, lower | −0.0307643344381812 | −0.0307643344381812 |
| Both tails, periodic upper | 0.0027611583144409 | 0.0027611583144409 |
| Both tails, energy upper | 0.0015979587552050 | 0.0015979587552050 |
| Total with periodic tail, upper | 0.0031165671647259 | 0.0031164673184146 |
| Total with energy tail, upper | 0.0019533676054900 | 0.0019532677591788 |

The last two entries of the **144-bit column** certify the boxed bounds. The 104-bit certificate gives $G_\chi<0.00311657$ and $G_\chi<0.00195337$. Each total is computed from the exact rational enclosures before decimal rounding. [Both machine-readable results](RESULT.json) · [Replay instructions](README.md)

## Enclosing the compact log integral

In residue order $0,1,2,3,4$ modulo five, the character values are $0,1,i,-i,-1$. Thus $A(x)=\sum_{1\le n\le x}\chi(n)$ takes values in $\{0,1,1+i\}$. Abel summation identifies the ordinary continuation for $\sigma=\Re s>0$ and yields

$$
 L(s,\chi)=s\int_1^\infty A(x)x^{-s-1}\,dx,\qquad
 |L(s,\chi)|\le\sqrt2\,|s|/\sigma .
$$

The integral converges locally uniformly and agrees with the Dirichlet series for $\sigma>1$. For each quarter interval $[j/4,(j+1)/4]$, put $c=(2j+1)/8$ and $f_c(u)=L(1/2+i(c+u),\chi)$. On the circle $|u|=3/8$, the argument $s$ has $\Re s\ge1/8$ and $|s|\le |c|+7/8$. If $P_c$ is the Taylor polynomial through degree $K-1$, Cauchy's estimate gives

$$
\sup_{|u|\le1/8}|f_c(u)-P_c(u)|
 \le 8\sqrt2(|c|+1)\frac{3^{-K}}{1-1/3}
 \le 18(|c|+1)3^{-K}.
$$

The 104-bit run encloses the jet of the Dirichlet $L$-function at $1/2+ic+iX$. The 144-bit run explicitly forms the four residue classes

$$
L(s,\chi)=5^{-s}\big[\zeta(s,1/5)-\zeta(s,4/5)
                 +i\big(\zeta(s,2/5)-\zeta(s,3/5)\big)\big].
$$

This identity follows by grouping the absolutely convergent Dirichlet series, then by analytic continuation. Both routes use FLINT's rigorous Hurwitz arithmetic. The native Dirichlet jet performs the character-weighted residue sum internally. [Apostol's residue formula, DLMF 25.15.3](https://dlmf.nist.gov/25.15.E3) · [Johansson's rigorous Hurwitz evaluation](https://arxiv.org/abs/1309.2877) · [FLINT's pinned implementation](https://github.com/flintlib/flint/blob/v3.3.1/src/acb_dirichlet/l_jet.c#L65-L115)

Each quarter interval is subdivided into cells $[m/D,(m+1)/D]$. The dyadic denominator $D$ depends only on $|c|$ and ranges from 128 to 65,536. There are 16,384 centers and 1,573,120 cells. Complex-ball Horner evaluation encloses $P_c$ on the entire displacement interval. Adding the Cauchy remainder to the upper modulus gives $U>0$ with $|L|\le U$ everywhere on that cell. Its exact Cauchy probability is

$$
W=\frac1\pi\arctan\!\left(\frac{6D}{9D^2+4m(m+1)}\right),
$$

by subtracting the arctangents at its endpoints. The code accumulates $W\log U$ with outward rounding, retaining its sign even when $U<1$. The two half-axes are summed separately. At a zero of the nontrivial holomorphic function, the point value convention for the logarithm does not affect the integral.

One CSV row gives exact dyadic lower and upper integers, in units of $2^{-60}$, for the computed upper-sum expression on its quarter interval. The upper integer bounds the actual integral. The lower integer measures rounding of the upper sum and supplies no lower bound on the actual integral. [Quadrature source](certify.py) · [104-bit ledger](dirichlet-2048/cells.csv.gz) · [144-bit ledger](hurwitz-2048/cells.csv.gz)

## Two bounds for the omitted heights

For $t=|\Im s|\ge100$ on the critical line, set $N=5\lceil t/5\rceil$. Then $A(N)=0$ and $t\le N\le t+5$. The sum through $N$ has modulus at most $2\sqrt N$. Abel summation on $(N,\infty)$ gives

$$
 |L(s,\chi)|\le2\sqrt{t+5}
        +2\sqrt2\frac{\sqrt{t^2+1/4}}{\sqrt t}
 \le5\sqrt t .
$$

For the last step, $\sqrt{1+5/t}\le21/20$, $\sqrt{1+1/(4t^2)}\le101/100$, and $\sqrt2\le10/7$. Since $p(t)\le a/(\pi t^2)$ and $\log(5\sqrt t)>0$, integration on both tails gives

$$
\int_{|t|>T} p(t)\log|L|\,dt
\le\frac{3}{\pi T}\left(\log5+\frac{\log T+1}{2}\right).
$$

For the sharper bound, `RiemannMasullo.QuarticFive.critical_tail_energy` proves
$\int_{|t|>T}p(t)|L|^2\,dt\le E=20/\sqrt T$ for this ordinary Dirichlet character at every $T\ge1$. The exact tail probability is $\mu=2\arctan(a/T)/\pi$. Concavity of the logarithm for the conditional probability on the tail yields

$$
\int_{|t|>T}p(t)\log|L|\,dt\le\frac{\mu}{2}\log(E/\mu).
$$

One can first apply this inequality to $|L|^2+\varepsilon$ and let $\varepsilon\downarrow0$. The published theorem uses the three partial sums, Abel summation and Plancherel. [Public #7716](https://github.com/mccorvie/riemann-masullo/pull/7716) · [Exact Lean theorem at 74c19ab7](https://github.com/willzh0/riemann-masullo/blob/74c19ab745d8371574e9499815b58140dd1c1096/RiemannMasullo/ForMathlib/NumberTheory/LSeries/QuarticFiveCriticalTail.lean#L27-L37)

For a direct derivation, put $X=\sqrt T$ and subtract the Dirichlet polynomial through $N=\lfloor X\rfloor$, writing $L=P_N+sR$. Then $|P_N|\le2\sqrt X$. With angular frequency $t$, $R$ is the Fourier transform of $e^{-u/2}[A(e^u)-A(\min(e^u,N))]$ on $u>0$, extended by zero to $u\le0$. This function vanishes for $u\le\log X$. The partial sums have diameter $\sqrt2$, so Plancherel gives $\int_{\mathbb R}|R(t)|^2dt\le4\pi/X$. Now $p(t)|s|^2\le3/(2\pi)$ and $\int_{|t|>T}t^{-2}dt=2/T$. The squared triangle inequality yields a tail energy of at most $24X/(\pi T)+12/X\le20/\sqrt T$.

## The reference and a direct Green-mass comparison

At $s=2$, sum the rational complex character terms through $N=10{,}000$. This is a full-period cutoff. Abel summation bounds the omitted modulus by $\sqrt2/N^2$. The independent checker encloses every reciprocal square on a $2^{-100}$ grid, bounds the finite modulus by integer square root, and uses $3/(2N^2)$ for the remainder. It encloses logarithms by the positive inverse hyperbolic tangent series after binary range reduction, and $\pi$ by Machin's formula with alternating rational remainders. The resulting positive modulus lower bound also certifies $L(2,\chi)\ne0$. [Rational arithmetic](verify.py) · [Exact per-run comparisons](verify_both.py)

The numerical upper also bounds the ordinary Dirichlet zero sum directly. Set

$$
s(z)=\frac{2+z}{1-z}=\frac12+\frac32\,\frac{1+z}{1-z},\qquad
F(z)=(1-z)L(s(z),\chi).
$$

The Abel bound gives $|F(z)|\le 2\sqrt2|2+z|\le6\sqrt2$ in the disk and $F(0)=L(2,\chi)\ne0$. Each zero $\rho$ in the half-plane gives a zero $z_\rho=(\rho-2)/(\rho+1)$ with the same order. Jensen's disk formula and monotone convergence give the limiting radial log mean $\log|F(0)|+\sum_\rho \operatorname{ord}_\rho L\log(1/|z_\rho|)$. Apply Fatou's lemma to the nonnegative function $\log(6\sqrt2)-\log|F(re^{i\theta})|$ as $r\uparrow1$. The boundary log mean is finite and at least the radial limit. Boundary values exist off the point $1$ by analytic continuation. [Jensen's original formula, Acta Mathematica 22 (1899), pp. 359–364](https://doi.org/10.1007/BF02417878)

The factor $\log|1-e^{i\theta}|$ has circle mean zero. For $r<1$ the mean of $\log|1-re^{i\theta}|$ is zero, and for $r\ge1/2$ its negative part is bounded by the integrable $\log^+(\sqrt2/|1-e^{i\theta}|)$. Finally $t=(3/2)\cot(\theta/2)$ carries circle probability to $p(t)\,dt$. This proves $G_\chi\le\int p\log|L|-\log|L(2,\chi)|$ and absolute integrability of the measured logarithm.

## Related certificates

The previously published 512-term Hardy predictor gives $G_\chi<0.039745877564$ through a finite residual. A stronger calibration, $G_\chi<2.09879293\cdot10^{-7}$, uses verified zeros through height 20,000,000 and a zero-count tail. The present certificate measures the Cauchy log mean on a fixed grid and uses the period-five coefficients for all remaining heights. [Hardy trial](https://github.com/willzh0/riemann-masullo/tree/3c3768bbadbb911dbe7af82f1b08f371c4734ee3/research/5571/quartic-hardy-trials) · [Verified-height calculation](https://github.com/willzh0/riemann-masullo/tree/da8d5a8b3252c16120606b0b513d445e88cfbd0f/research/5571/quartic-green-calibration)
