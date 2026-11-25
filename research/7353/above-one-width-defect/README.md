# Opposite signs for a polar-free theta width trace

Masullo, §12.3, p. 514, and Theorem 12.5.1.1, pp. 519–520. Work over $\mathbb Q$ on the principal angular row with theta center $a=0$, narrow half-width $\alpha=1/4$, wide half-width $\beta=3/4$ and common Sobolev order $s=2$. Write $J$ for restriction. For the compact tests below, the wide-minus-narrow zero sum has the following signs.

| Additional log-norm translation $y$ | Enclosure |
|---:|---:|
| $0$ | $[2.8190,2.8555]$ |
| $1/4$ | $[-2.5528,-2.5089]$ |

With the nuclear convolutions in the project's signed trace theorem, this sum equals $\operatorname{Tr}(T_\beta|_{\ker J})$. Under the mixed nuclear factorization in the finite-theta calculation, this is the value of its rank-first, cutoff-second iterated limit; cutoff-first gives zero. The pull requests and earlier written argument supply those operator identifications. The enclosures below are an independent zero-side calculation. The paper's comparison at center $a=1/2$ remains open. [Signed trace on actual quotients, #7630](https://github.com/mccorvie/riemann-masullo/pull/7630) · [Finite-theta iterates and their hypotheses, #7626](https://github.com/mccorvie/riemann-masullo/pull/7626#issuecomment-7154316204) · [Lost-jet trace formula](https://github.com/mccorvie/riemann-masullo/pull/7609#issuecomment-7154139717)

## Test and coefficients

Let $\kappa$ be any real even nonnegative smooth probability density on $[-\epsilon,\epsilon]$, $\epsilon=2^{-32}$. For example normalize $\exp(-1/(1-(x/\epsilon)^2))$ on $|x|<\epsilon$ and extend by zero. Convolve $\kappa$ with 16 copies of normalized Lebesgue measure on $[-1/16,1/16]$ to obtain $g$. Put
$$
P(z)=(z^2-\tfrac14)z(z-1),\qquad
H(x)=10^{-4}P(-\partial_x)g(x-7/4),\qquad
\varphi_y(u)=V^{-1}H(\log|u|-y).
$$
Here $V$ is the volume of the norm-one classes in the project's kernel-times-logarithmic-Haar decomposition. Every $y\ge0$ gives a genuine compact smooth test supported above norm one: its log support lies in $[y+3/4-\epsilon,y+11/4+\epsilon]$. With the positive-exponent bilateral transform,
$$
\widehat H_y(z)=10^{-4}e^{(7/4+y)z}P(z)
\left(\frac{\sinh(z/16)}{z/16}\right)^{16}\widehat\kappa(z).
$$
It vanishes at both printed polar moments $\pm1/2$ and at the recentered moments $0,1$. Orthogonality on the compact kernel selects the principal row; $V^{-1}$ cancels its Haar volume. The sign of the translation follows directly from the project's Mellin integral $\int \varphi(u)\chi(u)|u|^z\,du$. [Above-one test class](https://github.com/mccorvie/riemann-masullo/issues/7353#issuecomment-7148058188) · [Project trace expansion](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec3.lean#L2810)

For each positive-order nontrivial zeta zero $\rho=\sigma+i\gamma$, let $d_\rho=n_\beta(\rho)-n_\alpha(\rho)$, where $n$ counts the jets retained at that width. Then $0\le d_\rho\le m_\rho$. At $\sigma=1/2$ the number is exactly $m_\rho$. The signed series is
$$
D(y)=\sum_\rho d_\rho\,\widehat H_y(\rho).
$$
Conjugation pairs terms so $D(y)$ is real. At $s=2$ the narrow edge $\sigma=1/4$ loses $m_\rho-1$ orders and the wide edge $\sigma=3/4$ contributes one. Both are covered by the upper bound on $d_\rho$. Nothing is assumed about zeros above the finite cutoff.

## Completing the zero list through height 64

The first script uses only the integers $1,\ldots,256$ in its two Dirichlet sums. To recover Hardy signs at $t\le68$, average finite alternating sums cut at a binomial random index with parameters $256,2/3$ and divide by $1-2^{1-s}$, $s=1/2+it$. In the Mellin integral for the alternating series the omitted geometric remainder has factor $\mathbb E[(-e^{-x})^B]=((1-2e^{-x})/3)^{256}$. Its modulus is at most $3^{-256}$. The gamma identity on the line and $|1-2^{1-s}|\ge\sqrt2-1$ bound the absolute error by $(\sqrt2+1)\sqrt{\cosh(68\pi)}/3^{256}$. Rotate by the Hardy phase. Opposite endpoint signs and 32 further bisections give 16 disjoint positive brackets from the quarter-interval seeds in the script, including two just above 64. [Finite binomial construction](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7153429283)

For each integer $0\le k\le64$, the Hadamard product and reflection give
$$
S_k=\Re(\xi'/\xi)(2+ik)
=\sum_\rho m_\rho\frac{2-\sigma}{(2-\sigma)^2+(k-\gamma)^2}.
$$
One may see the additive Hadamard constant cancel by taking the logarithmic derivative at the reflected point $-1+ik$ and subtracting. Bound $\zeta(2+ik)$ and its derivative with ordinary sums to 256 and integral-test tails $1/256$ and $(1+\log256)/256$. Subtract one guaranteed central contribution from each of the 32 signed brackets, using the more distant endpoint. The largest resulting upper bound is below $0.161586$. Every missed zero with $|\gamma-k|\le1/2$, including any extra multiplicity at a detected zero, would add at least $8/17$ by $1\le 2-\sigma\le2$. This proves that precisely 14 positive simple zeros occur through height 64, all central. The two later brackets contribute to this completeness check and are excluded from the finite trace sum. This is a small use of the classical shifted positive-resolvent test of Hiary, Ireland and Kyi. [Theorem 11](https://arxiv.org/html/2408.00187v1#S5)

## Bounding every remaining term

At each of the 14 enclosed positive sites, pair the reflected height and evaluate the polynomial, exponential and 16 box factors by interval arithmetic. Omitting $\widehat\kappa(z)$ costs a relative error at most $\epsilon |z|\exp(\epsilon|\Re z|)$, by integrating the difference from 1 against a probability measure. Before division by $10^4$, the two finite reference sums are within $0.001$ of $28372.45709$ and $-25308.46217$. The entire finite mollification errors are each below $0.00014$.

For $T=64$ and any contributing $\rho$ with $|\gamma|>T$, the four polynomial factors and normalized box transform satisfy
$$
|P(\rho)|\le(1+(5/(4T))^2)^2|\gamma|^4,\qquad
\left|\frac{\sinh(\rho/16)}{\rho/16}\right|\le \frac{16\cosh(3/64)}{|\gamma|}.
$$
The positive kernel at $k=0$ also gives $\sum_{|\gamma|>T}m_\rho/\gamma^2\le(1+4/T^2)\Re(\xi'/\xi)(2)<3$. Indeed $\Re(\xi'/\xi)(2)=3/2-(\log\pi+\gamma_E)/2+\zeta'(2)/\zeta(2)<3/2$. Thus at profile center $c=7/4+y$ the complete unscaled unknown tail is bounded by
$$
3(1+(5/(4T))^2)^2 e^{3(c+\epsilon)/4}
  (16\cosh(3/64))^{16}T^{-10}.
$$
It is less than $182$ and $220$ respectively. The script uses the unrounded bounds and encloses the signed totals in the intervals in the table.

The independent verifier uses a 300-bit evaluation of the zero count and ordinates. It checks all 32 endpoint signs and the 65 true log derivatives directly. It also evaluates the 16-fold box transform with its 17-term binomial finite-difference formula. The sharper centered arithmetic bound and evenness of the mollifier give enclosures $[2.8364,2.8381]$ and $[-2.5319,-2.5298]$. The first certificate requires none of those direct zeta calls.

## Arbitrarily late positive and negative traces

For this same test, $a_\rho=d_\rho\widehat H_0(\rho)$ are absolutely summable and $D(y)=\sum a_\rho e^{\rho y}$. The four moments annihilate real polynomial roots, and its first critical zero $\rho_0=1/2+i\gamma_0$ satisfies $|a_{\rho_0}|>1.1364$ from the first bracket.

Here is the signed endpoint argument. The Laplace transform of $D$ in $\Re w>3/4$ has meromorphic continuation $R(w)=\sum_\rho a_\rho/(w-\rho)$. This follows by absolute convergence, local finiteness and uniform convergence off the poles. Every nonzero coefficient gives its own residue. There are no real poles: $\zeta(x)$ has no zeros for $0<x<1$, by the positive alternating eta series. If a visible pole lies strictly to the right of $1/2$, an eventual upper bound $D(y)\le C e^{y/2}$ would make $C e^{y/2}-D(y)$ nonnegative on a tail. Its Laplace transform is analytic at every real point greater than $1/2$, so its abscissa of convergence is at most $1/2$ by Landau's positive-transform principle. It could then have no nonreal pole in that half-plane, a contradiction. Apply the argument also to $-D$. The principle follows by Taylor expansion about a real point just right of the putative abscissa and summation of nonnegative moment terms. [Continuous signed Landau theorem, #7555](https://github.com/mccorvie/riemann-masullo/pull/7555)

If every visible site has real part at most $1/2$, then $f(y)=e^{-y/2}D(y)$ is bounded. Cesàro averaging termwise gives mean zero and Fourier coefficient $a_{\rho_0}$ at frequency $\gamma_0$. If $f(y)\le M$ eventually, positivity of $M-f$ on that tail yields $|a_{\rho_0}|\le M$ by taking the modulus of its Fourier mean. Apply the same argument to $-f$. Consequently, in both cases,
$$
 \limsup_{y\to\infty} e^{-y/2}D(y)\ge |a_{\rho_0}|,\qquad
 \liminf_{y\to\infty} e^{-y/2}D(y)\le -|a_{\rho_0}|.
$$
This is a signed growth result for the off-center restriction family. The centered comparison in §12.3 still requires its own estimate.

## Reproduction

Use Python with python-flint 0.9.0. In this directory run the following commands.

```shell
python certificate.py
python verify.py
```

Each script writes its JSON receipt beside itself. The operator interpretation credits mlyle's restriction and finite-projection constructions and mrshu's signed trace and iterated-limit argument. The new calculation and signed bounds concern their lost-jet scalar on the restricted physical test class.

The [prime-side calculation and short-support proof](PRIME-SIDE.md) independently evaluate the full trace from 8 and 11 prime powers. They also recover the contribution of each rational prime power from arbitrarily short, polar-free tests.
