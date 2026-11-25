# One compact test for all primitive rational characters through conductor 400,000

For Masullo, Theorem 12.5.1.1, pp. 519–520, there is a single compact Bruhat test on the rational idèle classes for which the **sum of the absolute values of all omitted terms is below $3.70\cdot10^{-104}$**, at every positive strip half-width. The test sees every primitive Dirichlet character of conductor at most 400,000, including $\zeta$, and no other row. Its Mellin coefficient at the real reference $w=1/4$ is exactly one on **each** of those 29,565,923,838 rows. Its coefficient is nonzero at every possible off-central nontrivial zero in those rows. The logarithmic norm support is contained in $[1/2,11/2]$, so the test vanishes on the norm-one classes. Both polar moments vanish.

The small absolute upper is obtained by suppressing high frequencies on an interval where low off-line zeros have already been excluded. Exact cancellation as asserted in #5571 remains open. The same construction yields a monotone criterion for the full rational problem when the conductor cutoff tends to infinity. [As-written target and erratum](https://github.com/mccorvie/riemann-masullo/issues/5571) · [Rational equivalence on main](https://github.com/mccorvie/riemann-masullo/blob/9c791d74a81f1191d900e6d96f1270acee9b033e/RiemannMasullo/Ch13_ZerosHecke/RationalExteriorZeros.lean)

## The fixed radial function

Use the even, nonnegative smooth probability density $g$ from #7571. It is supported on $[-1,1]$. Its bilateral Laplace transform is
$$
 G(z)=\prod_{n=1}^{\infty}B_{r_n}(z),\qquad
 r_n=\frac{1}{n(n+1)},\qquad B_r(z)=\frac{\sinh(rz)}{rz},\quad B_r(0)=1 .
$$
Each factor is the transform of the uniform probability law on $[-r,r]$. The product converges locally uniformly and is nonzero for $\Re z\ne0$. The translated function $h(x)=g'''(x-3)-g'(x-3)/4$ is smooth, supported on $[2,4]$, and has transform $-e^{3z}z(z^2-1/4)G(z)$. These constructions and the sign convention are in Lean. [Quadratic box product](https://github.com/willzh0/riemann-masullo/blob/cf9f1a91b91ec900f93cb152daa3412bf466f59c/RiemannMasullo/ForMathlib/Analysis/Fourier/QuadraticBoxLaplace.lean) · [Translated profile and its antecedents](https://github.com/mccorvie/riemann-masullo/pull/7571)

Fix $k=172$ and $a=3/(2k)$. Convolve $h$ with $k$ more uniform interval laws of radius $a$. Write $f$ for the resulting smooth function divided by the value of its transform at $1/4$. Its transform is
$$
 R(z)=N^{-1}(-e^{3z})\,z(z^2-1/4)G(z)B_a(z)^k,\qquad
 N=\frac{3}{64}e^{3/4}G(1/4)B_a(1/4)^k \ \ge\ \frac{3}{64}e^{3/4}.
$$
The inequality uses the symmetry and unit mass of the laws. This gives $R(1/4)=1$, $R(0)=R(1/2)=R(-1/2)=0$, and $R(z)\ne0$ at every $0<|\Re z|<1/2$. Convolution adds at most $ka=3/2$ to each end of the support. Lyle used repeated boxes to attenuate high critical-line ordinates in a rational calibration which also annihilates prescribed low samples. [Lyle’s earlier window](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7147384761)

## The angular function and the actual omitted terms

In positive norm coordinates write $C_{\mathbb Q}=\widehat{\mathbb Z}^{\times}\times\mathbb R$. If $u$ is the unit coordinate and $x$ is log norm, the Tamagawa measure is $V\,du\,dx$, with $du$ probability Haar and $V$ the norm-one volume. For each positive $Q$ put
$$
 F_Q(u)=\sum_{q\le Q}\ \sum_{\chi\bmod q}^{*}\overline{\chi(u)},\qquad
 \varphi_Q(u,x)=V^{-1}F_Q(u)f(x).
$$
A star means primitive, including the conductor-one character. The expression is a finite locally constant function on the unit group. Equivalently, it is an explicit linear combination of congruence indicators,
$$
 F_Q(u)=\sum_{d\le Q}\varphi(d)\left(\sum_{m\le Q/d}\mu(m)\right)\mathbf1_{u\equiv1\bmod d}.
$$
Indeed the sum over all characters modulo $d$ is $\varphi(d)$ on the identity residue class and zero elsewhere. Invert the sum over primitive conductors dividing $d$. The total number of unit-group characters of exact conductor $q$ is correspondingly $(\mu*\varphi)(q)$. [Actual rational congruence cylinders](https://github.com/mccorvie/riemann-masullo/pull/7680) · [Primitive rational idelic lifts](https://github.com/mccorvie/riemann-masullo/pull/7623)

Haar orthogonality cancels $V$ and gives $R(w)$ for each selected normalized row and zero for all others. The inverse-character convention for attaching the Dirichlet function permutes the selected characters. Every finite-order character is trivial on every continuous positive-real norm section by connectedness. Conversely the normalized rational rows are the angular characters. In these coordinates a continuous homomorphism from the positive reals to the profinite unit group is trivial. Thus the assertion holds for every section in the original statement.

Write $z=\rho-1/2$ and let $m_\rho$ be the order of the zero. For any $\alpha>0$ the actual sum of norms in #5571 is
$$
 A(Q,\alpha)=\sum_{q\le Q}\ \sum_{\chi\bmod q}^{*}
       \ \sum_{|\Re \rho-1/2|\ge\alpha} m_\rho\,|R(\rho-1/2)|.
$$
Both edges of the open strip are included. Each individual character sum converges absolutely by the decay of the compact smooth Mellin transform and the usual zero count. This is a sum of the norms of the project's terms before summation. The resulting bound also bounds the modulus of the signed sum.

## The large-ordinate estimate

Let $H_*=1175/4=293.75$. Every selected off-central zero has $|\gamma|>H_*$, by the historical verifications described in the [height and counting estimates](GREEN-AND-TAILS.md). Put $h_*=aH_*$. For $|\Re z|\le1/2$, $u=a|\Im z|\ge h_*$,
$$
 |B_a(z)|\le\sqrt{(\sin u/u)^2+\big(\sinh(a/2)/h_*\big)^2}<0.217241 .
$$
Here $h_*\in(\pi/2,\pi)$, so the positive sinc decreases up to $\pi$. On $[\pi,5]$ its only interior extremum solves $u\cos u-\sin u=0$. The derivative of this last expression is $-u\sin u>0$ there. Its root exceeds $4.4934094579090$ by interval evaluation at that rational number. At the root, $|\sin u/u|=1/\sqrt{1+u^2}$. For $u\ge5$, $|\sin u/u|\le1/5$. The verifier uses the unrounded maximum of these three estimates. Call its complex-strip upper $c$.

For the first six factors of $G$, use $|B_{r_n}(z)|\le \cosh(r_n/2)/(r_n|\gamma|)$. For the next ten, replace $|\gamma|$ by $H_*$. The remaining symmetric probability law has support in $[-1/17,1/17]$, giving a bound $\cosh(1/34)$ for its transform. Finally,
$$
 |z(z^2-1/4)|\le |\gamma|^3\sqrt{1+\frac{1}{4H_*^2}}
                       \left(1+\frac1{2H_*^2}\right).
$$
Together these show $|R(z)|\le C c^{172}|\gamma|^{-3}$, where
$$
 C=\frac{64e^{3/4}}3
 \sqrt{1+\frac{1}{4H_*^2}}\left(1+\frac{1}{2H_*^2}\right)
 \cosh(1/34)
 \prod_{n=1}^{6}\frac{\cosh(r_n/2)}{r_n}
 \prod_{n=7}^{16}\frac{\cosh(r_n/2)}{r_n H_*}.
$$
Direct interval evaluation gives $C<72858$ and $C c^{172}<6.550\cdot10^{-110}$.

At the single common height the resulting inverse-cube bound across the whole family gives $A(400000,\alpha)<6.299\cdot10^{-104}$. An independent calculation, including a separate $\zeta$ tail estimate, reproduces that upper. Grouping the primitive characters into conductor intervals of length 1,024 and using their published conductor-dependent heights improves it to $A(400000,\alpha)<3.70\cdot10^{-104}$. Both bounds use the same test. The independent common-height calculation also uses the classical Hadamard sum for the zeta function. [Independent common-height verifier](independent_probe.py) · [160-bit replay](independent-160.json) · [192-bit replay](independent-192.json) [Family counts and zero estimates](GREEN-AND-TAILS.md) · [128-bit run](bounds-128.json) · [192-bit run](bounds-192.json)

## A cofinal criterion with fixed radial normalization

Keep $f$ and $R$ fixed for every $Q$, including $Q>400000$. Then $A(n,1/n)$ is nondecreasing for $n\ge1$. Each primitive row enters exactly once, its coefficient stays fixed after entry, and each set of included zeros increases as the half-width shrinks. A single off-line zero is eventually included and supplies the positive lower bound $m_\rho|R(\rho-1/2)|$. Conversely criticality of every Dirichlet zero makes every sum empty on the selected rows. Thus
$$
 \liminf_{n\to\infty} A(n,1/n)=0
 \quad\Longleftrightarrow\quad
 \text{Dirichlet GRH}
 \quad\Longleftrightarrow\quad
 \text{the rational all-width assertion of #5571}.
$$
The condition can equivalently use one unbounded subsequence. The fixed positive upper at a finite conductor cutoff leaves the cofinal condition open. This construction uses the original finite angular projection and an unweighted sum of the absolute exterior terms. The project also has an all-field criterion with a summable sequence of weights on finite arithmetic measurements. [All-field finite measurements](https://github.com/mccorvie/riemann-masullo/pull/7683)

To reproduce the numbers, run `uv run --no-project --with python-flint==0.9.0 python validate.py --bits 128` in this directory with Python and python-flint 0.9.0, then repeat with `--bits 192`. The radial and angular estimates are mathematical deductions from the cited results. The interval programs certify the numerical inequalities and sieve counts. [Verifier](validate.py)
