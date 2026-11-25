# A finite character matrix for the full zero divisors

Fix a number field $K$. Let $\psi_1,\ldots,\psi_t$ be distinct finite-order idèle-class characters of $K$, using the primitive local factors belonging to each character. The principal character is allowed. Write $m_i(\rho)$ for the order of its completed Hecke function at $0<\Re\rho<1$, with value zero at a regular nonzero point. Choose one finite Galois extension $L/\mathbb Q$ containing $K$ and the abelian extensions of $K$ cut out by all the characters. Put $G=\operatorname{Gal}(L/\mathbb Q)$, $H=\operatorname{Gal}(L/K)$, and $V_i=\operatorname{Ind}_H^G\psi_i$ under one consistent reciprocity convention.

## The divisor criterion

For any $c_1,\ldots,c_t\in\mathbb C$ the following are equivalent.

1. $\sum_i c_i m_i(\rho)=0$ at every individual point of the open critical strip, including the central line.
2. $\sum_i c_i\operatorname{tr}V_i(g)=0$ on every conjugacy class of $G$.

Thus the column rank of a finite character table is the exact dimension of the span of these full zero divisors. Enlarging $L$ inflates the representations and preserves the answer.

**From zeros to induced characters.** Write $L_i$ for the ordinary Hecke function, $\delta_i=1$ for the principal character and $0$ otherwise, and $q_i=|d_K|N\mathfrak f_i$. The entire functions of order at most one
$$
\xi_i(s)=[s(s-1)]^{\delta_i}q_i^{s/2}
 \Gamma_{\mathbb R}(s)^{a_i}\Gamma_{\mathbb R}(s+1)^{b_i}L_i(s)
$$
have precisely the zeros counted by $m_i$. Here a real place contributes according to its sign, and a complex place contributes one to each of $a_i,b_i$. Primitivity, nonvanishing on $\Re s=1$ and the functional equation account for the two boundaries. Clearing the principal poles produces nonzero values at both endpoints. A constant archimedean normalization and the conductor exponential leave the project's zero orders unchanged. [Thorner–Zaman, §2B, (2-3)–(2-8), pp. 1140–1141](https://msp.org/ant/2017/11-5/ant-v11-n5-p04-s.pdf#page=8) · [Project completion at the base revision](https://github.com/mccorvie/riemann-masullo/blob/9c791d74a81f1191d900e6d96f1270acee9b033e/RiemannMasullo/Ch03_IdelicZeta/Sec2.lean#L293)

Assume condition 1. In the logarithmic derivative of the genus-one Hadamard factorization the zero sum has terms $1/(s-\rho)+1/\rho$. These converge normally away from the zeros, so the weighted sum of the logarithmic derivatives is constant. Set $F=\sum_i c_i L_i'/L_i$, $A=\sum_i c_i a_i$, $B=\sum_i c_i b_i$ and $P=\sum_i c_i\delta_i$. Subtract the constant identity at $s$ from its value at $s+2$. The recurrence $\Gamma_{\mathbb R}(s+2)/\Gamma_{\mathbb R}(s)=s/(2\pi)$ gives
$$
0=F(s+2)-F(s)+\frac{A}{s}+\frac{B}{s+1}
 +P\left(\frac1{s+2}+\frac1{s+1}-\frac1s-\frac1{s-1}\right).
$$
On the positive real axis the Euler series gives $F(\sigma)=O(2^{-\sigma})$, by absolute convergence at $\sigma=2$. A nonzero rational function cannot decay exponentially at positive infinity. The rational summand is therefore identically zero. Its residue at $1$ gives $P=0$, and the remaining residues give $A=B=0$. Now $F(s)=F(s+2)$ on the right half-plane. Iteration and absolute convergence give $F=0$ there. For every rational prime unramified in $L$, the Dirichlet coefficient of $p^{-s}$ in $-F$ is
$$
(\log p)\sum_i c_i\operatorname{tr}V_i(\operatorname{Frob}_p).
$$
Uniqueness of the Dirichlet series and Chebotarev on $L/\mathbb Q$ give condition 2.

**From induced characters to zeros.** At a rational prime $p$, let $I$ be an inertia group and let $g$ lift Frobenius in its decomposition group. For every $r\ge1$,
$$
\operatorname{tr}(g^r\mid V_i^I)
   = |I|^{-1}\sum_{h\in I}\operatorname{tr}V_i(g^rh).
$$
Condition 2 kills the weighted sum of all these traces. Artin's induction identity identifies each local factor with the product of the primitive Hecke factors above $p$, including at ramified primes. Hence $\sum_i c_i L'_i/L_i=0$ for $\Re s>1$. Meromorphic continuation and residues at each $\rho$ in the open critical strip give condition 1, since gamma factors have no zero or pole there. This direction uses logarithmic derivatives of Hecke functions, and requires no Artin holomorphy conjecture. [Artin, *Zur Theorie der L-Reihen mit allgemeinen Gruppencharakteren* (1931), formula (18)](https://doi.org/10.1007/BF02941010)

**Discarding finitely many sites or any bounded height.** The criterion still holds if condition 1 is assumed only outside a finite set of sites. In the Hadamard calculation the weighted logarithmic derivative is then a constant plus $T(s)=\sum_\rho b_\rho/(s-\rho)$ over the exceptional sites, with $b_\rho=\sum_i c_i m_i(\rho)$. In the shift calculation the right side becomes $T(s+2)-T(s)$. Subtract this from the rational summand. As before the resulting rational function decays exponentially on the positive real axis and must vanish identically. At each exceptional $\rho$ in the open strip, only the term from $T(s)$ has a pole there: the shifted poles have real parts in $(-2,-1)$ and the gamma and polar terms have integral real arguments. Thus each $b_\rho=0$. There are only finitely many sites up to any fixed absolute height on these finitely many rows. Consequently every nonrelation among the induced characters is witnessed by full-divisor multiplicities at arbitrarily large heights, possibly on the central line.

## How this changes the actual test in Theorem 12.5.1.1

Let $u=\log|x|$ and $V=\operatorname{vol}(C_K^1)$ in the paper's measure. A test supported on these finite-order angular rows has the form
$$
\Phi(x)=V^{-1}\sum_i\overline{\psi_i(x)}\,h_i(u),
\qquad h_i\in C_c^\infty(\mathbb R).
$$
Each finite-order character is trivial on every continuous positive norm section because the domain is connected. Distinct characters have distinct restrictions to $C_K^1$. Orthogonality identifies the Mellin sample on row $i$ at $\rho$ with $\widehat h_i(\rho-1/2)$, where $\widehat h(z)=\int h(u)e^{uz}\,du$. In particular $\Phi|_{C_K^1}=0$ exactly when every $h_i(0)=0$.

Select linearly independent columns $V_{i_j}$ spanning all the characters of the induced representations, and solve
$$
\operatorname{tr}V_i=\sum_j d_{ij}\operatorname{tr}V_{i_j}.
$$
Replace $\Phi$ by the physical test on those rows with profiles $k_j=\sum_i d_{ij}h_i$. The divisor criterion gives, at every site,
$$
\sum_i m_i(\rho)\widehat h_i(\rho-1/2)
    =\sum_j m_{i_j}(\rho)\widehat k_j(\rho-1/2).
$$
This preserves the original signed omitted sum in every section and for either choice of boundary inclusion, even with the two wings read separately. Every $k_j(0)=0$ if the original test vanishes on norm one. Frobenius reciprocity makes the trivial-representation component exactly the principal-character coordinate, so that the change of basis also preserves any principal polar moments. Each smooth compact profile has arbitrarily fast vertical decay on a bounded real strip. The standard order-one zero count and finiteness of the angular expansion justify grouping these signed sums absolutely.

The rank is minimal for spanning all the full zero-divisor rows. The positive-width exterior omits the central line and sums over many different sites. Additional cancellations in that weaker observable are possible. In particular this criterion leaves the assertion for arbitrary tests in [#5571](https://github.com/mccorvie/riemann-masullo/issues/5571) open.

## A fixed physical profile that reads the off-line sites

Let $b$ be the probability density of the sum of independent uniforms on $[-2^{-j},2^{-j}]$, $j=1,2,\ldots$. This sum has support in $[-1,1]$ and bilateral Laplace transform
$$
B(z)=\prod_{j\ge1}\frac{\sinh(2^{-j}z)}{2^{-j}z}.
$$
The factors have value one at zero and deviations from one of order $4^{-j}$ on compact sets. Thus the product has precisely the zeros of the factors, all on the imaginary axis. On that axis the first $k$ factors give decay $O_k((1+|\Im z|)^{-k})$, since all the remaining factors have modulus at most one. Fourier inversion gives a real even $C^\infty$ density.

For $\ell>0$ let $p_\ell(u)=\ell^{-1}[b(u/\ell-2)+b(u/\ell+2)]$. Apply $d^2/du^2-1/4$ and multiply by a real constant so that the transform at $z=1/4$ is one. This gives a real even profile supported on $\ell\le |u|\le3\ell$. Its transform is a nonzero constant times
$$
 (z^2-1/4)\cosh(2\ell z)\, B(\ell z).
$$
It vanishes at both polar arguments and is nonzero for every $0<|\Re z|<1/2$. Consequently a pair of distinct quadratic characters with identical divisor rows gives a real inversion-even physical test with opposite nonzero coefficients at every possible off-line site. If central sites are also needed, take both $\ell=1$ and $\ell=\sqrt2$. The imaginary coordinates of their possible central zeros lie, respectively, in $(\pi/4)\mathbb Z\setminus\{0\}$ and $(\pi/(4\sqrt2))\mathbb Z\setminus\{0\}$. The sets are disjoint, and both transforms are nonzero at zero. Every interior site is visible to at least one of the two physical profiles.
