# Individual geometric blocks at zero strip width

For every number field, every test and every chart covered by #7406, its trace-norm bound holds at half-width $\alpha=0$ and Sobolev exponent $s=2$. In fact the individual trace norms are summable. This is a statement about the geometric part of each block, with the projection on the output in the order specified on p. 472. [Theorem 10.4.3.5(2) and the exact Lean statement](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/Ch10_TraceSpectral/Sec4b_Isolated.lean#L276)

## An exact energy identity

Fix one angular character and use the physical log frequency $\nu$ from a norm splitting. With the Fourier transform normalized isometrically, the physical weight $1+x^2$ gives exactly the inner product of $H^1(\mathbb R)$, up to a common Haar constant. The theta subspace $J$ consists of the functions vanishing on the locally finite set of line-zero ordinates. Even at a multiple zero only the value survives at $s=2$. Write $P$ for orthogonal projection onto $J^\perp$, $G=1-P$, and $\lambda$ for the smooth Mellin multiplier of the test on this component. [Sobolev weight](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/Ch09_HardySobolev/Sec2.lean#L3069) · [Common jet kernel](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L8368)

The canonical lift of the biorthogonal vector at $z$ is its cardinal function $h_z$. It is one at $z$. Between $z$ and its nearest neighbour on either side, put $d$ equal to that distance and $r=|\nu-z|$. Then $h_z=\sinh(d-r)/\sinh d$, with value zero past that neighbour. On a side without any neighbour it is $e^{-r}$. Indeed this continuous function belongs to $H^1$ and solves $h''=h$ between nodes. Integration by parts against $v\in J$ gives zero in the $H^1$ inner product. The endpoint terms vanish at the nodes and at infinity. This proves membership in $J^\perp$ and therefore identifies the unique lift with the prescribed values. Other angular components are zero. A fixed normalization of evaluation and its inverse normalization on $h_z$ cancel in the rank-one block.

Pointwise on the nodes, $\lambda h_z$ and $\lambda(z)h_z$ agree. Thus the geometric block is exactly

$$
R_z f=f(z)b h_z,\qquad b(\nu)=\lambda(\nu)-\lambda(z).
$$

For smooth complex $b$ and the real hat $h=h_z$, differentiation on either side gives

$$
|bh|^2+|(bh)'|^2=|b'|^2h^2+(|b|^2hh')'.
$$

At $z$ we have $b(z)=0$, at a finite neighbour $h=0$, and at an infinite endpoint $\lambda$ is bounded and $h,h'$ decay exponentially. Integration gives

$$
\boxed{\ \|b h_z\|_{H^1}^2=\int_{\mathbb R}|\lambda'(\nu)|^2h_z(\nu)^2\,d\nu.\ }
$$

In particular the large slopes of a narrow hat do not occur in its geometric output energy. The identity also gives a count-free square-sum bound. Only two hats can be nonzero strictly between consecutive nodes, and their sum there is $\cosh(\nu-(z+w)/2)/\cosh((w-z)/2)\le1$ for the endpoints $z,w$. On an unbounded component of the complement there is at most one hat, bounded by one. Therefore $\sum_z h_z(\nu)^2\le1$, and $\sum_z\|R_z\|_1^2\le C\|\lambda'\|_2^2$ with the common squared evaluation norm $C$. This square-sum conclusion alone does not imply trace-norm summability.

## The bound for every finite selection

On each side,

$$
0\le h_z(\nu)=e^{-r}\frac{1-e^{-2(d-r)}}{1-e^{-2d}}\le e^{-r}.
$$

Every compact Bruhat test comes from a compact Lie quotient of the norm-one group. Let $\ell$ be the angular lattice frequency on that quotient and $H_z=1+|\nu_z|+\|\ell\|_1$. The derivative $\lambda'$ is the transform of the test multiplied by $ix$. Integration by parts in the real and angular directions gives $|\lambda'(\nu)|\le C_N (1+|\nu-\nu_z|)^N H_z^{-N}$, uniformly on this stage. Inactive characters have zero multiplier. The exact identity and the exponential bound give $\|b h_z\|_{H^1}\le C'_N H_z^{-N}$, independently of both gaps. The norm of point evaluation is constant in the angular mode and the physical ordinate. Hence the rank-one trace norm obeys the same estimate. The project's joint divisor count bounds the number of active sites with $H_z\le R$ by a polynomial. Taking $N$ larger than its degree and summing dyadically gives $\sum_{\omega,z}\|R_{\omega,z}\|_1<\infty$. This proves the finite-selection bound in #7406, without grouping nearby zeros. [Joint divisor count](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/AppB_AnalyticNT/Sec4b.lean#L15861) · [Joint Fourier decay](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/AppB_AnalyticNT/Sec4b.lean#L16532)

## The ambient operator at higher even orders

For $s=2k$, $k\ge1$ an integer, the physical squared weight $(1+x^2)^k$ gives the binomial $H^k$ inner product in frequency. Its differential expression is $D=(1-\partial_\nu^2)^k$. Here $J$ is the common kernel of the retained jets, up to order $N_z-1$ with $N_z=\min(k,\operatorname{ord}_z L)$. On a bounded open interval $I$, for any $f$ the distribution $D P f$ annihilates compact smooth tests on $I$ whose retained jets vanish. The finite jet map is onto, by disjoint smooth cutoffs times Taylor monomials, so the restriction of $D P f$ is in the span of the corresponding $\delta_z^{(j)}$. The homogeneous equation on $I$ has dimension $2k$, with solutions given by the functions $\nu^j e^{\pm\nu}$ for $j<k$. Consequently a smooth symbol $d$ supported compactly in $I$ satisfies

$$
\operatorname{rank}(M_dP)\le 2k+\sum_{z\in I}N_z .
$$

Split the test multiplier on each mode with a fixed smooth partition of unity into bounded, overlapping frequency windows. By the product rule the operator norm of a term is bounded by the supremum of its symbol and its first $k$ derivatives times a constant depending only on $k$. These bounds decay rapidly jointly in height and angular frequency. Below cutoff $R$, the total jet contribution to the ranks grows polynomially by the joint count. So does the sum of the constant $2k$ terms, since the angular frequencies below $R$ form a polynomial-size lattice ball on a fixed test quotient. Thus $M_\lambda P$ has approximants of polynomial rank with faster-than-polynomial error. Its singular values decay faster than every inverse power and it has a representing projective tensor. At $k>1$ this proof for the ambient operator leaves the bounds for arbitrarily selected individual geometric blocks open. Positive widths and the quotient's individual blocks in #7241 also remain open.

The rational, one-component case of the local rank estimate for $k=1$ is already recorded in F259, and the project previously discussed ambient trace class via frequency windows. The individual geometric-block cancellation above uses the particular projections of #7406. These are mathematical proofs. [Earlier window discussion](https://github.com/mccorvie/riemann-masullo/issues/1169#issuecomment-7055349843) · [Erratum F259](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/ERRATA.md#L450)
