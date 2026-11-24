# Exact coordinate norms and sharp height cutoffs on the Sobolev line

For any number field, real chart parameter $a$, and one angular component, take $\alpha=0$ and $s=2$. The coordinate norm at each zero then has an exact formula in its two adjacent gaps. For each fixed test this gives an equivalent scalar version of the majorant in #7455. There is also a spacing-free replacement for the finite sections in #7241. For almost every translate of the unit height grid, the operators obtained by summing the actual zero blocks in each grid interval are absolutely summable in trace norm. The same grid works for every test on the component. Reordering whole intervals is allowed. [Issue #7455](https://github.com/mccorvie/riemann-masullo/issues/7455) · [Issue #7241](https://github.com/mccorvie/riemann-masullo/issues/7241)

## The component and its Gram kernel

Fix a representative $\chi=\chi(\eta)$ of the norm-one character $\eta$. Let $T$ be the set of distinct real $t$ for which the completed Hecke $L$-function of $\chi$ has positive vanishing order at $a+it$. On the zero-width strip a jet of index $j$ survives precisely when $j$ is below the arithmetic multiplicity and $2j+1<s$. Thus every site here contributes exactly one evaluation, including a zero of higher arithmetic multiplicity. Write $\Lambda_t$ for that functional, $x_t$ for its biorthogonal vector, and $k_t$ for its Riesz representative divided by $\|\Lambda_t\|$. Use the Hilbert inner product linear in its second variable. Let $H_\eta$ denote the closed span of the $k_t$ on this component. The realized dual jets span the full dual densely, and distinct components are orthogonal. [Boundary cutoff and basis definition](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L730) · [Basis realization](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L8434)

The quotient-dual embedding is isometric. In the reciprocal weight its zeroth jet is $\chi(g)e^{it\log|g|}$. Within one character the angular factors cancel, and Haar measure reduces the pairing up to a common positive scalar to the Fourier transform of $(1+y^2)^{-1}$. Different angular factors integrate to zero. Consequently $\|\Lambda_t\|$ is independent of $t$ and
$$
\langle k_t,k_u\rangle=e^{-|t-u|}.
\tag{1}
$$
The linked fork proves these input identities for every number field and basepoint choice. Its bounds for the coordinate norm use a symmetric isolating radius and a single comparison site. The finite inverse-matrix calculation for kernels of this form is classical. [Quotient-dual isometry](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L630) · [Kernel and angular orthogonality](https://github.com/mlyle/riemann-masullo/blob/094293aeeaf5b58f7b194e1e779aac4c330a6251/research/I314LineGaps.lean#L184) · [Previous bounds](https://github.com/mccorvie/riemann-masullo/issues/7241#issuecomment-7126304685) · [Ding and Zhang, Theorem 2](https://arxiv.org/pdf/1803.02575)

The only zero count used below is
$$
S=\sum_{t\in T}(1+|t|)^{-2}<\infty .
\tag{2}
$$
One may take the strip in the repository's multiplicity-weighted count wide enough to contain the fixed line $a$. Every retained site has multiplicity at least one. In particular $T$ is locally finite and $\#(T\cap[-R,R])\le S(1+R)^2$. Denote the test's Mellin transform in this chart by $M_\varphi(z)$, and put $\lambda(t)=M_\varphi(it)$. The transform decays faster than any power of height on every fixed vertical strip. Its derivatives satisfy the same estimates by Cauchy's formula on a fixed circle. This also follows from the smooth compactly supported logarithmic profile. The site of the $L$-function is $a+it$, and the argument of the test is $it$. [Weighted divisor count](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/Ch07_SchauderBasesZeta/Sec4.lean#L1262) · [Vertical decay](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/Ch07_SchauderBasesZeta/Sec4.lean#L1183) · [Multiplier on the coordinates](https://github.com/mlyle/riemann-masullo/blob/094293aeeaf5b58f7b194e1e779aac4c330a6251/research/I314LineGaps.lean#L349)

## Ordered orthogonal differences and the exact majorant

Order the sites increasingly as $t_i$ on an interval of integers, which may have either, both or neither endpoint. The empty case gives the zero operator. On each edge $t_{i-1}<t_i$, set
$$
d_i=t_i-t_{i-1},\quad r_i=e^{-d_i},\quad
s_i=\sqrt{1-r_i^2},\quad c_i=r_i/s_i=(e^{2d_i}-1)^{-1/2},\quad
e_i=(k_i-r_i k_{i-1})/s_i ,
$$
where $k_i=k_{t_i}$. At a first site set $e_i=k_i$, $r_i=c_i=0$ and $s_i=1$.

The $e_i$ form an orthonormal basis of $H_\eta$. Indeed (1) gives $\langle k_j,e_i\rangle=0$ for $j<i$ and $\langle k_j,e_i\rangle=s_i e^{-(t_j-t_i)}$ for $j\ge i$. This proves orthogonality and normalization. Iterating $k_i=s_i e_i+r_i k_{i-1}$ down to a site $t_m$ leaves a residual of norm $e^{-(t_i-t_m)}$. If there is no first site then $t_m\to-\infty$, so the residual tends to zero. At a first site the iteration terminates.

Define
$$
w_i=e_i/s_i - c_{i+1}e_{i+1},
$$
omitting the second term at a last site. The preceding pairing formula gives $\langle k_j,w_i\rangle=\delta_{ij}$, and waves on other components are orthogonal to $w_i$. Totality of all waves gives $w_i=\|\Lambda_i\|x_i$. In particular
$$
\boxed{\quad (\|\Lambda_i\|\,\|x_i\|)^2
       =1+c_i^2+c_{i+1}^2 .\quad}
\tag{3}
$$
Missing edges contribute zero. A singleton has condition number one. For equal gaps $d$ on both sides, (3) attains the fork's upper bound exactly. A site at the end of the chain attains its one-neighbor lower bound.

For #7455 the fixed circle has radius $2e$ here. Its minimal admissible bound for this test is
$$
m_i=\max_{|z-it_i|=2e}|M_\varphi(z)|.
$$
The maximum exists and $\sum_i m_i<\infty$ by (2) and strip decay. For a homogeneous test the corresponding circles on other components have zero Mellin transform. For any test the calculation applies to the sum restricted to this component. Consequently the majorant on this component holds **if and only if**
$$
\boxed{\quad
\sum_{\substack{i:\ t_{i-1}\ {\rm exists}\\ d_i<1}}
      \frac{m_{i-1}+m_i}{\sqrt{d_i}}<\infty .
\quad}
\tag{4}
$$
Indeed $m_i$ is bounded above by every admissible majorant at $i$ and itself is admissible. By (3), $\sqrt{1+c_i^2+c_{i+1}^2}$ lies between $(1+c_i+c_{i+1})/\sqrt3$ and $1+c_i+c_{i+1}$. Sum the resulting nonnegative quantities over sites and reindex by edges. For $d_i\ge1$ the $c_i$ are bounded. For $0<d_i<1$ the inequalities $2d_i\le e^{2d_i}-1\le(e^2-1)d_i$ follow from the tangent and chord of the exponential. This proves both directions of (4) for the *specified* test, including tests vanishing on the component. [Exact quantifiers of #7455](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/Ch10_TraceSpectral/Sec3_Isolated.lean#L119)

The comparison constants in this last argument are absolute. For an arbitrary test on the full quotient at $(\alpha,s)=(0,2)$, sum $m_{\eta,i}$ over all sites of all components and add the short-edge series (4) over all components. Each edge pairs neighbors of the same character. Finiteness of this one nonnegative sum is equivalent to the full majorant in #7455 for this test. The use of (2) to discard the first sum above was componentwise. Its convergence after summing in $\eta$ needs a separate estimate.

## The multiplier and the two boundary terms

Let $A$ be convolution restricted to $H_\eta$. The coordinate identity gives $A^* k_i=b_i k_i$ with $b_i=\overline{\lambda(t_i)}$. The component and its orthogonal complement both reduce the operator because this identity holds on the total wave family. For a finite set $F$, let $A_F$ be the actual manuscript section $\sum_{i\in F}\lambda(t_i)\Lambda_i(\,\cdot\,)x_i$. The symbol of $A_F^*$ on the waves is $b_i\mathbf{1}_F(i)$ by biorthogonality. The arguments below apply to both symbols. [Finite sections in Lean](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/Ch10_TraceSpectral/Sec3.lean#L405)

For any such multiplier $B k_i=h_i k_i$,
$$
B e_i=h_i e_i+c_i(h_i-h_{i-1})k_{i-1}.
\tag{5}
$$
At a first site only $h_i e_i$ occurs. The two displayed directions are orthogonal unit vectors. Summing their squared norms gives the exact Hilbert–Schmidt expression, allowing either side to be infinite,
$$
\|B\|_{S_2}^2=\sum_i |h_i|^2+\sum_{\text{edges }i}c_i^2 |h_i-h_{i-1}|^2 .
$$
Summing the trace norms of the rank-one terms gives
$$
\|B\|_{S_1}\le\sum_i |h_i|+\sum_{\text{edges }i}c_i|h_i-h_{i-1}|
\tag{6}
$$
whenever the right side is finite. Each summand in the column expansion is rank one and the resulting operator agrees with $B$ on the basis. For $h_i=b_i$ the right side is finite without a gap assumption. On $d_i<1$ use
$$
c_i|b_i-b_{i-1}|\le\sqrt{d_i/2}\ \sup_{[t_{i-1},t_i]}|\lambda'|.
$$
The heights across that interval differ by less than one. Equation (2) therefore sums these terms. For $d_i\ge1$ use $c_i\le(e^2-1)^{-1/2}$ and $\sum_i|\lambda(t_i)|<\infty$. In fact, putting $p(f)=\sup_t(1+|t|)^2|f(t)|$ gives the explicit bound
$$
\|A\|_{S_1}\le S\left[(1+2c(1))p(\lambda)+2\sqrt2\,p(\lambda')\right],
\qquad c(1)=(e^2-1)^{-1/2}.
$$
For a small gap, $(1+|t_i|)^2\le4(1+|u|)^2$ throughout the edge, which yields the derivative constant. For large gaps each site is an endpoint at most twice. In logarithmic coordinates $p(\lambda)$ and $p(\lambda')$ are continuous seminorms of the radial test profile, by two integrations by parts applied to that profile and its product with the log coordinate. The trace of $A$ on the component is $\sum_i\lambda(t_i)$ because the nondiagonal term in (5) is orthogonal to $e_i$. For a homogeneous test it gives the trace on the full quotient as well.

There is a sharp criterion for any exhausting sequence of finite intervals of consecutive sites $F_j=[p_j,q_j]$. Exhaustion here means that every fixed finite set eventually belongs to $F_j$. The following are equivalent.
  
1. $A_{F_j}\to A$ in trace norm on the component.
2. $A_{F_j}\to A$ in operator norm on the component.
3. Both crossing-edge quantities tend to zero,
   $$
   c_{p_j}|b_{p_j-1}|\longrightarrow 0,\qquad c_{q_j+1}|b_{q_j+1}|\longrightarrow 0,
   \tag{7}
   $$
   omitting absent edges.

Apply (5) to the tail symbol $h_i=b_i\mathbf{1}_{i\notin F_j}$. Each crossing quantity is at most the operator norm because it is the magnitude of the $k_{i-1}$ coefficient of the column $B e_i$. This proves necessity. In (6) the diagonal tail and the sum of the original edge differences with both endpoints outside $F_j$ tend to zero by absolute summability. The only additional jumps are precisely (7). This proves sufficiency.

## Absolute summability after grouping by a shifted unit grid

Write $\langle t\rangle=1+|t|$. For Lebesgue almost every $\theta\in[0,1)$ there is a constant $\epsilon_\theta>0$ such that
$$
\operatorname{dist}(t,\theta+\mathbb Z)\ge\epsilon_\theta\langle t\rangle^{-2}
\quad(t\in T).
\tag{8}
$$
In normalized Lebesgue measure on the circle, the exceptional set for a given $t$ and constant $\epsilon>0$ has measure at most $2\epsilon\langle t\rangle^{-2}$. The union bound gives measure at most $2\epsilon S$ for failure of (8) at that constant. Let $\epsilon\downarrow0$. This proves the assertion, with one exceptional null set for all tests. A countable intersection also permits the same shift on every angular component, with separate constants.

Fix such a shift and define the finite bins $I_n=T\cap[n+\theta,n+1+\theta)$. Then for every integer $L\ge0$ there is $C_L$, depending on the test, the component and the shift, such that
$$
\boxed{\quad \|A_{I_n}\|_{S_1}\le C_L(1+|n|)^{-L}.\quad}
\tag{9}
$$
For a nonempty bin, use (6) for its symbol. There are at most $S(3+|n|)^2$ diagonal terms. All internal edges have length less than one, so their coefficients are bounded by the derivative estimate following (6). Both the diagonal values and these coefficients decay to arbitrary polynomial order in $|n|$. At each of the at most two edges crossing the boundary, the jump magnitude is the symbol value at the **included** endpoint $t$. The edge length $d$ is at least $\operatorname{dist}(t,\theta+\mathbb Z)$, whence $c(d)\le(2\epsilon_\theta)^{-1/2}\langle t\rangle$. The included endpoint is in the bin, even if its neighbor is far away. Rapid decay absorbs all these polynomial factors, proving (9).

The series $\sum_{n\in\mathbb Z} A_{I_n}$ therefore converges absolutely in trace norm, and its sum equals $A$ on $H_\eta$ by the total waves and the adjoint identity. For every bounded insertion $U$ on the quotient this also gives
$$
\sum_{n\in\mathbb Z}
  \left|\sum_{i\in I_n}\Lambda_i\!\left(A(Ux_i)\right)\right|<\infty .
$$
Here $A$ inside the scalar formula denotes the full convolution, and the block is supported on $H_\eta$. Indeed the inner sum is $\operatorname{Tr}(U A_{I_n})$, bounded by $\|U\|\,\|A_{I_n}\|_{S_1}$. The partial sum for $|n|\le R$ has rank $O((1+R)^2)$ by (2) and trace-norm error $O_L((1+R)^{-L})$ for every $L$. Choosing $R$ proportional to the square root of the allowed approximation rank gives faster-than-polynomial decay of the singular values and membership in every Schatten class $S_p$, $p>0$. The estimates do not sum their component-dependent constants over infinitely many characters.

## Why the cutoff still matters

The restriction on cutoffs can be witnessed in the very same exponential Gram geometry. Start with the Fourier transform $f$ of any nonzero smooth compactly supported radial log profile. Its real zeros are discrete. Modulating the profile by a fixed frequency gives a transform $\lambda$ with $\lambda(n)\ne0$ at every positive integer, since only countably many modulations are forbidden. Choose
$$
0<\delta_n<\min(1/4,\,|\lambda(n)|^4)
$$
small enough that both $\big|\lambda(n\pm\delta_n/2)\big|\ge|\lambda(n)|/2$. Put two synthetic sites at $n\pm\delta_n/2$. They obey (2) with only two sites per pair. The sharp cutoff at height $n$ splits the pair and has an error in operator norm at least $c(\delta_n)|\lambda(n+\delta_n/2)|$, which grows at least as a positive constant times $|\lambda(n)|^{-1}$. The half-integer grid contains each pair in a single bin and satisfies (8). Also $m_i\ge|\lambda(t_i)|$ by the maximum principle, so (4) fails on this synthetic divisor. Which gaps occur among actual Hecke zeros is an arithmetic question.

## Scope and verification

The manuscript asks for every permitted enumeration in (10.3.1.1), p. 448, and (10.3.2.1), p. 453. The single constant beneath (10.3.1.18) on p. 451 and the scalar estimate (10.3.2.7) on pp. 454–455 cannot supply that conclusion. An earlier issue comment proposed replacing the sum by smooth frequency windows, and the earlier universal spacing equivalence treats all homogeneous tests. Equations (4), (7) and (9) above use individual coordinates, arbitrary contiguous cutoffs, and sharp translated unit intervals, respectively. Equation (9) provides a weaker summation statement for the actual rank-one blocks. The individual-site assertions in #7241 and #7455 remain open for the Hecke divisor, as do the positive-width strip and simultaneous summation across characters. [Manuscript, pp. 448–455](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/paper/the-music-of-the-primes.pdf) · [Prior smooth-window proposal](https://github.com/mccorvie/riemann-masullo/issues/7241#issuecomment-7142557248) · [Exact scope of arbitrary enumerations](https://github.com/mccorvie/riemann-masullo/issues/5217#issuecomment-7097340814) · [Other positive-width reduction](https://github.com/mccorvie/riemann-masullo/issues/7455#issuecomment-7145348798)

The proof uses the pinned quotient and Mellin inputs above. The companion file [NearestGram.lean](NearestGram.lean) checks the abstract coordinate identity (3), including endpoints and singletons, the multiplier identity (5), and its column norm over any complex Hilbert space. The infinite trace and shifted-grid arguments are mathematical proofs in this note. The finite-model program [check_finite_model.py](check_finite_model.py) tests 160 intervals against independent dense matrix solves and also tests extremely small gaps at 100 decimal digits. From a configured checkout the checks are reproducible with the following commands.

~~~text
lake lean research/issue-7241/NearestGram.lean
python research/issue-7241/check_finite_model.py
~~~
