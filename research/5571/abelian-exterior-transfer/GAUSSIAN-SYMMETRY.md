# Exact signed cancellation for Gaussian angular characters

For Theorem 12.5.1.1, pp. 519–520, there is a **single nonzero inversion-even Bruhat test** on $C_{\mathbb Q(i)}$ for which the signed sum of the omitted terms is **exactly zero** at every positive width and for every norm section. It samples each nontrivial, finite-conductor-one angular Hecke character, and its coefficient at every possible off-central zero of every such row is nonzero. These assertions use no finite-height verification.

## The test and its nonzero samples

For a nonzero Gaussian ideal $(a)$ put $\Xi_k((a))=(a/\bar a)^{2k}$, $k\in\mathbb Z$. This is independent of the generator since the four units have fourth power one. It gives the unramified idèle-class character of angular weight $4k$ (up to simultaneous inversion in the ideal/idèle dictionary), trivial on the usual positive real section. Class number one and the four units give precisely these normalized finite-conductor-one characters. In particular $\Xi_1((2+i))=(-7+24i)/25$, whereas $\Xi_{-1}$ gives its conjugate. The characters at $k$ and $-k$ are distinct for every $k\ne0$, as is also seen on the complex angular group. [Rudnick and Waxman, §4.1, p. 13](https://arxiv.org/pdf/1705.07498#page=13)

Take the compact real profile $f$ from the [normalized rational test](../dirichlet-slab-exterior/README.md), with bilateral Laplace transform $R(z)$. Its support is in $[1/2,11/2]$. Define
$$
 g(u)=\frac{f(u)-f(-u)}{1+e^{-3/2}},\qquad R_o(z)=\frac{R(z)-R(-z)}{1+e^{-3/2}}.
$$
The even factors in $R$ and its exponential translation give $R(-1/4)=-e^{-3/2}$, so $R_o(1/4)=1$. Apart from a nonzero constant,
$$
 R_o(z)=\cosh(3z)\,z(z^2-1/4)\,G(z)B_{3/344}(z)^{172}.
$$
Each factor is nonzero on $0<|\Re z|<1/2$. In particular $\cosh(3z)$ has all its zeros on the imaginary axis. Also $R_o(0)=R_o(1/2)=R_o(-1/2)=0$. The physically odd $g$ is smooth, has compact support, and vanishes near zero.

For $|z|=1$ let
$$
 W(z)=2\left(\frac{\bar z}{2-\bar z}-\frac z{2-z}\right)
     =\sum_{k=1}^\infty 2^{1-k}(\bar z^k-z^k).
$$
Writing $V$ for the norm-one Tamagawa volume, take
$$
 \Phi(x)=V^{-1}W(\Xi_1(x))\,g(\log|x|).
$$
This is a physical Bruhat test: the angular factor is smooth on a circle quotient and the radial factor has compact support. Both factors change sign under $x\mapsto x^{-1}$, so $\Phi(x^{-1})=\Phi(x)$. It is nonzero because the angular character takes all circle values on norm-one classes and $g$ is nonzero. It vanishes on the norm-one classes. The two polar terms vanish by angular orthogonality. Multiplying $\Phi$ by $i$ gives a real-valued test with the same cancellation. Earlier work on this issue proves exact exterior cancellation for inversion-odd tests. [Earlier inversion symmetry](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7122971222)

## Cancellation, including both edges

Conjugating ideals preserves their norm and exchanges $\Xi_k$ and $\Xi_{-k}$. Their ordinary Dirichlet series are identical in $\Re s>1$. Hence their continuations have exactly the same nontrivial zeros with the same orders at the **same complex sites**. This identity is recorded explicitly for the Gaussian characters by Rudnick and Waxman. Their archimedean factors are regular and nonzero in the open critical strip. [Equality of the two functions, §4.1](https://arxiv.org/pdf/1705.07498#page=13)

In the standard positive norm chart, Haar orthogonality in $\Phi$ gives the coefficients $2^{1-k}R_o(\rho-1/2)$ and $-2^{1-k}R_o(\rho-1/2)$ on the two rows. Other rows have coefficient zero. Thus a zero of order $m$ contributes $+m2^{1-k}R_o(\rho-1/2)$ and its exact negative, with the same edge condition $|\Re\rho-1/2|\ge\alpha$.

This pairing also gives an unordered absolutely convergent sum. In each unit ordinate interval at height $T$, the number of zeros of the $k$th row counted with multiplicity is $O(\log(2+|k|+|T|))$. This zero-count estimate is unconditional. Its use here only needs uniform vertical-strip decay of the transform at the **actual real parts** of the zeros, supplied by integration by parts in the fixed smooth compact function $g$. Summing ordinate intervals gives $O_g(\log(2+k))$ per row, and $\sum_{k\ge1}2^{1-k}\log(2+k)<\infty$. Thus the two-row cancellations give the literal signed exterior sum zero for every $\alpha>0$, including equality at the two edges. [Uniform local zero count, equation (4.6), p. 17](https://arxiv.org/pdf/1705.07498#page=17)

For a different norm section write $\Xi_k(\tau(e^u))=e^{ia_ku}$. The normalized row is $\Xi_k|\cdot|^{-ia_k}$, whose zero is $\rho+ia_k$. Against the conjugate of the physical raw character its Mellin sample is $R_o(\rho-1/2)$ because the imaginary shifts cancel. The two chart indices may have different ordinates, but their real parts and the two numerical contributions are unchanged. This proves the result for every norm section. [Norm-section argument](README.md)

Even without any assumption on zero locations, this test has nonzero Mellin coefficient at a density-one fraction of all positive-ordinate zeros of each fixed nonzero row. In the open critical strip the possible zeros of $R_o(\rho-1/2)$ must be central and have $\Im\rho\in(\pi/6)\mathbb Z$: the $\cosh$ factor gives odd multiples of $\pi/6$, the original boxes give multiples of $\pi n(n+1)$, and the added boxes give multiples of $344\pi/3$. The locally normally convergent box product introduces no other zeros. For $k>0$, the algebraic character $(a)\mapsto a^{4k}$ gives a holomorphic CM newform of weight $4k+1$ and level four; unitary normalization gives $L(s,\Xi_k)$. Its positive zero ordinates, multiplied by $6/\pi$, are uniformly distributed modulo one. The exact lattice therefore has density zero, with multiplicity. Negative $k$ has the same zeros. This conclusion counts the full divisor, including the critical line. [Hecke–Shimura construction, Theorem 1.4](https://arxiv.org/pdf/math/0511228#page=3) · [Akbary and Murty, Corollary 11](https://www.cs.uleth.ca/~akbary/uniform.pdf#page=13)

## What the absolute sum measures

For this very same test the sum of norms is
$$
 A_\Phi(\alpha)=2\sum_{k=1}^\infty 2^{1-k}
 \sum_{\substack{\rho:\,L(\rho,\Xi_k)=0\\ 0<\Re\rho<1,\ |\Re\rho-1/2|\ge\alpha}}
      m_{\rho,k}\,|R_o(\rho-1/2)|.
$$
Every summand on an off-central site is strictly positive. Consequently $A_\Phi(1/n)$ is nondecreasing, and its liminf is zero if and only if **every** $L(s,\Xi_k)$, $k\ne0$, has all its nontrivial zeros on the critical line. This latter assertion is open. The signed identity above therefore resolves the paper’s sum for a specific infinite angular family of test coefficients while leaving the full assertion over $\mathbb Q(i)$ open.

## A countable set of signed translates that detects every angular row

The exact symmetry admits a test of its limits. For $h\ge6$ and real $\theta$ take the physical translates
$$
 \Phi_{\theta,h}(x)=V^{-1}W(e^{-i\theta}\Xi_1(x))\,g(\log|x|-h).
$$
Every translate is admissible since its support has positive logarithmic norm. These are translations of one actual test: any pair $(h,\theta)$ is realized by a class with log norm $h$ and $\Xi_1$-phase $\theta$, using a standard real section and a norm-one complex rotation. This specifies the physical translation independently of the section used to list the zeros. At $\theta=0$ cancellation holds for **every** $h\ge6$, even on either exterior wing counted by itself, since the terms cancel at each matching raw zero. At $h=0$ the symmetric two-wing sum of each individual row also vanishes by the self-dual functional equation and the oddness of $R_o$.

At a fixed width $\alpha>0$, the signed assertion for all the prescribed translates with $\theta=1/j$, $j=1,2,\ldots$, and $h\in\mathbb Q$, $h\ge6$, is equivalent to the absence of exterior zeros for every $\Xi_k$, $k\ne0$. More precisely, if any exterior zero exists, a **single rational $h\ge6$** makes the signed sum nonzero for all but finitely many $\theta\bmod 2\pi$. The same proof works with only one of the two closed exterior wings.

Indeed fix a row $k$ with an exterior site and write $w=\rho-1/2$. Its function of radial translation is
$$
 S_k(h)=\sum_{\rho\ {\rm exterior}}m_{\rho,k} R_o(w)e^{hw}.
$$
It is continuous by uniform convergence on compact real $h$ intervals. If it vanished for all $h\ge6$, its Laplace transform against $e^{-s(h-6)}$ would give, for $\Re s>1/2$,
$$
 0=\sum_{\rho\ {\rm exterior}}\frac{m_{\rho,k}R_o(w)e^{6w}}{s-w}.
$$
For this fixed row the sites have no finite accumulation, and its coefficients are absolutely summable. The right side continues meromorphically by normal convergence away from its poles; the residue at each site is $m_{\rho,k}R_o(w)e^{6w}\ne0$. Hence some rational $h\ge6$ has $S_k(h)\ne0$. At that $h$, the full signed sum is the Fourier series with terms $2^{1-k}(e^{ik\theta}-e^{-ik\theta})S_k(h)$ for $k\ge1$. The row bound $S_k(h)=O_{g,h}(\log(2+k))$ makes this series holomorphic on $|\Im\theta|<\log 2$. It has a nonzero Fourier coefficient, so its real zeros are isolated and finite in a period. This proves the assertion about rotations and the stated countable criterion. The converse follows immediately from absence of exterior sites. KadirKess used the single-character radial-translation argument to reduce exterior cancellation to a family with a separate angular test for each character. The Fourier coefficients of the one compact angular function here recover all the Gaussian rows from an accumulating sequence of rotations. [Earlier translated-profile criterion](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7128949260)

## A real finite-order example outside the norm lifts

The ray group of $\mathbb Q(i)$ at $7\mathbb Z[i]$ is $A=\mathbb F_{49}^\times/\mu_4$, cyclic of order 12. The residue of $2+i$ has order 48 since its norm $5$ has order 6 modulo 7. Its class $v$ generates $A$ and conjugation sends $v$ to $v^7$. Let $\eta_j(v)=\exp(2\pi i j/12)$. Take the following real, inversion-even angular function on the idèle classes, with the ray characters pulled back by reciprocity:
$$
 Y=\bar\eta_1+\bar\eta_{11}-\bar\eta_7-\bar\eta_5 .
$$
It is odd under field conjugation and $Y(v)=2\sqrt3$. Each of its four characters is primitive of Gaussian conductor $7\mathbb Z[i]$ and fails conjugation invariance. The two pairs $(1,7)$ and $(11,5)$ have identical functions within each pair by conjugating ideals. The two functions belonging to the different pairs are genuinely different: at $109=3^2+10^2$ both prime-ideal classes equal $v^2$, so their Dirichlet coefficients are $2e^{i\pi/3}$ and $2e^{-i\pi/3}$.

Use the even radial profile $g_e(u)=(f(u)+f(-u))/(1-e^{-3/2})$. Its transform equals one at $1/4$ and is proportional to $\sinh(3z)z(z^2-1/4)G(z)B_{3/344}(z)^{172}$, nonzero whenever $0<|\Re z|<1/2$. The real physical test $V^{-1}Y(x)g_e(\log|x|)$ is even under inversion in **both factors** and vanishes on norm-one classes. Its selected Mellin samples are $+M_{g_e},+M_{g_e},-M_{g_e},-M_{g_e}$ in the order shown in $Y$. Thus the signed sum vanishes **separately on each of the two exterior wings** at every positive width, by the two distinct-character equalities. No zeros or low ordinates have to be assumed or computed. [Finite-field and split-prime check](verify_exact_pair.py) · [Exact output](exact-pair.json)
