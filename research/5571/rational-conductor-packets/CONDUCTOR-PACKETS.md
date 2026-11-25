# Finite angular levels of the rational trace

Masullo, §12.3, p. 514 and Theorem 12.5.1.1, pp. 519–520. On the rational field the exterior sum of each individual character remains open. The assertions below concern actual finite angular tests and their dependence on the conductors. The scalar has a Hilbert-space trace interpretation when the two quotient convolutions in the width-restriction theorem have nuclear witnesses. [Literal centered exterior sum](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch12_TraceGeometric/Sec5.lean#L98) · [Width restriction](https://github.com/mccorvie/riemann-masullo/pull/7630)

## A bound for each angular cylinder

Use the rational norm section with positive real component. Write $G_q=(\mathbb Z/q\mathbb Z)^\times$, and let $\chi^*$ be the primitive Dirichlet character inducing $\chi\bmod q$. Each occurs once. The arithmetic lift to the idèle classes has angular value $\chi(\operatorname{res}_q u)^{-1}$ and unramified Euler value $\chi^*(p)$. Consequently the *single* Bruhat test
$$
 V^{-1}{\bf1}_{\operatorname{res}_q u=r}H(\log|u|),\qquad r\in G_q,
$$
assigns the coefficient $\overline{\chi(r)}/\phi(q)$ to the row of $\chi^*$ and zero to rows of higher angular level. Here $V$ is the norm-one Haar mass. The argument is integration of a character over a coset of an open subgroup of the compact norm-one group. [Idelic inverse convention](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/External/AlgebraicNumberTheoryLean/Chebotarev/DirichletHeckeRat.lean#L493) · [Agreement with the primitive Dirichlet series](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch13_ZerosHecke/Targets.lean#L278)

At center zero, fix $0\le\alpha<1/2<\beta$ and $s>1$. Write $d_\rho$ for the number of jets lost on restriction from $\beta$ to $\alpha$, and $m_\rho$ for the positive order at a zero of the completed primitive function. Fix $0<\delta\le\min(1/2-\alpha,\beta-1/2)$ with $\sigma=1/2+\delta<1$. Put
$$
 \theta=(1-\sigma)\min\{3/(2-\sigma),2/\sigma\}<1.
$$
For $P(z)=(z^2-\tfrac14)z(z-1)$, $g\in C_c^\infty([-1,1])$, $c>0$, $|t|\le M$, let
$$
 H_{\eta,t}(x)=\eta^4P(-\partial_x)\,g((x-c-\eta t)/\eta),\qquad 0<\eta\le1 .
$$
Write $\widehat H(z)=\int H(x)e^{zx}\,dx$. For every $\epsilon>0$,
$$
 \Gamma(q,\eta):=\frac1{\phi(q)}\sum_{\chi\bmod q}\sum_{\rho\ {\rm of}\ \chi^*}
 (m_\rho-d_\rho)|\widehat H_{\eta,t}(\rho)|
 \ll_{g,c,M,\delta,\epsilon}(\eta/q)^{1-\theta-\epsilon}.
 \tag{1}
$$
For the actual centered exterior sum replace $m_\rho-d_\rho$ by $m_\rho{\bf1}_{|\Re\rho-1/2|\ge\alpha_0}$ and $\rho$ by $\rho-1/2$, choosing $0<\delta\le\alpha_0$. This includes the edges. For a fixed smooth radial $H$ of compact support the bound is $O_{H,\delta,\epsilon}(q^{-(1-\theta)+\epsilon})$. If $H(0)=0$, its angular cylinders are admissible norm-one-vanishing tests in #5571.

Indeed, $0\le d_\rho\le m_\rho$ always, and every order is lost for $|\Re\rho-1/2|<\delta$. Right-hand missing multiplicities are bounded by the zeros of the product of **all** characters at the one modulus $q$. The extra Euler factors of imprimitive characters have their zeros on $\Re s=0$. Reflection $\rho\mapsto1-\bar\rho$ bounds the other side by the same count, including for a complex character. Montgomery's bound as printed in Jutila (1.1) is $O((qT)^\theta\log^{14}(2qT))$ for $T\ge2$. On either fixed Mellin strip the test transform is $O_A(\eta(1+\eta|\Im z|)^{-A})$. Sum first to $\max(2,\eta^{-1})$ and then over its dyadic multiples. Before absorbing logarithms the result is bounded by a constant times
$$
 (\eta/q)^{1-\theta}\,(q/\phi(q))\,\log^{14}(2q/\eta).
$$
The elementary inequality $q/\phi(q)\le\zeta(2)(1+\log q)$ suffices. For example multiply $\prod_{p\mid q}(1+p^{-1})$ out and sum over divisors. The two outer suprema over width weights and bounded $t$ require no zero spacing. [Jutila, *On a density theorem of H. L. Montgomery for L-functions*, p. 3, (1.1), including the height, modulus, and edge conventions](https://www.acadsci.fi/mathematica/1972/no520pp01-13.pdf#page=3)

## Exact arithmetic weights and the finite-conductor error

Suppose $H$ is smooth, compactly supported in $x>0$, and $\widehat H(0)=\widehat H(1)=0$. For the shrinking family it suffices to take $\eta(M+1)<c$. Put $I_a(H)=\int_0^\infty H(x)e^{-ax}/(1-e^{-2x})\,dx$, where $a=0$ for an even character and $a=1$ for an odd one. The positive-log explicit formula is
$$
 F_\chi(H):=\sum_\rho m_\rho\widehat H(\rho)
 =-\sum_{p^k}\chi^*(p^k)\log p\,H(\log p^k)-I_a(H).
$$
One can shift the smoothed contour for $-L'/L(s,\chi^*)$. The trivial zeros are $-a-2k$, the conductor distribution is supported at log norm zero, and for the principal character the correction is $\widehat H(1)+\widehat H(0)$. This last term vanishes. [Battistoni and Molteni, Theorem 7, (3.15)](https://sites.unimi.it/molteni/research/papers-pdf/Explicit%20formulae%20for%20L-functions%20and%20generators%20of%20the%20class%20group.pdf)

For $n=p^k$ write $q=p^e m$, $p\nmid m$. The cylinder coefficient of this prime power and the archimedean kernel are exactly
$$
 W_{q,r}(p^k)=\frac{{\bf1}_{r\equiv p^k\bmod m}}{\phi(p^e)},\qquad
 K_{q,r}(x)=\tfrac12\left(\frac{{\bf1}_{r=1\bmod q}}{1-e^{-x}}
                 +\frac{{\bf1}_{r=-1\bmod q}}{1+e^{-x}}\right).
$$
Indeed if $p\mid q$ only characters with trivial $p^e$-component survive at $p$. Orthogonality on the coprime part leaves the indicated weight. For the archimedean kernel project even and odd characters by $(1\pm\chi(-1))/2$. At $q=1,2$ both indicators contribute. The $r=1$ ramification term also appears in Fiorilli and Miller's family explicit formula. [Fiorilli and Miller, §3.1, (3.4)–(3.5)](https://web.williams.edu/Mathematics/sjmiller/public_html/math/papers/DirichletZeros_DFandSJM_240arxiv.pdf)

Write $D_\chi(H)=\sum_\rho d_\rho\widehat H(\rho)$ and $D_{q,r}(H)=\phi(q)^{-1}\sum_\chi\overline{\chi(r)}D_\chi(H)$. Then
$$
 D_{q,r}(H)=-\sum_{p^k}\log p\,W_{q,r}(p^k)H(\log p^k)
             -\int H(x)K_{q,r}(x)\,dx+E_{q,r},\qquad |E_{q,r}|\le\Gamma.
 \tag{2}
$$
Use (1) for scaled $H$ or the fixed-test estimate for fixed $H$. For a full centered trace the positive-log formula uses $e^{-x/2}H(x)$, introducing $p^{-k/2}$ in the prime sum. The centered exterior sum itself satisfies the small absolute estimate (1).

For any fixed integer $b\ge2$ and fixed $H$ as above, along *every* sequence $q\to\infty$ prime to $b$,
$$
 D_{q,b}(H)=-\Lambda(b)H(\log b)+O_{H,b,\delta,\epsilon}(q^{-(1-\theta)+\epsilon}).
 \tag{3}
$$
The archimedean indicators vanish once $q>b+1$. At $n=b$ the weight is one. At each of the finitely many other prime powers a nonzero weight requires $m\mid n-b$, so $1/\phi(p^e)\le2|n-b|/q$ (also when $e=0$). Conductor growth thus extracts the single prime power with a fixed radial test. This is an angular limit.

## The law across the actual characters

Let $\mathcal P$ be the finite set of prime bases whose powers are seen by $H$. For each $p\in\mathcal P$, take independent uniform phases $Z_p$ on the complex unit circle and independent Bernoulli variables $B_{q,p}$ of means $1/\phi(p^{v_p(q)})$, with $\phi(1)=1$. Independently choose $a\in\{0,1\}$ with equal probability. Define
$$
 Y_q=-I_a(H)-\sum_{p\in\mathcal P} B_{q,p}\log p\sum_k H(\log p^k)Z_p^k .
$$
For each fixed $j,k\ge0$, as $q\to\infty$ through arbitrary moduli,
$$
 \frac{1}{\phi(q)}\sum_{\chi\bmod q}D_\chi(H)^j\overline{D_\chi(H)}^{\,k}
 =\mathbb E\,Y_q^j\overline{Y_q}^{\,k}
 +O_{H,j,k,\delta,\epsilon}(q^{-(1-\theta)+\epsilon}).
 \tag{4}
$$
For proof, write $I_a$ as a linear function of $\chi(-1)$ and expand the full moments. A typical factor is $\chi(-1)^b\chi^*(U)\overline{\chi^*(V)}$, $b\in\{0,1\}$. Let $q_S$ be the full part of $q$ supported on primes of $UV$, and $q'=q/q_S$. Character orthogonality gives its expectation exactly as
$$
 \frac{{\bf1}_{q'\mid((-1)^bU-V)}}{\phi(q_S)}.
$$
When the signed difference is zero, this equals the model moment, by uniqueness of prime factorization. Otherwise it is $O_{H,j,k}(1/q)$ because $q'$ divides a fixed nonzero integer and $q_S/\phi(q_S)$ is bounded in terms of $\mathcal P$. The model moment is then zero. The remaining passage from full to lost moments uses (1). Uniformly in $\chi\bmod q$, each character has $O(\log(2q(2+|T|)))$ nontrivial zeros with ordinates in $[T-1,T+1]$, multiplicities included. Consequently its absolute missing mass is $O_H(\log(2q))$ and the full sum is bounded independently of $q$ by its finite prime expansion. The difference of the two monomials has average $O(q^{-(1-\theta)+\epsilon})$ after absorbing fixed logarithmic powers. [Koukoulopoulos, *The Distribution of Prime Numbers*, Lemmas 11.4(a) and 8.2(a)](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf#page=125)

In particular the mean squared magnitude of the actual lost scalar is
$$
 \frac{|I_0(H)|^2+|I_1(H)|^2}{2}
 +\sum_{p^k}\frac{(\log p)^2 |H(\log p^k)|^2}{\phi(p^{v_p(q)})}
 +O_{H,\delta,\epsilon}(q^{-(1-\theta)+\epsilon}).
$$
When all the Bernoulli parameters converge, (4) gives convergence in distribution to the indicated bounded limiting model. Tightness follows from the second moment, and bounded support determines the limiting moments. For the tower $q=\ell^e$ at a fixed prime, the base $\ell$ disappears and all other primes retain independent uniform phases. For a sharp profile supported around just one $p\ne\ell$ this law is a mixture of two uniform circles with offsets $-I_0,-I_1$.

The same tower has a pointwise consequence. On the compact angular group $\mathbb Z_\ell^\times$, evaluate a cylinder at each successive residue of a fixed $u$. Its lost-scalar limit equals $-\Lambda(n)H(\log n)$ if $u=n=p^k$ with $p\ne\ell$, the archimedean weights $-(I_0+I_1)/2$ and $-(I_0-I_1)/2$ at $u=1$ and $u=-1$, and zero elsewhere. The $\ell$-power contribution is distributed uniformly on the cylinders. For the centered exterior sums every such limit is zero. If that functional is represented by a finite measure, it has no point masses. More quantitatively, write $c_\chi$ for the fixed centered exterior scalar of a primitive character with conductor an $\ell$-power. Then $\sum_{\operatorname{cond}\chi\le\ell^e}|c_\chi|^2\ll_\epsilon (\ell^e)^{\theta+\epsilon}$ on this tower. This follows by multiplying the sum of absolute values from (1) by the unit-height bound above. The weighted square sum $\sum_\chi(1+\operatorname{cond}\chi)^{-2s}|c_\chi|^2$ therefore converges for every $s>\theta/2$. This controls the order of the angular distribution. The requirement in #5571 remains exact vanishing for each individual character.

A sharp distinction holds for the full lost distribution on this local tower. If any of the finitely many displayed atom coefficients is nonzero, its conductor Sobolev threshold is exactly $s>1/2$. For sufficiently large $e$ its atom sites are distinct modulo $\ell^e$. Full-row Parseval gives energy $\phi(\ell^e)\sum_u|\mu(\{u\})|^2+O_H(1)$. Replacing the full rows by the lost rows costs $O_H((\ell^e)^\theta\log^{15}(2\ell^e))$ by (1), the individual logarithmic zero bound and the uniform bound on the full rows. Differencing successive levels shows shell energy asymptotic to a positive constant times $\ell^e$, including divergence at $s=1/2$. If all the atom coefficients vanish, the full measure is a multiple of Haar and the previous $s>\theta/2$ bound applies to the lost distribution itself.

There is a uniform metric version of (4). The Wasserstein distance $W_1$ between the law of $D_\chi(H)$ and the indicated model is $O_{H,\delta}(1/\log(2q))$. For the two bounded full laws, the degree-$d$ discrepancy before subtracting missing jets is $O_H(L_H^d/q)$: each signed difference of products is at most $2N^d$ for a fixed largest supported norm $N$, and the sum of absolute polynomial coefficients is exponential in $d$. Expanding the exponential gives characteristic-function discrepancy $O_H(e^{K_H|t|}/q)$ on $\mathbb R^2$. Truncate a $1$-Lipschitz dual test smoothly beyond the common fixed disk, and convolve with a nonnegative probability kernel of frequency support $|t|\le T$ and first absolute moment $O(1/T)$ (the scaled, normalized square modulus of a band-limited Schwartz function suffices). Fourier inversion bounds the difference by $O_H(T^{-1}+T^2e^{K_HT}/q)$. Take a small multiple of $\log(2q)$ and couple the full and lost scalar on the same character using (1).

## Finite check at modulus five

For the [two fixed smooth translates](https://github.com/willzh0/riemann-masullo/blob/75fe70f47c3185ed11624fb7c9d776216e1cbe74/research/7353/above-one-width-defect/PRIME-SIDE.md), the full-width row of the quartic character with $\chi(2)=i$ and the real angular cylinder $r=2$ have the following values. Each displayed real or imaginary component is within $6\cdot10^{-15}$ of its displayed value.

| Profile center | Quartic row | Cylinder $r=2$ |
|---|---:|---:|
| $7/4$ | $0.293405781905632+1.889627597716255i$ | $2.255745246789718$ |
| $2$ | $-1.548438745593439-1.504191707104235i$ | $-2.267782982441304$ |

The values use the full width $\alpha=0,\ \beta\ge1$. The supplied code checks 23,496 prime-power weights in exact cyclotomic arithmetic for all moduli through 48, including 3,004 ramified cases, and 1,424 parity projections. For the numerical table it compares the Fourier average with the direct formula (2), including the previously computed eight or eleven prime powers. An independent character enumeration checked an additional 14,496 coefficients and 1,208 parity projections.

To reproduce, install python-flint 0.9.0, save the [fixed-profile numerical helper](https://github.com/willzh0/riemann-masullo/blob/75fe70f47c3185ed11624fb7c9d776216e1cbe74/research/7353/above-one-width-defect/prime_check.py) locally, and run the following with its path. The certificate writes its JSON receipt beside itself.

~~~shell
python packet_check.py /path/to/prime_check.py
~~~
