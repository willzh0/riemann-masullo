# A finite-window count of off-line zeros

For Masullo, Theorem 12.5.1.1, pp. 519–520, issue #5571. This is a written reduction. The missing comparison is a uniform lower bound for the contribution of zeros on the critical line.

Fix a number field and a normalized unitary Hecke character $\chi$. Let $d$ be the degree, $Q=|D_F|N\mathfrak f_\chi$, and $e=\mathbf 1_{\chi=1}$. Write $\Lambda_\chi$ for the project's meromorphically continued gamma-times-finite completion. The conductor-normalized entire completion is
$$
\Xi_\chi(s)=[s(s-1)]^eQ^{s/2}\Lambda_\chi(s).
$$
Take removable values at the principal poles. Its zeros $\rho=\beta+i\gamma$ are counted with multiplicity $m_\rho$. Define $N_{\rm off}=\sum_{\beta\ne1/2}m_\rho$ in the extended nonnegative integers. Both signs of $\gamma$ enter the sum for every character.

For $b>1$ let $X(b)=b\Re(\Xi_\chi'/\Xi_\chi)(1/2+b)$. The gamma and conductor terms give
$$
X(b)=M(b)+O_\chi(b^{-1}),\qquad
M(b)=\tfrac12db\log(b/(2\pi))+\tfrac12b\log Q+C_\chi,\qquad
C_\chi=2e+\sum_{v\ {\rm real}}(\epsilon_v/2-1/4)+\sum_{v\ {\rm complex}}|m_v|/2 .
$$
Here $\epsilon_v$ is the real parity and $m_v$ the complex angular parameter. Indeed, for a fixed imaginary archimedean shift Stirling's formula gives $\Re\psi(z)=\Re(\log z-1/(2z))+O(|z|^{-2})$. A real gamma factor contributes $b\log(b/(2\pi))/2+\epsilon_v/2-1/4+O_\chi(b^{-1})$, a complex factor contributes $b\log(b/(2\pi))+|m_v|/2+O_\chi(b^{-1})$, and the two pole-clearing factors give $2e+O(b^{-1})$. Absolute convergence of the logarithmic derivative of the finite Euler product at real part two bounds its value at $\sigma\ge2$ by $O_\chi(2^{-(\sigma-2)})$. [Project normalization (Ch. 3, §2)](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch03_IdelicZeta/Sec2.lean#L190) · [Digamma expansion, DLMF 5.11.2](https://dlmf.nist.gov/5.11.E2)

For $n\ge1$ put $a=16^n$, $b_j=a\sqrt{1+j/n}$ for $0\le j<n$, and
$$
K_n(z)=\prod_{j<n}\frac{b_j^2}{b_j^2+z^2},\qquad
c_j=(-1)^j\frac n{n+j}\binom{2n-1}{n-1}\binom{n-1}{j}.
$$
Then
$$
D_n=\sum_{j<n}c_j M(b_j)-
\sum_{\substack{\beta=1/2\\|\gamma|\le32a}}m_\rho K_n(\gamma)
\ \longrightarrow\ N_{\rm off}.
$$
In particular a fixed $\eta_\chi>0$ and an unbounded sequence with $D_n\le2-\eta_\chi$ suffice to exclude every off-line zero for this character. The implication still holds when the second sum is replaced by certified lower bounds. Without off-line zeros the exact expression tends to zero.

## Proof

The functional equation and conjugation give same-character reflection $\rho\mapsto1-\bar\rho$ with equal multiplicity. Subtract the genus-one Hadamard logarithmic derivatives at $1/2+b$ and $1/2-b$. The exponential constant and all $1/\rho$ terms cancel. The real logarithmic derivatives at these two points are negatives by reflection. Writing $z_\rho=\gamma+i(\beta-1/2)$ gives the absolutely convergent identity
$$
X(b)=\sum_\rho m_\rho\,\Re\frac{b^2}{b^2+z_\rho^2}.
$$
In fact the real summand is $b/2$ times the sum of $(b\pm(\beta-1/2))/((b\pm(\beta-1/2))^2+\gamma^2)$. This derivation also covers non-real characters.

Partial fractions in $z^2$ give $K_n(z)=\sum_j c_jb_j^2/(b_j^2+z^2)$. Evaluating at zero gives $\sum c_j=1$. The displayed binomial coefficients give $\sum|c_j|\le8^n$. Consequently $\sum_j c_j X(b_j)=\sum_\rho m_\rho\Re K_n(z_\rho)$, while replacing $X$ by $M$ costs $O_\chi(8^n/a)$.

For real $t$ and $|u|\le1/2$, maximizing over $t$ gives $|\arg(b^2+(t+iu)^2)|\le\arcsin(|u|/b)$. In particular $\sum_j|\arg(b_j^2+z_\rho^2)|\le n/a<\pi/2$. Thus $\Re K_n(z_\rho)>0$ at every zero. For fixed $z$ the product tends to one because $\sum_j |z^2|/b_j^2\le n|z|^2/a^2\to0$. If the off-line set is finite, add its limits. If it is infinite, positivity permits retaining any finite subset. This gives divergence to $+\infty$ without an upper bound on the off-line multiplicities.

With $H=32a$, the central tail is bounded by
$$
\sum_{\substack{\beta=1/2\\|\gamma|>H}}m_\rho K_n(\gamma)
\le H^2(2a^2/H^2)^n\sum_{|\gamma|>1}m_\rho/\gamma^2
=1024\,2^{-n}\sum_{|\gamma|>1}m_\rho/\gamma^2 .
$$
The last sum is finite by the order-one product. The arithmetic and truncation errors are therefore $O_\chi(2^{-n})$. The remaining limit follows from positivity and reflection, which pairs every off-line zero with a distinct site.

A simpler option uses only two widths. For $b\to\infty$ take $4X(b)/3-X(2b)/3$. Its kernel is $K_b(z)=4b^4/((b^2+z^2)(4b^2+z^2))$ and its elementary arithmetic term is $b[d\log(b/(4\pi))+\log Q]/3+C_\chi$. Use the central window $|\gamma|\le b^2$. Its tail is at most $4\sum_{|\gamma|>b^2}m_\rho/\gamma^2=o(1)$, giving the same exact count with a quadratic height window.

## A finite rational example

Choose the four squared widths $256,320,384,448$ independently of the expanding sequence above. Their partial-fraction weights are $35,-84,70,-20$. For $\zeta$ the program certifies one zero in each of 112 disjoint positive Hardy sign-change brackets below $256.5$, refines each bracket by 32 bisections, and counts the reflected brackets too. If $u_i$ are the positive upper endpoints, the single residual satisfies
$$
U=\sum_{j=0}^3c_j X(b_j)-2\sum_iK(u_i)<3.24779\cdot10^{-8}.
$$
Writing $\theta=\sum_j\arcsin(1/(2b_j))$, a missing site at $|\gamma|\le T$ contributes at least $\cos\theta\,\prod_j b_j^2/(b_j^2+T^2+1/4)$. The reflected pair at $T=173$ costs more than $3.33260\cdot10^{-8}$, and the rational off-line quartet at $T=189$ costs more than $3.30953\cdot10^{-8}$. The alternating eta series excludes a real zero in $(0,1)$. Thus all zeta zeros through height $189$ are on the line, using one unshifted weighted sum. A separate check at 300 bits verifies 224 endpoint signs and the four exact logarithmic derivatives. This illustrates the finite comparison on a previously known range. [Earlier 771-term sign formula and uniform error](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7153429283) · [Previous translated comparison to 256.5](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7153778840)

Install Python with python-flint 0.9.0. Run the scripts in the order shown. Each writes its own JSON beside the script. The main certificate uses only finite sums and interval arithmetic for elementary functions and the gamma factor. The independent verifier calls the actual zeta function.

```shell
python finite_certificate.py
python verify_certificate.py
python check_kernel.py
```

Hiary, Ireland and Kyi develop the shifted positive resolvent and finite sign-change method in Theorems 7 and 11. Büthe's Theorems 3.2 and 4.5 give positive explicit-formula completeness tests, including Hecke characters over number fields. The problem left here is a lower bound for the finite critical-line mass along unbounded heights for each fixed character. [Hiary–Ireland–Kyi (2024)](https://arxiv.org/html/2408.00187v1) · [Büthe (2015)](https://arxiv.org/pdf/1308.6704)
