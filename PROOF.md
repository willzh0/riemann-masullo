# A finite critical-line certificate for the quartic character modulo 5

For the primitive character with $\chi(2)=i$, exactly **13 nontrivial zeros** have $|\Im\rho|\le22$. Each is simple and has real part $1/2$. Seven have negative ordinate and six have positive ordinate. This is a written mathematical argument with interval-arithmetic certificates run at 160 and 224 bits.

The four meshes produced **567 conservative passes in 40,324 consecutive comparisons**. Those events measure a rise in magnitude. The zero count follows separately from 31 Hardy sign changes and a translated arithmetic upper bound. The sign scan proves at least 16 negative and 15 positive critical-line zeros in $[-40,40]$. Completeness here was checked on the closed subwindow $[-22,22]$. The all-height signed inequality in #5571 remains open.

## Character, phase and the choice of signed heights

In residues $0,1,2,3,4$, the values of $\chi$ are $0,1,i,-i,-1$. The generator $2\bmod 5$ has order four, so this specifies a multiplicative, odd, nonprincipal character of prime conductor 5. With $s=1/2+it$ and the Gauss sum $\tau=\sum_{r=1}^4\chi(r)e^{2\pi ir/5}$, the normalization is

$$
\Lambda_\chi(s)=(5/\pi)^{(s+1)/2}\Gamma((s+1)/2)L(s,\chi),\qquad
\Lambda_\chi(s)=\varepsilon_\chi\,\overline{\Lambda_\chi(1-\bar s)}.
$$

Pairing residues $1,4$ and $2,3$ gives $\tau=2i\sin(2\pi/5)-2\sin(4\pi/5)$. Thus
$$
\varepsilon_\chi=\tau/(i\sqrt5)
=\sqrt{(5+\sqrt5)/10}+i\sqrt{(5-\sqrt5)/10}
=0.85065080835203993218\ldots+0.52573111211913360603\ldots\,i .
$$
The script encloses the finite Gauss sum, its trigonometric expression and the radical formula. For the principal square root, $\arg\varepsilon_\chi/2=0.276787179448522625754266\ldots$. The completed functional equation makes the following Hardy function real and real analytic. The rotation has modulus one and the gamma factor is regular at all real $t$.
$$
 Z_\chi(t)=
 \frac{\Gamma(3/4+it/2)}{|\Gamma(3/4+it/2)|}
 e^{\,it\log(5/\pi)/2}\,L(1/2+it,\chi)/\sqrt{\varepsilon_\chi}.
$$
The reflected zero $1-\bar\rho$ belongs to the same character at the same ordinate. Conjugating the ordinate exchanges $\chi$ with $\bar\chi$. Direct enclosures for this fixed $\chi$ give $2.60369703536006\le |L(1/2-6i,\chi)|\le2.60369703536007$ and $0.22500822125435\le |L(1/2+6i,\chi)|\le0.22500822125436$. [DLMF, primitive character functional equation and Gauss sum](https://dlmf.nist.gov/25.15#E5)

## Finite line polynomial and its tail

Write $f(m)=m^{-s}$, $\Delta f(m)=f(m+1)-f(m)$. Starting with the periodic sequence $a_0=\chi$, take the unique mean-zero period-five sequence satisfying $a_{h+1}(r-1)-a_{h+1}(r)=a_h(r)$ cyclically. It exists because $\sum_r a_h(r)=0$. Subtracting the mean after taking the five partial sums computes its Gaussian-rational entries exactly. Summation by parts, first on finite intervals and then at infinity, gives
$$
 L(s,\chi)=\sum_{m=1}^{N-1}\chi(m)f(m)
 +\sum_{h=0}^{p-1}a_{h+1}(N-1)\Delta^h f(N)
 +\sum_{m=N}^{\infty}a_p(m)\Delta^p f(m).
$$
The character has bounded partial sums, so its series converges for $\Re s>0$ and agrees there with its continuation. The boundary terms vanish since the periodic sequences are bounded and $\Delta^h f(m)=O_s(m^{-1/2-h})$ on the line.

Expanding each forward difference by the binomial theorem makes the first two sums an explicit finite polynomial in $m^{-s}$ with Gaussian-rational coefficients. There are 232 nonzero coefficients with $1\le m\le283$, for $N=256,p=28$. Iterating the fundamental theorem of calculus on $[0,1]^p$ gives
$$
 |\Delta^p f(m)|\le |(s)_p|m^{-1/2-p}.
$$
Here $(s)_p=s(s+1)\cdots(s+p-1)$. The exact coefficient bound is $A_p=\max_r(|\Re a_p(r)|+|\Im a_p(r)|)=987/78125$. On all $|t|\le40$ the remainder satisfies
$$
 A_p\frac{(N-1)^{1/2-p}}{p-1/2}\prod_{h=0}^{p-1}\sqrt{(h+1/2)^2+40^2}
 <1.636\cdot10^{-24}.
$$
The program adds this uniform remainder to every complex value or magnitude enclosure. Individual grid magnitudes use elementary integer logarithms, exponentials and square roots.

As a separate check, the four series for residues $r=1,\dots,4$ were evaluated by Euler–Maclaurin at $t=0,\ \pm1,\ \pm6,\ \pm12,\ \pm24,\ \pm40$. For each residue, retain 32 terms and put $x=160+r$. Add
$$
 x^{-s}\left(\frac{x}{5(s-1)}+\frac12\right)
 +\sum_{j=1}^{12}\frac{B_{2j}5^{2j-1}(s)_{2j-1}}{(2j)!}\,x^{-s-2j+1}.
$$
For general $p=12$ the omitted term has magnitude at most
$$
 \frac{4\,5^{2p-1}|(s)_{2p}|}{6^{2p}(2p-1/2)}x^{1/2-2p}.
$$
This follows by integrating the $2p$-th derivative in the periodic Bernoulli remainder, using $\sup|B_{2p}(\{\cdot\})|/(2p)!\le2\zeta(2p)/(2\pi)^{2p}\le4/6^{2p}$. The formula continues from $\Re s>1$ to the critical line, since the remainder integral converges there. Multiplication by $\chi(r)$ and summation give four outward complex rectangles whose sum overlaps the independent finite-polynomial rectangle at every test ordinate.

## Conservative consecutive-grid calibration

At mesh parameter $n$, let $t_k=k/n^2$ for every $-n^3\le k\le n^3+1$. The last value is retained for the successor comparison. The output contains exact integers $r_k$, denominator $B=2^{n+20}$, and the proved inequality
$$
 \big|\,r_k/B-|L(1/2+it_k,\chi)|\,\big|<2^{-n}
$$
at every node. The number $r_k$ is obtained by flooring a scaled ball midpoint. The error inequality uses the full finite-polynomial ball and the analytic tail, independent of that choice of midpoint. The code restarts the geometric progression of phases every 128 nodes and checks the first node, zero and the last successor directly at each mesh.

An integer comparison accepts the left node $k$ exactly when
$$
 (n+1)(r_k+2^{20})<n\max(0,r_{k+1}-2^{20}).
$$
This implies $(n+1)|L(1/2+it_k,\chi)|<n|L(1/2+it_{k+1},\chi)|$. The high-precision balls independently decide this latter strict criterion at every pair. Counts are classified by the sign of the left index.

| $n$ | Comparisons | Accepted $k<0$ | Accepted $k\ge0$ | Actual strict rises $k<0$ | Actual strict rises $k\ge0$ |
|---:|---:|---:|---:|---:|---:|
| 8 | 1,025 | 4 | 5 | 8 | 8 |
| 12 | 3,457 | 36 | 24 | 37 | 26 |
| 16 | 8,193 | 65 | 66 | 65 | 66 |
| 24 | 27,649 | 196 | 171 | 196 | 171 |

The 577 actual strict rises include ten which the conservative margin does not decide as passes. The four meshes calibrate the finite criterion. A single rise supplies a comparison between two magnitudes and carries no conclusion about a zero between those samples.

## Certified Hardy signs

The initial scan uses the 641 endpoints $t=k/8,\ |k|\le320$. Each sign-changing bracket is bisected to width $2^{-24}$. Both endpoint signs of each final bracket are independently enclosed in two ways. The first uses Acb's gamma function in the normalization above. The second uses finite real elementary sums for the phase. All 62 signs agree. Each bracket contains at least one critical zero of odd multiplicity because a nonzero real analytic function changing sign on a compact interval with nonzero endpoints must have at least one zero of odd order in its interior.

For the second check set $x=3/4$, $b=t/2$, $M=256$ and
$$
 \theta_M=b\log M-\sum_{k=0}^M\arctan\frac{b}{x+k}.
$$
Euler's limit for $\Gamma(x+ib)$ shows that the limiting angle represents its phase. The increments of $\theta_m$ are $b\log(1+1/m)-\arctan(b/(m+1+x))$. The inequalities $|\log(1+1/m)-1/m|\le1/(2m^2)$, $|u-\arctan u|\le|u|^3/3$, and the integral test bound the limiting angle error by
$$
 |\theta-\theta_M|\le\frac{|b|(3/2+x)}{M-1}+\frac{|b|^3}{6(M-1)^2}.
$$
Rotating the complex $L$-value rectangle by this whole angle interval gives an outward real interval at every saved endpoint. For example, the first negative zero closest to zero occurs in $(-69338619/16777216,-34669309/8388608)$, and the first positive one in $(103743227/16777216,25935807/4194304)$. [DLMF, Euler's product limit](https://dlmf.nist.gov/5.8#E1)

## Translated arithmetic and the closed windows

For $\rho=\beta+i\gamma$ running through nontrivial zeros with multiplicity and $s=2+iy$, the completed logarithmic derivative satisfies
$$
 D_\chi(y)=\Re\frac{\Lambda_\chi'}{\Lambda_\chi}(2+iy)
 =\sum_\rho \frac{2-\beta}{(2-\beta)^2+(y-\gamma)^2}.
$$
The real constant in the genus-one partial fraction expansion cancels by $\Re B=-\sum_\rho\Re(1/\rho)$. This is the primitive finite-order case of Zaman's Lemma 2.2.1. The real parts converge absolutely, the strip gives $0<\beta<1$, and there are no principal polar terms. This signed-$y$ identity uses exactly the character in the table above. [Zaman, *Analytic estimates for the Chebotarev Density Theorem and their applications*, Lemma 2.2.1, pp. 32–33](https://www.math.toronto.edu/zaman/files/thesis.pdf#page=41)

For the prime-power enclosure with $K=32768$, calculate
$$
 \tfrac12\log(5/\pi)+\tfrac12\Re\psi((3+iy)/2)
 -\Re\sum_{m\le K}\Lambda(m)\chi(m)m^{-2-iy}.
$$
The sieve inserts $\log p$ for every unramified power $m=p^a$. The discarded absolute sum is at most $\sum_{m>K}\log(m)/m^2\le(\log K+1)/K<0.000347816$. The code evaluates the prime factors and all arithmetic intervals on each signed center.

An independent enclosure uses only direct integer sums for $L(2+iy)$ and $L'(2+iy)$ through $N=8192$. Their remainders are at most $1/N$ and $(\log N+1)/N$. Complex ball division is performed after checking that the denominator rectangle excludes zero. To enclose $\psi(z)$, $z=(3+iy)/2$, use
$$
 \Psi_M(z)=\log M-\sum_{k=0}^M (k+z)^{-1},\qquad
 |\Re(\psi(z)-\Psi_M(z))|\le \frac{1/2+|1+z|}{M-1},\quad M=4096.
$$
The limit follows from the elementary digamma series. The bound comes from $|\log(1+1/m)-1/(m+1+z)|\le(1/2+|1+z|)/m^2$, since $\Re z>0$, and summation from $M$. Thus the final signs and upper bounds also have a complete calculation by elementary functions and finite integer sums, including the gamma and digamma contributions. [DLMF, digamma series](https://dlmf.nist.gov/5.7#E6)

For each Hardy bracket $J=[l,u]$, select one odd-multiplicity zero in its interior. At center $y$, these distinct representatives have total mass at least the exact rational
$$
 H(y)=\sum_J\frac{a}{a^2+\max(|y-l|,|y-u|)^2},\qquad a=3/2 .
$$
All remaining copies have positive mass. If an unrepresented copy has $|y-\gamma|\le2$, its mass is at least $\min_{1\le b\le2} b/(b^2+4)=1/5$, using $b=2-\beta$. Consequently $D_\chi(y)-H(y)<1/5$ excludes every additional copy in the closed cell. The recorded residual is an upper bound for unrepresented mass because $H(y)$ is a lower bound for represented mass.

| Center $y$ | Listed zeros in $[y-2,y+2]$ | Upper bound on $D_\chi(y)-H(y)$ |
|---:|---:|---:|
| −20 | 2 | 0.068369007214 |
| −16 | 2 | 0.062174002220 |
| −12 | 1 | 0.058199249422 |
| −8 | 1 | 0.055738801249 |
| −4 | 1 | 0.054432406024 |
| 0 | 0 | 0.054110960786 |
| 4 | 0 | 0.054734570294 |
| 8 | 2 | 0.056379593839 |
| 12 | 1 | 0.059264383631 |
| 16 | 2 | 0.063829056378 |
| 20 | 1 | 0.070933836364 |

The prime-power calculation has worst upper bound $0.070933836364$. The direct integer calculation gives a lower bound $0.127183416886$ for the smallest margin below $1/5$. No bracket straddles any cell edge. These eleven closed cells cover $[-22,22]$, including zero and both outer endpoints. Every listed zero in the cover is simple and is the only zero in its bracket. The remaining 18 sign-change brackets supply additional selected zeros outside the cover and tighten $H(y)$.

## Exact comparison with Hiary–Ireland–Kyi and the principal-character calibration

Hiary–Ireland–Kyi §4 assumes real Dirichlet coefficients, which give conjugate ordinates. Their §5 Theorem 11 treats $\zeta$. For $z=x+iy,\ x\le0,\ y>0$, its assumptions include $0<\tau\le y$, a finite family of nonempty disjoint genuine sign brackets contained in $[y-\tau,y+\tau]$ and omitting $y$, and $0<\eta\le y$. Write
$$
 \phi(\beta,\eta,x)=\frac{\beta-x}{(\beta-x)^2+\eta^2}
 +\frac{1-\beta-x}{(1-\beta-x)^2+\eta^2},
$$
set $\phi_0=\phi(0,\eta,x)$, $\phi_m=\phi(1/2,\eta,x)$, and form $H$ from the far endpoints with $a=1/2-x$. The three strict antecedents are $H+g_j>\Re v_{1,z}$, with $g_1=\min(\phi_0,\phi_m)$, $g_2=\phi_m$, $g_3=\min(\phi_0,\phi_m/2)$. They imply centrality, simplicity of central zeros, and completeness with simplicity, respectively. [Hiary, Ireland and Kyi, §4](https://arxiv.org/html/2408.00187v1#S4) and [§5, Theorem 11](https://arxiv.org/html/2408.00187v1#S5)

For this character the separate signed identity above gives the translated weights. The same-height reflection interchanges $\beta-x$ and $1-\beta-x$, so the correct right-half-plane evaluation is $1-\bar z=2+iy$ for $x=-1$. At $\eta=2$ the thresholds become $9/20,12/25,6/25$. For an off-line pair, writing $w=(\beta-1/2)^2\in[0,1/4]$ gives a cost of at least $3(25/4-w)/((25/4)^2+(7/2)w+w^2)$, decreasing to $9/20$. A nonsimple central zero costs at least two additional central copies at $6/25$ per copy. Indeed a selected nonsimple zero has odd order at least three, and an unselected nonsimple zero has order at least two. A further simple central zero costs at least $6/25$. This proves the translated implications for this character at both signs using its own arithmetic data.

With the one-sided paper geometry, take $\tau=|y|$ and retain only brackets in $[y-|y|,y+|y|]$ avoiding $y$. At positive centers $8,12,16,20$, all three inequalities pass. At $y=4$ only (i) and (ii) pass, with the computed residual in $[0.251684327021,0.252379957381]$ above $g_3=0.24$. The directly computed negative centers $-4,-8,-12,-16,-20$ pass all three fixed-character inequalities. The stronger two-sided table uses all 31 brackets and the direct positive-mass inequality. Its radius-two cell at zero uses the direct argument as well. The machine output retains all margins, selected counts and geometries.

The earlier principal-$\mathbb Q$ example uses 771 base integers, the principal polar factors, and conjugation for the other sign of the ordinate. Its sign brackets and translated upper estimates give 112 simple positive zeros through 256.5 in the updated receipt. Here the gamma shift is odd, the nonprincipal completed function has no polar correction, and both signs for this fixed nonreal character were computed. [Earlier numerical $\zeta$ verification and update](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7153778840)
