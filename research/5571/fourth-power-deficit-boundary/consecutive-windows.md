# Long consecutive blocks with zero actual complete deficit

Fix one of the two mixed fourfold cells $s=(+,-)$ or $s=(-,+)$ of the rational principal character. At each $J$, choose an ordered pair of distinct primes in $U_J=(J^{12},2J^{12}]$. Write $A_s(j;q,d)=[j^8/2-C_s(j^4;q,d)]_+$ for the actual complete deficit at a sample, and write $A'_s$ for the prime-only version. All estimates concern the prescribed coupled scale and the same pair throughout each block. [Mlyle’s complete Jacobi classes](https://github.com/mccorvie/riemann-masullo/pull/7627)

For every $0<\varepsilon<1$ there is a $c_\varepsilon>0$ such that every sufficiently large $J$ admits two deterministic intervals of consecutive integers $I_J^0,I_J^+\subseteq[c_\varepsilon J,J]$, each of length at least $J^{1-\varepsilon}$, with the following unconditional properties.

* A proportion at least $1/32$ of the ordered distinct pairs has $A_s(j;q,d)=0$ at **every** $j\in I_J^0$.
* A proportion at least $1/32$ has, simultaneously at **every** $j\in I_J^+$, both $A_s(j;q,d)\gg J^6\sqrt{\log J}$ and $A'_s(j;q,d)-A_s(j;q,d)\ge j^{16/3}/2$.

In particular there are unbounded coupled heights $K$ at which a proportion at least $1/32$ has identical cumulative complete deficits at $K$ and $K-\lfloor K^{1-\varepsilon}\rfloor$. The entire terminal block contributes exactly zero. In fact every sufficiently large $X$ contains a run of at least $X^{1-\varepsilon}$ consecutive such heights in $[c'_\varepsilon X,X]$, with the auxiliary primes sampled from the prescribed family at each height. The total contribution from earlier samples remains open at the critical scale.

If rational RH holds, both intervals can be the same terminal interval $[(1-\delta)J,J]$ with an absolute fixed $\delta>0$. The populations of pairs in the two assertions are then different. If rational RH fails, the two blocks can be made disjoint, and a common proportion tending to one satisfies their respective assertions in **all three** nonidentity cells. If a zero attains a real part $\Theta>1/2$ maximal among all zeta zeros, both block lengths can also be taken $\gg_\Theta J$.

Let $L_s(J)$ denote the longest consecutive run of zero complete deficits in $1\le j\le J$ for the drawn pair. The longest run detects whether any zeta zero attains the supremum of their real parts.
$$
 L_s(J)/J\longrightarrow0\text{ in probability}
 \quad\Longleftrightarrow\quad
 \text{no nontrivial zeta zero attains }\Theta.
$$
In the unattained case $\log(1+L_s(J))/\log J\to1$ in probability nevertheless. The attainment equivalence holds as well when each sample uses the best of the three complete cells. A separate criterion below characterizes rational RH using only exact zero increments on terminal intervals for the $h$-prime negative parity cells.

## Uniform variation of the genuine twists

For the odd primes let $P_o(x)=\sum_{p\ {\rm odd}}(x-p)_+\log p$. Write $S_q(x),S_d(x),Z(x)$ for the corresponding sums twisted by $(q/p),(d/p),(q/p)(d/p)$ respectively. For any of the three twists $\xi(p)$, define $T(t)=\sum_{p\le t,\ p\ {\rm odd}}\xi(p)\log p$. The prime-supported mean-square theorem, and conditioning in the product case, give $\|T(t)\|_2\ll\sqrt{t\log(2t)}$ for $0\le t\le J^4$ (with the sum zero for $t<3$). The implicit constant is absolute. If $X_\xi(x)$ is the first-Riesz sum of this twist then $X_\xi(x)=\int_0^x T(t)\,dt$, and hence for $0\le x_1\le x_2\le J^4$,
$$
 \left\|\sup_{x_1\le x\le x_2}|X_\xi(x)-X_\xi(x_2)|\right\|_2
 \le \int_{x_1}^{x_2}\|T(t)\|_2\,dt
 \ll (x_2-x_1)J^2\sqrt{\log J}.
$$
It follows that the suprema of the three raw twists on the whole prefix have $L^2$ norm $O(J^6\sqrt{\log J})$. Their variations on the terminal $\delta$ fraction in the $j$ variable have $L^2$ norm $O(\delta J^6\sqrt{\log J})$. These estimates avoid a union bound over neighboring samples. [Selberg mean-square theorem](prime-sieve.md)

## The rational critical-line case

Put $B=\sum_{p\ {\rm odd}}(J^4-p)_+^2\log^2p\sim(4/3)J^{12}\log J$. The four product-twist moments give both $\Pr(Z(J^4)>\sqrt B/8)\ge1/8-o(1)$ and $\Pr(Z(J^4)<-\sqrt B/8)\ge1/8-o(1)$. The two mixed prime masses are $P_o-Z\pm(S_q-S_d)$. Swapping $q,d$ preserves $Z$ and exchanges the orientations. Thus at the terminal sample each preassigned mixed prime mass exceeds $P_o+\sqrt B/8$ on a proportion at least $1/16-o(1)$, and is below $P_o-\sqrt B/8$ on another proportion of at least that size. [Sign minorant and orientation argument](product-moments.md)

Choose $\delta>0$ sufficiently small that the increment of the signed combination of the three twists anywhere on the terminal $\delta$ fraction exceeds $\sqrt B/32$ with probability at most $1/64$, by the preceding maximal estimate. Here and below the integer interval uses inward rounding. Under rational RH, $|x^2/2-P_o(x)|=O(x^{3/2})=o(\sqrt B)$ uniformly there. The complete corrections are nonnegative and $O(J^{16/3})$. On the high-mass set the complete deficit consequently vanishes at every sample of this same block. On the low-mass set the complete deficit is uniformly $\gg\sqrt B$, so the entire cube and higher-power correction survives clipping. By the simultaneous cube estimate the correction is at least $j^{16/3}/2$ for all these samples outside an additional set of probability $o(1)$. Both surviving proportions exceed $1/32$ for all sufficiently large $J$. [Uniform cube estimate](prime-sieve.md)

## The case of a zero right of one-half

Let $S(x)=P(x)-x^2/2$ include the prime $2$ and let $\Theta=\sup_\rho\Re\rho>1/2$. For every fixed zero $\rho_0$ with $\beta=\Re\rho_0>1/2$, and every sufficiently large $J$, there are points $x_\pm$ with
$$
 c_\beta J^4\le x_\pm\le J^4/2,\qquad \pm S(x_\pm)\gg_\beta J^{4+4\beta},
$$
where constants may depend on the selected zero. This is the signed part of mlyle’s fixed compact test. To see why both signs occur, write $F(y)=e^{-3y/2}S(e^y)$ and fix $1/2<\sigma<\beta$. Ingham’s density estimate gives $\sum_{\Re\rho>\sigma,\,\Im\rho>0}1/\Im\rho<\infty$. Mlyle’s compact probability $P$ annihilates every such conjugate pair. There are no real zeta zeros in $(0,1)$, as follows, for example, from the alternating eta series. Thus the absolute value of the signed integral against $P$ is $O(e^{(\sigma-1/2)y})$. The compact complex test isolating $\rho_0$ is pointwise dominated by a constant multiple of $P$, and its integral has modulus $\gg e^{(\beta-1/2)y}$. Consequently each of $\int P(v)[\pm F(y+v)]_+\,dv$ satisfies this same lower bound, using $2[t]_+=|t|+t$. Taking $y=4\log J$ minus a constant determined by the fixed support and by $\log 2$ gives the claimed pair of peaks. [Mlyle’s rational compact positive and signed tests](https://github.com/mlyle/riemann-masullo/blob/255d2b1531f3534cd35ea5dd9eb379fadd2c1104/research/5571/rational-fourth-power-deficit.md) · [Ingham, 1940](https://doi.org/10.1093/qmath/os-11.1.201)

The twice-decaying explicit formula gives a uniform modulus for the normalized deterministic prime error. For $v=\log x\ge1$,
$$
 -e^{-(1+\Theta)v}S(e^v)
 =\sum_\rho \frac{e^{(\rho-\Theta)v}}{\rho(\rho+1)}
    +O(e^{-(\Theta-1/2)v}).
$$
This holds also when $\Theta=1$, by the usual first-Riesz formula. For $|w|\le1/2$ and $v,v+w\ge0$, the absolute sum of the increments of its zero series is
$$
 \ll \sum_\rho\frac{\min(2,(1+|\Im\rho|)|w|)}{1+|\Im\rho|^2}
 \ll |w|\log^2(2/|w|).
$$
The first inequality follows by integrating each exponential's derivative between the two nonnegative arguments, and also by its trivial bound of two. For the second split at $|\Im\rho|=1/|w|$ and sum by parts using $N(T)\ll T\log(2T)$. [Absolute Riesz formula and classical zero count](vk-endpoint.md)

Take $\beta>\max(1/2,\Theta-\varepsilon/16)$, with $\beta=\Theta$ allowed if attained. At either peak the normalized amplitude is $\gg J^{-4(\Theta-\beta)}$. For logarithmic shifts $|w|\le J^{-\varepsilon/2}$, the series variation is $o(J^{-4(\Theta-\beta)})$, and so are both prime-power remainder values because $\beta>1/2$. Thus a full logarithmic neighborhood around each peak preserves its sign and a fixed fraction of its unnormalized amplitude. These neighborhoods supply two deterministic blocks of integers $j$ of lengths $\gg_\beta J^{1-\varepsilon/2}$ within $[c'_\beta J,J]$, hence at least $J^{1-\varepsilon}$ for every sufficiently large $J$. When $\beta=\Theta$, choose a sufficiently small fixed logarithmic shift instead, obtaining length $\gg_\beta J$. The two blocks are disjoint because they have opposite signs.

The maximal estimate on the whole prefix gives probability $o(1)$ that any of the three raw twists approaches a fixed positive multiple of $J^{4+4\beta}$, since $\beta>1/2$. Omitting $p=2$ costs $O(J^4)$, and the complete corrections are $O(J^{16/3})$. On the remaining pairs every nonidentity cell has exactly zero deficit throughout the high-mass block. Throughout the low-mass block every cell has complete deficit $\gg_\beta J^{4+4\beta}$ and its whole cube correction survives. The uniform cube estimate holds simultaneously throughout both blocks with probability tending to one. This proves the fixed-height assertions.

Finally apply the block assertion at $J=X$ with exponent loss $\varepsilon/2$. For every integer $K$ in the latter half of its zero block, $K\asymp_\varepsilon X$ and the last $\lfloor K^{1-\varepsilon}\rfloor$ samples lie in that block. The deterministic signed surplus there still holds if the auxiliary interval changes from $U_X$ to $U_K$. Apply the same whole-prefix maximal estimate at $K$ to obtain the stated proportion in each newly prescribed family. The latter half contains at least $X^{1-\varepsilon}$ consecutive eligible heights eventually. On rational RH the original terminal window already works at every sufficiently large height.

There is also a width bound for any fixed right-hand zero with $\beta>\Theta-1/4$. In the normalized zero series split at a fixed $1/2<\sigma<\beta$. Ingham’s summable reciprocal ordinates make the series with $\Re\rho>\sigma$ uniformly Lipschitz since $\sum_{\Re\rho>\sigma}|\rho-\Theta|/|\rho(\rho+1)|<\infty$. The remainder in this split is $O(J^{-4(\Theta-\sigma)})$ on $x\asymp J^4$. A sufficiently small constant times $J^{-4(\Theta-\beta)}$ is therefore an admissible logarithmic radius at either peak. Each deterministic block has length $\gg_{\rho_0}J^{1-4(\Theta-\beta)}$. At an attained supremum this recovers a fixed positive proportion.

## The longest zero run and attainment

Mlyle previously established the shrinking-support argument and an analogous run classification for two deterministic square-index compensators. Here the events concern the actual complete Jacobi cells, with a proportion over distinct primes at the fourth-power scale. [Mlyle’s square-index run classification](https://github.com/mlyle/riemann-masullo/blob/69f6639d0e53c2a04aa3b5f8487a1be237274b97/research/5571/square-prefix-fixed-window-count/README.md)

Suppose $\Theta$ is unattained. Then $\Theta>1/2$. For fixed $\sigma_0$ with $1/2<\sigma_0<\Theta$, Ingham’s density theorem gives a finite sum of reciprocal positive ordinates over $\Re\rho>\sigma_0$. As $\sigma\uparrow\Theta$ its tail sum over $\Re\rho>\sigma$ tends to zero by dominated convergence. The elementary binary annihilating factors in mlyle’s test have widths $\pi/\gamma$. Hence the compact test giving the two signs can be supported in a logarithmic interval of **any** prescribed positive length.

More explicitly, select $\sigma>\max(\sigma_0,\Theta-1/8)$ so that the sum of the binary widths is sufficiently small. Convolve their probability law with a smooth probability of arbitrarily small support, producing a bounded smooth $K$ in $[0,\ell]$. Choose $\rho_0$ with $\beta>\sigma$. The transform of $K$ is entire and has a zero of finite positive order $m$ at $z_0=\rho_0-1/2$. It is a nonzero entire function since its value at zero is one. Removing the zero by dividing by $(z-z_0)^m$ is realized by iterating the compact primitive, giving a bounded density $L$ supported in $[0,\ell]$ and nonzero in transform at $z_0$. The probability $P=K*{\rm Unif}[-\ell,\ell]$ is constant on $[0,\ell]$, dominates a positive multiple of $|L|$, and remains an annihilator. Its entire support has length $3\ell$, which can be made as small as required. Translating the fixed tests in logarithmic scale puts both signed peaks inside any interval of that length at every sufficiently large scale. One can use a strictly interior smaller interval so that passing to integer fourth powers stays inside the desired interval. [Mlyle’s compact kernel and primitive](https://github.com/mlyle/riemann-masullo/blob/69f6639d0e53c2a04aa3b5f8487a1be237274b97/research/5571/square-prefix-fixed-window-count/README.md)

Fix $0<t<1$. Choose a finite mesh of disjoint narrow subintervals in $[tJ/4,J]$ so that every interval of $tJ$ consecutive indices in $[1,J]$ contains at least one mesh interval. One construction uses mesh centers spaced by $tJ/4$ and subintervals of radius $tJ/32$ around centers at least that distance from either end. For large $J$ each has a logarithmic fourth-power subinterval of width bounded below in terms of $t$. Choose the tests shorter than this width and use the same fixed target zero in all cells. The persistence bound just proved supplies an integer sample of large deterministic deficit in each mesh interval, since $\Theta-\beta<1/8$. The whole-prefix maximal estimate simultaneously makes all three complete deficits strictly positive at all those samples on a common set of pairs of probability $1-o(1)$. Therefore $\Pr(L_s(J)\ge tJ)\to0$; the same proof applies to the best-cell selector. The long blocks proved above yield $L_s(J)\ge J^{1-\varepsilon}$ with probability tending to one in the unattained case. Conversely an attained right-hand zero gives a zero block of proportional size with probability tending to one, and rational RH gives one on a proportion at least $1/32$. Under rational RH every nontrivial zero attains $\Theta=1/2$. This proves the equivalence and the logarithmic limit.

## A zero-increment criterion for rational RH

There is already an exact criterion for **one fixed mixed cell and two distinct auxiliary primes**. Fix $0<\varepsilon<1$ and prescribe any integers $1\le n_J\le J^{1-\varepsilon}$. Let $p_J$ be the fraction of pairs for which all true complete deficits vanish on the final $n_J$ samples. Thus $n_J=1$ uses the terminal sample alone. Then
$$
 \begin{array}{ll}
 \mathrm{RH}_{\mathbf Q}:&1/12\le\liminf p_J\le\limsup p_J\le11/12,\\
 \neg\mathrm{RH}_{\mathbf Q}:&\liminf p_J=0,\qquad\limsup p_J=1.
 \end{array}
$$
For every $\eta>0$, requiring $p_J\ge J^{-\eta}$ at all sufficiently large $J$ is therefore, when required for all $\eta$, equivalent to rational RH. The equivalent condition with $1-p_J$ is valid as well.

On RH take $b_J=(\log J)^{-1/4}$ in the [quartic sign minorant](product-moments.md). Each sign of $Z(J^4)$ with magnitude $>b_J\sqrt B$ has probability at least $1/6-o(1)$. Swapping the two primes gives the high or low fixed orientation on a probability at least $1/12-o(1)$. Across the last $n_J$ samples the twisted combination has $L^2$ maximal variation $O(J^{-\varepsilon}J^6\sqrt{\log J})=o(b_J\sqrt B)$. The uniform RH drift $O(J^6)$ and every complete correction are also $o(b_J\sqrt B)$. Hence both the zero-deficit event and its complement have probability at least $1/12-o(1)$.

If RH fails, fix a zero with real part $\beta>1/2$ sufficiently near $\Theta$ that $4(\Theta-\beta)<\varepsilon/2$. The two deterministic blocks above have lengths $\gg J^{1-4(\Theta-\beta)}$. Re-sample at a cutoff $K$ in the latter half of either block, as in the terminal conclusion. For all $n_K$ final samples the signed prime surplus has one sign and magnitude $\gg_\beta K^{4+4\beta}$. On $1-o(1)$ of the newly drawn pairs all these complete deficits are zero on the high-mass block and positive on the low-mass block.

One obtains a quantitative rarity bound at those cutoffs. For every $\nu>0$, the single-prime sixth moment of the unweighted twist $T(t)$ for $t\le K^4$ is $\|T(t)\|_6\ll_\nu K^\nu\sqrt{t\log(2t)}$. Indeed cube the character polynomial, group equal squarefree kernels, and apply Heath-Brown with length $t^3\le Q$. The sum of the squares of the grouped coefficients is at most $15(\sum_{p\le t}\log^2p)^3$ by the pairings of six prime occurrences. The same proof works with bounded signs inserted in the coefficients, and conditioning on the second prime handles the product twist. Integrating the maximal estimate by Minkowski now gives $O_\nu(K^{6+\nu})$ for the $L^6$ norm of the supremum of the full first-Riesz twists. Markov bounds $p_K$ on the low-mass subsequence and $1-p_K$ on the high-mass subsequence by $O_{\rho,\nu}(K^{-24(\beta-1/2)+\nu})$ for every $\nu>0$. This proves the subpower formulation and, for every $\kappa\ge0$, the implication
$$
 p_J\ge J^{-\kappa-o(1)}\text{ at all large }J
 \quad\Longrightarrow\quad
 \Theta\le\tfrac12+\kappa/24 .
$$
The same implication uses the lower bound for $1-p_J$. Since $\beta$ may be chosen arbitrarily close to $\Theta$, no attainment assumption enters. [Single-prime sixth-moment argument](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7154774282) · [Formal transfer for the original cells](https://github.com/mccorvie/riemann-masullo/pull/7648)

## Parity and fixed fractional windows

For fixed $h\ge2$, let $H_{\mathbf q}(L)$ be the complete twice-normalized negative parity deficit up to the index $L$, for one fixed tuple of distinct auxiliary primes. Then
$$
 \mathrm{RH}_{\mathbf Q}
 \quad\Longleftrightarrow\quad
 \forall\,0<\lambda<1\ \exists\, h\ge2:\quad
 \limsup_{J\to\infty}\Pr_{\mathbf q\in U_J^{\ne h}}
 \{H_{\mathbf q}(J)=H_{\mathbf q}(\lfloor\lambda J\rfloor)\}>0.
$$
Here $U_J^{\ne h}$ means the ordered $h$-tuples of pairwise distinct members of $U_J$. Both partial sums use exactly that same tuple and the stated probability is over the full prescribed family.

On rational RH the unconditional product process tends, first in $J$ and then in $h$, to $Y(u)=2\int_0^{u^4}W(s)\,ds$. A uniform neighborhood of $W(s)=-s$ has positive probability. On a sufficiently small neighborhood $Y(u)<-\lambda^8/2$ for every $u\in[\lambda,1]$. Such a strict upper bound is an open event for the continuous path. Hence all sufficiently large fixed $h$ have a positive liminf probability of a negative raw twist of size $\gg_\lambda J^6\sqrt{\log J}$ at every sample on the terminal interval. The RH drift is $O(J^6)$ and the odd-power correction is nonnegative. The true complete deficit is therefore exactly zero at every such sample. [Functional theorem with the two orders of limits](parity-path.md)

If rational RH fails, select a fixed zero with $\beta>\max(1/2,\Theta-1/8)$. A deterministic block with prime deficit $\gg_\beta J^{4+4\beta}$ occurs between $c_\beta J$ and $J$ at every large $J$ by the compact test. For the $h$-prime product twist, condition on $h-1$ of its distinct primes and apply the prime-supported quadratic estimate to the last one; its nonnegative mean-square bound increases by at most $|U_J|/(|U_J|-h+1)\le2$ when $h\le|U_J|/2$. The whole-prefix supremum has $L^2$ norm $O(J^6\sqrt{\log J})$ uniformly throughout this range. The twice-weighted complete prime-power correction is $O(J^{16/3})$. With $\lambda=c_\beta/2$, the probability of a zero increment on the entire terminal interval thus tends to zero uniformly over these $h$. In particular the right side of the criterion fails. The proof gives a criterion stated only in terms of exact zero increments; the step of establishing the requisite probabilities unconditionally for every $\lambda$ remains open.

For the terminal sample alone let $p_{h,J}$ be its zero-deficit probability in the $h$-prime negative parity union. The same reasoning gives
$$
 p_{h,J}\ge J^{-\kappa-o(1)}\text{ at all large }J
 \quad\Longrightarrow\quad
 \Theta\le\tfrac12+\kappa/(24h)
$$
for each fixed $h\ge2$. The $6h$-th moment for the single sample costs $J^{6+\nu}$ after taking its root. It follows by raising the prime polynomial to power $3h$, grouping squarefree kernels of size at most $(J^4)^{3h}=Q^h$ and sieving against the squarefree products of the $h$ distinct auxiliary primes. A product has at most $h!$ ordered representations. At a low-mass target peak Markov gives an exceptional fraction $\ll_{\rho,\nu,h}J^{-24h(\beta-1/2)+\nu}$. Conversely on RH the two-step Gaussian path limit and the absence of an atom at zero for $Y(1)$ give $\lim_{h\to\infty}\limsup_{J\to\infty}|p_{h,J}-1/2|=0$. Thus even a fixed polynomial lower fraction for the terminal sample at every large height, available for arbitrarily large fixed $h$, would suffice for rational RH. [Distinct-prime $6h$-th moment and parity interpretation](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7154774282) · [Formal parity transfer](https://github.com/mccorvie/riemann-masullo/pull/7655)

## An exact finite check on consecutive samples

At $J=12$ the [integer verifier](verify_consecutive_windows.py) uses the same reproducible set of 96 genuine auxiliary primes as the moment verifier. For either preassigned mixed orientation, at least **2,416 of its 9,120 ordered distinct pairs** have exactly zero complete deficit at **all four** samples $j=9,10,11,12$. At least **2,032** instead have positive complete deficit and gain at least $j^{16/3}/2$ simultaneously at all four samples. All comparisons in these two counts use outward integer bounds for the logarithms and enumerate every contributing odd prime power. They certify this finite sample only.
