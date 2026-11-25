# One-sided bounds for the actual rational principal Jacobi-class deficits

Fix $J$, $Q=J^{12}$ and the primes $U=(Q,2Q]\cap\mathbb P$, and write $M=|U|\asymp Q/\log Q$. Unless otherwise specified, choose an ordered pair of **distinct** members uniformly. At $x=j^4$ put
$$
 b_p(x)=(x-p)_+\log p,\qquad P(x)=\sum_p b_p(x),\qquad
 c(x)=x^2/2,\qquad A_j=[c(x)-P(x)]_+,\qquad D(J)=\sum_{j\le J}A_j .
$$
All sums over $j$ start at 1. Write $\eta_q(p)=(q/p)$ in the project's Jacobi convention. In particular $\eta_q(2)=1$ for odd $q$.

For signs $s,t\in\{-1,1\}$, $C'_{s,t}(x)$ is four times the prime Riesz sum on $\eta_q(p)=s,\eta_d(p)=t$, and $C_{s,t}(x)$ is the corresponding complete von Mangoldt sum. The full and prime cumulative deficits $H_{s,t},H'_{s,t}$ sum the positive parts $[c-C_{s,t}]_+,[c-C'_{s,t}]_+$, respectively. Let $H_*$ allow the best of the three nonidentity complete cells at each sample. These are the actual positive rational principal weights and principal pole center. [Mlyle’s complete-class definitions and comparison](https://github.com/mccorvie/riemann-masullo/pull/7627)

The [four-moment calculation](product-moments.md) strengthens the clipped cube saving to an unconditional lower proportion of $1/12$ for either fixed mixed cell and proves a simultaneous lower bound for the complete deficit itself. The [Selberg mean-square estimate](prime-sieve.md) gives the corresponding upper bounds for individual cells. The [full parity law](parity-path.md) determines the coupled distribution of the deficit and the saving under rational RH, and evaluates the correction to the mean unconditionally. The [first Riesz zero-free-region estimate](vk-endpoint.md) gives a full-prefix upper bound with exponential constant $0.644419636701\ldots$ on the $J$ variable.

## A sharp gain from the positive cubes, including after clipping

For the fixed opposite-sign cell $(-,+)$ or $(+,-)$, unconditionally,
$$
 \mathbb E(H'_{s,t}(J)-H_{s,t}(J))=J^{19/3+o(1)}.
$$
For each $\varepsilon>0$ and all sufficiently large $J$, a fraction at least $J^{-\varepsilon}$ of distinct pairs satisfies
$$
 H_{s,t}(J)\le H'_{s,t}(J)-J^{19/3-\varepsilon}.
$$
If the supremum $\Theta$ of the real parts of the nontrivial zeta zeros exceeds $1/2$, this fraction tends to one for every fixed $\varepsilon>0$. The two-sided exponent here concerns the actual *amount saved* on passing from prime to complete deficits. Its scale is smaller than $J^7$. An upper bound of order $J^{7+o(1)}$ for complete deficits on enough pairs remains open.

**Raw cubes.** For every nonidentity cell, the squares are absent and all remaining higher-power terms are nonnegative. Its first surviving term is four times the selected part of
$$
 W_3(x)=\sum_{p^3\le x}(x-p^3)\log p
       =\int_0^{x^{1/3}}3t^2\vartheta(t)\,dt
       \sim \tfrac34 x^{4/3}.
$$
The asymptotic follows from the ordinary prime number theorem. For odd powers $k\ge5$, Chebyshev's bound gives a total $O(x^{6/5}\log(2x))$, uniformly even before selecting primes. The sign of a cube is the sign of the underlying prime. This calculation uses the unweighted first Riesz kernel $x-p^3$. Mlyle’s earlier positive cube theorem addresses a different phase weight and square-root kernel. [Mlyle’s cube bound](https://github.com/mccorvie/riemann-masullo/pull/7622)

We record the elementary variance needed below. For arbitrary real weights $h_p$ on $p\le Y$, $Y^3\le Q$, complete-period orthogonality on an interval of length $Q$ gives
$$
 \mathbb E_{q\in U}\left|\sum_{p\le Y} h_p\eta_q(p)\right|^2
 \ll \log(2Q)\sum_{p\le Y}|h_p|^2.
 \tag{1}
$$
Indeed each off-diagonal pair of odd-prime symbols has mean zero on a full period and remainder at most $pr\le Y^2$. The diagonal costs $Q\sum|h_p|^2$, and the remaining terms cost at most $Y^2(\sum|h_p|)^2\le Y^3\sum|h_p|^2$. Separate $p=2$, restrict the nonnegative sum to $U$, and divide by $M$. Holding one auxiliary prime fixed proves the same estimate for the product twist, since the inserted multiplier has magnitude at most one. Restriction to distinct pairs changes nonnegative bounds by at most $M/(M-1)$. This is mlyle's elementary second moment. [Complete-period estimate](https://github.com/mlyle/riemann-masullo/blob/6129a148ba20a0aad50c4b47717276f5441aad73/RiemannMasullo/Ch13_ZerosHecke/QuadraticPrimeTwists.lean#L146)

A normalized cell differs from the unrestricted sum by a signed sum of its two single twists and their product. Apply (1) to $h_p=(x-p^3)_+\log p$ with $Y=x^{1/3}$. Since $\sum h_p^2\ll x^{7/3}\log(2x)$, the selected fourfold cube sum has $L^2$ distance $O(x^{7/6}\sqrt{\log(2x)\log(2Q)})$ from $W_3(x)$. Consequently, at every sufficiently large $j\le J$,
$$
 \Pr(C_{s,t}(j^4)-C'_{s,t}(j^4)<\tfrac12 j^{16/3})
       \ll j^{-4/3}\log^2(2J).
 \tag{2}
$$
Summing the $L^2$ bounds and the higher-power bound also yields a normalization for the raw correction. For each of the three cells, in probability and in $L^1$,
$$
  J^{-19/3}\sum_{j\le J}(C_{s,t}(j^4)-C'_{s,t}(j^4))\longrightarrow \tfrac9{76}.
 \tag{3}
$$
The constant is $(3/4)/(1+16/3)$. The same convergence holds for selections varying by pair and sample, since the maximum of three absolute errors is bounded by their sum.

**Which samples can use the cube mass.** Put $e=4\Theta+4\ge6$. Mlyle's rational fourth-power calculation gives $D(J)=J^{e+1+o(1)}$, including the critical endpoint and an unattained supremum. The absolutely convergent once-integrated explicit formula and the cost of replacing ideal powers by primes give $A_j\ll j^e$. For the latter, the nontrivial-zero part is bounded by $x^{1+\Theta}\sum_\rho |\rho(\rho+1)|^{-1}$, and the discarded powers cost $O(x^{3/2})$. These unconditional facts imply that, for each arbitrarily small fixed $\tau>0$ with $e\tau>0$, there are $\gg_\tau J^{1-\tau}$ indices $j\in[J^{1-\tau},J]$ with $A_j\ge J^{e-2\tau}$ for all large $J$. In fact $D(J)\ge J^{e+1-\tau}$, while the earlier indices contribute $O(J^{(1-\tau)(e+1)})$ and the small values contribute $O(J^{e+1-2\tau})$. The remaining terms are each $O(J^e)$. [Mlyle’s rational full exponent and endpoint](https://github.com/mlyle/riemann-masullo/blob/255d2b1531f3534cd35ea5dd9eb379fadd2c1104/research/5571/rational-fourth-power-deficit.md) · [Integrated formula and prime transfer](https://github.com/willzh0/riemann-masullo/blob/b6c048c2884165921b5066f9a82fc919ebadfa5e/research/5571/fourth-power-deficit-boundary/README.md)

Write $A'_j=[c(j^4)-C'_{s,t}(j^4)]_+$. At each prime, if $M_+$ and $M_-$ are the auxiliary sign counts, the probability of a prescribed opposite-sign cell on distinct pairs is $M_+M_-/[M(M-1)]\le M/[4(M-1)]$. The weights are nonnegative. It follows that
$$
 \mathbb E A'_j\ge A_j-P(j^4)/(M-1)=A_j-O(J^8/M).
 \tag{4}
$$
This inequality fixes the direction relevant to clipping. From (1), now with $Y=x$ and $\sum b_p(x)^2\ll x^3\log(2x)$, the positive-part Lipschitz bound gives
$$
 \|A'_j-A_j\|_2\ll j^6\log(2J).
 \tag{5}
$$
For the indices just found, Cauchy–Schwarz on $A'_j>A_j/3$ in (4) and (5) gives probability $\gg_\tau J^{-4\tau}/\log^2(2J)$. For small enough fixed $\tau$ this exceeds the failure probability in (2) by a power. On their intersection $A'_j>A_j/3\ge J^{e-2\tau}/3\gg j^{16/3}$. Exactly
$$
 A'_j-[c(j^4)-C_{s,t}(j^4)]_+
     =\min\{A'_j,C_{s,t}(j^4)-C'_{s,t}(j^4)\}.
$$
It is at least $j^{16/3}/2$ there. Sum over the selected indices and take $\tau$ sufficiently small for any desired exponent loss. This proves the lower expectation. Mlyle's uniform bound $O(J^{19/3})$ gives the upper expectation and converts the expectation lower bound to the stated fraction (use half the requested exponent loss first). If $e>6$, choose $\tau$ with $e-2\tau>6$. On every selected index Chebyshev's inequality in (5) ensures $A'_j>A_j/3$ with probability $1-O_\tau(J^{-\eta})$ for some $\eta>0$. Markov's inequality on the number of failures across these deterministic indices gives the stated fraction tending to one, without assuming independence between samples.

## A one-sided bound on the optimized complete deficit

Let $S_q(x)=\sum_p b_p(x)\eta_q(p)$ and $B(q)=\sum_{j\le J}|S_q(j^4)|$. The two cells whose first sign is negative together contain all primes with $\eta_q(p)=-1$. One of their fourfold masses is therefore at least $2\sum_{\eta_q(p)=-1} b_p=P(x)-S_q(x)$. Their complete masses are at least their prime masses. The same observation for the second auxiliary prime yields the exact pointwise bound
$$
 H_*(q,d;J)\le D(J)+\min\{B(q),B(d)\}.
$$
On independent ordered pairs this yields the upper tail
$$
 \Pr(H_*>D(J)+t)\le
 \min\!\left(1,\left(C_\varepsilon J^{7+\varepsilon}/t\right)^{12}\right).
$$
The factorization uses the two separate auxiliary primes and the established $L^6$ upper for a single twist. Conditioning to distinct pairs costs at most $M/(M-1)$ in probability. [Single-twist sixth moment](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7154774282)

The same distinct-pair upper tail follows from the product parity bound since the larger mixed complete class dominates the mean of the two. The marginal argument also covers the diagonal and locates every exception in a square of one-variable exceptions.

This gives an unconditional upper bound on the actual $H_*$ containing no unknown prime mean. Put $V(J)=(\log J)^{3/5}(\log\log J)^{-1/5}$. For each $0<c<0.1853\cdot4^{3/5}$, there is a subset $E_J\subseteq U$ of size $J^{o(1)}$ outside whose square
$$
       H_*(q,d;J)\ll_c J^9 e^{-cV(J)} .
$$
Indeed Johnston and Yang's explicit bound on $|\vartheta(y)-y|$ and $P(x)=\int_0^x\vartheta(y)\,dy$ yield $D(J)\ll_{c'}J^9e^{-c'V(J)}$ for each $c'$ in this open range. To preserve any strict constant, discard $y\le x^{1-\xi}$ and then $j\le J^{1-\xi}$ at power-saving cost, and let the fixed $\xi>0$ be sufficiently small. The polynomial logarithmic factors are absorbed by an arbitrarily small loss in $c'$. For $t=J^9 e^{-cV(J)}$, the single-variable sixth moment gives $\#\{q:B(q)>t\}\ll_\varepsilon M J^{42+6\varepsilon}/t^6=J^{o(1)}$ in the sense of a bound $O_\eta(J^\eta)$ for every $\eta>0$. Take this set for $E_J$. This saving below $J^9$ coexists with the open critical exponent $7$. [Johnston and Yang, Theorem 1.4](https://doi.org/10.1016/j.jmaa.2023.127460)

## Minimum deficits on growing initial windows at the coupled auxiliary scale

Let $y=a\log J\log\log J$ with fixed $0<a<12/\log2$. For every sufficiently large $J$, at least a $J^{-a\log2+o(1)}$ fraction of distinct pairs from the specified $U$ have
$$
 H_{-,-}(q,d;L)=\tfrac12 \qquad (1\le L\le y^{1/4}),
$$
where the same $q,d$ and the same cell are used throughout. Here $L$ is the index cutoff inside the ambient auxiliary family at $J$. Taking $y=o(\log J\log\log J)$ tending to infinity gives a family of relative size $J^{-o(1)}$. The term at $j=1$ forces $1/2$ for every pair. Mlyle previously constructed a prescribed fixed-cutoff class by CRT and then took the auxiliary primes large, and checked that a particular finite choice eventually develops a deficit. The count here works inside the prescribed dyadic range at every sufficiently large $J$. [Fixed-cutoff CRT theorem](https://github.com/mccorvie/riemann-masullo/pull/7642) · [Finite example from mlyle](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7154752844)

Choose a sufficiently large fixed $j_0$. A positive proportion of all $q$ have $\eta_q(p)=-1$ at every odd $p\le P_0=j_0^4$, by CRT and the fixed-progression PNT. Conditional on this event, for distinct odd primes $P_0<p,r\le y$,
$$
 \mathbb E(\eta_q(p)\eta_q(r))=O_{A,P_0}((\log Q)^{-A})
$$
for each fixed $A$. The dyadic progression prime counts are uniform modulo $M_0pr\le(\log Q)^4$ for all large $Q$, where $M_0$ is the fixed product of the small odd primes. The character averages cancel over the reduced classes by CRT. Taking a stronger logarithmic error before summing over classes and normalizing gives the displayed bound. [Thorner and Zaman, Siegel–Walfisz consequence of Theorem 1.1](https://arxiv.org/pdf/2108.10878#page=3)

At $x=j^4\le y$ the conditional second moment of $T_q(x)=\sum_{P_0<p\le x}b_p(x)\eta_q(p)$ is at most
$$
 C x^3\log(2x)+O_{A,P_0}(x^4(\log Q)^{-A}),
$$
with absolute $C$ for its diagonal term. A union bound on $|T_q(j^4)|>j^8/10$ for $j>j_0$ costs at most $C'\sum_{j>j_0}\log(2j)/j^4+o(1)$. Choose $j_0$ first to make this smaller than $1/2$. The odd prime Riesz mass is at least $2x^2/5$ for all sufficiently large $x$ by the ordinary PNT. On the surviving fixed positive proportion of auxiliaries, the negative prime mass is at least $(2x^2/5-x^2/10)/2>x^2/8$, simultaneously in these samples. The forced small signs only increase it. For $2\le j\le j_0$ every odd prime through $j^4$ has a negative sign; the explicit lower bound in the next paragraph covers these cutoffs.

There are at most $2^{\pi(y)}$ sign vectors on the odd primes through $y$. Cauchy–Schwarz gives at least $c_0^2 M^2 2^{-\pi(y)}-M$ ordered *distinct* pairs of surviving auxiliaries with the same vector, for a fixed $c_0>0$. Their $(-,-)$ prime sum is four times the one-prime negative mass, and taking the complete sum increases it. Since $\pi(y)=(a+o(1))\log J$ and $a\log2<12$, the loss of the diagonal is negligible.

**The negative parity union.** There is also an absolute $c_0'>0$ such that a $J^{-o(1)}$ fraction of distinct pairs attain this same minimum for the *twice*-normalized negative parity complete cell, simultaneously for $j^4\le c_0'\log Q$. For $z=c_0'\log Q$ let $L$ be the product of the odd primes through $z$, with $k$ prime factors. It suffices to produce opposite signs on all these primes with at most one exception $p_*>16$. For two complementary vectors, the product character then has negative sign at each required prime.

For such a pair let $\vartheta_g$ weight the retained odd primes. With at most one deletion, for $64\le t\le z$,
$$
 \vartheta_g(t)\ge t-t/\log t-\log(2t)\ge 5t/8
$$
by Rosser–Schoenfeld's inequality (3.16). Hence $2\int_{64}^x\vartheta_g(t)\,dt>x^2/2$ for $256\le x\le z$. For $x=16$ the condition holds using all odd primes; at $x=81$ it still holds after deleting any one. Both finite checks may be made with integers by replacing $e$ with its upper bound $11/4$ in $\prod p^{4(x-p)}>e^{x^2}$. At $j=1$ every raw sum vanishes and the deficit is $1/2$. This also proves the small-cutoff assertion above. [Rosser and Schoenfeld, equation (3.16)](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf#page=8)

To count the required vectors, apply Thorner–Zaman, Theorem 1.1 at interval endpoint $2Q$ and length $Q$. If an exceptional character modulo $L$ is present, call a sign vector favorable when its value under this real character is $-1$. Otherwise all vectors are favorable. On favorable reduced classes the main-term factor $\lambda$ is at least 1. Since $\log L\sim c_0'\log Q$, take the absolute constant $c_0'$ sufficiently small. Their main-term size condition then holds and the relative error is at most $1/2$, uniformly. Each favorable sign vector comprises $\varphi(L)2^{-k}$ reduced classes and contains $\gg M2^{-k}$ primes of $U$. The exceptional character is a product of the Legendre symbols at some nonempty subset $S$ of the primes dividing this odd squarefree $L$. When $|S|$ is even, complement all signs. When it is odd, complement all signs except one at $p_*\in S$; both vectors remain favorable. For all sufficiently large $Q$, this $p_*$ may be chosen greater than 16: only finitely many primitive characters have squarefree conductor supported at odd primes at most 16, and each has a fixed zero-free neighborhood of 1. The exceptional threshold tends to 1 as $L$ grows. There are at least $2^{k-1}$ favorable starting vectors. Their distinct-vector pairs give $\gg M^2 2^{-k}$ ordered pairs in total. Since $k=O(\log Q/\log\log Q)$, this gives the claimed subpower fraction. The same construction works for every fixed $\lambda_0<2+\sqrt2$ through $j^4\le\lambda_0z$ when $\lambda_0>1$, by using the already-retained primes up to $z$: their twice-weighted mass at $x\in[z,\lambda_0z]$ is $2xz-z^2+o(z^2)$ uniformly by the PNT, even after the possible deletion. [Thorner and Zaman, Theorem 1.1](https://arxiv.org/pdf/2108.10878#page=1)

These initial windows grow with $J$. Extending their minimum-deficit conclusion to every $j\le J$ remains open.

## Many whole rows attain the minimum on a growing initial interval

There are absolute $c_0,c_1,C>0$ such that every sufficiently large $J$ has a set of at least $c_1|U_J|\exp[-C\log J/\log\log J]$ primes $q$ satisfying
$$
 H_*(q,d;\lfloor(c_0\log J)^{1/4}\rfloor)=1/2
 \quad\text{for every }d\in U_J,\ d\ne q.
$$
The same set can be taken outside $E_J$, so each of its rows obeys both this exact initial claim and the preceding full-prefix upper bound.

**Arithmetic progressions.** Fix a sufficiently small absolute $\kappa>0$. Put $z=\kappa\log Q$, $m=\prod_{3\le p\le z}p$ over odd primes, and let $k$ be the number of those primes. The prime number theorem gives $\log m\sim z$ and $k=O(\log Q/\log\log Q)$. Pick one sign for each $(q/p)$. Each complete sign pattern represents exactly $\varphi(m)/2^k$ reduced residue classes modulo $m$.

Normally prescribe every sign to be negative. If Thorner–Zaman’s possible exceptional real character $\chi_1\bmod m$ exists, it is a product of distinct Legendre characters since $m$ is odd and squarefree. If the all-negative pattern gives $\chi_1=+1$, change the prescribed sign at the largest prime $p_*$ in this product to positive. Then $\chi_1=-1$ on the entire chosen pattern. Along any sequence with an exceptional character, its largest conductor prime tends to infinity. Otherwise the primitive conductors would belong to a finite set, whose fixed real $L$-functions have a zero-free interval immediately below one. This contradicts the defining exceptional bound $\beta_1\ge1-1/[13\log(3m)]$. Thus for large $J$ any discarded prime $p_*$ exceeds $10^4$.

Apply Thorner–Zaman Theorem 1.1 with $x=2Q,h=Q$, the modulus $m$, and $\varepsilon=1/100$. In every chosen class their $\lambda\ge1$, by the sign choice and the integral in their definition. Their $\theta\le32/37$. Since $\log m\le2\kappa\log Q$, choose $2\kappa<1-32/37-1/100$. Then $\lambda h/\varphi(m)\ge x^{\theta+\varepsilon}$ eventually. Their relative error is at most $C_\varepsilon e^{-c_\varepsilon/(3\kappa)}$ for large $Q$, because the denominator in the exponential is $\log m+O(1)+o(\log Q)$. Decrease the fixed $\kappa$ to make the bound at most $1/2$. Each chosen class therefore contributes at least $Q/(2\varphi(m))$ in prime log weight on $(Q,2Q]$. Summing the classes and dividing by $\log(2Q)$ gives at least $Q/(2^{k+1}\log(2Q))$ admissible first primes $q$. This is $\gg |U_J|2^{-k}$. [Thorner–Zaman, Theorem 1.1 and definition of the exceptional character](https://arxiv.org/pdf/2108.10878#page=1)

**Prime mass in each row.** For every such $q$, the symbol is negative on all odd $p\le z$ except possibly $p_*$. For $41\le t\le z$, the sum of $\log p$ over the guaranteed negative primes below $t$ exceeds $2t/3$ for sufficiently large $J$. In fact $\vartheta(t)>t(1-1/\log t)$, and removing $p=2$ leaves more than $0.70t$ since $\log41>3.7$, $\log2<0.7$. Removing $p_*$, when necessary and $t\ge p_*$, costs at most $t(\log p_*)/p_*<0.01t$. Therefore for $82\le x\le z$,
$$
 4\sum_{p\le x,\ (q/p)=-1}(x-p)\log p
 \ \ge\ \tfrac43(x^2-41^2)\ \ge\ x^2 .
$$
The finite verification below establishes this inequality for $x=16,81$ even on a subset of the odd primes, and a possible exceptional prime exceeds both. This covers all fourth powers $2^4\le j^4\le z$. The marginal bound now gives $C_*(j^4)\ge j^8/2$ for every such $j$ and every allowed $d$. The entire initial deficit is the first sample’s $1/2$. Finally $z=12\kappa\log J$. Removing the $J^{o(1)}$ elements of $E_J$ preserves the lower bound on the row count with an adjusted constant. [Rosser–Schoenfeld, Theorem 4, (3.16)](https://doi.org/10.1215/ijm/1255631807)

## Exact finite rows for the whole coupled prefix

For $J=12,16,24,32,40,48,60$, the attached integer-only certificate exhibits two distinct auxiliary primes in the prescribed interval $(J^{12},2J^{12}]$. For either displayed first prime $q$ and **every** permitted second prime $d\ne q$, the optimally selected complete cumulative deficit through the full index $J$ is exactly $1/2$. For example the two first primes at $J=60$ are 2176782336000004572923 and 2176782336000141269483.

For each $2\le j\le J$ it checks $4\sum_{\eta_q(p)=-1}(j^4-p)\log p>j^8$. Consequently one of the two negative-first-sign cells reaches the pole center; the larger complete mass does too. The choice between those two cells may change with the second prime and the sample. The program proves primality by complete Lucas certificates, verifies the auxiliary interval endpoints, enumerates all odd primes through $J^4$, and uses integer lower bounds for logarithms. The least verified relative excess at $J=60$ exceeds 562,400 parts per billion for the first witness and 962,998 for the second. [Verification script](verify_jacobi_marginal.py)


At $J=60$ this proves the exact minimum for more than $1.6\times10^{20}$ ordered distinct pairs. Here $Q=60^{12}>2.1\times10^{21}$ and $48<\log Q<\log(2Q)<50$. Equations (3.14)–(3.15) of Rosser–Schoenfeld imply $\vartheta(2Q)-\vartheta(Q)>Q(1-1/\log(2Q)-1/(2\log Q))>0.96Q$. Thus $|U_J|>0.96Q/50$, and $4|U_J|-6$ exceeds the stated count. [Rosser–Schoenfeld, Theorem 4](https://doi.org/10.1215/ijm/1255631807)

Take the two $J=12$ primes together. At $j=2$ both mixed cells have zero complete mass because both auxiliary signs are negative at $3,5,7,11,13$, and $2$ has both signs positive. At $j=11$, the deficit of the remaining $(-,-)$ cell exceeds $1,232,275$, including every contributing odd prime power. The verifier upper-bounds each $\log p$ by $(694/1000)\operatorname{bitlength}(p^{256})/256$. Thus every fixed class incurs cumulative deficit at least $128+1/2$, whereas choosing the better nonidentity class at each sample gives exactly $1/2$ for this pair. This is a strict finite gain from optimization in the rational principal case. [Earlier fixed-pair test for the nonprincipal character modulo four](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7154752844)
