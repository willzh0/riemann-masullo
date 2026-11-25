# Positive odd cubes and actual complete quadratic-class deficits

For the rational principal character, fix either opposite-sign class $s=(+,-)$ or $s=(-,+)$. On the uniform space of ordered **distinct** primes $q,d\in U=(J^{12},2J^{12}]$, let $H_s$ and $H'_s$ denote its cumulative complete and prime-only deficits at $j^4$ with center $j^8/2$. Put $G_s=H'_s-H_s$. These are the fourfold normalized classes of [mlyle’s PR #7627](https://github.com/mccorvie/riemann-masullo/pull/7627).

For every $\varepsilon>0$,
$$
 \liminf_{J\to\infty}\Pr(G_s\ge J^{19/3-\varepsilon})\ge \tfrac1{12}.
$$
There is an absolute $c>0$ such that
$$
 \liminf_{J\to\infty}
 \Pr\{H_s\ge cJ^7\sqrt{\log J},\ G_s\ge J^{19/3-\varepsilon}\}
 \ \ge\ \tfrac1{31}.
$$
Both assertions concern actual deficits at a fixed orientation. The unconditional argument combines the product-twist calculation below with [mlyle’s rational every-prefix exponent](https://github.com/mlyle/riemann-masullo/blob/255d2b1531f3534cd35ea5dd9eb379fadd2c1104/research/5571/rational-fourth-power-deficit.md). The [elementary cube proof](actual-complete-deficits.md) already gives an unconditional $J^{19/3+o(1)}$ expectation and a subpower family without the additional product-twist asymptotics.

There is also a two-sided estimate for the actual complete deficit $H_{\rm par}$ of the union of the opposite-sign classes, normalized by two. This union is the arithmetic observable in the addendum to the [earlier twelfth-moment upper bound](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7154774282). Assuming rational RH,
$$
 \tfrac1{21}\ \le\ \liminf\frac{\mathbb E H_{\rm par}}{J^7\sqrt{\log J}}
 \ \le\ \limsup\frac{\mathbb E H_{\rm par}}{J^7\sqrt{\log J}}
 \ \le\ \tfrac1{7\sqrt3}.
$$
The last upper bound also holds for the mean of the best of the three individual complete classes chosen separately at every sample. Rational RH enters only through the integrated estimate $x^2/2-\sum_p(x-p)_+\log p=O(x^{3/2})$. The zero-free half-plane in #5571 remains open.

## The cube in every nonidentity cell

The [prime-supported mean-square proof](prime-sieve.md) also bounds each of the original fixed opposite-sign complete deficits from both sides on rational RH. The liminf at scale $J^7\sqrt{\log J}$ is at least $1/21$, and the limsup is at most $(2+1/\sqrt3)/7$. Its unconditional all-field second-moment estimate replaces the earlier factor $\log J$ with $\sqrt{\log J}$.

Write $x=j^4,\ Q=J^{12},\ N=|U|\asymp Q/\log Q$. Write $\lambda_p(q)=(q/p)$. The project takes $\lambda_2(q)=1$ for odd $q$, the quadratic character of the residue field of characteristic two. Thus $2^k$ contributes to none of the three nonidentity cells. All prime bases of interest are less than $q,d$. An odd prime has the signs of its odd powers, and every even power has signs $(+,+)$.

If $P_s(x)$ is four times the prime Riesz mass of a nonidentity class, its complete mass is $P_s(x)+C_s(x)$, with
$$
 C_s(x)=4\!\!\sum_{\substack{\text{odd }p,\ k\ge3\ {\rm odd}\\
           (\lambda_p(q),\lambda_p(d))=s}}(x-p^k)_+\log p\ge0 .
$$
Its exact contribution to the deficit difference is $\min([x^2/2-P_s(x)]_+,C_s(x))$.

The PNT gives $\sum_p(x-p^3)_+\log p\sim(3/4)x^{4/3}$ by integration of $3t^2\vartheta(t)$ to $x^{1/3}$. All $k\ge5$ together contribute $O(x^{6/5}\log(2x))$ before imposing signs, by Chebyshev. Since $\sum_{p\le Y}(x-p^3)_+^2\log^2p\ll x^2Y\log(2Y)$ at $Y=x^{1/3}$, the second-moment inequality of #7627 yields
$$
 \Pr\left(\left|C_{s,3}(j^4)-\sum_p(x-p^3)_+\log p\right|>
              \eta j^{16/3}\right)
 \ll \eta^{-2}j^{-4/3}\log^2(2J).
$$
Here $C_{s,3}$ is the normalized selected cube alone. Indeed $4\,1_s=(1+e\lambda_p(q))(1+f\lambda_p(d))$; use the single-twist bound $\|\sum h_p\lambda_p\|_2^2\ll\log Q\sum h_p^2$, valid when $Y^3\le Q$. Holding $d$ fixed handles the product. Conditioning on distinct primes increases a nonnegative mean by at most $N/(N-1)$. Including the prime $2$ in the unrestricted cube changes it by $O(x)$. [Exact Lean second moment](https://github.com/mlyle/riemann-masullo/blob/6129a148ba20a0aad50c4b47717276f5441aad73/RiemannMasullo/Ch13_ZerosHecke/QuadraticPrimeTwists.lean#L146)

Taking $\eta=1/\log J$, summing the displayed bound over the three classes and all $j\ge(\log J)^{15}$, costs $O(1/\log J)$. Uniformly for such $j$, outside this exceptional set,
$$
        C_s(j^4)=(3/4+o(1))j^{16/3}.
$$
Deterministically $C_s(j^4)\ll j^{16/3}$ for every $j$. Consequently even a class depending on the pair and the sample satisfies
$$
       J^{-19/3}\sum_{j\le J}C_s(j^4)\longrightarrow c_0:=9/76
$$
in probability and in every fixed finite $L^r$. The initial logarithmic range contributes a negligible amount.

## Moments of the two-prime product twist

Only odd primes occur below. Put $b_p=(x-p)_+\log p,\ P=\sum b_p,\ W=x\log(2x)$ and $B=\sum b_p^2\sim x^3\log x/3$. The last estimate follows from the PNT by partial summation, first for $\sum_{p\le t}\log^2p\sim t\log t$, then for the quadratic kernel. Write
$$
 S_q=\sum b_p\lambda_p(q),\qquad Z=\sum b_p\lambda_p(q)\lambda_p(d).
$$
For $J^{1/2}\le j\le J$, uniformly on distinct pairs,
$$
        \mathbb E (Z/\sqrt B)^r =
            \begin{cases}o(1)&r=1,3,\\1+o(1)&r=2,\\3+o(1)&r=4.\end{cases}
$$

To prove this first draw the primes independently. If $m$ is odd squarefree, put $\mu(m)=N^{-1}\sum_{q\in U}(q/m)$. Independence identifies the mean of each prime tuple in $Z^r$ with $\mu(m)^2$, where $m$ is its squarefree kernel. In particular the square terms have exactly their independent-random-sign value. Applying Heath-Brown directly with inner coefficient $1_U(q)$ gives
$$
 V(L):=\sum_{m\le L}^{*}|\mu(m)|^2
   \ll_\delta (LQ)^\delta(1+L/Q)\log Q ,
$$
where the star denotes odd squarefree integers. The order of the symbols here is exactly $(q/m)$. [Heath-Brown, Theorem 1, p. 237 (1995)](https://doi.org/10.4064/aa-72-3-235-275)

Put $V_k=V(x^k)$. Grouping by squarefree kernel gives
$$
\begin{aligned}
 |\mathbb E Z|&\le W V_1,\\
 |\mathbb E Z^2-B|&\le 2W^2 V_2,\\
 |\mathbb E Z^3|&\le 3WB V_1+6W^3V_3,\\
 |\mathbb E Z^4-(3B^2-2\sum b_p^4)|
     &\le 20W^2B V_2+24W^4V_4 .
\end{aligned}
$$
For $r=3$, the singleton coefficient is $b_p^3+3b_p\sum_{u\ne p}b_u^2$. For $r=4$, the coefficient at $pr,\ p\ne r$, comprises $4b_p^3b_r+4b_pb_r^3+12b_pb_r\sum_{u\notin\{p,r\}}b_u^2$. A product of four distinct primes has 24 orderings. Since $x^3\le Q\le x^6$ in the asserted sample range, we have $V_1,V_2,V_3\ll x^{1/10}\log(2x)$, and $V_4\ll x^{1/10}(1+x)\log(2x)$ on taking $\delta=1/100$. Also $\sum b_p^4\le W^2B$. Dividing the four errors by $B^{r/2}$ proves the claim for independent primes. The diagonal has probability $1/N$ and there $Z=P\ll x^2$. Its normalized contribution for every $r\le4$ is $O(N^{-1}(P/\sqrt B)^r)=o(1)$. This argument gives actual moment asymptotics in addition to the prior upper bounds on higher moments.

For $X=Z/\sqrt B$, Hölder gives $\mathbb E|X|\ge(\mathbb EX^2)^{3/2}/(\mathbb EX^4)^{1/2}$, while Cauchy gives the reverse upper bound $\mathbb E|X|\le(\mathbb E X^2)^{1/2}$. Hence
$$
       1/(2\sqrt3)-o(1)\le\mathbb E X_+\le 1/2+o(1).
$$
For a sign probability, put $p(y)=y(y+1)^2(3-2y)/4$. On $y\le0$, $p(y)\le0$. On $y\ge0$, $1-p(y)=(y-1)^2(2y^2+5y+4)/4\ge0$. Thus $p(y)\le1_{y>0}$. Using the four moments in $\mathbb E p((\pm X-h)/\sqrt3)$ gives, uniformly for bounded $h\ge0$,
$$
 \Pr(\pm X>h)\ge
 \tfrac16-\tfrac{h}{2\sqrt3}+\tfrac{h^3}{12\sqrt3}-\tfrac{h^4}{18}-o(1).
$$
In particular each sign exceeding $h_J=(\log J)^{-1/4}$ has probability at least $1/6-o(1)$; each sign exceeding $1/8$ has probability at least $1/8-o(1)$.

## Passing to the actual deficits

The two mixed single-cell prime masses are $P-Z\pm(S_q-S_d)$. One is at most $P-Z$ and the other is at least $P-Z$. For each of the events above, $q\leftrightarrow d$ preserves $Z$ and exchanges the two orientations. For a preassigned mixed cell the corresponding low-mass or high-mass conclusion therefore holds on at least half the event, ties included.

Under rational RH let $R=x^2/2-P$. Then $R=O(x^{3/2})$, uniformly, by the integrated von Mangoldt formula and the prime-power decomposition. Dropping $p=2$ costs $O(x)$. [Johnston, Lemmas 2.3 and 2.6](https://arxiv.org/pdf/2201.06184) For $j\ge J^{1/2}$, $h_J\sqrt B\gg x^{3/2}(\log J)^{1/4}$. Positive $Z>h_J\sqrt B$ thus makes the low-mass mixed prime deficit larger than the entire $C_s\ll x^{4/3}$. Negative $Z<-h_J\sqrt B$ gives exactly zero complete deficit in the high-mass mixed cell. At every such sample, either conclusion holds for its fixed orientation on a proportion at least $1/12-o(1)$ of distinct pairs.

In particular $\liminf \mathbb EG_s/J^{19/3}\ge c_0/12=3/304$. Indeed take $aJ\le j\le J$, where $a>0$ is fixed, apply the uniform cube asymptotic on the saturation event, sum and let $a\downarrow0$. Also $G_s/J^{19/3}\le c_0+o(1)$ outside a set of probability $o(1)$, and $G_s/J^{19/3}\ll1$ everywhere. The last two statements imply $\liminf\Pr(G_s\ge J^{19/3-\varepsilon})\ge1/12$, and even $\liminf\Pr(G_s\ge(c_0/24)J^{19/3})\ge1/23$.

For a joint statement, use $J/2\le j\le J$, $Z>\sqrt B/8$, and the low-mass orientation. The hit probability for a prescribed orientation, including $C_s\ge j^{16/3}/2$, is at least $1/16-o(1)$ at each sample. On each hit the actual complete deficit is at least $\sqrt B/16\ge J^6\sqrt{\log J}/1024$ for large $J$, and the gain equals $C_s$. If $K$ counts hits among the $L$ samples, $0\le K/L\le1$, $\mathbb E(K/L)\ge1/16-o(1)$, so $\Pr(K/L\ge1/32)\ge1/31-o(1)$. There are then at least $J/65$ hits for large $J$. This proves a joint actual-H lower bound with $c=1/(65\cdot1024)$ and gain $\ge 2^{-19/3}J^{19/3}/65$ on that proportion. No independence across $j$ is needed.

The parity-union deficit at $x$ is exactly $[R+Z-(C_{+,-}+C_{-,+})/2]_+$. Its mean on RH differs from $\mathbb E Z_+$ by $O(x^{3/2})$ by Lipschitz continuity. Summing the bounds on $\mathbb E X_+$, using $\sum_{j\le J}\sqrt B\sim 2J^7\sqrt{\log J}/(7\sqrt3)$, proves the two displayed constants. The $j<J^{1/2}$ prefix contributes at most $O(J^{9/2})$ since every complete rational mass is nonnegative. At each $j$ the larger of the two complete mixed masses is at least its arithmetic mean, which proves the asserted upper for the best cell.

Finally suppose rational RH fails. Put $e=4+4\Theta>6$. Mlyle’s every-prefix calculation gives $D(J)=J^{e+1+o(1)}$ and $A_j=[j^8/2-\sum_p b_p]_+\ll j^e$ for the unrestricted primes. For arbitrarily small fixed $\tau>0$, these give $\gg_\tau J^{1-\tau}$ indices $j\ge J^{1-\tau}$ with $A_j\ge J^{e-2\tau}$. To see this, discard earlier indices with total $O(J^{(1-\tau)(e+1)})$ and smaller values with total $O(J^{e+1-2\tau})$, then use the pointwise cap. On each remaining index the elementary second moment for prime weights bounds all three raw discrepancies $\|P_s(x)-\sum_p b_p(x)\|_2\ll J^6\log J$. Choose $\tau$ with $e-2\tau>6$. Chebyshev gives a power-saving probability of a discrepancy exceeding $A_j/3$ in any cell. The expected fraction of failing indices tends to zero. By Markov, on $1-o(1)$ of all pairs at least half of these indices pass simultaneously for all three cells. Intersect with the simultaneous cube event. On those pairs every nonidentity selector satisfies $H_s\gg J^{e+1-3\tau}$ and $G_s\gg J^{(19/3)(1-\tau)}$. Taking $\tau$ arbitrarily small proves the unconditional claims stated at the start.

If a zero actually attains $\Theta>1/2$, the constant in the clipped gain can be retained with probability tending to one. The every-prefix lower bound for this fixed zero gives $D(J)\ge cJ^{e+1}$. Since $A_j\ll j^e$, one may first discard $j<aJ$ with a sufficiently small fixed $a>0$, and then $A_j<bJ^e$ with small fixed $b>0$. At least $\delta J$ indices remain for some $\delta>0$. At each such index the $L^2$ discrepancy is $o(J^e)$, uniformly, so the expected fraction of failures is $o(1)$ across the three cells. Outside a set of probability $o(1)$ at least half the retained indices have all three prime deficits exceeding the whole cube correction. Their cube masses are simultaneously at least $j^{16/3}/2$. Thus $H'-H\gg_\Theta J^{19/3}$ on that family for every nonidentity selector, with a positive constant depending on the fixed leading zero. [Every-prefix bound from an actual fixed zero](README.md)

## Finite checks

The [finite verifier](verify_product_moments.py) checks four grouped character-moment identities by exact integer arithmetic over **all 464** primes in $(2^{12},2^{13}]$, including subtraction of the diagonal. At $J=12$ it computes every distinct pair in a reproducible sample of 96 genuine auxiliary primes. It independently enumerates prime powers for three specified pairs at every $j$, checks clipping, and checks the optimized-cell upper bound by the parity deficit for all 9,120 distinct ordered pairs. The four terminal standardized moments were $0.01913,\ 0.96522,\ 0.08238,\ 2.79044$. The finite experiment is an arithmetic interface check. The asymptotic statements above are paper proofs; the transfer into these moment asymptotics has not been formalized in Lean.
