# Testing the exterior zeros on one tower of normal number fields

For Masullo's Theorem 12.5.1.1, pp. 519–520, the supremum of the horizontal distances of all nontrivial Hecke zeros from the critical line can be recovered from signed sums in the paper's own test space. Choose one fixed tower of normal number fields. At stage $n$, translates of one compact real test give the signed observations. Averaging each translate with its inverse gives an inversion-even test with the same signed result. A fixed, locally finite grid of rational log-norm translations suffices at every stage. The tests depend only on the fields and characters. [Original issue and statement](https://github.com/mccorvie/riemann-masullo/issues/5571) · [Test-space equivalence on main](https://github.com/mccorvie/riemann-masullo/blob/9c791d74a81f1191d900e6d96f1270acee9b033e/RiemannMasullo/Ch12_TraceGeometric/Sec5.lean#L1174)

The stronger form assigns **one number-field test per sampling time** across the entire tower, with $T^3/3+O(T^2)$ samples through time $T$. After normalization using the completed logarithmic derivative at $s=2$, the single chronological growth rate equals the all-field horizontal reach. Even the signed values rounded to integers determine the individual character multiplicities at all the measured upstairs exterior sites. [Chronological schedule, normalization and reconstruction](SCHEDULE.md)

## Fields and characters

Work inside a fixed algebraic closure of $\mathbb Q$. On each number field $F$ choose the norm section $s_F(u)$ with every archimedean component the positive real $u^{1/[F:\mathbb Q]}$ and every finite component 1. For a finite extension $L/F$, the local archimedean degrees over each place of $F$ sum to $[L:F]$. Consequently $N_{L/F}s_L(u)=s_F(u)$, including above a real place that becomes complex. The normalized unitary characters of $C_F$ are precisely the dual of the compact norm-one classes $C_F^1$. This dual is countable since its characters are orthogonal in the separable space $L^2(C_F^1)$.

Enumerate the pairs $(F_i,\psi_i)$ comprising every embedded number field and every such normalized character. Let $K_n$ be the Galois closure of the compositum of $F_1,\ldots,F_n$. Let $P_n$ be the finite **set** of the pullbacks to $K_n$ of $\psi_i$ and $\psi_i^{-1}$ for $1\le i\le n$. Pullback carries $P_n$ into $P_{n+1}$. Repeated characters on a given field occur once. The construction includes characters of infinite order with archimedean variation. It uses a countable exhaustion and requires no computed list of their zeros.

Write $V_n$ for the Tamagawa volume of $C_{K_n}^1$. Choose a fixed real compact smooth radial profile $h$ supported in $[2,4]$, whose Mellin transform $M(w)$ is nonzero for $0<|\Re w|<1/2$. The explicit quadratic box construction also gives $M(0)=M(\pm 1/2)=0$. For $q\ge0$ take the following admissible test on $K_n$.

$$
 B_{n,q}(x)=V_n^{-1} h(\log |x|-q)\sum_{\lambda\in P_n}\overline{\lambda(x)}.
$$

The angular polynomial is real because $P_n$ is stable under inversion. Each character is smooth at infinity and locally constant on the compact finite unit factors. Radial compactness and compactness of $C_{K_n}^1$ give compact support. The function vanishes on every norm-one class. Put $a_n=1/(n+2)$. Write $m(\lambda,\rho)$ for the order of the completed Hecke function at an open-strip site, using zero at a nonzero value of the function. Orthogonality cancels $V_n$ and gives the native signed exterior sum
$$
 S_n(q)=\sum_{|\Re w|\ge a_n} b_n(w)M(w)e^{qw},\qquad
 b_n(w)=\sum_{\lambda\in P_n}m_{K_n}(\lambda,1/2+w).
$$
Here $w$ ranges over the distinct centered zero sites in the packet. The site multiplicities and both edges of the strip enter as printed. Inversion maps $(\lambda,w)$ to $(\lambda^{-1},-w)$ by the completed functional equation. Thus replacing $B_{n,q}$ by $(B_{n,q}(x)+B_{n,q}(x^{-1}))/2$ leaves this signed sum equal to $S_n(q)$. These last tests are real and inversion-even. The absolute sums below use the original forward tests $B_{n,q}$. [Section and character tests](https://github.com/mccorvie/riemann-masullo/blob/9c791d74a81f1191d900e6d96f1270acee9b033e/RiemannMasullo/Ch12_TraceGeometric/Sec5.lean#L866) · [Inversion on the exterior](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7122971222)

## A signed measurement of horizontal distance

For each integer $k\ge2$ sample the nonnegative rationals
$$
 \mathcal Q_k=\{k+j/k^2:-k^2\le j\le 2k^2,\ j\in\mathbb Z\},\qquad
 \mathcal Q=\bigcup_{k\ge2}\mathcal Q_k .
$$
There are $O(T^3)$ trial translations up to $T$ per field and packet. Define
$$
 d_n=\limsup_{\substack{q\to\infty\\q\in\mathcal Q}}
             \frac{\log(1+|S_n(q)|)}{q}.
$$
Then $d_n$ is **exactly** the supremum of $|\Re\rho-1/2|$ among the selected zeros in the closed exterior, with value zero for an empty exterior. The sequence $d_n$ is nondecreasing and
$$
 \lim_{n\to\infty}d_n
   =\sup_{F,\psi,\rho}\left|\Re\rho-\tfrac12\right|.
$$
The supremum on the right ranges over all number fields, all unitary Hecke characters and all their open-strip zeros. In particular all $d_n=0$, their limit being zero, and the full assertion of #5571 are equivalent. It also suffices for the signed sums on the grid to vanish at every sufficiently large translation for each $n$. The central analytic question on p. 520 is now whether each of these growth rates vanishes. [Proof of the sampling and residue formulas](SAMPLING.md)

## A monotone sum of the norms of the original terms

At each stage use $B_{n,0}$ and sum the norms of its original summands. This gives
$$
 A_n=\sum_{|\Re w|\ge a_n} b_n(w)|M(w)|.
$$
Fixed-character counting and rapid vertical decay prove absolute convergence at each finite stage. For a finite Galois extension $L/F$, the upstairs order of a norm pullback dominates the **sum** of the orders of all distinct downstairs characters having that same pullback, at the same site. Group the old rows of $P_n$ by their images to obtain $A_{n+1}\ge A_n$. Equality of images at different stages therefore costs no multiplicity. The same argument preserves the support of the old divisor and proves monotonicity of $d_n$. [Classical arithmetic proof and an example](TRANSFER.md)

If $(F_i,\psi_i,\rho)$ is any off-line witness, every sufficiently late stage satisfies
$$
 A_n\ge m_{F_i}(\psi_i,\rho)\,|M(\rho-1/2)|>0,\qquad
 d_n\ge |\Re\rho-1/2| .
$$
Conversely each nonzero measurement comes from an actual off-line site. Thus $\liminf A_n=0$ is another equivalent form of #5571. No value of either limit is established here. For independent choices of norm sections one normalizes a given full character by an imaginary power of the norm. This translates its zero ordinate and the Mellin argument by opposite shifts in the same physical integral and preserves horizontal distance. Hence the canonical coordinates detect the original all-section assertion. [Chart computation](https://github.com/willzh0/riemann-masullo/blob/9c621eacaf985d182bd9f93a03e75d7af822fa01/research/7220/hecke-perfect-powers/DESCENT.md)

The fixed-character one-sided translated-test criterion is due to KadirKess. Mlyle also gives a field-wide choice of radial profile for weighted defects. Earlier finite-conductor calculations give a monotone absolute criterion over $\mathbb Q$. The field transfer, the coincident positive multiplicities of all rows of a packet, and the locally finite sampling estimate produce the tower formulas above. [KadirKess](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7128949260) · [Mlyle](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7148602651) · [Rational finite-conductor test](https://github.com/mccorvie/riemann-masullo/pull/7714)