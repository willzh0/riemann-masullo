# An explicit finite Hardy grid for varying Hecke characters and number fields

Let $d=[F:\mathbf Q]$. Fix a continuous multiplicative norm section and a unitary Hecke character $\chi$ trivial on it. Set $Q_\chi=|\operatorname{disc}F|\,\mathrm N\mathfrak f_\chi$. At a real place let $\beta_v=i\nu_v+e_v$ with parity $e_v\in\{0,1\}$. At a complex place let $\beta_v=i\nu_v+|\ell_v|/2$ with angular weight $\ell_v\in\mathbf Z$. These are the shifts in the project's local gamma factors. Write $B_\chi=1+\sum_{v\mid\infty}|\beta_v|$. All logarithms are natural unless a base is indicated. [Hecke gamma parameters and their half-integer estimate](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/AppB_AnalyticNT/HeckeGammaShiftBound.lean#L85)

Fix a field and character with $d\le k$, $Q_\chi\le2^k$ and $B_\chi\le2^k$ for some integer $k\ge3$. Fix **one exponent** $N\ge100dk$, and put $p_0=\max(k,\lceil N/(100d)\rceil)$. For every integer precision $p\ge p_0$ and every index $n\ge2^{1000000dp^2}$, the original corrected Gaussian-rational finite ideal residual satisfies
\[
 0\le U_{\chi,N,n}-(1-e^{-2G_\chi})<2^{-p}.
\]
Consequently, at every $n\ge2^{1000000dp_0^2}$ the error is bounded above by
\[
 2^{\,1-\sqrt{\log_2 n/(1000000d)}}.
\]
Indeed take $p=\lfloor\sqrt{\log_2 n/(1000000d)}\rfloor$. The single choice $N=100dk$ works at every precision $p\ge k$, uniformly in all fields and characters satisfying the same caps. The logarithmic estimate below obtains explicit precision for $G_\chi$ itself on the **same** sequence of finite tables.

Here $G_\chi\ge0$ is the pole-corrected half-plane Green sum from two. The result gives an accuracy and onset for an existing arithmetic expression, with no zero verification. The grid values at these indices have not been evaluated. The general root-log rate has a Lean proof with existential constants. The argument below gives explicit family parameters using the functional equation, a disk sublevel estimate and finite Taylor extrapolation. [Original finite grid](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/AppB_AnalyticNT/HeckeFiniteHardyGreen.lean#L639) · [General formal rate](https://github.com/mccorvie/riemann-masullo/pull/7722) · [Earlier sharper rational-conductor parameters](https://github.com/willzh0/riemann-masullo/blob/a6a348cb8b9a12a7ab1fd37a956062f8e0092d4f/research/5571/quartic-hardy-trials/CONDUCTOR-GRID.md)

## Uniform analytic normalization

Write $\delta=1$ for the principal character and $\delta=0$ otherwise, and fill removable values by continuation. Work first with $A(s)=((s-1)/(s+1))^\delta L(s,\chi)$. For the principal character the filled value at one is $\operatorname{Res}_{s=1}\zeta_F/2$. This function is holomorphic in a neighborhood of the closed strip $-1/2\le\Re s\le2$. The usual unitary Hecke functional equation in the project's convention is
\[
 \Lambda_{\chi^{-1}}(1-s)=c_\chi Q_\chi^{s-1/2}\Lambda_\chi(s)
\]
for the completion without the factor $Q_\chi^{s/2}$. The Euler product and local gamma factors give $\Lambda_{\chi^{-1}}(s)=\overline{\Lambda_\chi(\bar s)}$ by analytic continuation. Apply the two identities at $s=2$ and $s=-1$. Since $\Lambda_\chi(2)\ne0$, taking the conjugate of the first equality and substituting in the second gives $|c_\chi|^2=1$. For $\sigma>1$, $|L(\sigma+it,\chi)|\le\zeta_F(\sigma)\le\zeta(\sigma)^d$ by the local Euler products. [Conductor-scaled functional equation](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/AppB_AnalyticNT/Sec4b.lean#L1860)

On the line $\sigma=-1/2$, gamma recurrence and conjugation bound the modulus of the reflected-to-original gamma quotient by $(B_\chi+3+|t|)^d$. The finite dual Euler bound at $3/2$ is at most $3^d$, and $|(s-1)/(s+1)|\le3$. Thus
\[
 |A(-1/2+it)|\le 3 Q_\chi 3^d (B_\chi+3+|t|)^d.
\]
Take $h=B_\chi+4$. At the left boundary $B_\chi+3+|t|\le2|s+h|$. On $\sigma=2$ the quotient $|A(s)/(s+h)^d|$ is at most $2^d$. The Phragmén–Lindelöf principle for a fixed vertical strip therefore gives throughout it
\[
 |A(s)|\le 3Q_\chi6^d |s+h|^d.
\]
The polynomial vertical growth needed for the strip principle is qualitative. Its constants do not enter this upper bound. For $\sigma\ge1/10$ the actual pole-cleared function $C(s)=((s-1)/s)^\delta L(s,\chi)$ has $|C(s)/A(s)|\le11$ wherever the ratio is defined. The factor relation extends across removable values. In particular $C(1)=\operatorname{Res}_{s=1}\zeta_F$ for the principal character. Since $|s+h|\le(B_\chi+4)|s+1|$ there, and the ordinary Euler bound applies on $\sigma\ge2$, we obtain
\[
 |C(s)|\le M|s+1|^d,\qquad M=36Q_\chi[6(B_\chi+4)]^d \quad(\sigma\ge1/10).
\]
The local shifts above apply to every complex angular weight and real spectral parameter. [Fixed-strip growth](https://github.com/willzh0/riemann-masullo/blob/9555044c7d3dc27ffa05e503615fab73b1c1c404/RiemannMasullo/AppB_AnalyticNT/Sec1.lean#L2511) · [Mathlib strip Phragmén–Lindelöf theorem](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Complex/PhragmenLindelof.lean#L275)

Fix $N\ge100dk$. The hypotheses give $M\le2^{6+k+d(k+4)}$. Since $(5/4)^4>2$ and $N-d-2\ge4(6+k+d(k+4))$, the analytic function $C(s)/(s+1)^{N-2}$ is bounded by one on $\sigma\ge1/4$. Cauchy's estimate at radius $1/4$ gives derivative bound four on $\sigma\ge1/2$. With $s=(2+z)/(1-z)$ the scalar-one disk function $F(z)=C(s)/(s+1)^N$ extends continuously with $F(1)=0$. The identity $1/(s+1)=(1-z)/3$ and the chain rule give $\|F\|_\infty\le1$ and $|F'(z)|\le16/9$ on the disk off that point. The removable principal value at $s=1$ is included. The Hardy squared distance is $R=1-e^{-2G_\chi}$ by the pole-corrected boundary identity and Szegő's formula. [Coefficient energy and normalization](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/AppB_AnalyticNT/HeckeFiniteHardyGreen.lean#L136) · [Szegő's prediction theorem](https://doi.org/10.1007/BF01199955)

## Accuracy of the canonical ideal row

Put $P(s)=(1-2^{1-s})^2L(s,\chi)$. On $\Re s\ge2$, $|P(s)|\le9\cdot3^d$. On every $\sigma=1/2-m$, $m\ge1$, the squared Euler filter has modulus at most $9\cdot4^m$, the conductor factor costs $Q_\chi^m$, and the local gamma recurrences cost $(B_\chi+3m+|t|)^{dm}$. With $K=\max(9\cdot3^d,4Q_\chi)$ this gives
\[
 |P(s)|\le K^{m+1}(B_\chi+3m+|t|)^{dm}.
\]
The finite Taylor extrapolation lemma then bounds $|P(s)|\le(2u)^{(4d+1)u}$ on every needed circle at scale $u=2^j$ as soon as $u\ge K^5[2(B_\chi+40)]^{4d}$. In particular the base-two logarithm of this onset is at most $10k+20+4d(k+4)$. [Exact boundary-to-disk lemma](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/ForMathlib/NumberTheory/LSeries/PolynomialExtrapolation.lean#L185) · [Finite Hecke boundary bounds](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/AppB_AnalyticNT/HeckePolynomialBounds.lean#L188)

In the original table $m'=2n+1$, $v=6(m'+1)$, $j=\lfloor\log_2(v+2)\rfloor+1$, and $u=2^j\ge v+1$. All $n\ge2^{1000000dp^2}$ with $p\ge p_0$ clear this onset, since $p\ge k$. The coefficient mass at two is at most $(1+4/2^2+4/4^2)\zeta_F(2)\le(9/4)2^d$. The ordinary input is the sum $a_r$ of the character values of all integral ideals of norm $r$, with ramified local factors omitted in its primitive Euler product. Each corrected coefficient is $a_r-4a_{r/2}+4a_{r/4}$, with terms having nonintegral indices set to zero. The table uses ordinary norm indices strictly below $[4(v+2)]^{4d+7}=(48n+56)^{4d+7}$ and the principal-character flag. [Exact cutoff and ideal coefficients](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/AppB_AnalyticNT/FiniteHardyIdealTable.lean#L345) At $\lvert z\rvert\le1/5$, $\Re s\ge3/2$, the inverse squared Euler factor costs at most $(1-2^{-1/2})^{-2}<12$, and both $\lvert(s-1)/s\rvert^\delta$ and $\lvert(1-z)/3\rvert^N$ are at most one. Thus the true disk value error at the nodes is at most $12(2+(9/4)2^d)2^{-3(j+1)u}\le2^{-v}$. Fourier extraction at its $12(m'+1)$ nodes on $\lvert z\rvert=1/8$ bounds every coefficient error through $m'$ by
\[
 8^{m'}\big(2^{-6(m'+1)}+(8/3)(5/8)^{12(m'+1)}\big)\le4^{-m'}.
\]
This uses the cap $\lvert F\rvert\le1$ at $\lvert z\rvert=1/5$ and $(5/8)^2<1/2$. [Original finite extrapolation](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/AppB_AnalyticNT/FiniteHardyIdealTable.lean#L30) · [Fourier row](https://github.com/willzh0/riemann-masullo/blob/a332ca1e157a11eeda1ed7074619a015b33abfc7/RiemannMasullo/AppB_AnalyticNT/FiniteHardyIdealTable.lean#L343)

## A uniform clipping estimate and the finite minimum

For each $j\in\mathbf Z$ consider $I_j=[j-1/2,j+1/2]$. On the disk of radius $19/10$ centered at $2+ij$ the analytic pole-cleared function has modulus at most $M_j=M[4(|j|+2)]^d$. At the center the Euler product, including the principal clearing factor, gives the lower bound $2^{-d-1}$. Write $A_j=\log(2^{d+1}M_j)$. Jensen's disk inequality, taking outer radii tending to $19/10$ that contain no zero on their circle, bounds the number of zeros through radius $9/5$, counted with multiplicity, by $20A_j$. Choose a zero-free circumference of radius between $7/4$ and $9/5$. After dividing out the finite Blaschke factors in that disk, Harnack's inequality for its remaining logarithm gives a bound $24A_j$ on the critical segment. Each Blaschke factor through the segment has modulus at least the distance to its zero divided by four. Hence
\[
 \left|\{t\in I_j:-\log|C(1/2+it)|>24A_j+y\}\right|
 \ \le\ 160 A_j e^{-y/(20A_j)}\quad(y>0).
\]
Isolated critical-line zeros form a null set. All their orders are retained in Jensen's inequality. [Disk sublevel argument and constants](https://github.com/willzh0/riemann-masullo/blob/a6a348cb8b9a12a7ab1fd37a956062f8e0092d4f/research/5571/quartic-hardy-trials/CLIPPED-OUTER.md#explicit-quartic-clipping-at-all-heights) · [Euler lower bound for the filled continuation](https://github.com/willzh0/riemann-masullo/blob/5e6a89356bd592a93269a96113bb7c3315605fae/RiemannMasullo/AppB_AnalyticNT/Sec4b_HeckeVerticalDisks.lean#L100)

On the critical line the normalization adds at most $N\log(|j|+2)$ to $-\log|C|$. Let $Y=-\log|F|$ in this boundary coordinate, $J=2^{100p}$ and $H=100000dp^2$. Here $d\le k\le p$ and $N\le100dp$. The Cayley circle measure has Cauchy density $3/(2\pi((3/2)^2+t^2))$. The sum of its interval suprema is below nine. For $|j|\le J$,
\[
 A_j\le 110dp,\qquad
 H-24A_j-N\log(J+2)\ge 40p\cdot20 A_j.
\]
Integration of the sublevel bound above height $H$ gives a contribution to $e_H=\int(Y-H)_+$ of at most $9\cdot3200(110dp)^2e^{-40p}<2^{-p}/64$ from all these blocks. For $|j|>J$ the integral of $Y$ on $I_j$ is at most $(3224+N) A_j^2$. Use $A_j\le C_0+d\log |j|$ where $C_0=\log(2^{d+1}M\,12^d)$, $C_0+d\log J\le110dp$. The density is at most $2/j^2$ on these blocks. Integrating the decreasing function $(C_0+d\log x)^2/x^2$ gives the far-block bound
\[
 \frac{4(3224+N)}{J}\big((110dp)^2+2d(110dp)+2d^2\big)<2^{-p}/64.
\]
For the near bound one can replace its prefactor by $2^{29}p^4$, and use $p\le2^p$ and $e>2$. The far prefactor is at most $2^{25}p^6$, since $3224+100dp\le460p^2$ and $(110dp)^2+2d(110dp)+2d^2\le12200p^4$. Both exponential remainders are therefore less than $2^{-p}/64$. Thus $e_H<2^{-p}/32$.

Let $\epsilon=2^{-p}$. In the clipped outer predictor use smoothing tolerance $\epsilon/64$. Its untruncated squared residual is at most one and at most $R+2(e_H+\epsilon/64)$. The size condition $50e^{4H}\le n+1$ allows degree-$n$ truncation in the required ellipsoid. Rounding the two coordinates of each coefficient toward zero at denominator $(n+1)^3$ preserves its weighted budget. The error through the visible row, the rounding, and the table's own hidden-tail correction add at most $12/\sqrt n\le\epsilon/64$ to the untruncated residual norm. The same row-error and derivative estimates give the opposite bound $R\le U$ from the hidden-tail inequality applied to every grid element. Consequently $U-R\le2(e_H+\epsilon/64)+2(\epsilon/64)+(\epsilon/64)^2<\epsilon$. This applies also when $R=0$. [Trial, truncation and rounding estimates](https://github.com/willzh0/riemann-masullo/blob/a6a348cb8b9a12a7ab1fd37a956062f8e0092d4f/research/5571/quartic-hardy-trials/CLIPPED-OUTER.md#a-bounded-analytic-predictor-from-a-clipped-modulus) · [Formal clipped predictor](https://github.com/mccorvie/riemann-masullo/pull/7721)

## Effective precision for the full logarithmic Green sum

Let $R_\chi=1-e^{-2G_\chi}$ and $b=7+k+d(k+7)$. The same half-plane estimate gives a uniform lower bound for the complementary mass,
\[
 1-R_\chi=e^{-2G_\chi}\ \ge\ 2^{-2b}.
\]
Indeed the pole-corrected Cauchy log identity gives $G_\chi=\int\log|C(1/2+it)|\,d\mu(t)-\log|C(2)|$, with the probability measure in the preceding section. At two the absolute Euler lower bound including the pole correction gives $|C(2)|\ge2^{-d-1}$. The elementary integral $\int\log|3/2+it|\,d\mu(t)=\log3$ follows from $t=(3/2)\tan \theta$ and $\int_0^{\pi/2}\log(\cos\theta)\,d\theta=-(\pi/2)\log2$. The latter follows by reflection and the double-angle identity for $\sin(2\theta)$. Therefore
\[
 G_\chi\le \log M+d\log3+(d+1)\log2\le b\log2.
\]
These estimates also apply when $C$ has zeros on the boundary, since its logarithm is integrable there. [Ordinary pole-corrected Cauchy identity](https://github.com/mccorvie/riemann-masullo/pull/7696)

Given an integer $\ell\ge1$, set $p=\max(p_0,2b+\ell+1)$. For the same fixed exponent $N$ and every $n\ge2^{1000000dp^2}$ we have $U_{\chi,N,n}<1$ and
\[
 0\le-\tfrac12\log(1-U_{\chi,N,n})-G_\chi<2^{-\ell}.
\]
To see this, put $x=(U_{\chi,N,n}-R_\chi)/(1-R_\chi)$. Then $0\le x<2^{-\ell-1}$, and the logarithmic difference is $-\tfrac12\log(1-x)\le x$ on $[0,1/2]$. This supplies an accuracy and onset for the true all-height integral from the original finite arithmetic table, without any zero data. For example the degree-one family with $k=3$, $N=300$ may take $b=20$, $p=61$ for twenty binary places. The earlier rational-character estimates exploit periodicity and give smaller indices. No logarithmic table evaluation is needed for the error bound.

## A finite comparison over growing arithmetic families

Choose one representative of each number field up to isomorphism and one norm section for that representative. Let $\mathcal C_k$ contain the normalized characters with $d\le k$, $Q_\chi\le2^k$ and $B_\chi\le2^k$. Hermite–Minkowski finiteness bounds the fields because $|\operatorname{disc}F|\le Q_\chi$. There are finitely many conductor ideals and finite-unit characters in each field. The archimedean parities and angular integers are bounded. For any fixed such data, the Dirichlet unit equations place the real archimedean exponents modulo the common norm direction in a translate of the dual of the unit lattice. Bounded shifts meet finitely many points of that lattice. If two characters have the same finite-unit data, angular data and archimedean parameters modulo the common norm direction, their ratio is a norm twist times a character of the finite ideal class group. The class character is trivial on the connected image of the section. Two normalized representatives therefore have the same common twist. This proves finiteness, and every fixed normalized character occurs for all large $k$. With arbitrary input sections the assertion is mathematical finiteness. Evaluation with certified error requires effective field and character data. Deciding membership in the exact closed archimedean bound at equality also needs more than arbitrary real approximations. Molin–Page give a coordinate method with a certified-precision analysis for specified algebraic oracles. [Milne, *Algebraic Number Theory*, Theorems 4.4, 5.9 and 8.43](https://www.jmilne.org/math/CourseNotes/ANT.pdf) · [Molin–Page, Definition 16, Algorithms 17–18 and Remark 19](https://arxiv.org/abs/2210.02716)

Put $M_k=\max_{(F,\chi)\in\mathcal C_k}U_{\chi,100dk,\,2^{1000000dk^2}}$. The rational principal character makes the family nonempty. Since the families are increasing and every finite error is less than $2^{-k}$,
\[
 \lim_{k\to\infty} M_k
   = \sup_{F,\chi}(1-e^{-2G_\chi}).
\]
The exterior assertion at all positive widths over all these fields is equivalent to $M_k\le2^{-k}$ for every $k\ge3$, and also to this upper bound at arbitrarily large $k$. A certified strict $M_k>2^{-k}$ at a single stage would imply that at least one row in that family has an off-line zero. The universal arithmetic upper remains open. No finite maximum at these stages has been evaluated. [Original exterior-sum implication](https://github.com/willzh0/riemann-masullo/blob/03d3305db4e489507d12955604ddad057f74ab64/RiemannMasullo/Ch12_TraceGeometric/Sec5_Isolated.lean#L1576)

## Checking the constants

Running the standard-library command below reproduces [the rational and polynomial certificate](receipt.json). The verifier translates each polynomial in $p,d$ (or $k,d$) to powers of $p-3,d-1$ (or $k-3,d-1$) and checks its coefficients. The proof above supplies the analytic estimates and the indicated uses of $d\le k\le p$. The certificate evaluates none of the Hardy minima. The accompanying [Mathlib arithmetic checks](UniformConstants.lean) verify the dyadic constants and conversion to a logarithmic error. Their six printed roots use precisely the three standard Lean axioms. The full uniform parameter theorem above is a written proof.

```
python check_uniform_grid.py
```
