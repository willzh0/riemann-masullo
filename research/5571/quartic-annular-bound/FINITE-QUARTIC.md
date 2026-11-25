# A finite critical-scale bound on the actual quartic annular prime sum

For Masullo, Theorem 12.5.1.1, pp. 519–520, fix the primitive quartic character modulo five with $\chi(2)=i$. Use the unchanged prime statistic from the [positive annular criterion](https://github.com/willzh0/riemann-masullo/blob/b61df9f867cec621a23ea9cfc7a5ff9c8b7f8622/research/5571/quartic-periodic-dilation/linear-prime-cutoffs.md),
$$
 K(u)=\int_1^2(1-uv)_+\,dv,\qquad Q_\chi(y)=\sum_{p\le y}\chi(p)\log p\,K(p/y).
$$
For **every integer $1\le j\le10^{39}$** the full complex value satisfies $|Q_\chi(j)|<0.951\sqrt j$. For every real $10^{24}\le y\le10^{38}$ the bound is $0.428\sqrt y$. The cumulative full norm satisfies $\sum_{j\le J}|Q_\chi(j)|<J^{3/2}$ for **every integer $1\le J\le5\cdot10^{39}$**. This permits arbitrary phases at each sample. The open step is to prove the critical exponent along some sequence of cutoffs tending to infinity. Mlyle's earlier bound through $8{,}000{,}000$ concerns the different, unrestricted triangular sample at $j^4$. We use the verified low-zero and residue inputs from that work. [Original calculation and its prior credit](https://github.com/mlyle/riemann-masullo/tree/3f90b6c75f2e36f52c2c9cb427155a556bcee9d8/research/5571/quartic-mod-five-deficit)

## Smoothing the complete sum

Write $D(y)=\sum_n\chi(n)\Lambda(n)K(n/y)$. Set $\delta=2.9\cdot10^{-7}$, $v=\delta^2$, $c=e^{-v/2}$, and let $\nu=(1+c)N(0,v)-cN(0,2v)$, with the second parameter denoting variance. Its Laplace transform is $M(z)=(1+c)e^{vz^2/2}-ce^{vz^2}$. In particular $M(0)=M(1)=M(-1)=1$. Put $D_\nu(y)=\int D(ye^{-h})\,d\nu(h)$.

The first triangular explicit formula for this odd nonprincipal character supplies, for all $x>0$,
$$
 \left|\sum_n\chi(n)\Lambda(n)(1-n/x)_+
       +\sum_\rho\frac{x^\rho}{\rho(1+\rho)}\right|
 \le4+8/x .
$$
For $x>1$ the residual before division by $x$ is $a_0 x+1+\log x-a_1-\sum_{m\ge1}x^{-2m}/[2m(2m+1)]$, with $|a_0|,|a_1|<1$. For $0<x<1$ the prime side is empty and the absolute zero weight is bounded by the completed logarithmic derivative, as detailed in the referenced calculation. Nontrivial zeros include both signs of the ordinate, with multiplicity. Integration over $1\le b\le2$ at $x=ye^{-h}/b$, followed by $\nu$, gives
$$
 \left|D_\nu(y)+\sum_\rho y^\rho \kappa(\rho)M(\rho)\right|\le 12+37/y,\qquad
 \kappa(z)=\frac{\int_1^2 b^{-z}\,db}{z(1+z)}
          =\frac{2^{1-z}-1}{(1-z)z(1+z)} .
$$
Absolute zero weights and the Gaussian exponential moments justify the integrations. The constants use $\|\nu\|_{\mathrm{TV}}\le3$ and $12\int e^h d|\nu|(h)<37$. [Odd triangular formula and quartic parameter calculation](https://github.com/mlyle/riemann-masullo/blob/3f90b6c75f2e36f52c2c9cb427155a556bcee9d8/research/5571/quartic-mod-five-deficit/README.md)

Platt's verification gives $\Re\rho=1/2$ through $H=20{,}000{,}000$ for both quartic conjugates, hence at every $|\Im\rho|\le H$ for this character. The positive sum $B=2\sum_\rho\Re(1/(1-\rho))$ is below $0.204$. Thus on those zeros $\sum |1/[\rho(1+\rho)]|\le B$. On $0\le\Re z\le1$, $|M(z)|\le1.00001$. To see this, write $x=e^{-v(\Im z)^2/2}$ and $b=e^{v/2}$. Then $|e^{vz^2/2}-x|\le b-1+b\delta$, by $|t|e^{-vt^2/2}\le1/\delta$. Compare with $(1+c)x-cx^2\in[0,1]$. Their difference in modulus is bounded by $(3+b)(b-1+b\delta)$. The entire low-zero contribution is therefore at most $0.16900\sqrt y$, using $\int_1^2 b^{-1/2}db=2(\sqrt2-1)$. [Platt, Theorem 7.1, p. 14](https://arxiv.org/pdf/1305.3087#page=14)

Above $H$, put $S_3=\sum_{|\gamma|>H}|\gamma|^{-3}$. The two-sided count satisfies $N(T)=T\log(5T/(2\pi e))/\pi+E(T)$ with $|E(T)|\le0.298\log(5T)+4.358$. Integration by parts against $T^{-3}$ gives
$$
 S_3\le\frac{\log(5H/(2\pi))+1/2}{2\pi H^2}
  +\frac{2(0.298\log(5H)+4.358)+0.298/3}{H^3}<6.798\cdot10^{-15}.
$$
As $|\kappa(\rho)|\le 3|\gamma|^{-3}$, the contribution for $y\ge1$ is at most $2.022\cdot10^{-21}y$, from the two Gaussian factors at $H$. [Bennett, Martin, O'Bryant and Rechnitzer, *Counting zeros of Dirichlet L-functions*, Corollary 1.2, p. 1456](https://personal.math.ubc.ca/~bennett/BeMaObRe-MathComp-2021.pdf#page=2)

## Cost of returning to the unchanged kernel

Write $F(t)=(e^t+e^{-t}-2)\mathbf1_{t>0}$. Then $K(e^r)=1-\tfrac32e^r+F(r+\log2)-F(r)/2$. At a given knot take the analytic expression for $F$ on the side containing $t$ and extend it over the whole line. Its $\nu$-average after translation by $h$ equals its starting value. The error is confined to points crossing the knot. For $s=|h|$ its modulus is at most $e^s(s-|t|)_+^2$, because $2(\cosh w-1)\le w^2e^{|w|}$. For each fixed $h$ and knot all crossings have the same sign. Use the zero branch at $t=0$.

In the following $M_k(a)=\int |h|^k e^{a|h|}\,d|\nu|(h)$. The accompanying certificate bounds this by twice the corresponding $N(0,v)$ moment plus one $N(0,2v)$ moment. For $h=\sigma Z$, $Z\sim N(0,1)$, use
$$
 \mathbb E |h|^k e^{a|h|}\le \sigma^k\big(\mathbb E|Z|^k+
      a\sigma\sqrt{2(2k+1)!!}\,e^{a^2\sigma^2}\big).
$$
This follows from $e^u\le1+ue^u$ and Cauchy–Schwarz. For the cubic term the sign of the density can be used exactly. It changes on the positive half-line at $\delta r$, with $r=2\sqrt{\log(\sqrt2(1+c)/c)}$. Put $T(t)=2(t^2+2)e^{-t^2/2}/\sqrt{2\pi}$ and $m_3=2\sqrt{2/\pi}$. Integration over the two signs yields
$$
 J_3=\delta^{-3}\int|h|^3\,d|\nu|(h)
  =(1+c-2\sqrt2 c)m_3+2\{2\sqrt2 c\,T(r/\sqrt2)-(1+c)T(r)\}<2.731 .
$$
Thus $M_3(2)+M_4(2)\le\delta^3J_3+3M_4(2)$ by $e^{2s}\le1+2se^{2s}$. 

In particular $M_1(1)<2.8\delta$, $M_2(2)<4.1\delta^2$, $M_3(2)<7.8\delta^3$ and $M_4(2)<18.1\delta^4$.

For $10^6\le y\le10^{24}$, count all integers in the two crossing intervals. At a knot $ay$, $a=1/2$ or $1$, the symmetric interval has length at most $2ay s e^s$. Its log weights are at most $\log(2y)+s$. Including the knot coefficients $1,1/2$ yields
$$
 |D-D_\nu|\le (2yM_3(2)+1.5M_2(2))\log(2y)+2yM_4(2)+1.5M_3(2).
$$

For $y\ge10^{24}$ handle primes by residue. Choose any phase and project the error onto its real part. At a fixed $h$, knot, and sign of the density of $\nu$, the sum of the positive weights among the four residues is at most $|\sin\theta|+|\cos\theta|\le\sqrt2$. The expression
$(s-|t|)_+^2=\int_0^s2(s-z)\mathbf1_{|t|<z}\,dz$ permits a one-sided interval count. Depending on the sign of $h$, the interval is $(ay e^{-z},ay]$ or $(ay,ay e^z]$. Endpoints varying with $z$ have measure zero. The fixed endpoint $ay$, when present, is included on precisely the lower side.

Let $z_0=4y^{-1/4}$. For $z\ge z_0$ the interval length satisfies $y^{3/4}\le L\le ay z e^z$. Indeed $1-e^{-z}\ge z/2$ up to $z=1$, and $1-e^{-z}\ge1/2$ thereafter. Now $\log(L/5)\ge0.72\log y$. Brun–Titchmarsh bounds the prime count in each reduced residue by $L/[2\log(L/5)]$. After weighting by $\log y+z$ and summing only the favorable residues, the count is at most $ay z e^z(1+z)$ since $\sqrt2/(2\cdot0.72)<1$. The knot coefficients satisfy $\sum_j c_j a_j=1$. Integrating $2(s-z)z$ therefore bounds this part of the error by $y(M_3(2)+M_4(2))/3$. This bound works for the full complex norm by taking its maximizing phase. [Montgomery and Vaughan, Theorem 2, (1.10), p. 121](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf#page=3)

For $z<z_0$ the integer bound $(ayze^{z_0}+1)(\log y+1)$ applies. Integrating over $z$ costs, after both knot coefficients, at most $2s(1+\log y)(8e^{z_0}\sqrt y+1.5z_0)$. This gives $17(1+\log y)\sqrt y\,M_1(1)$ after the outer expectation. The proper-power part of $D-D_\nu$ needs no progression estimate. Since $\psi(x)-\vartheta(x)\le4.002\sqrt{x}$ for $x\ge1$, each crossing of a proper prime power costs in total at most $1.5\cdot4.002\sqrt y\,M_2(2)$. For $x<1$ such a sum is empty. [Rosser and Schoenfeld, Theorem 6, (5.3), p. 265](https://www.ams.org/journals/mcom/1975-29-129/S0025-5718-1975-0457373-7/S0025-5718-1975-0457373-7.pdf#page=23)

## Removing the actual proper powers

In the middle range, partial summation against decreasing $K$ transfers $\psi(x)-\vartheta(x)\le1.001102\sqrt x+3x^{1/3}$ to
$$
 |D(y)-Q_\chi(y)|\le1.001102\,I_{1/2}\sqrt y+3 I_{1/3}y^{1/3},\qquad
 I_b=b\int_0^1 K(u)u^{b-1}du=\frac{\int_1^2 v^{-b}\,dv}{1+b}.
$$
At $y\ge10^{24}$ the true square coefficient is the nonprincipal quadratic character $\chi^2$. Put $X_0=8\cdot10^9$. Above $X_0$ the four progression main terms cancel, leaving $|\sum_{p\le t}\chi^2(p)\log p|\le t/(40\log X_0)$. Below $X_0$ the absolute bound is $1.001102X_0$. Integrating the decreasing weight $K(p^2/y)$ yields a square contribution at most $1.001102X_0+\sqrt y/(40\log X_0)$. Each prime capable of a higher power is at most $y^{1/3}$ and all its exponents cost together at most $\log y$. Thus the full proper-power contribution in this range divided by $\sqrt y$ is less than $0.014632$. [Bennett, Martin, O'Bryant and Rechnitzer, *Explicit bounds for primes in arithmetic progressions*, Theorem 1.2, p. 431](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5) · [Rosser and Schoenfeld, Theorem 6, (5.1) and (5.3)](https://www.ams.org/journals/mcom/1975-29-129/S0025-5718-1975-0457373-7/S0025-5718-1975-0457373-7.pdf#page=23)

## Arithmetic checks

The [certificate](quartic_bound.py) proves bounds for whole real intervals by monotone majorants. It gives $0.932162$ on $10^6\le y\le10^{24}$, $0.427042$ on $10^{24}\le y\le10^{38}$ and $0.950824$ on $10^{24}\le y\le10^{39}$. It also recalculates $B$ and the two complex affine bounds using interval Taylor series of the quartic $L$-function at 1 and 2.

For $1\le j\le10^6$ an Eratosthenes sieve takes integer floors of $2^{80}\log p$ and $2^{80}\log(p)/p$. Write $A,B,C$ for the three signed prefixes of $\log p,p\log p,\log(p)/p$, respectively, using the two actual real and imaginary coefficients. For $m=\lfloor j/2\rfloor$,
$$
 2j Q_\chi(j)=j^2(C_j-C_m)-2jA_j+4jA_m+B_j-4B_m.
$$
The errors from the integer logarithmic floors sum to less than $j^3+6j^2$ in each coordinate of the numerator multiplied by $2^{80}$. Comparison of squared integers proves $|Q_\chi(j)|/\sqrt j<0.169460$ for every such $j$. The largest upper enclosure occurs at $j=25$. To reproduce the two Arb runs, execute `uv run --no-project --with python-flint==0.9.0 python quartic_bound.py --bits 128` in this directory and repeat with `--bits 192`. [128-bit output](quartic-bound-128.json) · [192-bit output](quartic-bound-192.json)

For the cumulative extension, let $Y_1=10^{24}$, $Y_2=10^{39}$ and $J_* =5\cdot10^{39}$. The preceding high-range ledger gives $|Q_\chi(j)|\le a\sqrt j+bj$ for $Y_1\le j\le J_*$, where the $17M_1(1)$ term in $a$ uses $\log J_*$ and
$b=3S_3[(1+c)e^{v(1-H^2)/2}+ce^{v(1-H^2)}]+(\delta^3J_3+3M_4(2))/3$. The exact $a,b$ are evaluated in the certificate. Concavity gives $\sum_{j\le J}\sqrt j\le (2/3)J^{3/2}+\sqrt J/2$. For $Y_2\le J\le J_*$ the normalized full prefix is bounded by
$$
 .933(Y_1/Y_2)^{3/2}+a(2/3+1/(2Y_2))
        +(b/2)\sqrt{J_*}(1+1/Y_2)<.982.
$$
The earlier prefixes follow from the pointwise estimates.
