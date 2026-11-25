# Small variances of the actual quartic terminal prime statistic

Let $H=20{,}000{,}000,\ V=25/H^2$, and use the compensated law
$\nu_{\sqrt v}=(1+c)N(0,v)-cN(0,2v)$, $c=e^{-v/2}$. Write $q_v(x)=\Re\int Q(xe^h)d\nu_{\sqrt v}(h)$, indexing by **variance** here. For either sign, either terminal weight from the dossier, or any measurable $0\le g(v)\le1$, put
$$
 S(x)=\int_0^V g(v)[\pm q_v(x)]_+\,dv.
$$
For $1\le x\le10^{24}$, $S(x)<4.51\cdot10^{-14}\sqrt x$. On each ray in the table,
$$
       S(x)<4.42\cdot10^{-15}\sqrt x+B x .
$$

| Lower endpoint | $B$ | Anchor width $H\sigma$ | Log-bin size $\Delta$ |
|---:|---:|---:|---:|
| $10^{24}$ | $3.32\cdot10^{-34}$ | 5.20 | $\sigma/600$ |
| $10^{36}$ | $2.63\cdot10^{-34}$ | 5.20 | $\sigma/1200$ |
| $10^{48}$ | $2.32\cdot10^{-34}$ | 5.17 | $\sigma/1500$ |
| $10^{60}$ | $2.13\cdot10^{-34}$ | 5.13 | $\sigma/1500$ |
| $10^{66}$ | $2.06\cdot10^{-34}$ | 5.11 | $\sigma/1500$ |

Omitting Kadiri's zero-free region gives $B=3.56\cdot10^{-34}$ for all $x\ge10^{24}$, with $H\sigma=5.29,\ \Delta=\sigma/600$. The proof uses the signs of the real prime coefficients in classes 1 and 4 modulo five. The unsigned complex-norm problem has different prime-class constants.

## The older raw estimate under a small Gaussian shift

The historical proof at its fixed smoothing width $2.9\cdot10^{-7}$ yields, for every real $y\ge10^{24}$,
$$
 |Q(y)|\le(.184+.000014\log y)\sqrt y+2.43\cdot10^{-20}y.
$$
The published upper horizon enters the numerical maximum of an increasing expression. Its pointwise argument leaves $\log y$ and $y$ explicit and applies above that horizon. The separate constant, log and linear coefficients before rounding are $0.183645805,0.000013804,2.422425\cdot10^{-20}$ as upper bounds. [Historical raw annular calculation and certificate](https://github.com/willzh0/riemann-masullo/blob/842ce30ef40dfa1e2a9138d37ebb1960d37b9315/research/5571/quartic-annular-bound/FINITE-QUARTIC.md).

For $1\le y\le10^{24}$, the global real bound in the quartic height calculation gives $|\Re Q(y)|<.633\sqrt y$. The sum vanishes below one. Thus the two estimates combine at every positive $y$ with $.633+.000014\log_+ y$ in the square-root term. At $x\ge1$, $\log_+(xe^h)\le\log x+h_+$. For $\delta\le10^{-6}$, the existing total-variation bounds give $\int e^{h/2}d|\nu_\delta|,\int e^h d|\nu_\delta|<1.14$ and $\int |h|e^{h/2}d|\nu_\delta|<2.8\delta$. This directly gives
$$
 S(x)\le V\{[1.14(.633+.000014\log x)+.000014(2.8\sqrt V)]\sqrt x
                      +1.14(2.43\cdot10^{-20})x\}.
$$
The resulting linear coefficient is less than $1.732\cdot10^{-33}$. For the stronger bound on $x\le10^{24}$, apply the separate global inequality $|\Re Q(y)|\le(5/8)\sqrt y+y\log H/(6H^2)$ for every $y>0$ before taking the two Gaussian moments. This does not assume that a shifted input stays below $10^{24}$. [Pointwise real bound](../QUARTIC_LINEAR_HEIGHT.md) · [Compensated total-variation moments](../README.md).

## Exact ordering of the two-knot defects

Let $F(r)=(2\cosh r-2){\bf1}_{r>0}$, $D_v=\nu_{\sqrt v}*F-F$. The reproduced exponentials imply $D_v(-r)=-D_v(r)$. For $r>0$, let
$$
 A_t=\mathbb E F(X_t-r),\quad P_t=\Pr(X_t>r),\qquad X_t\sim N(0,t).
$$
Since $F''=F+2{\bf1}_{(0,\infty)}$ distributionally, $A'_t=A_t/2+P_t,\ A_0=0$. The Gaussian is even, hence $D_v(r)=cA_{2v}-(1+c)A_v$. Differentiation gives
$$
 \partial_vD_v(r)=\tfrac12(cA_{2v}-A_v)+2cP_{2v}-(1+c)P_v.
$$
Here $cA_{2v}-A_v=e^{v/2}\int_v^{2v}e^{-t/2}P_t\,dt\ge2(1-c)P_v$, because $P_t$ increases for $r>0$. Thus $\partial_vD_v(r)\ge2c(P_{2v}-P_v)\ge0$. This also proves the sign since $D_0=0$. In particular $|D_w-D_v|=|D_w|-|D_v|$ pointwise whenever $w\ge v$.

Write $J(v)=\int_{\mathbb R}|D_v(r)|dr$ and $m_k=\mathbb E|N(0,1)|^k$. Integrating $F$ over the positive half-line gives
$$
 J(v)=2\sum_{j\ge1}
  \frac{m_{2j+1}v^{j+1/2}}{(2j+1)!}
  [\,c\,2^{j+1/2}-(1+c)\,].
$$
All brackets are positive for $0<v\le10^{-12}$. The leading coefficient with $c=1$ is $(2\sqrt2-2)m_3/3=0.44065947505\ldots$. In the positive upper tail after dropping the subtraction, successive terms starting at $j=2$ have ratio at most $2v/7$. It follows that
$$
 .440659\,v^{3/2}\le J(v)\le .440660\,v^{3/2}.
$$
The dossier's variation bound is $\operatorname{Var}|D_v|\le4.1v$ on the same range. [Two-knot identity and variation proof](../README.md).

## An oriented Brun–Titchmarsh estimate at each terminal point

Fix an anchor $w=\sigma^2\ge V$ from the table and compare $q_v(x)$ with $q_w(x)$. The two knots have $(a,c_a)=(2,1),(1,-1/2)$ and coordinates $r=\log(ap/x)$. The constant and exponential parts of $K$ cancel exactly between the two widths. On either log half-line the defect difference has fixed sign. For any prescribed sign in the positive part, at most one residue class, 1 or 4 modulo 5, contributes positively on each side of each knot. Prime five has zero coefficient.

Set $R=100\sigma,\ X=x/a$. Divide each half of $[-R,R]$ into bins of width $\Delta$ as in the table. Each bin $(u,u+\Delta]$ corresponds to a prime interval of length $L=Xe^u(e^\Delta-1)\ge (x/2)e^{-R}\Delta$. On each such interval $\log p\le\log x+R$. The Montgomery–Vaughan inequality for one reduced class is $2L/(\varphi(5)\log(L/5))$, and $L\le Xe^R\Delta$. It gives the upper logarithmic mass $Xe^R C(x)\Delta$, where
$$
 C(x)=\frac{\log x+R}{2[\log x+\log(\Delta/10)-R]}.
$$
The denominator is positive on every stated ray, and $C$ decreases there. The half-open bins cover endpoints once. The central knot has zero weight. [Montgomery–Vaughan, Theorem 2, (1.10)](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf#page=3).

The upper sum of $f=|D_w|-|D_v|$ satisfies $\sum\Delta\sup_I f\le \int_{\mathbb R}f+\Delta\operatorname{Var}f$. Summing the knot weights uses $\sum_a |c_a|/a=1$. On averaging $0\le v\le V$, the resulting coefficient per unit variance, multiplying $x$, is at most
$$
 B_{\rm phys}=e^R C(x)
    \{.440660\,\sigma^3-.440659(2/5)V^{3/2}
                                      +4.1\Delta(w+V/2)\}
                      +10^{-500}\sigma^3 .                         \tag{1}
$$
For the tail $|r|>R$, ordered defects give $f(r)\le|D_w(r)|\le\int_{h>|r|}h^2e^{|h|}d|\nu_\sigma|(h)$. Chebyshev on the primes at each knot bounds both tails together by $4x\int_{h>R}h^2e^{2h}d|\nu_\sigma|$. For each component of standard deviation $s\le\sqrt2\sigma$, Cauchy–Schwarz and $\mathbb E(X_s^4e^{4X_s})=e^{8s^2}(3s^4+96s^6+256s^8)<4s^4$, where $X_s$ in this moment denotes $N(0,s^2)$, bound the total after the factor 4 by $48\sigma^2e^{-1250}$. This is below the tail in (1).

## The smoothed anchor at the selected width

Separate from $Q$ only $R^+(y)=-\sum_{\beta>1/2,\ |\gamma|>H}M(\rho)y^\rho$, with multiplicities and $M(s)=(2^{1-s}-1)/[(1-s)s(1+s)]$. The low-zero calculation bounds $|\Re(Q-R^+)(y)|$ by $(.625+3U_3)\sqrt y$ for all $y>0$, improving to $(.062+3U_3)\sqrt y$ for $y\ge10^{12}$, where $U_3<6.8\cdot10^{-15}$. For $y<1$ use $Q=0$ and $\beta>1/2$ in $R^+$. At $x\ge10^{24}$, $xe^h<10^{12}$ requires $e^{h/2}\le10^{-6}$, so its extra tilted mass is at most $3\cdot10^{-6}$. This proves the square-root term in the table after multiplication by $V$. [Thirteen-zero refinement and right-hand decomposition](../README.md).

For $T\ge H$ write $z=\sigma T,\ k=2+z^2$ and
$$
 D_\sigma(T)=\frac{e^{-z^2/2}}{T^2}
 \left[\frac{\log T/k+1/k^2}{\pi}
                  +\frac{.55}{T}\{2\log T+1/(k+1)\}\right].
$$
This bounds $\sum_{|\gamma|>T}|\gamma|^{-3}e^{-\sigma^2\gamma^2/2}$ for the full quartic divisor. Indeed $u^2\ge1+2\log u$ for $u\ge1$. Apply the dossier's $U_m(T)$ with $m=3+z^2$. The right divisor has at most half this mass by the same-ordinate functional equation. Its true Gaussian multiplier has modulus bounded by $A e^{-\sigma^2\gamma^2/2}$, where $A=2e^{w/2}+e^w e^{-wH^2/2}$.

Since $(1+2^{1-\beta})x^\beta$ increases with $\beta$ for $x\ge2$, the coarse high contribution to the anchor is at most $x A D_\sigma(H)$. Alternatively use $\beta\le1-d$ up to $3H/2$, where $d=1/[5.60\log(7.5H)]$. The anchor high coefficient becomes
$$
 B_{\rm high}=A\{(1+2^d)x^{-d}D_\sigma(H)/2
                                      +D_\sigma(3H/2)\}.
$$
Evaluate the decreasing factors at the lower endpoints of the rays. Then $B=V(B_{\rm phys}+B_{\rm high})$ proves the table. [Zero-count ledger](../CUMULATIVE.md) · [Kadiri, Theorem 1.1](https://www.cs.uleth.ca/~kadiri/articles/explicit_zerofree_regions_for_dirichlet_l_functions.pdf).

The table uses the full prime row. For $x\ge2$, either of the dossier's finite cutoffs gives an additional error below $10^{-1000}V$ on this narrow variance interval. Put $L=\log(N/x)$. For the square and near-linear prescriptions $L\ge\log2$ and $L^2\ge(\log2)\log x$. A prime beyond $N$ requires $h>L$. The simple bound $\sum_p(\log p)K(p/t)\le(\log2)^2t$ and Gaussian exponential tilting give a per-variance loss at most $3(\log2)^2e^V x\exp[-L^2/(16V)]$, since $L-2V\ge L/2$. This is below $10^{-1000}$ throughout.

The improvement here is in the explicit coefficient. For two distinct fixed values of $H\sigma$, the exact kink mass scales as $H^{-3}$, and a fixed interval of $H^2v$ has length proportional to $H^{-2}$. Taking the absolute physical prime crossings therefore retains an $H^{-5}$ term. A stronger order would require further signed prime cancellation or extra information on the high zeros.

Run `uv run verify_terminal_bound.py` to reproduce the small-variance and combined bounds at 128 and 192 bits. The final subrange in the combined estimate uses the same formulas with the split and anchor shown in the [main proof](README.md).
