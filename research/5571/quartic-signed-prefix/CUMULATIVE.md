# A cumulative estimate for the high quartic zero terms

Let $Q_\chi(x)$, $E_\pm(J)=\sum_{j\le J}[\pm\Re Q_\chi(j)]_+$ and $M(s)=(2^{1-s}-1)/[(1-s)s(s+1)]$ be the actual quartic prime observable and its Mellin kernel. For all integer $1\le J\le10^{36}$ the unchanged signed prefixes satisfy
$$
 E_\pm(J)<0.904\,J^{3/2}.
$$
They satisfy $E_\pm(J)<J^{3/2}$ through $1.24\cdot10^{36}$, using the global positive quartic zero sum and the companion quadratic formula in the [pointwise ledger](QUARTIC_LINEAR_HEIGHT.md). With the independently certified 13 low quartic zeros, the bound improves to $0.824J^{3/2}$ through $10^{36}$ and $0.997J^{3/2}$ through $1.5\cdot10^{36}$. All these estimates use Platt’s finite height $H=20,000,000$. The cofinal $J^{3/2+o(1)}$ upper remains open. [Platt, published Theorem 10.1, p. 3026](https://www.ams.org/journals/mcom/2016-85-302/S0025-5718-2016-03077-X/S0025-5718-2016-03077-X.pdf#page=18)

The cubic Mellin kernel gives a pointwise high-tail loss $O(x\log H/H^2)$. In the cumulative one-sided problem the following argument replaces it by $O(J^2\log H/H^{5/2})$ before using a historical zero-free region. It uses neither a smoothed arithmetic observable nor a spacing or simplicity assumption on the zeros.

## Zero counts and a local bound

Write $N(t)$ for the number of zeros of the chosen quartic with absolute ordinate at most $t$, counting multiplicities. For $t\ge H$ the theorem of Bennett, Martin, O’Bryant and Rechnitzer gives
$$
 N(t)=F(t)+e(t),\quad F(t)=\frac t\pi\log\frac{5t}{2\pi e}+\frac14,\qquad
 |e(t)|\le\eta\log t,\quad \eta=0.55 .
$$
Indeed their bound is $0.22737\ell+2\log(1+\ell)-1/2$, $\ell=\log(5(t+2)/(2\pi))<\log t$. Replacing $\ell$ by $\log t$, the ratio to $\log t$ decreases on this interval and at $H$ is below $0.541$. [Bennett et al., Theorem 1.1](https://arxiv.org/pdf/2005.02989#page=2)

Let $\mathcal Z^+$ consist of the zeros $\rho=\beta+i\gamma$ with $\beta>1/2,\ |\gamma|>H$, counted with multiplicity. The functional equation pairs each right zero with a left zero at the same signed ordinate, in the same character. For $t=|\gamma|>H$, the number of $\rho'\in\mathcal Z^+$ with $|\gamma'-\gamma|\le v$ is therefore at most
$$
        (v/\pi+\eta)\log(t+v).
$$
To verify this, the absolute ordinates lie in $[\max(H,t-v),t+v]$. Take the difference of the endpoint counts using the left limit for a closed endpoint, apply $|F'(u)|\le\log(t+v)/\pi$, and take half. The cutoff boundary has no right-hand zeros. This handles correlations as well as multiplicities.

Integrate this bound against $2v(2+v^2)^{-2}\,dv$ to obtain
$$
 \sum_{\rho'\in\mathcal Z^+}\frac1{2+(\gamma-\gamma')^2}
 \le c_0\log t,\qquad c_0=0.6287 .
$$
The constant from the $\log t$ term before rounding is $1/(2\sqrt2)+\eta/2$. For the remaining $\log(1+v/t)$ use $\log(1+v/t)\le\sqrt{v/t}$. The integral of $2v^{3/2}(v/\pi+\eta)/(2+v^2)^2$ is below 6 by splitting at one. The ledger checks $1/(2\sqrt2)+\eta/2+6/(\sqrt H\log H)<c_0$.

With $\mathcal Z$ counting all zeros, Stieltjes integration gives for $T\ge H,\ L=\log T$,
$$
 \sum_{\mathcal Z:\,|\gamma|>T}\frac{\log|\gamma|}{|\gamma|^6}
 \le S(T):=0.0652\frac{L^2}{T^5}.
$$
For $f(t)=t^{-6}\log t$, the $dF$ part costs at most $[L^2+2L/5+2/25]/(5\pi T^5)$. The endpoint term and $\int |f'|\,|e|$ cost at most $\eta[2L^2+L/3+1/18]/T^6$. The ratio to $L^2/T^5$ decreases and is below 0.065195 at $H$. Similarly the moments of the whole high tail at $H$ satisfy
$$
 U_m=\frac{\log H/(m-1)+(m-1)^{-2}}{\pi H^{m-1}}+
       \frac{\eta(2\log H+1/m)}{H^m}
 \ \ge\ \sum_{|\gamma|>H}|\gamma|^{-m},\qquad m=2,3,4.
$$

## Continuous mean square and signed mean

Write $R^+(x)=-\sum_{\rho\in\mathcal Z^+}M(\rho)x^\rho$. The other high zeros contribute at most $3U_3\sqrt x$ for $x\ge1$. Take $J\ge2$ and
$b_\rho=J^\beta|M(\rho)|$. Consider $R^+(Je^u)$ with weight $w(u)=1$ on $u\le0$ and $w(u)=e^{-3u}$ on $u>0$. Both sides are integrable after squaring. The Gram kernel for two terms with $a=\beta+\beta'\in[1,2]$, $d=\gamma-\gamma'$, is
$$
 \frac{1}{a+id}+\frac{1}{3-a-id}
       =\frac3{(a+id)(3-a-id)} .
$$
Its modulus is at most $3/(2+d^2)$, since $a(3-a)\ge2$ and the modulus of the denominator is at least $a(3-a)+d^2$. The local count and $2b_\rho b_{\rho'}\le b_\rho^2+b_{\rho'}^2$ give
$$
 \int_\mathbb R w(u)|R^+(Je^u)|^2du
       \le3c_0\sum_{\rho\in\mathcal Z^+} b_\rho^2\log|\gamma| .
$$
Finite truncations followed by dominated convergence justify the expansion because on each half-line the absolute sums have an integrable square majorant since $\tfrac12<\beta<1$.

For $H<|\gamma|\le3H$, Kadiri’s unconditional region for conductor five gives $\beta\le1-d_0,\ d_0=(5.60\log(15H))^{-1}$. Since $J^\beta(1+2^{1-\beta})=J^\beta+2(J/2)^\beta$ is increasing, $b_\rho\le(1+2^{d_0})J^{1-d_0}/|\gamma|^3$ there. At all heights $b_\rho\le2J/|\gamma|^3$. Each right-hand measure is bounded by half the total at its absolute ordinates. Therefore the normalized contribution of half the continuous modulus to the signed prefix is bounded by
$$
 B(J)=\frac14\sqrt{3c_0\big[(1+2^{d_0})^2J^{1-2d_0}S(H)+4JS(3H)\big]} .
$$
Indeed $\int_0^J|R^+(x)|\,dx\le J(\int_{-\infty}^0e^{2u}du)^{1/2}\|R^+(Je^\cdot)\|_{L^2(w\,du)}$, and the first integral of the square weight equals $1/2$. The unsplit elementary version replaces the bracket by $4JS(H)$. [Kadiri, Theorem 1.1](https://www.cs.uleth.ca/~kadiri/articles/explicit_zerofree_regions_for_dirichlet_l_functions.pdf#page=1)

The integrated complex signed mean has absolute value at most $J^2U_4$, by integrating $x^\rho$ explicitly, using $|1+\rho|\ge|\gamma|$, and again taking half the counting measure. Thus either actual sign, via $2[f]_\pm=|f|\pm f$, incurs only $\sqrt J\,U_4/2$ in addition to $B(J)$ after normalization. On $x\ge1$, termwise differentiation gives $|(R^+)'(x)|\le(3/2) U_2$, and $|R^+(1)|\le(3/2)U_3$. The positive part of either real projection is 1-Lipschitz. Comparing cell by cell with its integral and adding the $j=1$ endpoint costs at most $(3/2)(JU_2+U_3)$. These steps hold for zeros at either sign of the ordinate.

## Arithmetic remainder and numerator

In the full primary quartic tail $R_H(x)$ include all zeros of this character with $|\gamma|>H$, at the original ordinates. For the genuine prime sum the independent quadratic-subtraction calculation gives $|\Re(Q_\chi-R_H)|\le(5/8)\sqrt x$ for all $x\ge1$, improving to $0.181\sqrt x$ for $x\ge10^{12}$. It subtracts every even prime power using the primitive quadratic character modulo five and bounds the remaining odd powers in the true real residue classes. Its three separate finite-height certificates use both original mod-five characters and both signs. The count treats positive and negative ordinates separately. The independent low-zero replay tightens the low primary coefficient from $0.16836$ to $0.049502$ and the large-$x$ coefficient to 0.062. [Pointwise proof and replay](QUARTIC_LINEAR_HEIGHT.md)

For $2\le J\le10^{20}$ the global $5/8$ coefficient, $B(10^{20})$, the signed and sampling allowances, and the left/critical $3U_3$ contribution total less than 0.626 after normalization. At $J=1$ the actual sample is zero. For $J\ge10^{20}$, if $T=10^{12}$ and $c=0.181$ or $0.062$, the normalized nonprimary remainder is bounded by
$$
 c(2/3+1/J)+(5/8-c)(T/J)^{3/2}
$$
since $\sum_{j\le J}\sqrt j\le(2/3)J^{3/2}+\sqrt J$. Add
$B(J)+3U_3+\sqrt J\,U_4/2+(3/2)(U_2/\sqrt J+U_3/J^{3/2})$. For an interval of integer prefixes bound each monotone term at its appropriate endpoint. At $10^{36}$ the upper ledger gives $0.903274$ using the global primary-zero moment and $0.823940$ using the first thirteen. At $1.24\cdot10^{36}$ the former gives $0.990463$, and at $1.5\cdot10^{36}$ the latter gives $0.996353$. [128/192-bit arithmetic](verify_cumulative.py)

Mlyle’s earlier verified bounds use the triangular statistic $S_\chi(j^4)$, through $2.5$ million signed prefixes and $8$ million complex prefixes. The BMOR Appendix A.3 finite progression bounds imply $\sum_{j\le J}|\Re Q_\chi(j)|<0.675135J^{3/2}$ through $4\cdot10^{13}$. Indeed the two relevant signed progression components are bounded by $1.824960\sqrt x$. The square correction is common to residues 1 and 4. Partial summation multiplies this bound by $4(\sqrt2-1)/3$. This earlier-range consequence and the present much larger interval concern the same true $Q_\chi$. [BMOR verified progression bounds](https://personal.math.ubc.ca/~andrewr/pubs/EBPAP.pdf#page=86) · [Mlyle’s triangular calibration](https://github.com/mlyle/riemann-masullo/tree/3f90b6c75f2e36f52c2c9cb427155a556bcee9d8/research/5571/quartic-mod-five-deficit)
