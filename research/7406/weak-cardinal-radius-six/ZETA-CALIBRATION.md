# Radius-six weak Sobolev cardinals at Riemann zeta zeros

At $\alpha=0$, $a=1/2$, $s=3$ and $\theta=3/2$, the first 128 positive zero ordinates give $1.54749<W_E\le 2\pi/3$. Each member of the classical close pair near height 7005 gives $W_E>21$ using all 14 true local ordinates. These are finite calibrations for Theorem 10.4.3.5(2), p. 472. The uniform geometric block estimate remains open. [Issue #7406](https://github.com/mccorvie/riemann-masullo/issues/7406) · [Lehmer, 1956, pp. 297–298](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5833-11511_2006_Article_BF02401102.pdf#page=7)

| Centers | Minimum $W_E$ (index) | Maximum $W_E$ (index) | Minimum $\Delta_E$ (index) | Maximum $\Delta_E$ (index) |
|---|---:|---:|---:|---:|
| 1–32 | 1.71220934984 (32) | $2\pi/3$ (1) | 2.72538381412 (27) | $\pi$ (1) |
| 1–128 | 1.54749803572 (118) | $2\pi/3$ (1) | 2.43077835912 (114) | $\pi$ (1) |

| Close-pair center | Indices in $E$ | $W_E$ | $\Delta_E$ |
|---|---:|---:|---:|
| 6709 | 6703–6716 | 21.45656003424 | 29.93037947570 |
| 6710 | 6703–6716 | 23.25152957789 | 32.41294721857 |

The tables round the displayed values. The receipts enclose each result separately and certify the indices attaining each prefix extremum. [128-bit intervals](weak-cardinals-128.json) · [192-bit intervals](weak-cardinals-192.json)

## Certifying the nodes

Let $N(T)$ count all nontrivial zeros with $0<\Im\rho\le T$, including multiplicities. The verifier evaluates $N(0)=0$, $N(300)=138$, $N(6998)=6701$, and $N(7012)=6716$ using Arb. It isolates zeros 1–139 and 6701–6717 with exact real part $1/2$ and disjoint, strictly increasing ordinate balls. The counts and guard enclosures prove that the zeros in both working windows are exhaustive and simple. Every closed radius-six neighborhood fits strictly inside its working window. The lower guard at zero excludes negative ordinates for the first center as well. [Historical Arb documentation for indexed isolation and total counts](https://arblib.org/acb_dirichlet.html#riemann-zeta-function-zeros) · [FLINT 3.3.1 implementation](https://github.com/flintlib/flint/blob/v3.3.1/src/acb_dirichlet/zeta_zeros.c)

Every center-to-node interval distance is strictly below or strictly above 6. Of the 17,664 comparisons for the prefix, indices 77 and 80 come closest, with distance $6-0.000644735825446588\ldots$. The close-pair window contributes 30 further strict comparisons. Its two centers are $0.037698497726140188\ldots$ apart. For each of the 130 centers $w$, the verifier also evaluates $N(w-6)$ and $N(w+6)$ directly and compares both counts with the indices found by interval distances.

## Fourier normalization and certified linear algebra

For $b>0$, use $G_{b,r}(d)=(2\pi)^{-1}\int_{\mathbb R}e^{id\xi}(b+\xi^2)^{-r}\,d\xi$. Inserting the gamma integral for the negative power gives

$$
G_{b,r}(d)=\frac{1}{2\sqrt{\pi}\,\Gamma(r)}
 \int_0^\infty t^{r-3/2}\exp\!\left(-bt-\frac{d^2}{4t}\right)dt .
$$

The modified Bessel integral gives the following entries for $d>0$. The gamma integral at $d=0$ gives the diagonals directly. [NIST DLMF 10.32.10](https://dlmf.nist.gov/10.32.E10)

$$
\begin{aligned}
 G_{b,3/2}(d)&=\frac{d}{\pi\sqrt b}K_1(\sqrt b\,d),
 &G_{b,3/2}(0)&=\frac{1}{\pi b},\\
 G_{b,5/2}(d)&=\frac{d^2}{3\pi b}K_2(\sqrt b\,d),
 &G_{b,5/2}(0)&=\frac{2}{3\pi b^2}.
\end{aligned}
$$

With $G_{b,r}$ denoting the matrix on the actual neighborhood $E$, take $c=G_{1,3/2}^{-1}e_w$. The cardinal has Fourier transform $(1+\xi^2)^{-3/2}\sum_{u\in E}c_u e^{-iu\xi}$. Its squared $H^{1/2}$ norm and the difference of the diagonal inverse entries are

$$
 W_E=c^\mathsf{T}G_{1,5/2}c,\qquad
 \Delta_E=(G_{2,3/2}^{-1})_{ww}-(G_{1,3/2}^{-1})_{ww}.
$$

Each Gram matrix is positive definite because its quadratic form integrates the squared modulus of a finite exponential sum against a strictly positive Fourier density. The verifier checks strict positivity of every pivot of an interval $LDL^\mathsf{T}$ factorization of all three matrices. It solves the two systems by Arb ball arithmetic and checks both cardinal residuals. For $E=\{\gamma_1\}$, the scalar entries give $c=\pi$, $W_E=2\pi/3$ and $\Delta_E=\pi$ exactly. [Arb certified matrix operations](https://arblib.org/arb_mat.html)

## Replay

The script pins python-flint 0.8.0 from August 2025. Its published wheels bundle FLINT 3.3.1. The two runs calculate the zero enclosures, all Gram entries and all solves afresh. The comparison checks that every 192-bit recorded ordinate and quadratic ball lies inside its 128-bit counterpart. [August 2025 release](https://pypi.org/project/python-flint/0.8.0/) · [Portable verifier](check_cardinals.py)

~~~sh
uv run check_cardinals.py --bits 128
uv run check_cardinals.py --bits 192
uv run check_cardinals.py --compare weak-cardinals-128.json weak-cardinals-192.json
~~~
