# Absolute exterior sums in two cyclotomic towers

Let \(f\) be exactly the compact real radial function of the pinned rational calculation. Its bilateral Laplace transform \(R\) satisfies \(R(1/4)=1\), \(R(0)=R(\pm1/2)=0\), and \(R(z)\ne0\) whenever \(0<|\Re z|<1/2\). Its log support is in \([1/2,11/2]\). All estimates below use that same \(f\), including its translation, its 172 extra boxes of radius \(3/344\), and its real normalization. [Pinned definition and sources](https://github.com/willzh0/riemann-masullo/blob/d095ce533f7116c119464461d00a4f3b2641e759/research/5571/dirichlet-slab-exterior/README.md)

## Exact identity for each selected Hecke character

For an odd prime \(p\), put \(E=\mathbb Q(\zeta_p)\), \(G=\operatorname{Gal}(E/\mathbb Q)\), and let \(H=\operatorname{Gal}(E/K)\) for any intermediate field \(K\). For a character \(\psi\) of \(H\), denote by \(A_{K,\psi}(\alpha)\) the sum of \(m_\rho|R(\rho-1/2)|\) over all its nontrivial zeros satisfying \(|\Re\rho-1/2|\ge\alpha>0\). Both boundary lines are included. These are the actual absolute exterior terms of #5571 for a compact idèle-class test. With \(V_K\) the Tamagawa volume of its norm-one group and \(\psi\) pulled back by reciprocity, use \(V_K^{-1}\overline{\psi(g)}f(\log|g|_K)\), with the character inverted as necessary for the project's convention. A selected angular row contributes \(R\); orthogonality kills all the others. The packet test for a subset is the sum of its character tests. Each finite-order character is trivial on a continuous positive norm section, by connectedness. If the restrictions to the norm-one classes of two section-normalized characters agree, their quotient is also trivial on the section, so the full characters agree. This proves the same selection for every norm section. The radial support excludes the norm-one classes.

Each \(\psi\in\widehat H\) extends to exactly \(d=[K:\mathbb Q]\) characters of the cyclic group \(G\). Frobenius reciprocity decomposes \(\operatorname{Ind}_H^G\psi\) as the direct sum of these characters, each once. Induction and direct sums for Artin \(L\)-functions, and the Artin–Hecke identification for one-dimensional characters, give
\[
 L_K(s,\psi)=\prod_{\chi\in\widehat G:\ \chi|_H=\psi}L_\mathbb Q(s,\chi^*).
\]
The trivial rational factor here is \(\zeta(s)\) with its Euler factor at \(p\). Every nontrivial rational factor is primitive at \(p\). These statements include ramified places. At sites of the open critical strip all the factors are holomorphic; gamma and conductor factors are holomorphic and nonvanishing there. Thus the completed zero orders add, even when several factors vanish at the same site. Each positive order gets the same real weight from the test. Consequently
\[
 A_{K,\psi}(\alpha)=\sum_{\chi|_H=\psi} A_{\mathbb Q,\chi}(\alpha),
 \qquad
 \sum_{\psi\in\widehat H} A_{K,\psi}(\alpha)
   = A_{E,1}(\alpha)
   = A_{\mathbb Q,1}(\alpha)+\sum_{\chi\bmod p,\ \chi\ne1}A_{\mathbb Q,\chi}(\alpha).
\]
Taking inverse characters permutes the packet; the rowwise identity pairs inverses on both sides if that convention is used. The equalities are for full multiplicities and the specified finite-order characters of \(K\). [Knapp, §5, pp. 264–266, properties (1) and (3) and Theorem 5.1](https://math.stanford.edu/~conrad/JLseminar/refs/Knappintro.pdf) · [Sutherland, Theorem 19.15](https://math.mit.edu/classes/18.785/2016fa/LectureNotes19.pdf#page=10)

## The degree-399,988 field

The largest prime through \(400{,}000\) is \(399{,}989\). Its group order is \(399{,}988=2^2 19^2 277\), giving 18 intermediate fields including \(\mathbb Q\) and \(E\). This is the maximum full cyclotomic degree among single moduli \(q\le400{,}000\). For a composite \(q\), its smallest prime divisor is at most \(\sqrt q\), so \(\varphi(q)\le q-\sqrt q\le400{,}000-\sqrt{400{,}000}\). The real subfield has degree \(199{,}994\) and supplies two rows. The quadratic subfield is \(\mathbb Q(\sqrt {399989})\), since \(p\equiv1\bmod4\), and supplies \(199{,}994\) rows.

Write \(T_k(q,H)\) for the two-sided Stieltjes upper bound in the pinned file. At \(p=399{,}989\), the verified height is \(H_p=200+37{,}500{,}000/p=293.752578195900\ldots\). The \(\zeta\) height is \(H_\zeta=3{,}000{,}175{,}332{,}800\). The sum of inverse-cube tails for all relevant factors is bounded by
\[
(p-2)T_3(p,H_p)+T_3(1,H_\zeta)<13.009372884438.
\]
The earlier single-sidelobe calculation at \(H_p\) already implies a complete packet bound \(8.519931413\cdot10^{-109}\). The following interval calculation improves this to **\(5.190169594\cdot10^{-113}\)**. For the quadratic subfield the principal row is bounded by \(1.297584570\cdot10^{-118}\), and each remaining selected row by \(2.595169140\cdot10^{-118}\). Only the principal row includes the rational \(\zeta\) factor. [Height, counting theorem and Stieltjes estimate](https://github.com/willzh0/riemann-masullo/blob/d095ce533f7116c119464461d00a4f3b2641e759/research/5571/dirichlet-slab-exterior/GREEN-AND-TAILS.md)

Here is a finite covering proof for the complex strip estimate in this calculation. Set \(r_n=1/[n(n+1)]\), \(a=3/344\), and \(B_r(z)=\sinh(rz)/(rz)\). For a cell \([l,l+\Delta]\) of positive ordinates and \(|\Re z|\le1/2\), put
\[
 U_r=\sqrt{\sinh^2(r/2)+
 \min\{1,\ |\sin(r(l+\Delta/2))|+r\Delta/2\}^2}.
\]
The sine is one-Lipschitz, \(|\sinh(x+iy)|^2=\sinh^2 x+\sin^2 y\), and \(|z|\ge|\Im z|\). Hence \(|B_r(z)|\le U_r/(r|\Im z|)\). Symmetry of the underlying interval probability also gives \(|B_r(z)|\le\cosh(r/2)\). These estimates cover both signs of the ordinate. Let
\[
 D(l)=\frac{64e^{3/4}}3
       \sqrt{1+\frac1{4l^2}}\left(1+\frac1{2l^2}\right).
\]
The factor \(e^{3/4}\) includes the upper translation factor \(e^{3/2}\) divided by the lower normalization \(3e^{3/4}/64\), with the rational coefficient displayed separately. On each cell we obtain
\[
 |R(z)|\,|\Im z|^3\le D(l)\cosh(1/66)
 \left(\frac{U_a}{al}\right)^{172}
 \prod_{n=1}^6\frac{U_{r_n}}{r_n}
 \prod_{n=7}^{32}\min\left(\cosh(r_n/2),\frac{U_{r_n}}{r_n l}\right).
\]
The six inverse powers handle the cubic polynomial and the desired inverse-cube tail. The remaining original boxes have symmetric law supported in \([-1/33,1/33]\). All \(9{,}700\) closed cells of width \(1/16\) from \(293.75\) through \(900\) are evaluated with outward-rounded interval arithmetic. Their maximum is below \(3.989561711\cdot10^{-114}\). On \(|\Im z|\ge900\) put \(U_r=\cosh(r/2)\), use the first 16 original factors and \(l=900\), and bound the remaining symmetric tail by \(\cosh(1/34)\). This part is below \(1.242\cdot10^{-154}\). These two overlapping bounds give the claimed complete normalized packet estimate. Applied to the full rational family's pinned grouped inverse-cube bound \(564612.009428476\), the same calculation gives \(2.252554455\cdot10^{-108}\).

## The quartic field and a measured nonprincipal row

For \(p=5\), \(E=\mathbb Q(\zeta_5)\) and the nontrivial proper intermediate field is \(K=\mathbb Q(\sqrt5)\). Each of the three nonprincipal rational factors is verified through \(H=20{,}000{,}000\). Keeping the six inverse powers from the first six factors of \(G\), take \(\cosh(r_n/2)/(r_nH)\) for \(7\le n\le4471\), and \(\cosh(1/8944)\) for the remaining symmetric probability. Here \(4471\cdot4472\le H<4472\cdot4473\). Each of the extra boxes satisfies \(|B_a(z)|\le\cosh(a/2)/(aH)<5.733387840\cdot10^{-6}\). The whole inverse-cube sum is bounded by \(3T_3(5,H)+T_3(1,H_\zeta)<2.0391101650\cdot10^{-14}\). This gives, for all positive widths,
\[
 A_{E,1}(\alpha)<7.656587073\cdot10^{-4747}.
\]
For the two rows over \(K\) the separate bounds are \(2.552195691\cdot10^{-4747}\) (principal) and \(5.104391382\cdot10^{-4747}\) (nonprincipal). The latter row has \(L_K(s,\psi)=L(s,\chi)L(s,\overline\chi)\) for the quartic \(\chi(2)=i\). The principal \(K\)-row is \(\zeta(s)L(s,\chi^2)\).

Let \(P(t)=(3/2)/[\pi((3/2)^2+t^2)]\). By the pinned Poisson–Jensen identity the integral of \(P(t)\log|\zeta_E(1/2+it)|\) is \(\log(\zeta(2)L(2,\chi^2)|L(2,\chi)|^2/2)+G_E(0)\). Absolute integrability permits the finite addition across factors. The total Green mass satisfies
\[
 0\le G_E(0)\le\tfrac34\bigl(3T_2(5,H)+T_2(1,H_\zeta)\bigr)
 <6.296400984\cdot10^{-7}.
\]
The resulting interval for the physical Poisson integral is
\((-0.604816151440950,-0.604815521800850)\). For the nonprincipal character of \(\operatorname{Gal}(E/K)\) the corresponding interval is
\((-0.061528625085190,-0.061528205326603)\). It is obtained from \(2\log|L(2,\chi)|\) and a Green mass bounded above by \(4.197585860\cdot10^{-7}\). These interval conclusions use the finite-height estimates for possible exterior zeros; the exact masses may vanish. [Poisson integral and Green identity](https://github.com/willzh0/riemann-masullo/blob/d095ce533f7116c119464461d00a4f3b2641e759/research/5571/dirichlet-slab-exterior/GREEN-AND-TAILS.md) · [Earlier single quartic row](https://github.com/willzh0/riemann-masullo/tree/da8d5a8b3252c16120606b0b513d445e88cfbd0f/research/5571/quartic-green-calibration)

Run the verifier with Python and python-flint 0.9.0 at each of the two supplied precisions. The inequalities are classical and the numerical enclosures use Arb. The project’s exact cofinal cancellation remains open. [Verifier](check_cyclotomic.py) · [128-bit receipt](cyclotomic-128.json) · [192-bit receipt](cyclotomic-192.json)

A second verifier uses the interval sine of each complete ordinate cell directly. It bounds the same normalized radial coefficient on the original 9,700 cells. [Independent verifier](interval_mesh_check.py) · [128-bit run](sine-128.txt) · [192-bit run](sine-192.txt)
