# Exterior sums under abelian base change

For Masullo, Theorem 12.5.1.1, pp. 519–520, the sum of the signed omitted terms has an exact zero on a nonzero, inversion-even test over $\mathbb Q(i)$. That test takes a nonzero sample at every possible off-central zero of every nontrivial unramified angular Hecke character of the Gaussian integers. Cancellation comes from conjugating ideals. The absolute sum for the same test detects precisely whether this entire infinite family has an off-line zero. [Exact Gaussian signed cancellation](GAUSSIAN-SYMMETRY.md)

A second test over $\mathbb Q(i)$ has absolute exterior sum below $9.562\cdot 10^{-113}$ across 2,463,841,722 conjugation-invariant characters jointly. These include every invariant character of actual conductor norm at most $10^{10}$. Its raw Mellin value at $1/4$ is one for each selected row. The arithmetic transfer giving this bound applies to any finite abelian extension of number fields. [Gaussian conductor classification and arithmetic proof](GAUSSIAN-CONDUCTORS.md) · [Cyclic examples and estimates](CYCLOTOMIC.md)

## One physical test for a complete abelian packet

Let $E/K$ be a finite abelian extension of number fields, $D=\operatorname{Gal}(E/K)$, $d=|D|$ and $N:C_E\to C_K$ the relative idèle-class norm. Let $\psi$ be a unitary Hecke character of $K$, and let $g$ be a smooth compactly supported function on $\mathbb R$ with $g(0)=0$. Write $M_g(w)=\int_\mathbb R g(u)e^{wu}\,du$. On each field use Tamagawa Haar on the idèle classes and let $V_F$ be the total volume of its compact norm-one subgroup. Define
$$
 \Phi_K(x)=\frac{d}{V_K}\,\mathbf1_{NC_E}(x)\overline{\psi(x)}\,g(\log|x|_K),
 \qquad
 \Phi_E(y)=\frac{1}{V_E}\,\overline{\psi(Ny)}\,g(\log|y|_E).
$$
Global reciprocity gives $C_K/NC_E=D$. In particular $d\mathbf1_{NC_E}=\sum_{\eta\in\widehat D}\bar\eta$, each $\eta$ inflated to $C_K$. This makes $\Phi_K$ a sum of $d$ genuine Bruhat tests. Continuous characters have smooth restrictions on the Lie part and an open kernel on the profinite compact part. The radial support gives compact support on the idèle classes, and $g(0)=0$ gives the required vanishing on norm-one classes. Integrating on that subgroup with probability Haar after dividing by $V_K$ selects precisely the rows $\psi\eta$ in raw character coordinates. The upstairs test similarly selects $\psi\circ N$. [Tate, (1.2.2)–(1.2.3), pp. 4–5](https://www.math.ias.edu/~goresky/pdf/3-01Tate.pdf#page=2) · [Project character test and Haar normalization](https://github.com/mccorvie/riemann-masullo/blob/9c791d74a81f1191d900e6d96f1270acee9b033e/RiemannMasullo/Ch12_TraceGeometric/Sec5.lean#L866)

With the usual unitary Hecke convention the primitive finite functions satisfy
$$
 L_E(s,\psi\circ N)=\prod_{\eta\in\widehat D} L_K(s,\psi\eta).
$$
Restriction of the Weil character of $\psi$ corresponds to relative norm pullback. Inducing it back gives $\psi\otimes\mathbb C[D]=\bigoplus_{\eta\in\widehat D}\psi\eta$. Additivity and inductivity of local factors give the identity, first in $\Re s>1$ and then by meromorphic continuation. The arguments apply to infinite-order $\psi$. They retain the factors at ramified primes: at $w\mid v$ one takes inertia invariants of the induced representation and groups the summands over all $w\mid v$. For example, $E=\mathbb Q(i)$, $K=\mathbb Q$, $\psi=\chi_{-4}$ gives $\psi\circ N=1$, with the full $\zeta$ factor at $2$ restored by the trivial twist. [Tate, (2.3.5) and §3, pp. 12–14](https://www.math.ias.edu/~goresky/pdf/3-01Tate.pdf#page=10) · [Deligne, Proposition 3.8, pp. 530–531](https://publications.ias.edu/sites/default/files/Number20.pdf#page=30)

Inside $0<\Re\rho<1$, the finite functions have no poles, and the archimedean and conductor factors are regular and nonzero. Thus the order of the completed function on the left at $\rho$ is the sum of the orders on the right, with an order of zero at an ordinary nonzero value. All these orders are nonnegative in the open strip. It follows for **each** $\alpha>0$ that the absolute exterior sum for $\Phi_E$ equals that for $\Phi_K$, with common value
$$
 \sum_{\eta\in\widehat D} \sum_{|\Re\rho-1/2|\ge\alpha}
           m_{\psi\eta}(\rho)\,|M_g(\rho-1/2)|.
$$
The signed sums also agree, with $M_g$ in place of $|M_g|$. Each sum is absolutely convergent by the fixed-character zero count and rapid vertical-strip decay of $M_g$. The equality counts both horizontal wings, both signs of the ordinate, and any shared zero with its full order.

The formulas use raw characters so even independently chosen norm sections give the same samples. For a raw character $\xi$ with $\xi(\tau(e^u))=e^{iau}$, its normalized representative in this chart is $\xi|\cdot|^{-ia}$. An original zero $\rho$ occurs at $\rho+ia$ for this representative. The integral against the physical factor $\bar\xi$ has sample $M_g((\rho+ia)-1/2-ia)=M_g(\rho-1/2)$. This also preserves the exterior edge condition. For finite-order characters $a=0$ for every continuous positive section. With the inverse convention for identifying ideal and idèle characters, invert the labels on both sides. The full packet formulas and the conjugate pairs used here are preserved.

## What the reduction covers

For $g=f$ from the [normalized radial construction](../dirichlet-slab-exterior/README.md), $M_g$ is nonzero whenever $0<|\Re w|<1/2$. The absolute sum of the principal row upstairs at a given width is zero exactly when every character of the class-field packet below has no zero at that width. As $\alpha$ runs through $1/n$, this tests criticality of the full packet. For one finite-order character of $K$ take the cyclic class field cut out by its kernel. Consequently criticality of all Dedekind zeta functions of number fields is equivalent to criticality of **all finite-order Hecke characters** over all number fields. The exact physical measurements above realize this familiar class-field reduction inside the sum of Theorem 12.5.1.1. An infinite-order $\psi$ retains infinite order after finite norm pullback since $(\psi\circ N)\circ\iota=\psi^d$. The full target includes these characters as well. [Project class-field construction](https://github.com/mccorvie/riemann-masullo/blob/9c791d74a81f1191d900e6d96f1270acee9b033e/RiemannMasulloClassField/Remark7131.lean#L64) · [Original target](https://github.com/mccorvie/riemann-masullo/issues/5571)

For an abelian top field $E/\mathbb Q$ and an intermediate $K$, each character of $\operatorname{Gal}(E/K)$ decomposes into exactly $[K:\mathbb Q]$ rational extensions under induction. The subsets of extensions partition all Dirichlet factors of $\zeta_E$. In $E=\mathbb Q(\zeta_{399989})$, the whole packet on each of the 18 intermediate fields therefore has absolute exterior sum below $5.191\cdot10^{-113}$ for the original fixed $f$. The degree of $E$ is 399,988. For $E=\mathbb Q(\zeta_5)$ the corresponding bound is $7.657\cdot10^{-4747}$. These are deliberately frequency-suppressing tests normalized to one on the chosen real Mellin reference. [Field-by-field proof and interval arithmetic](CYCLOTOMIC.md)
