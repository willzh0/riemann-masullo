# Arbitrarily many quadratic characters with equal completed functions

The single-prime arithmetic construction used here is due to Bart de Smit. The two index-$2(\ell+1)$ subgroups and the elliptic-curve realization appear in Proposition 1 and §3 of his paper. Taking products, choosing square-class characters on the common Borel, and inserting their signs in the physical test give the following application to Theorem 12.5.1.1 on pp. 519–520. [De Smit, *Generating arithmetically equivalent number fields with elliptic curves*, pp. 393–396](https://pub.math.leidenuniv.nl/~smitbde/papers/ants1998-desmit.pdf#page=3)

## Disjoint supports over fields with trivial automorphism group

For every $m\ge1$ there exists a single $K$ with $\operatorname{Aut}_{\mathbb Q}(K)=1$ and $2^m$ distinct quadratic characters with the same completed Hecke function. There is a real physical test for every one of $2^m-1$ pairwise disjoint angular supports. Each test is even under inversion, selects all $2^m$ characters with nonzero coefficients of equal size, and cancels at each zero, including both exterior wings for every width and norm section.

Use $E:y^2=x^3-x+1$. Its $j=-6912/23$ is not an algebraic integer, so the curve has no complex multiplication. By Serre's open-image theorem its adelic Galois image contains a principal congruence subgroup. Therefore, outside a fixed finite set, any distinct odd primes $\ell_1,\ldots,\ell_m$ give
$$
 \operatorname{Gal}\bigl(\mathbb Q(E[\ell_1\cdots\ell_m])/\mathbb Q\bigr)
 = \prod_i\mathrm{GL}_2(\mathbb F_{\ell_i}).
$$
Write $L$ for this field, $B_i$ for an upper Borel in each factor and $K=L^{\prod_i B_i}$. Then $[K:\mathbb Q]=\prod_i(\ell_i+1)$. Each Borel has a unique invariant line and is its own normalizer. The product has the same normalizer property, giving $\operatorname{Aut}_{\mathbb Q}(K)=1$. [Serre, *Propriétés galoisiennes des points d'ordre fini des courbes elliptiques*, §4.4, theorem 3 and corollary 1, pp. 299–300](https://www.college-de-france.fr/media/jean-pierre-serre/UPL5874918517843398173_Serre_proprie_te_s_galoisiennes_des_courbes_elliptiques.pdf#page=41)

For each $i$ write $a_i,d_i$ for the diagonal entries, and $\lambda_i$ for the quadratic character of $\mathbb F_{\ell_i}^{\times}$. For $S\subseteq\{1,\dots,m\}$ take the product $\psi_S$ of $\lambda_i(d_i)$ for $i\in S$ and $\lambda_i(a_i)$ for $i\notin S$. Varying a diagonal entry independently shows that all $2^m$ characters are distinct and of order two. The two local induced traces agree by the invariant-line calculation in the [quartic example](QUARTICS.md), valid for every odd prime. Induction on the product is the tensor product of the inductions, so all $\operatorname{Ind}\psi_S$ are isomorphic. This gives equality of the completed functions, including ramified factors and the archimedean factors. Their quadratic extension fields are pairwise nonisomorphic over $\mathbb Q$: the kernels contain the full unipotents of each Borel, which force a unique invariant line in each projection. Any conjugation carrying one kernel to another must preserve each chosen line and belong to the product Borel, where each kernel is normal. Every embedding into an algebraic closure extends to a Galois automorphism, and $L$ is normal.

Put $\chi_0=\psi_{\varnothing}$ and $\delta_i=\lambda_i(\det_i)$, so $\psi_S=\chi_0\prod_{i\in S}\delta_i$. The $\delta_i$ are independent, and $\chi_0$ is independent of them (vary both diagonal signs in one factor). These finite signs are all realized on the norm-one subgroup, since finite-order characters are trivial on every positive norm section. Thus each sign cell $\delta=\eta\in\{\pm1\}^m$ has normalized angular Haar measure $2^{-m}$. For $\eta\ne(1,\ldots,1)$ take
$$
 Y_\eta=\chi_0\,\mathbf 1_{\delta=\eta}
      =2^{-m}\sum_S\left(\prod_{i\in S}\eta_i\right)\psi_S .
$$
The coefficient sum is $2^{-m}\prod_i(1+\eta_i)=0$. Multiply by the same fixed real even [radial profile](DIVISORS.md). Each of the nonzero physical tests has signed sum zero at every site. Their supports are disjoint. They form a basis of the $2^m-1$ dimensional space of zero-sum scalar weights on these particular rows. This describes the exhibited space of tests, independently of the location of any zero of their common $L$-function.

## A degree-192 example with eight characters

For this specific curve the first three primes $3,5,7$ work jointly, giving degree $4\cdot6\cdot8=192$. The primes $3,5$ alone give degree 24 and four characters. The following table gives witnesses at primes of good reduction. Write $a_p=p+1-\#E(\mathbb F_p)$ and $\Delta=a_p^2-4p$.

| $\ell$ | $(p,a_p,\Delta)$ with $\Delta$ nonsquare mod $\ell$ | $(p,a_p,\Delta)$ with $v_\ell(\Delta)=1$ |
|---|---|---|
| 3 | $(5,-2,-16)$ | $(7,-4,-12)$ |
| 5 | $(3,-3,-3)$ | $(11,2,-40)$ |
| 7 | $(5,-2,-16)$ | $(79,-6,-280)$ |

The first witness precludes a common invariant line. The second gives a nonscalar Jordan block modulo $\ell$: a scalar reduction of a $2\times2$ $\ell$-adic matrix forces its discriminant $(a-d)^2+4bc$ to be divisible by $\ell^2$. Some power gives a nontrivial transvection. Conjugacy and irreducibility give two transvections with different fixed lines. Over these prime fields their powers give both elementary root groups in the basis of those lines, hence the whole $\mathrm{SL}_2$. The cyclotomic determinant is surjective, so each indicated $\mathrm{GL}_2$ image is full.

For joint surjectivity add the factors in order. The earlier group has order $48$ when adjoining the factor at 5, and $48\cdot480$ when adjoining the factor at 7. These orders are prime to the respective new prime. Hence any common quotient of the earlier product and the new factor kills all transvections of the new factor. It factors through that determinant, and is abelian. Every abelian quotient of the earlier product factors through its determinants as well: a diagonal conjugation writes each elementary root group as commutators since all the fields have more than two elements. The determinants are jointly independent by the cyclotomic character and the Chinese remainder theorem. Goursat's lemma now excludes any common nontrivial quotient cutting down the image. This proves the product assertion for the explicit example using just the displayed point counts. A finite verifier independently enumerates the invariant lines for all 2,544 invertible matrices in the three groups and checks the seven angular indicators. [Point counts, induced traces and disjoint supports](check_families.py)

## An example whose quotient character does not come from a rational norm

Let $L$ be the splitting field of Trinks' polynomial $X^7-7X+3$, with $G=\mathrm{GL}_3(\mathbb F_2)\cong\mathrm{PSL}_2(7)$. Let $H$ be the upper unitriangular group, the stabilizer of a full flag. It fixes a unique line and a unique plane in the natural module. Thus $N_G(H)=H$, and $K=L^H$ has degree 21 and trivial automorphism group. [Serre, *Sur les représentations modulaires de degré 2*, §5.5, pp. 225–226](https://www.college-de-france.fr/media/jean-pierre-serre/UPL5835292064138487263_Serre_Repr.modulaires_Galois.pdf#page=47) · [Rohrlich, *Galois theory, elliptic curves, and root numbers*, p. 345](https://www.numdam.org/item/CM_1996__100_3_311_0.pdf#page=36)

For $h\in H$ with entries $a=h_{12}, b=h_{23}$, take $\eta_a(h)=(-1)^a$ and $\eta_b(h)=(-1)^b$. Each kernel has three involutions and the identity. All involutions in $G$ are conjugate. The induced permutation characters of the two kernels are therefore equal by the fixed-coset formula. For either kernel its induced permutation character is $\operatorname{Ind}_H^G1+\operatorname{Ind}_H^G\eta$. Subtraction gives $\operatorname{Ind}\eta_a=\operatorname{Ind}\eta_b$. On the six conjugacy classes of orders $1,2,3,4,7,7$ the common trace is $21,1,0,-1,0,0$. The kernels are not conjugate: their fixed vector subspaces in $\mathbb F_2^3$ have dimensions two and one. This produces distinct real quadratic characters of $K$ with identical completed functions.

The quotient $\eta_a\eta_b$ cannot be a rational finite-order Hecke character pulled back by $N_{K/\mathbb Q}$. Such a rational Galois character would restrict to this quotient on the absolute group of $K$, and hence be trivial on the absolute group of $L$. It would factor through $G$, which is perfect and has no nontrivial one-dimensional characters. The quotient is nontrivial on $H$, giving a contradiction. Thus the same real even test works beyond the rational determinant twists used in the elliptic examples. The finite checks evaluate both degree-21 signed actions on every group element and recover matching Euler factors from polynomials for the two degree-42 extension fields at good primes of each Frobenius order. [Finite group, trace and signs](flag_group.py) · [Actual prime factorizations](flag_primes.py)
