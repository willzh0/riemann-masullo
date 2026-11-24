# Repeated primary poles in primitive totally imaginary quartic fields

**Result for issue #7336.** Let \(F\) have signature \((0,2)\) and let its normal closure act as \(A_4\) or \(S_4\) on its four embeddings. Write \(X=\widehat{C_F^1}\) for the group of global unitary norm-one Hecke characters. The following are unconditional.

1. For each infinite-order \(\chi\in X\), at most one unordered pair of distinct finite places over the same rational prime can give a repeated primary pole, across all rational primes together. A repeated pole at the primary fibre consequently has multiplicity two.
2. For each such pair, the characters that can have a repeated pole lie on at most one rational line in \((X/X_{\rm tors})\otimes_{\mathbb Z}\mathbb Q\). Thus among the \((2B+1)^3\) products of three independent characters modulo torsion with exponents in \([-B,B]\), at most \(1+2BM\) can have a repeated pole at any of \(M\) specified pairs.
3. An infinite-order character with both angular exponents zero has no repeated primary pole anywhere over \(F\).
4. For \(F=\mathbb Q(\vartheta)\) with \(\vartheta^4+\vartheta+1=0\) and \(p=3\), the exact certificate below excludes a repeated pole for **every one of 1,030,300 specified infinite-order, everywhere-finitely-unramified Hecke characters, at every height**.

The issue's comment on degree three derives a cubic result and suggests item 1 and a Four Exponentials implication for primitive totally imaginary quartics. The proof below supplies the quartic argument, adds the converse-direction rank restriction in item 2, and gives an explicit family with a rational certificate. The biquadratic example in PR #7451 has Galois group \(V_4\) and falls outside this theorem. A later comment searches the two biquadratic phases through height index 10^60 and gives a necessary condition on an individual record. The polynomial bound at the surviving individual record centers in the general issue remains open. [Biquadratic record search](https://github.com/mccorvie/riemann-masullo/issues/7336#issuecomment-7145685777) [Earlier cubic argument and quartic sketch](https://github.com/mccorvie/riemann-masullo/issues/7336#issuecomment-7145386474) · [PR #7451](https://github.com/mccorvie/riemann-masullo/pull/7451) · [Current gap](https://github.com/mccorvie/riemann-masullo/issues/7336)

## From an actual Hecke character to algebraic exponentials

Choose embeddings \(\sigma_1,\sigma_2\), one in each conjugate pair. Put \(\ell(x)=\log|\sigma_1 x|\). On archimedean idèles of norm one the infinity character has the form

\[
\chi_\infty(z_1,z_2)=e^{it_\chi\log|z_1|}
 (z_1/|z_1|)^{m_1}(z_2/|z_2|)^{m_2},
\]
with \(t_\chi\in\mathbb R\) and \(m_1,m_2\in\mathbb Z\). Here \(|z_1||z_2|=1\). The coordinate \(t_\chi\) is additive under character multiplication and independent of the choice of global norm twist.

Let \(\epsilon\) be a fundamental unit. For a pair \(w,w'\) over \(p\) of residue degrees \(f,f'\), choose \(h>0\) killing the ideal class group, and \(g\) with \((g)=(\mathfrak p_w^{f'}\mathfrak p_{w'}^{-f})^h\). Both \(\epsilon\) and \(g\) have absolute field norm one. At a common pole the finite idèle \(b=\pi_w^{f'}/\pi_{w'}^{f}\) has norm one and character value one. Indeed the two unramified local factors at that center both take value one on uniformizers, and the norm twist is one on \(b\). This is the ratio used in the repository proof. The idèle \(b^h/g\) has finite unit coordinates and archimedean coordinates \(g_\infty^{-1}\). The image of the compact profinite product of finite unit groups in the circle is finite. It follows that \(\chi_\infty(g)\) is a root of unity. The same conclusion for \(\epsilon\) follows from its diagonal principal idèle. Since the angular factors at algebraic \(x\) are algebraic, each of

\[
e^{\ell(x)},\quad e^{it_\chi\ell(x)}
\]
is algebraic for \(x=\epsilon\), and also for \(x=g\) whenever the pair gives a repeated pole. These are restrictions on the actual global character. [Local idèle ratio in Lean](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/Ch07_SchauderBasesZeta/Sec3b.lean#L5294)

Two algebraic facts supply the independence needed next.

* If \(\ell(x)=0\), two distinct conjugates of \(x\), counted using the four embeddings, have product one. Double transitivity carries this identity to every pair, so all four conjugates are equal and \(x=\pm1\). Consequently \(\ell(\epsilon),\ell(g)\) are rationally independent. For two different unordered pairs the three numbers \(\ell(\epsilon),\ell(g),\ell(g')\) are rationally independent. Indeed the two signed divisors have distinct two-element supports and are independent, including when the pairs share a place. An integral relation among the logarithms would first kill both divisor coefficients, then force the remaining power of \(\epsilon\) to be torsion.
* If \(t_\chi=0\), then \((m_1,m_2)=(0,0)\). Otherwise the exponent vector \(a=(m_1,-m_1,m_2,-m_2)\) gives a root of unity when used as exponents of the four conjugates of \(\epsilon\), because this monomial is \(\chi_\infty(\epsilon)^2\). All Galois translates give roots of unity too. Their rational span is the entire coordinate-sum-zero space. To see this, fix a nonzero coordinate \(a_i\) and average over the stabilizer of \(i\). Double transitivity makes the other three coordinates all \(-a_i/3\). The four translates of that average span the zero-sum space. Clearing denominators shows every conjugate ratio \(\sigma_i\epsilon/\sigma_j\epsilon\) is torsion. Their absolute values are therefore equal and, by the unit norm, all are one. This contradicts the first fact.

When \(t_\chi=m_1=m_2=0\), \(\chi\) has finite order on the whole norm-one class group. For any representing norm-one idèle \(a\), divide \(a^h\) by a generator of its finite ideal. The resulting finite coordinates are units and its archimedean part has norm one. The fixed exponent of the finite-unit image times \(h\) kills \(\chi\). The converse holds because a finite-order character is trivial on the connected archimedean norm-one group. We have proved that \(\chi\mapsto t_\chi\) is injective modulo torsion.

## Applying Six Exponentials in both directions

The Six Exponentials Theorem says that for two rationally independent \(x_i\) and three rationally independent \(y_j\), some \(e^{x_i y_j}\) is transcendental. [Waldschmidt, Theorem 2.1, p. 4](https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/DION2005proceedings.pdf#page=4)

* Two pairs for one infinite-order character would give the independent sets \(\{1,it_\chi\}\) and \(\{\ell(\epsilon),\ell(g),\ell(g')\}\), with all six exponentials algebraic.
* Two characters independent modulo torsion for one pair would give the independent sets \(\{\ell(\epsilon),\ell(g)\}\) and \(\{1,it_{\chi_1},it_{\chi_2}\}\), again with all six exponentials algebraic. Rational independence of the two real \(t\)'s follows from injectivity modulo torsion. The real number 1 adds a third independent direction to the two purely imaginary numbers.

The count follows because a rational line through the origin meets the box \([-B,B]^3\cap\mathbb Z^3\) in at most \(2B+1\) points, including zero. For a purely radial infinite-order character, a repeated pair would give \(t_\chi\ell(\epsilon)/(2\pi),t_\chi\ell(g)/(2\pi)\in\mathbb Q\), with the former nonzero. Their ratio contradicts independence. Under the *conjectural* Four Exponentials statement, the \(2\times2\) array from just one character and one pair would exclude that pair as well. Items 1–4 use no such conjecture.

## An explicit field, prime, and certificate

Set \(F=\mathbb Q(\vartheta)\) with \(f(X)=X^4+X+1\). Its discriminant is the prime 229. The polynomial is irreducible modulo 2 and its reduction modulo 3 has factor degrees 1 and 3. The normal group is \(S_4\) since it contains a 4-cycle and a 3-cycle and therefore has order divisible by 12, while the unique index-two subgroup \(A_4\) contains no 4-cycle. The signature is \((0,2)\). The Minkowski bound equals \(3\sqrt{229}/(2\pi^2)<3\), and inertness of 2 precludes an ideal of norm 2, so the class number is one. The roots of unity are just \(\pm1\), since the primitive non-Galois quartic has no proper subfield other than \(\mathbb Q\).

At \(p=3\), let \(w_1,w_3\) have residue degrees 1 and 3. Since \(N(1-\vartheta)=f(1)=3\), the two-place ratio is represented by
\[
g=(1-\vartheta)^4/3,\qquad (g)=\mathfrak p_{w_1}^{\,3}/\mathfrak p_{w_3}.
\]
For example, choose the full 3-fibre for \(S_0\) and the prime over 2 for \(S\). The global characters below are unramified at all finite places, the Picard condition holds and the norm at the place over 2 is 16. The absence of any repeated 3-primary pole is independent of the outside place and the section used for the height.

Let \(z_1,z_2\) be the upper-half-plane roots of \(f\), with positive and negative real part respectively, and choose \(\sigma_j(\vartheta)=z_j\). The script proves that \(\epsilon=\vartheta\) is a fundamental unit. Write \(L=\log|z_1|\) and \(D(x_1,x_2)=(\log|x_1|-\log|x_2|)/2\). For each integer triple \((k,u,v)\) set

\[
t=(2\pi k-2u\arg z_1-2v\arg z_2)/L,\qquad
\lambda_\infty(x)=e^{itD(x)}
 (x_1/|x_1|)^{2u}(x_2/|x_2|)^{2v}.
\]

This character is one on \(\vartheta\) and \(-1\), hence on all units. Set the finite ideal character on \((a)\) to \(\lambda_\infty(a)^{-1}\), which defines it on all ideals because the class number is one. Multiplying archimedean and finite parts gives the claimed global characters. Every nonzero triple gives infinite order on the norm-one group. Indeed a finite-order character kills its connected archimedean subgroup, which forces \(u=v=0\) and then \(k=0\). This also proves independence of the three generators.

Let \(A=\ell(g)/L\), \(B_j=(4\arg(1-z_j)-A\arg z_j)/\pi\). Since \(g\) has norm one,
\[
\lambda_\infty(g)=\exp\bigl(2\pi i(kA+uB_1+vB_2)\bigr).
\]
The finite local factors are unramified, so \(\chi(b)=\lambda_\infty(g)^{-1}\). A common 3-primary pole would require \(kA+uB_1+vB_2\in\mathbb Z\). For all nonzero triples in \([-50,50]^3\), the certificate proves
\[
\operatorname{dist}(kA+uB_1+vB_2,\mathbb Z)\ \ge\ \frac{62050034}{10^{14}}.
\]
At any pole of the degree-one place, the degree-three uniformizer value is \(\chi(b)^{-1}\), so its chord distance from one is at least four times this bound. This rules out a common pole at every height for all 1,030,300 characters. It does not assert anything about other character powers outside the box.

Run `python research/issue-7336/verify_quartic.py` from the repository root. With Python and SymPy 1.14.0 it gives

~~~
disc=229, S4, signature=(0,2), class number 1, p=3 has degrees 1 and 3
theta is a fundamental unit: 22 possible quartics ruled out exactly
coordinate centers / 100000000000000: [-715834103511298, 43386664021545, 563076443293116]
coordinate error radii / 100000000000000: [1, 1, 1]
nonzero triples certified: 1030300
uniform distance to Z >= 62050034/100000000000000; least certificate at (-17, 35, 43)
~~~

The fundamental-unit check uses the house \(H\), the largest modulus of a conjugate. For a totally imaginary quartic, \(H^2\) is the largest real root of the sextic with roots \(r_i r_j\) for \(i<j\). Indeed one such pair is a largest-modulus conjugate and its complex conjugate, and every pair product has modulus at most \(H^2\). The sextic shows \(H(\vartheta)<6/5\). If \(\vartheta=\pm\eta^n\), \(n\ge2\), then \(H(\eta)^2<6/5\) and \(H(\eta)<11/10\). Since \(\eta\) generates the primitive quartic field, its monic minimal polynomial has constant 1 and remaining coefficients bounded by \(4,7,5\) in absolute value, by elementary symmetric functions. Its discriminant is 229 times an integer square. Among the irreducible quartics of signature \((0,2)\) surviving these exact filters, all 22 have a pair product strictly above \(6/5\). This rules out a proper power.

To certify the angles, the script isolates the two upper roots in rational rectangles. It bounds \(\log r\) using the series for \(2\operatorname{artanh}((r-1)/(r+1))\) with a geometric bound on the tail, and bounds \(\arctan\) by its alternating series after range reduction. Machin's formula encloses \(\pi\). Each operation rounds outward to a rational grid. The final million distance comparisons use integers. An independent 90-decimal evaluation from the two local characters directly found the same minimizing triple, up to sign, with distance 0.00000062050167725264506587. The rigorous bound comes from the rational certificate. The all-fields rank bounds above are mathematical proofs using the classical Six Exponentials Theorem. The arithmetic argument has not been formalized in Lean.

The manuscript introduces the primary heights on p. 360 and returns on pp. 361–363 to the earlier proof. The coefficient change is at the end of p. 349 and the oscillation discussion continues on p. 350. The current reconstruction adds the single-place shifted estimate only at separated record centers in degree at least three. None of these calculations supplies that estimate when a repeated pole really occurs. [Masullo, pp. 349–350 and 360–363](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/paper/the-music-of-the-primes.pdf) · [Merged reduction #7413](https://github.com/mccorvie/riemann-masullo/pull/7413) · [Exact residual statement](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/Ch07_SchauderBasesZeta/Sec3b.lean#L5950)
