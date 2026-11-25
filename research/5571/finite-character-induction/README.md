# When two Hecke zero sums cancel at the same zeros

Theorem 12.5.1.1 on pp. 519–520 of *The Music of the Primes* discards the zero terms outside an open strip. For a finite list of finite-order Hecke characters of one number field, one can compute every constant-coefficient identity among their full critical-strip zero divisors from a finite group. The resulting change of basis preserves the signed exterior sum for every positive width, on each side of the strip separately. It applies even when the radial functions of the characters differ. [Issue #5571 and the Lean statement](https://github.com/mccorvie/riemann-masullo/issues/5571) · [Criterion, proof and reduction](DIVISORS.md)

A specialization of de Smit's 1998 construction gives a quartic field with trivial rational automorphism group. Take a root $x$ of $3x^4-6x^2+12x-1$, put $K=\mathbb Q(x)$ and $D=x^3-x+1$. The primitive quadratic Hecke characters of $K(\sqrt D)$ and $K(\sqrt{-3D})$ disagree at the degree-one prime above 41 defined by $x=24\bmod41$. Nevertheless their completed $L$-functions agree. A real test invariant under inversion can have a nonzero Mellin sample on each row at every possible off-line interior site and opposite signed coefficients there. Its signed omitted sum vanishes at every width. Degree four is minimal for a nonzero relation of this kind that is invariant under every automorphism of the field. [Quartic proof, bad primes and minimality](QUARTICS.md)

The construction also yields arbitrarily many distinct quadratic characters with the same completed function on a field with trivial automorphism group. One degree-192 example has eight such characters and seven real cancellation tests with pairwise disjoint angular supports. A separate degree-21 example shows that the quotient of the two characters need not descend from a character of $\mathbb Q$ by the norm. [Constructions and sources](FAMILIES.md)

If an exterior zero exists on either selected row in the quartic example, its individual contribution to the sum of norms is positive. Showing that this mass vanishes for every character, or proving the paper's assertion for arbitrary admissible tests, remains open. The earlier Gaussian construction used conjugation of the underlying field and has a Lean proof for each angular pair. The quartic, finite-rank and growing-family arguments here are written mathematics. [Gaussian pair PR](https://github.com/mccorvie/riemann-masullo/pull/7720) · [Earlier inversion-odd case](https://github.com/mccorvie/riemann-masullo/pull/7411)

## Reproduce the finite calculations

Run the commands from this directory with Python 3. The quartic polynomial check and the septic prime-factorization check use SymPy. The group and point-count checks use exact finite arithmetic. The analytic and class-field-theoretic arguments are in the linked proofs.

~~~sh
python check_quartic.py
python check_families.py
python flag_group.py
python flag_primes.py
~~~
