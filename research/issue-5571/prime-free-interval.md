# A first-order equation for the rational strip trace on one prime-free interval

Fix any nonempty open interval $I\subset(0,\log 2)$ in the log norm and any $0<\alpha<1/2$. For **every primitive Dirichlet character** $\chi$, including the zeta character, the following two statements are equivalent.

1. All its nontrivial zeros lie in $|\Re\rho-1/2|<\alpha$.
2. On $I$, the distribution formed from its **open-strip** zeros satisfies

   $$
   (\partial_x-\kappa_\chi)\left[(e^{2x}-1)
     \{S_{\mathrm{in},\chi}(x)-\delta_\chi(e^{x/2}+e^{-x/2})\}\right]=0.
   $$

Here $S_{\mathrm{in},\chi}=\sum_{|\Re\rho-1/2|<\alpha}m_\rho e^{(\rho-1/2)x}$, $\delta_\chi=1$ for the principal character and zero otherwise, and $\kappa_\chi=3/2$ for even characters and $1/2$ for odd ones. The equation allows an arbitrary integration constant. It suffices to test the geometric comparison on any one interval selected **before** the character, width or zero is known. The constancy assertion for the strip trace is open.

## Why the full trace obeys the equation

Use the radial character test $\varphi(c)=\overline{\chi(c)}h(\log|c|)$, with $h\in C_c^\infty(I)$, for the rational norm section supported at the real place. Orthogonality on $\widehat{\mathbf Z}^{\times}$ picks out $\chi$. Divide the global Mellin terms by the norm-one volume, so the surviving moment is $H(w)=\int h(x)e^{wx}\,dx$. Both polar terms acquire the factor $\delta_\chi$. The character identification also follows directly by representing each rational idèle class by a positive real and a finite unit idèle. Every section-normalized character is then a character of the profinite unit group and factors through a finite quotient.

The finite-place restrictions are identically zero since no $p^k$, $k\in\mathbf Z$, belongs to $(1,2)$. At the real place the measure is a constant multiple of $dr/r$ on each sign component. Writing $r=e^x>1$, the local density, up to one positive constant, is

$$
 \frac{\sqrt r}{2}\left(\frac1{r-1}+\frac{\chi(-1)}{r+1}\right)
 =\frac{e^{\kappa_\chi x}}{e^{2x}-1}.
$$

The normalized all-zero formula therefore gives the stated differential equation with $S_{\rm all,\chi}$ in place of $S_{\rm in,\chi}$. The unknown constant plays no role. These zero sums define distributions: repeated integration by parts gives arbitrary inverse powers of the ordinate uniformly for $|\Re w|\le1/2$, and the classical full zero count is $O_\chi(T\log(2T))$. [Manuscript, pp. 519–520](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/transcription/chapters/chapter-12.md#L1334) · [Real principal value for tests vanishing at one](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/AppB_AnalyticNT/Sec4b.lean#L6831)

## A normalized witness with every local term zero

Let $w=\rho-1/2$. Write $E$ for the distinct exterior frequencies in this character, including the edges. Montgomery’s classical density estimate with $\sigma=1/2+\alpha$, combined with the functional equation for the left side, gives

$$
 \#\{w\in E:|\Im w|\le T\}\ll_{q,\alpha}T^{1-\delta}(\log(2T))^{14},
 \qquad \delta=\frac{4\alpha}{3-2\alpha}>0.
$$

Indeed $1-\delta=3(1-\sigma)/(2-\sigma)$. This estimate counts all characters of the fixed modulus and includes the boundary. Each dyadic shell contributes $O_{q,\alpha}(2^{-j\delta}(1+j)^{14})$ to the reciprocal-height sum. In particular $\sum_{w\in E}(1+|\Im w|)^{-1}<\infty$. The reciprocal-height tail above $T\ge2$ is $O_{q,\alpha}(T^{-\delta}(\log(2T))^{14})$. [Montgomery, *Topics in Multiplicative Number Theory*, Chapter 12](https://link.springer.com/book/10.1007/BFb0060851) · [Jutila, formula (1.1), p. 3, with its fixed-modulus quantifiers](https://www.acadsci.fi/mathematica/1972/no520pp01-13.pdf#page=3)

Choose a target $u$ in $-1/2<\Re u<1/2$. Put $E'=E\setminus\{u\}$. On any compact interval of positive length inside $I$, sparse Laplace interpolation supplies a smooth $g$ with transform $G(u)=1$, vanishing at

$$
 E'\ \cup\ (E'+2)\ \cup\ \{u+2,-1/2,1/2,3/2,5/2\}.
$$

This union still has summable reciprocal heights and excludes $u$. Multiplying by $1-e^{2x}$ gives $h=(1-e^{2x})g$ and $H(w)=G(w)-G(w+2)$. Thus $H(u)=1$, $H(E')=0$, and $H(\pm1/2)=0$. Both real-place integrals vanish separately, for exponents $\kappa=1/2,3/2$, since $\int h(x)e^{\kappa x}/(e^{2x}-1)\,dx=-G(\kappa)=0$. This retains the target while annihilating the local terms even for the principal character. [Sparse interpolation, PR 7419 at its checked revision](https://github.com/mlyle/riemann-masullo/blob/e3c632cd5a350ccafa2167a0f666afc3042aa01b/RiemannMasullo/ForMathlib/Analysis/Complex/SparseLaplaceInterpolation.lean#L403)

For completeness, the interpolation uses an elementary compact measure. Center the prescribed frequencies at $u$. For a tail frequency $v$, set $a=\pi/|\Im v|$ and use the probability measure proportional to $e^{a\Re v}\delta_0+\delta_a$. Its Laplace transform at $v$ is zero and its mass is one. For $T>2(1+|\Im u|)$ the total support length needed for the original and shifted frequencies above height $T$ is $O_{q,\alpha}(T^{-\delta}(\log(2T))^{14})$. Choose it smaller than half the prescribed interval. Convolve the distributions of the independent increments and then convolve with a smooth translated bump of integral one. A polynomial in $-\partial_x$, normalized at zero and of degree $O_{q,\alpha}(1+T^{1-\delta}(\log(2T))^{14})$, removes the finite exceptional frequencies. Finally multiply by $e^{-ux}$.

If $u\in E$, the normalized exterior sum on this witness is exactly $m_{1/2+u}>0$, while the all-zero sum is zero. The normalized open-interior sum is consequently exactly $-m_{1/2+u}$. If the proposed ODE holds, the quantity in square brackets equals $C e^{\kappa_\chi x}$ on $I$ for some constant $C$, by the elementary distributional uniqueness theorem for a function with zero derivative. Both polar moments and the $\kappa_\chi$ orbital integral of the witness vanish, so the interior sum must be zero. This contradiction proves the reverse implication. It detects an edge zero with its full multiplicity.

There is also an unconditional positive class of tests for the small-width theorem. Take $u\notin E$. The construction gives $H(u)=1$ and every exterior term vanishes individually. Add finitely many other interior targets to the forbidden list and superpose the resulting profiles to prescribe arbitrary finite interior Mellin data. This gives an infinite-dimensional space of smooth tests on the one fixed positive shell satisfying the trace formula. The tests depend on the exterior set through the mathematical construction. The same profile can serve all primitive characters in any fixed finite conductor list when its prescribed points are interior to the strip.

## Other number fields

For an arbitrary number field $F$ of degree $n$ and **every section-normalized unitary Hecke character** $\chi$, the same construction works unconditionally throughout the range

$$
 0<\alpha<1/2,\qquad c_1 n(1/2-\alpha)<1,
$$

where $c_1>0$ is the absolute constant of Lemke Oliver and Thorner. Their Corollary 1.2 for $\mathrm{GL}_1$ bounds the count to the right of $\sigma$ by $(Q_\chi T^n)^{c_1(1-\sigma)}$; reflection supplies the left side and a possible unitary norm twist only translates ordinates. The same dyadic argument gives reciprocal-height summability. The range is nonempty for each degree and the support interval can be fixed independently of the character. No numerical value of $c_1$ is assumed. [Lemke Oliver and Thorner, Corollary 1.2, p. 4](https://arxiv.org/pdf/1505.03122#page=4)

The archimedean factors now specify a finite set $K_\chi$ of exponents. Use $r=|z|_v=e^x$ and write the inverse local character as $\operatorname{sgn}(z)^\epsilon r^{it_v}$ at a real place and $e^{im_v\theta}r^{it_v}$ at a complex place. A real place contributes the exponent $\kappa_v+it_v$. For a complex place put $b_v=(1-|m_v|)/2+it_v$. At $R=\sqrt r>1$ the angular average of $e^{im_v\theta}/|1-Re^{i\theta}|^2$ is $R^{-|m_v|}/(R^2-1)$ by the geometric series. Its orbital density is a constant times $r^{b_v}/(r-1)$. After multiplication by $r^2-1$ its two exponents are $b_v,b_v+1$. All exponents in $K_\chi$ have real parts in $\frac12\mathbf Z$, whereas an exterior frequency has real part strictly between $-1/2$ and $1/2$ and separated from zero. Add $K_\chi$ to the forbidden interpolation points. Every local term and both poles then vanish on an exterior witness. The corresponding equation for the open-strip trace uses $\prod_{k\in K_\chi}(\partial_x-k)$ in place of the single first-order factor and the same multiplier $e^{2x}-1$. Use distinct exponents in that polynomial. For the positive class of tests, choose interior interpolation targets disjoint from $K_\chi$. This general-field calculation uses the normalized squared complex absolute value in the project’s trace formula. [Normalized convention in the project](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/Ch12_TraceGeometric/Sec5.lean#L234)

For **every** $0<\alpha<1/2$, the witness construction works for the principal character of an abelian extension $F/\mathbf Q$, and for each Dirichlet character pulled back by $N_{F/\mathbf Q}$. The corresponding Hecke function factors, up to Euler factors regular and nonzero in the strict strip, into a finite product of Dirichlet functions. Indeed at an unramified prime $p$ of residue degree $f$, the values of all characters of $\mathrm{Gal}(F/\mathbf Q)$ at Frobenius are the $f$-th roots of unity with equal multiplicity. Twisting by $\eta(p)$ gives the factor $(1-\eta(p)^f p^{-fs})^{-[F:\mathbf Q]/f}$. Thus rational density supplies the stronger range in these components. [Abelian factorization by Euler factors, §7.2](https://janschuetz.perso.math.cnrs.fr/lehre/ANT.pdf)

## Verification and open step

A finite-window counterexample shows why a total zero-count bound alone would be insufficient. Take $P>\log 2$, $0<\alpha\le\beta<1/2$, and the entire function $\cosh(P(s-1/2))+\cosh(P\beta)$. It is invariant under $s\mapsto1-s$ and conjugation, with simple exterior frequencies $\pm\beta+(2j+1)\pi i/P$. Poisson summation gives their weighted trace exactly as $2P\sum_{k\in\mathbf Z}(-1)^k\cosh(\beta kP)h(kP)$. This is zero for every admissible profile supported in $(-P,P)$, although the divisor is infinite. These frequencies have linear counting growth, and their reciprocal-height sum diverges. This example concerns the proposed abstract inference from a bounded norm window. It has no asserted Hecke origin.

The sparse interpolation input is formalized in PR 7419. The application to Hecke zeros and the differential equation here are mathematical arguments. Showing that the open-strip trace obeys the local differential equation remains open. To identify it with (12.5.1.4)'s closed-strip spectral-quotient trace when a zero lies on an edge, the project's edge correction or a limit from smaller widths is still needed. [Project's open-strip theorem](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/Ch12_TraceGeometric/Sec5.lean#L98) · [Closed-strip kernel statement and its edge convention](https://github.com/mccorvie/riemann-masullo/blob/8586f1c40558a900ba79fb41487c2567d4bc5268/RiemannMasullo/Ch12_TraceGeometric/Sec5_Isolated.lean#L53)
