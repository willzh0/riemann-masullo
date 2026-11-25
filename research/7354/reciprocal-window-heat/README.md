# The running Gaussian correction at norm one

For the rational real-place mean-zero Paley–Wiener level at order zero and twist one half, the logarithmic heat scale changes the finite part of a quotient Bruhat test crossing norm one. Write \(R=BL\), let \(w\) be its smooth radial profile, and take \(Bh\to0\) and \(R\to\infty\). If \(\tau\log R\to\kappa<\infty\), the limit after subtracting \(w(1)\log R\) is
\[
\operatorname{actualCentralTraceFinitePart}(\delta,w)+\kappa\big(w'(1)+w''(1)\big).
\]
The coefficient is a second derivative in log radius. It can have either sign for smooth tests with the same value at the identity.

The construction uses mrshu’s Gaussian prescription and sharp reciprocal-window finite part, thierryaaron’s real-even level and Haar interval operator, and the real-even cosine heat kernel. The heat sandwich is the one from the [native order-zero compact Bruhat calculation](https://github.com/mccorvie/riemann-masullo/pull/7705). At positive variance its trace equals the integral of the quotient-Haar diagonal by the finite-band reproducing-kernel formula in the same source. [Sharp interval-operator finite part](https://github.com/mccorvie/riemann-masullo/pull/7693) · [Real-even Gaussian calculation](https://github.com/mccorvie/riemann-masullo/pull/7646) · [Haar interval-average construction](https://github.com/mccorvie/riemann-masullo/pull/7681) · [Sharp sine-integral estimate](https://github.com/mccorvie/riemann-masullo/pull/7602)

Let \(0<\delta<1\), \(I=[(1+\delta)^{-1},(1-\delta)^{-1}]\), and let \(w\) be real, smooth and compactly supported in \(I\). Only two bounded log derivatives are needed. Write \(W(y)=w(e^y)\), \(R=BL\), \(H=Bh\), \(B>0\), and \(0\le h\le L\). Use \(w\) as the radial test in both source theorems. Let \(T_{\tau,h,L,B}\) denote the heat trace of the true mean-zero cosine compression of #7646. Let \(T_{0,0,L,B}\) denote its zero-heat upper-mask trace. The phase-coordinate computation below is a mathematical derivation from the two sources. The accompanying Lean file checks the endpoint estimates, oscillatory scale estimates, Gaussian coefficient cancellation, and the actual two-row trace bound separately.

For \(R\ge1\), \(0<2\tau\le1\), choose a fixed \(d>0\) satisfying \((1+\delta)(e^d-1)\le\delta/2\). There is a constant \(C=C(w,\delta,d)\) for which
\[
\left|T_{\tau,h,L,B}-T_{0,0,L,B}
-\big(\mathbb E W(-Z)-W(0)\big)\log R\right|
\le C\left((2\tau)^{1/4}+\sqrt{2\tau}
 +(1+\log R)e^{-d^2/(8\tau)}+H\right),
\qquad Z\sim\mathcal N(0,2\tau).
\]
The test-dependent coefficient obeys
\[
|\mathbb E W(-Z)-W(0)|\le\tau\|W''\|_\infty.
\]
Consequently the limit of \(T_{\tau,h,L,B}-w(1)\log(BL)\) is exactly \(\texttt{actualCentralTraceFinitePart}(\delta,w)\) when \(BL\to\infty,\ Bh\to0,\ \tau\to0,\ \tau\log(BL)\to0\). At zero variance there is no heat displacement. For a complex smooth compact test the same calculation applies to its real and imaginary parts, with the complex-linear extension of the sharp finite part. Norm-one angular volume and the polar term already enter the sharp trace. [Exact finite part and averaged trace, #7693](https://github.com/mccorvie/riemann-masullo/pull/7693) · [Exact Gaussian sandwich for the physical mean-zero compression, #7646](https://github.com/mccorvie/riemann-masullo/pull/7646)

## The two moving endpoints

Set \(m(z)=\min(1,e^z)\), \(R_z=Rm(z)\), \(c=(ge^z)^{-1}-1\), and \(S_R(c)=\operatorname{Si}(2\pi Rc)/(\pi c)\). At \(c=0\) its continuous value is \(2R\), and the totalized zero used in the sharp scalar theorem has the same interval integral. With the floor set to zero, the unpolarized shifted ambient trace from #7646 is
\[
 A_R(z)=\int_{I_z} F_z(c)\,[S_{R_z}(c)+S_{R_z}(c+2)]\,dc,
 \quad F_z(c)=\frac{w(e^{-z}/(1+c))}{\sqrt{1+c}},
\]
\[
 I_z=[e^{-z}(1-\delta)-1,\ e^{-z}(1+\delta)-1].
\]
Indeed the single atom at \(ge^z\) carries the half-density \((ge^z)^{-1/2}\), the Haar measure is \(dg/g\), and the two cosines give the direct and reflected reciprocal phases. The factor \(m(z)\) comes from the exact intersection of the two sharp frequency bands. The outer Gaussian in the sandwich has variance \(\tau+\tau\).

For \(|z|\le d\), the left endpoints of \(I_z,I_0\) are at most \(-\delta/2\). The right endpoints are at least \(\delta/2\). The strip lengths are exactly \((1-\delta)|e^{-z}-1|\) and \((1+\delta)|e^{-z}-1|\). The direct kernel is bounded on both strips by \(2(\pi/2+2)/(\pi\delta)\), the reflected kernel has its denominator bounded away from zero, and \(F_z\) is uniformly bounded. Replacing \(I_z\) by \(I_0\) therefore costs \(O(|z|)\). This bound also covers a sharp truncation of a smooth function with nonzero endpoint values. The stated physical heat theorem uses the continuous zero extension in the compact-test operator of #7646.

## The uniform estimate at the singularity

Write \(I_0=[-\delta,\delta]\), \(M(R)=\int_{I_0} S_R(c)\,dc\), and \(\Delta_z=w(e^{-z})-w(1)\). On the common interval, the fundamental theorem of calculus in \(z\) and \(c\) gives
\[
 |F_z(c)-F_0(c)-\Delta_z|
 \le \sup_{|u|\le d,\,|v|\le\delta}|\partial_v\partial_u F_u(v)|\,|c|\,|z|.
\]
Multiplication by \(|S_{R_z}(c)|\le(\pi/2+2)/(\pi|c|)\) makes its integral \(O(|z|)\). The reflected kernel costs \(O(|z|)\) directly under the coefficient change.

The identity \(d\,\operatorname{Si}(a e^t)/dt=\sin(a e^t)\) gives
\[
 |S_{R_z}(c)-S_R(c)|\le|\log m(z)|/(\pi |c|),\qquad c\ne0 .
\]
Apply this to the Lipschitz remainder \(F_0(c)-F_0(0)\); the phase zero cancels its denominator. It applies without subtraction at the reflected phase \(c+2\). The constant part is controlled by the exact Fubini formula from #7693,
\[
 M(R)=\frac2\pi\int_0^R\frac{\operatorname{Si}(2\pi\delta t)}{t}\,dt .
\]
It gives \(|M(R_z)-M(R)|\le(2/\pi)(\pi/2+2)|\log m(z)|\). Also \(|M(R)-\log R|\le C_\delta\) for \(R\ge1\), by splitting at one and using \(|\operatorname{Si}(x)-\pi/2|\le 2/x\) for \(x>0\). Thus \(|M(R_z)-\log R|\le C_{\delta,d}\) on the local window. Since \(|\Delta_z|=O(|z|)\), all constants are independent of the moving cutoffs. Combining the terms gives the finite-radius estimate
\[
 |A_R(z)-A_R(0)-\Delta_z\log R|\le C|z|,
 \qquad R\ge1,\quad |z|\le d .
\]

For all shifts there is a global bound \(|A_R(z)|\le C(1+\log R)\). In the original Haar integral, over \(u=ge^z\le1/2\) or \(u\ge2\) both half-density-weighted phase bounds \(u^{-1/2}/|u^{-1}\pm1|\) are uniformly bounded. In \(1/2\le u\le2\), use \(c=1/u-1\in[-1/2,1]\), the bounded \(F_z\), and
\[
 |S_{R_z}(c)|\le\min(2R,\ (\pi/2+2)/(\pi |c|)).
\]
Integrating this bound at \(1/R\) costs \(O(1+\log R)\). This stronger large-shift estimate also applies when \(\tau\log R\) tends to a finite positive constant. The Gaussian tail theorem in the project gives \(\mathbb P(|Z|\ge d)\le 2e^{-d^2/(8\tau)}\). On \(|Z|<d\) use \(\mathbb E|Z|\le\sqrt{2\tau}\). These estimates give the first display for the ambient part at floor zero. Taylor's theorem around zero and \(\mathbb E Z=0,\ \mathbb E Z^2=2\tau\) yield the second display.

## Polar correction and floor

For the same spatial gate, put \(A\) and \(M\) for the cold ambient and mean-zero operators and \(C_\tau=\operatorname{Tr}(S_\tau M S_\tau)-\operatorname{Tr}(S_\tau A S_\tau)\). The rank-two identity in #7646 gives
\[
 |C_\tau-C_0|\le 2\|\texttt{compactDilationAction}(w)\|\,(2\tau)^{1/4}
\]
at every \(h,L,B>0\), and also with real \(h,L\). Here \(\|(S_{2\tau}-1)e_B\|^2\le\sqrt{2\tau}\). The estimate compares the finite gated *relative* trace directly to its cold value, so a support restriction \(g\ge1\) is unnecessary. The cold finite traces of the two source branches also agree directly. For the unit constant band vector \(e_B=B^{-1/2}\mathbf1_{(0,B]}\), the normalized inverse cosine transform gives \(Ce_B(x)=\texttt{realBandKernel}(B,x)/\sqrt B\) and \(CD_g e_B(x)=\texttt{realBandKernel}(B,x/g)/\sqrt{gB}\). Thus the cold gated matrix coefficient \(\langle e_B,C^*M_{(h,L]}CD_g e_B\rangle\) is the integral of \(\texttt{realPWPolarDiagonal}(B,g,x)/\sqrt g\) on \((h,L]\). The ambient two cosines give \(\texttt{realPWBandDiagonal}(B,g,x)/\sqrt g\) on that interval. Their difference is the single-dilation scalar identified with the actual quotient trace by #7693, with continuity supplying \(g=1\). The cold polar subtraction in the limiting density is \(\min(1,g)/\sqrt g\) against \(w(g)\,dg/g\).

For \(0\le h\le L\), the two spatial masks differ by the mask on \((0,h]\). Its shifted ambient trace, uniformly in \(z\), is bounded by \(4Bh\int_I |w(g)|g^{-1/2}\,dg/g\), by the rectangular estimate of #7646. Its cold mean-zero trace is \(O(Bh)\), by the \(8Bh\) diagonal bound from #7693. Applying the triangle inequality to these two floor terms and the preceding relative trace at \(h,L\) gives the first display. The cold heat operator is the identity because the centered Gaussian of variance zero is the point mass at zero.

The spatial restriction is substantive. If \(Bh\to\rho\in(0,\infty)\), the same reasoning at bounded upper cutoff \(Bh\) removes heat from the lower mask with error tending to zero. In detail, \(A_{Bh}(z)\) is jointly continuous in \(Bh,z\) on bounded parameter sets by the finite double cosine integral; its global rectangular majorant is uniform when \(Bh\) is bounded. The rank-two estimate is also uniform. The limiting finite part then loses the sharp finite trace \(T_{0,0,\rho,1}(w)\), with band one and upper spatial cutoff \(\rho\). At \(g=1\), the mean-zero band diagonal at any \(x>0\) is four times the variance of \(t\mapsto\cos(2\pi xt)\) for \(0\le t\le1\), which is positive. Continuity gives \(T_{0,0,\rho,1}(w)>0\) for some nonnegative smooth bump supported sufficiently near one.

Finally, if \(\tau\log R\to\kappa<\infty\) and \(Bh\to0\), the heat displacement converges to \(\kappa W''(0)=\kappa(w'(1)+w''(1))\). This follows from the displayed bound and second-order Taylor expansion with dominated convergence against a fixed standard normal. A test with nonzero log curvature shows why the schedule \(\tau\log R\to0\) preserves the same finite part uniformly as a statement for smooth tests.

## Verification

The standalone Lean file uses the project and its pinned Mathlib. Its declarations check the quantitative rank correction, the two endpoint movements, uniform control of the sine integral when its scale changes, the reference integral displacement, and the factor of \(2\tau\) in the centered Gaussian remainder. The combined asymptotic estimate above is supplied as a written proof. The Python check compares the original Haar integral directly against its shifted phase integral, exercises both endpoint directions, and computes finite ambient heat and cold floor examples.

`NativeWindow.lean` identifies the Chapter 9 compact quotient convolution with the vectorwise Haar interval average, the native upper cutoff with the sharp radial mask, and their cold centered Hilbert trace with the finite part in #7693. Its final existence theorem constructs a genuine quotient Bruhat test from each such smooth real profile before the exhaustion schedule is chosen. `SeamStability.lean` checks eight bounds used in moving the Gaussian through norm one. `verification.txt` records the reported axioms and numerical consistency checks. The combined positive-variance asymptotic above is a written consequence of these identities and bounds.

To replay in a checkout of this commit with the repository’s Lean toolchain:

```sh
lake build RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalOrderZeroHeatTrace RiemannMasullo.Ch12_TraceGeometric.Sec4_RatEmptyAveragedTraceFinitePart
lake env lean -DwarningAsError=true research/7354/reciprocal-window-heat/NativeWindow.lean
lake env lean -DwarningAsError=true research/7354/reciprocal-window-heat/SeamStability.lean
python research/7354/reciprocal-window-heat/check_window.py
```

The finite quadratures use NumPy and SciPy. They exercise both directions of endpoint movement and the two ways to evaluate the Haar integral.
