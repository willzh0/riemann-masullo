# A finite certificate for the quartic Dirichlet character modulo 5

The primitive character with $\chi(2)=i$ has exactly **13 nontrivial zeros with $|\operatorname{Im}\rho|\le22$**. Seven have negative ordinate and six have positive ordinate. All 13 are simple and lie on $\operatorname{Re}s=1/2$. Both signs of the ordinate are evaluated for this fixed character. [Proof, including all analytic error bounds](PROOF.md)

The arithmetic inputs are the values $(0,1,i,-i,-1)$ on the five residue classes. A finite Dirichlet polynomial with 232 nonzero coefficients and largest integer 283 encloses the line values throughout $|t|\le40$, with error below $1.636\cdot10^{-24}$. It locates 31 disjoint Hardy sign changes. In eleven translated Poisson windows, two independent calculations bound the mass available for any additional zero. They certify the complete count on the smaller closed window $[-22,22]$. The separate conservative magnitude grids give 9, 60, 131 and 367 passes at the four resolutions. The proof of the zero count uses the sign brackets and the arithmetic upper bounds. [Representative numerical certificate](receipt.json)

## Replay

Python's standard library suffices to check the recorded endpoint signs, recompute the rational bracket contributions at every center, and verify both arithmetic upper bounds against the single-extra-zero cost $1/5$.

    python verify.py

To regenerate the interval enclosures and compare them with the published certificate, run the following commands in this directory. Both complete runs were checked with Python 3.13.9, python-flint 0.8.0 and FLINT 3.3.1. The generator uses Arb/Acb ball arithmetic. Its terminal Hardy signs and translated sums have independent finite elementary evaluations. [Generator](quartic5.py) · [Exact rational verifier](verify.py) · [FLINT ball arithmetic](https://flintlib.org/doc/algorithms/ball-arithmetic/overview.html)

    python -m pip install -r requirements.txt
    python -B quartic5.py --bits 160 --out run160
    python -B quartic5.py --bits 224 --out run224
    python -B verify.py run160 run224

A full run regenerates the magnitude table and the detailed interval certificate locally. The verifier checks all 40,324 consecutive comparisons, the analytic tail after squaring it in exact rational arithmetic, the two signs of every saved bracket, every translated window and the published sample values. The complete magnitude-table SHA-256 is `047a53030f5398b905fc3c77d5bd80f519b5ecd6694219513a8dbae5308c763d`.

## Reading the compact data

- Each `hardy_brackets` row is $[k,L_-,U_-,L_+,U_+]$. The bracket is $[k,k+1]/2^{24}$. The Hardy values at its ends belong to $[L_-,U_-]/10^{12}$ and $[L_+,U_+]/10^{12}$, using the elementary gamma-phase calculation.
- Each `scalars` row is $[y,L_p,U_p,L_d,U_d]$. The completed real logarithmic derivative at $2+iy$ lies in both $[L_p,U_p]/10^{10}$ from prime powers and $[L_d,U_d]/10^{10}$ from direct integer sums and the elementary digamma estimate.
- For each mesh $n$, accepted and actual strict-rise counts are listed by $k<0$ and $k\ge0$. The saved magnitude numerators use denominator $2^{n+20}$ at $k=-n^3,-6n^2,0,6n^2,n^3,n^3+1$. Every true magnitude at $t=k/n^2$ is enclosed to absolute error $2^{-n}$. The two signed line-magnitude examples are decimal enclosures in units of $10^{-14}$.
- The fields `lo`, `hi` and `digits` elsewhere denote inclusive rational endpoints in units of $10^{-\mathrm{digits}}$.

This calibrates the arithmetic comparison proposed for Theorem 12.5.1.1 at finite height for one nonreal character. The signed bound over all heights and the all-character assertion in #5571 remain open. Hiary–Ireland–Kyi §5 gives the translated argument for $\zeta$. The proof identifies its hypotheses and supplies the same-character arithmetic identity and sign computation used here. [Hiary–Ireland–Kyi, Theorem 11](https://arxiv.org/html/2408.00187v1#S5) · [Earlier 771-integer principal-character calibration](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7153778840) · [Open problem](https://github.com/mccorvie/riemann-masullo/issues/5571)
