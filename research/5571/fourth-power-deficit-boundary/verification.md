# Lean verification

The exact joint tree proves both implications for the genuine Hecke statistic. For every normalized character and $1/2\le b\le1$, absence of completed Hecke zeros in $\Re s>b$ is equivalent to $D_\chi(J)=O_\varepsilon(J^{4b+5+\varepsilon})$ for every $\varepsilon>0$. At $b=1/2$, requiring the resulting growth estimate for every normalized character of the field is equivalent to the actual all-positive-width exterior sum in Theorem 12.5.1.1, pp. 519–520. [Fixed-character theorem](https://github.com/willzh0/riemann-masullo/blob/74670690d9d37932e86bd3a4f19bcd65b688b2b0/RiemannMasullo/Ch13_ZerosHecke/FourthPowerPrimeDeficitCriterion.lean#L46) · [Exterior trace theorem](https://github.com/willzh0/riemann-masullo/blob/74670690d9d37932e86bd3a4f19bcd65b688b2b0/RiemannMasullo/Ch13_ZerosHecke/FourthPowerPrimeDeficitCriterion.lean#L65)

The forward proof subtracts the causal quadratic $(x-1)^2/2$ on $x\ge1$ in the principal case. Its Mellin symbol has an integrable vertical tail. Restoring $x^2/2$ costs $O(x)$. A fixed-strip Landau disk estimate applies to the individual Hecke function in its assumed zero-free half-plane. Mellin inversion bounds the actual first Riesz mean, the degree-one transfer costs $O_F(x^{3/2})$, and $j^4$ sampling gives the stated exponent. Mlyle’s compiled lower direction supplies the converse. The no-loss boundary upper bound, the three-case endpoint classification and the one-subsequence theorem in this directory are written proofs. [Actual first-Riesz upper theorem](https://github.com/willzh0/riemann-masullo/blob/74670690d9d37932e86bd3a4f19bcd65b688b2b0/RiemannMasullo/Ch13_ZerosHecke/HeckeRieszPerron.lean#L718) · [Mlyle’s six-module integration](https://github.com/mlyle/riemann-masullo/tree/fe3a0369549a312fade55dfffb8860882e0f16f4)

| Check | Verified result |
| --- | --- |
| Joint revision | 74670690d9d37932e86bd3a4f19bcd65b688b2b0, tree e0634cc41c397e2a9d2784638cff5c5edd4ce332 |
| Pinned toolchain | Lean 4.36.0, compiler commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9 |
| Focused, named, default Lake builds | 10,209, 19,448 and 21,290 jobs |
| Lint and changed-file warnings-as-errors | Passed |
| Global signatures | All 14,842 official base signatures preserved. The six donor files add 59, the arithmetic transfer adds 3, and the two final analytic modules add 29, for 14,933 total. |
| Axioms | All 15 new public proofs in the analytic commit and the 3 transfer roots use only propext, Classical.choice and Quot.sound. |
| Fixed-character iff proof term | 2,950 reachable project declarations, zero admissions |
| All-width iff proof term | 3,048 reachable project declarations, zero admissions |
| First-Riesz upper proof term | 2,875 reachable project declarations, zero admissions |

The only vendored project module reached by these proof terms is the general complex-analytic part of PrimeNumberTheoremAnd. Its generic Landau disk theorem was already present in the October 20 source. [October source, FinalBound](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/StrongPNT.lean#L1024)

[Upstream PR #7628](https://github.com/mccorvie/riemann-masullo/pull/7628) supplies five independent modules at 8defb6bb3a8a5254b0b498d4ac4c0365e2403c83. They prove boundary-series extraction, a complex-power discretization bound, the Lipschitz log-grid estimate, the finite uniform-convolution tail bound and the degree-one sampling bound. The named and default builds completed 19,438 and 21,280 jobs. Its eight public proofs use the three standard axioms; all 14,842 base signatures were preserved, with 10 additions. [Upstream CI verdict](https://github.com/mccorvie/riemann-masullo/actions/runs/45556945476/job/139011165509)

To rebuild the joint tree with its pinned dependencies, run the following in that checkout.

~~~sh
lake build RiemannMasullo.Ch13_ZerosHecke.FourthPowerPrimeDeficitCriterion
lake build RiemannMasullo Challenge Main
lake build
bash scripts/lint.sh
~~~

## Upstream placement and CI

The fixed-character criterion and the all-width exterior trace equivalence are now submitted together in upstream PR #7636 at `c0eed8bfceaf9da3eb96016967760da98af3f919`. The global theorem lives in the Chapter 12 isolation file, with the identical proposition hash `4100885192`. The fixed-character result stays in Chapter 13. The earlier joint revision `74670690` remains available as a historical fork integration. [Upstream #7636](https://github.com/mccorvie/riemann-masullo/pull/7636) · [Isolated theorem](https://github.com/willzh0/riemann-masullo/blob/c0eed8bfceaf9da3eb96016967760da98af3f919/RiemannMasullo/Ch12_TraceGeometric/Sec5_Isolated.lean#L310) · [Fixed-character theorem](https://github.com/willzh0/riemann-masullo/blob/c0eed8bfceaf9da3eb96016967760da98af3f919/RiemannMasullo/Ch13_ZerosHecke/FourthPowerPrimeDeficitCriterion.lean#L46)

The exact head passed the scoped build (10,211 jobs), named build (19,448), default build (21,290), repository lint and the three-axiom check. It preserved all 14,842 upstream signatures and all 14,901 on the joined donor revision. The private localization definition retains type hash `3612427113` and body hash `2561026364`. The theorem relocation also removes one unused private notation, giving 14,932 signatures over 595 modules. The two proof closures have zero admissions among 2,950 and 3,048 project declarations. A private proof-term traversal from all 64 public theorem roots in the ten added modules and the isolated equivalence found no matches in the project’s source-attribution registry for November RH work. Upstream’s automated review returned the successful `read` verdict. [Upstream CI](https://github.com/mccorvie/riemann-masullo/actions/runs/45559544939/job/139019662951) · [Five-file change above mlyle’s joined donor](https://github.com/willzh0/riemann-masullo/compare/fe3a0369549a312fade55dfffb8860882e0f16f4...c0eed8bfceaf9da3eb96016967760da98af3f919)
