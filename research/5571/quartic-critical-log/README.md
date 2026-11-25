# Quartic critical-line certificate

The 144-bit Hurwitz ledger proves **$G_\chi<0.00195327$** for the primitive Dirichlet character modulo five with $\chi(2)=i$. The same ledger and an elementary pointwise estimate on both infinite tails give **$G_\chi<0.00311647$**. The calculation bounds the critical-line logarithm at every height using a fixed grid and explicit analytic tails. [Mathematical proof](PROOF.md) · [Exact per-ledger results](RESULT.json) · [Public tail-energy theorem, #7716](https://github.com/mccorvie/riemann-masullo/pull/7716)

## Verify the published ledgers

From this directory, run the following command with standard Python and assertions enabled.

```text
python verify_both.py
```

The checker decompresses each ledger and verifies the SHA-256 of its original CSV and the quadrature program against the native receipt. It checks every quarter interval, sums the two signed half-axes, encloses the reference and both tails using rational arithmetic, and compares the totals with the claimed thresholds for that run. As controls, removing a quarter interval or reversing a contribution causes rejection, even after rehashing. Each compressed ledger is lossless. The [manifest](SHA256SUMS) identifies every other published file in this directory.

| Run | Elementary tail, all-height upper | Energy tail, all-height upper | Wall time |
|---|---:|---:|---:|
| FLINT Dirichlet jet, 104 bits and 20 terms | 0.0031165671647259 | 0.0019533676054900 | 59.375 s |
| Four-residue Hurwitz jet, 144 bits and 22 terms | 0.0031164673184146 | 0.0019532677591788 | 72.605 s |

Both runs cover 1,573,120 cells in $[-2048,2048]$. The stronger opening inequalities use the second row. Inspect the [104-bit receipt](dirichlet-2048/receipt.json), [144-bit receipt](hurwitz-2048/receipt.json), [rational verifier](verify.py) and [threshold checker](verify_both.py).

## Regenerate the function enclosures

The two measurements used CPython 3.13.9 for Windows x86-64, python-flint 0.8.0 and FLINT 3.3.1. The program uses only python-flint and the Python standard library. To reproduce that dependency in a local virtual environment on Windows, run

```powershell
py -3.13 -m venv .venv
.\.venv\Scripts\python -m pip install --require-hashes --only-binary=:all: --no-deps -r requirements-win-cp313.txt
.\.venv\Scripts\python certify.py --T 2048 --prec 104 --order 20 --fine 16 --coarse 7 --workers 4 --engine dirichlet --out replay-dirichlet
.\.venv\Scripts\python certify.py --T 2048 --prec 144 --order 22 --fine 16 --coarse 7 --workers 4 --engine hurwitz --out replay-hurwitz
.\.venv\Scripts\python verify_both.py replay-dirichlet replay-hurwitz --out replay-result.json
```

Other platforms can run the same commands with a native python-flint 0.8.0 installation. The recorded times used four single-thread workers on an AMD Ryzen 9 9950X3D and include enclosure generation, summation and reference checks through the final receipt calculation. The checker alone took under one second. [Pinned Windows wheel hash](requirements-win-cp313.txt) · [Official package release](https://pypi.org/project/python-flint/0.8.0/#files)

The source checks the period values $0,1,i,-i,-1$, conductor and character order. It also compares ordinary evaluations and jets at eight predetermined centers across both halves, including displaced evaluations. The two computations share FLINT's Hurwitz enclosure kernel. The independent arithmetic checker uses Python integers and fractions for every operation after the FLINT cell enclosures. [Quadrature](certify.py) · [Python bindings](https://github.com/flintlib/python-flint/blob/0.8.0/src/flint/types/acb_series.pyx#L524-L546) · [FLINT Dirichlet jet](https://github.com/flintlib/flint/blob/v3.3.1/src/acb_dirichlet/l_jet.c#L65-L115) · [Rigorous Hurwitz algorithm](https://arxiv.org/abs/1309.2877)
