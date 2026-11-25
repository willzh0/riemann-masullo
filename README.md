# Four finite signed moments for the quartic character modulo five

Run the following command with Python 3.8 or later. It takes no arguments and uses the standard library. Compare its output with [four-coefficients.txt](four-coefficients.txt).

```sh
python check_finite.py
```

The primitive Dirichlet character takes the values $0,1,i,-i,-1$ on residues $0,1,2,3,4$. For each $1\le n\le4$, the script enumerates prime powers through the inclusive cutoff $X=25^n$, including $X=390625$ for the fourth row. In the real statistic the ramified prime 5 contributes zero. At other primes the local value is $\chi(p)$. The script computes the finite moment defined in [the prime-power Laguerre construction](https://github.com/mccorvie/riemann-masullo/pull/7703).

$$
 E_n(X)=n\sum_{p^k\le X}\frac{\Re(\chi(p)^k)}{k\,p^{2k}}
    \sum_{j=1}^n {n-1\choose j-1}\frac{(-3k\log p)^j}{j!}.
$$

The two prefixes include a leading one and the positive parts of $E_n$ and $-E_n$, respectively. For $n=4$ the sieve visits 33,291 prime powers. Exactly 16,670 have nonzero real weight.

## Interval arithmetic

All interval endpoints are integers in units of $2^{-128}$. The script rounds arithmetic and the final decimal display outwards. It splits $p=2^e y$, $1\le y<2$, to obtain $\log p=e\log2+\log y$. For $1\le y\le2$, put $u=(y-1)/(y+1)\le1/3$. The first 48 terms of $2\sum_{j\ge0}u^{2j+1}/(2j+1)$ enclose $\log y$ after adding one unit to the upper endpoint. Indeed, the omitted positive series is at most $9/[4(2\cdot48+1)3^{97}]<2^{-128}$. The same argument applies at $y=2$. Binomial coefficients, factorials, division and polynomial evaluation use integer arithmetic. The four finite enclosures can be reproduced without an $L$-function library.

The companion Lean result deduces uniform inequalities through $n=300{,}000{,}000{,}000{,}000$ from two positive-height zero verifications for this character and its inverse. This script directly enumerates the first four indices. David Platt’s verified height at conductor five is $20{,}000{,}000$. [Accepted manuscript, Theorem 9.1](https://research-information.bris.ac.uk/ws/portalfiles/portal/67056136/platt_grh3.0.pdf#page=17)

[Formal coefficient and prefix statements at the verified feature commit](https://github.com/willzh0/riemann-masullo/blob/424f9f3e9eae0e2d501cfea5b4ea626226485dd5/RiemannMasullo/Ch01_Introduction/Sec4_QuarticFiveSignedUpper.lean)
