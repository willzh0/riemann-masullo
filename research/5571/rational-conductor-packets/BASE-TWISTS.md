# Actual complete deficits across base Hecke twists

Masullo, Theorem 12.5.1.1, pp. 519–520. The averaging variable below is the **base Hecke character**. For each such character, the two auxiliary primes and their complete Jacobi classes have the meaning in #7627. The individual fixed-character upper bound remains open. [Fourth-power criterion](https://github.com/mccorvie/riemann-masullo/pull/7636) · [Complete cells](https://github.com/mccorvie/riemann-masullo/pull/7627) · [Auxiliary-pair transfer](https://github.com/mccorvie/riemann-masullo/pull/7648)

## Critical-scale bounds

Fix a number field $F$ of degree $d$ and a section-normalized unitary Hecke character $\chi$. Let $\xi$ run uniformly over primitive rational Dirichlet characters of conductor at most $C$, counted once each. Write $\psi_\xi=\chi\cdot(\widetilde\xi\circ N_{F/\mathbb Q})$. The twist is trivial on the connected positive norm section since it has finite order. The conductor parameter $C$ refers to the rational twisting characters.

Take $x_j=j^4$, $U=(J^{12},2J^{12}]\cap\mathbb P$, and any fixed ordered $u,v\in U$. A complete cell keeps the norms $n$ with prescribed Jacobi signs $(u/n),(v/n)$ and weighs them by four. Take the positive part of the true pole center $\mathbf1_{\psi_\xi=1}x_j^2/2$ minus the real first Riesz sum in that cell. Sum for $1\le j\le J$. Write $H_{\xi,u,v}(J)$ for the result, allowing even the worst choice among the four cells at each sample, depending on $\xi,u,v,j$. Let $D_{\psi_\xi}(J)$ be the unrestricted prime-only deficit of #7636. For $J,C\ge2$ and each fixed integer $k\ge1$,
$$
 \max\{\|D_{\psi_\xi}(J)\|_{2k},\,\|H_{\xi,u,v}(J)\|_{2k}\}
 \ll_{F,\chi,k}J^7\sqrt{\log(2J)}(1+J^{4k}/C^2)^{1/(2k)}. \tag{1}
$$
At $C\ge J^2$ the mean square of the actual complete deficit is $O_{F,\chi}(J^{14}\log(2J))$, uniformly for each auxiliary pair. For $C\ge J^{2k}$ the fraction of base twists for which **any** eligible ordered pair gives a deficit above $J^{7+\varepsilon}$ is
$$
 \ll_{F,\chi,k}J^{24-2k\varepsilon}\log^k(2J). \tag{2}
$$
Choose $k>12/\varepsilon$ for a power saving. If $\log C/\log J\to\infty$, the exceptional proportion is smaller than every prescribed inverse power of $J$. Already at $C\ge J^2$, applying (1) with $k=1$ under the product measure on characters and pairs gives exceptional proportion $O(J^{-2\varepsilon}\log(2J))$. Hence a proportion tending to one of base characters meets the bound on a proportion tending to one of pairs.

### The actual local factors and pole

Let $a_\chi(p^m)$ be the coefficient of $-L'/L$ at rational norm $p^m$. It is the sum of $f_v\log(p)\chi_v(\varpi_v)^{m/f_v}$ over unramified places $v\mid p$ of residue degree $f_v\mid m$, so $|a_\chi(p^m)|\le d\log p$. Let $\Delta$ contain the discriminant primes and those below the finite ramification of $\chi$. At every $p\nmid\Delta$, and everywhere when $(\operatorname{cond}\xi,\Delta)=1$,
$$
 a_{\psi_\xi}(p^m)=\xi(p^m)a_\chi(p^m).
$$
For $\xi$ unramified at $p$, a local uniformizer acquires the factor $\xi(p)^{f_v}$. If $\xi$ ramifies at $p\nmid\Delta$, each $F_v/\mathbb Q_p$ is unramified, its local norm is onto on units and the initial $\chi_v$ is unramified. The twisted Euler factor then has zero coefficient, as does $\xi(p^m)$. For arbitrary conductors each discrepancy at $p\mid\Delta$ is at most $2d\log p$ per power. This costs $O_{F,\chi}(x\log(2x))$ at a sample, or $O_{F,\chi}(J^5\log(2J))$ cumulatively, even for the fourfold masks. [Milne, *Class Field Theory*, Chapter III, Proposition 1.2](https://www.jmilne.org/math/CourseNotes/CFT.pdf#page=107)

At most $O_F(1)$ primitive labels can give a pole. Two such labels differ by a rational character whose norm pullback is trivial. This character is unramified outside the discriminant. Its $d$th power is trivial by testing scalar rational idèles, whose norm back down is their $d$th power. For each of the finitely many discriminant primes, $\mathbb Z_p^\times/(\mathbb Z_p^\times)^d$ is finite. Finite-order rational idèle class characters are determined by the finite units. These facts bound the kernel independently of $C$. Among clean conductors coprime to $\Delta$, only the primitive principal label can yield a pole, and then only when $\chi$ is principal.

There are $\gg C^2$ primitive labels. The coprime restriction also leaves $\gg_\Delta C^2$: the primitive-count function is $\phi^*=\mathrm{id}*\mu*\mu$, with $\mathrm{id}(n)=n$, hence
$$
 \sum_{\substack{q\le C\\(q,\Delta)=1}}\phi^*(q)
 =\frac{\phi(\Delta)}{2\Delta}\prod_{p\nmid\Delta}(1-p^{-2})^2 C^2
 +O_\Delta(C\log^2(2C)).
$$
Use $\sum_{n\le Y,(n,\Delta)=1}n=\phi(\Delta)Y^2/(2\Delta)+O_\Delta(Y)$ and bound the absolutely convergent double Möbius tail at $ab>C$ by $O(\log(2C)/C)$. [Project primitive-character count](https://github.com/mccorvie/riemann-masullo/pull/7473)

### Proof of (1) and (2)

At $x=x_j$ and a fixed sign cell start with prime coefficients $b_p=4\,\mathbf1_{\rm cell}(p)(x-p)_+a_\chi(p)$. The unrestricted case has weight one. Chebyshev's estimate gives $\sum|b_p|^2\ll_F x^3\log(2x)$. Write
$$
 (\sum_p b_p\xi(p))^k=\sum_{n\le x^k}B_n\xi(n).
$$
Each product admits at most $k!$ ordered prime factorizations, so $\sum|B_n|^2\le k!(\sum|b_p|^2)^k$. Apply the multiplicative large sieve over primitive Dirichlet characters at length $x^k$ and conductor cutoff $C$. Divide by the primitive count and use $q/\phi(q)\ge1$. The single-cell $2k$-norm is at most a constant times $x^{3/2}\sqrt{\log(2x)}(1+x^k/C^2)^{1/(2k)}$. For adaptive signs the $2k$th power of the maximum is bounded by the sum of the four $2k$th powers.

The true proper-power tail is $O_F(x^{3/2})$ in every cell since $\sum_{m\ge2,\,p^m\le x}\log p\ll\sqrt x$ by Chebyshev. For any of the three nonidentity cells #7627 gives $O_F(x^{4/3})$ since squares are absent. The $O_F(1)$ pole labels cost $O_F(x^2 C^{-1/k})$ in the $2k$-norm, absorbed in the displayed bound. Minkowski and $\sum_{j\le J}j^6\sqrt{\log(2j)}\ll J^7\sqrt{\log(2J)}$ give (1). Markov and $|U|^2\le4J^{24}$ give (2). [Conrey–Iwaniec–Soundararajan, multiplicative large sieve (1.5), p. 3](https://arxiv.org/pdf/1105.1176#page=3) · [Native additive sieve](https://github.com/mccorvie/riemann-masullo/pull/7472) · [Earlier character average for the theta error](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7146011837)

At every individual prime conductor $\ell>J^{4k}$ with $\ell\nmid\Delta$, average over its $\ell-2$ nonprincipal characters. Each is primitive and its newly ramified good prime rules out a pole. Orthogonality over all characters is exactly diagonal on products of primes of size $\le J^{4k}<\ell$; deleting the principal row from a nonnegative moment costs at most the denominator ratio $(\ell-1)/(\ell-2)$. Equation (1) holds here with the conductor factor replaced by an absolute constant.


## Sharp means in the rational family

Take $F=\mathbb Q$ with trivial initial character. Normalize by $J^7\sqrt{\log J}$. Both at individual prime conductors with $\log\ell/\log J\to\infty$, and over primitive conductors through $C$ with $\log C/\log J\to\infty$, the following limits hold. For the cell rows the mean also averages the two auxiliary primes uniformly. Conditioning them to be distinct has the same limit.

| Actual cumulative deficit | Limit of its normalized mean |
|---|---:|
| Unrestricted primes or unrestricted prime powers | $1/(7\sqrt{3\pi})\simeq0.0465336$ |
| One fixed nonidentity cell | $2/(7\sqrt{3\pi})\simeq0.0930671$ |
| Best of the three nonidentity cells, chosen separately at every sample | $\frac{2}{7}\sqrt{2/3}\int_0^\infty\Phi(-t)^3dt\simeq0.00976597$ |

Here $\Phi$ is the standard normal distribution function. In particular the square-root logarithm in (1) is necessary on average.

**Single prime conductor.** At $x=j^4$ put $b_p=(x-p)_+\log p$, $S_x=\sum b_p^2$. Partial summation and the prime number theorem give $S_x\sim x^3\log x/3$. For independent uniform unit-circle phases the real sum $\Re\sum b_p Z_p$, divided by $\sqrt{S_x/2}$, converges to a standard normal since $\max b_p/\sqrt{S_x}\to0$. Bounded independent summands (or their moment generating functions) also give convergence of every fixed moment. At prime level every fixed mixed moment agrees exactly with the independent phase moment once $\ell>x^r$ for its total degree $r$: a congruence of integer products is then an equality. Under the assumed growth, deleting the principal character has negligible effect even after normalization; its unrestricted raw negative part is zero. The second moment gives uniform integrability. Hence $\mathbb E(-\Re\sum b_p\xi(p))_+\sim\sqrt{S_x}/(2\sqrt\pi)\sim j^6\sqrt{\log j}/\sqrt{3\pi}$. This is uniform for $\varepsilon J\le j\le J$ by the same argument along every sequence in that range. Earlier samples cost $O(\varepsilon^7J^7\sqrt{\log J})$ by the second moment. Summation gives the first constant. Proper powers cost $O(J^7)$.

A positive proportion already has $D_\xi(J)\gg J^7\sqrt{\log J}$ at each prime $\ell>J^8$. Indeed over all characters $Y=\Re\sum b_p\xi(p)$ has mean zero, $\mathbb EY^2=S_x/2$, and $\mathbb EY^4\le2S_x^2$ by product orthogonality. Interpolation gives $\mathbb E(-Y)_+=\mathbb E|Y|/2\ge\sqrt{S_x}/8$. Summing in $j$, removing the zero raw contribution of the principal label and applying Paley–Zygmund to the cumulative deficit with its upper second moment gives the claim.

**Varying primitive conductors.** For unequal positive $m,n\le x^r$, primitive character orthogonality and Möbius inversion give
$$
 \left|\sum_{q\le C}\sum_{\xi\bmod q}^{*}\xi(m)\overline{\xi(n)}\right|
 \le\sum_{d\mid m-n}\phi(d)\lfloor C/d\rfloor
 \le C\,\tau(|m-n|).
$$
The same upper bound holds with a fixed coprimality restriction on $q$. Divide by $\gg C^2$ and normalize the weights by $\sqrt{S_x}$. The off-diagonal error in a moment of total degree $r$ is $O(x^r/C)$ since $\sum|b_p|/\sqrt{S_x}\le\sqrt x$ and $\tau(h)\le2\sqrt{|h|}$. Remove $p\le\sqrt x$ for the diagonal calculation: their normalized $L^2$ mass is $o(1)$ by the large sieve because their squared coefficient mass is $o(S_x)$. For a surviving diagonal product of at most $r$ larger primes, the chance of a common conductor factor is $O(r/\sqrt x)$, using $\sum_{q\le C,\,p\mid q}\phi^*(q)\le\sum_{k\le C/p}pk\ll C^2/p$. The absolute diagonal coefficients total at most $(r/2)!S_x^{r/2}$ for equal holomorphic and antiholomorphic degrees, and the prime-product diagonal is empty for unequal degrees. This proves moment convergence for the truncated array and distributional convergence for the full one. The possible principal pole costs $O(J^9/C^2)$ in the mean. The same reasoning applies to real linear combinations of disjoint cell sums.

**Actual complete cells.** Take $T=J^4$. For the positive weights $\gamma_p=b_p^2$, the quadratic second moment in #7627 gives $O(\log(2T)\sum b_p^4)$ for the mean square of a single Jacobi twist over the auxiliary primes, up to the separate square of the $p=2$ term. Indeed, expand $(u/p)$ in reduced additive fractions for odd $p$. The additive large sieve on the auxiliary integer interval yields $O(T^3+T^2)\sum\gamma_p^2$; division by $|U|\gg T^3/\log(2T)$ gives the bound. The third, product twist follows by conditioning on the second auxiliary prime. As $\sum b_p^4\ll x^5\log^3(2x)$, for every $\varepsilon J\le j\le J$ the four cells simultaneously have $\sum_{\rm cell} b_p^2=(1/4+o_{\mathbb P}(1))S_x$. This assertion is uniform in the choice of a single sample in the indicated range. After multiplication by four the variance of each real cell sum is $(2+o_{\mathbb P}(1))S_x$. On any sequence of such typical auxiliary pairs, disjoint prime supports give jointly independent limiting standard normals after division by $\sqrt{2S_x}$. Uniformly bounded conditional second moments control atypical pairs and allow passage to the mean of the minimum of three positive parts. Its Gaussian mean is $\int_0^\infty\Phi(-t)^3dt$. A single negative part has Gaussian mean $1/\sqrt{2\pi}$. Summation over samples, followed by the lower-order proper-power comparison, gives the two stated constants. No independence between different samples is required. [Weighted auxiliary estimate](https://github.com/mccorvie/riemann-masullo/pull/7627)

[PR #7658](https://github.com/mccorvie/riemann-masullo/pull/7658) gives the fully formal rational second-moment version for the true pole-centered complete sums with the constant $4,096,000$ in front of $(1+J^4/C^2)J^{14}\log(2J)$. Its two-level exceptional bound has constant $8,192,000$. Mlyle’s parallel [PR #7663](https://github.com/mccorvie/riemann-masullo/pull/7663) gives common exceptional sets across all prefixes at a single prime modulus for degree-one prime coefficients. Its [updated proof](https://github.com/mccorvie/riemann-masullo/pull/7663/commits/4b2999e6ed51de6690f6b12754f824e58920131a) also proves the two-sided positive-proportion statement for the actual unrestricted deficit at each large prime modulus above the eighth-power threshold, with explicit constants. [PR #7672](https://github.com/mccorvie/riemann-masullo/pull/7672) proves the rational higher moments and the single exceptional set for all auxiliary pairs and all sample-by-sample sign choices. The all-field bounds and limiting means are written mathematics. The [joint path law](BASE-TWIST-PATHS.md) determines the number-field constants, the correlations across prefixes and the typical scale even for the best of all four complete cells. An exceptional set of varying base characters may contain the same prescribed character for every $J$.
