# The part of the terminal measurement that still needs an upper

Use the two true finite prime measurements of the [terminal criterion](../ADAPTIVE-WIDTHS.md#one-prescribed-terminal-sample-using-only-primes-up-to-its-square). A superscript $[V,U]$ restricts the original positive integral to $V\le v\le U$, with zero when the interval is empty. For its finite grid, assign each original cell the mass of its intersection with this interval and evaluate at the original left endpoint. The two portions of a cut cell then add to its original contribution.

Put $L=\log x,\ H=20{,}000{,}000,\ a=1/(1.0197H^2)\approx 2.45170148\cdot10^{-15}$. For both weights, both real signs and their prescribed finite grids,
$$
     {\cal A}^{[aL,L]}_\pm(x)\ll x^{1/2-31a/8}+1 .
$$
The normalized coefficient of this portion is below $0.90$ for all $x\ge2$ and below $0.00775$ for $x\ge10^{24}$. For the exponential weight, every fixed slope $a\le d\le1/100$ gives an explicit cofinal exponent below $1/2$ on $[dL,L]$. It is determined by the first verified quartic ordinate and is $0.37584553\ldots$ at $d=1/100$.

In contrast, write $\Theta=\sup_{\rho:\,L(\rho,\chi)=0}\Re\rho$ over nontrivial zeros. For the exponential weight and any $0\le V(x)=o(\log x)$,
$$
       \lim_{x\to\infty}
       \frac{\log(1+{\cal A}^{[V(x),a\log x]}_\pm(x))}{\log x}=\Theta .
$$
This also holds for the second weight $e^{-4v-v^2}$ when $V=o(\sqrt{\log x})$. No regularity is required of $V$. A cofinal bound of $x^{1/2+o(1)}$ for even one sign in this middle interval is thus equivalent to confinement of the quartic divisor. The all-height arithmetic upper on the middle interval remains open.

## An unconditional upper above a linear variance floor

For every unknown right quartic zero put $g_\rho=\gamma^2-\beta^2$. Platt gives $|\gamma|>H$. Kadiri implies $\beta\le 1-d$ through $1.01H$ with $d=1/[5.60\log(5.05H)]$. Above $1.01H$ use $\beta<1$. The inequalities
$$
   [1-1.0197(1-2d)]H^2>1,\qquad [(1.01)^2-1.0197]H^2>1
$$
imply $2(\beta-1/2)\le a g_\rho$ for every such zero. Hence $x^{\beta-1/2}e^{-vg_\rho/2}\le1$ when $v\ge aL$. Each of the other two Gaussian channels is no larger than the same majorant. The entire high right contribution relative to $\sqrt x$ is at most $(9/4)U_3(H)e^{-4aL}$, using $|M(\rho)|\le3/|\gamma|^3$. [Platt, historical verification](https://arxiv.org/pdf/1305.3087#page=14) · [Kadiri’s region](https://www.cs.uleth.ca/~kadiri/articles/explicit_zerofree_regions_for_dirichlet_l_functions.pdf#page=1) · [Absolute moments](../CUMULATIVE.md)

For the remaining unsmoothed real row the uniform bound is $(5/8+3U_3(H))\sqrt y$, including $y<1$. Its Gaussian shift costs at most $3 e^{v/8}\sqrt x$ times this constant, by integrating $e^{h/2}$ against the Gaussian positive majorant. Integration from $aL$ gives the stated $x^{1/2-31a/8}$ bound. Each finite prime cutoff and each cut grid costs $O(1)$ on every subset of the original variance interval, using the same positive omission and mesh bounds as for the whole integral. For the numerical coefficient from $10^{24}$ onward, instead apply the [weighted low-spectrum and elementary bounds](README.md) starting at zero, with the preceding upper on the high right portion. Even for the smaller asymptotic cutoff the prime omission costs at most 6 when $N\ge x^2$, and $6\sqrt{\pi}/x$ when the alternative is smaller. The existing full finite estimate covers $2\le x\le10^{24}$. [Unconditional numerical ledger](terminal-bound-receipt.txt) · [Underlying real row and finite cutoff](../ADAPTIVE-WIDTHS.md)

## The leading verified zero on that portion

This paragraph concerns $W(v)=e^{-4v}$ and its grid. Fix $d\in[a,1/100]$. Let $\gamma_0>0$ be the least absolute ordinate of the projected primary divisor of $\chi$. The 13 two-sided brackets through height 22 isolate $\gamma_0=4.1329\ldots$ and give a strict gap to the next absolute ordinate. Put
$$
 s_0=\tfrac12+i\gamma_0,\quad g_0=\gamma_0^2-\tfrac14,\quad
 b_0=-\tfrac12\{m_\chi(s_0)+m_\chi(\bar s_0)\}M(s_0),\quad
 \alpha_0(d)=\tfrac12-dg_0/2,\quad \omega_0(d)=\alpha_0(d)-4d .
$$
For each sign the continuous integral and the grid satisfy the same unconditional asymptotic
$$
 {\cal A}^{[dL,L]}_\pm(x)=
 x^{\omega_0(d)}\left\{2|b_0|\int_0^\infty e^{-(4+g_0/2)z}
  [\,\pm\cos(\gamma_0(1+d/2)L+\arg b_0+(\gamma_0/2)z)\,]_+\,dz
    +o(1)\right\}.
$$
The leading factor is a positive continuous periodic function of $L$ with positive minimum. Indeed for every initial phase each sign occurs on an interval of $z\ge0$. Explicitly, write $k=4+g_0/2,\ t=\gamma_0/2$. Either positive half-wave integrates to $2/t$ over a full period. Integrating the first period with its smallest weight gives a lower bound $4|b_0|e^{-2\pi k/t}/t>1.22\cdot10^{-18}$ for the profile, and bounding the cosine by one gives upper $2|b_0|/k<0.002529$. In particular each sign is bounded above and below by positive $d$-dependent multiples of $x^{\omega_0(d)}$. At $d=a$ the decrement from $1/2$ is $3.04389\ldots\cdot10^{-14}$. [Original projected coefficients and collision treatment](../ADAPTIVE-WIDTHS.md) · [Two-sided low roots](../low-spectrum-192.json)

To prove the formula, write $v=dL+z$. A primary exponent on the first channel has power $\beta-d(\gamma^2-\beta^2)/2$ in $x$. At $d=a$ the two ordinate bands of the preceding proof give upper $0.499971$ for every unverified primary exponent, including left-side exponents. For the first pair $\alpha_0(a)>0.49999999999997$. Their gap to the first pair increases in $d$ because $\gamma^2-\beta^2>g_0$. Every other primary critical zero in the verified window has a strictly smaller first-channel exponent because of the gap after $\gamma_0$. The second Gaussian channel always loses another $d/2$. The third has still smaller real exponent, since all $|\gamma|>2$. The high secondary zeros have exponent at most $1/2-a(H^2-1)/8<0.378$, without any assumption on their location within the strip. Their verified terms have exponent at most $1/4$. The coefficient series are absolutely summable and all their $z$-multipliers are bounded by 1 on $z\ge0$. The elementary and odd-power error after smoothing is $O(1+x^{1/3}e^{v/18})$, making its normalized $e^{-4z}$-integral $o(1)$. On this slope interval $1/3+d/18<0.334<0.415<\alpha_0(d)$. These uniform bounds allow the endpoint $(1-d)L$ to tend to infinity. A finite cutoff or cut-cell grid error is $O(1)$, whereas $\omega_0(d)>0$. Taking the real part of the surviving conjugate pair and using the Lipschitz positive part proves the formula. [True prime and secondary expansion](../QUARTIC_LINEAR_HEIGHT.md) · [Gaussian channels](../LOG-WIDTHS.md)

## Moving the frequency-isolating test

Suppose first that $\Theta>1/2$. Fix a primary zero at $\rho_0=\beta_0+i\gamma_0$ in the projected upper half-plane, with $\beta_0>1/2$. Choose $1/2<\sigma<\beta_0$. The compact positive annihilating test $P$ and divided complex test $F$ from the [original proof](../ADAPTIVE-WIDTHS.md#the-unattained-case-and-the-positive-test-in-squared-width) can be supported on $[0,B]$ for a fixed finite $B$. Their support budget is finite for this $\sigma$ by fixed-conductor zero density, irrespective of attainment. Here the test can use any fixed $B$, since $V(x)+B<\log x$ eventually. The construction also works for an attained $\Theta>1/2$.

The transform of $P$ annihilates all three variance exponents of every projected $\rho$ with $\Re\rho>\sigma$. The transform of $F$ annihilates all these exponents except $w=\rho_0^2/2$, and $|F|\le C P$. At a collision with $w$, the possible upper-half-plane divisor points are $\rho_0,\sqrt{\rho_0^2+1},\sqrt{(\rho_0^2+1)/2}$. Their real parts are distinct. The actual opposite ordinates have already been included in the projected multiplicity, and lower-half-plane variance exponents have negative imaginary part. Hence the contributor at $w$ with largest real part $\beta_*\ge\beta_0$ wins by a fixed power of $x$ whenever there are multiple contributors. [Compact test from mlyle](https://github.com/mlyle/riemann-masullo/blob/69f6639d0e53c2a04aa3b5f8487a1be237274b97/research/5571/square-prefix-fixed-window-count/README.md) · [Collision calculation](../ADAPTIVE-WIDTHS.md)

Translate both tests by $V=V(x)$. Every transform gets a factor $e^{w'V}$ at exponent $w'$, so each prescribed zero persists, and all contributors at the one retained exponent receive the same $e^{wV}$. The surviving modulus is $\gg x^{\beta_*}e^{\Re(w)V}$. On the translated support all lower primary terms total $O(x^\sigma)$ by absolute summability and $|\Phi_v|\le3$. All secondary terms total $O(\sqrt x)$ for the same reason. The elementary error is $O(1+x^{1/3}e^{(V+B)/18})$. Since $V=o(L)$, the selected modulus dominates these errors by a positive power of $x$. The inequality
$$
 2\int P(v-V)[\pm q_v(x)]_+\,dv
 \ \ge\ C^{-1}\left|\int F(v-V)q_v(x)\,dv\right|
                -\left|\int P(v-V)q_v(x)\,dv\right|
$$
therefore gives a positive lower of size $\gg x^{\beta_*}e^{\Re(w)V}$ on a bounded-width interval. To pass from $P$ to the actual ordinary integral use its fixed supremum norm. The weight $e^{-4v}$ on this interval is at least $e^{-4(V+B)}$. Letting $\beta_0$ approach $\Theta$ gives the lower logarithmic rate $\Theta$. The upper follows from the full terminal bound $O(x^\Theta)$. This proves a statement at every sufficiently large prescribed terminal, with no requirement that a rate of convergence in a compactness argument compete with $x$.

When $\Theta=1/2$, all primary zeros lie on the verified real-part line at every height. Choose $A$ sufficiently large, and evaluate at the three widths $v=V+A+4\pi k/(3\gamma_0)$, $k=0,1,2$. Their leading first-pair phases are spaced by $120$ degrees. The $e^{-v/2}$ second channel, the faster third channel and all other critical ordinates are uniformly small relative to the leading amplitude once $A$ is large. This is uniform for $V\ge0$, by the gap after $\gamma_0$ and absolute summability. The verified secondary terms are $O(x^{1/4})$. The unverified secondary terms are $O(\sqrt x\,e^{-v(H^2-1)/8})$, uniformly small relative to the first pair. The lower elementary terms are $O(1+x^{1/3}e^{v/18})$ and are negligible relative to the leading $x^{1/2}e^{-g_0 v/2}$ when $V=o(L)$. At least one witness has each sign with a fixed normalized margin. A fixed neighborhood at each witness retains half the margin by continuity of the leading cosine and the uniform absolute error bounds. Its $e^{-4v}$-weighted integral is $\gg x^{1/2}e^{-(4+g_0/2)V}$. This proves the lower logarithmic rate at $\Theta=1/2$ while allowing arbitrary locations for high zeros of the quadratic character.

In both cases $V+B<aL$ eventually, after increasing $B$ in the critical case to include the three fixed neighborhoods. The finite-prime and cut-cell errors are $O(1)$. This proves the middle-interval assertion. For the second weight, the additional factor on the witness interval is at least $e^{-(V+B)^2}$, which is $x^{-o(1)}$ if $V=o(\sqrt L)$. More generally, for any $0\le V(x)\le L$, this second weighted middle interval satisfies
$$
 \frac{\log(1+{\cal A}^{[V,aL]}_\pm(x))}{L}=(\Theta-V^2/L)_++o(1).
$$
When $V\le2\sqrt L$, the witness estimates are uniform and the extra loss beyond $e^{-V^2}$ is $e^{-O_\rho(\sqrt L)}$. For every fixed $\epsilon>0$ first choose a contributing zero with $\beta_0>\Theta-\epsilon$, or use the critical case. This gives the lower up to $\epsilon+o(1)$ wherever the proposed exponent exceeds $2\epsilon$. Else nonnegativity suffices within $2\epsilon$. For the upper on the infinite prime row, take out $e^{-V^2}$ and use the absolute $O(x^\Theta)$ integral bound for $e^{-4v}$. The finite-prime and grid errors are $O(1)$. For $V>2\sqrt L$ this already gives logarithmic rate zero, including when the cropped interval is empty. These conclusions locate the missing estimate in the true finite arithmetic, without assuming a zero-free half-plane.
