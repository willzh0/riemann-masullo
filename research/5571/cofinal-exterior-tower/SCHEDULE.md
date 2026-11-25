# One chronological sequence for the entire tower

There is an explicit refinement of the [tower criterion](README.md) that uses one real test on one number field at each rational sampling time. Up to time $T$ it takes $T^3/3+O(T^2)$ measurements across the **entire** tower. The exponential growth rate of this one sequence equals the horizontal reach of all nontrivial unitary Hecke zeros. Within each selected upstairs packet its signed data even distinguish the individual character multiplicities at a shared zero.

## The physical test

Retain the towers $K_n$, inverse-stable packets $P_n$ and widths $a_n$, numbered $n\ge1$. Use interval radii $r_j=1/(3j\lceil\sqrt j\rceil)$. They satisfy $1/(6j^{3/2})\le r_j\le 1/(3j^{3/2})$ and $\sum r_j\le1$ by the integral test. The sum of independent centered uniform variables of these radii has a probability law supported in $[-1,1]$. Its transform is $G(w)=\prod_j\sinh(r_jw)/(r_jw)$. In $|\Re w|\le1/2$ every $j\le(|w|/12)^{2/3}$ has $r_j|w|\ge2$. The remaining factors have product bounded by $e^{1/2}$ after accounting for the bounds $e^{r_j/2}$ on every factor. Hence $|G(w)|\le C e^{-c|w|^{2/3}}$. Fourier inversion on the imaginary axis now gives a compact real smooth density $g$. As before the product has no zero off the axis. Take $h(x)=g'''(x-3)-g'(x-3)/4$. It is supported in $[2,4]$, with $M(w)=-e^{3w}w(w^2-1/4)G(w)$, including both vanishing polar moments.

Give each label $\lambda$ a known coefficient $c_\lambda$ of positive real part with $c_{\lambda^{-1}}=\bar c_\lambda$. The coefficients can be chosen linearly independent over $\mathbb Q$ inside $\mathbb C$. Assign each inversion orbit a different prime $p$ and use $\sqrt p$ as its common real part. For a two-element orbit append imaginary parts $\pm\sqrt{p'}$, where each such orbit has its own additional prime $p'$. Distinct prime square roots are linearly independent by the sign automorphisms of their multiquadratic field. Taking real and imaginary parts of any rational relation successively kills all its coefficients. Thus the complex number $\sum_\lambda c_\lambda m_\lambda$ determines the whole vector of integer multiplicities, including at coincidences. The positivity of the real parts also guarantees that this number is nonzero for every nonzero vector of nonnegative orders.

Use the angular polynomial $\sum c_\lambda\overline{\lambda(x)}$ in the radial test $B_{n,q}$ of the tower theorem. It is real by the inverse pairing. Symmetrizing the whole translated test by $x\mapsto x^{-1}$ keeps the signed sums equal, so every measurement can use a real inversion-even Bruhat test vanishing on norm-one classes. Write $Y_n(t)$ for its signed sum before the following fixed normalization and $w=\rho-1/2$. The coefficient at $e^{tw}$ is $u_w=M(w)\sum_\lambda c_\lambda m_\lambda(\rho)$.

For the actual completed function $\Lambda_\lambda$ in the project, let
$$
 J_\lambda=\tfrac12\log Q_\lambda+
      \Re\!\left(\frac{\Lambda_\lambda'}{\Lambda_\lambda}(2)
                     +\tfrac32\mathbf1_{\lambda=1}\right).
$$
Its known positive Poisson formula has terms $m_\lambda(\rho)(2-\Re\rho)/((2-\Re\rho)^2+(\Im\rho)^2)$. The kernel is at least $1/(4+(\Im\rho)^2)$. Put $H=e^2(4\|h\|_1+\|h''\|_1)$, so $(4+(\Im w)^2)|M(w)|\le H$ by two integrations by parts on $[2,4]$. Scale the test by
$$
 b_n=\big(1+H\textstyle\sum_{\lambda\in P_n}|c_\lambda|J_\lambda\big)^{-1}.
$$
This normalization uses the functions at $s=2$, away from the critical strip. It gives $\sum_w b_n|u_w|\le1$ uniformly across the tower. [Positive Poisson formula for every normalized character, including the conductor and principal corrections](https://github.com/mccorvie/riemann-masullo/pull/7669)

## The schedule and exact growth

For $k\ge2$ take $q=k+j/k^2$, $0\le j<k^2$, and assign that time only to field $K_n$ with $n=1+v_2(j+1)$. Here $v_2$ counts factors of two. Sampling times in different blocks are disjoint. Define the measured value $Y(q)=b_nY_n(q)$ at the assigned field and width. Then
$$
 \limsup_{q\to\infty}\frac{\log(1+|Y(q)|)}q
  =\sup_{F,\psi,\rho}|\Re\rho-\tfrac12|.
$$
The upper bound follows at once from the uniform normalization. For the lower bound fix a nonempty exterior in any stage $n$. Write $\sigma_n$ for its rightmost supremum. Its continuous signed growth exponent is exactly $\sigma_n$ by the [Laplace residue argument](SAMPLING.md). The following estimates give that same exponent on its assigned samples. The [Galois norm inequality](TRANSFER.md) and the exhaustive choice of the stages then give the lower bound for every originating field. If all exteriors are empty every measurement is zero.

For fixed $n$ the sampled mesh is $\Delta=2^n/k^2$ on each sufficiently late block. Splitting the transform's $e^{-c|w|^{2/3}}$ bound between a summable fixed-packet zero count and a supremum of $x^p e^{-c x^{2/3}/2}$ gives
$$
 |Y_n^{(p)}(t)|\le C_n e^{\sigma_nt}D^p (p!)^{3/2},\qquad t\ge0 .
$$
Take $p=\lfloor k/\sqrt{\log(k+2)}\rfloor$. For each $t\in[k,k+1)$ choose $p$ consecutive assigned nodes nearest to $t$, taking an end stencil if necessary. Ties can be resolved toward the smaller index. In coordinates with the first node at zero and spacing one, $t$ lies in $[-1,p]$. For each cardinal interpolation polynomial its numerator is bounded by $p^{p-1}$. The sum of the reciprocals of the absolute denominators is $2^{p-1}/(p-1)!$. Thus the sum of the absolute interpolation weights is at most $(4e)^p=e^{o(k)}$ for large $k$.

Let $I_n(t)$ be this interpolant of the unscaled samples, which are known by dividing by $b_n$. On the finite initial interval without enough nodes set it to zero. The node product in the degree $p-1$ interpolation remainder is bounded by $(p\Delta)^p$. Using $p!\ge(p/e)^p$ gives
$$
 |Y_n(t)-I_n(t)|\le 2C_n e^{\sigma_n(k+1)}
         (eD\,p^{3/2}\,2^n/k^2)^p .
$$
The logarithm of the factor in parentheses is at most $-\tfrac12\log k+O_n(1)$. Multiplication by $p$ gives a negative term of order $k\sqrt{\log k}$. Hence the error decays faster than $e^{-Ak}$ for every fixed $A>0$. These bounds also apply when the point is just outside the interpolation nodes at an end of the block. The derivative remainder uses the interval containing both the nodes and that point. The subexponential interpolation weights rule out any strict deficit in the sampled exponent relative to the continuous exponent.

## What the exact samples determine

For the same fixed stage the error $Y_n-I_n$ has an entire one-sided Laplace transform by the superexponential error estimate and local boundedness. Thus the transform of the interpolant, initially taken for $\Re z>1/2$, has the same poles and residues as $\sum_w u_w/(z-w)$ throughout the plane. Indeed the two meromorphic continuations differ by an entire function. At each selected $w$, division of the residue by $M(w)$ determines $\sum_\lambda c_\lambda m_\lambda(1/2+w)$. Rational independence gives each selected character's order at that site. This recovers the labelled exterior divisor on the measured upstairs packet. Norm pullback from a nonabelian extension can add other zeros. The proof transports a lower-field witness with its multiplicity as a lower bound.

These recovery statements use infinite exact measurements and analytic continuation. The unresolved estimate for #5571 is subexponential growth of $Y(q)$, or equivalently its vanishing at all these times.

## Exact exterior multiplicities after rounding

One may record only the nearest integer $Z(q)$ to the real normalized sample $Y(q)$, with either fixed rule for ties. Its distance from $Y(q)$ is at most $1/2$. Therefore its chronological growth exponent using $\log(1+|Z(q)|)$ is unchanged. For fixed $n$ the interpolation error contributed by rounding after division by $b_n$ is at most $(4e)^p/(2b_n)=e^{o(k)}$ on the $k$th block. Its one-sided Laplace transform is holomorphic on $\Re z>0$. Thus the interpolant of the rounded data still determines every residue in the right half-plane. At a right-hand exterior site one divides by the known nonzero Mellin sample to obtain each individual integer order as above. Reflection maps $w$ to $-\bar w$ **for the same character** and preserves its order, recovering the left exterior as well. This argument even allows arbitrary bounded additive error before rounding. It uses positive widths, so no reconstruction on the central line is required. [Same-character reflection](https://github.com/mccorvie/riemann-masullo/blob/8ee044ded1adfcda4af6f2962dc68d8e1c56b9e8/RiemannMasullo/Ch01_Introduction/Sec4_HeckePoisson.lean#L129) · [Earlier integer rounding of signed growth rates](https://github.com/mccorvie/riemann-masullo/pull/7704)

Since $|Y(q)|\le e^{q/2}$, each recorded integer has $O(q+1)$ bits. The measurements through time $T$ use $O(T^4)$ bits altogether. This is a count of data values and their sizes. It supplies neither an arithmetic algorithm for obtaining the signed measurements nor a finite bound on the observations required to decide an infinite growth rate.
