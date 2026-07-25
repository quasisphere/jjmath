# Calderón--Zygmund Kernels and $L^p$ Singular Integrals

The harmonic-analysis layer is intended to be independent of the
quasiconformal application. Its first target is the classical route from a
translation-invariant singular kernel to bounded operators on $L^p$:

$$
  \text{kernel estimates}
  \Longrightarrow \text{weak type }(1,1)
  \Longrightarrow \text{strong }L^q
  \Longrightarrow \text{complex interpolation}.
$$

The Beurling transform will be the first substantial consumer, but the kernel
and interpolation APIs should also apply to Riesz transforms and other
Euclidean convolution operators.

## Standard kernel conditions

Let $X$ be a normed additive group, let $E$ be a normed target, and let
$K:X\to E$. In dimension $d$, the two basic pointwise estimates are

$$
  |K(x)|\leq \frac{C_0}{|x|^d},
  \qquad
  |K(x-h)-K(x)|
    \leq C_1\frac{|h|}{|x|^{d+1}}
    \quad\text{when }2|h|\leq|x|.
$$

The formal predicates record exactly these formulas. Cancellation is kept as
a separate condition: on every centered annulus $a<|x|<b$, the kernel is
integrable and has integral zero. Keeping the three inputs separate makes it
clear which part of a later singular-integral proof uses size, regularity, or
cancellation.


@include{lean:JJMath.HarmonicAnalysis.HasKernelFirstDifference}


The first-difference estimate is usually used after translating a bad cube or
ball to its center. If $2|y-c|\leq|x-c|$, then

$$
  |K(x-y)-K(x-c)|
    \leq C_1\frac{|y-c|}{|x-c|^{d+1}}.
$$

@include{lean:JJMath.HarmonicAnalysis.HasKernelFirstDifference.sub_sub_le}

## The Beurling kernel

On the complex plane, the physical kernel of the Beurling transform is

$$
  K(z)=-\frac{1}{\pi z^2}.
$$

Its size is exactly $1/(\pi|z|^2)$. For the first difference, write
$u=z-h$ and factor

$$
  u^{-2}-z^{-2}
    =(u^{-1}-z^{-1})(u^{-1}+z^{-1}).
$$

When $2|h|\leq|z|$, the reverse triangle inequality gives
$|u|\geq|z|/2$. Hence

$$
  |u^{-1}-z^{-1}|\leq\frac{2|h|}{|z|^2},
  \qquad
  |u^{-1}+z^{-1}|\leq\frac3{|z|},
$$

which yields the standard bound

$$
  |K(z-h)-K(z)|
    \leq\frac6\pi\frac{|h|}{|z|^3}.
$$

@include{lean:JJMath.Quasiconformal.norm_planarBeurlingKernel}

@include{lean:JJMath.Quasiconformal.norm_planarBeurlingKernel_sub_le}


@include{lean:JJMath.Quasiconformal.planarBeurlingKernel_hasKernelFirstDifference}

## Fourier cancellation and polar annuli

Every nonconstant integer Fourier mode has zero average over a full period:

$$
  \int_a^{a+2\pi} e^{in\theta}\,d\theta=0
  \qquad(n\in\mathbb Z\setminus\{0\}).
$$

The proof is elementary but reusable: integrate
$(e^{in\theta})'=in e^{in\theta}$ and use periodicity. We record both the
standard interval and its translated form.



The planar polar-coordinate formula is likewise kept independent of any
particular kernel. For a function with values in a real normed vector space,

$$
  \int_{a<|z|<b}F(z)\,dz
    =\int_{(a,b)\times(-\pi,\pi)}
       rF(re^{i\theta})\,dr\,d\theta,
  \qquad a>0.
$$


The same change of variables is available outside a disk. In particular,
the decay exponent appearing in a planar first-difference estimate has the
exact integrable tail

$$
  \int_{|z-c|>a}|z-c|^{-3}\,dz=\frac{2\pi}{a},
  \qquad a>0.
$$

@include{lean:JJMath.HarmonicAnalysis.setIntegral_exterior_eq_polar}

@include{lean:JJMath.HarmonicAnalysis.integrableOn_norm_sub_inv_cube_exterior}

@include{lean:JJMath.HarmonicAnalysis.setIntegral_norm_sub_inv_cube_exterior}

For the Beurling kernel the polar integrand factors as a radial term times
$e^{-2i\theta}$. The Fourier-mode theorem therefore proves cancellation,
while continuity away from zero proves integrability on every annulus.



## From kernels to operators

The operator layer starts with the inner radial cutoff

$$
  K_\varepsilon(y)=\mathbf 1_{\{|y|>\varepsilon\}}K(y)
$$

and its convolution through an arbitrary continuous bilinear pairing. The
same module records annular truncations and proves that an annularly
cancelling kernel remains integrable and has integral zero after such a
cutoff.





For the Beurling kernel, a positive inner cutoff removes the only pole and
leaves a measurable function bounded by $1/(\pi\varepsilon^2)$. It is
therefore locally integrable, and its convolution with every smooth compactly
supported function is absolutely convergent at every point:

$$
  \mathcal S_\varepsilon g(x)
    =\int_{|y|>\varepsilon}-\frac{g(x-y)}{\pi y^2}\,dy.
$$





The Fourier definition and the physical kernel are now connected away from
the support of the input. If $x\notin\operatorname{supp}g$, differentiation
under the Cauchy integral has no singularity and gives

$$
  \partial_z\mathcal Cg(x)
    =\int_{\mathbb C}-\frac{g(w)}{\pi(x-w)^2}\,dw.
$$

Since $\partial_z\mathcal Cg=\mathcal Sg$ almost everywhere, this proves the
off-support representation used in the Calderón--Zygmund argument.

@include{lean:JJMath.Quasiconformal.hasFDerivAt_cauchyTransform_of_not_mem_tsupport}

@include{lean:JJMath.Quasiconformal.frechetDZValue_cauchyTransform_eq_kernelIntegral_of_not_mem_tsupport}

@include{lean:JJMath.Quasiconformal.beurlingTransformL2_eq_kernelIntegral_ae_off_tsupport}

Weak and strong operator estimates are recorded independently of kernels.
Weak type $(1,1)$ uses the division-free distribution inequality

$$
  \lambda\,\mu\{x:|Tf(x)|\geq\lambda\}
    \leq C\int|f|,
$$

while strong type $(p,p)$ uses the extended $L^p$ seminorm. This keeps the
generic interpolation and decomposition layers independent of the Beurling
application.

@include{lean:JJMath.HarmonicAnalysis.distributionFunction}




The first integrated bad-part estimate is complete. If $|y-c|\leq r$, then
the first-difference condition and the inverse-cube integral give

$$
  \int_{|x-c|>2r}|K(x-y)-K(x-c)|\,dx\leq\pi C_1.
$$

@include{lean:JJMath.HarmonicAnalysis.HasKernelFirstDifference.setIntegral_norm_sub_sub_exterior_le}

For an integrable function $b$ supported in $|y-c|\leq r$, the product
majorant

$$
  Cr|x-c|^{-3}|b(y)|
$$

is integrable on $\{|x-c|>2r\}\times\mathbb C$. Fubini therefore upgrades
the pointwise kernel estimate to

$$
  \int_{|x-c|>2r}
    \left|\int_{\mathbb C}
      \bigl(K(x-y)-K(x-c)\bigr)b(y)\,dy\right|\,dx
    \leq\pi C\|b\|_1.
$$

@include{lean:JJMath.HarmonicAnalysis.HasKernelFirstDifference.setIntegral_norm_integral_sub_sub_mul_le}

If $b$ has mean zero, subtracting the constant $K(x-c)$ does not change its
kernel integral. The preceding bound is consequently available directly for
the ordinary convolution of every mean-zero bad piece:

$$
  \int_{|x-c|>2r}
    \left|\int_{\mathbb C}K(x-y)b(y)\,dy\right|\,dx
    \leq\pi C\|b\|_1.
$$

@include{lean:JJMath.HarmonicAnalysis.integral_kernel_mul_eq_integral_sub_sub_mul_of_integral_eq_zero}


@include{lean:JJMath.HarmonicAnalysis.HasKernelFirstDifference.setIntegral_norm_integral_mul_le_of_integral_eq_zero}

For finitely many bad pieces, restrict to the region outside every doubled
support disk and use the triangle inequality. The per-piece bounds add with
no loss:

$$
  \int_{|x-c_i|>2r_i\ \forall i}
    \left|\sum_i\int_{\mathbb C}K(x-y)b_i(y)\,dy\right|\,dx
    \leq\pi C\sum_i\|b_i\|_1.
$$


## The dyadic grid for the decomposition

The planar decomposition will use the standard half-open dyadic squares

$$
  Q_{n,k}=
  [k_1 2^n,(k_1+1)2^n)\times
  [k_2 2^n,(k_2+1)2^n),
  \qquad n\in\mathbb Z,\quad k\in\mathbb Z^2.
$$

@include{lean:JJMath.HarmonicAnalysis.dyadicSquare}

At every scale, the floor of the two rescaled coordinates selects the unique
square containing a point. Consequently the squares are measurable,
pairwise disjoint, and cover the plane. Their exact area is $(2^n)^2$.

@include{lean:JJMath.HarmonicAnalysis.mem_dyadicSquare_iff_dyadicIndex_eq}



@include{lean:JJMath.HarmonicAnalysis.volume_dyadicSquare}

For the physical-space kernel estimate, each square is also placed inside a
closed disk centered at its lower-left corner with radius twice its side
length. This deliberately non-sharp radius keeps the stopping-time geometry
simple and changes only an absolute constant in the eventual exceptional-set
bound.

@include{lean:JJMath.HarmonicAnalysis.dyadicSquare_subset_closedBall_dyadicCorner}

Every square lies in its uniquely determined parent, whose side length is
twice as large and whose area is four times as large. More generally,
intersecting dyadic squares are nested: the square at the finer scale lies in
the square at the coarser scale.

@include{lean:JJMath.HarmonicAnalysis.dyadicSquare_subset_parent}

@include{lean:JJMath.HarmonicAnalysis.volume_dyadicSquare_parent_toReal}

@include{lean:JJMath.HarmonicAnalysis.dyadicSquare_subset_of_le_of_inter_nonempty}

Consequently, for any property of dyadic squares, distinct inclusion-maximal
squares with that property are disjoint. If the property fails at every
sufficiently coarse scale, each square having the property is contained in a
maximal one.

@include{lean:JJMath.HarmonicAnalysis.IsMaximalDyadicSquare}

@include{lean:JJMath.HarmonicAnalysis.pairwiseDisjoint_maximalDyadicSquare}

@include{lean:JJMath.HarmonicAnalysis.exists_maximalDyadicSquare_superset}

For an integrable normed-space-valued function $f$ and a level $\alpha>0$, a
square $Q$ is declared bad when

$$
  \alpha |Q|<\int_Q\|f(x)\|\,dx.
$$

@include{lean:JJMath.HarmonicAnalysis.IsBadDyadicSquare}

Integrability rules out bad squares at all sufficiently coarse scales,
because their areas tend to infinity while their integrals remain bounded by
$\|f\|_1$. Thus every bad square is covered by a maximal bad square. The
maximal family is countable, measurable, and pairwise disjoint, and its union
is exactly the union of all bad squares.

@include{lean:JJMath.HarmonicAnalysis.Integrable.exists_coarse_scale_not_isBadDyadicSquare}

@include{lean:JJMath.HarmonicAnalysis.IsBadDyadicSquare.exists_maximal_superset}

@include{lean:JJMath.HarmonicAnalysis.badDyadicRegion_eq_maximalBadDyadicRegion}

Maximality also makes the parent of a selected square non-bad. Since a parent
has four times the area of its child, every maximal bad square satisfies the
two-sided average estimate

$$
  \alpha |Q|<\int_Q\|f(x)\|\,dx\leq4\alpha |Q|.
$$

@include{lean:JJMath.HarmonicAnalysis.setIntegral_norm_le_four_mul_level_mul_volume_of_mem_maximalBadDyadicSquares}

The remaining pointwise covering follows from Lebesgue differentiation. A
square containing $z$ lies in the centered disk of radius four times its side
length, whose area is $16\pi$ times the square's area. The ball
differentiation theorem therefore squeezes the mean oscillation of $f$ on the
point-selected dyadic squares to zero.

@include{lean:JJMath.HarmonicAnalysis.dyadicAverage_norm_sub_le_closedBallAverage}

@include{lean:JJMath.HarmonicAnalysis.ae_tendsto_dyadicAverage_norm_sub}

Hence almost every point with $\|f(z)\|>\alpha$ belongs to a bad square.
Countable additivity over the disjoint maximal family also gives the standard
exceptional-region estimate

$$
  \alpha\left|\bigcup_{Q\,\mathrm{maximal\ bad}}Q\right|
  \leq\|f\|_1.
$$

@include{lean:JJMath.HarmonicAnalysis.ae_mem_badDyadicRegion_of_lt_norm}

@include{lean:JJMath.HarmonicAnalysis.level_mul_volume_maximalBadDyadicRegion_le_integral_norm}

## Good and bad pieces

For each maximal square $Q$, subtract the vector average on $Q$ and extend
by zero:

$$
  b_Q(x)=\mathbf 1_Q(x)
    \left(f(x)-\fint_Qf(y)\,dy\right).
$$

This is an integrable function supported in $Q$, its integral is zero, and
its $L^1$ cost is at most twice the mass of $f$ on $Q$.

@include{lean:JJMath.HarmonicAnalysis.calderonZygmundBadPart}

@include{lean:JJMath.HarmonicAnalysis.integral_calderonZygmundBadPart_eq_zero}

@include{lean:JJMath.HarmonicAnalysis.integral_norm_calderonZygmundBadPart_le}

Pairwise disjointness makes the family pointwise summable: at any point at
most one bad piece is nonzero. Define

$$
  b=\sum_Q b_Q,
  \qquad g=f-b.
$$

Then $f=g+b$ exactly. Off the bad region one has $g=f$, while on $Q$ the
good part is the constant vector average $f_Q$. Both $b$ and $g$ are
integrable, and the total $L^1$ mass of the individual bad pieces satisfies

$$
  \sum_Q\|b_Q\|_1\leq2\|f\|_1.
$$

@include{lean:JJMath.HarmonicAnalysis.calderonZygmundBadSum}

@include{lean:JJMath.HarmonicAnalysis.calderonZygmundGoodPart}

@include{lean:JJMath.HarmonicAnalysis.calderonZygmundGoodPart_add_badSum}

@include{lean:JJMath.HarmonicAnalysis.tsum_integral_norm_calderonZygmundBadPart_le}

Maximality bounds every selected average by $4\alpha$, and dyadic
differentiation bounds $f$ by $\alpha$ almost everywhere off the bad region.
Consequently

$$
  \|g\|_\infty\leq4\alpha,
  \qquad
  \|g\|_1\leq\|f\|_1,
  \qquad
  \int\|g\|^2\leq4\alpha\|f\|_1.
$$

@include{lean:JJMath.HarmonicAnalysis.ae_norm_calderonZygmundGoodPart_le}

@include{lean:JJMath.HarmonicAnalysis.integral_norm_calderonZygmundGoodPart_le}

@include{lean:JJMath.HarmonicAnalysis.integral_norm_sq_calderonZygmundGoodPart_le}

The energy statement is also available in the exact form needed by an
$L^2$ operator.  The good part belongs to $L^2$ whenever $alpha>0$; if the
original function is additionally in $L^2$, then so does the total bad part.

@include{lean:JJMath.HarmonicAnalysis.memLp_two_calderonZygmundGoodPart}

@include{lean:JJMath.HarmonicAnalysis.memLp_two_calderonZygmundBadSum}

## Countable exterior aggregation

The finite tail estimate extends to a countable family whenever the $L^1$
norms are summable. The analytic bridge is an absolute-convergence theorem:
summability of the integrated norms gives pointwise absolute summability
almost everywhere and an integrable pointwise vector sum. Applying this to
the kernel convolutions gives

$$
  \int_{|x-c_i|>2r_i\ \forall i}
    \left|\sum_i\int K(x-y)b_i(y)\,dy\right|\,dx
  \leq\pi C\sum_i\|b_i\|_1.
$$

@include{lean:JJMath.HarmonicAnalysis.ae_summable_norm_of_summable_integral_norm}

@include{lean:JJMath.HarmonicAnalysis.integrable_tsum_of_summable_integral_norm}

@include{lean:JJMath.HarmonicAnalysis.HasKernelFirstDifference.setIntegral_norm_tsum_integral_mul_le_of_integral_eq_zero}

For a maximal dyadic square of side $2^n$, use its lower-left corner and the
support radius $r_Q=2^{n+1}$. The square lies in
$\overline B(c_Q,r_Q)$. The enlarged exceptional region is

$$
  \Omega^*=\bigcup_Q\overline B(c_Q,2r_Q).
$$

Each doubled disk has area $16\pi|Q|$, so

$$
  \alpha|\Omega^*|\leq16\pi\|f\|_1.
$$

The countable tail theorem and the bound for the total bad-piece mass now
give the concrete estimate

$$
  \int_{(\Omega^*)^c}
    \left|\sum_Q\int K(x-y)b_Q(y)\,dy\right|\,dx
  \leq2\pi C\|f\|_1.
$$

@include{lean:JJMath.HarmonicAnalysis.enlargedMaximalBadDyadicRegion}

@include{lean:JJMath.HarmonicAnalysis.level_mul_volume_enlargedMaximalBadDyadicRegion_le}

@include{lean:JJMath.HarmonicAnalysis.HasKernelFirstDifference.setIntegral_norm_tsum_badPart_le}

## The Fourier-side weak-type bridge

The good contribution is now complete.  Since the Beurling transform is an
$L^2$ isometry,

$$
  \|\mathcal Sg\|_2^2\leq4\alpha\|f\|_1,
$$

and the $L^2$ Chebyshev inequality gives the corresponding superlevel-set
estimate.  For inputs in $L^1\cap L^2$, linearity also gives the exact
identity $\mathcal Sf=\mathcal Sg+\mathcal Sb$ in $L^2$.

@include{lean:JJMath.Quasiconformal.norm_beurlingTransformL2_goodPart_sq_le}

@include{lean:JJMath.Quasiconformal.beurlingTransformL2_goodPart_superlevel}

@include{lean:JJMath.Quasiconformal.beurlingTransformL2_goodPart_add_badSum}

To extend the physical-kernel representation from smooth test functions to a
rough bad piece supported in $\overline B(c,r)$, global smooth density is not
enough: approximants must remain separated from the exterior
$|x-c|>2r$.  A fixed cutoff equal to one on the support of the bad piece and
supported in $\overline B(c,3r/2)$ gives, for every $\varepsilon>0$, a test
function $\varphi$ with

$$
  \operatorname{supp}\varphi\subseteq\overline B(c,3r/2),
  \qquad \|b-\varphi\|_2\leq\varepsilon.
$$

@include{lean:JJMath.Quasiconformal.intermediateDiskCutoff}

@include{lean:JJMath.Quasiconformal.exists_planeTestFunction_eLpNorm_sub_le_tsupport_subset_intermediateDisk}

The separated physical-kernel estimate is now complete.  The new polar input
is the inverse-fourth-power tail bound

$$
  \int_{|z-c|>a}|z-c|^{-4}\,dz\leq\frac{2\pi}{a^2}.
$$

If $h$ is supported in $D=\overline B(c,3r/2)$, the elementary separation
$|x-w|^{-1}\leq4|x-c|^{-1}$ for $|x-c|>2r$ gives

$$
  |\mathcal Kh(x)|
    \leq16\pi^{-1}|x-c|^{-2}\|h\|_1.
$$

After squaring and integrating, Hölder's estimate
$\|h\|_1^2\leq|D|\|h\|_2^2$ yields

$$
  \int_{|x-c|>2r}|\mathcal Kh(x)|^2\,dx
  \leq
  (16\pi^{-1})^2|D|\frac{2\pi}{(2r)^2}\|h\|_2^2.
$$

@include{lean:JJMath.HarmonicAnalysis.setIntegral_norm_sub_inv_four_exterior_le}

@include{lean:JJMath.Quasiconformal.norm_beurlingKernelIntegral_le_of_support_intermediateDisk_of_mem_exterior}

@include{lean:JJMath.Quasiconformal.integral_norm_sq_le_volume_mul_integral_norm_sq_of_memLp_two_of_support_closedBall}

@include{lean:JJMath.Quasiconformal.setIntegral_norm_sq_beurlingKernelIntegral_le_of_memLp_two_of_support_intermediateDisk}

The passage to rough data is now complete.  For a compactly supported
$h\in L^2$, choose the support-controlled test approximants above.  Their
Fourier-side Beurling transforms converge in $L^2$, hence in measure.  The
separated estimate makes the physical kernel integrals converge in $L^2$ on
the doubled exterior.  Since the two approximating sequences agree almost
everywhere there by the smooth off-support formula, uniqueness of limits in
measure gives

$$
  \mathcal Sh(x)=\int_{\mathbb C}-\frac{h(w)}{\pi(x-w)^2}\,dw
  \quad\text{for almost every }|x-c|>2r.
$$

@include{lean:JJMath.Quasiconformal.beurlingTransformL2_eq_kernelIntegral_ae_exterior_of_memLp_two_of_support_closedBall}

To pass this identity through the countable bad sum, exhaust the maximal bad
squares by finite families $\mathcal F_n$ and put
$b^{(n)}=\sum_{Q\in\mathcal F_n}b_Q$. Pairwise disjointness gives the useful
pointwise domination $|b^{(n)}|\leq|b|$. Thus the partial sums converge to
$b$ in $L^2$, while the integrated first-difference estimate makes the
corresponding physical kernel sums converge in $L^1((\Omega^*)^c)$.

@include{lean:JJMath.Quasiconformal.norm_calderonZygmundBadPartialSum_le}

@include{lean:JJMath.Quasiconformal.calderonZygmundBadPartialSum_sub_badSum_eLpNorm_tendsto}

@include{lean:JJMath.Quasiconformal.beurlingKernelIntegral_badPart_ae_summable_compl_enlarged}

@include{lean:JJMath.Quasiconformal.beurlingKernelIntegral_badPartialSum_eLpNorm_one_tendsto}

For every finite family, linearity and the rough one-piece formula identify
the Fourier and physical sums on the common exterior.

@include{lean:JJMath.Quasiconformal.beurlingTransformL2_badPartialSum_eq_kernelIntegral}

The Fourier sums converge in measure to $\mathcal Sb$ and the physical sums
converge in measure to the kernel series. Uniqueness of the limit now gives
the countable off-support formula

$$
  \mathcal Sb(x)=\sum_Q\int_{\mathbb C}
    -\frac{b_Q(w)}{\pi(x-w)^2}\,dw
  \quad\text{for almost every }x\in(\Omega^*)^c.
$$

@include{lean:JJMath.Quasiconformal.beurlingTransformL2_badSum_eq_tsum_kernelIntegral_ae_compl_enlarged}

The weak-type step is now purely distributional. For a finite positive
threshold $t$, make the Calderón--Zygmund decomposition at level $t$. Up to a
null set, the $t$-superlevel set of $\mathcal Sf=\mathcal Sg+\mathcal Sb$ is
contained in the union of

- the enlarged bad region $\Omega^*$;
- the $t/2$-superlevel set of $\mathcal Sg$;
- the $t/2$-superlevel set of $\mathcal Sb$ outside $\Omega^*$.

The exceptional-region estimate contributes $16\pi\|f\|_1$. The good-part
$L^2$ estimate and Chebyshev contribute $16\|f\|_1$. On the exterior, the
physical series is integrable, its $L^1$ norm is at most $12\|f\|_1$, and
Markov at threshold $t/2$ contributes $24\|f\|_1$.

@include{lean:JJMath.HarmonicAnalysis.HasKernelFirstDifference.integrableOn_tsum_badPart}

@include{lean:JJMath.Quasiconformal.ofReal_level_mul_volume_beurlingTransformL2_goodPart_superlevel_half_le}

@include{lean:JJMath.Quasiconformal.ofReal_level_mul_restrict_compl_enlarged_volume_beurlingTransformL2_badSum_superlevel_half_le}

Adding the three pieces gives, for $f\in L^1\cap L^2$,

$$
  t\,\bigl|\{z:t\leq|\mathcal Sf(z)|\}\bigr|
    \leq (40+16\pi)\int_{\mathbb C}|f(z)|\,dz.
$$

@include{lean:JJMath.Quasiconformal.beurlingTransformL2_distribution_le_lintegral_of_integrable_memLp_two}

## Beginning the $L^1$ extension

The weak estimate already contains the continuity needed for density. In
general, if

$$
  t\,|\{|F_i|\geq t\}|\leq C m_i,
  \qquad m_i\longrightarrow0,
$$

with $C<\infty$, division by a fixed finite $t>0$ shows that $F_i\to0$ in
measure.

@include{lean:JJMath.HarmonicAnalysis.tendstoInMeasure_zero_of_weak_distribution_bound}

For the Beurling transform this says that $f_i\to0$ in $L^1$, with every
$f_i\in L^1\cap L^2$, implies $\mathcal Sf_i\to0$ in measure. Applying this
to the two-parameter family $f_n-f_m$ gives the global Cauchy estimate

$$
  \|f_n-f_m\|_1\longrightarrow0
  \quad\Longrightarrow\quad
  \mathcal Sf_n-\mathcal Sf_m\longrightarrow0
  \text{ in measure}.
$$

@include{lean:JJMath.Quasiconformal.beurlingTransformL2_tendstoInMeasure_zero_of_eLpNorm_one_tendsto_zero}

@include{lean:JJMath.Quasiconformal.beurlingTransformL2_cauchyInMeasure_of_eLpNorm_one_cauchy}

There is also now a fixed approximating sequence for every
$f\in L^1(\mathbb C)$. Replace $f$ on a null set by a measurable
representative and take its standard finite-valued range approximations.
They are integrable simple functions, hence belong to every finite $L^p$;
in particular,

$$
  f_n\in L^1\cap L^2,
  \qquad \|f_n-f\|_1\longrightarrow0.
$$

@include{lean:JJMath.Quasiconformal.integrableSimpleApproximation}

@include{lean:JJMath.Quasiconformal.memLp_two_integrableSimpleApproximation}

@include{lean:JJMath.Quasiconformal.eLpNorm_one_integrableSimpleApproximation_sub_tendsto_zero}

@include{lean:JJMath.Quasiconformal.beurlingTransformL2_integrableSimpleApproximation_cauchyInMeasure}

The required completeness statement is now available independently of the
Beurling transform. Select a subsequence so that the measure of

$$
  \{|F_{n_{k+1}}-F_{n_k}|\geq2^{-k}\}
$$

is at most $2^{-k}$. Borel--Cantelli makes the consecutive differences
summable pointwise almost everywhere, and completeness of the target gives
an almost-everywhere limit. On a finite-measure space, convergence of that
subsequence in measure combines with the original two-parameter Cauchy
estimate to recover convergence in measure of the whole sequence.

@include{lean:JJMath.exists_strictMono_tendsto_ae_of_cauchyInMeasure}

@include{lean:JJMath.tendstoInMeasure_of_cauchyInMeasure_of_subseq_ae}


Fixed scalar multiplication also preserves convergence in measure, by
rescaling every positive threshold by the norm of the scalar.

@include{lean:JJMath.tendstoInMeasure_const_smul}

For an integrable planar function, apply this construction to the transforms
of the canonical simple approximants. It produces a measurable candidate
$G_f$ and full convergence in measure to $G_f$ on every closed disk.

@include{lean:JJMath.Quasiconformal.integrableBeurlingLimit}

@include{lean:JJMath.Quasiconformal.integrableBeurlingApproximation_tendstoInMeasure_restrict_closedBall}

If $f=g$ almost everywhere, the two simple approximation sequences approach
one another in $L^1$. Their transforms therefore approach one another in
measure, and diskwise uniqueness gives $G_f=G_g$ almost everywhere. Thus the
construction descends to a map from $L^1(\mathbb C)$ into measurable
functions modulo null sets.

@include{lean:JJMath.Quasiconformal.integrableBeurlingLimit_congr_ae}

@include{lean:JJMath.Quasiconformal.beurlingTransformL1}

There is no ambiguity on the old domain. If
$f\in L^1\cap L^2$, the same simple approximants converge to $f$ in $L^2$.
The $L^2$ isometry makes their transforms converge in measure to the original
Fourier multiplier, while they converge locally in measure to $G_f$.
Uniqueness on the disk exhaustion gives

$$
  G_f=\mathcal Sf\quad\text{almost everywhere}.
$$

@include{lean:JJMath.Quasiconformal.beurlingTransformL1_ae_eq_beurlingTransformL2}

Although the canonical range approximation is not itself exactly linear, it
is asymptotically linear in $L^1$. Restricted continuity in measure and
diskwise uniqueness therefore make the resulting extension exactly additive
and complex homogeneous.

@include{lean:JJMath.Quasiconformal.integrableBeurlingLimit_add}

@include{lean:JJMath.Quasiconformal.integrableBeurlingLimit_const_smul}


It remains important not to lose a factor when passing the weak estimate to
the limit. The general limit theorem uses a lower threshold $at$, with
$0<a<1$. Almost-everywhere convergence puts the $t$-superlevel set of the
limit inside the eventual $at$-superlevel set of the approximants. Tail
intersections, continuity of measure from below, convergence of the
controlling masses, and finally $a\uparrow1$ preserve the original constant.

@include{lean:JJMath.HarmonicAnalysis.weak_distribution_bound_of_tendsto_ae}

The canonical simple approximants have convergent $L^1$ masses, so the
extended transform inherits the full restricted constant:

$$
  t\,\bigl|\{z:t\leq|\mathcal Sf(z)|\}\bigr|
    \leq(40+16\pi)\int_{\mathbb C}|f(z)|\,dz.
$$

@include{lean:JJMath.Quasiconformal.beurlingTransformL1_distribution_le}

The next step is strong-type interpolation below two. Duality then supplies
an exponent above two, and exact complex interpolation back toward $L^2$
will provide the norm control needed by the Beltrami solver.

The distributional interpolation argument begins with the elementary
half-threshold estimate for a sum; it will be applied to the transforms of
the high- and low-value parts of the input.

@include{lean:JJMath.HarmonicAnalysis.distributionFunction_add_le_half}

Distribution functions depend only on the almost-everywhere class of a
function. Their $p$th moments are recovered by the layer-cake identity

$$
  \int_X |g|^p=p\int_0^\infty t^{p-1}d_g(t)\,dt.
$$

@include{lean:JJMath.HarmonicAnalysis.distributionFunction_congr_ae}

@include{lean:JJMath.HarmonicAnalysis.lintegral_enorm_rpow_eq_lintegral_distributionFunction}

For the high/low split at height $u$, the low part of an integrable function
is square integrable because $|f|^2\leq u|f|$ there. Linearity and the
half-threshold estimate therefore combine the inherited weak $(1,1)$ bound
on the high part with the exact $L^2$ estimate on the low part:

$$
\begin{aligned}
  d_{\mathcal Sf}(t)\leq{}&
    \frac{(40+16\pi)\int_{\{|f|>u\}}|f|}{t/2}
    +\frac{\int_{\{|f|\leq u\}}|f|^2}{(t/2)^2}.
\end{aligned}
$$

@include{lean:JJMath.Quasiconformal.memLp_two_indicator_compl_enorm_gt}

@include{lean:JJMath.Quasiconformal.eLpNorm_two_sq_eq_lintegral_enorm_sq}

@include{lean:JJMath.Quasiconformal.eLpNorm_two_beurlingTransformL2_apply}

@include{lean:JJMath.Quasiconformal.beurlingTransformL1_distribution_le_high_low}

Set $u=t$. Tonelli's theorem reduces the high tail to

$$
  \int_0^\infty t^{p-2}
    \int_{\{|f|>t\}}|f|
  =\frac1{p-1}\int_{\mathbb C}|f|^p,
$$

and the low tail to

$$
  \int_0^\infty t^{p-3}
    \int_{\{|f|\leq t\}}|f|^2
  =\frac1{2-p}\int_{\mathbb C}|f|^p.
$$

The endpoint restrictions $p>1$ and $p<2$ are exactly the convergence
conditions for these two one-dimensional power integrals.

@include{lean:JJMath.Quasiconformal.lintegral_upper_tail_mul_rpow_eq}

@include{lean:JJMath.Quasiconformal.lintegral_lower_tail_mul_rpow_eq}

Substitution in layer cake gives the extended-valued moment estimate

$$
  \int_{\mathbb C}|\mathcal Sf|^p
    \leq p\left(
      \frac{2(40+16\pi)}{p-1}+\frac4{2-p}
    \right)\int_{\mathbb C}|f|^p.
$$

Taking the positive $p$th root gives the corresponding norm bound and, for
$f\in L^1\cap L^p$, proves that $\mathcal Sf\in L^p$.

@include{lean:JJMath.Quasiconformal.lintegral_rpow_beurlingTransformL1_le}

@include{lean:JJMath.Quasiconformal.eLpNorm_beurlingTransformL1_le}

@include{lean:JJMath.Quasiconformal.memLp_beurlingTransformL1}

Finite-support $L^p$ simple functions form a dense subspace and are
automatically integrable. Sending such a function into $L^1$, applying the
weak transform, and taking the resulting $L^p$ class is complex linear. The
same constant $A_p$ bounds this map on the dense subspace, so it has a unique
bounded extension

$$
  \mathcal S_p:L^p(\mathbb C)\longrightarrow L^p(\mathbb C),
  \qquad \|\mathcal S_pF\|_p\leq A_p\|F\|_p.
$$

@include{lean:JJMath.Quasiconformal.integrable_simpleFunc_toSimpleFunc}

@include{lean:JJMath.Quasiconformal.simpleFuncToL1LinearMap}

@include{lean:JJMath.Quasiconformal.beurlingTransformLpSimpleFuncLinearMap}

@include{lean:JJMath.Quasiconformal.beurlingTransformLp}

@include{lean:JJMath.Quasiconformal.beurlingTransformLp_apply_simpleFunc}

@include{lean:JJMath.Quasiconformal.norm_beurlingTransformLp_le}

The real-interpolation construction below two is therefore complete.

## Bilinear transpose and duality

For complex-valued functions the appropriate transpose pairing is bilinear,
not Hermitian:

$$
  B(f,g)=\int_{\mathbb C}f(z)g(z)\,dz.
$$

It is continuous on $L^2\times L^2$. Fourier transform and inverse Fourier
transform are both self-transpose for this pairing. The proof first uses
Fubini on Schwartz functions and then extends by density.

@include{lean:JJMath.Quasiconformal.planeL2BilinearPairing}

@include{lean:JJMath.Quasiconformal.planeL2BilinearPairing_fourier_left}

@include{lean:JJMath.Quasiconformal.planeL2BilinearPairing_fourierInv_left}

Let $(Rf)(\xi)=f(-\xi)$. On planar $L^2$ one has
$\mathcal F^{-1}=R\mathcal F$. The Beurling symbol is even, so its multiplier
commutes with $R$. Reversing the three factors in
$\mathcal S=\mathcal F^{-1}M_m\mathcal F$ therefore produces the same
operator:

$$
  B(\mathcal Sf,g)=B(f,\mathcal Sg).
$$

@include{lean:JJMath.Quasiconformal.planeL2Reflection_fourier_eq_fourierInv}

@include{lean:JJMath.Quasiconformal.beurlingFourierSymbol_neg}

@include{lean:JJMath.Quasiconformal.planeL2BilinearPairing_beurlingTransformL2_left}

The weak-$L^1$ extension agrees with the Fourier multiplier on
$L^1\cap L^2$, so the same integral symmetry holds there. Finite-support
simple functions belong to this common domain regardless of their finite
positive exponent. Thus the transpose identity is now ready for the
above-two argument.

@include{lean:JJMath.Quasiconformal.integral_beurlingTransformL1_mul_eq_integral_mul_beurlingTransformL1}

@include{lean:JJMath.Quasiconformal.memLp_two_simpleFuncToL1LinearMap}

The quantitative dual-norm step is now complete independently of the
Beurling transform. For $q\geq2$, set

$$
  N_q(z)=|z|^{q-2}\overline z,
  \qquad E_n=S_n\cap\{|h|\leq n\},
  \qquad g_n=\mathbf1_{E_n}N_q(h).
$$

Then $g_n$ is strongly measurable, belongs to every finite $L^r$, and, for
Hölder-conjugate $p,q$,

$$
  h g_n=\mathbf1_{E_n}|h|^q,
  \qquad |g_n|^p=\mathbf1_{E_n}|h|^q,
  \qquad
  \|g_n\|_p=\left(\int_{E_n}|h|^q\right)^{1/p}.
$$

@include{lean:JJMath.HarmonicAnalysis.complexLpNormingValue}

@include{lean:JJMath.HarmonicAnalysis.complexLpNormingTruncation}

@include{lean:JJMath.HarmonicAnalysis.memLp_complexLpNormingTruncation}

@include{lean:JJMath.HarmonicAnalysis.mul_complexLpNormingTruncation}

@include{lean:JJMath.HarmonicAnalysis.lpNorm_complexLpNormingTruncation}

Each $g_n$ has canonical simple approximants supported in $E_n$. They converge
both in $L^p$ and in the pairing with $h$. Thus a bound

$$
  \left|\int_X hs\,d\mu\right|\leq C\|s\|_p
$$

for every $L^p$ simple function passes first to $g_n$. The two norming
identities give

$$
  A_n\leq C A_n^{1/p},
  \qquad A_n=\int_{E_n}|h|^q,
$$

hence $A_n^{1/q}\leq C$. Finally, $E_n\uparrow X$ and the Fatou inequality
for $L^q$ seminorms prove $h\in L^q$ and $\|h\|_q\leq C$.

@include{lean:JJMath.HarmonicAnalysis.complexLpNormingTruncationApproximation}

@include{lean:JJMath.HarmonicAnalysis.tendsto_integral_mul_complexLpNormingTruncationApproximation}

@include{lean:JJMath.HarmonicAnalysis.memLp_and_lpNorm_le_of_simpleFunc_pairing}

Now let $p$ and $q$ be Hölder conjugate with $1<p<2\leq q$, and let $F$ be a
finite-support $L^q$ simple function. For every finite-support $s\in L^p$,
bilinear symmetry and compatibility on simple functions give

$$
  \int_{\mathbb C}(\mathcal SF)s
    =\int_{\mathbb C}F(\mathcal Ss).
$$

Hölder's inequality and the completed lower-exponent estimate therefore show

$$
  \left|\int_{\mathbb C}(\mathcal SF)s\right|
    \leq A_p\|F\|_q\|s\|_p.
$$

The quantitative duality theorem places the weak transform of $F$ in $L^q$
with norm at most $A_p\|F\|_q$.

@include{lean:JJMath.Quasiconformal.norm_integral_mul_le_lpNorm_mul_lpNorm}

@include{lean:JJMath.Quasiconformal.memLp_and_lpNorm_beurlingTransformL1_simpleFunc_le}

Linearity comes from the weak transform, and finite-support simple functions
are dense in $L^q$. Extending the bounded simple-function map completes the
strong Beurling transform above two with the same constant.

@include{lean:JJMath.Quasiconformal.beurlingTransformLpAboveSimpleFuncLinearMap}

@include{lean:JJMath.Quasiconformal.beurlingTransformLpAbove}

@include{lean:JJMath.Quasiconformal.beurlingTransformLpAbove_apply_simpleFunc}

@include{lean:JJMath.Quasiconformal.norm_beurlingTransformLpAbove_le}

Both completed transforms use the same operator on the finite-support simple
core. Indeed, there the weak transform agrees almost everywhere with the
exact Fourier-multiplier $L^2$ transform.

@include{lean:JJMath.Quasiconformal.beurlingTransformL1_simpleFuncToL1LinearMap_ae_eq_beurlingTransformL2}


@include{lean:JJMath.Quasiconformal.beurlingTransformLpAbove_apply_simpleFunc_ae_eq_beurlingTransformL2}

## Exact interpolation at $L^2$

For the Beltrami equation, a merely finite $L^q$ bound is not enough. If
$\|\mu\|_\infty$ may be arbitrarily close to one, one needs exponents
$p>2$ for which

$$
  \|\mu\|_\infty\,\|T\|_{L^p\to L^p}<1.
$$

The Beurling transform has exact $L^2$ norm one, while the preceding section
now supplies a finite bound at one exponent $q>2$. The dense-core
compatibility above gives a single operator with both endpoint estimates, so
complex interpolation between them will make the interpolated norm tend to
one as $p\to2$. Mathlib already provides Hadamard's three-lines theorem, so
the remaining reusable result is the Riesz--Thorin construction on the common
simple core and its density layer. This will be developed here rather than
embedded in the quasiconformal solver.

The analytic simple-function deformation is now available. For

$$
  a(z)=\frac r{p_0}(1-z)+\frac r{p_1}z,
  \qquad
  w_z=\begin{cases}0,&w=0,\\(w/|w|)|w|^{a(z)},&w\ne0,
  \end{cases}
$$

the map $z\mapsto w_z$ is entire and

$$
  |w_z|=|w|^{\frac r{p_0}(1-\operatorname{Re}z)
    +\frac r{p_1}\operatorname{Re}z}.
$$

@include{lean:JJMath.HarmonicAnalysis.complexInterpolationValue}

@include{lean:JJMath.HarmonicAnalysis.differentiable_complexInterpolationValue}

@include{lean:JJMath.HarmonicAnalysis.norm_complexInterpolationValue}

The reciprocal-exponent identity recovers the original function at the
interpolation point. The deformation preserves integrable simple functions,
and a normalized $L^r$ simple function has norm one on both boundary lines.

@include{lean:JJMath.HarmonicAnalysis.complexInterpolationL1SimpleFunc}

@include{lean:JJMath.HarmonicAnalysis.complexInterpolationL1SimpleFunc_of_reciprocal_interpolation}

@include{lean:JJMath.HarmonicAnalysis.lpNorm_complexInterpolationSimpleFunc_eq_one_of_re_eq_zero}

@include{lean:JJMath.HarmonicAnalysis.lpNorm_complexInterpolationSimpleFunc_eq_one_of_re_eq_one}

For a complex-bilinear pairing $B$, the two deformations admit finite
value-fiber expansions, and hence

$$
  z\longmapsto B(f_z,g_z)
$$

is a finite double sum of entire scalar functions. The scalar norm formula
also makes this pairing uniformly bounded on the entire closed strip, not
merely on compact sub-strips.

@include{lean:JJMath.HarmonicAnalysis.complexInterpolationBilinearPairing_eq_sum}

@include{lean:JJMath.HarmonicAnalysis.differentiable_bilinearMap_complexInterpolationL1SimpleFunc}

@include{lean:JJMath.HarmonicAnalysis.bddAbove_norm_complexInterpolationBilinearPairing}

Hadamard's theorem now gives the reusable simple-core Riesz--Thorin estimate.
If the pairing constants at the two endpoints are $A$ and $C$, and the input
and test exponents satisfy their reciprocal interpolation identities, then

$$
  |B(f,g)|\leq A^{1-\theta}C^\theta\|f\|_r\|g\|_s.
$$

@include{lean:JJMath.HarmonicAnalysis.norm_bilinearMap_le}

For the Beurling transform, the common pairing is defined using the exact
Fourier multiplier on the canonical $L^2$ inclusions of integrable simple
functions.

@include{lean:JJMath.Quasiconformal.beurlingL2SimpleBilinearPairing}

Its two endpoint bounds are the norm-one $L^2\times L^2$ estimate and the
finite $L^q\times L^{q'}$ estimate inherited from the completed above-two
operator.

@include{lean:JJMath.Quasiconformal.norm_beurlingL2SimpleBilinearPairing_le}

@include{lean:JJMath.Quasiconformal.norm_beurlingL2SimpleBilinearPairing_above_le}

Interpolation gives the expected $A_p^\theta$ pairing constant. Quantitative
simple-test duality then turns this into strong $L^r$ membership and the same
norm bound for the weak transform of every integrable simple input.

@include{lean:JJMath.Quasiconformal.norm_beurlingL2SimpleBilinearPairing_interpolation_le}

@include{lean:JJMath.Quasiconformal.memLp_and_lpNorm_beurlingTransformL1_integrableSimpleFunc_interpolation_le}

Finite-support $L^r$ simple functions are converted to the integrable common
core without changing their representatives or norms. The interpolated
transform is complex-linear and uniformly bounded there, so density gives a
bounded operator on all of $L^r$ with the same constant.

@include{lean:JJMath.Quasiconformal.beurlingTransformLpInterpolated}

@include{lean:JJMath.Quasiconformal.norm_beurlingTransformLpInterpolated_operator_le}

On the simple common core, this completed operator still agrees almost
everywhere with the exact Fourier-multiplier transform.

@include{lean:JJMath.Quasiconformal.beurlingTransformLpInterpolated_apply_simpleFunc_ae_eq_beurlingTransformL2}

Using the same measurable simple approximation simultaneously in $L^r$ and
$L^2$ extends this compatibility to the full intersection. Boundedness gives
convergence in both norms, hence in measure, and uniqueness of the limit in
measure identifies the two outputs.

@include{lean:JJMath.Quasiconformal.beurlingTransformLpNearTwo_toLp_ae_eq_beurlingTransformL2}

For the Beltrami application it suffices to fix the endpoint pair $3/2,3$.
Writing

$$
  r_\theta^{-1}=\frac{1-\theta}{2}+\frac\theta3
$$

puts $r_\theta$ strictly between $2$ and $3$ when $0<\theta<1$.
Continuity of $A_{3/2}^\theta$ at zero then gives, for every $k<1$, a
positive parameter with $kA_{3/2}^\theta<1$.

@include{lean:JJMath.Quasiconformal.exists_beurlingNearTwo_contraction_parameters}
