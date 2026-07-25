# Principal Solutions of the Beltrami Equation

For a compactly supported coefficient $\mu$ with
$\|\mu\|_\infty<1$, the analytic construction seeks a map

$$
  f(z)=z+\mathcal C h(z),
  \qquad
  h-\mu\mathcal S h=\mu.
$$

Here $\mathcal C$ is the Cauchy transform and $\mathcal S$ is the Beurling
transform. This equation is designed so that
$\partial_{\bar z}\mathcal C h=h$ and
$\partial_z\mathcal C h=\mathcal S h$, which gives
$\partial_{\bar z}f=\mu\partial_zf$.

## The Cauchy transform on test functions

For $g\in C_c^\infty(\mathbb C)$, set

$$
  \mathcal Cg(z)=\frac1\pi\int_{\mathbb C}\frac{g(w)}{z-w}\,dw.
$$

The singularity is mild enough for this to be an ordinary Bochner integral,
not a principal value. Indeed, $w\mapsto w^{-1}$ has norm $|w|^{-1}$ and is
locally integrable in real dimension two. Translation gives the same result
for the kernel centered at any $z$, and compact support of $g$ makes the
product globally integrable.

@include{lean:JJMath.Quasiconformal.locallyIntegrable_planarCauchyKernel}

@include{lean:JJMath.Quasiconformal.integrable_planarCauchyKernel_mul_testFunction}

### The fundamental solution

For $\varepsilon>0$, regularize the reciprocal kernel by

$$
  K_\varepsilon(z)=\frac{\overline z}{|z|^2+\varepsilon^2}.
$$

It is smooth and its antiholomorphic Wirtinger derivative is

$$
  \partial_{\bar z}K_\varepsilon(z)
    =\frac{\varepsilon^2}{(|z|^2+\varepsilon^2)^2}.
$$

@include{lean:JJMath.Quasiconformal.frechetDBarValue_regularizedCauchyKernel}

Integration by parts moves $\partial_{\bar z}$ from a compactly supported
test function onto this smooth kernel. After multiplying by $1/\pi$, the
right-hand side is a nonnegative radial approximate identity of total mass
one.

@include{lean:JJMath.Quasiconformal.integral_regularizedCauchyKernel_mul_frechetDBarValue}

@include{lean:JJMath.Quasiconformal.integral_cauchyApproximateIdentityProfile}

The regularized kernels converge pointwise away from zero to $1/z$ and are
dominated by $1/|z|$, which is integrable against the compactly supported
derivative of a test function. Dominated convergence on the left and the
approximate-identity limit on the right therefore give the exact normalized
fundamental-solution identity

$$
  -\frac1\pi\int_{\mathbb C}\frac{\partial_{\bar z}\varphi(z)}{z}\,dz
    =\varphi(0).
$$

@include{lean:JJMath.Quasiconformal.neg_piInv_mul_integral_inv_mul_frechetDBarValue_eq_eval_zero}

### Passing through convolution

Translation centers the fundamental solution at an arbitrary point $w$:

$$
  -\frac1\pi\int_{\mathbb C}
      \frac{\partial_{\bar z}\varphi(z)}{z-w}\,dz
    =\varphi(w).
$$

@include{lean:JJMath.Quasiconformal.neg_piInv_mul_integral_sub_inv_mul_frechetDBarValue_eq_eval}

The Cauchy integral is the convolution of $1/z$ with the test function,
multiplied by $1/\pi$. Standard compactly supported convolution regularity
makes it smooth.

@include{lean:JJMath.Quasiconformal.cauchyTransform_eq_piInv_mul_reciprocalConvolution}

@include{lean:JJMath.Quasiconformal.contDiff_cauchyTransform}

Applying the centered fundamental solution first proves
$\mathcal C(\partial_{\bar z}g)=g$. Differentiating the convolution then gives
the pointwise identity

$$
  \partial_{\bar z}\mathcal Cg=g.
$$

@include{lean:JJMath.Quasiconformal.cauchyTransform_planeTestFunctionDBar_eq}

@include{lean:JJMath.Quasiconformal.frechetDBarValue_cauchyTransform}

Differentiating in the other Wirtinger direction passes through the same
convolution and gives the pointwise formula

$$
  \partial_z\mathcal Cg=\mathcal C(\partial_zg).
$$

@include{lean:JJMath.Quasiconformal.frechetDZValue_cauchyTransform_eq}

The Cauchy transform also has the far-field decay needed to localize this
identity. A test function is supported in some centered disk, and outside
twice that disk the reverse triangle inequality gives

$$
  |\mathcal Cg(z)|\leq
    \frac{2}{\pi|z|}\int_{\mathbb C}|g(w)|\,dw.
$$

@include{lean:JJMath.Quasiconformal.exists_nonneg_support_radius_planeTestFunction}

@include{lean:JJMath.Quasiconformal.norm_cauchyTransform_le_of_support_subset_closedBall}

The Fourier multiplier algebra itself is already complete. On every test
function one has the exact $L^2$ identity

$$
  \mathcal S(\partial_{\bar z}\varphi)=\partial_z\varphi.
$$

@include{lean:JJMath.Quasiconformal.beurlingTransformL2_schwartzWirtingerDBar}

@include{lean:JJMath.Quasiconformal.beurlingTransformL2_testFunctionDBar}

The test-function identity extends to the Cauchy transform itself:

$$
  \partial_z\mathcal Cg=\mathcal Sg
  \quad\text{almost everywhere}.
$$

Choose a fixed smooth bump equal to one on the unit disk and dilate it to
radius $R$. Applying the displayed test-function identity to the product of
this cutoff with $\mathcal Cg$ gives the desired equality on every fixed
disk, up to product-rule terms supported in the expanding transition
annulus. The cutoff derivative is $O(R^{-1})$, while the far-field bound is
$O(R^{-1})$ there. The resulting error is pointwise $O(R^{-2})$ on a disk of
area $O(R^2)$, so its $L^2$ norm is $O(R^{-1})$. This ordinary smooth cutoff
argument avoids introducing logarithmic Sobolev cutoffs into the Fourier
layer.

@include{lean:JJMath.Quasiconformal.cauchyDiskCutoff_eq_one_of_norm_le}

@include{lean:JJMath.Quasiconformal.cauchyDiskCutoff_eq_zero_of_two_mul_le_norm}

@include{lean:JJMath.Quasiconformal.exists_norm_fderiv_cauchyDiskCutoff_le_div}

@include{lean:JJMath.Quasiconformal.exists_norm_frechetDZValue_and_frechetDBarValue_cauchyDiskCutoff_le_div}

@include{lean:JJMath.Quasiconformal.frechetDZValue_cauchyDiskCutoff_eq_zero_of_norm_lt}

@include{lean:JJMath.Quasiconformal.frechetDBarValue_cauchyDiskCutoff_eq_zero_of_norm_lt}

The localized product is bundled as an actual compactly supported smooth test
function, and both Wirtinger product rules have already been expanded:

@include{lean:JJMath.Quasiconformal.frechetDBarValue_cutoffCauchyTransform}

@include{lean:JJMath.Quasiconformal.frechetDZValue_cutoffCauchyTransform}

When the inner cutoff disk contains the support of $g$, the
antiholomorphic product-rule error is exactly
$(\partial_{\bar z}\beta_R)\mathcal Cg$:

@include{lean:JJMath.Quasiconformal.cauchyDiskCutoffDBarError_apply}

@include{lean:JJMath.Quasiconformal.norm_cauchyDiskCutoffDBarError_le}

@include{lean:JJMath.Quasiconformal.exists_norm_testFunctionPlaneL2_cauchyDiskCutoffDBarError_le_div}

@include{lean:JJMath.Quasiconformal.frechetDZValue_cauchyTransform_ae}

The weak integration-by-parts argument and the $L^2$ Beurling isometry then
assemble the full local Sobolev differential:

@include{lean:JJMath.Quasiconformal.cauchyTransform_isLocalW12On}

Thus the Cauchy--Beurling interface on smooth compactly supported data is
complete.

## The $L^2$ Beurling transform

With the Fourier convention used here, the symbols of $\partial_z$ and
$\partial_{\bar z}$ are respectively $\pi i\overline\xi$ and $\pi i\xi$.
The multiplier converting the second derivative into the first is therefore

$$
  m(\xi)=\frac{\overline\xi}{\xi}\qquad(\xi\ne0).
$$

Assigning $m(0)=1$ does not change its measurable class and makes
$|m(\xi)|=1$ at every frequency.

The sign and conjugation are now checked formally on Schwartz functions:

@include{lean:JJMath.Quasiconformal.fourier_schwartzWirtingerZ_apply}

@include{lean:JJMath.Quasiconformal.fourier_schwartzWirtingerDBar_apply}

@include{lean:JJMath.Quasiconformal.norm_beurlingFourierSymbol}

The Beurling transform on planar $L^2$ is defined by

$$
  \mathcal S u=\mathcal F^{-1}(m\,\mathcal F u).
$$

@include{lean:JJMath.Quasiconformal.beurlingTransformL2_apply}

Plancherel and the unit modulus of $m$ immediately give the exact isometry

$$
  \|\mathcal S u\|_{L^2}=\|u\|_{L^2}.
$$

@include{lean:JJMath.Quasiconformal.norm_beurlingTransformL2_apply}

This construction deliberately works directly in $L^2$. Multiplication by
$m$ does not preserve the Schwartz class because of its behavior at the
origin, so a Schwartz-space Fourier multiplier would be the wrong primary
object.

## The $L^2$ Beltrami equation

For $\mu\in L^\infty(\mathbb C)$, multiplication followed by the Beurling
transform defines $T_\mu=M_\mu\mathcal S$ on $L^2$. Pointwise multiplication
has its expected operator bound,

@include{lean:JJMath.Quasiconformal.norm_l2PointwiseMultiplier_le}

and the Beurling isometry therefore gives

$$
  \|T_\mu\|_{L^2\to L^2}\leq\|\mu\|_{L^\infty}.
$$

@include{lean:JJMath.Quasiconformal.norm_beltramiL2Operator_le}

If $\|\mu\|_\infty<1$, the norm-convergent geometric series inverts
$I-T_\mu$. Thus every $g\in L^2$ has a unique solution of

$$
  h-\mu\mathcal Sh=g.
$$


The coefficient hypothesis used for principal solutions supplies the right
hand side. A bounded measurable coefficient which vanishes almost everywhere
outside a disk lies in $L^2$:


Combining this fact with $|\mu|\leq k<1$ gives exactly the Hilbert-space
equation needed by the construction:


This completes the $L^2$ Neumann step. It does not yet give the extra
integrability used to make the Cauchy potential continuous.

## A strict contraction above exponent two

The completed interpolation theory supplies a bounded Beurling transform on
$L^r(\mathbb C)$ for exponents $2<r<3$ sufficiently close to $2$.
Pointwise multiplication by an $L^\infty$ coefficient is bounded on every
such space:

@include{lean:JJMath.Quasiconformal.norm_lpPointwiseMultiplier_le}

For the interpolation segment from $2$ to $3$, the operator norm satisfies

$$
  \|\mathcal S_r\|_{L^r\to L^r}\leq A_{3/2}^\theta,
  \qquad
  \frac1r=\frac{1-\theta}{2}+\frac\theta3.
$$

The near-$2$ parameter theorem chooses $\theta>0$ so that
$\|\mu\|_\infty A_{3/2}^\theta<1$. Hence the actual
multiplier--Beurling composition is a strict contraction:

@include{lean:JJMath.Quasiconformal.norm_beltramiLpOperator_beurlingNearTwo_lt_one}

The Neumann series therefore gives existence and uniqueness for the
$L^r$ Beltrami equation:

@include{lean:JJMath.Quasiconformal.existsUnique_beltramiLpNearTwoEquation}

If $\mu$ is supported in a disk and the right-hand side also belongs to
$L^2$, the $L^r$ solution belongs to $L^2$: the product
$\mu\mathcal S_rh$ is supported in the same finite-area disk, so exponent
monotonicity lowers it from $L^r$ to $L^2$. Compatibility of
$\mathcal S_r$ with the exact $L^2$ transform then turns the equation into
the Hilbert-space Beltrami equation. Its uniqueness identifies the two
Neumann solutions.

@include{lean:JJMath.Quasiconformal.beltramiLpNearTwoSolution_toLp_two_eq_beltramiL2Solution}

Finally, the parameter choice is packaged for a raw bounded measurable
coefficient supported in a disk. Its $L^\infty$ norm selects the interpolation
data, disk support puts the same coefficient in the selected $L^r$ space,
and the resolvent supplies the unique solution of
$h-\mu\mathcal S_rh=\mu$.

@include{lean:JJMath.Quasiconformal.existsUnique_compactlySupported_beltramiLpNearTwoEquation}

The equation itself also forces the solution to have the same disk support
as the coefficient and right-hand side:

@include{lean:JJMath.Quasiconformal.beltramiLpNearTwoSolution_ae_zero_outside_closedBall}

## Local higher integrability

The same resolvent machinery applies to an arbitrary continuous local
$W^{1,2}$ solution of the Beltrami equation; no global Cauchy representation
is needed. Given a smooth compactly supported cutoff $\chi$, multiplication
by $\chi$ gives a global weak Sobolev map. Smooth graph approximation on the
support of $\chi$ passes the test-function identity to the rough map and
proves

$$
  \mathcal S_2\bigl(\partial_{\bar z}(\chi f)\bigr)
    =\partial_z(\chi f)
  \quad\text{in }L^2(\mathbb C).
$$

@include{lean:JJMath.Quasiconformal.beurlingTransformL2_complexWeakSobolevCutoffDBarPlaneL2}

Localize the coefficient itself to the support of $\chi$. The resulting
$\mu_\chi$ retains the essential bound for $\mu$ and vanishes outside a
disk. The product-rule error

$$
  G_{\chi,f,\mu}
    =\partial_{\bar z}(D\chi\otimes f)
      -\mu\,\partial_z(D\chi\otimes f)
$$

is measurable, bounded, and disk-supported, so it belongs to every
$L^p(\mathbb C)$.

@include{lean:JJMath.Quasiconformal.localizedBeltramiCoefficient_ae_norm_le}

@include{lean:JJMath.Quasiconformal.complexWeakSobolevCutoffBeltramiError_memLp}

The localized equation therefore has the exact Hilbert-space form

$$
  [\partial_{\bar z}(\chi f)]
    -[\mu_\chi]\mathcal S_2[\partial_{\bar z}(\chi f)]
    =[G_{\chi,f,\mu}].
$$

@include{lean:JJMath.Quasiconformal.complexWeakSobolevCutoffDBarPlaneL2_beltramiEquation}

Choose the near-$2$ exponent for $\mu_\chi$. The corresponding $L^p$
resolvent solution is also in $L^2$, where uniqueness identifies it with
$\partial_{\bar z}(\chi f)$. Compatibility of the two Beurling transforms
then places $\partial_z(\chi f)$ in the same $L^p$ space. A cutoff equal to
one on a prescribed compact set gives the local conclusion: for every
compact $Q\subset\Omega$, some $2<p<3$ satisfies

$$
  Df\in L^p(Q).
$$

@include{lean:JJMath.Quasiconformal.IsLocalW12On.exists_derivative_memLpOn_compact_nearTwo}

## The rough Cauchy potential

Let $p>2$ and let $q$ be its Hölder conjugate. Then $1<q<2$, which is
exactly the local integrability range of the planar Cauchy kernel. More
precisely, restricting a centered kernel to any compact set gives an
$L^q$ function:

@include{lean:JJMath.Quasiconformal.memLp_indicator_planarCauchyKernel_of_isCompact}

Consequently, if $h\in L^p(\mathbb C)$ is supported in a disk, the integral

$$
  \mathcal C_ph(z)=\frac1\pi\int_{\mathbb C}\frac{h(w)}{z-w}\,dw
$$

is absolutely convergent at every point.


Support-controlled smooth approximation is available at every finite
exponent. Reflection and translation preserve planar measure, so the
$L^q$ norm of the kernel on a disk is independent of its center. Enlarging
one disk therefore gives a uniform kernel bound while the evaluation point
ranges over a compact disk. Hölder's inequality turns $L^p$ approximation
into locally uniform approximation of the corresponding Cauchy potentials.
This proves continuity of the pointwise integral without requiring a
separate abstract Morrey theorem:

@include{lean:JJMath.Quasiconformal.continuous_cauchyTransformLp}

Disk support also places $h$ in $L^1$. The elementary far-field estimate is

$$
  |\mathcal C_ph(z)|\leq
    \frac{2}{\pi|z|}\int_{\mathbb C}|h(w)|\,dw
$$

when $|z|\geq2R$, and hence the rough potential has the principal decay.

@include{lean:JJMath.Quasiconformal.tendsto_cauchyTransformLp_cocompact_zero}

## The rough Sobolev identities

Fixed-support $L^p$ convergence above exponent two automatically lowers to
$L^2$ convergence. The Fourier Beurling isometry therefore gives strong
$L^2$ convergence of the holomorphic derivative components, while local
uniform convergence of the Cauchy potentials gives their strong local $L^2$
convergence. Passing the smooth weak-derivative identities to the limit on
every closed disk and exhausting the plane proves

$$
  \partial_{\bar z}\mathcal C_ph=h,
  \qquad
  \partial_z\mathcal C_ph=\mathcal S_2h
$$

almost everywhere.

@include{lean:JJMath.Quasiconformal.memLp_two_of_memLp_of_ae_zero_outside_closedBall}

@include{lean:JJMath.Quasiconformal.tendsto_eLpNorm_two_of_tendsto_eLpNorm_of_common_closedBall_support}

@include{lean:JJMath.Quasiconformal.tendstoUniformlyOn_cauchyTransform_of_tendsto_eLpNorm}

@include{lean:JJMath.Quasiconformal.cauchyTransformLp_isLocalW12On}

## The analytic principal solution

Adding the identity map gives

$$
  f(z)=z+\mathcal C_ph(z),
  \qquad
  \partial_zf=1+\mathcal S_2h,
  \qquad
  \partial_{\bar z}f=h.
$$

@include{lean:JJMath.Quasiconformal.principalBeltramiMap_isLocalW12On}

The near-$2$ Neumann equation and compatibility with the $L^2$ transform
give $h=\mu(1+\mathcal S_2h)$. Consequently the principal map is continuous,
locally Sobolev, solves the prescribed weak Beltrami equation, satisfies

$$
  |Df|^2\leq\frac{1+k}{1-k}J_f
$$

almost everywhere, and obeys $f(z)-z\to0$ at infinity.

@include{lean:JJMath.Quasiconformal.isProperMap_of_continuous_of_tendsto_sub_id_cocompact_zero}

In fact the full straight-line homotopy from the identity to the principal
map remains proper.


The same normalization already determines the outer boundary class. For
every target point, a sufficiently large positive circle has an image loop
which avoids that target and represents the standard positive class.


Equivalently, the integer winding number of this normalized large image loop
is exactly one.


@include{lean:JJMath.Quasiconformal.exists_analyticPrincipalSolution_of_compactSupport}

The analytic construction is therefore complete, including properness of the
principal map. The logarithmic condenser argument now proves that every
connected subset of each fiber is a point. The protected weighted-Jacobian
measure then proves openness directly. Properness and protected
almost-everywhere multiplicity make every fiber finite, while openness on a
smaller isolating disk makes each local index strictly positive.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.connected_fiber_subsingleton_of_boundedDistortion_of_isProperMap}

@include{lean:JJMath.Quasiconformal.open_discrete_and_localIndex_pos_of_boundedDistortion_of_isProperMap}

Properness and discreteness then make every fiber finite. The integer degree
on a large circle is one, and planar boundary additivity identifies it with
the sum of the local indices in the fiber.

@include{lean:JJMath.Quasiconformal.finite_fiber_of_isProperMap_of_isDiscrete_fiber}

@include{lean:JJMath.Quasiconformal.planarFiberIndexSum_eq_one_of_tendsto_sub_id_cocompact_zero}

Positive integer summands with total one force every fiber to be a singleton.
The resulting continuous open bijection is a plane homeomorphism, every local
index is one, and hence the map preserves planar orientation.

@include{lean:JJMath.Quasiconformal.planarLocalIndex_eq_one_of_tendsto_sub_id_cocompact_zero}

@include{lean:JJMath.Quasiconformal.exists_principalHomeomorphism_of_compactSupport}

Thus the compact-support principal homeomorphism is proved without invoking
the still-optional general Whyburn--Stoilow theorem. The next construction
extends the plane homeomorphism over infinity and affinely normalizes it at
$0$ and $1$, after which coefficient truncation feeds into normalized
spherical compactness.
