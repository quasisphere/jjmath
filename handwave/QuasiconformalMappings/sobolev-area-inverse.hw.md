# Sobolev Change of Variables for Planar Quasiconformal Maps

This article follows the analytic spine from local planar $W^{1,2}$
regularity to the area formula and the quasiconformality of the inverse.  The
central point is that ambient Fréchet differentiability almost everywhere is
not needed: approximate differentiability, a Lusin--Whitney decomposition,
and the Lusin $N$ property provide exactly the hypotheses required by the
Jacobian theorem on countably many measurable pieces.

## From coordinate ACL to Lusin $N$

A continuous planar local $W^{1,2}$ map is absolutely continuous on almost
every protected horizontal and vertical segment.  On such segments its line
derivatives are the evaluations $Df(1)$ and $Df(i)$ of the weak differential.

@include{lean:JJMath.Quasiconformal.planarWeakSobolev_horizontal_acl_on_compact_of_continuousOn}

@include{lean:JJMath.Quasiconformal.planarWeakSobolev_vertical_acl_on_compact_of_continuousOn}

For a homeomorphism, four suitably selected ACL lines surround a small
square.  The diameter of the mapped boundary is controlled by their line
energies, while the area of the mapped square is bounded by the square of
that diameter.  After averaging over the four surrounding strips one obtains
the scale-invariant estimate

$$
  |f(Q)|\leq 64\int_{2Q}\lVert Df\rVert^2.
$$

@include{lean:JJMath.Quasiconformal.IsLocalW12On.volume_ambientMap_image_square_le}

A fine grid cover and a sixteen-color bounded-overlap argument turn this
local estimate into nullity of the image of every compact null set.
Measurability of homeomorphic images and inner regularity then give the full
Lusin $N$ property.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.volume_ambientMap_image_eq_zero_of_isCompact_null}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.hasLusinNOn_ambientMap}

## The Morrey route without injectivity

For the open-and-discrete theorem one cannot use the preceding
homeomorphism argument.  Local higher integrability instead supplies
$Df\in L^p$ for some $p>2$.  On a planar ball, finite-measure comparison
lowers the differential exponent from $p$ to $2$, and the ordinary
$L^2$ Poincaré inequality becomes

$$
  \|f-a\|_{L^2(B(x,r))}
    \leq
    Cr\|Df\|_{L^p(B(x,r))}
      |B(x,r)|^{1/2-1/p}.
$$

@include{lean:JJMath.Quasiconformal.complex_valued_euclideanSobolev_poincare_Lp_scale_covariant}

After using the exact area of a planar ball, the same estimate takes the
more transparent real-valued form

$$
  \|f-a\|_{L^2(B(x,r))}
    \leq
    C\pi^{1/2-1/p}
    \|Df\|_{L^p(B(x,r))}r^{2-2/p}.
$$

@include{lean:JJMath.Quasiconformal.complex_valued_euclideanSobolev_poincare_Lp_real_scale}

The corresponding centers can be chosen simultaneously on all dyadic
balls inside a fixed compact ball.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.exists_dyadic_poincareCenters}

The abstract Campanato step is independent of Sobolev theory.  If the
normalized errors decay geometrically, comparison on two consecutive
nested balls makes the centers a Cauchy sequence with a quantitative
geometric tail.

@include{lean:JJMath.Quasiconformal.exists_limit_dyadicCenters_of_eLpNorm_le_geometric}

For $q=2^{-(1-2/p)}$, the scale identity
$r_n^{2-2/p}=R^{1-2/p}q^nr_n$ puts these errors into the geometric form
required by the abstract argument.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.exists_dyadic_poincareCenters_geometric}

Continuity identifies the limiting constant with the actual value of the
map, not merely an almost-everywhere representative, and retains the same
tail estimate.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.exists_dyadic_poincareCenters_with_value_bound}

Centers on overlapping nonconcentric balls can be compared through a common
half-radius ball.  To keep the energy ball identical to the ball whose image
is estimated, approach a boundary point radially through

$$
  x_n=c+\bigl(1-(3/4)^n\bigr)(x-c).
$$

The comparison balls have radii $\frac12(3/4)^nr$, remain inside
$\overline B(c,r)$, and yield a geometric series with ratio
$(3/4)^{1-2/p}$. Thus

$$
  |f(c)-f(x)|
    \leq C_p^{\mathrm{rad}}
      \|Df\|_{L^p(\overline B(c,r))}
      r^{1-2/p}.
$$

@include{lean:JJMath.Quasiconformal.IsLocalW12On.norm_center_sub_le_morrey_on_same_closedBall}

Comparing two points through the center gives a diameter estimate using only
the same closed ball.  Squaring it and using

$$
  w^{1-2/p}e^{2/p}\leq w+e
$$

for finite $w,e\geq0$ gives the particularly useful area bound

$$
  |f(\overline B(c,r))|
    \leq C_p^2
      \left(
        |\overline B(c,r)|
        +\int_{\overline B(c,r)}\|Df\|^p
      \right).
$$

@include{lean:JJMath.Quasiconformal.IsLocalW12On.volume_image_closedBall_le_constant_mul_add_energy}

Now let $N$ be null and contained in the interior of a compact set $C$.
The finite measure

$$
  \nu(A)=|A|+\int_A\|Df\|^p
$$

also vanishes on $N$. Besicovitch covering supplies countably many closed
balls centered on $N$, all contained in $\operatorname{int}C$, whose total
$\nu$-mass is arbitrarily small. Countable subadditivity and the same-ball
area estimate show that $f(N)$ is null.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.volume_image_eq_zero_of_null_of_memLp}

Exhausting the plane by closed balls turns higher integrability on every
compact set into the full Lusin $N$ property.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.hasLusinNOn_of_derivative_memLpOn_compact_above_two}

For continuous maps of bounded distortion, the Beltrami equation supplies
the required exponent $p>2$ on each compact set. Hence these maps satisfy
Lusin $N$ before the open-and-discrete theorem is used.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.boundedDistortion_hasLusinNOn}

## Approximate differentiability and Lusin--Whitney pieces

The scale-covariant planar Poincaré inequality controls a Sobolev function by
its weak differential on every ball.  Lebesgue differentiation of the value
and differential fields, followed by a dyadic comparison of the Poincaré
centers, gives the fixed-center affine remainder estimate

$$
  \lVert f-f(x)-Df(x)(\,\cdot-x)\rVert_{L^2(B(x,r))}=o(r^2)
$$

for almost every $x$.  Chebyshev's inequality converts this mean-square
estimate into approximate differentiability with approximate differential
$Df(x)$.

@include{lean:JJMath.Quasiconformal.complex_valued_euclideanSobolev_poincare_L2_scale_covariant}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.ae_hasApproxFDerivAt}

The Lusin--Whitney construction uniformizes the density and affine defects on
bounded exhaustions.  It produces countably many measurable pieces covering
almost all of the source on which $f$ has the genuine within-set derivative
$Df$.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.exists_countable_measurable_cover_hasFDerivWithinAt}

## The Sobolev area formula

Mathlib's differentiable area theorem applies on each measurable
within-differentiability piece.  Injectivity makes the corresponding image
pieces disjoint, and Lusin $N$ removes the image of the exceptional source
set.  Thus, for measurable $s\subseteq\Omega$ and nonnegative measurable
$g$,

$$
  \int_s J_f(z)g(f(z))\,dz
    =\int_{f(s)}g(y)\,dy.
$$

@include{lean:JJMath.Quasiconformal.areaFormula_of_countable_cover_hasFDerivWithinAt_of_hasLusinNOn}

The distortion inequality forces $J_f\geq0$ almost everywhere, so the
absolute Jacobian in the general area theorem is the oriented weak Jacobian.
This gives the public quasiconformal area formula, including a Bochner-valued
version used in the inverse argument.

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.areaFormula}

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.integral_image_eq_integral_weakJacobian_smul}

## Multiplicity without injectivity

For the open-and-discrete theorem, injectivity is not yet available.  The
right target-side quantity is the extended fiber cardinality

$$
  N(f,S,y)=\#\{x\in S:f(x)=y\}.
$$

@include{lean:JJMath.Quasiconformal.preimageMultiplicity}

On the positive-Jacobian part of a within-differentiability piece, Mathlib's
quantitative linear-approximation partition can be chosen with error below
half the inverse norm of the model differential.  The map is injective on
each resulting measurable piece.  The sum of the image indicators of these
sheets is exactly $N(f,S,y)$, not merely an auxiliary counting function.

@include{lean:JJMath.Quasiconformal.exists_countable_measurable_injective_cover_of_hasFDerivWithinAt_of_weakJacobian_pos}

@include{lean:JJMath.Quasiconformal.tsum_image_indicator_one_eq_preimageMultiplicity}

The zero-Jacobian part has null image by the fixed-dimensional Sard lemma.
After flattening the Lusin--Whitney piece index and the injective-sheet index,
Lusin $N$ removes the exceptional source-null set.  Choosing a measurable
representative of the weak differential then gives the full Sobolev
multiplicity formula

$$
  \int_{\mathbb C}N(f,S,y)g(y)\,dy
    =
  \int_S J_f(x)g(f(x))\,dx.
$$

@include{lean:JJMath.Quasiconformal.IsLocalW12On.areaFormula_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae}

For a continuous whole-plane map of bounded distortion, higher
integrability provides Lusin $N$ and the distortion inequality provides
$J_f\geq0$. Thus the multiplicity formula is available before openness or
discreteness is known.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.boundedDistortion_areaFormula_preimageMultiplicity}

Pointwise submultiplicativity and bounded distortion now give the
noninjective pullback estimate

$$
  \int_S\|a(f(x))\circ Df(x)\|^2\,dx
    \leq
  K\int_{\mathbb C}N(f,S,y)\|a(y)\|^2\,dy.
$$

@include{lean:JJMath.Quasiconformal.IsLocalW12On.boundedDistortion_lintegral_norm_comp_sq_le_multiplicity}

In particular, an almost-everywhere finite bound $N(f,S,\cdot)\leq M$
turns this into the usual quasiconformal energy inequality with the extra
factor $M$.  This is the analytic interface needed by the logarithmic
condenser proof of lightness. The protected disk-degree formula below
supplies exactly such a bound.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.boundedDistortion_lintegral_norm_comp_sq_le_of_multiplicity_le}

## Positive regular values and disk degree

The first degree input is already visible in the differential.  A real-linear
map satisfies the sharp lower bound

$$
  \bigl(|\partial_zL|-|\partial_{\bar z}L|\bigr)|\xi|
    \leq |L\xi|.
$$

When $J(L)>0$, the coefficient on the left is positive.  Comparing the affine
map $\xi\mapsto w+L(\xi-z)$ with its complex-linear part shows that every
centered boundary circle has index one.

@include{lean:JJMath.Quasiconformal.norm_weakDZ_sub_norm_weakDBar_mul_le}

@include{lean:JJMath.Quasiconformal.exists_planarCircleIndex_affine_eq_one_of_weakJacobian_pos}

At a Fréchet regular point the nonlinear remainder is smaller than half this
linear lower bound on a sufficiently small disk.  The center is therefore
isolated in its fiber and its local index is one.

@include{lean:JJMath.Quasiconformal.HasFDerivAt.exists_planarCircleIndex_eq_one_of_weakJacobian_pos}

@include{lean:JJMath.Quasiconformal.planarLocalIndex_eq_one_of_hasFDerivAt_of_weakJacobian_pos}

Consequently a positive regular fiber is discrete and locally finite.  For a
smooth map, choose disjoint isolating disks around exactly the preimages in a
given disk.  Smooth perforated-disk additivity then identifies the outer
boundary degree with the number of interior preimages, without imposing any
global finiteness or properness hypothesis.


For arbitrary smooth approximants one must retain signs: mollification need
not preserve nonnegative Jacobian.  A negative-Jacobian regular point has
local index $-1$, so the general regular-value formula is

$$
  \operatorname{ind}\bigl(f|_{\partial B},y\bigr)
    =
  \sum_{x\in B\cap f^{-1}(y)}\operatorname{sgn}J_f(x).
$$

@include{lean:JJMath.Quasiconformal.planarLocalIndex_eq_neg_one_of_hasFDerivAt_of_weakJacobian_neg}

@include{lean:JJMath.Quasiconformal.planarCircleIndex_eq_finsum_jacobianSign_fiber_inter_ball_of_regular}

The negative-Jacobian locus has the same measurable injective-sheet
decomposition as the positive locus, after postcomposition with complex
conjugation.  Its area density is $-J_f$.  Sard's theorem then removes the
critical values, so throughout any target ball separated from the boundary
image the disk degree agrees almost everywhere with the signed regular-fiber
count.

@include{lean:JJMath.Quasiconformal.areaFormula_preimageMultiplicity_of_hasFDerivWithinAt_of_weakJacobian_neg}

@include{lean:JJMath.Quasiconformal.eventually_planarDiskDegree_eq_finsum_jacobianSign_fiber_inter_ball}

The correct approximation bridge is therefore the distributional degree
formula.  For a target test function supported in a ball separated from the
boundary image, it identifies the Jacobian integral with the constant
boundary index times the target integral.  Integrating the signed count with
the positive- and negative-sheet area formulas proves this first for smooth
maps.

@include{lean:JJMath.Quasiconformal.integral_weakJacobian_mul_comp_eq_planarCircleIndex_mul_integral_of_contDiff}

For a continuous $W^{1,2}_{\mathrm{loc}}$ map, the localized standard
mollifiers converge both uniformly on the compact source disk and in its
$W^{1,2}$ graph norm.  Strong $L^1$ convergence of the Jacobians, together
with dominated convergence for the composed target test, passes the
Jacobian-weighted integral to the limit.  Uniform convergence keeps every
approximating boundary loop inside the protected perturbation range, so its
index is eventually the original index.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.exists_smoothApproxGraphL2Data_on_compact_tendstoUniformlyOn}

@include{lean:JJMath.Quasiconformal.PlanarWeakSobolevSmoothApproxGraphL2Data.weakJacobian_test_comp_integral_tendsto_of_tendstoUniformlyOn}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.integral_weakJacobian_mul_comp_eq_planarCircleIndex_mul_integral}

For maps of bounded distortion, the Sobolev multiplicity is almost-everywhere
measurable and its real interpretation is integrable on a source disk.
Comparing its weighted area formula with the distributional degree identity
therefore gives

$$
  N(f,B(z,r),y)
    =
  \operatorname{ind}\bigl(f|_{\partial B(z,r)},w\bigr)
$$

for almost every $y$ in every target ball about $w$ separated from the
boundary image.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.eventually_preimageMultiplicity_toReal_eq_planarCircleIndex_of_boundedDistortion}

There is no remaining good-radius requirement merely to make the boundary
image null.  The full Lusin $N$ property sends every planar-null Euclidean
circle to a null set.  Moreover, compact separation supplies a nonempty
protected target ball, so one may evaluate the almost-everywhere identity at
one point of that ball.  Nonnegativity of multiplicity then proves that every
boundary index away from its boundary image is nonnegative.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.boundedDistortion_volume_image_sphere_eq_zero}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.planarCircleIndex_nonneg_of_boundedDistortion}

For the condenser argument it is important not to demand a global
multiplicity bound.  The covector field supplied by a target cutoff is
supported in a protected target ball, and the multiplicity is bounded there
by the finite disk index.  The pullback estimate has therefore been localized
to the support of the covector field:

$$
  \int_{B(z,r)}\|a(f(x))\circ Df(x)\|^2\,dx
    \leq
  K\,\operatorname{ind}(f|_{\partial B(z,r)},w)
  \int_{\mathbb C}\|a(y)\|^2\,dy.
$$

@include{lean:JJMath.Quasiconformal.IsLocalW12On.boundedDistortion_lintegral_norm_comp_sq_le_planarCircleIndex}

## Proper-map lightness

For a proper map, the inverse image of $\overline B(w,2)$ lies in a large
source disk. If a compact nontrivial continuum $E\subseteq f^{-1}(w)$
existed, compare it with a scaled positive ray outside that disk. These two
plates have strictly positive condenser capacity.

Let $\widetilde u_{w;e^{-n},1}$ be a smooth logarithmic cutoff around $w$.
It vanishes on $E$, while properness makes
$\widetilde u_{w;e^{-n},1}\circ f$ equal to one on the source ray. The smooth
outer chain rule makes this composition an admissible Sobolev competitor.
Its differential vanishes outside the large source disk, and the protected
pullback inequality bounds its energy by a fixed boundary index times
$O(1/n)$. Letting $n\to\infty$ contradicts the positive capacity of the
fixed source condenser.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.compact_connected_fiber_subsingleton_of_boundedDistortion_of_isProperMap}

Taking closures inside the compact proper fiber removes the compactness
assumption on the connected subset. Thus every proper planar map of bounded
distortion is light.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.connected_fiber_subsingleton_of_boundedDistortion_of_isProperMap}

The protected weighted-Jacobian argument turns lightness into openness.
Properness then confines the fiber to a source disk, where protected
almost-everywhere multiplicity is finite. Openness rules out an infinite
fiber, and a final local multiplicity argument makes every isolated local
index positive. This proves the proper open-and-discrete theorem directly.

@include{lean:JJMath.Quasiconformal.open_discrete_and_localIndex_pos_of_boundedDistortion_of_isProperMap}

## The inverse weak differential

At points with positive Jacobian the inverse differential must be
$(Df)^{-1}$; on the zero-Jacobian branch it is harmless to use the total
Wirtinger pseudoinverse.  The area formula first shows that the image of the
measurable zero-Jacobian source set is null.  It then gives local $L^2$ bounds
for the inverse candidate and transports the same $K$-distortion inequality
to the target.

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.volume_ambientMap_image_eq_zero_of_weakJacobian_eq_zero_ae}

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.exists_inverseDifferentialCandidate_memLpOn_compact}

An $L^2$ bound and an almost-everywhere inverse formula do not by themselves
identify a distributional derivative.  The missing step is the planar
Sobolev Piola identity.  Smooth graph approximants prove the adjugate
integration-by-parts formula after a compact cutoff; strong $L^2$ convergence
passes the adjugate terms to the limit, and strong $L^1$ convergence of the
Jacobians handles the main term.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.planarAdjugate_test_identity}

Combining the Piola identity with the Bochner area formula identifies the
pseudoinverse field as the weak differential of the inverse homeomorphism.
The topological orientation predicate is symmetric under inversion, so the
inverse is again $K$-quasiconformal.  In particular the forward map also has
Lusin $N^{-1}$.

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.inverseDifferentialCandidate_isWeakDerivativeOn}

@include{lean:JJMath.Quasiconformal.PreservesPlanarOrientation.symm}

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.symm}

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.hasLusinNInvOn}

The same area-formula package upgrades the nonnegative Jacobian statement to
strict positivity almost everywhere for a quasiconformal homeomorphism. The
zero-Jacobian source set has null image; the inverse Lusin property then pulls
that null image back to a null source set.

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.weakJacobian_pos_ae}

## The weakly holomorphic factor

There is a second use of the inverse differential beyond inverse
quasiconformality. Suppose two real-linear differentials $A$ and $B$ have the
same Beltrami coefficient and $J(B)>0$. Composing $A$ with the inverse of $B$
cancels the conjugate Wirtinger component:

$$
  \bigl(A\circ B^{-1}\bigr)_{\bar z}=0.
$$

The proof avoids division by the Wirtinger determinant. First compose with
the adjugate, where the cancellation is the polynomial identity
$-A_zB_{\bar z}+A_{\bar z}B_z=0$, and then use
$\operatorname{adj}(B)=J(B)B^{-1}$.

@include{lean:JJMath.Quasiconformal.weakDBar_comp_realLinearPseudoInverse_eq_zero_of_same_beltrami}

To use this identity after a Sobolev chain rule one needs a weak form of the
Cauchy--Riemann theorem. If
$g=u+iv\in W^{1,2}_{\mathrm{loc}}(\Omega)$ and
$\partial_{\bar z}g=0$ almost everywhere, then
$u_x=v_y$ and $u_y=-v_x$. Testing these equations against the two first
derivatives of a compactly supported smooth function shows that $u$ and $v$
are weakly harmonic; symmetry of the test's mixed second derivatives is the
cancellation. The Euclidean Weyl lemma makes both components harmonic.
When $g$ is continuous, its classical differential agrees almost everywhere
with its weak differential, and continuity upgrades
$\partial_{\bar z}g=0$ to a pointwise identity. Thus $g$ is holomorphic.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.differentiableOn_complex_of_continuousOn_of_weakDBar_eq_zero_ae}

## Stoilow factorization and the nonproper theorem

The normalized sphere solution fixing infinity has a whole-plane finite
chart. In that chart it is a quasiconformal homeomorphism fixing $0$ and $1$,
solves the prescribed Beltrami equation, and has positive weak Jacobian almost
everywhere.

@include{lean:JJMath.Quasiconformal.exists_normalized_plane_homeomorph_of_beltrami}

Now let $f:\mathbb C\to\mathbb C$ be continuous and locally $W^{1,2}$, and
let $\Phi$ be a quasiconformal homeomorphism with the same coefficient:

$$
  \partial_{\bar z}f=\mu\,\partial_zf,
  \qquad
  \partial_{\bar z}\Phi=\mu\,\partial_z\Phi.
$$

Set $g=f\circ\Phi^{-1}$. The inverse weak differential is the
pseudoinverse of $D\Phi$, the complex Sobolev chain rule gives a weak
differential for $g$, and strict positivity of $J_\Phi$ permits the
pointwise cancellation above. Hence $\partial_{\bar z}g=0$ almost everywhere,
so the Sobolev Weyl lemma makes $g$ entire and

$$
  f=g\circ\Phi.
$$

@include{lean:JJMath.Quasiconformal.exists_differentiable_factor_of_same_weakBeltrami}

Extracting the coefficient
$\mu=\partial_{\bar z}f/\partial_zf$ from the bounded-distortion inequality
and applying the whole-plane measurable Riemann mapping theorem gives the
full Sobolev Stoilow factorization.

@include{lean:JJMath.Quasiconformal.exists_stoilow_factorization_of_boundedDistortion}

If the range of $f$ has at least two points, then the range of $g$ does too.
The holomorphic open-mapping theorem makes $g$ open, and the isolated-zero
theorem makes every fiber of $g$ discrete. Both properties pull back through
$\Phi$. Finally the existing protected-multiplicity theorem turns openness
into strict positivity of every local index.
