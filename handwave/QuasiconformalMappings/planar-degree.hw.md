# Planar winding numbers and local indices

The topological inversion step needs integer degrees, rather than only an
unnamed homotopy class of punctured-plane loops. The exponential covering

$$
  \exp:\mathbb C\longrightarrow\mathbb C\setminus\{0\}
$$

provides the normalization. Every loop $\gamma$ based at $1$ has a unique
logarithmic lift $L_\gamma$ beginning at $0$.

@include{lean:JJMath.Quasiconformal.puncturedLoopLogLift}

More generally, a path $\gamma$ from $a$ to $b$ has a lift beginning at the
principal logarithm of $a$. Its endpoint difference

$$
  \Delta\log(\gamma)=L_\gamma(1)-L_\gamma(0)
$$

is the useful additive quantity.

@include{lean:JJMath.Quasiconformal.puncturedPathLogLift}

@include{lean:JJMath.Quasiconformal.puncturedPathLogIncrement}

It adds under concatenation, changes sign under reversal, and is invariant
under endpoint-fixed homotopy.

@include{lean:JJMath.Quasiconformal.puncturedPathLogIncrement_trans}


@include{lean:JJMath.Quasiconformal.puncturedPathLogIncrement_eq_of_homotopic}

Since $\gamma(1)=1$, its lifted endpoint is an integral period:

$$
  L_\gamma(1)=2\pi i\,\operatorname{wind}(\gamma),
  \qquad \operatorname{wind}(\gamma)\in\mathbb Z.
$$

@include{lean:JJMath.Quasiconformal.puncturedLoopWindingNumber}

@include{lean:JJMath.Quasiconformal.puncturedLoopLogLift_one_eq_windingNumber_mul}

For a closed path based at an arbitrary nonzero point, dividing by its base
point gives a loop based at $1$, and its logarithmic increment is exactly the
corresponding winding period.

@include{lean:JJMath.Quasiconformal.puncturedPathLogIncrement_eq_windingNumber_mul}

Based homotopies lift with the same initial point and therefore have the same
endpoint. Concatenating two loops concatenates the first lift with a translate
of the second lift, so winding numbers add.

@include{lean:JJMath.Quasiconformal.puncturedLoopWindingNumber_eq_of_homotopic}


The positive unit circle has the explicit logarithmic lift
$L(t)=2\pi i t$, hence winding number one.

@include{lean:JJMath.Quasiconformal.puncturedLoopWindingNumber_positiveCircleLoop}

The local cancellation mechanism is already topological. If a continuous map
from a square avoids zero, the bottom-then-right and left-then-top routes are
endpoint-fixed homotopic. Additivity therefore gives

$$
  \Delta\log(B)+\Delta\log(R)
    =\Delta\log(L)+\Delta\log(T).
$$

@include{lean:JJMath.Quasiconformal.puncturedPathLogIncrement_square_boundary}

Equivalently, the positively oriented boundary loop of every such square has
zero logarithmic period.


For the global perforated-disk argument, pointwise multiplication is more
efficient than assembling cells. Logarithmic increments turn products into
sums and integer powers into integer multiples:

$$
  \Delta\log(\gamma\delta)
    =\Delta\log(\gamma)+\Delta\log(\delta),
  \qquad
  \Delta\log(\gamma^n)=n\,\Delta\log(\gamma).
$$

@include{lean:JJMath.Quasiconformal.puncturedPathLogIncrement_pointwiseMul}

@include{lean:JJMath.Quasiconformal.puncturedPathLogIncrement_zpow}

A closed loop with zero logarithmic increment has a closed logarithmic lift.
The lift descends through the endpoint identification
$[0,1]/(0\sim1)\simeq S^1$. Extending this complex logarithm from $S^1$ to
the plane by Tietze and exponentiating gives a continuous filling which never
meets zero.

@include{lean:JJMath.Quasiconformal.exists_punctured_extension_of_logIncrement_eq_zero}

## Boundary and local indices

For a continuous planar map $f$, a circle whose image avoids $w$ determines
an integer boundary index: translate the image loop by $-w$, normalize its
initial point to $1$, and take its winding number.

@include{lean:JJMath.Quasiconformal.planarCircleIndex}

If an annulus of concentric circles has image disjoint from $w$, the boundary
index is independent of the radius.

@include{lean:JJMath.Quasiconformal.planarCircleIndex_eq_of_radial_homotopy}

A point $z\in f^{-1}(w)$ in a discrete fiber has a small disk containing no
other point of that fiber. Every two such isolating radii give the same circle
index, so they define an unambiguous integer local index.

@include{lean:JJMath.Quasiconformal.exists_isFiberIsolatingRadius_of_isDiscrete_fiber}

@include{lean:JJMath.Quasiconformal.planarCircleIndex_eq_of_isFiberIsolatingRadius}

@include{lean:JJMath.Quasiconformal.planarLocalIndex}

For a finite fiber inside an outer disk, the isolating radii can be chosen
simultaneously so that their closed disks are pairwise disjoint and remain
strictly inside the outer disk.

@include{lean:JJMath.Quasiconformal.exists_pairwiseDisjoint_isolatingRadii_of_finite_fiber_subset_ball}

Remove the corresponding open disks. The remaining perforated closed disk is
compact and contains every outer and inner boundary circle. Smooth
approximation can be made uniformly smaller there than the positive distance
$|f-w|$. The approximating smooth map still avoids $w$, and straight-line
homotopy preserves every boundary winding number.

@include{lean:JJMath.Quasiconformal.perforatedClosedDisk}

@include{lean:JJMath.Quasiconformal.exists_contDiff_avoiding_approximationOn_perforatedClosedDisk}

@include{lean:JJMath.Quasiconformal.planarCircleIndex_eq_of_norm_sub_lt}

On a finite perforated disk, the positive outer index is the sum of the
positive inner indices.

@include{lean:JJMath.Quasiconformal.planarCircleIndex_eq_sum_of_contDiff_of_avoids_perforatedClosedDisk}

The proof uses coordinate vortices instead of a polygonal decomposition. If
$n_i$ is the index on the $i$th inner circle, divide the
target-avoiding map by

$$
  \prod_i (q-c_i)^{n_i}.
$$

On the $i$th inner boundary, its own coordinate vortex has index one and all
other vortex factors have index zero. The corrected boundary loop therefore
has zero increment and can be filled without zero. Since the inner disks are
disjoint, the fillings paste to the corrected map over a finite closed cover.

@include{lean:JJMath.Quasiconformal.exists_punctured_extension_of_vortexCorrected_perforatedClosedDisk}

The corrected map now extends without zero across the full outer disk. Radial
contraction forces its outer logarithmic increment to vanish.

@include{lean:JJMath.Quasiconformal.puncturedClosedBallBoundaryPath_logIncrement_eq_zero}

Every center $c_i$ lies inside the outer circle, hence each coordinate vortex
has outer increment $2\pi i$. The product law gives the desired sum formula.
This needs no smoothness in its topological core, differential forms, or
bespoke cell complex.

For a finite discrete fiber enclosed by a circle, boundary additivity is the
central topological statement:

$$
  i(f,\partial B;w)=\sum_{z\in f^{-1}(w)}i(f,z;w).
$$

@include{lean:JJMath.Quasiconformal.planarCircleIndex_eq_planarFiberIndexSum_of_fiber_subset_ball}

For an asymptotically identity map the left side is one on a sufficiently
large circle. If all local indices are positive, the finite sum can therefore
have only one term; the map is bijective, and the surviving local index is
one. For a plane homeomorphism, local index one is exactly what is needed to
recover the boundary-loop definition of planar orientation preservation.

@include{lean:JJMath.Quasiconformal.preservesPlanarOrientation_wholePlaneSubtype_of_localIndex_eq_one}

The planar degree layer is complete: logarithmic increments, winding numbers,
local indices, vortex cancellation, finite hole filling, perforated-disk
boundary additivity, and the continuous finite-fiber formula are all proved.

The general topological interface is the planar Whyburn--Stoilow theorem. A
continuous map is light when every connected subset of every point fiber is
a singleton or empty. If, in addition, every target-avoiding positive circle
has nonnegative index, then the map is open, its fibers are discrete, and
every local index is positive. This general theorem remains useful, but the
proper bounded-distortion route below now proves the needed conclusions
directly.

The first separation layer of this theorem is now formalized. A compact
totally disconnected set has arbitrarily small ambient open neighborhoods
whose boundaries miss the set: choose a clopen piece in the compact
subspace, then separate it from the complementary compact piece by
normality.

@include{lean:JJMath.Quasiconformal.exists_open_closure_subset_frontier_disjoint_of_compact_totallyDisconnected}

Two general compactness facts drive the finer separation argument. Connected
components in compact Hausdorff spaces have arbitrarily small clopen
neighborhoods, and a decreasing family of compact connected sets has
connected nonempty intersection.

@include{lean:JJMath.Quasiconformal.exists_isClopen_connectedComponent_subset_of_compact}

@include{lean:JJMath.Quasiconformal.isConnected_iInter_of_antitone_nonempty_compact_connected}

Intersecting a light fiber with a closed disk gives the compact version
locally. Taking the connected component containing the distinguished point
then produces a relatively compact connected open neighborhood $V$ with

$$
  x\in V,\qquad \overline V\subseteq U,\qquad
  \partial V\cap f^{-1}(f(x))=\varnothing.
$$

@include{lean:JJMath.Quasiconformal.exists_open_closure_subset_frontier_disjoint_fiber_of_light}

@include{lean:JJMath.Quasiconformal.frontier_connectedComponentIn_subset_frontier_of_isOpen}

@include{lean:JJMath.Quasiconformal.exists_connected_open_closure_subset_frontier_disjoint_fiber_of_light}

Compactness upgrades avoidance at one target to stable avoidance. The
positive minimum of $|f-w|$ on $\partial V$ gives an $\varepsilon>0$ such
that the same boundary misses every fiber over $B(w,\varepsilon)$.



The nested-continuum argument then traps a component of the inverse image of
a sufficiently small closed target ball strictly inside the chosen source
neighborhood. If every such component reached the source boundary, their
intersection would be a nontrivial continuum in one point fiber.

@include{lean:JJMath.Quasiconformal.exists_closedBall_preimage_component_disjoint_frontier_of_light}

Taking a clopen neighborhood of the trapped component inside the compact
closed-ball preimage and separating its two compact pieces in the plane gives
a genuine normal source domain. Thus, in every prescribed neighborhood of
$x$, there are a relatively compact connected open set $W\ni x$ and $r>0$
such that

$$
  |f(z)-f(x)|>r
  \qquad(z\in\partial W).
$$

@include{lean:JJMath.Quasiconformal.exists_normalSourceDomain_of_light}

The boundary-distance gap already supplies the target neighborhood needed by
the open-mapping argument: the whole ball $B(f(x),r)$ belongs to the
component of $f(x)$ in the complement of $f(\partial W)$.


The standard degree argument uses one further property. If the degree of
$f$ on $W$ is nonzero at $f(x)$, local constancy away from
$f(\partial W)$ and vanishing outside $f(W)$ force the entire component of
$f(x)$ in $\mathbb C\setminus f(\partial W)$ to lie in $f(W)$. This support
consequence, for every relatively compact open domain, is enough to prove
openness.


For the Sobolev bounded-distortion route, one can avoid defining degree on
the rough boundary of $W$. Choose a smooth source cutoff $\chi$ which is one
on the selected compact part of the inverse image and whose derivative
vanishes over a protected target ball. The scalar Piola identity says that
the weighted Jacobian functional

$$
  \varphi\longmapsto
  \int_{\mathbb C}\chi(z)^2J_f(z)\varphi(f(z))\,dz
$$

has zero distributional derivative on that ball.

@include{lean:JJMath.Quasiconformal.integral_fderiv_realLinearAdjugate_eq_zero_of_contDiff}

@include{lean:JJMath.Quasiconformal.integral_cutoff_composition_jacobian_eq_zero_of_contDiff}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.integral_cutoff_composition_jacobian_eq_zero}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.integral_cutoff_jacobian_fderiv_comp_eq_zero}

The normal-domain boundary gap provides exactly such a cutoff in every
prescribed source neighborhood.

@include{lean:JJMath.Quasiconformal.exists_degreeCutoff_of_light}

The measure-theoretic form of the Sobolev area formula identifies the
pushforward of Jacobian mass with multiplicity-weighted area. Weighting once
more by $\chi^2$ gives a finite source measure whose pushforward is absolutely
continuous with respect to area. Its Radon--Nikodym density is denoted by
$\rho$.

@include{lean:JJMath.Quasiconformal.weakJacobianMeasureOn}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.map_weakJacobianMeasureOn_eq_withDensity_preimageMultiplicity}

@include{lean:JJMath.Quasiconformal.weightedWeakJacobianMeasureOn}

@include{lean:JJMath.Quasiconformal.weightedWeakJacobianDensity}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.map_weightedWeakJacobianMeasureOn_absolutelyContinuous}

The protected Piola identity becomes

$$
  \int_{\mathbb C}\rho(y)D\varphi(y)v\,dy=0
$$

for every test function supported in the protected target ball and every
$v\in\mathbb C$.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.weightedWeakJacobianDensity_sq_stationary_on_ball}

An $L^1$ function whose distributional gradient vanishes on a ball is almost
everywhere constant there. The proof passes through the Euclidean Weyl lemma
and then applies Sobolev zero-gradient rigidity.

@include{lean:JJMath.Uniformization.integrable_ae_eq_const_on_ball_of_distributionalGradient_zero}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.weightedWeakJacobianDensity_sq_ae_eq_const_on_ball}

The constant cannot vanish. Indeed, zero Jacobian mass on a source ball
would force $Df=0$ almost everywhere there; continuity would make $f$
constant on the ball, contradicting lightness. Removing the nonzero cutoff
factor near the distinguished source point therefore proves that the
constant density is strictly positive.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.eqOn_const_of_differential_eq_zero_ae}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.integral_weakJacobian_pos_on_ball_of_boundedDistortion_of_light}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.weightedWeakJacobianDensity_sq_ae_eq_pos_const_on_ball}

If a point of the protected target ball were outside
$f(\operatorname{supp}\chi)$, compactness of the support would give a smaller
target ball missing that image. The pushforward measure would vanish there,
contradicting its positive constant density. Hence the protected ball is
covered, and choosing the cutoff inside an arbitrary source neighborhood
proves openness.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.ball_subset_image_tsupport_of_degreeCutoff}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.isOpenMap_of_boundedDistortion_of_light}

The multiplicity comparison also supplies a short discreteness argument in
the proper case. More generally, suppose an open map has finite constant
multiplicity almost everywhere on a target ball. If its fiber inside the
counted open source set were infinite, choose more than that multiplicity
many fiber points and pairwise disjoint neighborhoods around them. Openness
makes every nearby target occur in each neighborhood, contradicting the
almost-everywhere multiplicity bound.

@include{lean:JJMath.Quasiconformal.finite_fiber_inter_of_isOpenMap_of_eventually_preimageMultiplicity_eq}

For a proper bounded-distortion map, the inverse image of a small closed
target disk is compact and lies inside a large source disk. The large
boundary circle is uniformly separated from the target, so protected
multiplicity is finite almost everywhere there. The preceding argument makes
the whole fiber finite.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.finite_fiber_of_boundedDistortion_of_isProperMap}

Strict positivity of local index has an equally direct proof. An isolating
disk contains a smaller disk whose image is, by openness, a neighborhood of
the target value. Choose a nearby target where multiplicity agrees with the
isolating circle index. It has a preimage in the smaller disk, so that
multiplicity and hence the circle index are nonzero.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.planarCircleIndex_pos_of_boundedDistortion_of_isOpenMap}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.planarLocalIndex_pos_of_boundedDistortion_of_isOpenMap}

Combining proper-map lightness, direct openness, finite fibers, and positive
local indices completes the proper open-and-discrete theorem used by the
principal solution.

@include{lean:JJMath.Quasiconformal.open_discrete_and_localIndex_pos_of_boundedDistortion_of_isProperMap}

The nonproper whole-plane quasiregular theorem is now proved separately by
analytic Stoilow factorization; once that argument supplies openness and
discrete fibers, the positive local-index result above finishes its
degree-theoretic conclusion.


The all-purpose topological Whyburn--Stoilow statement remains an optional
leaf. It is used by neither the proper principal-solution route nor the
analytic Stoilow route.
