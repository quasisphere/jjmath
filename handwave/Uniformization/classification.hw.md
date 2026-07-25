# Classification by universal cover

Every connected Riemann surface has a simply connected universal cover.  The simply connected uniformization theorem gives exactly three possibilities for that cover: the Riemann sphere, the complex plane, or the unit disk.

@include{lean:JJMath.Uniformization.simplyConnected_riemannSurface_uniformization}

Although the path-class construction starts from a base point, changing the base point does not change the biholomorphic type of the cover.  Lift the endpoint projection from one path-class cover through the other, and lift in the reverse direction.  Uniqueness of covering lifts makes the two maps inverse; because they preserve endpoints, pulled-back complex coordinates make both maps locally the identity.

@include{lean:JJMath.Uniformization.pathHomotopyUniversalCover_basepoint_biholomorphicSurfaces}

Consequently, choosing one base point in the simply connected trichotomy gives a trichotomy quantified over every base point.

@include{lean:JJMath.Uniformization.riemannSurface_hasUniversalCoverTrichotomy}

## Holomorphic covering maps and deck transformations

A holomorphic covering map is a topological covering map whose projection is holomorphic.  For the path-class universal cover, every complex chart is obtained by composing a local-sheet projection with a chart downstairs.  Thus the endpoint projection has the identity as its coordinate expression.

@include{lean:JJMath.Uniformization.IsHolomorphicCoveringMap}


Deck transformations preserve endpoints.  The same chart calculation therefore identifies each deck transformation locally with the identity map between two pulled-back charts, making every deck homeomorphism biholomorphic.

@include{lean:JJMath.Uniformization.PathHomotopyUniversalCover.deckBiholomorphic}

A continuous lift of a holomorphic map into a path-class cover is holomorphic for the same reason: in a pulled-back chart it is the associated base chart composed with the map downstairs.  In particular, a simply connected holomorphic cover can be compared over the base with the path-class universal cover.

@include{lean:JJMath.Uniformization.holomorphicMap_to_pathHomotopyUniversalCover_of_endpoint_eq}

@include{lean:JJMath.Uniformization.simplyConnectedCoverHomeomorph_endpoint}

## Quotient realization

Fix a base point $x_0$ and a biholomorphism $E:\widetilde X_{x_0}\to U$.  Transport the natural deck action of $\pi_1(X,x_0)$ to $U$ by
$$
\gamma\cdot_Eu=E\bigl(\gamma\cdot E^{-1}(u)\bigr).
$$
The map $p_E:U\to X$ given by $p_E(u)=\pi(E^{-1}(u))$ is a surjective covering map, and its fibers are exactly the orbits of this action.  It therefore descends to a homeomorphism
$$
\overline p_E:U/\pi_1(X,x_0)\longrightarrow X.
$$

Give the orbit quotient the complex atlas pulled back from $X$ along this homeomorphism.  It becomes a Riemann surface, $\overline p_E$ becomes biholomorphic, and the orbit projection $U\to U/\pi_1(X,x_0)$ is a holomorphic covering map.  Consequently,
$$
X\cong U/\pi_1(X,x_0)
$$
biholomorphically, for every chosen uniformizing coordinate $E$.

@include{lean:JJMath.Uniformization.PathHomotopyUniversalCover.biholomorphicSurfaces_uniformizingDeckQuotient}

Applying this quotient construction to the sphere, plane, or disk supplied by the universal-cover trichotomy gives the corresponding quotient form of uniformization.

@include{lean:JJMath.Uniformization.riemannSurface_hasQuotientUniformizationTrichotomy}

## The spherical case

Suppose the universal cover is the Riemann sphere.  Transport the deck action through a biholomorphism with the sphere.  Every biholomorphic self-map of the sphere has a fixed point: after moving the image of infinity to infinity or zero, the finite-coordinate map is affine, and a quadratic equation produces a fixed point.  A deck action is free, so no nonidentity deck transformation can occur.  The covering projection is therefore one-to-one and hence a biholomorphism; the base surface is the sphere.

@include{lean:JJMath.Uniformization.biholomorphic_riemannSphere_has_fixedPoint}

@include{lean:JJMath.Uniformization.biholomorphicSurfaces_riemannSphere_of_hasSphericalUniversalCover}

For the converse, we prove directly in the Riemann-sphere model that the sphere is simply connected.  Its two standard coordinate domains, the finite chart $z$ and the reciprocal chart $w=1/z$, cover the sphere.  Pulling this cover back along a loop and using compactness of $[0,1]$ gives finitely many subdivision intervals, with each restricted path contained in one chart.

@include{lean:JJMath.riemannSphere_path_exists_standardChart_subdivision}

Two paths with the same endpoints inside one standard chart are homotopic there, since the chart target is the contractible plane.  Choose a point $p$ away from the finitely many subdivision vertices.  On each interval, if $p$ lies in the chosen chart, replace the path by a path between the same endpoints in the punctured coordinate plane; if $p$ lies outside that chart, keep the path.  The original and replacement pieces are homotopic in the full chart, and their concatenation is a loop omitting $p$.

@include{lean:JJMath.riemannSphere_paths_homotopic_in_standardChart}

@include{lean:JJMath.riemannSphere_path_homotopic_avoiding_point_in_standardChart}

@include{lean:JJMath.riemannSphere_loop_homotopic_avoiding_point}

Translate $p$ to zero and apply spherical inversion, sending it to infinity.  The transformed loop lies in the finite chart and contracts by a convex homotopy in $mathbb C$.  Mapping the contraction back proves that every loop on the sphere is null-homotopic.

@include{lean:JJMath.riemannSphere_loop_nullhomotopic_of_avoids_point}

@include{lean:JJMath.riemannSphere_simplyConnectedSpace}

Thus a surface biholomorphic to the sphere is simply connected.  Its path-class endpoint projection has only one path class over each point and is therefore a biholomorphism, proving the converse and the exact spherical classification.

@include{lean:JJMath.Uniformization.PathHomotopyUniversalCover.endpoint_injective_of_simplyConnected}

@include{lean:JJMath.Uniformization.hasSphericalUniversalCover_iff_biholomorphicSurfaces_riemannSphere}

## Planar deck groups

Suppose instead that the universal cover is the complex plane.  A biholomorphic automorphism of the plane is affine, $z\mapsto az+b$.  If it is nonidentity and has no fixed point, then $a=1$, so it is a translation.  Hence a free deck group on the plane acts by translations.  Proper discontinuity makes its translation subgroup discrete, and the base is biholomorphic to the corresponding translation quotient.

@include{lean:JJMath.Uniformization.biholomorphic_complexPlane_eq_affine}

@include{lean:JJMath.Uniformization.conjugatedPlanarDeckBiholomorphic_apply}

@include{lean:JJMath.Uniformization.planarDeckSubmodule_discreteTopology}

The quotient by a full lattice is constructed directly.  Mathlib supplies the quotient topology and local-homeomorphism charts.  On overlaps, two chosen lifts differ locally by one lattice vector, so every chart transition is locally a translation.  This gives the quotient its complex one-manifold structure, and the quotient projection is a holomorphic covering map.

@include{lean:JJMath.Uniformization.complexTorus_isManifold}

@include{lean:JJMath.Uniformization.complexTorusQuotientMk_isHolomorphicCoveringMap}

The exponential map supplies the standard holomorphic covering of the punctured plane.

@include{lean:JJMath.Uniformization.complexExponentialCover_isHolomorphicCoveringMap}

## Ranks zero, one, and two

Regard a discrete translation subgroup as a ℤ-submodule of the real two-dimensional vector space ℂ.  The equality between real span rank and integral rank for a discrete subgroup bounds its integral rank by two.  Thus its rank is $0$, $1$, or $2$.

@include{lean:JJMath.Uniformization.discreteComplexSubmodule_finrank_cases}

Rank zero gives the plane.  Rank one gives a cyclic translation quotient, biholomorphic through an exponential coordinate to the punctured plane.  Rank two gives a full complex lattice and its complex torus.  The full-rank lattice model has integral rank two.

@include{lean:JJMath.Uniformization.biholomorphicSurfaces_complexPlane_of_planarDeckSubmodule_finrank_zero}

@include{lean:JJMath.Uniformization.biholomorphicSurfaces_complexCylinder_of_planarDeckSubmodule_finrank_one}

@include{lean:JJMath.Uniformization.biholomorphicSurfaces_complexTorus_of_planarDeckSubmodule_finrank_two}


Conversely, the identity, exponential, and lattice quotient maps give surjective holomorphic plane covers of the three models.  Uniqueness of simply connected covers gives a homeomorphism from the plane to the path-class cover, and that forward comparison is holomorphic.  Uniformization cannot make the path-class cover spherical, by noncompactness, or a disk, by Liouville's theorem.  It is therefore planar.

@include{lean:JJMath.Uniformization.hasParabolicUniversalCover_of_holomorphic_complexPlane_cover}

Thus the planar classification is an exact equivalence.

@include{lean:JJMath.Uniformization.hasParabolicUniversalCover_iff_isPlaneCylinderOrTorus}

## The disk remainder

If the universal cover is neither spherical nor planar, the simply connected trichotomy leaves only the unit disk.  Basepoint change propagates this identification to every based universal cover.  The Cayley transform identifies the unit disk with the upper half-plane, so the two hyperbolic formulations are equivalent.

@include{lean:JJMath.Uniformization.hasUnitDiscUniversalCover_iff_not_hasSpherical_and_not_hasParabolic}

Using both the spherical and planar classifications, this says equivalently that the surface is not the sphere, plane, cylinder, or a complex torus.

@include{lean:JJMath.Uniformization.hasUnitDiscUniversalCover_iff_not_biholomorphicSphere_and_not_isPlaneCylinderOrTorus}

In particular, a surface biholomorphic to none of the spherical or parabolic base models has disk universal cover; this direction needs only the already proved spherical and planar forward classifications.

@include{lean:JJMath.Uniformization.hasUnitDiscUniversalCover_of_not_biholomorphicSphere_and_not_isPlaneCylinderOrTorus}

@include{lean:JJMath.Uniformization.hasUnitDiscUniversalCover_iff_hasUpperHalfPlaneUniformizingCover}

Together with the existing pairwise exclusion of the three simply connected models, this proves the universal-cover trichotomy in its upper-half-plane formulation.


The three exact equivalences are collected in the final classification theorem.

@include{lean:JJMath.Uniformization.riemannSurface_universalCover_classification}
