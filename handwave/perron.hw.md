# Perron's Method

Perron's method gives a route to the harmonic Dirichlet problem that is local
enough to avoid assuming second countability of the ambient Riemann surface.
That matters for Rado's theorem: the analytic construction should be available
before second countability has been proved.

This note records the main formalization pipeline.  The supporting lemmas live
in the Lean file and can be followed from these central statements.

## Harmonic And Subharmonic Functions

The harmonic, subharmonic, and superharmonic background is isolated in
[the subharmonicity note](article:subharmonic).  The key imported facts for
Perron's method are the comparison principle, closure of the Perron family
under maxima, and local-to-global behavior.

The maximum-principle input is componentwise, so it remains usable before any
global countability theorem is available.

@include{lean:JJMath.Uniformization.HasComponentwiseMaximumPrincipleGeometry}

@include{lean:JJMath.Uniformization.harmonic_nonpositive_of_boundary_nonpositive_componentwise}

@include{lean:JJMath.Uniformization.subharmonic_le_constant_of_boundary_le}

@include{lean:JJMath.Uniformization.subharmonic_le_superharmonic_of_boundary_le}

## Perron Data

The order-theoretic part of Perron's method only needs a nonempty open region,
not compact closure.  On such a region one can define admissible subfunctions,
their value sets, and the Perron envelope.  If the family is locally bounded
above on compact subsets of the region, the envelope is lower semicontinuous
and is itself locally bounded above.  Nonemptiness is supplied by an explicit
lower bound for the boundary data rather than by compactness.

@include{lean:JJMath.Uniformization.PerronOpen}

@include{lean:JJMath.Uniformization.PerronOpenBoundaryData}

@include{lean:JJMath.Uniformization.perronOpenBoundaryData_eventually_lt_boundary_add}

@include{lean:JJMath.Uniformization.perronOpenBoundaryData_eventually_gt_boundary_sub}

@include{lean:JJMath.Uniformization.IsPerronOpenAdmissible}

@include{lean:JJMath.Uniformization.perronOpenAdmissible_sup}

@include{lean:JJMath.Uniformization.perronOpenEnvelope}

@include{lean:JJMath.Uniformization.PerronOpenFamilyLocallyBoundedAbove}

@include{lean:JJMath.Uniformization.IsBoundedPerronOpenAdmissible}

@include{lean:JJMath.Uniformization.boundedPerronOpenAdmissible_sup}

@include{lean:JJMath.Uniformization.boundedPerronOpenEnvelope}

@include{lean:JJMath.Uniformization.perronOpen_family_nonempty_of_boundary_lower_bound}

@include{lean:JJMath.Uniformization.exists_perronOpenAdmissible_envelope_sub_lt}

@include{lean:JJMath.Uniformization.perronOpenEnvelope_lowerSemicontinuousOn}

@include{lean:JJMath.Uniformization.perronOpenEnvelope_locally_bounded_above_of_family_locally_bounded}

@include{lean:JJMath.Uniformization.boundedPerronOpenEnvelope_lowerSemicontinuousOn}

@include{lean:JJMath.Uniformization.exists_boundedPerronOpenAdmissible_envelope_sub_lt}

For the full Dirichlet problem with boundary values attained by the resulting
candidate, we still use a relatively compact Perron domain.  Compactness is
what turns continuous boundary data into global upper and lower extrema and is
also used in the barrier globalization arguments.

@include{lean:JJMath.Uniformization.PerronDomain}

@include{lean:JJMath.Uniformization.PerronDomain.toPerronOpen}

@include{lean:JJMath.Uniformization.PerronBoundaryData}

@include{lean:JJMath.Uniformization.PerronBoundaryData.toPerronOpenBoundaryData}

@include{lean:JJMath.Uniformization.IsPerronAdmissible}

@include{lean:JJMath.Uniformization.perronEnvelope}

When explicit boundary bounds are available, the compactness step that
extracts extrema from the boundary can be bypassed.  These bounded variants
are the forms to use for noncompact Perron constructions where the admissible
family is controlled directly.

@include{lean:JJMath.Uniformization.perron_family_nonempty_of_boundary_lower_bound}

@include{lean:JJMath.Uniformization.perron_family_locally_bounded_above_of_boundary_upper_bound}

@include{lean:JJMath.Uniformization.perron_family_nonempty_and_locally_bounded_of_boundary_bounds}

@include{lean:JJMath.Uniformization.perronValueSet_nonempty_of_family_nonempty}

@include{lean:JJMath.Uniformization.exists_perronAdmissible_envelope_sub_lt_of_family_nonempty}

@include{lean:JJMath.Uniformization.perronEnvelope_locally_bounded_above_of_family_nonempty_of_family_locally_bounded}

Boundary regularity consists of the componentwise maximum-principle geometry
and a Perron barrier at every boundary point.

@include{lean:JJMath.Uniformization.HasPerronBarrierAt}

For noncompact open regions, the boundary argument is local: a barrier only
needs to live in a neighborhood of the boundary point, while boundedness of
the Perron family controls the rest of the open region.

@include{lean:JJMath.Uniformization.HasLocalPerronOpenBarrierAt}

@include{lean:JJMath.Uniformization.localPerronOpenBarrier_positive_floor_on_frontier}

@include{lean:JJMath.Uniformization.localPerronOpenBarrier_tendsto_zero}

@include{lean:JJMath.Uniformization.localPerronOpenBarrierAt_exists_global_superharmonic_patch}

@include{lean:JJMath.Uniformization.boundedPerronOpenAdmissible_sup_const_affine_negative_barrier}

@include{lean:JJMath.Uniformization.boundedPerronOpenBarrier_upper_family_bound_of_local_barrier}

@include{lean:JJMath.Uniformization.boundedPerronOpenBarrier_lower_calibration_of_local_barrier}

@include{lean:JJMath.Uniformization.boundedPerronOpenBarrier_lower_subfunction_eventually_gt_of_local_barrier}

@include{lean:JJMath.Uniformization.boundedPerronOpenEnvelope_eventually_lt_boundary_add_of_local_barrier}

@include{lean:JJMath.Uniformization.boundedPerronOpenEnvelope_eventually_gt_boundary_sub_of_local_barrier}

@include{lean:JJMath.Uniformization.exteriorTangentDisk_logPotential_has_local_perronOpen_barrier}

@include{lean:JJMath.Uniformization.PerronRegularBoundary}

## Harmonic Replacement

The local operation in Perron's method is harmonic replacement: solve the
Dirichlet problem on a smaller coordinate disk and patch the harmonic solution
back into the original subfunction.  The Euclidean Poisson computation is
isolated in [the disk Poisson extension note](article:poisson-extension-disc).

@include{lean:JJMath.Uniformization.IsCoordinatePerronDisk}

@include{lean:JJMath.Uniformization.harmonic_replacement_exists}

@include{lean:JJMath.Uniformization.harmonic_replacement_dominates_original_on_univ}

@include{lean:JJMath.Uniformization.harmonic_replacement_preserves_admissibility}

@include{lean:JJMath.Uniformization.harmonic_replacement_preserves_open_admissibility}

@include{lean:JJMath.Uniformization.harmonic_replacement_preserves_bounded_open_admissibility}

## Interior Harmonicity

Constants give nonemptiness of the Perron family, and the boundary maximum
principle gives local boundedness.  Harmonic replacement then produces a
directed family of harmonic minorants whose supremum is the Perron envelope.
Harnack convergence gives local uniform convergence, and harmonicity is closed
under locally uniform limits.

@include{lean:JJMath.Uniformization.perron_family_nonempty_and_locally_bounded}

@include{lean:JJMath.Uniformization.perronEnvelope_lowerSemicontinuousOn}

@include{lean:JJMath.Uniformization.harnack_directed_harmonic_minorants_tendstoLocallyUniformlyOn}

@include{lean:JJMath.Uniformization.pointwise_sSup_directed_harmonic_family_harmonicOn_coordinate_disk}

@include{lean:JJMath.Uniformization.exists_coordinate_perron_disk_mem}

@include{lean:JJMath.Uniformization.exists_coordinate_perron_disk_compactly_contained_open}

@include{lean:JJMath.Uniformization.abstract_perron_lifting_principle_on_coordinate_disk}

@include{lean:JJMath.Uniformization.perron_lifting_principle_on_coordinate_disk}

@include{lean:JJMath.Uniformization.perron_envelope_is_harmonic}

@include{lean:JJMath.Uniformization.boundedPerronOpenEnvelope_harmonicOn_coordinate_disk}

@include{lean:JJMath.Uniformization.boundedPerronOpenEnvelope_is_harmonic}

## Boundary Values

At a regular boundary point, calibrated barriers squeeze the Perron envelope
between \(\varphi(p)-\varepsilon\) and \(\varphi(p)+\varepsilon\).  The lower
estimate is produced by an explicit admissible barrier subfunction; the upper
estimate uses comparison with a superharmonic barrier.

@include{lean:JJMath.Uniformization.perronEnvelope_eventually_gt_boundary_sub_of_barrier}

@include{lean:JJMath.Uniformization.perronBarrier_upper_family_bound}

@include{lean:JJMath.Uniformization.perronEnvelope_eventually_lt_boundary_add_of_barrier}

@include{lean:JJMath.Uniformization.perron_envelope_tends_to_boundary_value}

Consequently the Perron Dirichlet candidate solves the harmonic Dirichlet
problem on every regular Perron domain.

@include{lean:JJMath.Uniformization.perron_envelope_solves_dirichlet}

## Smooth Boundary Domains

Smooth boundary points admit Perron barriers by flattening the boundary in a
complex chart and using a local defining function or exterior tangent disk.
The implicit-function input is that
[a centered positive vertical differential gives a local implicit zero graph](lean:JJMath.Uniformization.smoothComplexZeroSet_verticalDerivative_has_local_implicit_graph_at_origin).
The side-identification step is that
[a positive vertical derivative identifies the sublevel side of a local graph](lean:JJMath.Uniformization.smoothComplexSublevelSet_side_of_local_implicit_graph_at_origin);
together these give that
[a centered positive vertical differential gives a local implicit sublevel graph](lean:JJMath.Uniformization.smoothComplexSublevelSet_verticalDerivative_has_local_implicit_graph_at_origin).
After centering and applying adapted orthonormal coordinates this implies that
[a vertical differential gives a local implicit sublevel graph](lean:JJMath.Uniformization.smoothPlaneSublevelSet_verticalDerivative_has_local_implicit_graph).
The Taylor input is that
[a smooth real graph with zero tangent has a quadratic upper bound](lean:JJMath.Uniformization.smoothRealFunction_tangent_zero_has_quadratic_upper_bound).
Together with
[adapted orthonormal coordinates for nonzero real differentials](lean:JJMath.Uniformization.realLinearFunctional_has_adapted_isometry),
this proves that
[a smooth plane sublevel set has adapted graph coordinates](lean:JJMath.Uniformization.smoothPlaneSublevelSet_has_adapted_quadratic_graph_bound).
Together with the explicit exterior-circle calculation, this proves that
[a smooth plane sublevel set has quadratic exterior support](lean:JJMath.Uniformization.smoothPlaneSublevelSet_has_quadratic_exterior_support).
This gives
[a smooth plane sublevel set has an exterior tangent disk](lean:JJMath.Uniformization.smoothPlaneSublevelSet_has_exterior_tangent_disk).
This implies that
[a smooth defining function has an exterior tangent disk](lean:JJMath.Uniformization.smoothBoundaryDefiningFunction_has_exterior_tangent_disk).
Once such a disk is available,
[its logarithmic potential is a local Perron barrier](lean:JJMath.Uniformization.exteriorTangentDisk_logPotential_has_local_perron_barrier),
and therefore
[a smooth defining function gives a local Perron barrier](lean:JJMath.Uniformization.smoothBoundaryDefiningFunction_has_local_perron_barrier).
Then
[a local Perron barrier extends to a global Perron barrier](lean:JJMath.Uniformization.localPerronBarrierAt_globalizes)
by compactness, using
[locally superharmonic functions are superharmonic](lean:JJMath.Uniformization.superharmonicOnSurface_of_locally).
Once those barriers are available, smooth boundary domains with the
componentwise maximum-principle geometry are Perron-regular.

@include{lean:JJMath.Uniformization.smoothBoundaryDomain_boundary_points_have_barriers}

@include{lean:JJMath.Uniformization.smoothBoundaryDomain_perronRegular}

@include{lean:JJMath.Uniformization.perron_dirichlet_solution_on_smooth_boundary_domain}
