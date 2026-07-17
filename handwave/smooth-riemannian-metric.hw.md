# Smooth Riemannian Metrics on Riemann Surfaces

This note isolates the background geometric construction used by the energy
method.  The goal is to put an honest smooth Riemannian metric on the real
tangent bundle of a Riemann surface.

## Real Smooth Surface

A Riemann surface is first regarded as a real smooth surface by forgetting
complex linearity in its holomorphic coordinate changes.

@include{lean:JJMath.Uniformization.SurfaceRealModel}

@include{lean:JJMath.Uniformization.ContMDiffRiemannianMetricOnSurface}

@include{lean:JJMath.Uniformization.SmoothRiemannianMetricOnSurface}

@include{lean:JJMath.Uniformization.complexOneManifold_has_real_smooth_structure}

## Local Coordinate Metrics

The model tangent plane has its Euclidean real inner product.  In a chart,
this form is pulled back through the tangent-coordinate trivialization to
produce a local positive definite symmetric tangent-bilinear form.

@include{lean:JJMath.Uniformization.TangentBilinearFormModel}

@include{lean:JJMath.Uniformization.TangentBilinearFormAt}

@include{lean:JJMath.Uniformization.IsPositiveDefiniteSymmetricTangentForm}

@include{lean:JJMath.Uniformization.euclideanTangentBilinearForm}

@include{lean:JJMath.Uniformization.euclideanTangentBilinearForm_positiveDefinite}

@include{lean:JJMath.Uniformization.positiveDefiniteSymmetricBilinearForm_pullback}

@include{lean:JJMath.Uniformization.tangentBilinearForm_trivializationAt_continuousLinearMapAt}

@include{lean:JJMath.Uniformization.trivialization_symmL_euclideanTangentBilinearForm_positive}

## Patching

The positive definite symmetric forms form a convex fiberwise target, so local
coordinate metrics can be patched by a smooth partition of unity.  The
finite-dimensional boundedness of the unit balls supplies the remaining
boundedness field in the Riemannian metric structure.

@include{lean:JJMath.Uniformization.positiveDefiniteSymmetricTangentForm_convex}

@include{lean:JJMath.Uniformization.exists_local_contMDiff_positiveDefiniteSymmetricTangentForm}

@include{lean:JJMath.Uniformization.exists_contMDiff_positiveDefiniteSymmetricTangentForm_via_partitionOfUnity}

@include{lean:JJMath.Uniformization.positiveDefiniteSymmetricBilinearForm_complex_isCoercive}

@include{lean:JJMath.Uniformization.positiveDefiniteSymmetricTangentForm_isVonNBounded}

@include{lean:JJMath.Uniformization.exists_smoothRiemannianMetricOnSurface_via_partitionOfUnity}

For Riemann surfaces, Radó second countability supplies the
countability needed for the partition-of-unity construction.

@include{lean:JJMath.Uniformization.riemannSurface_has_smoothRiemannianMetric}

## Conformal Background Metrics

For the logarithmic pole construction, the background metric should be
conformal to the complex structure.  In coordinates, this means the
divergence-form coefficient \(\rho g^{ij}\) is the Euclidean identity matrix.
Such metrics are obtained by patching Euclidean metrics pulled back from
holomorphic charts; holomorphic transition maps are conformal, so the patched
metric remains conformal.

@include{lean:JJMath.Uniformization.SurfaceMetricConformalToComplexStructure}

@include{lean:JJMath.Uniformization.BackgroundSurfaceMetricConformalToComplexStructure}

@include{lean:JJMath.Uniformization.IsConformalTangentForm}

@include{lean:JJMath.Uniformization.conformalTangentForm_positiveDefinite}

@include{lean:JJMath.Uniformization.conformalTangentForm_convex}

@include{lean:JJMath.Uniformization.surfaceMetricConformalCoefficient_eq_of_scalar_gram}

@include{lean:JJMath.Uniformization.tangentTrivializationAt_continuousLinearMapAt_complex_linear_nonzero}

@include{lean:JJMath.Uniformization.trivialization_symmL_euclideanTangentBilinearForm_conformal}

@include{lean:JJMath.Uniformization.exists_local_contMDiff_conformalTangentForm}

@include{lean:JJMath.Uniformization.exists_conformal_contMDiff_tangentFormSection_via_holomorphic_partitionOfUnity}

@include{lean:JJMath.Uniformization.conformalContMDiffRiemannianMetricOfTangentFormSection}

@include{lean:JJMath.Uniformization.conformalSmoothMetricOfTangentFormSection}

@include{lean:JJMath.Uniformization.complex_inner_mul_right}

@include{lean:JJMath.Uniformization.complexLinearMap_apply_eq_mul}

@include{lean:JJMath.Uniformization.complexLinearMap_pullback_euclidean_conformal}

@include{lean:JJMath.Uniformization.complexLinearMap_conformal_frame}

@include{lean:JJMath.Uniformization.surfaceChartTangentMap_complex_linear_nonzero}

@include{lean:JJMath.Uniformization.surfaceChartTangentMap_conformal_frame}

@include{lean:JJMath.Uniformization.surfaceMetric_scalar_gram_of_conformal_tangentFormSection_at}

@include{lean:JJMath.Uniformization.surfaceMetricConformalToComplexStructure_of_conformal_tangentFormSection_at}

@include{lean:JJMath.Uniformization.surfaceMetricConformalToComplexStructure_of_conformal_tangentFormSection}

@include{lean:JJMath.Uniformization.exists_conformal_contMDiffRiemannianMetricOnSurface_via_holomorphic_partitionOfUnity}

@include{lean:JJMath.Uniformization.exists_conformal_smoothRiemannianMetricOnSurface_via_holomorphic_partitionOfUnity}

@include{lean:JJMath.Uniformization.riemannSurface_has_conformal_smoothRiemannianMetric}

@include{lean:JJMath.Uniformization.smoothRiemannianMetricOnSurface_induces_conformal_energy_background_metric}

@include{lean:JJMath.Uniformization.riemannSurface_has_conformal_energy_background_metric}

## Riemannian Area Measure

The measure part is separated out as the Riemannian volume measure.  In
coordinates, and with the Borel measurable structure on the surface, its
density is the square root of the determinant of the metric Gram matrix.

@include{lean:JJMath.Uniformization.SmoothPositiveAreaMeasureOnSurface}

@include{lean:JJMath.Uniformization.surfaceMetricGramDetAt}

@include{lean:JJMath.Uniformization.surfaceMetricVolumeDensityAt}

The actual density in an arbitrary coordinate chart is obtained by applying
the chart's tangent map to the standard coordinate frame.

@include{lean:JJMath.Uniformization.surfaceChartTangentMap}

@include{lean:JJMath.Uniformization.surfaceMetricGramDetInChart}

@include{lean:JJMath.Uniformization.surfaceMetricVolumeDensityInChart}

@include{lean:JJMath.Uniformization.riemannianVolumeChartMeasure}

Chart compatibility is stated using the coordinate transition map and its
overlap domain and range.

@include{lean:JJMath.Uniformization.surfaceChartTransition}

@include{lean:JJMath.Uniformization.surfaceChartOverlapDomain}

@include{lean:JJMath.Uniformization.surfaceChartOverlapRange}

@include{lean:JJMath.Uniformization.RiemannianVolumeChartMeasuresCompatible}

@include{lean:JJMath.Uniformization.IsRiemannianVolumeMeasureOnSurface}

The compatibility proof is reduced to
[the Riemannian volume density in one coordinate system is the density in the
other coordinate system multiplied by the absolute Jacobian determinant of the
transition map](lean:JJMath.Uniformization.surfaceMetricVolumeDensityInChart_transform_on_overlap),
and [this density transformation law makes the transition map carry one local
measure to the other](lean:JJMath.Uniformization.riemannianVolumeChartMeasure_map_overlap_eq_of_density_transform).
The first reduction uses that [the transition map between two surface charts
is differentiable on their coordinate overlap](lean:JJMath.Uniformization.surfaceChartTransition_hasFDerivWithinAt_on_overlap),
that [the coordinate tangent frame from one chart is obtained from the
coordinate tangent frame of the other chart by applying the derivative of the
transition map](lean:JJMath.Uniformization.surfaceChartTangentMap_comp_transition_on_overlap),
and the elementary fact that [the corresponding Riemannian volume densities
differ by the absolute Jacobian determinant](lean:JJMath.Uniformization.surfaceMetricVolumeDensityInChart_transform_of_tangentMap_comp).
The second reduction is the weighted change-of-variables theorem on a chart
overlap.

@include{lean:JJMath.Uniformization.surfaceChartTransition_hasFDerivWithinAt_on_overlap}

@include{lean:JJMath.Uniformization.surfaceChartTangentMap_comp_transition_on_overlap}

@include{lean:JJMath.Uniformization.surfaceMetricVolumeDensityInChart_transform_of_tangentMap_comp}

@include{lean:JJMath.Uniformization.weighted_changeOfVariablesOn_overlap}

@include{lean:JJMath.Uniformization.surfaceMetricVolumeDensityInChart_transform_on_overlap}

@include{lean:JJMath.Uniformization.riemannianVolumeChartMeasure_map_overlap_eq_of_density_transform}

@include{lean:JJMath.Uniformization.riemannianVolumeChartMeasuresCompatible_of_smoothMetric}

The global step is separated into three parts.  First,
[the Gram determinant of the metric is smooth in chart coordinates](lean:JJMath.Uniformization.surfaceMetricGramDetInChart_contDiffOn)
and
[the chart tangent map is invertible](lean:JJMath.Uniformization.surfaceChartTangentMap_isInvertible),
so
[the chart tangent map has nonzero determinant](lean:JJMath.Uniformization.surfaceChartTangentMap_det_ne_zero),
which implies that the Gram determinant is
[strictly positive in chart coordinates](lean:JJMath.Uniformization.surfaceMetricGramDetInChart_pos);
taking the square root gives that the coordinate Riemannian density is
[smooth and strictly positive](lean:JJMath.Uniformization.surfaceMetricVolumeDensityInChart_smooth_positive).
Second, the coordinate Riemannian volumes are
[supported on their chart images](lean:JJMath.Uniformization.riemannianVolumeChartMeasure_restrict_target)
and
[finite on compact subsets of a chart image](lean:JJMath.Uniformization.riemannianVolumeChartMeasure_finite_on_compact).
Third, second countability gives
[a countable chart-source cover](lean:JJMath.Uniformization.exists_countable_chartAt_source_cover),
which can be enumerated as
[a sequence of chart sources covering the surface](lean:JJMath.Uniformization.exists_nat_chartAt_source_cover).
The global measure is then constructed by
[summing the measures pulled back from the disjoint coordinate
pieces](lean:JJMath.Uniformization.chartMeasureGluingMeasure).
Each pulled-back piece is
[supported on its assigned source piece](lean:JJMath.Uniformization.chartMeasureGluingLocalMeasure_restrict_sourcePiece),
different pieces are disjoint there, and restricting the global sum to one
piece
[recovers exactly that local contribution](lean:JJMath.Uniformization.chartMeasureGluingMeasure_restrict_sourcePiece).
Inside any fixed target chart, the source pieces determine a measurable
partition of the target chart image, and the restricted coordinate measures
[sum back to the target chart measure](lean:JJMath.Uniformization.chartMeasureGluingOverlapTargetPiece_sum_restrict).
Thus the global pushforward statement is reduced to the one local overlap
calculation that
[a single pulled-back chart piece transforms to the corresponding target
overlap piece](lean:JJMath.Uniformization.chartMeasureGluingLocalMeasure_chart_pushforward_piece),
after which the construction has
[the prescribed chart pushforwards](lean:JJMath.Uniformization.chartMeasureGluingMeasure_chart_pushforward).
For compact finiteness, it is enough to work locally inside a chart: a compact
set contained in one chart source
[has finite glued measure](lean:JJMath.Uniformization.chartMeasureGluingMeasure_compact_subset_chart_source_ne_top),
and local compactness of the surface then implies that the glued measure is
[finite on compact subsets](lean:JJMath.Uniformization.chartMeasureGluingMeasure_finite_on_compact).
Finally,
[a compatible family of locally finite coordinate measures glues to a global
Borel measure with the prescribed chart pushforwards](lean:JJMath.Uniformization.exists_measure_with_compatible_chart_pushforwards).
Applying this gluing theorem to the compatible Riemannian coordinate measures
gives
[a compatible family of smooth positive coordinate volume measures glues to a
global Borel measure](lean:JJMath.Uniformization.exists_measure_with_riemannian_chart_pushforwards).

@include{lean:JJMath.Uniformization.surfaceMetricGramDetInChart_contDiffOn}

@include{lean:JJMath.Uniformization.surfaceChartTangentMap_isInvertible}

@include{lean:JJMath.Uniformization.surfaceChartTangentMap_det_ne_zero}

@include{lean:JJMath.Uniformization.surfaceMetricGramDetInChart_pos}

@include{lean:JJMath.Uniformization.surfaceMetricVolumeDensityInChart_smooth_positive}

@include{lean:JJMath.Uniformization.riemannianVolumeChartMeasure_restrict_target}

@include{lean:JJMath.Uniformization.riemannianVolumeChartMeasure_finite_on_compact}

@include{lean:JJMath.Uniformization.exists_countable_chartAt_source_cover}

@include{lean:JJMath.Uniformization.exists_nat_chartAt_source_cover}

@include{lean:JJMath.Uniformization.chartMeasureGluingSourcePiece}

@include{lean:JJMath.Uniformization.chartMeasureGluingSourcePiece_subset}

@include{lean:JJMath.Uniformization.pairwise_disjoint_chartMeasureGluingSourcePiece}

@include{lean:JJMath.Uniformization.iUnion_chartMeasureGluingSourcePiece}

@include{lean:JJMath.Uniformization.iUnion_chartMeasureGluingSourcePiece_eq_univ}

@include{lean:JJMath.Uniformization.measurableSet_chartMeasureGluingSourcePiece}

@include{lean:JJMath.Uniformization.chartMeasureGluingTargetPiece}

@include{lean:JJMath.Uniformization.chartMeasureGluingTargetPiece_subset}

@include{lean:JJMath.Uniformization.measurableSet_chartMeasureGluingTargetPiece}

@include{lean:JJMath.Uniformization.chartMeasureGluingOverlapTargetPiece}

@include{lean:JJMath.Uniformization.chartMeasureGluingOverlapTargetPiece_subset}

@include{lean:JJMath.Uniformization.measurableSet_chartMeasureGluingOverlapTargetPiece}

@include{lean:JJMath.Uniformization.pairwise_disjoint_chartMeasureGluingOverlapTargetPiece}

@include{lean:JJMath.Uniformization.iUnion_chartMeasureGluingOverlapTargetPiece_eq_target}

@include{lean:JJMath.Uniformization.chartMeasureGluingOverlapTargetPiece_subset_overlapRange}

@include{lean:JJMath.Uniformization.surfaceChartTransition_preimage_overlapTargetPiece_inter_overlapDomain}

@include{lean:JJMath.Uniformization.surfaceChartTransition_continuousOn_overlap}

@include{lean:JJMath.Uniformization.surfaceChartTransition_aemeasurable_restrict_overlapDomain}

@include{lean:JJMath.Uniformization.chartMeasureGluingLocalMeasure}

@include{lean:JJMath.Uniformization.chartMeasureGluingLocalMeasure_restrict_sourcePiece}

@include{lean:JJMath.Uniformization.chartMeasureGluingLocalMeasure_restrict_sourcePiece_of_ne}

@include{lean:JJMath.Uniformization.chartMeasureGluingLocalMeasure_own_chart_pushforward}

@include{lean:JJMath.Uniformization.chartMeasureGluingMeasure}

@include{lean:JJMath.Uniformization.chartMeasureGluingMeasure_restrict_sourcePiece}

@include{lean:JJMath.Uniformization.chartMeasureGluingOverlapTargetPiece_sum_restrict}

@include{lean:JJMath.Uniformization.chartMeasureGluingLocalMeasure_chart_pushforward_piece}

@include{lean:JJMath.Uniformization.chartMeasureGluingMeasure_chart_pushforward}

@include{lean:JJMath.Uniformization.chartMeasureGluingMeasure_compact_subset_chart_source_ne_top}

@include{lean:JJMath.Uniformization.chartMeasureGluingMeasure_finite_on_compact}

@include{lean:JJMath.Uniformization.exists_measure_with_compatible_nat_chart_pushforwards}

@include{lean:JJMath.Uniformization.exists_measure_with_compatible_countable_chart_pushforwards}

@include{lean:JJMath.Uniformization.exists_measure_with_compatible_chart_pushforwards}

@include{lean:JJMath.Uniformization.exists_measure_with_riemannian_chart_pushforwards}

@include{lean:JJMath.Uniformization.exists_riemannianVolumeMeasureOnSurface}

## Metric Differential Operators

The metric-volume construction is packaged as a reusable measure geometry.
This keeps later potential theory from carrying the coordinate gluing data
explicitly.

@include{lean:JJMath.Uniformization.SurfaceMetricMeasureGeometry}

@include{lean:JJMath.Uniformization.SurfaceMetricMeasureGeometry.isFiniteMeasureOnCompacts}

@include{lean:JJMath.Uniformization.smoothRiemannianMetricOnSurface_induces_measure_geometry}

The differential part consists of the exterior derivative on functions, the
inverse-metric pairing on covectors, and a Laplace-Beltrami operator
characterized by integration by parts against compactly supported smooth
tests.

@include{lean:JJMath.Uniformization.HasCompactSupportOnSurface}

@include{lean:JJMath.Uniformization.hasCompactSupportOnSurface_tendsto_zero_at_cocompact}

@include{lean:JJMath.Uniformization.isSmoothOnSurface_mul}

@include{lean:JJMath.Uniformization.isSmoothOnSurface_finset_sum}

@include{lean:JJMath.Uniformization.hasCompactSupportOnSurface_mul_left}

@include{lean:JJMath.Uniformization.hasCompactSupportOnSurface_mul_right}

@include{lean:JJMath.Uniformization.hasCompactSupportOnSurface_finset_sum}

@include{lean:JJMath.Uniformization.IsSurfaceDifferential}

@include{lean:JJMath.Uniformization.surfaceExteriorDerivative}

@include{lean:JJMath.Uniformization.surfaceExteriorDerivative_isSurfaceDifferential}

@include{lean:JJMath.Uniformization.IsCotangentInnerForSurfaceMetric}

@include{lean:JJMath.Uniformization.exists_cotangentInnerForSurfaceMetric}

@include{lean:JJMath.Uniformization.IsLaplaceBeltramiForSurfaceMetric}

@include{lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltrami}

In coordinates, the weak identity is the usual divergence-form computation:
the metric-dual pairing is \(g^{ij}\partial_i f\,\partial_j h\), the
Laplacian is \(\rho^{-1}\partial_i(\rho g^{ij}\partial_j f)\), and compact
support removes the Euclidean boundary terms.  The main coordinate
compatibility step says that the corresponding vector density transforms
correctly on chart overlaps.

@include{lean:JJMath.Uniformization.surfaceMetricCotangentPairingInChart_eq}

@include{lean:JJMath.Uniformization.surfaceMetricGradientPairingInChart_eq}

@include{lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltramiInChart_mul_volumeDensity}

@include{lean:JJMath.Uniformization.surfaceMetricGradientFlux_vectorDensityPullback_on_overlap}

@include{lean:JJMath.Uniformization.surfaceMetricGradientFlux_divergence_transform_on_overlap}

@include{lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltramiInChart_eq_on_overlap}

@include{lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltrami_global_weak_identity}

@include{lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltrami_weak}

@include{lean:JJMath.Uniformization.exists_laplaceBeltramiForSurfaceMetric}

@include{lean:JJMath.Uniformization.SurfaceMetricGradientGeometry}

Combining the metric, the volume measure, the cotangent pairing, and the
Laplace-Beltrami operator gives the background geometry used by the Green
energy construction.

@include{lean:JJMath.Uniformization.BackgroundSurfaceMetricOnSurface}

@include{lean:JJMath.Uniformization.BackgroundSurfaceMetricOnSurface.laplaceBeltrami_eq_divergence}

@include{lean:JJMath.Uniformization.smoothRiemannianMetricOnSurface_induces_gradient_geometry}

@include{lean:JJMath.Uniformization.smoothRiemannianMetricOnSurface_induces_energy_background_metric}

@include{lean:JJMath.Uniformization.riemannSurface_has_energy_background_metric}
