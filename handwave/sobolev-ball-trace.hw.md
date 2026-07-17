# Sobolev Traces On Balls

This note records the trace input used for Euclidean ball extensions.  The
setting is a finite-dimensional real inner-product space with Lebesgue
measure.  For a scalar \(W^{1,2}\) function on the unit ball, the goal is to
construct a measurable boundary representative \(\tau\) on the unit sphere
such that the normalized \(L^1\)-error in shrinking inner collars tends to
zero.

@include{lean:JJMath.Uniformization.HasL1TraceFromInsideSphere}

@include{lean:JJMath.Uniformization.HasL1TraceFromOutsideSphere}

## Radial Endpoint Representative

The boundary value is obtained from radial limits.  In stereographic polar
coordinates, the map \((r,y)\mapsto r\sigma(y)\) turns radial rays into
vertical coordinate lines.  Pulling the weak-derivative identity through this
chart reduces the key analytic input to the following slicing statement:
weak derivatives on the product strip \((0,1)\times E\) restrict to almost
every vertical line.

The slicing proof is separated into two mathematical ingredients.  First,
there is a countable family of smooth compactly supported tests on \((0,1)\)
that is dense in the topology of uniform convergence of the function and its
first derivative, with all approximants supported in one compact subinterval.
Second, product testing and Fubini give the one-dimensional weak-derivative
identity for that countable family on one common full-measure set of vertical
lines; the density statement then extends the identity to all smooth compactly
supported tests.

@include{lean:JJMath.Uniformization.exists_countable_c1_dense_smooth_tests_Ioo}

@include{lean:JJMath.Uniformization.realWeakDerivativeOn_Ioo_test_identity_of_countable_c1_dense_test_data}

@include{lean:JJMath.Uniformization.realWeakDerivativeOn_Ioo_of_countable_c1_dense_test_data}

@include{lean:JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_slice_local_integrability_ae_on_unit_strip}

@include{lean:JJMath.Uniformization.compactlySupported_firstCoordinate_slicedIntegral_locallyIntegrable_on_unit_strip}

@include{lean:JJMath.Uniformization.integrableOn_prod_vertical_slice_ae}

@include{lean:JJMath.Uniformization.integrableOn_vertical_slice_ae_of_integrableOn_measurable}

@include{lean:JJMath.Uniformization.locallyIntegrableOn_unit_strip_vertical_slices_ae}

@include{lean:JJMath.Uniformization.firstCoordinateSliceWeakDerivativeResidual}

@include{lean:JJMath.Uniformization.firstCoordinateSliceWeakDerivativeResidual_locallyIntegrable_on_unit_strip}

@include{lean:JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_one_test_slice_residual_pairing_zero_on_unit_strip}

@include{lean:JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_one_test_slice_residual_distribution_zero_on_unit_strip}

@include{lean:JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_one_test_slice_identity_ae_on_unit_strip}

@include{lean:JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_one_test_slice_integral_eq_ae_on_unit_strip}

@include{lean:JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_slice_test_data_ae_on_unit_strip}

@include{lean:JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_fiberwise_realWeakDerivative_on_unit_strip_of_countable_c1_dense_tests}

@include{lean:JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_fiberwise_realWeakDerivative_on_unit_strip}

Once the vertical slicing statement is available, the one-dimensional ACL
representative theorem gives, for almost every direction \(\theta\), an
absolutely continuous representative of \(r\mapsto u(r\theta)\).  The
fundamental theorem of calculus on rays gives
\[
  |u(r\theta)-u(s\theta)|
    \le \int_r^s |du(t\theta)\theta|\,dt .
\]
Passing \(s\uparrow1\) along \(L^1\)-Cauchy boundary slices produces the
endpoint representative \(\tau\) and the radial tail bound.

@include{lean:JJMath.Uniformization.scalarWeakSobolev_stereographic_polar_patch_fiberwise_realWeakDerivative_from_polar_chart_slices}

@include{lean:JJMath.Uniformization.scalarWeakSobolev_stereographic_polar_patch_full_vertical_acl_representative}

@include{lean:JJMath.Uniformization.scalarWeakSobolev_unit_ball_radial_acl_all_segments_ae_sphere}

@include{lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_l1_cauchy_trace_sphere_tendstoInMeasure_data_analytic_leaf}

@include{lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_acl_trace_tail_bound}

## Tail Majorant

The pointwise radial estimate is packaged through the nonnegative tail
majorant
\[
  R(x)=\int_{\|x\|}^1
    |du(t x/\|x\|)(x/\|x\|)|\,dt .
\]
This majorant bounds the distance from \(u(x)\) to the radial extension of
\(\tau\) in every sufficiently thin collar.  Its normalized collar mass tends
to zero because the radial tail integral is controlled by the ordinary
\(L^1\)-mass of \(|du|\) in the same collar, up to a fixed finite constant.

@include{lean:JJMath.Uniformization.euclideanSobolevUnitBallRadialTailMajorant}

@include{lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_l1_trace_bound}

## Interior Trace

The final trace statement is a squeeze argument.  The normalized
\(L^1\)-trace error is bounded by the normalized collar integral of the tail
majorant, and that integral tends to zero for \(du\in L^2\).

@include{lean:JJMath.Uniformization.euclideanSobolev_unit_ball_has_l1_trace_from_inside_core}

@include{lean:JJMath.Uniformization.euclideanSobolev_unit_ball_has_l1_trace_from_inside}
