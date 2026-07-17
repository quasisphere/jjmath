# Weyl's Lemma For Surface Energy Solutions

The regularity step needed by the energy method is the harmonic case of
Weyl's lemma.  A locally \(W^{1,2}\) surface function whose weak gradient has
zero distributional divergence should become, in every conformal coordinate
chart, a Euclidean weakly harmonic function.  The Euclidean Weyl theorem then
produces a harmonic representative in the chart; a separate pointwise
representative hypothesis is used when one wants the original chosen
representative itself to be harmonic.

## Weak Equations

The surface weak equation is stated chart-locally using compactly supported
smooth coordinate tests and the metric coefficient contraction
\(\rho g^{ij}\xi_i\partial_j\eta\).  The zero-source case is weak
harmonicity.  In conformal coordinates, this coefficient tensor is the
Euclidean identity, so the chart equation becomes the ordinary Euclidean
zero-divergence identity for the pulled-back weak derivative.

@include{lean:JJMath.Uniformization.IsWeakLaplaceBeltramiSourceOnSurface}

@include{lean:JJMath.Uniformization.IsWeaklyHarmonicOnSurface}

@include{lean:JJMath.Uniformization.weaklyHarmonicOnSurface_of_weakLaplaceBeltramiSource_zero}

@include{lean:JJMath.Uniformization.IsEuclideanWeaklyHarmonicOn}

## Euclidean Weyl Lemma

The Euclidean proof uses cutoff-local standard mollifiers.  The weak
zero-divergence identity makes the mollifications harmonic on protected
neighbourhoods, and local \(L^1\) convergence identifies the harmonic limit
with the weak solution.  The compactness input is the local harmonic
\(L^1\)-estimate: annular averaging gives pointwise control, differentiated
Poisson formulae give derivative control, and Arzelà-Ascoli extracts a
locally uniform harmonic subsequential limit.

@include{lean:JJMath.Uniformization.exists_local_cutoff_standardMollifier_harmonicOnNhd_and_tendsto_ae_and_l1_of_weaklyHarmonicOn}

@include{lean:JJMath.Uniformization.annulus_integral_abs_eq_setIntegral_circleAverage_mul_radius}

@include{lean:JJMath.Uniformization.exists_radius_circleAverage_abs_le_const_mul_integral_abs_annulus_uniform_center}

@include{lean:JJMath.Uniformization.harmonic_center_directionalFderiv_eq_circleAverage_poissonKernel_directionalFderiv_mul}

@include{lean:JJMath.Uniformization.exists_harmonic_fderiv_closedBall_integral_abs_constant}

@include{lean:JJMath.Uniformization.harmonic_locallyL1_bounded_compactExhaustion_ascoli_data}

@include{lean:JJMath.Uniformization.localEuclideanWeylHarmonicRepresentative_of_weaklyHarmonicOn}

@include{lean:JJMath.Uniformization.euclidean_weyl_harmonicRepresentative_of_weaklyHarmonicOn}

## Surface Charts

The remaining bridge is geometric.  In a conformal chart, the surface weak
derivative pulls back to a Euclidean weak derivative, and conformality
identifies the metric coefficient contraction with the Euclidean cotangent
pairing.  Once this chart weak equation is available, the Euclidean Weyl
theorem gives a harmonic chart representative.

@include{lean:JJMath.Uniformization.chartRegion_isOpen_of_weaklyHarmonicOnSurface}

@include{lean:JJMath.Uniformization.exists_euclideanWeakDerivative_zeroDivergence_chart_of_weaklyHarmonicOnSurface}

@include{lean:JJMath.Uniformization.euclideanWeaklyHarmonicOn_chart_of_weaklyHarmonicOnSurface}

@include{lean:JJMath.Uniformization.weyl_harmonicRepresentative_chart_of_weaklyHarmonicOnSurface}

@include{lean:JJMath.Uniformization.weyl_harmonicOnNhd_chart_of_weaklyHarmonicOnSurface}

@include{lean:JJMath.Uniformization.weyl_harmonicOnSurface_of_weaklyHarmonicOnSurface}
