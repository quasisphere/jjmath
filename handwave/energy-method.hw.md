# Green Functions by the Energy Method

This note records the current energy-method route to Green functions from
positive pure Dirichlet capacity.  The proof chooses a conformal background
metric only as a bookkeeping device for local \(L^2\), weak derivatives, and
regularity.  The final hypothesis is metric-free: positive pure Dirichlet
capacity supplies a conformal representative with the estimates needed below.

Fix a pole \(p\).  Choose a compactly supported logarithmic model
\[
  \phi(z)=-\chi(z)\log |z-z(p)|
\]
with \(\chi=1\) near the pole.  The correction \(h\) is constructed in the
pure \(H^1_0\) completion and decoded only to a local finite-energy scalar
representative.  The final Green function is a regular representative of
\(\phi+h\), not the arbitrary decoded Sobolev representative itself.

## Geometric Setup

The background metric is chosen conformal to the complex structure.  The
cutoff logarithmic model is smooth away from the pole, has compact support,
and has a smooth source supported where the cutoff changes.

@include{lean:JJMath.Uniformization.BackgroundSurfaceMetricOnSurface}

@include{lean:JJMath.Uniformization.BackgroundSurfaceMetricConformalToComplexStructure}

@include{lean:JJMath.Uniformization.riemannSurface_has_conformal_energy_background_metric}

@include{lean:JJMath.Uniformization.LogarithmicCutoffPoleModel}

@include{lean:JJMath.Uniformization.exists_logarithmicCutoffPoleModel}

## Pure Capacity And The Hilbert Space

The variational space is the homogeneous Dirichlet completion of compactly
supported smooth differentials.  Its norm is the pure Dirichlet norm, so a
continuous source functional immediately gives a Riesz representative and
the Euler equation.

@include{lean:JJMath.Uniformization.GreenSobolevH10SmoothCompactSupport}

@include{lean:JJMath.Uniformization.greenSobolevH10SmoothCompactSupport_admits_hilbert_structure}

@include{lean:JJMath.Uniformization.greenSobolevH10SmoothCompactSupport_denseRange_core}

@include{lean:JJMath.Uniformization.greenSobolevH10SmoothCompactSupportSource}

@include{lean:JJMath.Uniformization.greenSobolevH10RieszRepresentative}

@include{lean:JJMath.Uniformization.greenSobolevH10SmoothCompactSupportEnergy_rieszRepresentative_eulerLagrange}

Positive pure Dirichlet capacity controls compact-local \(L^2\) mass of
compactly supported smooth scalar primitives by their pure Dirichlet energy.
This is the mathematical input that makes compactly supported sources
continuous on the smooth Dirichlet core and lets Cauchy sequences of
primitives converge locally.

@include{lean:JJMath.Uniformization.HasPositivePureDirichletCapacityAtInfinity}

@include{lean:JJMath.Uniformization.HasPureDirichletCapacityAtInfinity}

## Local Weak Correction

The Riesz representative is decoded to a local finite-energy correction.
Smooth compactly supported scalar tests are lifted to directions in the pure
completion, and compatibility of the local Dirichlet pairing with the Hilbert
inner product gives the weak Green equation.  The correction is not merely a
completed differential: it comes with a local Sobolev scalar representative
whose weak gradient is the completed differential, and it satisfies the
opposite-source equation on the punctured surface.

@include{lean:JJMath.Uniformization.GreenSobolevH10LocalCorrection}

@include{lean:JJMath.Uniformization.GreenSobolevH10SmoothTest}

@include{lean:JJMath.Uniformization.IsLocalWeakGreenCorrection}

@include{lean:JJMath.Uniformization.GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData}

@include{lean:JJMath.Uniformization.greenSobolevH10SmoothCompactSupportLocalRieszCorrection_isLocalWeakGreenCorrection}

The variational construction is now separated into three steps.  First,
positive pure capacity gives a compact-local \(L^2\) scalar representative
of the pure Riesz vector, with the chosen finite-energy differential as weak
gradient.  Second, compactly supported coordinate tests are extended by zero
to admissible smooth pure tests, and the global smooth-test Euler identity is
localized to the punctured chart region.  Third, the Sobolev representative
and the punctured weak equation package as a finite-Dirichlet correction, and
the completed Hilbert pairing gives the smooth-test Dirichlet identity.

@include{lean:JJMath.Uniformization.GreenSobolevH10SmoothCompactSupportRieszRepresentativeSobolevData}

@include{lean:JJMath.Uniformization.greenSobolevH10SmoothCompactSupport_rieszRepresentative_exists_sobolev_data}

@include{lean:JJMath.Uniformization.smoothChartTestExtension_differential_memHilbertSchmidtL2}

@include{lean:JJMath.Uniformization.greenSobolevH10SmoothCompactSupport_rieszRepresentative_punctured_chartTest_source_identity}

@include{lean:JJMath.Uniformization.greenSobolevH10SmoothCompactSupport_rieszRepresentative_has_honest_local_correction}

@include{lean:JJMath.Uniformization.logarithmicCutoffPoleModel_has_smooth_h10_local_weak_correction_data}

@include{lean:JJMath.Uniformization.exists_local_weak_green_correction_of_pure_dirichlet_capacity}

## Analytic Upgrade

For a local correction, the weak potential is \(\phi+h\).  The energy
construction first produces a regular representative \(G\) which is harmonic
off the pole and has the standard logarithmic singularity.  The simply
connected boundary-at-infinity argument then supplies nonnegativity and
compact positive superlevels, which are the exact downstream properties
needed for the exponential disk map.

@include{lean:JJMath.Uniformization.localEnergyGreenPotential}

The analytic work first proves source cancellation. The cutoff model solves
the weak equation with its stored source on the punctured surface, while the
local correction package supplies the opposite-source identity there. Weyl
regularity then gives a regular harmonic representative of the weak
potential.

@include{lean:JJMath.Uniformization.logarithmicCutoffPoleModel_isIntrinsicLocalSobolevH1On_punctured}

@include{lean:JJMath.Uniformization.logarithmicCutoffPoleModel_punctured_chart_weak_source_identity}

@include{lean:JJMath.Uniformization.logarithmicCutoffPoleModel_isWeakLaplaceBeltramiSourceOn_punctured}

The regular representative is constructed from Weyl's lemma in charts.  The
remaining local analytic leaf is the logarithmic singularity at the pole,
proved from the cutoff model and removability of bounded punctured harmonic
functions.

@include{lean:JJMath.Uniformization.greenSobolevH10SmoothCompactSupportLocalWeakCorrectionData_weaklyHarmonicOn_punctured}

@include{lean:JJMath.Uniformization.exists_regularLocalEnergyPotentialRepresentative_of_weaklyHarmonicOnSurface}

@include{lean:JJMath.Uniformization.greenSobolevH10SmoothCompactSupportLocalWeakCorrectionData_regular_logarithmic_singularity}

## Compact-Superlevel Boundary At Infinity

The pure homogeneous zero-trace condition is used through fixed-level
truncations.  A global signed fixed-level clip is constant near the
logarithmic pole and is an admissible pure zero-trace test.  After reducing
to the noncompact simply connected case, the escaping-domain extraction is
pole-aware: the logarithmic pole is the only allowed exceptional frontier
point.  Testing punctured harmonicity against the clip and applying the chain
rule rules out a crossing between the two fixed levels.  A parallel
negative-level truncation gives nonnegativity.

@include{lean:JJMath.Uniformization.continuousOn_punctured_escaping_strictSuperlevel_component_yields_poleAware_level_domain}

@include{lean:JJMath.Uniformization.positive_strictSuperlevel_high_component_escapes_or_pole_mem_closure}

@include{lean:JJMath.Uniformization.strictSuperlevel_components_with_pole_closure_eq_of_preconnected_punctured_nhds}

@include{lean:JJMath.Uniformization.logarithmic_singularity_positive_strictSuperlevel_has_preconnected_punctured_nhds}

@include{lean:JJMath.Uniformization.noncompact_poleNormalized_positive_superlevel_has_escaping_high_component}

@include{lean:JJMath.Uniformization.noncompact_poleNormalized_positive_superlevel_has_poleAware_escaping_level_domain}

@include{lean:JJMath.Uniformization.noncompact_regular_positive_superlevel_has_high_component_away_from_pole}

@include{lean:JJMath.Uniformization.regular_negative_superlevel_has_escaping_component}

@include{lean:JJMath.Uniformization.regular_negative_superlevel_yields_escaping_level_domain}

@include{lean:JJMath.Uniformization.CompactSuperlevelGreenFunctionWithPole}

## Final Theorem

The final assembly unpacks the metric-free positive-capacity hypothesis,
chooses the conformal background metric it provides, constructs the local
weak correction for the chosen pole, upgrades the local potential to an
honest compact-superlevel Green datum, and returns it with the prescribed
pole.
