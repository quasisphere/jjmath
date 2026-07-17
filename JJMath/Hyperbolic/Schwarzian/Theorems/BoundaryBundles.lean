import JJMath.Hyperbolic.Schwarzian.Theorems.LocalMaps

/-!
# Split Schwarzian theorem wrappers and hyperbolic specialization
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems

/-- The coefficient scalar Taylor input is now supplied by `LocalSchwarzianData` analyticity. -/
theorem coefficientScalarTaylor
    (_B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems) :
    HolomorphicSchwarzianCoefficientScalarTaylorTheorem :=
  holomorphicSchwarzianCoefficientScalarTaylor_of_localAnalytic

/-- The bundled scalar Taylor input gives the Taylor-control data used upstream. -/
theorem coefficientTaylorControl
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems) :
    HolomorphicSchwarzianCoefficientTaylorControlTheorem :=
  holomorphicSchwarzianCoefficientTaylorControl_of_scalarTaylor
    B.coefficientScalarTaylor

/-- The bundled Taylor-control input gives the geometric majorants used by Frobenius. -/
theorem coefficientMajorants
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems) :
    HolomorphicSchwarzianCoefficientGeometricMajorantTheorem :=
  holomorphicSchwarzianCoefficientGeometricMajorant_of_taylorControl
    B.coefficientTaylorControl

/-- The bundled local boundary gives local projective Schwarzian developing maps. -/
theorem localProjectiveDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius
    B.holomorphicSchwarzian
    (holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant
      B.coefficientMajorants)

/-- The bundled local boundary gives metric-recovering Schwarzian ball pre-atlases. -/
theorem metricRecoveringBallPreAtlas
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetRiccatiAnalyticBoundary
    B.localProjectiveDevelopingMaps B.twoJetNormalization B.riccatiBoundary

/-- The bundled local boundary gives metric-recovering Schwarzian pre-atlases. -/
theorem metricRecoveringPreAtlas
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_ballPreAtlas
    B.metricRecoveringBallPreAtlas

/-- The bundled local boundary gives metric-recovering normalization atlases. -/
theorem metricRecoveringNormalizationAtlas
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_ballPreAtlas
    B.metricRecoveringBallPreAtlas

/-- The bundled local boundary gives real upper-half-plane branch atlases. -/
theorem realUpperHalfPlaneBranchAtlas
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering
    B.metricRecoveringNormalizationAtlas B.realTransitions

/-- The bundled local boundary gives genuine local upper-half-plane developing maps. -/
theorem localUpperHalfPlaneDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusTwoJetRiccatiAnalyticBoundary
    B.holomorphicSchwarzian
    (holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant
      B.coefficientMajorants)
    B.twoJetNormalization B.riccatiBoundary

/--
The bundled coefficient/Frobenius/Riccati part also gives genuine local
upper-half-plane developing maps through the sharper Frobenius normal-form
route.  This avoids the broad `twoJetNormalization` field: the remaining
inputs for this compatibility theorem are explicit Schwarzian invariance for
the normal-form postcomposition and upper-half-plane landing of the normalized
two-jet.  The newer `localUpperHalfPlaneDevelopingMaps_of_normalFormLift`
replaces both by the sharper lift boundary.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_frobeniusSchwarzianLanding
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems)
    (hSchwarzian :
      LocalProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem)
    (hUpper : HyperbolicProjectiveTwoJetNormalizationLandsInUpperHalfPlaneTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusSchwarzianLanding
    B.holomorphicSchwarzian
    (holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant
      B.coefficientMajorants)
    hSchwarzian hUpper B.riccatiBoundary.recoversMetric

/--
The bundled coefficient/Frobenius/Riccati part gives genuine local
upper-half-plane developing maps through the sharper Frobenius normal-form
route, with explicit Schwarzian invariance now proved internally.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_frobeniusLanding
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems)
    (hUpper : HyperbolicProjectiveTwoJetNormalizationLandsInUpperHalfPlaneTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.localUpperHalfPlaneDevelopingMaps_of_frobeniusSchwarzianLanding
    localProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem hUpper

/--
The bundled coefficient/Frobenius/Riccati part gives genuine local
upper-half-plane developing maps from an explicit normal-form `ℍ` lift with
derivative identifications on the landing ball.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_normalFormLift
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems)
    (hLift : LocalProjectiveFrobeniusNormalFormUpperHalfPlaneLiftTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_normalFormLift
    B.holomorphicSchwarzian
    (holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant
      B.coefficientMajorants)
    hLift B.riccatiBoundary.recoversMetric

/--
The bundled coefficient/Frobenius/Riccati part gives genuine local
upper-half-plane developing maps from derivative identification for the
explicit normal-form affine branch on the landing ball.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_derivativeIdentification
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems)
    (hDeriv : LocalProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivativeIdentification
    B.holomorphicSchwarzian
    (holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant
      B.coefficientMajorants)
    hDeriv B.riccatiBoundary.recoversMetric

/--
The bundled coefficient/Frobenius/Riccati part gives genuine local
upper-half-plane developing maps through the canonical third-derivative
normal-form route.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_canonicalThirdDerivativeIdentification
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_canonicalThirdDerivativeIdentification
    B.holomorphicSchwarzian
    (holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant
      B.coefficientMajorants)
    localProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem
    B.riccatiBoundary.recoversMetric

/--
The bundled coefficient/Frobenius/Riccati part gives genuine local
upper-half-plane developing maps from the intrinsic Frobenius quotient-rule
boundary.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_affineHasDerivAt
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems)
    (hBase : LocalProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_affineHasDerivAt
    B.holomorphicSchwarzian
    (holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant
      B.coefficientMajorants)
    hBase B.riccatiBoundary.recoversMetric

/--
The bundled coefficient/Frobenius/Riccati part gives genuine local
upper-half-plane developing maps from the individual Frobenius-solution
derivative theorem.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_solutionHasDerivAt
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems)
    (hSolDeriv : CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.localUpperHalfPlaneDevelopingMaps_of_affineHasDerivAt
    (localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem_of_solutionHasDerivAt
      hSolDeriv)

/--
The bundled coefficient/Frobenius/Riccati part gives genuine local
upper-half-plane developing maps from the scalar termwise-derivative
power-series boundary.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_scalarFormalPowerSeriesDeriv
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems)
    (hScalarDeriv : ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.localUpperHalfPlaneDevelopingMaps_of_solutionHasDerivAt
    (centeredSchwarzianFrobeniusSolutionHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
      hScalarDeriv)

/--
The bundled coefficient/Frobenius/Riccati part gives genuine local
upper-half-plane developing maps with scalar termwise differentiation
discharged from mathlib.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_termwiseDifferentiation
    (B : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.localUpperHalfPlaneDevelopingMaps_of_canonicalThirdDerivativeIdentification

end HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems

/--
Sharper bundled local boundary for producing real upper-half-plane branch
atlases from a hyperbolic Liouville factor.

Compared with `HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems`, this
replaces the broad branch-level real-transition input by the actual
atlas-level input still needed downstream: distinct metric-recovering branches
with nonempty overlap have real Mobius transitions.  The diagonal and empty
overlap cases are handled formally by the local atlas machinery.
-/
structure HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems where
  /-- Hyperbolic Liouville factors produce holomorphic local Schwarzian data. -/
  holomorphicSchwarzian : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
  /-- Local projective Schwarzian maps admit the prescribed hyperbolic 2-jet normalization. -/
  twoJetNormalization : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem
  /-- The Riccati analytic boundary gives metric recovery for the normalized 2-jet. -/
  riccatiBoundary : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems
  /-- Distinct overlapping metric-recovering atlas branches have real Mobius transitions. -/
  overlappingOffDiagonalRealTransitions :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem

namespace HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems

/-- The coefficient scalar Taylor input is supplied by `LocalSchwarzianData` analyticity. -/
theorem coefficientScalarTaylor
    (_B : HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems) :
    HolomorphicSchwarzianCoefficientScalarTaylorTheorem :=
  holomorphicSchwarzianCoefficientScalarTaylor_of_localAnalytic

/-- The bundled scalar Taylor input gives the Taylor-control data used upstream. -/
theorem coefficientTaylorControl
    (B : HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems) :
    HolomorphicSchwarzianCoefficientTaylorControlTheorem :=
  holomorphicSchwarzianCoefficientTaylorControl_of_scalarTaylor
    B.coefficientScalarTaylor

/-- The bundled Taylor-control input gives the geometric majorants used by Frobenius. -/
theorem coefficientMajorants
    (B : HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems) :
    HolomorphicSchwarzianCoefficientGeometricMajorantTheorem :=
  holomorphicSchwarzianCoefficientGeometricMajorant_of_taylorControl
    B.coefficientTaylorControl

/-- The sharper bundled local boundary gives local projective Schwarzian developing maps. -/
theorem localProjectiveDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius
    B.holomorphicSchwarzian
    (holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant
      B.coefficientMajorants)

/-- The sharper bundled local boundary gives metric-recovering Schwarzian ball pre-atlases. -/
theorem metricRecoveringBallPreAtlas
    (B : HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetRiccatiAnalyticBoundary
    B.localProjectiveDevelopingMaps B.twoJetNormalization B.riccatiBoundary

/-- The sharper bundled local boundary gives metric-recovering Schwarzian pre-atlases. -/
theorem metricRecoveringPreAtlas
    (B : HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_ballPreAtlas
    B.metricRecoveringBallPreAtlas

/-- The sharper bundled local boundary gives metric-recovering normalization atlases. -/
theorem metricRecoveringNormalizationAtlas
    (B : HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_ballPreAtlas
    B.metricRecoveringBallPreAtlas

/-- The sharper bundled local boundary gives real upper-half-plane branch atlases. -/
theorem realUpperHalfPlaneBranchAtlas
    (B : HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering_overlappingOffDiagonal
    B.metricRecoveringNormalizationAtlas B.overlappingOffDiagonalRealTransitions

/-- The sharper bundled local boundary gives genuine local upper-half-plane developing maps. -/
theorem localUpperHalfPlaneDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusTwoJetRiccatiAnalyticBoundary
    B.holomorphicSchwarzian
    (holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant
      B.coefficientMajorants)
    B.twoJetNormalization B.riccatiBoundary

/--
The sharper bundled local boundary also gives genuine local upper-half-plane
developing maps through the canonical third-derivative route, so the scalar
termwise-differentiation boundary remains discharged in the overlap-sharp
package.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_termwiseDifferentiation
    (B : HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_canonicalThirdDerivativeIdentification
    B.holomorphicSchwarzian
    (holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant
      B.coefficientMajorants)
    localProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem
    B.riccatiBoundary.recoversMetric

end HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems

/--
Sharper bundled local boundary for producing real upper-half-plane branch
atlases from a hyperbolic Liouville factor.

This has the same downstream fields as
`HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems`, but asks for the
concrete Riccati calculus package.  The algebraic conversion to the older
Riccati analytic boundary is proved above.
-/
structure HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems where
  /-- Hyperbolic Liouville factors produce holomorphic local Schwarzian data. -/
  holomorphicSchwarzian : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
  /-- Local projective Schwarzian maps admit the prescribed hyperbolic 2-jet normalization. -/
  twoJetNormalization : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem
  /-- Concrete Riccati calculus plus the pullback calculation give metric recovery. -/
  riccatiCalculusBoundary : HyperbolicTwoJetRiccatiCalculusBoundaryTheorems
  /-- Metric-recovering upper-half-plane branches have real Mobius transitions. -/
  realTransitions : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem

namespace HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems

/-- Forget the concrete Riccati calculus provenance, retaining the older bundle. -/
def toAnalyticBoundary
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems) :
    HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems where
  holomorphicSchwarzian := B.holomorphicSchwarzian
  twoJetNormalization := B.twoJetNormalization
  riccatiBoundary := B.riccatiCalculusBoundary.toRiccatiAnalyticBoundary
  realTransitions := B.realTransitions

/-- The coefficient scalar Taylor input is supplied by local analyticity. -/
theorem coefficientScalarTaylor
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems) :
    HolomorphicSchwarzianCoefficientScalarTaylorTheorem :=
  B.toAnalyticBoundary.coefficientScalarTaylor

/-- The bundled scalar Taylor input gives Taylor-control data. -/
theorem coefficientTaylorControl
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems) :
    HolomorphicSchwarzianCoefficientTaylorControlTheorem :=
  B.toAnalyticBoundary.coefficientTaylorControl

/-- The bundled Taylor-control input gives the geometric majorants. -/
theorem coefficientMajorants
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems) :
    HolomorphicSchwarzianCoefficientGeometricMajorantTheorem :=
  B.toAnalyticBoundary.coefficientMajorants

/-- The sharper bundled local boundary gives local projective developing maps. -/
theorem localProjectiveDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem :=
  B.toAnalyticBoundary.localProjectiveDevelopingMaps

/-- The sharper bundled local boundary gives metric-recovering ball pre-atlases. -/
theorem metricRecoveringBallPreAtlas
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem :=
  B.toAnalyticBoundary.metricRecoveringBallPreAtlas

/-- The sharper bundled local boundary gives metric-recovering pre-atlases. -/
theorem metricRecoveringPreAtlas
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem :=
  B.toAnalyticBoundary.metricRecoveringPreAtlas

/-- The sharper bundled local boundary gives metric-recovering normalization atlases. -/
theorem metricRecoveringNormalizationAtlas
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  B.toAnalyticBoundary.metricRecoveringNormalizationAtlas

/-- The sharper bundled local boundary gives real upper-half-plane branch atlases. -/
theorem realUpperHalfPlaneBranchAtlas
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  B.toAnalyticBoundary.realUpperHalfPlaneBranchAtlas

/-- The sharper bundled local boundary gives genuine local upper-half-plane developing maps. -/
theorem localUpperHalfPlaneDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.toAnalyticBoundary.localUpperHalfPlaneDevelopingMaps

/-- The normal-form lift route, with the concrete Riccati calculus bundle. -/
theorem localUpperHalfPlaneDevelopingMaps_of_normalFormLift
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems)
    (hLift : LocalProjectiveFrobeniusNormalFormUpperHalfPlaneLiftTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.toAnalyticBoundary.localUpperHalfPlaneDevelopingMaps_of_normalFormLift hLift

/-- The derivative-identification route, with the concrete Riccati calculus bundle. -/
theorem localUpperHalfPlaneDevelopingMaps_of_derivativeIdentification
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems)
    (hDeriv : LocalProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.toAnalyticBoundary.localUpperHalfPlaneDevelopingMaps_of_derivativeIdentification hDeriv

/-- The canonical third-derivative route, with the concrete Riccati calculus bundle. -/
theorem localUpperHalfPlaneDevelopingMaps_of_canonicalThirdDerivativeIdentification
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.toAnalyticBoundary.localUpperHalfPlaneDevelopingMaps_of_canonicalThirdDerivativeIdentification

/-- The intrinsic quotient-rule route, with the concrete Riccati calculus bundle. -/
theorem localUpperHalfPlaneDevelopingMaps_of_affineHasDerivAt
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems)
    (hBase : LocalProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.toAnalyticBoundary.localUpperHalfPlaneDevelopingMaps_of_affineHasDerivAt hBase

/-- The individual Frobenius-solution derivative route, with the concrete bundle. -/
theorem localUpperHalfPlaneDevelopingMaps_of_solutionHasDerivAt
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems)
    (hSolDeriv : CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.toAnalyticBoundary.localUpperHalfPlaneDevelopingMaps_of_solutionHasDerivAt hSolDeriv

/--
The concrete Riccati calculus bundle gives local upper-half-plane developing
maps with scalar termwise differentiation discharged from mathlib.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_termwiseDifferentiation
    (B : HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.localUpperHalfPlaneDevelopingMaps_of_canonicalThirdDerivativeIdentification

end HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems

/--
Sharpest local boundary currently recorded for the local converse.

This is the same theorem package as
`HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems`, but its Riccati field
uses the canonical Frechet-Wirtinger derivatives of the original and pullback
conformal factors.
-/
structure HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems where
  /-- Hyperbolic Liouville factors produce holomorphic local Schwarzian data. -/
  holomorphicSchwarzian : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
  /-- Local projective Schwarzian maps admit the prescribed hyperbolic 2-jet normalization. -/
  twoJetNormalization : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem
  /-- Pullback calculation plus canonical Riccati calculus give metric recovery. -/
  canonicalRiccatiBoundary : HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems
  /-- Metric-recovering upper-half-plane branches have real Mobius transitions. -/
  realTransitions : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem

namespace HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems

/-- Forget to the concrete-calculus local boundary. -/
def toCalculusBoundary
    (B : HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems) :
    HyperbolicLiouvilleSchwarzianCalculusBoundaryTheorems where
  holomorphicSchwarzian := B.holomorphicSchwarzian
  twoJetNormalization := B.twoJetNormalization
  riccatiCalculusBoundary := B.canonicalRiccatiBoundary.toRiccatiCalculusBoundary
  realTransitions := B.realTransitions

/-- Forget to the older analytic-boundary package. -/
def toAnalyticBoundary
    (B : HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems) :
    HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems :=
  B.toCalculusBoundary.toAnalyticBoundary

/-- The canonical local boundary gives local projective developing maps. -/
theorem localProjectiveDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem :=
  B.toCalculusBoundary.localProjectiveDevelopingMaps

/-- The canonical local boundary gives metric-recovering ball pre-atlases. -/
theorem metricRecoveringBallPreAtlas
    (B : HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem :=
  B.toCalculusBoundary.metricRecoveringBallPreAtlas

/-- The canonical local boundary gives metric-recovering normalization atlases. -/
theorem metricRecoveringNormalizationAtlas
    (B : HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  B.toCalculusBoundary.metricRecoveringNormalizationAtlas

/-- The canonical local boundary gives real upper-half-plane branch atlases. -/
theorem realUpperHalfPlaneBranchAtlas
    (B : HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  B.toCalculusBoundary.realUpperHalfPlaneBranchAtlas

/-- The canonical local boundary gives genuine local upper-half-plane developing maps. -/
theorem localUpperHalfPlaneDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.toCalculusBoundary.localUpperHalfPlaneDevelopingMaps

/-- The normal-form lift route, with the canonical Riccati bundle. -/
theorem localUpperHalfPlaneDevelopingMaps_of_normalFormLift
    (B : HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems)
    (hLift : LocalProjectiveFrobeniusNormalFormUpperHalfPlaneLiftTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.toCalculusBoundary.localUpperHalfPlaneDevelopingMaps_of_normalFormLift hLift

/-- The derivative-identification route, with the canonical Riccati bundle. -/
theorem localUpperHalfPlaneDevelopingMaps_of_derivativeIdentification
    (B : HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems)
    (hDeriv : LocalProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.toCalculusBoundary.localUpperHalfPlaneDevelopingMaps_of_derivativeIdentification hDeriv

/-- The canonical third-derivative route, with the canonical Riccati bundle. -/
theorem localUpperHalfPlaneDevelopingMaps_of_canonicalThirdDerivativeIdentification
    (B : HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.toCalculusBoundary.localUpperHalfPlaneDevelopingMaps_of_canonicalThirdDerivativeIdentification

/--
The canonical local boundary gives local upper-half-plane developing maps with
scalar termwise differentiation discharged from mathlib.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_termwiseDifferentiation
    (B : HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  B.localUpperHalfPlaneDevelopingMaps_of_canonicalThirdDerivativeIdentification

end HyperbolicLiouvilleSchwarzianCanonicalBoundaryTheorems

/--
Full local boundary using the corrected Frechet-Wirtinger Riccati route.

This is the atlas-level counterpart of the corrected local-map boundary below:
it keeps the usual holomorphic-Schwarzian, two-jet normalization, and
real-transition inputs, but uses the metric-scaled Wirtinger-Riccati
metric-recovery package instead of the older canonical Riccati calculus bundle.
-/
structure HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems where
  /-- Hyperbolic Liouville factors produce holomorphic local Schwarzian data. -/
  holomorphicSchwarzian : HyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
  /-- Local projective Schwarzian maps admit the prescribed hyperbolic 2-jet normalization. -/
  twoJetNormalization : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem
  /-- Pullback derivative-identification plus corrected Wirtinger-Riccati metric recovery. -/
  derivIdentifiedCanonicalMetricWirtingerBoundary :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems
  /-- Metric-recovering upper-half-plane branches have real Mobius transitions. -/
  realTransitions : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem

namespace HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems

/-- The corrected full boundary gives two-jet metric recovery. -/
theorem recoversMetric
    (B : HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.derivIdentifiedCanonicalMetricWirtingerBoundary.recoversMetric

/-- The coefficient scalar Taylor input is supplied by local analyticity. -/
theorem coefficientScalarTaylor
    (_B : HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems) :
    HolomorphicSchwarzianCoefficientScalarTaylorTheorem :=
  holomorphicSchwarzianCoefficientScalarTaylor_of_localAnalytic

/-- The bundled scalar Taylor input gives Taylor-control data. -/
theorem coefficientTaylorControl
    (B : HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems) :
    HolomorphicSchwarzianCoefficientTaylorControlTheorem :=
  holomorphicSchwarzianCoefficientTaylorControl_of_scalarTaylor
    B.coefficientScalarTaylor

/-- The bundled Taylor-control input gives the geometric majorants. -/
theorem coefficientMajorants
    (B : HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems) :
    HolomorphicSchwarzianCoefficientGeometricMajorantTheorem :=
  holomorphicSchwarzianCoefficientGeometricMajorant_of_taylorControl
    B.coefficientTaylorControl

/-- The corrected full boundary gives local projective developing maps. -/
theorem localProjectiveDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_frobenius
    B.holomorphicSchwarzian
    (holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant
      B.coefficientMajorants)

/-- The corrected full boundary gives metric-recovering ball pre-atlases. -/
theorem metricRecoveringBallPreAtlas
    (B : HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem_of_twoJetDerivIdentifiedMetricWirtingerBoundary
    B.localProjectiveDevelopingMaps B.twoJetNormalization
    B.derivIdentifiedCanonicalMetricWirtingerBoundary

/-- The corrected full boundary gives metric-recovering pre-atlases. -/
theorem metricRecoveringPreAtlas
    (B : HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_ballPreAtlas
    B.metricRecoveringBallPreAtlas

/-- The corrected full boundary gives metric-recovering normalization atlases. -/
theorem metricRecoveringNormalizationAtlas
    (B : HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_ballPreAtlas
    B.metricRecoveringBallPreAtlas

/-- The corrected full boundary gives real upper-half-plane branch atlases. -/
theorem realUpperHalfPlaneBranchAtlas
    (B : HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering
    B.metricRecoveringNormalizationAtlas B.realTransitions

/-- The corrected full boundary gives genuine local upper-half-plane developing maps. -/
theorem localUpperHalfPlaneDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_frobeniusTwoJetNormalization
    B.holomorphicSchwarzian
    (holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant
      B.coefficientMajorants)
    B.twoJetNormalization B.recoversMetric

/--
The corrected full boundary gives genuine local upper-half-plane developing
maps through the canonical Frobenius normal-form route, avoiding the broad
two-jet-normalization field for the local-map projection.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_canonicalThirdDerivativeIdentification
    (B : HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_canonicalThirdDerivativeIdentification
    B.holomorphicSchwarzian
    (holomorphicSchwarzianFrobeniusPairExistence_of_coefficientGeometricMajorant
      B.coefficientMajorants)
    localProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem
    B.recoversMetric

end HyperbolicLiouvilleSchwarzianMetricWirtingerBoundaryTheorems

/--
Smallest local-map boundary currently recorded for the local converse.

The holomorphic-Schwarzian, Frobenius existence, normal-form chain rule, and
upper-half-plane landing parts are all supplied internally.  The only remaining
local-map input is the derivative-identified canonical pullback/Riccati
metric-recovery package.
-/
structure HyperbolicLiouvilleSchwarzianLocalMapCanonicalBoundaryTheorems where
  /-- Pullback derivative-identification plus canonical Riccati metric recovery. -/
  derivIdentifiedCanonicalBoundary :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems

namespace HyperbolicLiouvilleSchwarzianLocalMapCanonicalBoundaryTheorems

/-- The local-map boundary gives two-jet metric recovery. -/
theorem recoversMetric
    (B : HyperbolicLiouvilleSchwarzianLocalMapCanonicalBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.derivIdentifiedCanonicalBoundary.recoversMetric

/-- The local-map boundary gives genuine local upper-half-plane developing maps. -/
theorem localUpperHalfPlaneDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianLocalMapCanonicalBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivIdentifiedCanonicalRiccatiBoundary
    B.derivIdentifiedCanonicalBoundary

/--
The local-map boundary gives genuine local upper-half-plane developing maps
through the canonical Frobenius normal-form route.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_canonicalThirdDerivativeIdentification
    (B : HyperbolicLiouvilleSchwarzianLocalMapCanonicalBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_canonicalThirdDerivativeIdentification
    hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
    holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic
    localProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem
    B.recoversMetric

/-- The local-map boundary also gives local projective developing maps by forgetting `ℍ`. -/
theorem localProjectiveDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianLocalMapCanonicalBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_upperHalfPlane
    B.localUpperHalfPlaneDevelopingMaps

end HyperbolicLiouvilleSchwarzianLocalMapCanonicalBoundaryTheorems

/--
Smallest local-map boundary using the corrected Frechet-Wirtinger Riccati
route.

Compared with `HyperbolicLiouvilleSchwarzianLocalMapCanonicalBoundaryTheorems`,
this replaces the older canonical Riccati calculus side by the honest
metric-scaled Wirtinger-Riccati theorem.
-/
structure HyperbolicLiouvilleSchwarzianLocalMapMetricWirtingerBoundaryTheorems where
  /-- Pullback derivative-identification plus corrected Wirtinger-Riccati metric recovery. -/
  derivIdentifiedCanonicalMetricWirtingerBoundary :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems

namespace HyperbolicLiouvilleSchwarzianLocalMapMetricWirtingerBoundaryTheorems

/-- The corrected local-map boundary gives two-jet metric recovery. -/
theorem recoversMetric
    (B : HyperbolicLiouvilleSchwarzianLocalMapMetricWirtingerBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.derivIdentifiedCanonicalMetricWirtingerBoundary.recoversMetric

/-- The corrected local-map boundary gives genuine local upper-half-plane developing maps. -/
theorem localUpperHalfPlaneDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianLocalMapMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivIdentifiedCanonicalMetricWirtingerRiccatiBoundary
    B.derivIdentifiedCanonicalMetricWirtingerBoundary

/--
The corrected local-map boundary gives genuine local upper-half-plane
developing maps through the canonical Frobenius normal-form route.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_canonicalThirdDerivativeIdentification
    (B : HyperbolicLiouvilleSchwarzianLocalMapMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_canonicalThirdDerivativeIdentification
    hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
    holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic
    localProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem
    B.recoversMetric

/-- The corrected local-map boundary also gives local projective developing maps. -/
theorem localProjectiveDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianLocalMapMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_upperHalfPlane
    B.localUpperHalfPlaneDevelopingMaps

end HyperbolicLiouvilleSchwarzianLocalMapMetricWirtingerBoundaryTheorems

/--
Local-map boundary using derivative algebra and the corrected
Frechet-Wirtinger Riccati route.

The Poincare Laplacian calculation is not an input: derivative algebra is
converted to actual affine derivative algebra, and the mixed-expression
calculation supplies the Laplacian field.
-/
structure HyperbolicLiouvilleSchwarzianLocalMapDerivativeAlgebraMetricWirtingerBoundaryTheorems where
  /-- Derivative algebra plus corrected Wirtinger-Riccati metric recovery. -/
  derivativeAlgebraCanonicalMetricWirtingerBoundary :
    HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

namespace HyperbolicLiouvilleSchwarzianLocalMapDerivativeAlgebraMetricWirtingerBoundaryTheorems

/-- The derivative-algebra local-map boundary gives two-jet metric recovery. -/
theorem recoversMetric
    (B :
      HyperbolicLiouvilleSchwarzianLocalMapDerivativeAlgebraMetricWirtingerBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.derivativeAlgebraCanonicalMetricWirtingerBoundary.recoversMetric

/--
The derivative-algebra local-map boundary gives genuine local upper-half-plane
developing maps.
-/
theorem localUpperHalfPlaneDevelopingMaps
    (B :
      HyperbolicLiouvilleSchwarzianLocalMapDerivativeAlgebraMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_derivativeAlgebra_and_wirtingerRiccati
    B.derivativeAlgebraCanonicalMetricWirtingerBoundary.canonicalPullbackDerivativeAlgebra
    B.derivativeAlgebraCanonicalMetricWirtingerBoundary.canonicalMetricWirtingerRiccati

/--
The derivative-algebra local-map boundary gives genuine local upper-half-plane
developing maps through the canonical Frobenius normal-form route.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_canonicalThirdDerivativeIdentification
    (B :
      HyperbolicLiouvilleSchwarzianLocalMapDerivativeAlgebraMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_canonicalThirdDerivativeIdentification
    hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
    holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic
    localProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem
    B.recoversMetric

/-- The derivative-algebra local-map boundary also gives local projective maps. -/
theorem localProjectiveDevelopingMaps
    (B :
      HyperbolicLiouvilleSchwarzianLocalMapDerivativeAlgebraMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_upperHalfPlane
    B.localUpperHalfPlaneDevelopingMaps

end HyperbolicLiouvilleSchwarzianLocalMapDerivativeAlgebraMetricWirtingerBoundaryTheorems

/--
Smallest local-map boundary using actual affine branch derivative data and the
corrected Frechet-Wirtinger Riccati route.

This is the concrete local version of the current remaining analytic boundary:
the pullback side is stated with `HasDerivAt` inputs rather than already
identified `deriv` fields.
-/
structure HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeMetricWirtingerBoundaryTheorems where
  /-- Affine derivative pullback data plus corrected Wirtinger-Riccati metric recovery. -/
  affineDerivativeCanonicalMetricWirtingerBoundary :
    HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems

namespace HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeMetricWirtingerBoundaryTheorems

/-- The affine-derivative local-map boundary gives two-jet metric recovery. -/
theorem recoversMetric
    (B : HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeMetricWirtingerBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.affineDerivativeCanonicalMetricWirtingerBoundary.recoversMetric

/--
The affine-derivative local-map boundary gives genuine local
upper-half-plane developing maps.
-/
theorem localUpperHalfPlaneDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_affineDerivative_and_wirtingerRiccati
    B.affineDerivativeCanonicalMetricWirtingerBoundary.canonicalPullbackAffineDerivative
    B.affineDerivativeCanonicalMetricWirtingerBoundary.canonicalMetricWirtingerRiccati

/--
The affine-derivative local-map boundary gives genuine local upper-half-plane
developing maps through the canonical Frobenius normal-form route.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_canonicalThirdDerivativeIdentification
    (B : HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_canonicalThirdDerivativeIdentification
    hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
    holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic
    localProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem
    B.recoversMetric

/-- The affine-derivative local-map boundary also gives local projective developing maps. -/
theorem localProjectiveDevelopingMaps
    (B : HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_upperHalfPlane
    B.localUpperHalfPlaneDevelopingMaps

end HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeMetricWirtingerBoundaryTheorems

/--
Smallest local-map boundary using actual affine branch derivative algebra and
the corrected Frechet-Wirtinger Riccati route.

Compared with
`HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeMetricWirtingerBoundaryTheorems`,
this does not ask for a Poincare Laplacian field.  The Laplacian identity is
derived from the explicit mixed-expression calculation.
-/
structure HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeAlgebraMetricWirtingerBoundaryTheorems where
  /--
  Affine derivative algebra plus corrected Wirtinger-Riccati metric recovery.
  -/
  affineDerivativeAlgebraCanonicalMetricWirtingerBoundary :
    HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

namespace HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeAlgebraMetricWirtingerBoundaryTheorems

/-- Forget to the older affine-derivative local-map boundary. -/
def toAffineDerivativeMetricWirtingerBoundary
    (B :
      HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeAlgebraMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeMetricWirtingerBoundaryTheorems where
  affineDerivativeCanonicalMetricWirtingerBoundary :=
    (B.affineDerivativeAlgebraCanonicalMetricWirtingerBoundary).toAffineDerivativeCanonicalMetricWirtingerRiccatiBoundary

/-- The affine-derivative-algebra local-map boundary gives two-jet metric recovery. -/
theorem recoversMetric
    (B :
      HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeAlgebraMetricWirtingerBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.affineDerivativeAlgebraCanonicalMetricWirtingerBoundary.recoversMetric

/--
The affine-derivative-algebra local-map boundary gives genuine local
upper-half-plane developing maps.
-/
theorem localUpperHalfPlaneDevelopingMaps
    (B :
      HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeAlgebraMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_affineDerivativeAlgebra_and_wirtingerRiccati
    B.affineDerivativeAlgebraCanonicalMetricWirtingerBoundary.canonicalPullbackAffineDerivativeAlgebra
    B.affineDerivativeAlgebraCanonicalMetricWirtingerBoundary.canonicalMetricWirtingerRiccati

/--
The affine-derivative-algebra local-map boundary gives genuine local
upper-half-plane developing maps through the canonical Frobenius normal-form
route.
-/
theorem localUpperHalfPlaneDevelopingMaps_of_canonicalThirdDerivativeIdentification
    (B :
      HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeAlgebraMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalUpperHalfPlaneDevelopingMapsTheorem_of_canonicalThirdDerivativeIdentification
    hyperbolicLiouvilleProducesHolomorphicSchwarzianTheorem
    holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic
    localProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem
    B.recoversMetric

/-- The affine-derivative-algebra local-map boundary also gives local projective maps. -/
theorem localProjectiveDevelopingMaps
    (B :
      HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeAlgebraMetricWirtingerBoundaryTheorems) :
    HyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem :=
  hyperbolicLiouvilleProducesLocalProjectiveDevelopingMapsTheorem_of_upperHalfPlane
    B.localUpperHalfPlaneDevelopingMaps

end HyperbolicLiouvilleSchwarzianLocalMapAffineDerivativeAlgebraMetricWirtingerBoundaryTheorems

/--
Apply the holomorphic-Schwarzian theorem to a conformal factor whose curvature
has already been identified as the constant `K`.
-/
theorem localSchwarzianData_of_hasGaussianCurvature
    (h : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (u : LocalConformalFactor) (K : ℝ) (hK : u.HasGaussianCurvature K) :
    Nonempty (LocalSchwarzianData u) :=
  h u K (u.solvesConstantCurvatureEquation_of_hasGaussianCurvature K hK)

/--
Apply the holomorphic-Schwarzian theorem to a hyperbolic local curvature
formula.
-/
theorem localSchwarzianData_of_hasGaussianCurvatureMinusOne
    (h : ConstantCurvatureProducesHolomorphicSchwarzianTheorem)
    (u : LocalConformalFactor) (hK : u.HasGaussianCurvatureMinusOne) :
    Nonempty (LocalSchwarzianData u) :=
  localSchwarzianData_of_hasGaussianCurvature h u (-1)
    ((u.hasGaussianCurvatureMinusOne_iff_hasGaussianCurvature_neg_one).mp hK)

end

end JJMath
