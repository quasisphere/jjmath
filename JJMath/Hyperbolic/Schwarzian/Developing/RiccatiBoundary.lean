import JJMath.Hyperbolic.Schwarzian.Developing.LiouvilleUniqueness

/-!
# Split Schwarzian developing-map constructions
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace LocalHyperbolicCanonicalPullbackLiouvilleFormulaData

/--
%%handwave
name:
  Liouville–Schwarzian uniqueness recovers the metric
statement:
  Let \(u:V→ℝ\) satisfy \(Δu=e^{2u}\), and let \(F:V→ℍ\) have the normalized hyperbolic two-jet at \(z₀\) and Schwarzian derivative \(\{F,z\}=2(u_{zz}-u_z²)\). If the canonical Poincaré pullback identities hold for \(F\), then \(e^{2u(z)}=|F'(z)|²/(\operatorname{Im} F(z))²\) throughout the normalization domain.
proof:
  Put \(v=\log |F'|-\log \operatorname{Im} F\) and \(φ=u-v\). Equality of metric Schwarzians turns \((φ,φ_z)\) into a closed linear first-order system with a continuous exponential divided-difference coefficient. The normalized two-jet gives \(φ(z₀)=φ_z(z₀)=0\); uniqueness along affine segments gives \(φ=0\), and exponentiation yields the formula.
-/
theorem densitySq_eq_original_of_originalMetricSchwarzian
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N)
    (hu : u.SolvesLiouvilleEquation)
    (hOriginal : LocalOriginalMetricSchwarzianIdentification S) :
    ∀ z, z ∈ N.domain →
      u.densitySq z = N.pullbackDensitySq z := by
  intro z hz
  let C : LocalHyperbolicPullbackLiouvilleCandidate N :=
    LocalHyperbolicPullbackLiouvilleCandidate.ofFormulaData P.toFormulaData
  let data : LocalLiouvilleSchwarzianUniquenessData N C :=
    LocalLiouvilleSchwarzianUniquenessData.ofCandidate C hu
      (hyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem_of_ballDomain
        hyperbolicTwoJetNormalizationHasBallDomainTheorem S N)
  let A : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData data :=
    localLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData_of_canonicalPullbackFormula
      P data hOriginal
  let F : LocalLiouvilleSchwarzianFirstOrderSystemData data :=
    localLiouvilleSchwarzianFirstOrderSystemData_of_wirtingerRiccati A
  let Escalar : LocalLiouvilleSchwarzianScalarDifferenceData data :=
    localLiouvilleSchwarzianScalarDifferenceData_of_firstOrderSystem F
  let Elinear : LocalLiouvilleSchwarzianLinearizedScalarDifferenceData data :=
    localLiouvilleSchwarzianLinearizedScalarDifferenceData_of_scalarDifference Escalar
  let Eclosed : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data :=
    localLiouvilleSchwarzianClosedFirstOrderLinearSystemData_of_linearizedScalarDifference
      Elinear
  have hpotentialClosed :
      ContinuousOn Eclosed.linearized.potential N.domain := by
    simpa [Eclosed, Elinear,
      localLiouvilleSchwarzianClosedFirstOrderLinearSystemData_of_linearizedScalarDifference,
      localLiouvilleSchwarzianLinearizedScalarDifferenceData_of_scalarDifference]
      using
        Escalar.linearizedPotential_continuousOn_of_realExpTwoDividedDifferenceContinuous
          realExpTwoDividedDifference_continuous
  let Ppotential :
      LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPotentialPathData
        Eclosed z :=
    { potential_continuousOn := hpotentialClosed }
  have hLog :
      u.logDensity z = C.conformalFactor.logDensity z :=
    ((Ppotential.toAffineSegmentDifferentialPathData hz).toAffineSegmentAnalyticPathData
      hz).logDensity_eq hz
  exact C.pullback_eq_densitySq_of_eq_original hz
    (C.densitySq_eq_of_logDensity_eq hLog)

end LocalHyperbolicCanonicalPullbackLiouvilleFormulaData

namespace LocalHyperbolicCanonicalPullbackDerivativeAlgebraData

/--
%%handwave
name:
  Metric recovery from pullback derivative algebra
statement:
  Derivative algebra for a normalized branch gives metric recovery as soon as the branch Schwarzian coefficient is the original metric Schwarzian of the Liouville factor. For every \(z\in\Omega\), the original squared density equals the canonical Poincaré pullback squared density.
proof:
  Convert the derivative identities to affine derivative identities, derive the Poincaré Laplacian formula, and apply the canonical pullback calculation.
-/
theorem densitySq_eq_original_of_originalMetricSchwarzian
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (A : LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N)
    (hu : u.SolvesLiouvilleEquation)
    (hOriginal : LocalOriginalMetricSchwarzianIdentification S) :
    ∀ z, z ∈ N.domain →
      u.densitySq z = N.pullbackDensitySq z := by
  intro z hz
  let B : LocalHyperbolicCanonicalPullbackAffineDerivativeAlgebraData N :=
    A.toAffineDerivativeAlgebraData
  let C : LocalHyperbolicCanonicalPullbackAffineDerivativeData N :=
    B.withLaplacian B.toCoreData.laplacian_eq_pullbackDensitySq
  let P : LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N :=
    C.toDerivIdentifiedData.toFormulaData
  exact P.densitySq_eq_original_of_originalMetricSchwarzian hu hOriginal z hz

/--
%%handwave
name:
  The explicit Poincaré pullback metric formula
statement:
  Derivative algebra for a normalized branch gives the concrete Poincaré metric recovery formula under the original metric-Schwarzian identification. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Use equality with the canonical pullback density and unfold that density as \(|F'|^2/(\operatorname{Im}F)^2\).
-/
theorem metric_recovery_of_originalMetricSchwarzian
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    (A : LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N)
    (hu : u.SolvesLiouvilleEquation)
    (hOriginal : LocalOriginalMetricSchwarzianIdentification S) :
    ∀ z, z ∈ N.domain →
      u.densitySq z =
        Complex.normSq (N.normalized.projective.affineMapDeriv z) /
          ((N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2) := by
  intro z hz
  simpa [LocalHyperbolicTwoJetUpperHalfPlaneNormalization.pullbackDensitySq] using
    A.densitySq_eq_original_of_originalMetricSchwarzian hu hOriginal z hz

end LocalHyperbolicCanonicalPullbackDerivativeAlgebraData

namespace HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems

end HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems

namespace HyperbolicTwoJetRiccatiCalculusBoundaryTheorems

end HyperbolicTwoJetRiccatiCalculusBoundaryTheorems

namespace HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalMetricWirtingerRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalMetricWirtingerRiccatiBoundaryTheorems

namespace HyperbolicTwoJetPullbackFormulaCanonicalRiccatiBoundaryTheorems

end HyperbolicTwoJetPullbackFormulaCanonicalRiccatiBoundaryTheorems

namespace HyperbolicTwoJetPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems

end HyperbolicTwoJetPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackFormulaCanonicalRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalPullbackFormulaCanonicalRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackWirtingerFormulaCanonicalRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalPullbackWirtingerFormulaCanonicalRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackDensityDerivativeCanonicalRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalPullbackDensityDerivativeCanonicalRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackBranchDerivativeCanonicalRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalPullbackBranchDerivativeCanonicalRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackSecondExpressionCanonicalRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalPullbackSecondExpressionCanonicalRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackThirdDerivativeCanonicalRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalPullbackThirdDerivativeCanonicalRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

end HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

end

end JJMath
