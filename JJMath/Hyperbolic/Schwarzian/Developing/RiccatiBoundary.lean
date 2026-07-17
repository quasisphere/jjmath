import JJMath.Hyperbolic.Schwarzian.Developing.LiouvilleUniqueness

/-!
# Split Schwarzian developing-map constructions
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

/--
Reduction from the Liouville-Schwarzian uniqueness data to the Riccati
difference package.

This is the formal home for the calculation
`S(v)-S(u)=0 ⟹ α_z = α(v_z+u_z)`.
-/
def LocalLiouvilleSchwarzianRiccatiReductionTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C),
      Nonempty (LocalLiouvilleSchwarzianRiccatiDifferenceData data)

/--
Concrete calculus version of the Riccati reduction target.

This leaves only the construction of the actual `u_z`, `v_z`, `u_zz`, and
`v_zz` fields, their derivative evidence, and the final first-derivative
uniqueness implication.  The algebraic Riccati equation itself is proved by
`LocalLiouvilleSchwarzianRiccatiReductionCalculusData.toRiccatiDifferenceData`.
-/
def LocalLiouvilleSchwarzianRiccatiReductionCalculusTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C),
      Nonempty (LocalLiouvilleSchwarzianRiccatiReductionCalculusData data)

/--
Canonical Frechet-Wirtinger version of the Riccati reduction target.

Compared with `LocalLiouvilleSchwarzianRiccatiReductionCalculusTheorem`, this
does not merely ask for some first and second derivative fields: it asks for
the canonical fields `u.wirtingerZ`, `u.wirtingerZZ` and their pullback
counterparts.
-/
def LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C),
      Nonempty (LocalLiouvilleSchwarzianCanonicalRiccatiCalculusData data)

/--
Metric-scaled canonical Frechet-Wirtinger version of the Riccati reduction
target.

This is the same target as
`LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem`, except that the
Schwarzian equality is stated for the actual projective-connection coefficient
`2 * (u_zz - u_z^2)`.  Lean cancels the factor `2` before applying the
Riccati algebra.
-/
def LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C),
      Nonempty (LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusData data)

/--
Corrected canonical Wirtinger-Riccati reduction target.

This records the local Frechet-Wirtinger equation obtained from equal metric
Schwarzians without asking the first Wirtinger fields to be holomorphic.
-/
def LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C),
      Nonempty (LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData data)

/--
The honest first-order Liouville-Schwarzian system target.

This strengthens the corrected Wirtinger-Riccati target by adding the
Liouville-side `∂bar α` equation and the base data for
`φ = v - u` and `α = v_z - u_z`.
-/
def LocalLiouvilleSchwarzianFirstOrderSystemTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C),
      Nonempty (LocalLiouvilleSchwarzianFirstOrderSystemData data)

/--
Scalar difference formulation of the genuine local uniqueness boundary.
-/
def LocalLiouvilleSchwarzianScalarDifferenceTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C),
      Nonempty (LocalLiouvilleSchwarzianScalarDifferenceData data)

/--
Continuity target for the explicit scalar Liouville linearized potential.

Unlike the closed first-order potential-continuity theorem, this is stated for
the concrete divided-difference coefficient produced from the scalar
difference equation.
-/
def LocalLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (E : LocalLiouvilleSchwarzianScalarDifferenceData data),
      ContinuousOn E.linearizedPotential N.domain

/--
Linearized scalar difference formulation of the genuine local uniqueness
boundary.
-/
def LocalLiouvilleSchwarzianLinearizedScalarDifferenceTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C),
      Nonempty (LocalLiouvilleSchwarzianLinearizedScalarDifferenceData data)

/--
Linear elliptic Cauchy-data formulation of the genuine local uniqueness
boundary.
-/
def LocalLiouvilleSchwarzianLinearEllipticCauchyTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C),
      Nonempty (LocalLiouvilleSchwarzianLinearEllipticCauchyData data)

/--
Closed first-order linear system formulation of the genuine local uniqueness
boundary.
-/
def LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C),
      Nonempty (LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data)

/--
Zero-uniqueness target for the corrected Wirtinger-Riccati system.

The equation supplied by
`LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData` is
`∂z α = α β`, where `α = v_z - u_z`.  The normalized two-jet data gives
`α z₀ = 0`.  This theorem target is the remaining analytic uniqueness
principle needed to conclude `α = 0` on the normalized local domain.
-/
def LocalWirtingerRiccatiZeroUniquenessTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (_A : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiData data),
      ∀ z, z ∈ N.domain →
        C.conformalFactor.wirtingerZ z - u.wirtingerZ z = 0

/--
Uniqueness target for the genuine first-order Liouville-Schwarzian system.

This is the mathematically honest remaining local uniqueness theorem: it sees
both the `∂z α` Riccati equation and the `∂bar α` Liouville equation.
-/
def LocalLiouvilleSchwarzianFirstOrderSystemUniquenessTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (_F : LocalLiouvilleSchwarzianFirstOrderSystemData data),
      ∀ z, z ∈ N.domain →
        u.logDensity z = C.conformalFactor.logDensity z

/--
Uniqueness target for the scalar elliptic difference formulation.
-/
def LocalLiouvilleSchwarzianScalarDifferenceUniquenessTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (_E : LocalLiouvilleSchwarzianScalarDifferenceData data),
      ∀ z, z ∈ N.domain →
        u.logDensity z = C.conformalFactor.logDensity z

/--
Uniqueness target for the linearized scalar elliptic difference formulation.
-/
def LocalLiouvilleSchwarzianLinearizedScalarDifferenceUniquenessTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (_E : LocalLiouvilleSchwarzianLinearizedScalarDifferenceData data),
      ∀ z, z ∈ N.domain →
        u.logDensity z = C.conformalFactor.logDensity z

/--
Uniqueness target for the standard linear elliptic Cauchy-data formulation.
-/
def LocalLiouvilleSchwarzianLinearEllipticCauchyUniquenessTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (_E : LocalLiouvilleSchwarzianLinearEllipticCauchyData data),
      ∀ z, z ∈ N.domain →
        u.logDensity z = C.conformalFactor.logDensity z

/--
Uniqueness target for the closed first-order linear system formulation.
-/
def LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C)
    (_E : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemData data),
      ∀ z, z ∈ N.domain →
        u.logDensity z = C.conformalFactor.logDensity z

/--
Path certificates plus Grönwall uniqueness imply the closed first-order
linear-system uniqueness theorem.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_pathData
    (hPath : LocalLiouvilleSchwarzianClosedFirstOrderPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem := by
  intro u S D z₀ N C data E z hz
  rcases hPath S N C data E z hz with ⟨P⟩
  exact P.logDensity_eq

/--
Operator-bound path certificates imply the closed first-order linear-system
uniqueness theorem.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_operatorBoundPathData
    (hPath : LocalLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_pathData
    (localLiouvilleSchwarzianClosedFirstOrderPathDataTheorem_of_operatorBoundPathData hPath)

/--
Bounded-coefficient path certificates imply the closed first-order
linear-system uniqueness theorem.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_coefficientBoundPathData
    (hPath : LocalLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_operatorBoundPathData
    (localLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathDataTheorem_of_coefficientBoundPathData
      hPath)

/--
Compact-continuous coefficient path certificates imply the closed first-order
linear-system uniqueness theorem.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_continuousCoefficientPathData
    (hPath :
      LocalLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_coefficientBoundPathData
    (localLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathDataTheorem_of_continuousCoefficientPathData
      hPath)

/--
Straight-segment path certificates imply the closed first-order linear-system
uniqueness theorem.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentPathData
    (hPath :
      LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_continuousCoefficientPathData
    (localLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathDataTheorem_of_affineSegmentPathData
      hPath)

/--
Analytic-core straight-segment path certificates imply the closed first-order
linear-system uniqueness theorem.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentAnalyticPathData
    (hPath :
      LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentPathData
    (localLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathDataTheorem_of_analyticPathData
      hPath)

/--
Differential-core straight-segment path certificates imply the closed
first-order linear-system uniqueness theorem.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentDifferentialPathData
    (hPath :
      LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentDifferentialPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentAnalyticPathData
    (localLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathDataTheorem_of_differentialPathData
      hPath)

/--
Potential-core straight-segment path certificates imply the closed first-order
linear-system uniqueness theorem.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentPotentialPathData
    (hPath :
      LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPotentialPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentDifferentialPathData
    (localLiouvilleSchwarzianClosedFirstOrderAffineSegmentDifferentialPathDataTheorem_of_potentialPathData
      hPath)

/--
Continuity of the scalar linearized potential implies the closed first-order
linear-system uniqueness theorem.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_potentialContinuity
    (hPotential :
      LocalLiouvilleSchwarzianClosedFirstOrderPotentialContinuityTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentPotentialPathData
    (localLiouvilleSchwarzianClosedFirstOrderAffineSegmentPotentialPathDataTheorem_of_potentialContinuity
      hPotential)

/--
Strengthened corrected Riccati target: the Frechet-Wirtinger equation is
supplemented by the Cauchy-Riemann/analytic data needed to reduce it to the
scalar holomorphic Riccati package.
-/
def LocalLiouvilleSchwarzianCanonicalMetricHolomorphicRiccatiTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N)
    (data : LocalLiouvilleSchwarzianUniquenessData N C),
      Nonempty (LocalLiouvilleSchwarzianCanonicalMetricHolomorphicRiccatiData data)

/--
The older metric-scaled complex-derivative target implies the corrected
Wirtinger-Riccati target by forgetting holomorphic derivative evidence to real
differentiability.
-/
theorem localLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem_of_metric
    (hMetric : LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusTheorem) :
    LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem := by
  intro u S D z₀ N C data
  rcases hMetric S N C data with ⟨A⟩
  exact ⟨A.toCanonicalMetricWirtingerRiccatiData⟩

/--
The corrected Wirtinger-Riccati reduction automatically gives the genuine
first-order system, because the missing `∂bar α` equation follows from the two
Liouville equations in the uniqueness data.
-/
theorem localLiouvilleSchwarzianFirstOrderSystemTheorem_of_wirtingerRiccati
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    LocalLiouvilleSchwarzianFirstOrderSystemTheorem := by
  intro u S D z₀ N C data
  rcases hWirtinger S N C data with ⟨A⟩
  exact ⟨localLiouvilleSchwarzianFirstOrderSystemData_of_wirtingerRiccati A⟩

/--
The genuine first-order system gives the scalar elliptic difference
formulation.
-/
theorem localLiouvilleSchwarzianScalarDifferenceTheorem_of_firstOrderSystem
    (hSystem : LocalLiouvilleSchwarzianFirstOrderSystemTheorem) :
    LocalLiouvilleSchwarzianScalarDifferenceTheorem := by
  intro u S D z₀ N C data
  rcases hSystem S N C data with ⟨F⟩
  exact ⟨localLiouvilleSchwarzianScalarDifferenceData_of_firstOrderSystem F⟩

/--
The corrected Wirtinger-Riccati reduction gives the scalar elliptic difference
formulation.
-/
theorem localLiouvilleSchwarzianScalarDifferenceTheorem_of_wirtingerRiccati
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    LocalLiouvilleSchwarzianScalarDifferenceTheorem :=
  localLiouvilleSchwarzianScalarDifferenceTheorem_of_firstOrderSystem
    (localLiouvilleSchwarzianFirstOrderSystemTheorem_of_wirtingerRiccati hWirtinger)

/--
The pure real continuity of the divided difference of `x ↦ exp (2x)` supplies
continuity of the explicit scalar Liouville linearized potential.
-/
theorem localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_of_realExpTwoDividedDifference
    (hdiv : RealExpTwoDividedDifferenceContinuityTheorem) :
    LocalLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem := by
  intro u S D z₀ N C data E
  exact E.linearizedPotential_continuousOn_of_realExpTwoDividedDifferenceContinuous hdiv

/--
The explicit scalar Liouville linearized potential is continuous on the
normalized domain.
-/
theorem localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_real :
    LocalLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem :=
  localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_of_realExpTwoDividedDifference
    realExpTwoDividedDifference_continuous

/--
The scalar elliptic difference formulation gives the linearized scalar
difference formulation.
-/
theorem localLiouvilleSchwarzianLinearizedScalarDifferenceTheorem_of_scalarDifference
    (hScalar : LocalLiouvilleSchwarzianScalarDifferenceTheorem) :
    LocalLiouvilleSchwarzianLinearizedScalarDifferenceTheorem := by
  intro u S D z₀ N C data
  rcases hScalar S N C data with ⟨E⟩
  exact ⟨localLiouvilleSchwarzianLinearizedScalarDifferenceData_of_scalarDifference E⟩

/--
The corrected Wirtinger-Riccati reduction gives the linearized scalar elliptic
difference formulation.
-/
theorem localLiouvilleSchwarzianLinearizedScalarDifferenceTheorem_of_wirtingerRiccati
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    LocalLiouvilleSchwarzianLinearizedScalarDifferenceTheorem :=
  localLiouvilleSchwarzianLinearizedScalarDifferenceTheorem_of_scalarDifference
    (localLiouvilleSchwarzianScalarDifferenceTheorem_of_wirtingerRiccati hWirtinger)

/--
The linearized scalar elliptic formulation gives the standard linear elliptic
Cauchy-data formulation.
-/
theorem localLiouvilleSchwarzianLinearEllipticCauchyTheorem_of_linearizedScalarDifference
    (hLinear : LocalLiouvilleSchwarzianLinearizedScalarDifferenceTheorem) :
    LocalLiouvilleSchwarzianLinearEllipticCauchyTheorem := by
  intro u S D z₀ N C data
  rcases hLinear S N C data with ⟨E⟩
  exact ⟨localLiouvilleSchwarzianLinearEllipticCauchyData_of_linearizedScalarDifference E⟩

/--
The corrected Wirtinger-Riccati reduction gives the standard linear elliptic
Cauchy-data formulation.
-/
theorem localLiouvilleSchwarzianLinearEllipticCauchyTheorem_of_wirtingerRiccati
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    LocalLiouvilleSchwarzianLinearEllipticCauchyTheorem :=
  localLiouvilleSchwarzianLinearEllipticCauchyTheorem_of_linearizedScalarDifference
    (localLiouvilleSchwarzianLinearizedScalarDifferenceTheorem_of_wirtingerRiccati
      hWirtinger)

/--
The linearized scalar elliptic formulation gives the closed first-order linear
system formulation.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem_of_linearizedScalarDifference
    (hLinear : LocalLiouvilleSchwarzianLinearizedScalarDifferenceTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem := by
  intro u S D z₀ N C data
  rcases hLinear S N C data with ⟨E⟩
  exact
    ⟨localLiouvilleSchwarzianClosedFirstOrderLinearSystemData_of_linearizedScalarDifference
      E⟩

/--
The corrected Wirtinger-Riccati reduction gives the closed first-order linear
system formulation.
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem_of_wirtingerRiccati
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem_of_linearizedScalarDifference
    (localLiouvilleSchwarzianLinearizedScalarDifferenceTheorem_of_wirtingerRiccati
      hWirtinger)

/--
The strengthened holomorphic Wirtinger-Riccati package gives the ordinary
Riccati reduction package.
-/
theorem localLiouvilleSchwarzianRiccatiReductionTheorem_of_canonicalMetricHolomorphicRiccati
    (hHolomorphic : LocalLiouvilleSchwarzianCanonicalMetricHolomorphicRiccatiTheorem) :
    LocalLiouvilleSchwarzianRiccatiReductionTheorem := by
  intro u S D z₀ N C data
  rcases hHolomorphic S N C data with ⟨A⟩
  exact ⟨A.toRiccatiDifferenceData⟩

/--
Metric-scaled canonical Frechet-Wirtinger data imply the unscaled canonical
Riccati target.
-/
theorem localLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem_of_metric
    (hMetric : LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusTheorem) :
    LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem := by
  intro u S D z₀ N C data
  rcases hMetric S N C data with ⟨A⟩
  exact ⟨A.toCanonicalRiccatiCalculusData⟩

/--
The canonical Frechet-Wirtinger target implies the concrete calculus target.
-/
theorem localLiouvilleSchwarzianRiccatiReductionCalculusTheorem_of_canonical
    (hCanonical : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem) :
    LocalLiouvilleSchwarzianRiccatiReductionCalculusTheorem := by
  intro u S D z₀ N C data
  rcases hCanonical S N C data with ⟨A⟩
  exact ⟨A.toCalculusData⟩

/--
The concrete Riccati calculus target implies the Riccati reduction theorem.
-/
theorem localLiouvilleSchwarzianRiccatiReductionTheorem_of_calculus
    (hCalc : LocalLiouvilleSchwarzianRiccatiReductionCalculusTheorem) :
    LocalLiouvilleSchwarzianRiccatiReductionTheorem := by
  intro u S D z₀ N C data
  rcases hCalc S N C data with ⟨A⟩
  exact ⟨A.toRiccatiDifferenceData⟩

/--
The canonical Frechet-Wirtinger target implies the Riccati reduction theorem.
-/
theorem localLiouvilleSchwarzianRiccatiReductionTheorem_of_canonical
    (hCanonical : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem) :
    LocalLiouvilleSchwarzianRiccatiReductionTheorem :=
  localLiouvilleSchwarzianRiccatiReductionTheorem_of_calculus
    (localLiouvilleSchwarzianRiccatiReductionCalculusTheorem_of_canonical
      hCanonical)

/--
Metric-scaled canonical Frechet-Wirtinger data imply the Riccati reduction
target.
-/
theorem localLiouvilleSchwarzianRiccatiReductionTheorem_of_canonicalMetric
    (hMetric : LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusTheorem) :
    LocalLiouvilleSchwarzianRiccatiReductionTheorem :=
  localLiouvilleSchwarzianRiccatiReductionTheorem_of_canonical
    (localLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem_of_metric
      hMetric)

/--
Existence of an integrating factor for the Riccati difference equation.

This is the remaining scalar first-order ODE step after reducing
Liouville-Schwarzian uniqueness to `α_z = α * coefficient`.
-/
def LocalRiccatiIntegratingFactorTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (R : LocalLiouvilleSchwarzianRiccatiDifferenceData data),
      Nonempty (R.IntegratingFactorData)

/--
Local primitive existence for the Riccati coefficient.

For the intended domains, this should follow after shrinking to a simply
connected ball and using holomorphicity/continuity of the coefficient.
-/
def LocalRiccatiPrimitiveExistenceTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (R : LocalLiouvilleSchwarzianRiccatiDifferenceData data),
      Nonempty (R.PrimitiveData)

/--
Exactness of the Riccati coefficient on the normalized domain.

This is the standard complex-analysis primitive target: `R.coefficient` is the
complex derivative of some function on `N.domain`.
-/
def LocalRiccatiCoefficientExactnessTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (R : LocalLiouvilleSchwarzianRiccatiDifferenceData data),
      Complex.IsExactOn R.coefficient N.domain

/--
If the Riccati coefficient is exact on the normalized domain, then it supplies
the primitive data used by the integrating-factor argument.
-/
theorem localRiccatiPrimitiveExistenceTheorem_of_exactness
    (hExact : LocalRiccatiCoefficientExactnessTheorem) :
    LocalRiccatiPrimitiveExistenceTheorem := by
  intro u S D z₀ N C data R
  rcases hExact R with ⟨A, hA⟩
  exact ⟨{
    primitiveFun := A
    has_deriv_at_eq_coefficient_on_domain := hA
  }⟩

/--
The local disk version of primitive existence for the Riccati coefficient.

This is the form supplied directly by mathlib: a holomorphic function on a
complex disk has a primitive there.
-/
def LocalRiccatiCoefficientBallHolomorphicTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (R : LocalLiouvilleSchwarzianRiccatiDifferenceData data),
      ∃ c r, N.domain = Metric.ball c r ∧
        DifferentiableOn ℂ R.coefficient (Metric.ball c r)

/--
Analytic disk-local form of the Riccati coefficient input.

This is closer to the natural output of the Schwarzian/Liouville calculations:
the Riccati coefficient is analytic on a neighborhood of the chosen ball.
-/
def LocalRiccatiCoefficientBallAnalyticTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (R : LocalLiouvilleSchwarzianRiccatiDifferenceData data),
      ∃ c r, N.domain = Metric.ball c r ∧
        AnalyticOnNhd ℂ R.coefficient (Metric.ball c r)

/--
Domain-level analytic form of the Riccati coefficient input.

This is the natural output expected from the Riccati reduction: the coefficient
is analytic on the chosen normalized domain, whatever concrete shape that
domain has.
-/
def LocalRiccatiCoefficientAnalyticTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (R : LocalLiouvilleSchwarzianRiccatiDifferenceData data),
      AnalyticOnNhd ℂ R.coefficient N.domain

/--
The domain-level Riccati coefficient analyticity theorem is now part of the
Riccati difference package produced by the reduction step.
-/
theorem localRiccatiCoefficientAnalyticTheorem :
    LocalRiccatiCoefficientAnalyticTheorem := by
  intro u S D z₀ N C data R
  exact R.coefficient_analytic_on_domain

/--
Domain-level analyticity plus a ball-shaped normalized domain gives the
disk-local analytic input.  The proof uses mathlib's `AnalyticOnNhd.mono`;
the equality case is intentionally just a rewrite.
-/
theorem localRiccatiCoefficientBallAnalyticTheorem_of_analytic_and_ballDomain
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem)
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem) :
    LocalRiccatiCoefficientBallAnalyticTheorem := by
  intro u S D z₀ N C data R
  rcases hBallDomain S N with ⟨c, r, hdomain⟩
  exact ⟨c, r, hdomain, by
    rw [← hdomain]
    exact hAnalytic R⟩

/--
Domain-level analyticity gives the disk-local analytic input using the ball
domain packaged in each two-jet normalization.
-/
theorem localRiccatiCoefficientBallAnalyticTheorem_of_analytic
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalRiccatiCoefficientBallAnalyticTheorem :=
  localRiccatiCoefficientBallAnalyticTheorem_of_analytic_and_ballDomain
    hAnalytic hyperbolicTwoJetNormalizationHasBallDomainTheorem

/--
If a coefficient is analytic on a larger set containing the normalized domain,
then it is analytic on the normalized domain by mathlib monotonicity.
-/
theorem localRiccatiCoefficientAnalytic_of_analyticOn_superset
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (R : LocalLiouvilleSchwarzianRiccatiDifferenceData data)
    {U : Set ℂ} (hAnalytic : AnalyticOnNhd ℂ R.coefficient U)
    (hSub : N.domain ⊆ U) :
    AnalyticOnNhd ℂ R.coefficient N.domain :=
  hAnalytic.mono hSub

/--
Analyticity on a neighborhood of a ball gives holomorphicity on that ball by
mathlib.
-/
theorem localRiccatiCoefficientBallHolomorphicTheorem_of_ballAnalytic
    (hAnalytic : LocalRiccatiCoefficientBallAnalyticTheorem) :
    LocalRiccatiCoefficientBallHolomorphicTheorem := by
  intro u S D z₀ N C data R
  rcases hAnalytic R with ⟨c, r, hdomain, hanalytic⟩
  exact ⟨c, r, hdomain, hanalytic.differentiableOn⟩

/--
Domain-level analyticity plus ball-shaped normalized domains gives the
disk-local holomorphic input needed by mathlib's primitive theorem.
-/
theorem localRiccatiCoefficientBallHolomorphicTheorem_of_analytic_and_ballDomain
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem)
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem) :
    LocalRiccatiCoefficientBallHolomorphicTheorem :=
  localRiccatiCoefficientBallHolomorphicTheorem_of_ballAnalytic
    (localRiccatiCoefficientBallAnalyticTheorem_of_analytic_and_ballDomain
      hAnalytic hBallDomain)

/-- Domain-level analyticity gives disk-local holomorphicity on the packaged ball domain. -/
theorem localRiccatiCoefficientBallHolomorphicTheorem_of_analytic
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalRiccatiCoefficientBallHolomorphicTheorem :=
  localRiccatiCoefficientBallHolomorphicTheorem_of_analytic_and_ballDomain
    hAnalytic hyperbolicTwoJetNormalizationHasBallDomainTheorem

/--
Holomorphicity of the Riccati coefficient on a disk gives exactness by
mathlib's primitive theorem for disks.
-/
theorem localRiccatiCoefficientExactnessTheorem_of_ballHolomorphic
    (hBall : LocalRiccatiCoefficientBallHolomorphicTheorem) :
    LocalRiccatiCoefficientExactnessTheorem := by
  intro u S D z₀ N C data R
  rcases hBall R with ⟨c, r, hdomain, hdiff⟩
  rw [hdomain]
  exact hdiff.isExactOn_ball

/--
Domain-level analyticity plus ball-shaped normalized domains gives exactness of
the Riccati coefficient, using mathlib's primitive theorem for disks.
-/
theorem localRiccatiCoefficientExactnessTheorem_of_analytic_and_ballDomain
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem)
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem) :
    LocalRiccatiCoefficientExactnessTheorem :=
  localRiccatiCoefficientExactnessTheorem_of_ballHolomorphic
    (localRiccatiCoefficientBallHolomorphicTheorem_of_analytic_and_ballDomain
      hAnalytic hBallDomain)

/-- Domain-level analyticity gives exactness on the packaged ball domain. -/
theorem localRiccatiCoefficientExactnessTheorem_of_analytic
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalRiccatiCoefficientExactnessTheorem :=
  localRiccatiCoefficientExactnessTheorem_of_analytic_and_ballDomain
    hAnalytic hyperbolicTwoJetNormalizationHasBallDomainTheorem

/--
The disk holomorphic primitive theorem gives the local Riccati primitive
existence theorem.
-/
theorem localRiccatiPrimitiveExistenceTheorem_of_ballHolomorphic
    (hBall : LocalRiccatiCoefficientBallHolomorphicTheorem) :
    LocalRiccatiPrimitiveExistenceTheorem :=
  localRiccatiPrimitiveExistenceTheorem_of_exactness
    (localRiccatiCoefficientExactnessTheorem_of_ballHolomorphic hBall)

/-- Analyticity on a ball gives the local Riccati primitive existence theorem. -/
theorem localRiccatiPrimitiveExistenceTheorem_of_ballAnalytic
    (hAnalytic : LocalRiccatiCoefficientBallAnalyticTheorem) :
    LocalRiccatiPrimitiveExistenceTheorem :=
  localRiccatiPrimitiveExistenceTheorem_of_ballHolomorphic
    (localRiccatiCoefficientBallHolomorphicTheorem_of_ballAnalytic hAnalytic)

/--
Domain-level analyticity plus ball-shaped normalized domains gives local
Riccati primitive existence.
-/
theorem localRiccatiPrimitiveExistenceTheorem_of_analytic_and_ballDomain
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem)
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem) :
    LocalRiccatiPrimitiveExistenceTheorem :=
  localRiccatiPrimitiveExistenceTheorem_of_ballAnalytic
    (localRiccatiCoefficientBallAnalyticTheorem_of_analytic_and_ballDomain
      hAnalytic hBallDomain)

/-- Domain-level analyticity gives local Riccati primitive existence. -/
theorem localRiccatiPrimitiveExistenceTheorem_of_analytic
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalRiccatiPrimitiveExistenceTheorem :=
  localRiccatiPrimitiveExistenceTheorem_of_analytic_and_ballDomain
    hAnalytic hyperbolicTwoJetNormalizationHasBallDomainTheorem

/--
Local Riccati primitive existence is now discharged from the analyticity field
carried by the Riccati difference package and the ball-shaped normalized
domain packaged by the two-jet normalization.
-/
theorem localRiccatiPrimitiveExistenceTheorem :
    LocalRiccatiPrimitiveExistenceTheorem :=
  localRiccatiPrimitiveExistenceTheorem_of_analytic
    localRiccatiCoefficientAnalyticTheorem

/--
The product-rule calculation for the primitive integrating factor.

Given the Riccati equation `α_z = α * coefficient` and a primitive
`A_z = coefficient`, this target proves directly that the derivative of
`α * exp(-A)` is zero on the local domain.
-/
def LocalRiccatiPrimitiveProductDerivativeZeroTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {R : LocalLiouvilleSchwarzianRiccatiDifferenceData data}
    (P : R.PrimitiveData),
      Nonempty (P.ProductDerivativeZeroData)

/--
The product-derivative-zero target follows from the derivative evidence carried
by the Riccati package and the primitive package.
-/
theorem localRiccatiPrimitiveProductDerivativeZeroTheorem :
    LocalRiccatiPrimitiveProductDerivativeZeroTheorem := by
  intro u S D z₀ N C data R P
  exact ⟨P.productDerivativeZeroData⟩

/--
The product-constancy calculation for the primitive integrating factor.

Given `A_z = coefficient`, this is the product-rule calculation
`(α exp(-A))_z = 0`, followed by constancy on the preconnected local domain.
-/
def LocalRiccatiPrimitiveProductConstancyTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    {R : LocalLiouvilleSchwarzianRiccatiDifferenceData data}
    (P : R.PrimitiveData),
      IsPreconnected N.domain →
        ∀ z, z ∈ N.domain →
          R.alpha z * P.integratingFactor z =
            R.alpha z₀ * P.integratingFactor z₀

/--
The product-derivative-zero calculation plus the mean-value theorem gives
primitive product constancy.
-/
theorem localRiccatiPrimitiveProductConstancyTheorem_of_productDerivativeZero
    (hDerivZero : LocalRiccatiPrimitiveProductDerivativeZeroTheorem) :
    LocalRiccatiPrimitiveProductConstancyTheorem := by
  intro u S D z₀ N C data R P _hPreconnected z hz
  rcases hDerivZero P with ⟨Z⟩
  exact
    LocalLiouvilleSchwarzianRiccatiDifferenceData.PrimitiveData.product_constant_on_domain_of_deriv_eq_zero
      Z z hz

/--
Primitive existence plus the product-constancy calculation gives an integrating
factor.
-/
theorem localRiccatiIntegratingFactorTheorem_of_primitive
    (hPrim : LocalRiccatiPrimitiveExistenceTheorem)
    (hConst : LocalRiccatiPrimitiveProductConstancyTheorem) :
    LocalRiccatiIntegratingFactorTheorem := by
  intro u S D z₀ N C data R
  rcases hPrim R with ⟨P⟩
  exact ⟨P.toIntegratingFactorData (hConst P data.domain_preconnected)⟩

/--
Primitive existence plus the product-derivative-zero calculation gives an
integrating factor.
-/
theorem localRiccatiIntegratingFactorTheorem_of_primitive_derivativeZero
    (hPrim : LocalRiccatiPrimitiveExistenceTheorem)
    (hDerivZero : LocalRiccatiPrimitiveProductDerivativeZeroTheorem) :
    LocalRiccatiIntegratingFactorTheorem :=
  localRiccatiIntegratingFactorTheorem_of_primitive hPrim
    (localRiccatiPrimitiveProductConstancyTheorem_of_productDerivativeZero hDerivZero)

/--
Primitive existence alone now gives an integrating factor: the product-rule
calculation is proved from the derivative fields in the Riccati and primitive
packages.
-/
theorem localRiccatiIntegratingFactorTheorem_of_primitiveExistence
    (hPrim : LocalRiccatiPrimitiveExistenceTheorem) :
    LocalRiccatiIntegratingFactorTheorem :=
  localRiccatiIntegratingFactorTheorem_of_primitive_derivativeZero hPrim
    localRiccatiPrimitiveProductDerivativeZeroTheorem

/--
Disk-local holomorphicity of the Riccati coefficient gives an integrating
factor.
-/
theorem localRiccatiIntegratingFactorTheorem_of_ballHolomorphic
    (hBall : LocalRiccatiCoefficientBallHolomorphicTheorem) :
    LocalRiccatiIntegratingFactorTheorem :=
  localRiccatiIntegratingFactorTheorem_of_primitiveExistence
    (localRiccatiPrimitiveExistenceTheorem_of_ballHolomorphic hBall)

/-- Disk-local analyticity of the Riccati coefficient gives an integrating factor. -/
theorem localRiccatiIntegratingFactorTheorem_of_ballAnalytic
    (hAnalytic : LocalRiccatiCoefficientBallAnalyticTheorem) :
    LocalRiccatiIntegratingFactorTheorem :=
  localRiccatiIntegratingFactorTheorem_of_ballHolomorphic
    (localRiccatiCoefficientBallHolomorphicTheorem_of_ballAnalytic hAnalytic)

/--
Domain-level analyticity plus ball-shaped normalized domains gives an
integrating factor.
-/
theorem localRiccatiIntegratingFactorTheorem_of_analytic_and_ballDomain
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem)
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem) :
    LocalRiccatiIntegratingFactorTheorem :=
  localRiccatiIntegratingFactorTheorem_of_ballAnalytic
    (localRiccatiCoefficientBallAnalyticTheorem_of_analytic_and_ballDomain
      hAnalytic hBallDomain)

/-- Domain-level analyticity gives an integrating factor on the packaged ball domain. -/
theorem localRiccatiIntegratingFactorTheorem_of_analytic
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalRiccatiIntegratingFactorTheorem :=
  localRiccatiIntegratingFactorTheorem_of_analytic_and_ballDomain
    hAnalytic hyperbolicTwoJetNormalizationHasBallDomainTheorem

/--
The scalar Riccati integrating-factor step is now discharged from the analytic
coefficient field in the Riccati package.
-/
theorem localRiccatiIntegratingFactorTheorem :
    LocalRiccatiIntegratingFactorTheorem :=
  localRiccatiIntegratingFactorTheorem_of_primitiveExistence
    localRiccatiPrimitiveExistenceTheorem

/--
Uniqueness for the Riccati difference equation with zero initial value.

On the preconnected local domain, the only solution of
`α_z = α * coefficient` with `α z₀ = 0` is `α = 0`.
-/
def LocalRiccatiZeroUniquenessTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    {N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀}
    {C : LocalHyperbolicPullbackLiouvilleCandidate N}
    {data : LocalLiouvilleSchwarzianUniquenessData N C}
    (R : LocalLiouvilleSchwarzianRiccatiDifferenceData data),
      IsPreconnected N.domain →
        ∀ z, z ∈ N.domain → R.alpha z = 0

/--
An integrating factor gives the zero-solution uniqueness theorem for the
Riccati difference equation.
-/
theorem localRiccatiZeroUniquenessTheorem_of_integratingFactor
    (hIF : LocalRiccatiIntegratingFactorTheorem) :
    LocalRiccatiZeroUniquenessTheorem := by
  intro u S D z₀ N C data R _hPreconnected z hz
  rcases hIF R with ⟨M⟩
  exact M.alpha_eq_zero z hz

/--
Domain-level analyticity of the Riccati coefficient on ball-shaped normalized
domains gives zero-solution uniqueness for the Riccati equation.
-/
theorem localRiccatiZeroUniquenessTheorem_of_analytic_and_ballDomain
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem)
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem) :
    LocalRiccatiZeroUniquenessTheorem :=
  localRiccatiZeroUniquenessTheorem_of_integratingFactor
    (localRiccatiIntegratingFactorTheorem_of_analytic_and_ballDomain
      hAnalytic hBallDomain)

/-- Domain-level analyticity gives zero-solution uniqueness for the Riccati equation. -/
theorem localRiccatiZeroUniquenessTheorem_of_analytic
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalRiccatiZeroUniquenessTheorem :=
  localRiccatiZeroUniquenessTheorem_of_analytic_and_ballDomain
    hAnalytic hyperbolicTwoJetNormalizationHasBallDomainTheorem

/--
Zero-solution uniqueness for the Riccati difference equation is now discharged
from the data carried by the Riccati package.
-/
theorem localRiccatiZeroUniquenessTheorem :
    LocalRiccatiZeroUniquenessTheorem :=
  localRiccatiZeroUniquenessTheorem_of_integratingFactor
    localRiccatiIntegratingFactorTheorem

/--
The strengthened holomorphic package supplies the zero-uniqueness theorem for
the corrected Wirtinger-Riccati statement by reducing it to the scalar
Riccati package.
-/
theorem localWirtingerRiccatiZeroUniquenessTheorem_of_canonicalMetricHolomorphicRiccati
    (hHolomorphic : LocalLiouvilleSchwarzianCanonicalMetricHolomorphicRiccatiTheorem) :
    LocalWirtingerRiccatiZeroUniquenessTheorem := by
  intro u S D z₀ N C data _A z hz
  rcases hHolomorphic S N C data with ⟨A⟩
  exact
    localRiccatiZeroUniquenessTheorem A.toRiccatiDifferenceData
      data.domain_preconnected z hz

/--
The corrected Frechet-Wirtinger Riccati data give zero-uniqueness directly
through the closed first-order path argument and scalar divided-difference
potential continuity.
-/
theorem localWirtingerRiccatiZeroUniquenessTheorem_of_scalarPotentialContinuity
    (hPotential :
      LocalLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem) :
    LocalWirtingerRiccatiZeroUniquenessTheorem := by
  intro u S D z₀ N C data A z hz
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
      using hPotential S N C data Escalar
  let Ppotential :
      LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPotentialPathData
        Eclosed z :=
    { potential_continuousOn := hpotentialClosed }
  exact
    ((Ppotential.toAffineSegmentDifferentialPathData hz).toAffineSegmentAnalyticPathData
      hz).alpha_eq hz

/--
The pure real divided-difference continuity lemma discharges the scalar
potential-continuity input for corrected Wirtinger-Riccati zero-uniqueness.
-/
theorem localWirtingerRiccatiZeroUniquenessTheorem_of_realExpTwoDividedDifference
    (hdiv : RealExpTwoDividedDifferenceContinuityTheorem) :
    LocalWirtingerRiccatiZeroUniquenessTheorem :=
  localWirtingerRiccatiZeroUniquenessTheorem_of_scalarPotentialContinuity
    (localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_of_realExpTwoDividedDifference
      hdiv)

/--
Corrected Frechet-Wirtinger Riccati zero-uniqueness is now proved from the
pathwise closed first-order system and the real divided-difference continuity
lemma.
-/
theorem localWirtingerRiccatiZeroUniquenessTheorem :
    LocalWirtingerRiccatiZeroUniquenessTheorem :=
  localWirtingerRiccatiZeroUniquenessTheorem_of_scalarPotentialContinuity
    localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_real

/--
Local uniqueness for the logarithmic Liouville-Schwarzian Cauchy problem.

This is the sharper analytic uniqueness theorem: it identifies the
logarithmic conformal factors, not merely their squared densities.
-/
def LocalLiouvilleSchwarzianLogUniquenessTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N),
    LocalLiouvilleSchwarzianUniquenessData N C →
      ∀ z, z ∈ N.domain →
        u.logDensity z = C.conformalFactor.logDensity z

/--
The Riccati reduction plus zero-solution uniqueness proves logarithmic
Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_riccati
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hRiccatiUnique : LocalRiccatiZeroUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem := by
  intro u S D z₀ N C data z hz
  rcases hReduce S N C data with ⟨R⟩
  exact R.logDensity_eq_of_alpha_eq_zero
    (fun w hw ↦ hRiccatiUnique R data.domain_preconnected w hw) z hz

/--
The Riccati reduction plus integrating-factor existence proves logarithmic
Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_integratingFactor
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hIF : LocalRiccatiIntegratingFactorTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccati
    hReduce (localRiccatiZeroUniquenessTheorem_of_integratingFactor hIF)

/--
Riccati reduction plus domain-level analytic coefficients on ball-shaped
normalized domains gives logarithmic Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiAnalyticAndBallDomain
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem)
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccati
    hReduce
    (localRiccatiZeroUniquenessTheorem_of_analytic_and_ballDomain
      hAnalytic hBallDomain)

/--
Riccati reduction plus domain-level analytic coefficients gives logarithmic
Liouville-Schwarzian uniqueness; ball domains are supplied by the normalized
branch package.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiAnalytic
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccati
    hReduce (localRiccatiZeroUniquenessTheorem_of_analytic hAnalytic)

/--
Once the Liouville-Schwarzian uniqueness problem has been reduced to the
Riccati difference package, the scalar Riccati uniqueness step is fully
discharged.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiReduction
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccati
    hReduce localRiccatiZeroUniquenessTheorem

/--
Concrete Riccati calculus data give logarithmic Liouville-Schwarzian
uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiCalculus
    (hCalc : LocalLiouvilleSchwarzianRiccatiReductionCalculusTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiReduction
    (localLiouvilleSchwarzianRiccatiReductionTheorem_of_calculus hCalc)

/--
Canonical Frechet-Wirtinger Riccati data give logarithmic
Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_canonicalRiccatiCalculus
    (hCanonical : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiCalculus
    (localLiouvilleSchwarzianRiccatiReductionCalculusTheorem_of_canonical
      hCanonical)

/--
The corrected Wirtinger-Riccati reduction plus its zero-uniqueness theorem
give log-density uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_canonicalMetricWirtingerRiccati
    (hReduce : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hUnique : LocalWirtingerRiccatiZeroUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem := by
  intro u S D z₀ N C data z hz
  rcases hReduce S N C data with ⟨A⟩
  exact
    LocalLiouvilleSchwarzianCanonicalRiccatiCalculusData.logDensity_eq_of_first_derivative_eq
      data
      (hUnique S N C data A) z hz

/--
The strengthened holomorphic Wirtinger-Riccati package gives logarithmic
Liouville-Schwarzian uniqueness through the already-proved scalar Riccati
machinery.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_canonicalMetricHolomorphicRiccati
    (hHolomorphic : LocalLiouvilleSchwarzianCanonicalMetricHolomorphicRiccatiTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiReduction
    (localLiouvilleSchwarzianRiccatiReductionTheorem_of_canonicalMetricHolomorphicRiccati
      hHolomorphic)

/--
The genuine first-order system plus its local uniqueness theorem gives
logarithmic Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_firstOrderSystem
    (hSystem : LocalLiouvilleSchwarzianFirstOrderSystemTheorem)
    (hUnique : LocalLiouvilleSchwarzianFirstOrderSystemUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem := by
  intro u S D z₀ N C data z hz
  rcases hSystem S N C data with ⟨F⟩
  exact hUnique S N C data F z hz

/--
The corrected Wirtinger-Riccati reduction plus the genuine first-order
uniqueness theorem gives logarithmic Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_firstOrderUnique
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hUnique : LocalLiouvilleSchwarzianFirstOrderSystemUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_firstOrderSystem
    (localLiouvilleSchwarzianFirstOrderSystemTheorem_of_wirtingerRiccati hWirtinger)
    hUnique

/--
The scalar elliptic difference formulation plus its local uniqueness theorem
gives logarithmic Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_scalarDifference
    (hScalar : LocalLiouvilleSchwarzianScalarDifferenceTheorem)
    (hUnique : LocalLiouvilleSchwarzianScalarDifferenceUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem := by
  intro u S D z₀ N C data z hz
  rcases hScalar S N C data with ⟨E⟩
  exact hUnique S N C data E z hz

/--
The corrected Wirtinger-Riccati reduction plus scalar-difference uniqueness
gives logarithmic Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_scalarDifferenceUnique
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hUnique : LocalLiouvilleSchwarzianScalarDifferenceUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_scalarDifference
    (localLiouvilleSchwarzianScalarDifferenceTheorem_of_wirtingerRiccati hWirtinger)
    hUnique

/--
The linearized scalar elliptic difference formulation plus its local
uniqueness theorem gives logarithmic Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_linearizedScalarDifference
    (hLinear : LocalLiouvilleSchwarzianLinearizedScalarDifferenceTheorem)
    (hUnique : LocalLiouvilleSchwarzianLinearizedScalarDifferenceUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem := by
  intro u S D z₀ N C data z hz
  rcases hLinear S N C data with ⟨E⟩
  exact hUnique S N C data E z hz

/--
The corrected Wirtinger-Riccati reduction plus linearized scalar-difference
uniqueness gives logarithmic Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_linearizedScalarDifferenceUnique
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hUnique : LocalLiouvilleSchwarzianLinearizedScalarDifferenceUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_linearizedScalarDifference
    (localLiouvilleSchwarzianLinearizedScalarDifferenceTheorem_of_wirtingerRiccati
      hWirtinger)
    hUnique

/--
The standard linear elliptic Cauchy-data formulation plus its local uniqueness
theorem gives logarithmic Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_linearEllipticCauchy
    (hCauchy : LocalLiouvilleSchwarzianLinearEllipticCauchyTheorem)
    (hUnique : LocalLiouvilleSchwarzianLinearEllipticCauchyUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem := by
  intro u S D z₀ N C data z hz
  rcases hCauchy S N C data with ⟨E⟩
  exact hUnique S N C data E z hz

/--
The corrected Wirtinger-Riccati reduction plus standard linear elliptic Cauchy
uniqueness gives logarithmic Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_linearEllipticCauchyUnique
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hUnique : LocalLiouvilleSchwarzianLinearEllipticCauchyUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_linearEllipticCauchy
    (localLiouvilleSchwarzianLinearEllipticCauchyTheorem_of_wirtingerRiccati
      hWirtinger)
    hUnique

/--
The closed first-order linear system formulation plus its pathwise uniqueness
theorem gives logarithmic Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_closedFirstOrderLinearSystem
    (hSystem : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem)
    (hUnique : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem := by
  intro u S D z₀ N C data z hz
  rcases hSystem S N C data with ⟨E⟩
  exact hUnique S N C data E z hz

/--
The corrected Wirtinger-Riccati reduction plus closed first-order linear
system uniqueness gives logarithmic Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_closedFirstOrderLinearSystemUnique
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hUnique : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_closedFirstOrderLinearSystem
    (localLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem_of_wirtingerRiccati
      hWirtinger)
    hUnique

/--
The closed first-order linear system plus continuity of its scalar linearized
potential gives logarithmic Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_closedFirstOrderLinearSystem_potentialContinuity
    (hSystem : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem)
    (hPotential :
      LocalLiouvilleSchwarzianClosedFirstOrderPotentialContinuityTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_closedFirstOrderLinearSystem
    hSystem
    (localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_potentialContinuity
      hPotential)

/--
The corrected Wirtinger-Riccati reduction plus scalar-potential continuity gives
logarithmic Liouville-Schwarzian uniqueness through the closed first-order
linear system.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_potentialContinuity
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hPotential :
      LocalLiouvilleSchwarzianClosedFirstOrderPotentialContinuityTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_closedFirstOrderLinearSystem_potentialContinuity
    (localLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem_of_wirtingerRiccati
      hWirtinger)
    hPotential

/--
The corrected Wirtinger-Riccati reduction plus continuity of the concrete
scalar divided-difference potential gives logarithmic Liouville-Schwarzian
uniqueness.  This avoids asking for potential continuity for arbitrary closed
first-order systems.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_scalarPotentialContinuity
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hPotential :
      LocalLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem := by
  intro u S D z₀ N C data z hz
  rcases (localLiouvilleSchwarzianScalarDifferenceTheorem_of_wirtingerRiccati
    hWirtinger) S N C data with ⟨Escalar⟩
  let Elinear :=
    localLiouvilleSchwarzianLinearizedScalarDifferenceData_of_scalarDifference
      Escalar
  let Eclosed :=
    localLiouvilleSchwarzianClosedFirstOrderLinearSystemData_of_linearizedScalarDifference
      Elinear
  have hpotentialClosed :
      ContinuousOn Eclosed.linearized.potential N.domain := by
    simpa [Eclosed, Elinear,
      localLiouvilleSchwarzianClosedFirstOrderLinearSystemData_of_linearizedScalarDifference,
      localLiouvilleSchwarzianLinearizedScalarDifferenceData_of_scalarDifference]
      using hPotential S N C data Escalar
  let Ppotential :
      LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPotentialPathData
        Eclosed z :=
    { potential_continuousOn := hpotentialClosed }
  exact
    ((Ppotential.toAffineSegmentDifferentialPathData hz).toAffineSegmentAnalyticPathData
      hz).logDensity_eq hz

/--
The corrected Wirtinger-Riccati reduction plus the pure real divided-difference
continuity lemma gives logarithmic Liouville-Schwarzian uniqueness through the
concrete scalar potential.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_realExpTwoDividedDifference
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hdiv : RealExpTwoDividedDifferenceContinuityTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_scalarPotentialContinuity
    hWirtinger
    (localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_of_realExpTwoDividedDifference
      hdiv)

/--
Corrected Wirtinger-Riccati data alone give logarithmic
Liouville-Schwarzian uniqueness via the proved scalar divided-difference
continuity lemma.
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_scalarPotentialContinuity
    hWirtinger
    localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_real

/--
Local uniqueness for the Liouville-Schwarzian system.

On a preconnected local domain, the original Liouville factor `u` agrees with
the Poincare pullback factor determined by a two-jet normalized
upper-half-plane Schwarzian branch, provided the pullback factor has the same
Schwarzian coefficient and the same normalized base data.
-/
def LocalLiouvilleSchwarzianUniquenessTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N),
    u.SolvesLiouvilleEquation → IsPreconnected N.domain →
      ∀ z, z ∈ N.domain →
        u.densitySq z = C.conformalFactor.densitySq z

/--
Logarithmic uniqueness implies the squared-density uniqueness statement used by
the metric-recovery bridge.
-/
theorem localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness
    (hLogUnique : LocalLiouvilleSchwarzianLogUniquenessTheorem) :
    LocalLiouvilleSchwarzianUniquenessTheorem := by
  intro u S D z₀ N C hu hPreconnected z hz
  exact C.densitySq_eq_of_logDensity_eq
    (hLogUnique S N C
      (LocalLiouvilleSchwarzianUniquenessData.ofCandidate C hu hPreconnected)
      z hz)

/--
Riccati reduction plus domain-level analytic coefficients on ball-shaped
normalized domains gives the squared-density Liouville-Schwarzian uniqueness
statement.
-/
theorem localLiouvilleSchwarzianUniquenessTheorem_of_riccatiAnalyticAndBallDomain
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem)
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiAnalyticAndBallDomain
      hReduce hAnalytic hBallDomain)

/--
Riccati reduction plus domain-level analytic coefficients gives
squared-density Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianUniquenessTheorem_of_riccatiAnalytic
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiAnalytic
      hReduce hAnalytic)

/--
Riccati reduction alone gives squared-density Liouville-Schwarzian uniqueness:
the coefficient analyticity, primitive, integrating factor, and zero-solution
steps are all supplied by the Riccati data and mathlib.
-/
theorem localLiouvilleSchwarzianUniquenessTheorem_of_riccatiReduction
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiReduction hReduce)

/--
Concrete Riccati calculus data give squared-density Liouville-Schwarzian
uniqueness.
-/
theorem localLiouvilleSchwarzianUniquenessTheorem_of_riccatiCalculus
    (hCalc : LocalLiouvilleSchwarzianRiccatiReductionCalculusTheorem) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiCalculus hCalc)

/--
Canonical Frechet-Wirtinger Riccati data give squared-density
Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianUniquenessTheorem_of_canonicalRiccatiCalculus
    (hCanonical : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_canonicalRiccatiCalculus
      hCanonical)

/--
Corrected Wirtinger-Riccati data plus continuity of the concrete scalar
linearized potential give squared-density Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianUniquenessTheorem_of_wirtingerRiccati_scalarPotentialContinuity
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hPotential :
      LocalLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_scalarPotentialContinuity
      hWirtinger hPotential)

/--
Corrected Wirtinger-Riccati data plus the pure real divided-difference
continuity lemma give squared-density Liouville-Schwarzian uniqueness.
-/
theorem localLiouvilleSchwarzianUniquenessTheorem_of_wirtingerRiccati_realExpTwoDividedDifference
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hdiv : RealExpTwoDividedDifferenceContinuityTheorem) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_wirtingerRiccati_scalarPotentialContinuity
    hWirtinger
    (localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_of_realExpTwoDividedDifference
      hdiv)

/--
Corrected Wirtinger-Riccati data give squared-density Liouville-Schwarzian
uniqueness via the proved scalar divided-difference continuity lemma.
-/
theorem localLiouvilleSchwarzianUniquenessTheorem_of_wirtingerRiccati
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati hWirtinger)

/--
Metric recovery from the hyperbolic 2-jet normalization.

This is the uniqueness step: once a local projective Schwarzian solution has
been Mobius-normalized to the prescribed hyperbolic base 2-jet, its Poincare
pullback squared density agrees with the original Liouville density.
-/
def HyperbolicTwoJetNormalizationRecoversMetricTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      ∀ z, z ∈ N.domain →
        u.densitySq z =
          Complex.normSq (N.normalized.projective.affineMapDeriv z) /
            ((N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2)

/--
%%handwave
name:
  Metric recovery from a normalized Schwarzian solution
statement:
  Let $F : V \to \mathbb H$ solve the metric Schwarzian equation for a
  hyperbolic conformal factor $u$ and have the normalized two-jet
  $F(z_0)=i$, $F'(z_0)=e^{u(z_0)}$, and
  $F''(z_0)=F'(z_0)(2u_z(z_0)-iF'(z_0))$.
  If the Poincaré pullback logarithmic factor
  $v=\log|F'|-\log\operatorname{Im}F$ solves the same Liouville--Schwarzian
  system as $u$ on a preconnected domain, and that system has the stated
  local uniqueness property, then
  $e^{2u}=|F'|^2/(\operatorname{Im}F)^2$ throughout $V$.
proof:
  The normalized two-jet gives $v(z_0)=u(z_0)$ and
  $v_z(z_0)=u_z(z_0)$. Local Liouville--Schwarzian uniqueness therefore gives
  $v=u$ on $V$. Exponentiating twice this equality yields the Poincaré
  pullback formula.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_liouvilleUniqueness
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hPreconnected : HyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem)
    (hUnique : LocalLiouvilleSchwarzianUniquenessTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem := by
  intro u S D z₀ N hu z hz
  rcases hPullback S N hu with ⟨C⟩
  exact C.pullback_eq_densitySq_of_eq_original hz
    (hUnique S N C hu (hPreconnected S N) z hz)

/--
The pullback calculation, preconnected shrinking, and logarithmic
Liouville-Schwarzian uniqueness give metric recovery.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hPreconnected : HyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem)
    (hLogUnique : LocalLiouvilleSchwarzianLogUniquenessTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_liouvilleUniqueness
    hPullback hPreconnected
    (localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness hLogUnique)

/--
The concrete scalar-potential route gives metric recovery from the hyperbolic
two-jet normalization.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_wirtingerRiccati_scalarPotentialContinuity
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hPreconnected : HyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem)
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hPotential :
      LocalLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness
    hPullback hPreconnected
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_scalarPotentialContinuity
      hWirtinger hPotential)

/--
The pure real divided-difference continuity lemma gives the scalar-potential
metric-recovery route.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_wirtingerRiccati_realExpTwoDividedDifference
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hPreconnected : HyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem)
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hdiv : RealExpTwoDividedDifferenceContinuityTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_wirtingerRiccati_scalarPotentialContinuity
    hPullback hPreconnected hWirtinger
    (localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_of_realExpTwoDividedDifference
      hdiv)

/--
Corrected Wirtinger-Riccati data give metric recovery from the hyperbolic
two-jet normalization via the proved scalar divided-difference continuity
lemma.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_wirtingerRiccati
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hPreconnected : HyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem)
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness
    hPullback hPreconnected
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati hWirtinger)

namespace LocalHyperbolicCanonicalPullbackLiouvilleFormulaData

/--
%%handwave
name:
  Liouville--Schwarzian uniqueness recovers the metric
statement:
  Let $u : V\to\mathbb R$ satisfy $\Delta u=e^{2u}$, and let
  $F:V\to\mathbb H$ have the normalized hyperbolic two-jet at $z_0$ and
  Schwarzian derivative $\{F,z\}=2(u_{zz}-u_z^2)$. If the canonical
  Poincaré pullback identities hold for $F$, then throughout the normalization
  domain
  $$e^{2u(z)}=\frac{|F'(z)|^2}{(\operatorname{Im}F(z))^2}.$$
proof:
  Put $v=\log|F'|-\log\operatorname{Im}F$ and $\phi=u-v$. Equality of the
  metric Schwarzians turns $\phi$ and its first Wirtinger derivative into a
  closed linear first-order system whose coefficients contain the continuous
  divided difference of $e^{2u}$ and $e^{2v}$. The normalized two-jet gives
  $\phi(z_0)=\phi_z(z_0)=0$. Uniqueness along the affine segment from $z_0$
  to $z$ yields $\phi(z)=0$, and exponentiation gives the formula.
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
Derivative algebra for a normalized branch gives metric recovery as soon as
the branch Schwarzian coefficient is the original metric Schwarzian of the
Liouville factor.

The Poincare Laplacian field is supplied internally by converting derivative
algebra to actual affine derivative algebra and using the mixed-expression
calculation.
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
Derivative algebra for a normalized branch gives the concrete Poincare metric
recovery formula under the original metric-Schwarzian identification.
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

/--
Metric recovery for local Schwarzian data that carry the original metric
Schwarzian identification.  The only pullback-side input is the canonical
Poincare formula package; corrected Wirtinger-Riccati uniqueness is derived
from that package and the coefficient identification.
-/
def HyperbolicTwoJetMetricSchwarzianNormalizationRecoversMetricTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (M : LocalMetricSchwarzianData u)
    {D : LocalProjectiveDevelopingMap M.toLocalSchwarzianData} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      ∀ z, z ∈ N.domain →
        u.densitySq z =
          Complex.normSq (N.normalized.projective.affineMapDeriv z) /
            ((N.normalized.upperHalfPlaneMap z : ℂ).im ^ 2)

/--
The canonical Poincare pullback formula proves metric recovery for metric
Schwarzian data without an external corrected-Riccati theorem.
-/
theorem hyperbolicTwoJetMetricSchwarzianNormalizationRecoversMetricTheorem_of_canonicalPullbackLiouvilleFormula
    (hPullback : HyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem) :
    HyperbolicTwoJetMetricSchwarzianNormalizationRecoversMetricTheorem := by
  intro u M D z₀ N hu z hz
  rcases hPullback M.toLocalSchwarzianData N hu with ⟨P⟩
  exact P.densitySq_eq_original_of_originalMetricSchwarzian
    hu M.originalMetricIdentification z hz

/--
For metric-Schwarzian data, derivative algebra for the normalized branch
directly gives metric recovery.  The canonical Poincare formula and the
corrected uniqueness data are constructed internally from the derivative
algebra package.
-/
theorem hyperbolicTwoJetMetricSchwarzianNormalizationRecoversMetricTheorem_of_derivativeAlgebra
    (hAlg : HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem) :
    HyperbolicTwoJetMetricSchwarzianNormalizationRecoversMetricTheorem := by
  intro u M D z₀ N hu z hz
  rcases hAlg M.toLocalSchwarzianData N hu with ⟨A⟩
  exact A.metric_recovery_of_originalMetricSchwarzian
    hu M.originalMetricIdentification z hz

/--
The Riccati uniqueness route gives metric recovery from the hyperbolic two-jet
normalization.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiUniqueness
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hPreconnected : HyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem)
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hRiccatiUnique : LocalRiccatiZeroUniquenessTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness
    hPullback hPreconnected
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_riccati
      hReduce hRiccatiUnique)

/--
The integrating-factor route gives metric recovery from the hyperbolic two-jet
normalization.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_integratingFactor
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hPreconnected : HyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem)
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hIF : LocalRiccatiIntegratingFactorTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness
    hPullback hPreconnected
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_integratingFactor
      hReduce hIF)

/--
The primitive/integrating-factor route gives metric recovery from the
hyperbolic two-jet normalization.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiPrimitive
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hPreconnected : HyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem)
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hPrim : LocalRiccatiPrimitiveExistenceTheorem)
    (hConst : LocalRiccatiPrimitiveProductConstancyTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_integratingFactor
    hPullback hPreconnected hReduce
    (localRiccatiIntegratingFactorTheorem_of_primitive hPrim hConst)

/--
Primitive existence plus the derivative-zero product-rule calculation give
metric recovery from the hyperbolic two-jet normalization.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiPrimitiveDerivativeZero
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hPreconnected : HyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem)
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hPrim : LocalRiccatiPrimitiveExistenceTheorem)
    (hDerivZero : LocalRiccatiPrimitiveProductDerivativeZeroTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_integratingFactor
    hPullback hPreconnected hReduce
    (localRiccatiIntegratingFactorTheorem_of_primitive_derivativeZero
      hPrim hDerivZero)

/--
Primitive existence alone gives metric recovery from the hyperbolic two-jet
normalization, since the product-rule calculation is now proved by mathlib
calculus.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiPrimitiveExistence
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hPreconnected : HyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem)
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hPrim : LocalRiccatiPrimitiveExistenceTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_integratingFactor
    hPullback hPreconnected hReduce
    (localRiccatiIntegratingFactorTheorem_of_primitiveExistence hPrim)

/--
Disk-local holomorphicity of the Riccati coefficient gives metric recovery
from the hyperbolic two-jet normalization.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiBallHolomorphic
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hPreconnected : HyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem)
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hBall : LocalRiccatiCoefficientBallHolomorphicTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_integratingFactor
    hPullback hPreconnected hReduce
    (localRiccatiIntegratingFactorTheorem_of_ballHolomorphic hBall)

/--
Analyticity of the Riccati coefficient on ball-shaped normalized domains gives
metric recovery from the hyperbolic two-jet normalization.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiBallAnalytic
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hPreconnected : HyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem)
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hAnalytic : LocalRiccatiCoefficientBallAnalyticTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_integratingFactor
    hPullback hPreconnected hReduce
    (localRiccatiIntegratingFactorTheorem_of_ballAnalytic hAnalytic)

/--
Ball-shaped normalized domains and analytic Riccati coefficients give metric
recovery, with preconnectedness supplied by mathlib's connectedness of balls.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiBallAnalyticAndBallDomain
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem)
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hAnalytic : LocalRiccatiCoefficientBallAnalyticTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiBallAnalytic
    hPullback
    (hyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem_of_ballDomain
      hBallDomain)
    hReduce hAnalytic

/--
Domain-level analytic Riccati coefficients and ball-shaped normalized domains
give metric recovery.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiAnalyticAndBallDomain
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem)
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiBallAnalyticAndBallDomain
    hPullback hBallDomain hReduce
    (localRiccatiCoefficientBallAnalyticTheorem_of_analytic_and_ballDomain
      hAnalytic hBallDomain)

/--
Domain-level analytic Riccati coefficients give metric recovery; ball domains
and preconnectedness are supplied by the two-jet normalization package.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiAnalytic
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiAnalyticAndBallDomain
    hPullback hyperbolicTwoJetNormalizationHasBallDomainTheorem
    hReduce hAnalytic

/--
The current strongest unbundled metric-recovery bridge: after the direct
pullback Liouville calculation, the only uniqueness-side input is the Riccati
reduction data.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiReduction
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness
    hPullback
    (hyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem_of_ballDomain
      hyperbolicTwoJetNormalizationHasBallDomainTheorem)
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiReduction hReduce)

/--
The metric-recovery bridge expressed in terms of the concrete Riccati calculus
target.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiCalculus
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hCalc : LocalLiouvilleSchwarzianRiccatiReductionCalculusTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiReduction
    hPullback
    (localLiouvilleSchwarzianRiccatiReductionTheorem_of_calculus hCalc)

/--
The metric-recovery bridge expressed in terms of canonical Frechet-Wirtinger
Riccati calculus data.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_canonicalRiccatiCalculus
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hCanonical : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiCalculus
    hPullback
    (localLiouvilleSchwarzianRiccatiReductionCalculusTheorem_of_canonical
      hCanonical)

/--
Metric recovery from the strengthened holomorphic Wirtinger-Riccati package.
This is the honest replacement for the over-strong canonical complex-derivative
route: once the extra holomorphic Riccati data are supplied, the rest is
already handled by the scalar Riccati package.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_canonicalMetricHolomorphicRiccati
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hHolomorphic : LocalLiouvilleSchwarzianCanonicalMetricHolomorphicRiccatiTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiReduction
    hPullback
    (localLiouvilleSchwarzianRiccatiReductionTheorem_of_canonicalMetricHolomorphicRiccati
      hHolomorphic)

/--
Metric recovery from the corrected Wirtinger-Riccati reduction and the genuine
first-order Liouville-Schwarzian uniqueness theorem.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_wirtingerRiccati_firstOrderUnique
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hUnique : LocalLiouvilleSchwarzianFirstOrderSystemUniquenessTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness
    hPullback
    (hyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem_of_ballDomain
      hyperbolicTwoJetNormalizationHasBallDomainTheorem)
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_firstOrderUnique
      hWirtinger hUnique)

/--
Metric recovery from the corrected Wirtinger-Riccati reduction and uniqueness
for the scalar elliptic difference formulation.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_wirtingerRiccati_scalarDifferenceUnique
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hUnique : LocalLiouvilleSchwarzianScalarDifferenceUniquenessTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness
    hPullback
    (hyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem_of_ballDomain
      hyperbolicTwoJetNormalizationHasBallDomainTheorem)
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_scalarDifferenceUnique
      hWirtinger hUnique)

/--
Metric recovery from the corrected Wirtinger-Riccati reduction and uniqueness
for the linearized scalar elliptic difference formulation.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_wirtingerRiccati_linearizedScalarDifferenceUnique
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hUnique : LocalLiouvilleSchwarzianLinearizedScalarDifferenceUniquenessTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness
    hPullback
    (hyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem_of_ballDomain
      hyperbolicTwoJetNormalizationHasBallDomainTheorem)
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_linearizedScalarDifferenceUnique
      hWirtinger hUnique)

/--
Metric recovery from the corrected Wirtinger-Riccati reduction and standard
linear elliptic Cauchy uniqueness.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_wirtingerRiccati_linearEllipticCauchyUnique
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hUnique : LocalLiouvilleSchwarzianLinearEllipticCauchyUniquenessTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness
    hPullback
    (hyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem_of_ballDomain
      hyperbolicTwoJetNormalizationHasBallDomainTheorem)
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_linearEllipticCauchyUnique
      hWirtinger hUnique)

/--
Metric recovery from the corrected Wirtinger-Riccati reduction and pathwise
uniqueness for the closed first-order linear system.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_wirtingerRiccati_closedFirstOrderLinearSystemUnique
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hUnique : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness
    hPullback
    (hyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem_of_ballDomain
      hyperbolicTwoJetNormalizationHasBallDomainTheorem)
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_closedFirstOrderLinearSystemUnique
      hWirtinger hUnique)

/--
The remaining theorem package for the local metric-recovery uniqueness step.

The two-jet normalization has already been shrunk to a ball, and the Riccati
reduction data now carries coefficient analyticity.  The scalar Riccati ODE
part beneath this bundle is discharged by mathlib primitives on disks, the
product rule, the derivative of `Complex.exp`, and connectedness of balls.
-/
structure HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems where
  /-- The normalized upper-half-plane branch gives a Liouville pullback factor. -/
  pullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem
  /-- Equal Schwarzians reduce log-density uniqueness to a Riccati equation. -/
  riccatiReduction : LocalLiouvilleSchwarzianRiccatiReductionTheorem

namespace HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems

/--
The bundled Riccati boundary inherits ball-shaped normalized domains from the
two-jet normalization package itself.
-/
theorem ballDomain (_B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    HyperbolicTwoJetNormalizationHasBallDomainTheorem :=
  hyperbolicTwoJetNormalizationHasBallDomainTheorem

/-- The bundled Riccati analytic boundary gives logarithmic uniqueness. -/
theorem localLogUniqueness (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiReduction
    B.riccatiReduction

/-- The bundled Riccati analytic boundary gives squared-density uniqueness. -/
theorem localUniqueness (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness B.localLogUniqueness

/-- The bundled Riccati analytic boundary gives metric recovery. -/
theorem recoversMetric (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiReduction
    B.pullback B.riccatiReduction

end HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems

/--
Sharper bundled version of the metric-recovery boundary.

Compared with `HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems`, this asks for
the concrete Riccati calculus data rather than the already-packaged Riccati
difference data.  Lean proves the algebraic passage from this calculus data to
the Riccati package.
-/
structure HyperbolicTwoJetRiccatiCalculusBoundaryTheorems where
  /-- The normalized upper-half-plane branch gives a Liouville pullback factor. -/
  pullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem
  /-- The concrete same-Schwarzian calculus data behind the Riccati reduction. -/
  riccatiCalculus : LocalLiouvilleSchwarzianRiccatiReductionCalculusTheorem

namespace HyperbolicTwoJetRiccatiCalculusBoundaryTheorems

/-- Forget the concrete calculus provenance, retaining the Riccati reduction package. -/
def toRiccatiAnalyticBoundary
    (B : HyperbolicTwoJetRiccatiCalculusBoundaryTheorems) :
    HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems where
  pullback := B.pullback
  riccatiReduction :=
    localLiouvilleSchwarzianRiccatiReductionTheorem_of_calculus B.riccatiCalculus

/-- The bundled concrete Riccati calculus boundary gives logarithmic uniqueness. -/
theorem localLogUniqueness (B : HyperbolicTwoJetRiccatiCalculusBoundaryTheorems) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiCalculus
    B.riccatiCalculus

/-- The bundled concrete Riccati calculus boundary gives squared-density uniqueness. -/
theorem localUniqueness (B : HyperbolicTwoJetRiccatiCalculusBoundaryTheorems) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness B.localLogUniqueness

/-- The bundled concrete Riccati calculus boundary gives metric recovery. -/
theorem recoversMetric (B : HyperbolicTwoJetRiccatiCalculusBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiCalculus
    B.pullback B.riccatiCalculus

end HyperbolicTwoJetRiccatiCalculusBoundaryTheorems

/--
Sharpest bundled version of the metric-recovery boundary on the uniqueness
side: the Riccati data are the canonical Frechet-Wirtinger fields of the
original and pullback conformal factors.
-/
structure HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems where
  /-- The normalized upper-half-plane branch gives a Liouville pullback factor. -/
  pullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem
  /-- The canonical Frechet-Wirtinger Riccati target. -/
  canonicalRiccati : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem

namespace HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems

/-- Forget to the concrete Riccati calculus boundary. -/
def toRiccatiCalculusBoundary
    (B : HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetRiccatiCalculusBoundaryTheorems where
  pullback := B.pullback
  riccatiCalculus :=
    localLiouvilleSchwarzianRiccatiReductionCalculusTheorem_of_canonical
      B.canonicalRiccati

/-- Forget to the older Riccati analytic boundary. -/
def toRiccatiAnalyticBoundary
    (B : HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems :=
  B.toRiccatiCalculusBoundary.toRiccatiAnalyticBoundary

/-- The bundled canonical Riccati boundary gives logarithmic uniqueness. -/
theorem localLogUniqueness (B : HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_canonicalRiccatiCalculus
    B.canonicalRiccati

/-- The bundled canonical Riccati boundary gives squared-density uniqueness. -/
theorem localUniqueness (B : HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness B.localLogUniqueness

/-- The bundled canonical Riccati boundary gives metric recovery. -/
theorem recoversMetric (B : HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_canonicalRiccatiCalculus
    B.pullback B.canonicalRiccati

end HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems

/--
Metric-scaled canonical version of the metric-recovery boundary.

This is the form closest to the projective-connection calculation: the
remaining Schwarzian equality is the equality of the actual metric Schwarzian
coefficients, not the already-divided half-Schwarzian expressions.
-/
structure HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems where
  /-- The normalized upper-half-plane branch gives a Liouville pullback factor. -/
  pullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem
  /-- The metric-scaled canonical Frechet-Wirtinger Riccati target. -/
  canonicalMetricRiccati : LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusTheorem

namespace HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems

/-- Forget the metric scaling in the Schwarzian equality. -/
def toCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems where
  pullback := B.pullback
  canonicalRiccati :=
    localLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem_of_metric
      B.canonicalMetricRiccati

/-- Forget to the concrete Riccati calculus boundary. -/
def toRiccatiCalculusBoundary
    (B : HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetRiccatiCalculusBoundaryTheorems :=
  B.toCanonicalRiccatiBoundary.toRiccatiCalculusBoundary

/-- Forget to the older Riccati analytic boundary. -/
def toRiccatiAnalyticBoundary
    (B : HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems :=
  B.toCanonicalRiccatiBoundary.toRiccatiAnalyticBoundary

/-- The bundled metric-scaled canonical boundary gives logarithmic uniqueness. -/
theorem localLogUniqueness (B : HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  B.toCanonicalRiccatiBoundary.localLogUniqueness

/-- The bundled metric-scaled canonical boundary gives squared-density uniqueness. -/
theorem localUniqueness (B : HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  B.toCanonicalRiccatiBoundary.localUniqueness

/-- The bundled metric-scaled canonical boundary gives metric recovery. -/
theorem recoversMetric (B : HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.toCanonicalRiccatiBoundary.recoversMetric

end HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems

/--
Corrected Frechet-Wirtinger version of the metric-recovery boundary.

Compared with `HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems`, this
does not require the first Wirtinger fields to be packaged as holomorphic
complex-derivative data.  The pathwise Liouville-Schwarzian uniqueness
argument now handles the honest Frechet-Wirtinger equation.
-/
structure HyperbolicTwoJetCanonicalMetricWirtingerRiccatiBoundaryTheorems where
  /-- The normalized upper-half-plane branch gives a Liouville pullback factor. -/
  pullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem
  /-- The corrected metric-scaled Frechet-Wirtinger Riccati target. -/
  canonicalMetricWirtingerRiccati :
    LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem

namespace HyperbolicTwoJetCanonicalMetricWirtingerRiccatiBoundaryTheorems

/-- The older metric-scaled calculus boundary forgets to the corrected Wirtinger boundary. -/
def ofCanonicalMetricRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalMetricWirtingerRiccatiBoundaryTheorems where
  pullback := B.pullback
  canonicalMetricWirtingerRiccati :=
    localLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem_of_metric
      B.canonicalMetricRiccati

/-- The corrected Wirtinger boundary gives logarithmic uniqueness. -/
theorem localLogUniqueness
    (B : HyperbolicTwoJetCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati
    B.canonicalMetricWirtingerRiccati

/-- The corrected Wirtinger boundary gives squared-density uniqueness. -/
theorem localUniqueness
    (B : HyperbolicTwoJetCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_wirtingerRiccati
    B.canonicalMetricWirtingerRiccati

/-- The corrected Wirtinger boundary gives metric recovery. -/
theorem recoversMetric
    (B : HyperbolicTwoJetCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_wirtingerRiccati
    B.pullback
    (hyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem_of_ballDomain
      hyperbolicTwoJetNormalizationHasBallDomainTheorem)
    B.canonicalMetricWirtingerRiccati

end HyperbolicTwoJetCanonicalMetricWirtingerRiccatiBoundaryTheorems

/--
Formula-level metric-recovery boundary.

This is sharper than `HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems` on the
pullback side: it asks for the explicit Poincare pullback log-density formula
before packaging it as a `LocalHyperbolicPullbackLiouvilleCandidate`.
-/
structure HyperbolicTwoJetPullbackFormulaCanonicalRiccatiBoundaryTheorems where
  /-- The explicit pullback formula gives a Liouville factor. -/
  pullbackFormula : HyperbolicTwoJetPullbackLiouvilleFormulaTheorem
  /-- The canonical Frechet-Wirtinger Riccati target. -/
  canonicalRiccati : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem

namespace HyperbolicTwoJetPullbackFormulaCanonicalRiccatiBoundaryTheorems

/-- Forget the explicit formula provenance, retaining a pullback candidate. -/
def toCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetPullbackFormulaCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems where
  pullback := hyperbolicTwoJetPullbackLiouvilleCandidateTheorem_of_formula
    B.pullbackFormula
  canonicalRiccati := B.canonicalRiccati

/-- The formula-level boundary gives metric recovery. -/
theorem recoversMetric
    (B : HyperbolicTwoJetPullbackFormulaCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.toCanonicalRiccatiBoundary.recoversMetric

end HyperbolicTwoJetPullbackFormulaCanonicalRiccatiBoundaryTheorems

/--
Formula-level metric-scaled metric-recovery boundary.

This combines the explicit Poincare pullback formula with the more natural
metric-scaled canonical Riccati target.
-/
structure HyperbolicTwoJetPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems where
  /-- The explicit pullback formula gives a Liouville factor. -/
  pullbackFormula : HyperbolicTwoJetPullbackLiouvilleFormulaTheorem
  /-- The metric-scaled canonical Frechet-Wirtinger Riccati target. -/
  canonicalMetricRiccati : LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusTheorem

namespace HyperbolicTwoJetPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems

/-- Forget the metric scaling in the Schwarzian equality. -/
def toPullbackFormulaCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetPullbackFormulaCanonicalRiccatiBoundaryTheorems where
  pullbackFormula := B.pullbackFormula
  canonicalRiccati :=
    localLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem_of_metric
      B.canonicalMetricRiccati

/-- Forget the explicit formula provenance, retaining a metric-scaled canonical boundary. -/
def toCanonicalMetricRiccatiBoundary
    (B : HyperbolicTwoJetPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems where
  pullback := hyperbolicTwoJetPullbackLiouvilleCandidateTheorem_of_formula
    B.pullbackFormula
  canonicalMetricRiccati := B.canonicalMetricRiccati

/-- The formula-level metric-scaled boundary gives metric recovery. -/
theorem recoversMetric
    (B : HyperbolicTwoJetPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.toCanonicalMetricRiccatiBoundary.recoversMetric

end HyperbolicTwoJetPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems

/--
Canonical-formula metric-recovery boundary.

This is the same uniqueness-side boundary as
`HyperbolicTwoJetPullbackFormulaCanonicalRiccatiBoundaryTheorems`, but it fixes
the pullback log-density to the canonical expression
`(1 / 2) log (|F'|² / (Im F)²)`.
-/
structure HyperbolicTwoJetCanonicalPullbackFormulaCanonicalRiccatiBoundaryTheorems where
  /-- The canonical pullback formula gives a Liouville factor. -/
  canonicalPullbackFormula : HyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem
  /-- The canonical Frechet-Wirtinger Riccati target. -/
  canonicalRiccati : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem

namespace HyperbolicTwoJetCanonicalPullbackFormulaCanonicalRiccatiBoundaryTheorems

/-- Forget the canonical logarithmic representative, retaining the formula-level boundary. -/
def toPullbackFormulaCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackFormulaCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetPullbackFormulaCanonicalRiccatiBoundaryTheorems where
  pullbackFormula :=
    hyperbolicTwoJetPullbackLiouvilleFormulaTheorem_of_canonical
      B.canonicalPullbackFormula
  canonicalRiccati := B.canonicalRiccati

/-- The canonical-formula boundary gives metric recovery. -/
theorem recoversMetric
    (B : HyperbolicTwoJetCanonicalPullbackFormulaCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.toPullbackFormulaCanonicalRiccatiBoundary.recoversMetric

end HyperbolicTwoJetCanonicalPullbackFormulaCanonicalRiccatiBoundaryTheorems

/--
Canonical-formula metric-scaled metric-recovery boundary.

This fixes the pullback logarithmic density to the canonical expression and
states the uniqueness-side Schwarzian equality at the usual metric scale.
-/
structure HyperbolicTwoJetCanonicalPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems where
  /-- The canonical pullback formula gives a Liouville factor. -/
  canonicalPullbackFormula : HyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem
  /-- The metric-scaled canonical Frechet-Wirtinger Riccati target. -/
  canonicalMetricRiccati : LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusTheorem

namespace HyperbolicTwoJetCanonicalPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems

/-- Forget the metric scaling in the Schwarzian equality. -/
def toCanonicalPullbackFormulaCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalPullbackFormulaCanonicalRiccatiBoundaryTheorems where
  canonicalPullbackFormula := B.canonicalPullbackFormula
  canonicalRiccati :=
    localLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem_of_metric
      B.canonicalMetricRiccati

/-- Forget the canonical logarithmic representative, retaining the formula-level boundary. -/
def toPullbackFormulaCanonicalMetricRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems where
  pullbackFormula :=
    hyperbolicTwoJetPullbackLiouvilleFormulaTheorem_of_canonical
      B.canonicalPullbackFormula
  canonicalMetricRiccati := B.canonicalMetricRiccati

/-- The canonical-formula metric-scaled boundary gives metric recovery. -/
theorem recoversMetric
    (B : HyperbolicTwoJetCanonicalPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.toPullbackFormulaCanonicalMetricRiccatiBoundary.recoversMetric

end HyperbolicTwoJetCanonicalPullbackFormulaCanonicalMetricRiccatiBoundaryTheorems

/--
Wirtinger-formula metric-recovery boundary.

This is sharper than
`HyperbolicTwoJetCanonicalPullbackFormulaCanonicalRiccatiBoundaryTheorems` on
the pullback side: the Schwarzian calculation is reduced to the explicit first
and second Wirtinger formulas for the canonical Poincare pullback log-density.
-/
structure HyperbolicTwoJetCanonicalPullbackWirtingerFormulaCanonicalRiccatiBoundaryTheorems where
  /-- The canonical pullback formula follows from the Laplacian and Wirtinger formulas. -/
  canonicalPullbackWirtingerFormula :
    HyperbolicTwoJetCanonicalPullbackWirtingerFormulaTheorem
  /-- The canonical Frechet-Wirtinger Riccati target. -/
  canonicalRiccati : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem

namespace HyperbolicTwoJetCanonicalPullbackWirtingerFormulaCanonicalRiccatiBoundaryTheorems

/-- Forget the explicit Wirtinger-formula provenance, retaining the canonical formula boundary. -/
def toCanonicalPullbackFormulaCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackWirtingerFormulaCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalPullbackFormulaCanonicalRiccatiBoundaryTheorems where
  canonicalPullbackFormula :=
    hyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem_of_wirtingerFormula
      B.canonicalPullbackWirtingerFormula
  canonicalRiccati := B.canonicalRiccati

/-- The Wirtinger-formula boundary gives metric recovery. -/
theorem recoversMetric
    (B : HyperbolicTwoJetCanonicalPullbackWirtingerFormulaCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.toCanonicalPullbackFormulaCanonicalRiccatiBoundary.recoversMetric

end HyperbolicTwoJetCanonicalPullbackWirtingerFormulaCanonicalRiccatiBoundaryTheorems

/--
Density-derivative metric-recovery boundary.

This is sharper than the Wirtinger-formula bundle on the pullback side: the
first logarithmic Wirtinger formula is obtained from the pointwise
squared-density derivative formula by the Frechet-Wirtinger logarithm chain
rule.
-/
structure HyperbolicTwoJetCanonicalPullbackDensityDerivativeCanonicalRiccatiBoundaryTheorems where
  /-- The canonical pullback formula follows from the density derivative and second Wirtinger data. -/
  canonicalPullbackDensityDerivative :
    HyperbolicTwoJetCanonicalPullbackDensityDerivativeTheorem
  /-- The canonical Frechet-Wirtinger Riccati target. -/
  canonicalRiccati : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem

namespace HyperbolicTwoJetCanonicalPullbackDensityDerivativeCanonicalRiccatiBoundaryTheorems

/-- Forget the squared-density derivative provenance, retaining the Wirtinger-formula boundary. -/
def toCanonicalPullbackWirtingerFormulaCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackDensityDerivativeCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalPullbackWirtingerFormulaCanonicalRiccatiBoundaryTheorems where
  canonicalPullbackWirtingerFormula :=
    hyperbolicTwoJetCanonicalPullbackWirtingerFormulaTheorem_of_densityDerivative
      B.canonicalPullbackDensityDerivative
  canonicalRiccati := B.canonicalRiccati

/-- The density-derivative boundary gives metric recovery. -/
theorem recoversMetric
    (B : HyperbolicTwoJetCanonicalPullbackDensityDerivativeCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.toCanonicalPullbackWirtingerFormulaCanonicalRiccatiBoundary.recoversMetric

end HyperbolicTwoJetCanonicalPullbackDensityDerivativeCanonicalRiccatiBoundaryTheorems

/--
Branch-derivative metric-recovery boundary.

This is sharper than the density-derivative bundle on the first-derivative
side: the squared-density derivative formula is derived from actual complex
derivatives of the normalized branch and of its derivative branch.
-/
structure HyperbolicTwoJetCanonicalPullbackBranchDerivativeCanonicalRiccatiBoundaryTheorems where
  /-- The canonical pullback formula follows from actual branch derivatives and the remaining formulas. -/
  canonicalPullbackBranchDerivative :
    HyperbolicTwoJetCanonicalPullbackBranchDerivativeTheorem
  /-- The canonical Frechet-Wirtinger Riccati target. -/
  canonicalRiccati : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem

namespace HyperbolicTwoJetCanonicalPullbackBranchDerivativeCanonicalRiccatiBoundaryTheorems

/-- Forget the actual branch derivative provenance, retaining the density-derivative boundary. -/
def toCanonicalPullbackDensityDerivativeCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackBranchDerivativeCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalPullbackDensityDerivativeCanonicalRiccatiBoundaryTheorems where
  canonicalPullbackDensityDerivative :=
    hyperbolicTwoJetCanonicalPullbackDensityDerivativeTheorem_of_branchDerivative
      B.canonicalPullbackBranchDerivative
  canonicalRiccati := B.canonicalRiccati

/-- The branch-derivative boundary gives metric recovery. -/
theorem recoversMetric
    (B : HyperbolicTwoJetCanonicalPullbackBranchDerivativeCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.toCanonicalPullbackDensityDerivativeCanonicalRiccatiBoundary.recoversMetric

end HyperbolicTwoJetCanonicalPullbackBranchDerivativeCanonicalRiccatiBoundaryTheorems

/--
Second-expression metric-recovery boundary.

This is sharper than the branch-derivative bundle on the pullback side: the
remaining second Wirtinger formula is replaced by the Frechet derivative
identity for the explicit first Wirtinger expression.
-/
structure HyperbolicTwoJetCanonicalPullbackSecondExpressionCanonicalRiccatiBoundaryTheorems where
  /--
  The canonical pullback formula follows from actual branch derivatives and
  the explicit derivative of the first Wirtinger expression.
  -/
  canonicalPullbackSecondExpression :
    HyperbolicTwoJetCanonicalPullbackSecondExpressionTheorem
  /-- The canonical Frechet-Wirtinger Riccati target. -/
  canonicalRiccati : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem

namespace HyperbolicTwoJetCanonicalPullbackSecondExpressionCanonicalRiccatiBoundaryTheorems

/-- Forget the explicit second-expression provenance, retaining the branch-derivative boundary. -/
def toCanonicalPullbackBranchDerivativeCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackSecondExpressionCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalPullbackBranchDerivativeCanonicalRiccatiBoundaryTheorems where
  canonicalPullbackBranchDerivative :=
    hyperbolicTwoJetCanonicalPullbackBranchDerivativeTheorem_of_secondExpression
      B.canonicalPullbackSecondExpression
  canonicalRiccati := B.canonicalRiccati

/-- The second-expression boundary gives metric recovery. -/
theorem recoversMetric
    (B : HyperbolicTwoJetCanonicalPullbackSecondExpressionCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.toCanonicalPullbackBranchDerivativeCanonicalRiccatiBoundary.recoversMetric

end HyperbolicTwoJetCanonicalPullbackSecondExpressionCanonicalRiccatiBoundaryTheorems

/--
Third-derivative metric-recovery boundary.

This is sharper than the second-expression bundle on the pullback side: the
explicit first-expression derivative is proved from actual derivative
identities through `F''`.
-/
structure HyperbolicTwoJetCanonicalPullbackThirdDerivativeCanonicalRiccatiBoundaryTheorems where
  /--
  The canonical pullback formula follows from actual branch derivatives through
  `F''` and the remaining Laplacian calculation.
  -/
  canonicalPullbackThirdDerivative :
    HyperbolicTwoJetCanonicalPullbackThirdDerivativeTheorem
  /-- The canonical Frechet-Wirtinger Riccati target. -/
  canonicalRiccati : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem

namespace HyperbolicTwoJetCanonicalPullbackThirdDerivativeCanonicalRiccatiBoundaryTheorems

/-- Forget the third-derivative provenance, retaining the second-expression boundary. -/
def toCanonicalPullbackSecondExpressionCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackThirdDerivativeCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalPullbackSecondExpressionCanonicalRiccatiBoundaryTheorems where
  canonicalPullbackSecondExpression :=
    hyperbolicTwoJetCanonicalPullbackSecondExpressionTheorem_of_thirdDerivative
      B.canonicalPullbackThirdDerivative
  canonicalRiccati := B.canonicalRiccati

/-- The third-derivative boundary gives metric recovery. -/
theorem recoversMetric
    (B : HyperbolicTwoJetCanonicalPullbackThirdDerivativeCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.toCanonicalPullbackSecondExpressionCanonicalRiccatiBoundary.recoversMetric

end HyperbolicTwoJetCanonicalPullbackThirdDerivativeCanonicalRiccatiBoundaryTheorems

/--
Affine-derivative metric-recovery boundary.

This is sharper than the third-derivative bundle on the pullback side: the
derivative of the `ℍ`-valued lift is derived from the affine projective branch
by local equality on the open normalized domain.
-/
structure HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalRiccatiBoundaryTheorems where
  /--
  The canonical pullback formula follows from affine branch derivatives through
  `F''` and the remaining Laplacian calculation.
  -/
  canonicalPullbackAffineDerivative :
    HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem
  /-- The canonical Frechet-Wirtinger Riccati target. -/
  canonicalRiccati : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem

namespace HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalRiccatiBoundaryTheorems

/-- Forget the affine-derivative provenance, retaining the third-derivative boundary. -/
def toCanonicalPullbackThirdDerivativeCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalPullbackThirdDerivativeCanonicalRiccatiBoundaryTheorems where
  canonicalPullbackThirdDerivative :=
    hyperbolicTwoJetCanonicalPullbackThirdDerivativeTheorem_of_affineDerivative
      B.canonicalPullbackAffineDerivative
  canonicalRiccati := B.canonicalRiccati

/-- The affine-derivative boundary gives metric recovery. -/
theorem recoversMetric
    (B : HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.toCanonicalPullbackThirdDerivativeCanonicalRiccatiBoundary.recoversMetric

end HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalRiccatiBoundaryTheorems

/--
Derivative-identification metric-recovery boundary.

This is sharper than the affine-derivative bundle on the pullback side: the
actual `HasDerivAt` statements are derived from complex differentiability and
identification with mathlib's `deriv`.
-/
structure HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems where
  /--
  The canonical pullback formula follows from derivative identifications
  through `F''` and the remaining Laplacian calculation.
  -/
  canonicalPullbackDerivIdentified :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem
  /-- The canonical Frechet-Wirtinger Riccati target. -/
  canonicalRiccati : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem

namespace HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems

/-- Forget the derivative-identified pullback provenance, retaining the canonical Riccati bundle. -/
def toCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems where
  pullback :=
    hyperbolicTwoJetPullbackLiouvilleCandidateTheorem_of_formula
      (hyperbolicTwoJetPullbackLiouvilleFormulaTheorem_of_canonical
        (hyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem_of_derivIdentified
      B.canonicalPullbackDerivIdentified))
  canonicalRiccati := B.canonicalRiccati

/-- Forget to the concrete-calculus Riccati boundary. -/
def toRiccatiCalculusBoundary
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetRiccatiCalculusBoundaryTheorems :=
  B.toCanonicalRiccatiBoundary.toRiccatiCalculusBoundary

/-- Forget to the older Riccati analytic boundary. -/
def toRiccatiAnalyticBoundary
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems :=
  B.toCanonicalRiccatiBoundary.toRiccatiAnalyticBoundary

/-- Forget the `deriv`-identified provenance, retaining the affine-derivative boundary. -/
def toCanonicalPullbackAffineDerivativeCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalRiccatiBoundaryTheorems where
  canonicalPullbackAffineDerivative :=
    hyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem_of_derivIdentified
      B.canonicalPullbackDerivIdentified
  canonicalRiccati := B.canonicalRiccati

/-- The derivative-identification boundary gives metric recovery. -/
theorem recoversMetric
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
    B.toCanonicalRiccatiBoundary.recoversMetric

end HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems

/--
Derivative-identification metric-scaled metric-recovery boundary.

This is the current strongest pullback-side bridge paired with the
metric-scaled canonical Riccati target.
-/
structure HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricRiccatiBoundaryTheorems where
  /--
  The canonical pullback formula follows from derivative identifications
  through `F''` and the remaining Laplacian calculation.
  -/
  canonicalPullbackDerivIdentified :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem
  /-- The metric-scaled canonical Frechet-Wirtinger Riccati target. -/
  canonicalMetricRiccati : LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusTheorem

namespace HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricRiccatiBoundaryTheorems

/-- Forget the metric scaling in the Schwarzian equality. -/
def toCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems where
  canonicalPullbackDerivIdentified := B.canonicalPullbackDerivIdentified
  canonicalRiccati :=
    localLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem_of_metric
      B.canonicalMetricRiccati

/-- Forget the derivative-identified pullback provenance, retaining the metric-scaled boundary. -/
def toCanonicalMetricRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems where
  pullback :=
    hyperbolicTwoJetPullbackLiouvilleCandidateTheorem_of_formula
      (hyperbolicTwoJetPullbackLiouvilleFormulaTheorem_of_canonical
        (hyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem_of_derivIdentified
      B.canonicalPullbackDerivIdentified))
  canonicalMetricRiccati := B.canonicalMetricRiccati

/-- Forget to the older canonical Riccati boundary. -/
def toCanonicalRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems :=
  B.toCanonicalMetricRiccatiBoundary.toCanonicalRiccatiBoundary

/-- Forget to the concrete-calculus Riccati boundary. -/
def toRiccatiCalculusBoundary
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetRiccatiCalculusBoundaryTheorems :=
  B.toCanonicalMetricRiccatiBoundary.toRiccatiCalculusBoundary

/-- Forget to the older Riccati analytic boundary. -/
def toRiccatiAnalyticBoundary
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems :=
  B.toCanonicalMetricRiccatiBoundary.toRiccatiAnalyticBoundary

/-- The derivative-identification metric-scaled boundary gives metric recovery. -/
theorem recoversMetric
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.toCanonicalMetricRiccatiBoundary.recoversMetric

end HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricRiccatiBoundaryTheorems

/--
Derivative-identification boundary paired with the corrected
Frechet-Wirtinger Riccati uniqueness input.

This is the same pullback-side boundary as the metric-scaled calculus package,
but the uniqueness side only asks for the honest Frechet-Wirtinger Riccati
equation.
-/
structure HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems where
  /--
  The canonical pullback formula follows from derivative identifications
  through `F''` and the remaining Laplacian calculation.
  -/
  canonicalPullbackDerivIdentified :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem
  /-- The corrected metric-scaled Frechet-Wirtinger Riccati target. -/
  canonicalMetricWirtingerRiccati :
    LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem

namespace HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems

/-- Forget the derivative-identified pullback provenance, retaining the corrected boundary. -/
def toCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalMetricWirtingerRiccatiBoundaryTheorems where
  pullback :=
    hyperbolicTwoJetPullbackLiouvilleCandidateTheorem_of_formula
      (hyperbolicTwoJetPullbackLiouvilleFormulaTheorem_of_canonical
        (hyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem_of_derivIdentified
      B.canonicalPullbackDerivIdentified))
  canonicalMetricWirtingerRiccati := B.canonicalMetricWirtingerRiccati

/--
The older derivative-identified metric-scaled calculus boundary forgets to the
corrected Frechet-Wirtinger one.
-/
def ofCanonicalMetricRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems where
  canonicalPullbackDerivIdentified := B.canonicalPullbackDerivIdentified
  canonicalMetricWirtingerRiccati :=
    localLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem_of_metric
      B.canonicalMetricRiccati

/-- The derivative-identified corrected Wirtinger boundary gives metric recovery. -/
theorem recoversMetric
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
    B.toCanonicalMetricWirtingerRiccatiBoundary.recoversMetric

end HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems

/--
Derivative-algebra boundary paired with the corrected Frechet-Wirtinger
Riccati uniqueness input.

This is sharper than the older derivative-algebra-plus-Laplacian route: the
Poincare Laplacian calculation is derived after converting derivative algebra
to actual affine derivative algebra.
-/
structure HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems where
  /-- Derivative algebra for the canonical Poincare pullback. -/
  canonicalPullbackDerivativeAlgebra :
    HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem
  /-- The corrected metric-scaled Frechet-Wirtinger Riccati target. -/
  canonicalMetricWirtingerRiccati :
    LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem

namespace HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

/-- Convert directly to the derivative-identified corrected boundary. -/
def toDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems where
  canonicalPullbackDerivIdentified :=
    hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_derivativeAlgebra
      B.canonicalPullbackDerivativeAlgebra
  canonicalMetricWirtingerRiccati := B.canonicalMetricWirtingerRiccati

/-- The derivative-algebra corrected boundary gives two-jet metric recovery. -/
theorem recoversMetric
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.toDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundary.recoversMetric

/-- Forget to the corrected canonical metric package. -/
def toCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalMetricWirtingerRiccatiBoundaryTheorems :=
  B.toDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundary.toCanonicalMetricWirtingerRiccatiBoundary

end HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

/--
Affine-derivative boundary paired with the corrected Frechet-Wirtinger
Riccati uniqueness input.

Compared with the derivative-identified corrected boundary, this asks directly
for actual affine `HasDerivAt` statements.  Mathlib then supplies the
corresponding `deriv` identifications.
-/
structure HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems where
  /--
  The canonical pullback formula follows from actual affine branch derivatives
  through `F''` and the remaining Laplacian calculation.
  -/
  canonicalPullbackAffineDerivative :
    HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem
  /-- The corrected metric-scaled Frechet-Wirtinger Riccati target. -/
  canonicalMetricWirtingerRiccati :
    LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem

namespace HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems

/-- Convert the affine-derivative corrected boundary to the derivative-identified one. -/
def toDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems where
  canonicalPullbackDerivIdentified :=
    hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_affineDerivative
      B.canonicalPullbackAffineDerivative
  canonicalMetricWirtingerRiccati := B.canonicalMetricWirtingerRiccati

/-- The affine-derivative corrected boundary gives two-jet metric recovery. -/
theorem recoversMetric
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.toDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundary.recoversMetric

/-- Forget to the derivative-identified corrected boundary's canonical metric package. -/
def toCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalMetricWirtingerRiccatiBoundaryTheorems :=
  B.toDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundary.toCanonicalMetricWirtingerRiccatiBoundary

end HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems

/--
Affine-derivative-algebra boundary paired with the corrected
Frechet-Wirtinger Riccati uniqueness input.

Compared with
`HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems`,
this no longer carries the Poincare Laplacian field as an input.  The
Laplacian calculation is obtained from the explicit mixed-expression
derivative proof attached to the affine derivative algebra.
-/
structure HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems where
  /--
  Actual affine branch derivative algebra for the canonical Poincare pullback.
  The Poincare Laplacian calculation is derived from this algebra.
  -/
  canonicalPullbackAffineDerivativeAlgebra :
    HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem
  /-- The corrected metric-scaled Frechet-Wirtinger Riccati target. -/
  canonicalMetricWirtingerRiccati :
    LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem

namespace HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

/-- Add the internally derived Poincare Laplacian field, retaining the older boundary shape. -/
def toAffineDerivativeCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems where
  canonicalPullbackAffineDerivative :=
    hyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem_of_affineDerivativeAlgebra
      B.canonicalPullbackAffineDerivativeAlgebra
  canonicalMetricWirtingerRiccati := B.canonicalMetricWirtingerRiccati

/-- Convert directly to the derivative-identified corrected boundary. -/
def toDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems where
  canonicalPullbackDerivIdentified :=
    hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_affineDerivativeAlgebra
      B.canonicalPullbackAffineDerivativeAlgebra
  canonicalMetricWirtingerRiccati := B.canonicalMetricWirtingerRiccati

/-- The affine-derivative-algebra corrected boundary gives two-jet metric recovery. -/
theorem recoversMetric
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.toDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundary.recoversMetric

/-- Forget to the corrected canonical metric package. -/
def toCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalMetricWirtingerRiccatiBoundaryTheorems :=
  B.toDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundary.toCanonicalMetricWirtingerRiccatiBoundary

end HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

namespace HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

/-- Convert derivative algebra to the actual affine-derivative-algebra boundary. -/
def toAffineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems where
  canonicalPullbackAffineDerivativeAlgebra :=
    hyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem_of_derivativeAlgebra
      B.canonicalPullbackDerivativeAlgebra
  canonicalMetricWirtingerRiccati := B.canonicalMetricWirtingerRiccati

end HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems

/--
Bundled version of the current strongest metric-recovery bridge.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiAnalyticBoundary
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.recoversMetric

/--
The current strongest derivative-identified and metric-scaled boundary gives
metric recovery.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentifiedCanonicalMetricRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.recoversMetric

/--
The derivative-identified pullback boundary plus corrected Frechet-Wirtinger
Riccati uniqueness gives metric recovery.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentifiedCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.recoversMetric

/--
The affine-derivative-algebra pullback boundary plus corrected
Frechet-Wirtinger Riccati uniqueness gives metric recovery, with the Poincare
Laplacian calculation supplied internally.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_affineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.recoversMetric

/--
The derivative-algebra pullback boundary plus corrected Frechet-Wirtinger
Riccati uniqueness gives metric recovery, with the Poincare Laplacian
calculation supplied internally.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivativeAlgebraCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.recoversMetric

/--
Unbundled derivative-identified pullback plus corrected
Frechet-Wirtinger-Riccati uniqueness gives metric recovery.

This exposes the two current pullback/uniqueness inputs directly, without the
intermediate boundary structure.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati
    (hPullback : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentifiedCanonicalMetricWirtingerRiccatiBoundary
    { canonicalPullbackDerivIdentified := hPullback
      canonicalMetricWirtingerRiccati := hRiccati }

/--
Metric recovery from actual affine `HasDerivAt` pullback data and the
corrected Frechet-Wirtinger Riccati theorem.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_affineDerivative_and_wirtingerRiccati
    (hAffine : HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_affineDerivative hAffine)
    hRiccati

/--
Metric recovery from actual affine derivative algebra, the geometric Poincare
Laplacian identity, and the corrected Frechet-Wirtinger Riccati theorem.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_affineDerivativeAlgebra_laplacian_wirtingerRiccati
    (hAffine : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem)
    (hLap : HyperbolicTwoJetCanonicalPullbackLaplacianTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_affineDerivativeAlgebra_and_laplacian
      hAffine hLap)
    hRiccati

/--
Metric recovery from actual affine derivative algebra and the corrected
Frechet-Wirtinger Riccati theorem.  The Poincare Laplacian calculation is
derived from the affine algebra internally.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_affineDerivativeAlgebra_and_wirtingerRiccati
    (hAffine : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_affineDerivativeAlgebra
      hAffine)
    hRiccati

/--
Metric recovery from the three separated local inputs: derivative algebra for
the normalized branch, the geometric Poincare Laplacian identity, and the
corrected Frechet-Wirtinger Riccati theorem.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivativeAlgebra_laplacian_wirtingerRiccati
    (hAlg : HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem)
    (hLap : HyperbolicTwoJetCanonicalPullbackLaplacianTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_derivativeAlgebra_and_laplacian
      hAlg hLap)
    hRiccati

/--
Metric recovery from derivative algebra for the normalized branch and the
corrected Frechet-Wirtinger Riccati theorem.  The Poincare Laplacian
calculation is derived by converting derivative algebra to affine derivative
algebra.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivativeAlgebra_and_wirtingerRiccati
    (hAlg : HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_derivativeAlgebra hAlg)
    hRiccati

/--
Metric recovery from the four separated local inputs: regularity of the
normalized branch, derivative identification for its affine branch, the
geometric Poincare Laplacian identity, and the corrected Frechet-Wirtinger
Riccati theorem.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_regularity_derivativeIdentification_laplacian_wirtingerRiccati
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hId : HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem)
    (hLap : HyperbolicTwoJetCanonicalPullbackLaplacianTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_regularity_derivativeIdentification_and_laplacian
      hReg hId hLap)
    hRiccati

/--
Metric recovery from regularity, derivative identification, and the corrected
Frechet-Wirtinger Riccati theorem.  No separate Poincare Laplacian input is
needed.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_regularity_derivativeIdentification_wirtingerRiccati
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hId : HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_regularity_derivativeIdentification
      hReg hId)
    hRiccati

/--
Metric recovery from the five separated local inputs: regularity of the
normalized branch, the three affine derivative-identification levels, the
geometric Poincare Laplacian identity, and the corrected Frechet-Wirtinger
Riccati theorem.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_regularity_first_second_third_laplacian_wirtingerRiccati
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hFirst : HyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem)
    (hSecond : HyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem)
    (hThird : HyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem)
    (hLap : HyperbolicTwoJetCanonicalPullbackLaplacianTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_regularity_first_second_third_laplacian
      hReg hFirst hSecond hThird hLap)
    hRiccati

/--
Metric recovery from regularity, the three affine derivative-identification
levels, and the corrected Frechet-Wirtinger Riccati theorem.  The Poincare
Laplacian calculation is supplied internally by the derivative-algebra route.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_regularity_first_second_third_wirtingerRiccati
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hFirst : HyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem)
    (hSecond : HyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem)
    (hThird : HyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_regularity_first_second_third
      hReg hFirst hSecond hThird)
    hRiccati

/--
The sharper hyperbolic normalization theorem target.

This theorem target records the remaining analytic input:
after solving the Schwarzian equation, one can shrink near any point and
postcompose by a Mobius transformation so that the resulting local solution is
`ℍ`-valued and recovers the original conformal metric by the Poincare
pullback formula.
-/
def HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    (D : LocalProjectiveDevelopingMap S) ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ D.domain →
      ∃ N : LocalMetricRecoveringUpperHalfPlaneNormalization D,
        z ∈ N.normalized.domain

/--
The precise 2-jet normalization theorem plus metric recovery from that 2-jet
imply the older metric-recovering normalization target.
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (hRecovery : HyperbolicTwoJetNormalizationRecoversMetricTheorem) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem := by
  intro u S D z hu hz
  rcases hJet S D hu hz with ⟨N, hNz⟩
  refine ⟨LocalMetricRecoveringUpperHalfPlaneNormalization.ofTwoJetNormalization
    N (hRecovery S N hu), ?_⟩
  exact hNz

/--
The precise 2-jet normalization theorem plus the bundled Riccati analytic
boundary give the metric-recovering normalization target.
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetRiccatiAnalyticBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
    hJet B.recoversMetric

/--
The precise 2-jet normalization theorem plus the concrete Riccati calculus
boundary give the metric-recovering normalization target.
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetRiccatiCalculusBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiCalculusBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetRiccatiAnalyticBoundary
    hJet B.toRiccatiAnalyticBoundary

/--
The precise 2-jet normalization theorem plus the canonical Riccati boundary
give the metric-recovering normalization target.
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetCanonicalRiccatiBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetRiccatiCalculusBoundary
    hJet B.toRiccatiCalculusBoundary

/--
The precise 2-jet normalization theorem plus the sharp second-expression
pullback/Riccati boundary give the metric-recovering normalization target.
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetSecondExpressionBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalPullbackSecondExpressionCanonicalRiccatiBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
    hJet B.recoversMetric

/--
The precise 2-jet normalization theorem plus the sharp third-derivative
pullback/Riccati boundary give the metric-recovering normalization target.
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetThirdDerivativeBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalPullbackThirdDerivativeCanonicalRiccatiBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
    hJet B.recoversMetric

/--
The precise 2-jet normalization theorem plus the sharp affine-derivative
pullback/Riccati boundary give the metric-recovering normalization target.
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetAffineDerivativeBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalRiccatiBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
    hJet B.recoversMetric

/--
The precise 2-jet normalization theorem plus the sharp derivative-identified
pullback/Riccati boundary give the metric-recovering normalization target.
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetDerivIdentifiedBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
    hJet B.recoversMetric

/--
The precise 2-jet normalization theorem plus the derivative-identified
pullback/corrected-Wirtinger boundary give the metric-recovering normalization
target.
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetDerivIdentifiedMetricWirtingerBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
    hJet B.recoversMetric

/--
The precise 2-jet normalization theorem plus actual affine pullback
derivatives and corrected Wirtinger-Riccati uniqueness give the
metric-recovering normalization target.
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetAffineDerivativeMetricWirtingerBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
    hJet B.recoversMetric

/--
Concrete analytic ODE existence target: around every point, the holomorphic
coefficient admits a normalized local solution pair for
`y'' + (1 / 2) q y = 0`.
-/
def HolomorphicSchwarzianLinearODELocalExistenceTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u) ⦃z : ℂ⦄,
    z ∈ u.coordinateDomain →
      ∃ (U : Set ℂ), IsOpen U ∧ z ∈ U ∧ U ⊆ u.coordinateDomain ∧
        Nonempty (NormalizedSchwarzianLinearODESolutionPair S.coefficient U z)

/--
The Frobenius-pair existence theorem implies the normalized linear ODE local
existence theorem used by the Schwarzian chart construction.
-/
theorem holomorphicSchwarzianLinearODELocalExistence_of_frobeniusPairExistence
    (h : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    HolomorphicSchwarzianLinearODELocalExistenceTheorem := by
  intro u S z hz
  rcases h S hz with ⟨a, ⟨P⟩⟩
  exact
    ⟨centeredBallDomain z P.radius,
      isOpen_centeredBallDomain z P.radius,
      mem_centeredBallDomain_center P.radius_pos,
      P.domain_subset,
      ⟨P.toNormalizedSchwarzianLinearODESolutionPair⟩⟩

/--
Local existence of normalized solution pairs implies local solvability of the
Schwarzian equation.
-/
theorem holomorphicSchwarzianLocallySolvableTheorem_of_linearODELocalExistence
    (h : HolomorphicSchwarzianLinearODELocalExistenceTheorem) :
    HolomorphicSchwarzianLocallySolvableTheorem := by
  intro u S z hz
  rcases h S hz with ⟨U, hUopen, hzU, hsub, ⟨P⟩⟩
  exact
    ⟨{ domain := U
       isOpen_domain := hUopen
       domain_subset := hsub
       frame := P.toSchwarzianLinearODEFrame },
      hzU⟩

/--
The power-series/Frobenius existence theorem directly gives local solvability
of the Schwarzian equation.
-/
theorem holomorphicSchwarzianLocallySolvableTheorem_of_frobeniusPairExistence
    (h : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    HolomorphicSchwarzianLocallySolvableTheorem :=
  holomorphicSchwarzianLocallySolvableTheorem_of_linearODELocalExistence
    (holomorphicSchwarzianLinearODELocalExistence_of_frobeniusPairExistence h)

/-- Apply the local Schwarzian ODE existence theorem to a chosen coefficient. -/
theorem localSchwarzianODEChart_of_localSolvability
    (h : HolomorphicSchwarzianLocallySolvableTheorem)
    {u : LocalConformalFactor} (S : LocalSchwarzianData u) ⦃z : ℂ⦄
    (hz : z ∈ u.coordinateDomain) :
    ∃ C : LocalSchwarzianODEChart S, z ∈ C.domain :=
  h S hz

/-- Local Schwarzian solvability gives local projective developing maps. -/
theorem holomorphicSchwarzianLocalProjectiveDevelopingMapTheorem_of_localSolvability
    (h : HolomorphicSchwarzianLocallySolvableTheorem) :
    HolomorphicSchwarzianLocalProjectiveDevelopingMapTheorem := by
  intro u S z hz
  rcases h S hz with ⟨C, hzC⟩
  exact ⟨C.toLocalProjectiveDevelopingMap, hzC⟩

/-- Frobenius-pair existence gives local projective developing maps. -/
theorem holomorphicSchwarzianLocalProjectiveDevelopingMapTheorem_of_frobeniusPairExistence
    (h : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    HolomorphicSchwarzianLocalProjectiveDevelopingMapTheorem :=
  holomorphicSchwarzianLocalProjectiveDevelopingMapTheorem_of_localSolvability
    (holomorphicSchwarzianLocallySolvableTheorem_of_frobeniusPairExistence h)

/-- Apply the local projective-developing-map theorem to a chosen coefficient. -/
theorem localProjectiveDevelopingMap_of_localSolvability
    (h : HolomorphicSchwarzianLocalProjectiveDevelopingMapTheorem)
    {u : LocalConformalFactor} (S : LocalSchwarzianData u) ⦃z : ℂ⦄
    (hz : z ∈ u.coordinateDomain) :
    ∃ D : LocalProjectiveDevelopingMap S, z ∈ D.domain :=
  h S hz

end

end JJMath
