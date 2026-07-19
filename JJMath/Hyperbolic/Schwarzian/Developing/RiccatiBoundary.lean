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
%%handwave
name:
  Uniqueness for the Liouville–Schwarzian system along paths
statement:
  Suppose that for every \(z∈Ω\), the restricted state \(X=(φ_C-φ,α):[0,1]→ℂ²\) starts at \(0\), ends at its value at \(z\), and solves a uniformly Lipschitz linear ODE. Then \(φ(z)=φ_C(z)\) throughout \(Ω\).
proof:
  ODE uniqueness compares \(X\) with the zero solution, so \(X(1)=0\); its first component is \(φ_C(z)-φ(z)\).
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_pathData
    (hPath : LocalLiouvilleSchwarzianClosedFirstOrderPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem := by
  intro u S D z₀ N C data E z hz
  rcases hPath S N C data E z hz with ⟨P⟩
  exact P.logDensity_eq

/--
%%handwave
name:
  Uniqueness for the Liouville–Schwarzian system from operator bounds along paths
statement:
  If the linear operators defining the path-restricted system have a uniform operator-norm bound and the normalized state solves that system, then \(φ(z)=φ_C(z)\) for every \(z∈Ω\).
proof:
  The operator bound makes the path vector field uniformly Lipschitz. Apply [a normalized path solution of the closed system is identically zero](lean:localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_pathData).
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_operatorBoundPathData
    (hPath : LocalLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_pathData
    (localLiouvilleSchwarzianClosedFirstOrderPathDataTheorem_of_operatorBoundPathData hPath)

/--
%%handwave
name:
  Uniqueness for the Liouville–Schwarzian system from bounded path coefficients
statement:
  If the two coefficients \(β\) and \(γ\) of the path-restricted system are uniformly bounded and the normalized state solves the system, then \(φ(z)=φ_C(z)\) throughout \(Ω\).
proof:
  The coefficient bounds give a uniform norm bound for the associated linear operators. Apply [uniform operator bounds force equality of the logarithmic densities](lean:localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_operatorBoundPathData).
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_coefficientBoundPathData
    (hPath : LocalLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_operatorBoundPathData
    (localLiouvilleSchwarzianClosedFirstOrderOperatorBoundPathDataTheorem_of_coefficientBoundPathData
      hPath)

/--
%%handwave
name:
  Uniqueness for the Liouville–Schwarzian system from continuous path coefficients
statement:
  If \(β\) and \(γ\) are continuous on \([0,1]\), extended outside that interval by clamping, and the normalized state solves the restricted system, then \(φ(z)=φ_C(z)\) throughout \(Ω\).
proof:
  Compactness of \([0,1]\) bounds both coefficients; their clamped extensions retain those bounds. Apply [bounded coefficients force equality of the logarithmic densities](lean:localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_coefficientBoundPathData).
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_continuousCoefficientPathData
    (hPath :
      LocalLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_coefficientBoundPathData
    (localLiouvilleSchwarzianClosedFirstOrderCoefficientBoundPathDataTheorem_of_continuousCoefficientPathData
      hPath)

/--
%%handwave
name:
  Uniqueness for the Liouville–Schwarzian system along straight segments
statement:
  Suppose every straight segment from \(z₀\) to \(z∈Ω\) stays in \(Ω\), the coefficients \(β,γ\) and state \((φ_C-φ,α)\) are continuous along it, and the state satisfies the restricted ODE. Then \(φ=φ_C\) on \(Ω\).
proof:
  Restrict to the segment, clamp the continuous coefficients outside \([0,1]\), and apply [continuous path coefficients force logarithmic uniqueness](lean:localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_continuousCoefficientPathData).
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentPathData
    (hPath :
      LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_continuousCoefficientPathData
    (localLiouvilleSchwarzianClosedFirstOrderContinuousCoefficientPathDataTheorem_of_affineSegmentPathData
      hPath)

/--
%%handwave
name:
  Uniqueness from analytic straight-line restrictions
statement:
  On the disk-shaped normalized domain, assume \(β,γ\) and the canonical state are continuous along straight segments and that the state satisfies the restricted ODE. Then \(φ=φ_C\) on \(Ω\).
proof:
  Convexity of the normalized disk keeps every segment inside \(Ω\). Apply [the straight-line closed system has only the zero normalized solution](lean:localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentPathData).
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentAnalyticPathData
    (hPath :
      LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentPathData
    (localLiouvilleSchwarzianClosedFirstOrderAffineSegmentPathDataTheorem_of_analyticPathData
      hPath)

/--
%%handwave
name:
  Uniqueness from the differential identities along straight segments
statement:
  On the disk-shaped normalized domain, assume \(β\) and \(γ\) are continuous and the canonical state satisfies the differential equation along every straight segment. Then \(φ=φ_C\) on \(Ω\).
proof:
  Regularity of the two conformal factors makes the state continuous along each segment. Apply [analytic straight-line restrictions give logarithmic uniqueness](lean:localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentAnalyticPathData).
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentDifferentialPathData
    (hPath :
      LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentDifferentialPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentAnalyticPathData
    (localLiouvilleSchwarzianClosedFirstOrderAffineSegmentAnalyticPathDataTheorem_of_differentialPathData
      hPath)

/--
%%handwave
name:
  Uniqueness from continuity of the potential along straight segments
statement:
  If the scalar linearized Liouville potential is continuous on the disk-shaped normalized domain, then the straight-line closed system has only the zero normalized solution, and hence \(φ=φ_C\) on \(Ω\).
proof:
  Potential continuity gives continuity of \(γ\), while \(β\) is automatically continuous; the chain rule gives the path ODE. Apply [the straight-line differential system has only the zero normalized solution](lean:localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentDifferentialPathData).
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentPotentialPathData
    (hPath :
      LocalLiouvilleSchwarzianClosedFirstOrderAffineSegmentPotentialPathDataTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentDifferentialPathData
    (localLiouvilleSchwarzianClosedFirstOrderAffineSegmentDifferentialPathDataTheorem_of_potentialPathData
      hPath)

/--
%%handwave
name:
  Uniqueness from continuity of the linearized Liouville potential
statement:
  For a closed first-order Liouville–Schwarzian system on the normalized disk, continuity of its scalar linearized potential implies \(φ(z)=φ_C(z)\) for every \(z∈Ω\).
proof:
  Use potential continuity along each affine segment and apply [continuity of the potential gives pathwise logarithmic uniqueness](lean:localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_affineSegmentPotentialPathData).
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
%%handwave
name:
  The metric-scaled Wirtinger–Riccati equation from the metric-scaled Schwarzian identity
statement:
  If the canonical complex derivatives of the original and pullback logarithmic factors satisfy the metric-scaled Schwarzian identity, then their difference \(α\) satisfies the corresponding Fréchet–Wirtinger Riccati equation on the normalized domain.
proof:
  The complex derivative is the \(z\)-component of the Fréchet derivative; retain this component and the same metric-scaled Schwarzian identity.
-/
theorem localLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem_of_metric
    (hMetric : LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusTheorem) :
    LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem := by
  intro u S D z₀ N C data
  rcases hMetric S N C data with ⟨A⟩
  exact ⟨A.toCanonicalMetricWirtingerRiccatiData⟩

/--
%%handwave
name:
  The first-order Liouville–Schwarzian system from the corrected Wirtinger–Riccati equation
statement:
  Let \(φ=φ_C-φ_u\) and \(α=∂_zφ\). The corrected Wirtinger–Riccati equation for \(∂_zα\), together with the two Liouville equations, yields a closed first-order system for \((φ,α)\) containing both the \(∂_zα\) and \(∂_{\bar z}α\) equations and the normalized zero initial values.
proof:
  Subtract the two Liouville equations to obtain the \(∂_{\bar z}α\) equation; combine it with the Riccati \(∂_zα\) equation and the normalized two-jet identities.
-/
theorem localLiouvilleSchwarzianFirstOrderSystemTheorem_of_wirtingerRiccati
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    LocalLiouvilleSchwarzianFirstOrderSystemTheorem := by
  intro u S D z₀ N C data
  rcases hWirtinger S N C data with ⟨A⟩
  exact ⟨localLiouvilleSchwarzianFirstOrderSystemData_of_wirtingerRiccati A⟩

/--
%%handwave
name:
  The scalar Liouville difference equation from the first-order Liouville–Schwarzian system
statement:
  The genuine first-order system gives the scalar elliptic difference formulation.
proof:
  Unpack the first-order system and apply its canonical conversion to the scalar difference equation.
-/
theorem localLiouvilleSchwarzianScalarDifferenceTheorem_of_firstOrderSystem
    (hSystem : LocalLiouvilleSchwarzianFirstOrderSystemTheorem) :
    LocalLiouvilleSchwarzianScalarDifferenceTheorem := by
  intro u S D z₀ N C data
  rcases hSystem S N C data with ⟨F⟩
  exact ⟨localLiouvilleSchwarzianScalarDifferenceData_of_firstOrderSystem F⟩

/--
%%handwave
name:
  The scalar Liouville difference equation from the corrected Wirtinger–Riccati equation
statement:
  The corrected Wirtinger-Riccati reduction gives the scalar elliptic difference formulation.
proof:
  Combine [the corrected Wirtinger equation yields the full first-order Liouville–Schwarzian system](lean:localLiouvilleSchwarzianFirstOrderSystemTheorem_of_wirtingerRiccati) with [the first-order system yields the scalar elliptic difference equation](lean:localLiouvilleSchwarzianScalarDifferenceTheorem_of_firstOrderSystem).
-/
theorem localLiouvilleSchwarzianScalarDifferenceTheorem_of_wirtingerRiccati
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    LocalLiouvilleSchwarzianScalarDifferenceTheorem :=
  localLiouvilleSchwarzianScalarDifferenceTheorem_of_firstOrderSystem
    (localLiouvilleSchwarzianFirstOrderSystemTheorem_of_wirtingerRiccati hWirtinger)

/--
%%handwave
name:
  Continuity of the scalar linearized potential from continuity of the divided difference of \(e^{2x}\)
statement:
  If the divided difference of \(x↦e^{2x}\) is continuous on \(ℝ²\), then the potential \(Q(z)\) obtained by evaluating it at the two logarithmic conformal factors is continuous on \(Ω\).
proof:
  Express the linearized potential through the divided difference of \(e^{2x}\) and compose its continuity with the two logarithmic densities.
-/
theorem localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_of_realExpTwoDividedDifference
    (hdiv : RealExpTwoDividedDifferenceContinuityTheorem) :
    LocalLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem := by
  intro u S D z₀ N C data E
  exact E.linearizedPotential_continuousOn_of_realExpTwoDividedDifferenceContinuous hdiv

/--
%%handwave
name:
  Continuity of the scalar linearized potential
statement:
  The divided-difference potential \(Q(z)\) associated with the two logarithmic conformal factors is continuous on the normalized domain \(Ω\).
proof:
  Apply [the scalar linearized potential is continuous on the normalized domain](lean:localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_of_realExpTwoDividedDifference).
-/
theorem localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_real :
    LocalLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem :=
  localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_of_realExpTwoDividedDifference
    realExpTwoDividedDifference_continuous

/--
%%handwave
name:
  The linearized scalar Liouville equation from the scalar Liouville difference equation
statement:
  The scalar elliptic difference formulation gives the linearized scalar difference formulation.
proof:
  Rewrite the nonlinear difference \(e^{2φ_C}-e^{2φ_u}\) as \(Q(φ_C-φ_u)\).
-/
theorem localLiouvilleSchwarzianLinearizedScalarDifferenceTheorem_of_scalarDifference
    (hScalar : LocalLiouvilleSchwarzianScalarDifferenceTheorem) :
    LocalLiouvilleSchwarzianLinearizedScalarDifferenceTheorem := by
  intro u S D z₀ N C data
  rcases hScalar S N C data with ⟨E⟩
  exact ⟨localLiouvilleSchwarzianLinearizedScalarDifferenceData_of_scalarDifference E⟩

/--
%%handwave
name:
  The linearized scalar Liouville equation from the corrected Wirtinger–Riccati equation
statement:
  The corrected Wirtinger-Riccati reduction gives the linearized scalar elliptic difference formulation.
proof:
  Combine [the Wirtinger–Riccati equation yields the scalar elliptic difference equation](lean:localLiouvilleSchwarzianScalarDifferenceTheorem_of_wirtingerRiccati) with [the scalar difference equation yields its linearized form](lean:localLiouvilleSchwarzianLinearizedScalarDifferenceTheorem_of_scalarDifference).
-/
theorem localLiouvilleSchwarzianLinearizedScalarDifferenceTheorem_of_wirtingerRiccati
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    LocalLiouvilleSchwarzianLinearizedScalarDifferenceTheorem :=
  localLiouvilleSchwarzianLinearizedScalarDifferenceTheorem_of_scalarDifference
    (localLiouvilleSchwarzianScalarDifferenceTheorem_of_wirtingerRiccati hWirtinger)

/--
%%handwave
name:
  The linear elliptic Cauchy formulation from the linearized scalar equation
statement:
  The linearized scalar elliptic formulation gives the standard linear elliptic Cauchy-data formulation.
proof:
  Combine the linearized scalar equation with its normalized value and first-derivative Cauchy values.
-/
theorem localLiouvilleSchwarzianLinearEllipticCauchyTheorem_of_linearizedScalarDifference
    (hLinear : LocalLiouvilleSchwarzianLinearizedScalarDifferenceTheorem) :
    LocalLiouvilleSchwarzianLinearEllipticCauchyTheorem := by
  intro u S D z₀ N C data
  rcases hLinear S N C data with ⟨E⟩
  exact ⟨localLiouvilleSchwarzianLinearEllipticCauchyData_of_linearizedScalarDifference E⟩

/--
%%handwave
name:
  The linear elliptic Cauchy formulation from the corrected Wirtinger–Riccati equation
statement:
  The corrected Wirtinger-Riccati reduction gives the standard linear elliptic Cauchy-data formulation.
proof:
  Combine [the Wirtinger–Riccati equation yields the linearized scalar equation](lean:localLiouvilleSchwarzianLinearizedScalarDifferenceTheorem_of_wirtingerRiccati) with [the linearized scalar equation yields the elliptic Cauchy formulation](lean:localLiouvilleSchwarzianLinearEllipticCauchyTheorem_of_linearizedScalarDifference).
-/
theorem localLiouvilleSchwarzianLinearEllipticCauchyTheorem_of_wirtingerRiccati
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    LocalLiouvilleSchwarzianLinearEllipticCauchyTheorem :=
  localLiouvilleSchwarzianLinearEllipticCauchyTheorem_of_linearizedScalarDifference
    (localLiouvilleSchwarzianLinearizedScalarDifferenceTheorem_of_wirtingerRiccati
      hWirtinger)

/--
%%handwave
name:
  The closed first-order Liouville–Schwarzian system from the linearized scalar equation
statement:
  The linearized scalar elliptic formulation gives the closed first-order linear system formulation.
proof:
  Introduce the first derivative of the scalar difference as a second unknown, turning the linearized second-order equation into a closed first-order linear system.
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
%%handwave
name:
  The closed first-order Liouville–Schwarzian system from the corrected Wirtinger–Riccati equation
statement:
  The corrected Wirtinger-Riccati reduction gives the closed first-order linear system formulation.
proof:
  Combine [the Wirtinger–Riccati equation yields the linearized scalar equation](lean:localLiouvilleSchwarzianLinearizedScalarDifferenceTheorem_of_wirtingerRiccati) with [the linearized scalar equation yields the closed first-order system](lean:localLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem_of_linearizedScalarDifference).
-/
theorem localLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem_of_wirtingerRiccati
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem :=
  localLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem_of_linearizedScalarDifference
    (localLiouvilleSchwarzianLinearizedScalarDifferenceTheorem_of_wirtingerRiccati
      hWirtinger)

/--
%%handwave
name:
  The scalar Riccati reduction from the holomorphic metric-scaled Wirtinger–Riccati equation
statement:
  If \(α=∂_zφ_C-∂_zφ_u\) satisfies the metric-scaled Wirtinger–Riccati equation and the Cauchy–Riemann condition, while its coefficient is analytic, then \(α\) satisfies the scalar holomorphic Riccati equation \(α'=αq\) with \(α(z₀)=0\).
proof:
  The Cauchy–Riemann condition identifies the Fréchet \(z\)-derivative with the complex derivative; the normalized first derivative gives \(α(z₀)=0\).
-/
theorem localLiouvilleSchwarzianRiccatiReductionTheorem_of_canonicalMetricHolomorphicRiccati
    (hHolomorphic : LocalLiouvilleSchwarzianCanonicalMetricHolomorphicRiccatiTheorem) :
    LocalLiouvilleSchwarzianRiccatiReductionTheorem := by
  intro u S D z₀ N C data
  rcases hHolomorphic S N C data with ⟨A⟩
  exact ⟨A.toRiccatiDifferenceData⟩

/--
%%handwave
name:
  Canonical Wirtinger Riccati calculus from the metric-scaled Schwarzian identity
statement:
  Equality of the metric Schwarzians \(2(u_{zz}-u_z²)=2(v_{zz}-v_z²)\) implies equality of the corresponding half-Schwarzians and hence the canonical Riccati identities.
proof:
  Cancel the common metric factor (2) in the Schwarzian identity and keep the same canonical first and second Wirtinger derivatives.
-/
theorem localLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem_of_metric
    (hMetric : LocalLiouvilleSchwarzianCanonicalMetricRiccatiCalculusTheorem) :
    LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem := by
  intro u S D z₀ N C data
  rcases hMetric S N C data with ⟨A⟩
  exact ⟨A.toCanonicalRiccatiCalculusData⟩

/--
%%handwave
name:
  Concrete Riccati calculus from canonical Wirtinger calculus
statement:
  The canonical Wirtinger derivatives of the original and pullback logarithmic factors provide first- and second-derivative fields satisfying the concrete Riccati calculus identities.
proof:
  Choose the canonical first and second Wirtinger derivatives; all derivative identities and normalized equalities are unchanged.
-/
theorem localLiouvilleSchwarzianRiccatiReductionCalculusTheorem_of_canonical
    (hCanonical : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem) :
    LocalLiouvilleSchwarzianRiccatiReductionCalculusTheorem := by
  intro u S D z₀ N C data
  rcases hCanonical S N C data with ⟨A⟩
  exact ⟨A.toCalculusData⟩

/--
%%handwave
name:
  The scalar Riccati reduction from the Schwarzian identities
statement:
  Suppose \(u\) and \(v\) have equal half-Schwarzians, with analytic first derivatives on the normalized domain and equal normalized first-order data. Then \(α=v_z-u_z\) satisfies \(α'=αq\) for \(q=v_z+u_z\), with \(α(z₀)=0\).
proof:
  Subtract the two half-Schwarzian identities: \(v_{zz}-u_{zz}=(v_z-u_z)(v_z+u_z)\). The assumed derivative identities and analyticity supply the remaining Riccati hypotheses.
-/
theorem localLiouvilleSchwarzianRiccatiReductionTheorem_of_calculus
    (hCalc : LocalLiouvilleSchwarzianRiccatiReductionCalculusTheorem) :
    LocalLiouvilleSchwarzianRiccatiReductionTheorem := by
  intro u S D z₀ N C data
  rcases hCalc S N C data with ⟨A⟩
  exact ⟨A.toRiccatiDifferenceData⟩

/--
%%handwave
name:
  The scalar Riccati reduction from canonical Wirtinger calculus
statement:
  Canonical Wirtinger derivatives satisfying the equal half-Schwarzian identity yield \(α'=αq\) for \(α=v_z-u_z\) and \(q=v_z+u_z\), with analytic \(q\) and \(α(z₀)=0\).
proof:
  Combine [canonical Wirtinger identities imply the concrete Riccati calculus identities](lean:localLiouvilleSchwarzianRiccatiReductionCalculusTheorem_of_canonical) with [the Liouville–Schwarzian difference satisfies the scalar Riccati equation](lean:localLiouvilleSchwarzianRiccatiReductionTheorem_of_calculus).
-/
theorem localLiouvilleSchwarzianRiccatiReductionTheorem_of_canonical
    (hCanonical : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem) :
    LocalLiouvilleSchwarzianRiccatiReductionTheorem :=
  localLiouvilleSchwarzianRiccatiReductionTheorem_of_calculus
    (localLiouvilleSchwarzianRiccatiReductionCalculusTheorem_of_canonical
      hCanonical)

/--
%%handwave
name:
  The scalar Riccati reduction from the metric-scaled canonical Schwarzian identity
statement:
  Canonical Wirtinger derivatives satisfying equality of the metric Schwarzians yield \(α'=αq\) for \(α=v_z-u_z\) and \(q=v_z+u_z\), with analytic \(q\) and \(α(z₀)=0\).
proof:
  Combine [the metric-scaled Schwarzian identity implies the canonical Riccati identities](lean:localLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem_of_metric) with [the Liouville–Schwarzian difference satisfies the scalar Riccati equation](lean:localLiouvilleSchwarzianRiccatiReductionTheorem_of_canonical).
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
%%handwave
name:
  Existence of a local Riccati primitive from exactness of the Riccati coefficient
statement:
  If the Riccati coefficient \(q\) is exact on the normalized domain, then there is a function \(A\) with \(A'=q\) throughout that domain.
proof:
  Choose a primitive witnessing exactness and record its pointwise derivative equation \(A'=q\).
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
%%handwave
name:
  Analyticity of the Riccati coefficient
statement:
  In particular, the Riccati coefficient \(q\) is analytic on a neighborhood of the normalized domain.
proof:
  Use the assumed neighborhood analyticity of the coefficient.
-/
theorem localRiccatiCoefficientAnalyticTheorem :
    LocalRiccatiCoefficientAnalyticTheorem := by
  intro u S D z₀ N C data R
  exact R.coefficient_analytic_on_domain

/--
%%handwave
name:
  Analyticity near the normalized disk from analyticity and a disk-shaped normalized domain
statement:
  Domain-level analyticity plus a ball-shaped normalized domain gives the disk-local analytic input. Thus the normalized domain is a disk \(B(c,r)\) and \(q\) is analytic on a neighborhood of that disk.
proof:
  Write \(\Omega=B(c,r)\), rewrite the domain, and restrict the assumed neighborhood analyticity to that ball.
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
%%handwave
name:
  Analyticity near the normalized disk from analyticity of the Riccati coefficient
statement:
  Since the normalized domain is a disk \(B(c,r)\), analyticity of \(q\) on a neighborhood of the domain is exactly analyticity on a neighborhood of that disk.
proof:
  Apply [the Riccati coefficient is analytic near the normalized disk](lean:localRiccatiCoefficientBallAnalyticTheorem_of_analytic_and_ballDomain).
-/
theorem localRiccatiCoefficientBallAnalyticTheorem_of_analytic
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalRiccatiCoefficientBallAnalyticTheorem :=
  localRiccatiCoefficientBallAnalyticTheorem_of_analytic_and_ballDomain
    hAnalytic hyperbolicTwoJetNormalizationHasBallDomainTheorem

/--
%%handwave
name:
  Analyticity of the Riccati coefficient from analyticity on a larger neighborhood
statement:
  If a coefficient is analytic on a larger set containing the normalized domain, then it is analytic on the normalized domain by the standard library monotonicity. In particular, the Riccati coefficient \(q\) is analytic on a neighborhood of the normalized domain.
proof:
  Restrict neighborhood analyticity along the inclusion \(\Omega\subseteq U\).
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
%%handwave
name:
  Holomorphicity on the normalized disk from analyticity near the normalized disk
statement:
  Analyticity on a neighborhood of a ball gives holomorphicity on that ball by the standard library. Thus the normalized domain is a disk \(B(c,r)\) and \(q\) is complex differentiable throughout \(B(c,r)\).
proof:
  Neighborhood analyticity implies complex differentiability at every point of the ball.
-/
theorem localRiccatiCoefficientBallHolomorphicTheorem_of_ballAnalytic
    (hAnalytic : LocalRiccatiCoefficientBallAnalyticTheorem) :
    LocalRiccatiCoefficientBallHolomorphicTheorem := by
  intro u S D z₀ N C data R
  rcases hAnalytic R with ⟨c, r, hdomain, hanalytic⟩
  exact ⟨c, r, hdomain, hanalytic.differentiableOn⟩

/--
%%handwave
name:
  Holomorphicity on the normalized disk from analyticity and a disk-shaped normalized domain
statement:
  Domain-level analyticity plus ball-shaped normalized domains gives the disk-local holomorphic input needed by the standard primitive theorem. Thus the normalized domain is a disk \(B(c,r)\) and \(q\) is complex differentiable throughout \(B(c,r)\).
proof:
  Combine [the Riccati coefficient is analytic near the normalized disk](lean:localRiccatiCoefficientBallAnalyticTheorem_of_analytic_and_ballDomain) with [the Riccati coefficient is holomorphic on the normalized disk](lean:localRiccatiCoefficientBallHolomorphicTheorem_of_ballAnalytic).
-/
theorem localRiccatiCoefficientBallHolomorphicTheorem_of_analytic_and_ballDomain
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem)
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem) :
    LocalRiccatiCoefficientBallHolomorphicTheorem :=
  localRiccatiCoefficientBallHolomorphicTheorem_of_ballAnalytic
    (localRiccatiCoefficientBallAnalyticTheorem_of_analytic_and_ballDomain
      hAnalytic hBallDomain)

/--
%%handwave
name:
  Holomorphicity on the normalized disk from analyticity of the Riccati coefficient
statement:
  Domain-level analyticity gives disk-local holomorphicity on the normalized disk. Thus the normalized domain is a disk \(B(c,r)\) and \(q\) is complex differentiable throughout \(B(c,r)\).
proof:
  Apply [the Riccati coefficient is holomorphic on the normalized disk](lean:localRiccatiCoefficientBallHolomorphicTheorem_of_analytic_and_ballDomain).
-/
theorem localRiccatiCoefficientBallHolomorphicTheorem_of_analytic
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalRiccatiCoefficientBallHolomorphicTheorem :=
  localRiccatiCoefficientBallHolomorphicTheorem_of_analytic_and_ballDomain
    hAnalytic hyperbolicTwoJetNormalizationHasBallDomainTheorem

/--
%%handwave
name:
  Exactness of the Riccati coefficient from holomorphicity on the normalized disk
statement:
  Holomorphicity of the Riccati coefficient on a disk gives exactness by the standard primitive theorem for disks. Equivalently, the coefficient \(q\) has a complex primitive on the normalized domain.
proof:
  Rewrite the normalized domain as a disk and apply the primitive theorem for a holomorphic function on a complex disk.
-/
theorem localRiccatiCoefficientExactnessTheorem_of_ballHolomorphic
    (hBall : LocalRiccatiCoefficientBallHolomorphicTheorem) :
    LocalRiccatiCoefficientExactnessTheorem := by
  intro u S D z₀ N C data R
  rcases hBall R with ⟨c, r, hdomain, hdiff⟩
  rw [hdomain]
  exact hdiff.isExactOn_ball

/--
%%handwave
name:
  Exactness of the Riccati coefficient from analyticity and a disk-shaped normalized domain
statement:
  Domain-level analyticity plus ball-shaped normalized domains gives exactness of the Riccati coefficient, using the standard primitive theorem for disks. Equivalently, the coefficient \(q\) has a complex primitive on the normalized domain.
proof:
  Combine [the Riccati coefficient is holomorphic on the normalized disk](lean:localRiccatiCoefficientBallHolomorphicTheorem_of_analytic_and_ballDomain) with [the Riccati coefficient is exact on the normalized domain](lean:localRiccatiCoefficientExactnessTheorem_of_ballHolomorphic).
-/
theorem localRiccatiCoefficientExactnessTheorem_of_analytic_and_ballDomain
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem)
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem) :
    LocalRiccatiCoefficientExactnessTheorem :=
  localRiccatiCoefficientExactnessTheorem_of_ballHolomorphic
    (localRiccatiCoefficientBallHolomorphicTheorem_of_analytic_and_ballDomain
      hAnalytic hBallDomain)

/--
%%handwave
name:
  Exactness of the Riccati coefficient from analyticity of the Riccati coefficient
statement:
  Domain-level analyticity gives exactness on the normalized disk. Equivalently, the coefficient \(q\) has a complex primitive on the normalized domain.
proof:
  Apply [the Riccati coefficient is exact on the normalized domain](lean:localRiccatiCoefficientExactnessTheorem_of_analytic_and_ballDomain).
-/
theorem localRiccatiCoefficientExactnessTheorem_of_analytic
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalRiccatiCoefficientExactnessTheorem :=
  localRiccatiCoefficientExactnessTheorem_of_analytic_and_ballDomain
    hAnalytic hyperbolicTwoJetNormalizationHasBallDomainTheorem

/--
%%handwave
name:
  Existence of a local Riccati primitive from holomorphicity on the normalized disk
statement:
  The disk holomorphic primitive theorem gives the local Riccati primitive existence theorem. For every Riccati coefficient \(q\) satisfying \(α'=αq\), there is a function \(A\) with \(A'=q\) on the normalized domain.
proof:
  Combine [the Riccati coefficient has a primitive on the normalized domain](lean:localRiccatiPrimitiveExistenceTheorem_of_exactness) with [the Riccati coefficient is exact on the normalized domain](lean:localRiccatiCoefficientExactnessTheorem_of_ballHolomorphic).
-/
theorem localRiccatiPrimitiveExistenceTheorem_of_ballHolomorphic
    (hBall : LocalRiccatiCoefficientBallHolomorphicTheorem) :
    LocalRiccatiPrimitiveExistenceTheorem :=
  localRiccatiPrimitiveExistenceTheorem_of_exactness
    (localRiccatiCoefficientExactnessTheorem_of_ballHolomorphic hBall)

/--
%%handwave
name:
  Existence of a local Riccati primitive from analyticity near the normalized disk
statement:
  Analyticity on a ball gives the local Riccati primitive existence theorem. For every Riccati coefficient \(q\) satisfying \(α'=αq\), there is a function \(A\) with \(A'=q\) on the normalized domain.
proof:
  Combine [the Riccati coefficient is holomorphic on the normalized disk](lean:localRiccatiCoefficientBallHolomorphicTheorem_of_ballAnalytic) with [the Riccati coefficient has a primitive on the normalized domain](lean:localRiccatiPrimitiveExistenceTheorem_of_ballHolomorphic).
-/
theorem localRiccatiPrimitiveExistenceTheorem_of_ballAnalytic
    (hAnalytic : LocalRiccatiCoefficientBallAnalyticTheorem) :
    LocalRiccatiPrimitiveExistenceTheorem :=
  localRiccatiPrimitiveExistenceTheorem_of_ballHolomorphic
    (localRiccatiCoefficientBallHolomorphicTheorem_of_ballAnalytic hAnalytic)

/--
%%handwave
name:
  Existence of a local Riccati primitive from analyticity and a disk-shaped normalized domain
statement:
  Domain-level analyticity plus ball-shaped normalized domains gives local Riccati primitive existence. For every Riccati coefficient \(q\) satisfying \(α'=αq\), there is a function \(A\) with \(A'=q\) on the normalized domain.
proof:
  Combine [the Riccati coefficient is analytic near the normalized disk](lean:localRiccatiCoefficientBallAnalyticTheorem_of_analytic_and_ballDomain) with [the Riccati coefficient has a primitive on the normalized domain](lean:localRiccatiPrimitiveExistenceTheorem_of_ballAnalytic).
-/
theorem localRiccatiPrimitiveExistenceTheorem_of_analytic_and_ballDomain
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem)
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem) :
    LocalRiccatiPrimitiveExistenceTheorem :=
  localRiccatiPrimitiveExistenceTheorem_of_ballAnalytic
    (localRiccatiCoefficientBallAnalyticTheorem_of_analytic_and_ballDomain
      hAnalytic hBallDomain)

/--
%%handwave
name:
  Existence of a local Riccati primitive from analyticity of the Riccati coefficient
statement:
  Domain-level analyticity gives local Riccati primitive existence. For every Riccati coefficient \(q\) satisfying \(α'=αq\), there is a function \(A\) with \(A'=q\) on the normalized domain.
proof:
  Apply [the Riccati coefficient has a primitive on the normalized domain](lean:localRiccatiPrimitiveExistenceTheorem_of_analytic_and_ballDomain).
-/
theorem localRiccatiPrimitiveExistenceTheorem_of_analytic
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalRiccatiPrimitiveExistenceTheorem :=
  localRiccatiPrimitiveExistenceTheorem_of_analytic_and_ballDomain
    hAnalytic hyperbolicTwoJetNormalizationHasBallDomainTheorem

/--
%%handwave
name:
  Existence of a local Riccati primitive
statement:
  Analyticity of the Riccati coefficient on the normalized disk gives a local primitive. For every Riccati coefficient \(q\) satisfying \(α'=αq\), there is a function \(A\) with \(A'=q\) on the normalized domain.
proof:
  Combine [the Riccati coefficient is analytic on the normalized domain](lean:localRiccatiCoefficientAnalyticTheorem) with [the Riccati coefficient has a primitive on the normalized domain](lean:localRiccatiPrimitiveExistenceTheorem_of_analytic).
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
%%handwave
name:
  The product-rule identity for a Riccati primitive
statement:
  If \(A'=q\) and \(\alpha'=\alpha q\), then \((\alpha e^{-A})'=0\) on the normalized domain.
proof:
  Differentiate \(\alpha e^{-A}\); substituting \(\alpha'=\alpha q\) and \(A'=q\) makes the two product-rule terms cancel.
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
%%handwave
name:
  Constancy of the Riccati integrating-factor product from the identity \((\alpha e^{-A})'=0\)
statement:
  The product-derivative-zero calculation plus the mean-value theorem gives primitive product constancy. If the normalized domain is preconnected, then \(\alpha(z)e^{-A(z)}=\alpha(z_0)e^{-A(z_0)}\) for every point in it.
proof:
  A complex-differentiable function with zero derivative on a preconnected set is constant; compare its values at \(z\) and \(z_0\).
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
%%handwave
name:
  Existence of a Riccati integrating factor from a primitive and constancy of \(\alpha e^{-A}\)
statement:
  Primitive existence plus the product-constancy calculation gives an integrating factor. For every equation \(\alpha'=\alpha q\) satisfying \(α'=αq\), there is a nowhere-zero \(\mu\) such that \(\alpha\mu\) is constant on the normalized domain.
proof:
  Choose a primitive \(A\), set \(\mu=e^{-A}\), use its nonvanishing, and apply the supplied constancy of \(\alpha e^{-A}\).
-/
theorem localRiccatiIntegratingFactorTheorem_of_primitive
    (hPrim : LocalRiccatiPrimitiveExistenceTheorem)
    (hConst : LocalRiccatiPrimitiveProductConstancyTheorem) :
    LocalRiccatiIntegratingFactorTheorem := by
  intro u S D z₀ N C data R
  rcases hPrim R with ⟨P⟩
  exact ⟨P.toIntegratingFactorData (hConst P data.domain_preconnected)⟩

/--
%%handwave
name:
  Existence of a Riccati integrating factor from a primitive and the product-rule identity
statement:
  Primitive existence plus the product-derivative-zero calculation gives an integrating factor. For every equation \(\alpha'=\alpha q\) satisfying \(α'=αq\), there is a nowhere-zero \(\mu\) such that \(\alpha\mu\) is constant on the normalized domain.
proof:
  Combine [\(\alpha e^{-A}\) is constant on the preconnected normalized domain](lean:localRiccatiPrimitiveProductConstancyTheorem_of_productDerivativeZero) with [the Riccati equation admits a nowhere-zero integrating factor](lean:localRiccatiIntegratingFactorTheorem_of_primitive).
-/
theorem localRiccatiIntegratingFactorTheorem_of_primitive_derivativeZero
    (hPrim : LocalRiccatiPrimitiveExistenceTheorem)
    (hDerivZero : LocalRiccatiPrimitiveProductDerivativeZeroTheorem) :
    LocalRiccatiIntegratingFactorTheorem :=
  localRiccatiIntegratingFactorTheorem_of_primitive hPrim
    (localRiccatiPrimitiveProductConstancyTheorem_of_productDerivativeZero hDerivZero)

/--
%%handwave
name:
  Existence of a Riccati integrating factor from existence of a primitive
statement:
  Primitive existence alone now gives an integrating factor: the product-rule calculation is proved from the equations \(α'=αq\) and \(A'=q\). For every equation \(\alpha'=\alpha q\) satisfying \(α'=αq\), there is a nowhere-zero \(\mu\) such that \(\alpha\mu\) is constant on the normalized domain.
proof:
  Combine [the derivative of \(\alpha e^{-A}\) vanishes on the normalized domain](lean:localRiccatiPrimitiveProductDerivativeZeroTheorem) with [the Riccati equation admits a nowhere-zero integrating factor](lean:localRiccatiIntegratingFactorTheorem_of_primitive_derivativeZero).
-/
theorem localRiccatiIntegratingFactorTheorem_of_primitiveExistence
    (hPrim : LocalRiccatiPrimitiveExistenceTheorem) :
    LocalRiccatiIntegratingFactorTheorem :=
  localRiccatiIntegratingFactorTheorem_of_primitive_derivativeZero hPrim
    localRiccatiPrimitiveProductDerivativeZeroTheorem

/--
%%handwave
name:
  Existence of a Riccati integrating factor from holomorphicity on the normalized disk
statement:
  Disk-local holomorphicity of the Riccati coefficient gives an integrating factor. For every equation \(\alpha'=\alpha q\) satisfying \(α'=αq\), there is a nowhere-zero \(\mu\) such that \(\alpha\mu\) is constant on the normalized domain.
proof:
  Combine [the Riccati coefficient has a primitive on the normalized domain](lean:localRiccatiPrimitiveExistenceTheorem_of_ballHolomorphic) with [the Riccati equation admits a nowhere-zero integrating factor](lean:localRiccatiIntegratingFactorTheorem_of_primitiveExistence).
-/
theorem localRiccatiIntegratingFactorTheorem_of_ballHolomorphic
    (hBall : LocalRiccatiCoefficientBallHolomorphicTheorem) :
    LocalRiccatiIntegratingFactorTheorem :=
  localRiccatiIntegratingFactorTheorem_of_primitiveExistence
    (localRiccatiPrimitiveExistenceTheorem_of_ballHolomorphic hBall)

/--
%%handwave
name:
  Existence of a Riccati integrating factor from analyticity near the normalized disk
statement:
  Disk-local analyticity of the Riccati coefficient gives an integrating factor. For every equation \(\alpha'=\alpha q\) satisfying \(α'=αq\), there is a nowhere-zero \(\mu\) such that \(\alpha\mu\) is constant on the normalized domain.
proof:
  Combine [the Riccati coefficient is holomorphic on the normalized disk](lean:localRiccatiCoefficientBallHolomorphicTheorem_of_ballAnalytic) with [the Riccati equation admits a nowhere-zero integrating factor](lean:localRiccatiIntegratingFactorTheorem_of_ballHolomorphic).
-/
theorem localRiccatiIntegratingFactorTheorem_of_ballAnalytic
    (hAnalytic : LocalRiccatiCoefficientBallAnalyticTheorem) :
    LocalRiccatiIntegratingFactorTheorem :=
  localRiccatiIntegratingFactorTheorem_of_ballHolomorphic
    (localRiccatiCoefficientBallHolomorphicTheorem_of_ballAnalytic hAnalytic)

/--
%%handwave
name:
  Existence of a Riccati integrating factor from analyticity and a disk-shaped normalized domain
statement:
  Domain-level analyticity plus ball-shaped normalized domains gives an integrating factor. For every equation \(\alpha'=\alpha q\) satisfying \(α'=αq\), there is a nowhere-zero \(\mu\) such that \(\alpha\mu\) is constant on the normalized domain.
proof:
  Combine [the Riccati coefficient is analytic near the normalized disk](lean:localRiccatiCoefficientBallAnalyticTheorem_of_analytic_and_ballDomain) with [the Riccati equation admits a nowhere-zero integrating factor](lean:localRiccatiIntegratingFactorTheorem_of_ballAnalytic).
-/
theorem localRiccatiIntegratingFactorTheorem_of_analytic_and_ballDomain
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem)
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem) :
    LocalRiccatiIntegratingFactorTheorem :=
  localRiccatiIntegratingFactorTheorem_of_ballAnalytic
    (localRiccatiCoefficientBallAnalyticTheorem_of_analytic_and_ballDomain
      hAnalytic hBallDomain)

/--
%%handwave
name:
  Existence of a Riccati integrating factor from analyticity of the Riccati coefficient
statement:
  Domain-level analyticity gives an integrating factor on the normalized disk. For every equation \(\alpha'=\alpha q\) satisfying \(α'=αq\), there is a nowhere-zero \(\mu\) such that \(\alpha\mu\) is constant on the normalized domain.
proof:
  Apply [the Riccati equation admits a nowhere-zero integrating factor](lean:localRiccatiIntegratingFactorTheorem_of_analytic_and_ballDomain).
-/
theorem localRiccatiIntegratingFactorTheorem_of_analytic
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalRiccatiIntegratingFactorTheorem :=
  localRiccatiIntegratingFactorTheorem_of_analytic_and_ballDomain
    hAnalytic hyperbolicTwoJetNormalizationHasBallDomainTheorem

/--
%%handwave
name:
  Existence of a Riccati integrating factor
statement:
  Analyticity of the Riccati coefficient gives a primitive and hence an integrating factor. For every equation \(\alpha'=\alpha q\) satisfying \(α'=αq\), there is a nowhere-zero \(\mu\) such that \(\alpha\mu\) is constant on the normalized domain.
proof:
  Combine [the Riccati coefficient has a primitive on the normalized domain](lean:localRiccatiPrimitiveExistenceTheorem) with [the Riccati equation admits a nowhere-zero integrating factor](lean:localRiccatiIntegratingFactorTheorem_of_primitiveExistence).
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
%%handwave
name:
  Uniqueness for the scalar Riccati equation from an integrating factor
statement:
  An integrating factor gives the zero-solution uniqueness theorem for the Riccati difference equation. If \(\partial_z\alpha=\alpha q\) on the preconnected normalized domain and \(\alpha(z_0)=0\), then \(\alpha(z)=0\) throughout that domain.
proof:
  Constancy gives \(\alpha(z)\mu(z)=\alpha(z_0)\mu(z_0)=0\); since \(\mu(z)\ne0\), cancel it.
-/
theorem localRiccatiZeroUniquenessTheorem_of_integratingFactor
    (hIF : LocalRiccatiIntegratingFactorTheorem) :
    LocalRiccatiZeroUniquenessTheorem := by
  intro u S D z₀ N C data R _hPreconnected z hz
  rcases hIF R with ⟨M⟩
  exact M.alpha_eq_zero z hz

/--
%%handwave
name:
  Uniqueness for the scalar Riccati equation from analyticity and a disk-shaped normalized domain
statement:
  Domain-level analyticity of the Riccati coefficient on ball-shaped normalized domains gives zero-solution uniqueness for the Riccati equation. If \(\partial_z\alpha=\alpha q\) on the preconnected normalized domain and \(\alpha(z_0)=0\), then \(\alpha(z)=0\) throughout that domain.
proof:
  Combine [the Riccati equation admits a nowhere-zero integrating factor](lean:localRiccatiIntegratingFactorTheorem_of_analytic_and_ballDomain) with [a normalized Riccati solution with zero initial value vanishes on the domain](lean:localRiccatiZeroUniquenessTheorem_of_integratingFactor).
-/
theorem localRiccatiZeroUniquenessTheorem_of_analytic_and_ballDomain
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem)
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem) :
    LocalRiccatiZeroUniquenessTheorem :=
  localRiccatiZeroUniquenessTheorem_of_integratingFactor
    (localRiccatiIntegratingFactorTheorem_of_analytic_and_ballDomain
      hAnalytic hBallDomain)

/--
%%handwave
name:
  Uniqueness for the scalar Riccati equation from analyticity of the Riccati coefficient
statement:
  Domain-level analyticity gives zero-solution uniqueness for the Riccati equation. If \(\partial_z\alpha=\alpha q\) on the preconnected normalized domain and \(\alpha(z_0)=0\), then \(\alpha(z)=0\) throughout that domain.
proof:
  Apply [a normalized Riccati solution with zero initial value vanishes on the domain](lean:localRiccatiZeroUniquenessTheorem_of_analytic_and_ballDomain).
-/
theorem localRiccatiZeroUniquenessTheorem_of_analytic
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalRiccatiZeroUniquenessTheorem :=
  localRiccatiZeroUniquenessTheorem_of_analytic_and_ballDomain
    hAnalytic hyperbolicTwoJetNormalizationHasBallDomainTheorem

/--
%%handwave
name:
  Uniqueness for the scalar Riccati equation
statement:
  If \(\partial_z\alpha=\alpha q\) on the preconnected normalized domain and \(\alpha(z_0)=0\), then \(\alpha(z)=0\) throughout that domain.
proof:
  Combine [the Riccati equation admits a nowhere-zero integrating factor](lean:localRiccatiIntegratingFactorTheorem) with [a normalized Riccati solution with zero initial value vanishes on the domain](lean:localRiccatiZeroUniquenessTheorem_of_integratingFactor).
-/
theorem localRiccatiZeroUniquenessTheorem :
    LocalRiccatiZeroUniquenessTheorem :=
  localRiccatiZeroUniquenessTheorem_of_integratingFactor
    localRiccatiIntegratingFactorTheorem

/--
%%handwave
name:
  Uniqueness for the Wirtinger–Riccati equation from the holomorphic metric-scaled Wirtinger–Riccati equation
statement:
  The holomorphic Wirtinger–Riccati equation reduces to a scalar complex ODE. For every \(z\in\Omega\), the first-derivative difference \(\alpha=\partial_z\phi_C-\partial_z\phi\) therefore satisfies \(\alpha(z)=0\).
proof:
  Convert the holomorphic Fréchet–Wirtinger equation to the scalar Riccati equation and apply zero-solution uniqueness on the preconnected domain.
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
%%handwave
name:
  Uniqueness for the Wirtinger–Riccati equation from continuity of the scalar linearized potential
statement:
  The corrected Fréchet–Wirtinger Riccati equation gives zero-uniqueness directly through the closed first-order path argument and scalar divided-difference potential continuity. For every \(z\in\Omega\), the first-derivative difference \(\alpha=\partial_z\phi_C-\partial_z\phi\) therefore satisfies \(\alpha(z)=0\).
proof:
  Pass from the first-order system to the scalar difference and its closed linear system; continuity of the potential makes the normalized state solve the straight-segment ODE, whose uniqueness conclusion is \(\alpha=0\).
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
%%handwave
name:
  Uniqueness for the Wirtinger–Riccati equation from continuity of the divided difference of \(e^{2x}\)
statement:
  The pure real divided-difference continuity lemma discharges the scalar potential-continuity input for corrected Wirtinger-Riccati zero-uniqueness. For every \(z\in\Omega\), the first-derivative difference \(\alpha=\partial_z\phi_C-\partial_z\phi\) therefore satisfies \(\alpha(z)=0\).
proof:
  Combine [the scalar linearized potential is continuous on the normalized domain](lean:localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_of_realExpTwoDividedDifference) with [a normalized Riccati solution with zero initial value vanishes on the domain](lean:localWirtingerRiccatiZeroUniquenessTheorem_of_scalarPotentialContinuity).
-/
theorem localWirtingerRiccatiZeroUniquenessTheorem_of_realExpTwoDividedDifference
    (hdiv : RealExpTwoDividedDifferenceContinuityTheorem) :
    LocalWirtingerRiccatiZeroUniquenessTheorem :=
  localWirtingerRiccatiZeroUniquenessTheorem_of_scalarPotentialContinuity
    (localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_of_realExpTwoDividedDifference
      hdiv)

/--
%%handwave
name:
  Uniqueness for the Wirtinger–Riccati equation
statement:
  Corrected Fréchet-Wirtinger Riccati zero-uniqueness is now proved from the pathwise closed first-order system and the real divided-difference continuity lemma. For every \(z\in\Omega\), the first-derivative difference \(\alpha=\partial_z\phi_C-\partial_z\phi\) therefore satisfies \(\alpha(z)=0\).
proof:
  Combine [the scalar linearized potential is continuous on the normalized domain](lean:localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_real) with [a normalized Riccati solution with zero initial value vanishes on the domain](lean:localWirtingerRiccatiZeroUniquenessTheorem_of_scalarPotentialContinuity).
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
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from Riccati
statement:
  The Riccati reduction plus zero-solution uniqueness proves logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Choose the Riccati reduction, use zero-solution uniqueness to obtain \(\alpha=0\), and invoke the fact that a vanishing first-derivative difference and the normalized base value force equality of logarithmic densities.
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
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from an integrating factor
statement:
  The Riccati reduction plus integrating-factor existence proves logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [a normalized Riccati solution with zero initial value vanishes on the domain](lean:localRiccatiZeroUniquenessTheorem_of_integratingFactor) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_riccati).
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_integratingFactor
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hIF : LocalRiccatiIntegratingFactorTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccati
    hReduce (localRiccatiZeroUniquenessTheorem_of_integratingFactor hIF)

/--
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the Riccati reduction, analyticity, and a disk-shaped domain
statement:
  Riccati reduction plus domain-level analytic coefficients on ball-shaped normalized domains gives logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [a normalized Riccati solution with zero initial value vanishes on the domain](lean:localRiccatiZeroUniquenessTheorem_of_analytic_and_ballDomain) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_riccati).
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
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the Riccati reduction and analyticity
statement:
  Riccati reduction plus domain-level analytic coefficients gives logarithmic Liouville-Schwarzian uniqueness; the normalized domain is a disk. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [a normalized Riccati solution with zero initial value vanishes on the domain](lean:localRiccatiZeroUniquenessTheorem_of_analytic) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_riccati).
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiAnalytic
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccati
    hReduce (localRiccatiZeroUniquenessTheorem_of_analytic hAnalytic)

/--
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the scalar Riccati reduction
statement:
  Once the logarithmic difference satisfies \(α'=αq\) with analytic \(q\) and \(α(z₀)=0\), scalar Riccati uniqueness applies. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [a normalized Riccati solution with zero initial value vanishes on the domain](lean:localRiccatiZeroUniquenessTheorem) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_riccati).
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiReduction
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccati
    hReduce localRiccatiZeroUniquenessTheorem

/--
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the concrete Riccati calculus identities
statement:
  The concrete Riccati calculus identities give logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [the Liouville–Schwarzian difference satisfies the scalar Riccati equation](lean:localLiouvilleSchwarzianRiccatiReductionTheorem_of_calculus) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiReduction).
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiCalculus
    (hCalc : LocalLiouvilleSchwarzianRiccatiReductionCalculusTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiReduction
    (localLiouvilleSchwarzianRiccatiReductionTheorem_of_calculus hCalc)

/--
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from canonical Wirtinger calculus
statement:
  Canonical Fréchet–Wirtinger Riccati identities give logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [canonical Wirtinger identities imply the concrete Riccati calculus identities](lean:localLiouvilleSchwarzianRiccatiReductionCalculusTheorem_of_canonical) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiCalculus).
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_canonicalRiccatiCalculus
    (hCanonical : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiCalculus
    (localLiouvilleSchwarzianRiccatiReductionCalculusTheorem_of_canonical
      hCanonical)

/--
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from canonical metric Wirtinger Riccati
statement:
  The corrected Wirtinger-Riccati reduction plus its zero-uniqueness theorem give log-density uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Apply the assumed zero-uniqueness to the canonical derivative difference, then integrate the vanishing first-derivative difference using the normalized base value.
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
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the holomorphic metric-scaled Wirtinger–Riccati equation
statement:
  The holomorphic Wirtinger–Riccati equation gives logarithmic Liouville-Schwarzian uniqueness through the already-proved scalar Riccati machinery. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [the Liouville–Schwarzian difference satisfies the scalar Riccati equation](lean:localLiouvilleSchwarzianRiccatiReductionTheorem_of_canonicalMetricHolomorphicRiccati) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiReduction).
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_canonicalMetricHolomorphicRiccati
    (hHolomorphic : LocalLiouvilleSchwarzianCanonicalMetricHolomorphicRiccatiTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiReduction
    (localLiouvilleSchwarzianRiccatiReductionTheorem_of_canonicalMetricHolomorphicRiccati
      hHolomorphic)

/--
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the first-order Liouville–Schwarzian system
statement:
  The genuine first-order system plus its local uniqueness theorem gives logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Choose the stated local solution and apply the corresponding uniqueness hypothesis at \(z\in\Omega\).
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_firstOrderSystem
    (hSystem : LocalLiouvilleSchwarzianFirstOrderSystemTheorem)
    (hUnique : LocalLiouvilleSchwarzianFirstOrderSystemUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem := by
  intro u S D z₀ N C data z hz
  rcases hSystem S N C data with ⟨F⟩
  exact hUnique S N C data F z hz

/--
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the Wirtinger–Riccati reduction and first-order uniqueness
statement:
  The corrected Wirtinger-Riccati reduction plus the genuine first-order uniqueness theorem gives logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [the corrected Wirtinger equation yields the full first-order Liouville–Schwarzian system](lean:localLiouvilleSchwarzianFirstOrderSystemTheorem_of_wirtingerRiccati) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_firstOrderSystem).
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_firstOrderUnique
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hUnique : LocalLiouvilleSchwarzianFirstOrderSystemUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_firstOrderSystem
    (localLiouvilleSchwarzianFirstOrderSystemTheorem_of_wirtingerRiccati hWirtinger)
    hUnique

/--
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the scalar Liouville difference equation
statement:
  The scalar elliptic difference formulation plus its local uniqueness theorem gives logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Choose the stated local solution and apply the corresponding uniqueness hypothesis at \(z\in\Omega\).
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_scalarDifference
    (hScalar : LocalLiouvilleSchwarzianScalarDifferenceTheorem)
    (hUnique : LocalLiouvilleSchwarzianScalarDifferenceUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem := by
  intro u S D z₀ N C data z hz
  rcases hScalar S N C data with ⟨E⟩
  exact hUnique S N C data E z hz

/--
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the Wirtinger–Riccati reduction and uniqueness of the scalar equation
statement:
  The corrected Wirtinger-Riccati reduction plus scalar-difference uniqueness gives logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [the first-order system yields the scalar elliptic difference equation](lean:localLiouvilleSchwarzianScalarDifferenceTheorem_of_wirtingerRiccati) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_scalarDifference).
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_scalarDifferenceUnique
    (hWirtinger : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem)
    (hUnique : LocalLiouvilleSchwarzianScalarDifferenceUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_scalarDifference
    (localLiouvilleSchwarzianScalarDifferenceTheorem_of_wirtingerRiccati hWirtinger)
    hUnique

/--
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the linearized scalar equation
statement:
  The linearized scalar elliptic difference formulation plus its local uniqueness theorem gives logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Choose the stated local solution and apply the corresponding uniqueness hypothesis at \(z\in\Omega\).
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_linearizedScalarDifference
    (hLinear : LocalLiouvilleSchwarzianLinearizedScalarDifferenceTheorem)
    (hUnique : LocalLiouvilleSchwarzianLinearizedScalarDifferenceUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem := by
  intro u S D z₀ N C data z hz
  rcases hLinear S N C data with ⟨E⟩
  exact hUnique S N C data E z hz

/--
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the Wirtinger–Riccati reduction and uniqueness of the linearized scalar equation
statement:
  The corrected Wirtinger-Riccati reduction plus linearized scalar-difference uniqueness gives logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [the first-order system yields the scalar elliptic difference equation](lean:localLiouvilleSchwarzianLinearizedScalarDifferenceTheorem_of_wirtingerRiccati) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_linearizedScalarDifference).
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
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the linear elliptic Cauchy problem
statement:
  The standard linear elliptic Cauchy-data formulation plus its local uniqueness theorem gives logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Choose the stated local solution and apply the corresponding uniqueness hypothesis at \(z\in\Omega\).
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_linearEllipticCauchy
    (hCauchy : LocalLiouvilleSchwarzianLinearEllipticCauchyTheorem)
    (hUnique : LocalLiouvilleSchwarzianLinearEllipticCauchyUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem := by
  intro u S D z₀ N C data z hz
  rcases hCauchy S N C data with ⟨E⟩
  exact hUnique S N C data E z hz

/--
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the Wirtinger–Riccati reduction and elliptic Cauchy uniqueness
statement:
  The corrected Wirtinger-Riccati reduction plus standard linear elliptic Cauchy uniqueness gives logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [the linearized scalar equation yields the elliptic Cauchy formulation](lean:localLiouvilleSchwarzianLinearEllipticCauchyTheorem_of_wirtingerRiccati) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_linearEllipticCauchy).
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
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the closed first-order linear system
statement:
  The closed first-order linear system formulation plus its pathwise uniqueness theorem gives logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Choose the stated local solution and apply the corresponding uniqueness hypothesis at \(z\in\Omega\).
-/
theorem localLiouvilleSchwarzianLogUniquenessTheorem_of_closedFirstOrderLinearSystem
    (hSystem : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem)
    (hUnique : LocalLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem := by
  intro u S D z₀ N C data z hz
  rcases hSystem S N C data with ⟨E⟩
  exact hUnique S N C data E z hz

/--
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the Wirtinger–Riccati reduction and pathwise first-order uniqueness
statement:
  The corrected Wirtinger-Riccati reduction plus closed first-order linear system uniqueness gives logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [the Wirtinger–Riccati equation yields the closed first-order system](lean:localLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem_of_wirtingerRiccati) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_closedFirstOrderLinearSystem).
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
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from closed first order linear system potential continuity
statement:
  The closed first-order linear system plus continuity of its scalar linearized potential gives logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [pathwise uniqueness gives equality of the logarithmic densities on the normalized domain](lean:localLiouvilleSchwarzianClosedFirstOrderLinearSystemUniquenessTheorem_of_potentialContinuity) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_closedFirstOrderLinearSystem).
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
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the Wirtinger–Riccati equation and continuity of the closed-system potential
statement:
  The corrected Wirtinger-Riccati reduction plus scalar-potential continuity gives logarithmic Liouville-Schwarzian uniqueness through the closed first-order linear system. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [the Wirtinger–Riccati equation yields the closed first-order system](lean:localLiouvilleSchwarzianClosedFirstOrderLinearSystemTheorem_of_wirtingerRiccati) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_closedFirstOrderLinearSystem_potentialContinuity).
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
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the Wirtinger–Riccati equation and continuity of the scalar potential
statement:
  The corrected Wirtinger-Riccati reduction plus continuity of the concrete scalar divided-difference potential gives logarithmic Liouville-Schwarzian uniqueness. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Convert the Wirtinger equation successively to the scalar and closed linear formulations; continuity makes the normalized state solve the straight-segment ODE, whose uniqueness conclusion is equality of logarithmic densities.
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
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the Wirtinger–Riccati equation and continuity of the exponential divided difference
statement:
  The corrected Wirtinger-Riccati reduction plus the pure real divided-difference continuity lemma gives logarithmic Liouville-Schwarzian uniqueness through the concrete scalar potential. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [the scalar linearized potential is continuous on the normalized domain](lean:localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_of_realExpTwoDividedDifference) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_scalarPotentialContinuity).
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
%%handwave
name:
  Logarithmic Liouville–Schwarzian uniqueness from the corrected Wirtinger–Riccati equation
statement:
  The corrected Wirtinger–Riccati equation gives logarithmic Liouville-Schwarzian uniqueness via the proved scalar divided-difference continuity lemma. Precisely, for every normalized branch, compatible pullback candidate, and \(z\in\Omega\), one has \(\phi(z)=\phi_C(z)\).
proof:
  Combine [the scalar linearized potential is continuous on the normalized domain](lean:localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_real) with [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_scalarPotentialContinuity).
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
%%handwave
name:
  Liouville–Schwarzian uniqueness from logarithmic uniqueness
statement:
  Logarithmic uniqueness implies the squared-density uniqueness statement used by the metric-recovery bridge. Precisely, on the normalized domain \(\Omega\), the squared densities agree: \(\rho_u(z)^2=\rho_C(z)^2\).
proof:
  Apply logarithmic uniqueness and exponentiate twice to turn \(\phi=\phi_C\) into equality of squared densities.
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
%%handwave
name:
  Liouville–Schwarzian uniqueness from the Riccati reduction, analyticity, and a disk-shaped domain
statement:
  Riccati reduction plus domain-level analytic coefficients on ball-shaped normalized domains gives the squared-density Liouville-Schwarzian uniqueness statement. Precisely, on the normalized domain \(\Omega\), the squared densities agree: \(\rho_u(z)^2=\rho_C(z)^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiAnalyticAndBallDomain) with [the original and pullback squared densities agree on the normalized domain](lean:localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness).
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
%%handwave
name:
  Liouville–Schwarzian uniqueness from the Riccati reduction and analyticity
statement:
  Riccati reduction plus domain-level analytic coefficients gives squared-density Liouville-Schwarzian uniqueness. Precisely, on the normalized domain \(\Omega\), the squared densities agree: \(\rho_u(z)^2=\rho_C(z)^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiAnalytic) with [the original and pullback squared densities agree on the normalized domain](lean:localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness).
-/
theorem localLiouvilleSchwarzianUniquenessTheorem_of_riccatiAnalytic
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem)
    (hAnalytic : LocalRiccatiCoefficientAnalyticTheorem) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiAnalytic
      hReduce hAnalytic)

/--
%%handwave
name:
  Liouville–Schwarzian uniqueness from the scalar Riccati reduction
statement:
  For \(α'=αq\) with analytic \(q\) and \(α(z₀)=0\), a local primitive produces an integrating factor and forces \(α=0\). Precisely, on the normalized domain \(\Omega\), the squared densities agree: \(\rho_u(z)^2=\rho_C(z)^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiReduction) with [the original and pullback squared densities agree on the normalized domain](lean:localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness).
-/
theorem localLiouvilleSchwarzianUniquenessTheorem_of_riccatiReduction
    (hReduce : LocalLiouvilleSchwarzianRiccatiReductionTheorem) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiReduction hReduce)

/--
%%handwave
name:
  Liouville–Schwarzian uniqueness from the concrete Riccati calculus identities
statement:
  The concrete Riccati calculus identities give squared-density Liouville-Schwarzian uniqueness. Precisely, on the normalized domain \(\Omega\), the squared densities agree: \(\rho_u(z)^2=\rho_C(z)^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiCalculus) with [the original and pullback squared densities agree on the normalized domain](lean:localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness).
-/
theorem localLiouvilleSchwarzianUniquenessTheorem_of_riccatiCalculus
    (hCalc : LocalLiouvilleSchwarzianRiccatiReductionCalculusTheorem) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiCalculus hCalc)

/--
%%handwave
name:
  Liouville–Schwarzian uniqueness from canonical Wirtinger calculus
statement:
  Canonical Fréchet–Wirtinger Riccati identities give squared-density Liouville-Schwarzian uniqueness. Precisely, on the normalized domain \(\Omega\), the squared densities agree: \(\rho_u(z)^2=\rho_C(z)^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_canonicalRiccatiCalculus) with [the original and pullback squared densities agree on the normalized domain](lean:localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness).
-/
theorem localLiouvilleSchwarzianUniquenessTheorem_of_canonicalRiccatiCalculus
    (hCanonical : LocalLiouvilleSchwarzianCanonicalRiccatiCalculusTheorem) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness
    (localLiouvilleSchwarzianLogUniquenessTheorem_of_canonicalRiccatiCalculus
      hCanonical)

/--
%%handwave
name:
  Liouville–Schwarzian uniqueness from the Wirtinger–Riccati equation and continuity of the scalar potential
statement:
  The corrected Wirtinger–Riccati equation plus continuity of the concrete scalar linearized potential give squared-density Liouville-Schwarzian uniqueness. Precisely, on the normalized domain \(\Omega\), the squared densities agree: \(\rho_u(z)^2=\rho_C(z)^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_scalarPotentialContinuity) with [the original and pullback squared densities agree on the normalized domain](lean:localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness).
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
%%handwave
name:
  Liouville–Schwarzian uniqueness from the Wirtinger–Riccati equation and continuity of the exponential divided difference
statement:
  The corrected Wirtinger–Riccati equation plus the pure real divided-difference continuity lemma give squared-density Liouville-Schwarzian uniqueness. Precisely, on the normalized domain \(\Omega\), the squared densities agree: \(\rho_u(z)^2=\rho_C(z)^2\).
proof:
  Combine [the scalar linearized potential is continuous on the normalized domain](lean:localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_of_realExpTwoDividedDifference) with [the original and pullback squared densities agree on the normalized domain](lean:localLiouvilleSchwarzianUniquenessTheorem_of_wirtingerRiccati_scalarPotentialContinuity).
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
%%handwave
name:
  Liouville–Schwarzian uniqueness from the corrected Wirtinger–Riccati equation
statement:
  The corrected Wirtinger–Riccati equation gives squared-density Liouville-Schwarzian uniqueness via the proved scalar divided-difference continuity lemma. Precisely, on the normalized domain \(\Omega\), the squared densities agree: \(\rho_u(z)^2=\rho_C(z)^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati) with [the original and pullback squared densities agree on the normalized domain](lean:localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness).
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
  Let \(F:V→ℍ\) solve the metric Schwarzian equation for a hyperbolic logarithmic conformal factor \(u\), with normalized two-jet \(F(z₀)=i\), \(F'(z₀)=e^{u(z₀)}\), and \(F''(z₀)=F'(z₀)(2u_z(z₀)-iF'(z₀))\). If its Poincaré pullback logarithmic factor \(v=\log |F'|-\log \operatorname{Im} F\) solves the same Liouville–Schwarzian system as \(u\) on a preconnected domain and that system is locally unique, then \(e^{2u}=|F'|²/(\operatorname{Im} F)²\) throughout \(V\).
proof:
  The normalized two-jet gives \(v(z₀)=u(z₀)\) and \(v_z(z₀)=u_z(z₀)\). Local Liouville–Schwarzian uniqueness gives \(v=u\), and exponentiating twice yields the Poincaré pullback formula.
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
%%handwave
name:
  Metric recovery from logarithmic Liouville–Schwarzian uniqueness
statement:
  The pullback calculation, preconnected shrinking, and logarithmic Liouville-Schwarzian uniqueness give metric recovery. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the original and pullback squared densities agree on the normalized domain](lean:localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_liouvilleUniqueness).
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
%%handwave
name:
  Metric recovery from the Wirtinger–Riccati equation and continuity of the scalar potential
statement:
  The concrete scalar-potential route gives metric recovery from the hyperbolic two-jet normalization. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_scalarPotentialContinuity) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness).
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
%%handwave
name:
  Metric recovery from the Wirtinger–Riccati equation and continuity of the exponential divided difference
statement:
  The pure real divided-difference continuity lemma gives the scalar-potential metric-recovery route. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the scalar linearized potential is continuous on the normalized domain](lean:localLiouvilleSchwarzianScalarDifferencePotentialContinuityTheorem_of_realExpTwoDividedDifference) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_wirtingerRiccati_scalarPotentialContinuity).
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
%%handwave
name:
  Metric recovery from the corrected Wirtinger–Riccati equation
statement:
  The corrected Wirtinger–Riccati equation gives metric recovery from the hyperbolic two-jet normalization via the proved scalar divided-difference continuity lemma. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness).
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
%%handwave
name:
  Metric recovery for metric Schwarzian data from the canonical Poincaré pullback formula
statement:
  The canonical Poincaré pullback formula proves metric recovery for metric Schwarzian data without an external corrected-Riccati theorem. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Instantiate the canonical pullback formula with the original metric Schwarzian and use its identification with the original metric Schwarzian.
-/
theorem hyperbolicTwoJetMetricSchwarzianNormalizationRecoversMetricTheorem_of_canonicalPullbackLiouvilleFormula
    (hPullback : HyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem) :
    HyperbolicTwoJetMetricSchwarzianNormalizationRecoversMetricTheorem := by
  intro u M D z₀ N hu z hz
  rcases hPullback M.toLocalSchwarzianData N hu with ⟨P⟩
  exact P.densitySq_eq_original_of_originalMetricSchwarzian
    hu M.originalMetricIdentification z hz

/--
%%handwave
name:
  Metric recovery for metric Schwarzian data from the pullback derivative identities
statement:
  For the original metric Schwarzian, derivative algebra for the normalized branch directly gives metric recovery. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Use the derivative identities and apply its original-metric Schwarzian recovery formula.
-/
theorem hyperbolicTwoJetMetricSchwarzianNormalizationRecoversMetricTheorem_of_derivativeAlgebra
    (hAlg : HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem) :
    HyperbolicTwoJetMetricSchwarzianNormalizationRecoversMetricTheorem := by
  intro u M D z₀ N hu z hz
  rcases hAlg M.toLocalSchwarzianData N hu with ⟨A⟩
  exact A.metric_recovery_of_originalMetricSchwarzian
    hu M.originalMetricIdentification z hz

/--
%%handwave
name:
  Metric recovery from uniqueness for the scalar Riccati equation
statement:
  The Riccati uniqueness route gives metric recovery from the hyperbolic two-jet normalization. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_riccati) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness).
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
%%handwave
name:
  Metric recovery from an integrating factor
statement:
  The integrating-factor route gives metric recovery from the hyperbolic two-jet normalization. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_integratingFactor) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness).
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
%%handwave
name:
  Metric recovery from a Riccati primitive and constancy of \(\alpha e^{-A}\)
statement:
  The primitive/integrating-factor route gives metric recovery from the hyperbolic two-jet normalization. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the Riccati equation admits a nowhere-zero integrating factor](lean:localRiccatiIntegratingFactorTheorem_of_primitive) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_integratingFactor).
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
%%handwave
name:
  Metric recovery from a Riccati primitive and the product-rule identity
statement:
  Primitive existence plus the derivative-zero product-rule calculation give metric recovery from the hyperbolic two-jet normalization. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the Riccati equation admits a nowhere-zero integrating factor](lean:localRiccatiIntegratingFactorTheorem_of_primitive_derivativeZero) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_integratingFactor).
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
%%handwave
name:
  Metric recovery from existence of a Riccati primitive
statement:
  Primitive existence alone gives metric recovery from the hyperbolic two-jet normalization, since the product-rule calculation is now proved by the standard library calculus. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the Riccati equation admits a nowhere-zero integrating factor](lean:localRiccatiIntegratingFactorTheorem_of_primitiveExistence) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_integratingFactor).
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
%%handwave
name:
  Metric recovery from holomorphicity on the normalized disk
statement:
  Disk-local holomorphicity of the Riccati coefficient gives metric recovery from the hyperbolic two-jet normalization. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the Riccati equation admits a nowhere-zero integrating factor](lean:localRiccatiIntegratingFactorTheorem_of_ballHolomorphic) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_integratingFactor).
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
%%handwave
name:
  Metric recovery from analyticity near the normalized disk
statement:
  Analyticity of the Riccati coefficient on ball-shaped normalized domains gives metric recovery from the hyperbolic two-jet normalization. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the Riccati equation admits a nowhere-zero integrating factor](lean:localRiccatiIntegratingFactorTheorem_of_ballAnalytic) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_integratingFactor).
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
%%handwave
name:
  Metric recovery from analyticity and a disk-shaped normalized domain
statement:
  Ball-shaped normalized domains and analytic Riccati coefficients give metric recovery, with preconnectedness supplied by the standard connectedness of balls. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Apply [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiBallAnalytic).
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
%%handwave
name:
  Metric recovery from the Riccati reduction, analyticity, and a disk-shaped domain
statement:
  Domain-level analytic Riccati coefficients and ball-shaped normalized domains give metric recovery. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the Riccati coefficient is analytic near the normalized disk](lean:localRiccatiCoefficientBallAnalyticTheorem_of_analytic_and_ballDomain) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiBallAnalyticAndBallDomain).
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
%%handwave
name:
  Metric recovery from the Riccati reduction and analyticity
statement:
  Domain-level analytic Riccati coefficients give metric recovery; ball domains and preconnectedness are supplied by the two-jet normalization. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Apply [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiAnalyticAndBallDomain).
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
%%handwave
name:
  Metric recovery from the scalar Riccati reduction
statement:
  The Poincaré pullback Liouville formula and the scalar Riccati equation imply \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\) for every \(z\in\Omega\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiReduction) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness).
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
%%handwave
name:
  Metric recovery from the concrete Riccati calculus identities
statement:
  The metric-recovery bridge expressed in terms of the concrete Riccati calculus identities. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the Liouville–Schwarzian difference satisfies the scalar Riccati equation](lean:localLiouvilleSchwarzianRiccatiReductionTheorem_of_calculus) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiReduction).
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiCalculus
    (hPullback : HyperbolicTwoJetPullbackLiouvilleCandidateTheorem)
    (hCalc : LocalLiouvilleSchwarzianRiccatiReductionCalculusTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiReduction
    hPullback
    (localLiouvilleSchwarzianRiccatiReductionTheorem_of_calculus hCalc)

/--
%%handwave
name:
  Metric recovery from canonical Wirtinger calculus
statement:
  The metric-recovery bridge expressed in terms of canonical Fréchet–Wirtinger Riccati identities. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [canonical Wirtinger identities imply the concrete Riccati calculus identities](lean:localLiouvilleSchwarzianRiccatiReductionCalculusTheorem_of_canonical) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiCalculus).
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
%%handwave
name:
  Metric recovery from the holomorphic metric-scaled Wirtinger–Riccati equation
statement:
  Metric recovery from the holomorphic Wirtinger–Riccati equation. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the Liouville–Schwarzian difference satisfies the scalar Riccati equation](lean:localLiouvilleSchwarzianRiccatiReductionTheorem_of_canonicalMetricHolomorphicRiccati) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiReduction).
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
%%handwave
name:
  Metric recovery from the Wirtinger–Riccati reduction and first-order uniqueness
statement:
  Metric recovery from the corrected Wirtinger-Riccati reduction and the genuine first-order Liouville-Schwarzian uniqueness theorem. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_firstOrderUnique) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness).
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
%%handwave
name:
  Metric recovery from the Wirtinger–Riccati reduction and uniqueness of the scalar equation
statement:
  Metric recovery from the corrected Wirtinger-Riccati reduction and uniqueness for the scalar elliptic difference formulation. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_scalarDifferenceUnique) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness).
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
%%handwave
name:
  Metric recovery from the Wirtinger–Riccati reduction and uniqueness of the linearized scalar equation
statement:
  Metric recovery from the corrected Wirtinger-Riccati reduction and uniqueness for the linearized scalar elliptic difference formulation. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_linearizedScalarDifferenceUnique) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness).
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
%%handwave
name:
  Metric recovery from the Wirtinger–Riccati reduction and elliptic Cauchy uniqueness
statement:
  Metric recovery from the corrected Wirtinger-Riccati reduction and standard linear elliptic Cauchy uniqueness. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_linearEllipticCauchyUnique) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness).
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
%%handwave
name:
  Metric recovery from the Wirtinger–Riccati reduction and pathwise first-order uniqueness
statement:
  Metric recovery from the corrected Wirtinger-Riccati reduction and pathwise uniqueness for the closed first-order linear system. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Combine [the original and pullback logarithmic densities agree on the normalized domain](lean:localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati_closedFirstOrderLinearSystemUnique) with [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_logLiouvilleUniqueness).
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
%%handwave
name:
  The normalized domain is a disk
statement:
  Every normalized two-jet domain occurring here is a complex disk.
proof:
  Use the disk description supplied by the two-jet normalization.
-/
theorem ballDomain (_B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    HyperbolicTwoJetNormalizationHasBallDomainTheorem :=
  hyperbolicTwoJetNormalizationHasBallDomainTheorem

/--
%%handwave
name:
  Logarithmic uniqueness from the pullback formula and scalar Riccati reduction
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the logarithmic conformal factors agree: \(φ(z)=φ_C(z)\) for all \(z∈Ω\).
proof:
  Reduce the stated Riccati identities to zero-initial-value uniqueness for the first-derivative difference, then integrate using the normalized base value.
-/
theorem localLogUniqueness (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiReduction
    B.riccatiReduction

/--
%%handwave
name:
  Squared-density uniqueness from the pullback formula and scalar Riccati reduction
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the squared densities agree: \(ρ_u(z)²=ρ_C(z)²\) for all \(z∈Ω\).
proof:
  Exponentiate the preceding equality of logarithmic conformal factors.
-/
theorem localUniqueness (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness B.localLogUniqueness

/--
%%handwave
name:
  Metric recovery from the pullback formula and scalar Riccati reduction
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Logarithmic uniqueness from the pullback formula and concrete Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the logarithmic conformal factors agree: \(φ(z)=φ_C(z)\) for all \(z∈Ω\).
proof:
  Reduce the stated Riccati identities to zero-initial-value uniqueness for the first-derivative difference, then integrate using the normalized base value.
-/
theorem localLogUniqueness (B : HyperbolicTwoJetRiccatiCalculusBoundaryTheorems) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_riccatiCalculus
    B.riccatiCalculus

/--
%%handwave
name:
  Squared-density uniqueness from the pullback formula and concrete Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the squared densities agree: \(ρ_u(z)²=ρ_C(z)²\) for all \(z∈Ω\).
proof:
  Exponentiate the preceding equality of logarithmic conformal factors.
-/
theorem localUniqueness (B : HyperbolicTwoJetRiccatiCalculusBoundaryTheorems) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness B.localLogUniqueness

/--
%%handwave
name:
  Metric recovery from the pullback formula and concrete Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Logarithmic uniqueness from the pullback formula and canonical Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the logarithmic conformal factors agree: \(φ(z)=φ_C(z)\) for all \(z∈Ω\).
proof:
  Reduce the stated Riccati identities to zero-initial-value uniqueness for the first-derivative difference, then integrate using the normalized base value.
-/
theorem localLogUniqueness (B : HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_canonicalRiccatiCalculus
    B.canonicalRiccati

/--
%%handwave
name:
  Squared-density uniqueness from the pullback formula and canonical Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the squared densities agree: \(ρ_u(z)²=ρ_C(z)²\) for all \(z∈Ω\).
proof:
  Exponentiate the preceding equality of logarithmic conformal factors.
-/
theorem localUniqueness (B : HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_logUniqueness B.localLogUniqueness

/--
%%handwave
name:
  Metric recovery from the pullback formula and canonical Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Logarithmic uniqueness from the metric-scaled canonical Riccati identities
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the logarithmic conformal factors agree: \(φ(z)=φ_C(z)\) for all \(z∈Ω\).
proof:
  Reduce the stated Riccati identities to zero-initial-value uniqueness for the first-derivative difference, then integrate using the normalized base value.
-/
theorem localLogUniqueness (B : HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  B.toCanonicalRiccatiBoundary.localLogUniqueness

/--
%%handwave
name:
  Squared-density uniqueness from the metric-scaled canonical Riccati identities
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the squared densities agree: \(ρ_u(z)²=ρ_C(z)²\) for all \(z∈Ω\).
proof:
  Exponentiate the preceding equality of logarithmic conformal factors.
-/
theorem localUniqueness (B : HyperbolicTwoJetCanonicalMetricRiccatiBoundaryTheorems) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  B.toCanonicalRiccatiBoundary.localUniqueness

/--
%%handwave
name:
  Metric recovery from the metric-scaled canonical Riccati identities
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Logarithmic uniqueness from the corrected metric-scaled Wirtinger–Riccati equation
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the logarithmic conformal factors agree: \(φ(z)=φ_C(z)\) for all \(z∈Ω\).
proof:
  Reduce the stated Riccati identities to zero-initial-value uniqueness for the first-derivative difference, then integrate using the normalized base value.
-/
theorem localLogUniqueness
    (B : HyperbolicTwoJetCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    LocalLiouvilleSchwarzianLogUniquenessTheorem :=
  localLiouvilleSchwarzianLogUniquenessTheorem_of_wirtingerRiccati
    B.canonicalMetricWirtingerRiccati

/--
%%handwave
name:
  Squared-density uniqueness from the corrected metric-scaled Wirtinger–Riccati equation
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the squared densities agree: \(ρ_u(z)²=ρ_C(z)²\) for all \(z∈Ω\).
proof:
  Exponentiate the preceding equality of logarithmic conformal factors.
-/
theorem localUniqueness
    (B : HyperbolicTwoJetCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    LocalLiouvilleSchwarzianUniquenessTheorem :=
  localLiouvilleSchwarzianUniquenessTheorem_of_wirtingerRiccati
    B.canonicalMetricWirtingerRiccati

/--
%%handwave
name:
  Metric recovery from the corrected metric-scaled Wirtinger–Riccati equation
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from the explicit pullback formula and canonical Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from the explicit pullback formula and metric-scaled Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from the canonical pullback formula and canonical Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from the canonical pullback formula and metric-scaled Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from the explicit Wirtinger pullback formulas and canonical Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from the pullback density derivative and canonical Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from the branch derivative formula and canonical Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from the second pullback identity and canonical Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from the third-derivative identity and canonical Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from affine derivative identities and canonical Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from derivative identification and canonical Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from derivative identification and metric-scaled Riccati calculus
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from derivative identification and the Wirtinger–Riccati equation
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from derivative algebra and the Wirtinger–Riccati equation
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from affine derivative identities and the Wirtinger–Riccati equation
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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

/--
%%handwave
name:
  Metric recovery from affine derivative algebra and the Wirtinger–Riccati equation
statement:
  For every normalized branch satisfying the stated pullback and Riccati hypotheses, the original metric is the Poincaré pullback: \(ρ_u(z)²=|F'(z)|²/(\operatorname{Im} F(z))²\) for all \(z∈Ω\).
proof:
  Construct the Poincaré pullback factor, use Riccati uniqueness to identify its density with the original one, and unfold the pullback density formula.
-/
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
%%handwave
name:
  Metric recovery from the pullback formula and scalar Riccati reduction
statement:
  The pullback Liouville formula and scalar Riccati reduction imply metric recovery. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Apply metric recovery from the pullback Liouville formula and scalar Riccati equation.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_riccatiAnalyticBoundary
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.recoversMetric

/--
%%handwave
name:
  Metric recovery from derivative identification and metric-scaled Riccati calculus
statement:
  The current strongest derivative-identified and metric-scaled boundary gives metric recovery. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Forget the derivative-identified provenance and metric scaling to the pullback formula and canonical Riccati identities, then apply its metric-recovery theorem.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentifiedCanonicalMetricRiccatiBoundary
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.recoversMetric

/--
%%handwave
name:
  Metric recovery from derivative identification and the Wirtinger–Riccati equation
statement:
  The derivative-identified pullback boundary plus corrected Fréchet-Wirtinger Riccati uniqueness gives metric recovery. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Convert the derivative-identified pullback formulas into a pullback Liouville candidate and apply corrected Wirtinger–Riccati uniqueness.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentifiedCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.recoversMetric

/--
%%handwave
name:
  Metric recovery from affine derivative algebra and the Wirtinger–Riccati equation
statement:
  The affine-derivative-algebra pullback boundary plus corrected Fréchet-Wirtinger Riccati uniqueness gives metric recovery, with the Poincaré Laplacian calculation supplied internally. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Derive the Poincaré Laplacian and derivative identities from the affine derivative algebra, then apply the corrected Wirtinger boundary’s metric-recovery result.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_affineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.recoversMetric

/--
%%handwave
name:
  Metric recovery from derivative algebra and the Wirtinger–Riccati equation
statement:
  The derivative-algebra pullback boundary plus corrected Fréchet-Wirtinger Riccati uniqueness gives metric recovery, with the Poincaré Laplacian calculation supplied internally. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Convert derivative algebra to affine derivative algebra, derive the Poincaré Laplacian internally, and invoke the corrected Wirtinger boundary’s metric-recovery result.
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivativeAlgebraCanonicalMetricWirtingerRiccatiBoundary
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  B.recoversMetric

/--
%%handwave
name:
  Metric recovery from derivative identification and the Wirtinger–Riccati equation
statement:
  Derivative identification for the Poincaré pullback together with corrected Fréchet–Wirtinger Riccati uniqueness gives \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\) for every \(z\in\Omega\).
proof:
  Apply [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentifiedCanonicalMetricWirtingerRiccatiBoundary).
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati
    (hPullback : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentifiedCanonicalMetricWirtingerRiccatiBoundary
    { canonicalPullbackDerivIdentified := hPullback
      canonicalMetricWirtingerRiccati := hRiccati }

/--
%%handwave
name:
  Metric recovery from affine derivative identities and the Wirtinger–Riccati equation
statement:
  Metric recovery from actual affine complex-derivative identities and the corrected Fréchet-Wirtinger Riccati theorem. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Apply [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati).
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_affineDerivative_and_wirtingerRiccati
    (hAffine : HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_affineDerivative hAffine)
    hRiccati

/--
%%handwave
name:
  Metric recovery from affine derivative algebra, the Poincaré Laplacian identity, and the Wirtinger–Riccati equation
statement:
  Metric recovery from actual affine derivative algebra, the geometric Poincaré Laplacian identity, and the corrected Fréchet-Wirtinger Riccati theorem. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Apply [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati).
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
%%handwave
name:
  Metric recovery from affine derivative algebra and the Wirtinger–Riccati equation
statement:
  Metric recovery from actual affine derivative algebra and the corrected Fréchet-Wirtinger Riccati theorem. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Apply [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati).
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
%%handwave
name:
  Metric recovery from derivative algebra, the Poincaré Laplacian identity, and the Wirtinger–Riccati equation
statement:
  Metric recovery from the three separated local inputs: derivative algebra for the normalized branch, the geometric Poincaré Laplacian identity, and the corrected Fréchet-Wirtinger Riccati theorem. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Apply [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati).
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
%%handwave
name:
  Metric recovery from derivative algebra and the Wirtinger–Riccati equation
statement:
  Metric recovery from derivative algebra for the normalized branch and the corrected Fréchet-Wirtinger Riccati theorem. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Apply [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati).
-/
theorem hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivativeAlgebra_and_wirtingerRiccati
    (hAlg : HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem)
    (hRiccati : LocalLiouvilleSchwarzianCanonicalMetricWirtingerRiccatiTheorem) :
    HyperbolicTwoJetNormalizationRecoversMetricTheorem :=
  hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_derivativeAlgebra hAlg)
    hRiccati

/--
%%handwave
name:
  Metric recovery from regularity, derivative identification, the Poincaré Laplacian identity, and the Wirtinger–Riccati equation
statement:
  Metric recovery from the four separated local inputs: regularity of the normalized branch, derivative identification for its affine branch, the geometric Poincaré Laplacian identity, and the corrected Fréchet-Wirtinger Riccati theorem. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Apply [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati).
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
%%handwave
name:
  Metric recovery from regularity, derivative identification, and the Wirtinger–Riccati equation
statement:
  Metric recovery from regularity, derivative identification, and the corrected Fréchet-Wirtinger Riccati theorem. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Apply [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati).
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
%%handwave
name:
  Metric recovery from regularity, three derivative identities, the Poincaré Laplacian identity, and the Wirtinger–Riccati equation
statement:
  Metric recovery from the five separated local inputs: regularity of the normalized branch, the three affine derivative-identification levels, the geometric Poincaré Laplacian identity, and the corrected Fréchet-Wirtinger Riccati theorem. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Apply [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati).
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
%%handwave
name:
  Metric recovery from regularity, three derivative identities, and the Wirtinger–Riccati equation
statement:
  Metric recovery from regularity, the three affine derivative-identification levels, and the corrected Fréchet-Wirtinger Riccati theorem. For every \(z\in\Omega\), this is the formula \(\rho_u(z)^2=|F'(z)|^2/(\operatorname{Im}F(z))^2\).
proof:
  Apply [the normalized branch satisfies \(\rho_u^2=|F'|^2/(\operatorname{Im}F)^2\)](lean:hyperbolicTwoJetNormalizationRecoversMetricTheorem_of_derivIdentified_and_wirtingerRiccati).
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
%%handwave
name:
  Existence of a metric-recovering upper-half-plane normalization from two-jet normalization and metric recovery
statement:
  The precise 2-jet normalization theorem plus metric recovery from that 2-jet imply the older existence of a metric-recovering upper-half-plane normalization. Thus every point of the Schwarzian branch lies in a local upper-half-plane normalization whose Poincaré pullback metric equals the original conformal metric.
proof:
  Choose the two-jet normalization at the given point, attach the assumed metric-recovery identity to it, and retain the original point in the normalized domain.
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
%%handwave
name:
  Existence of a metric-recovering upper-half-plane normalization from two-jet normalization and the scalar Riccati reduction
statement:
  The precise 2-jet normalization theorem plus the pullback Liouville formula and scalar Riccati reduction give the existence of a metric-recovering upper-half-plane normalization. Thus every point of the Schwarzian branch lies in a local upper-half-plane normalization whose Poincaré pullback metric equals the original conformal metric.
proof:
  Apply [two-jet normalization and metric recovery give a metric-recovering upper-half-plane normalization](lean:hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet).
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetRiccatiAnalyticBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiAnalyticBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
    hJet B.recoversMetric

/--
%%handwave
name:
  Existence of a metric-recovering upper-half-plane normalization from two-jet normalization and concrete Riccati calculus
statement:
  The precise 2-jet normalization theorem plus the pullback formula and concrete Riccati calculus identities give the existence of a metric-recovering upper-half-plane normalization. Thus every point of the Schwarzian branch lies in a local upper-half-plane normalization whose Poincaré pullback metric equals the original conformal metric.
proof:
  Apply [two-jet normalization and metric recovery give a metric-recovering upper-half-plane normalization](lean:hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetRiccatiAnalyticBoundary).
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetRiccatiCalculusBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetRiccatiCalculusBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetRiccatiAnalyticBoundary
    hJet B.toRiccatiAnalyticBoundary

/--
%%handwave
name:
  Existence of a metric-recovering upper-half-plane normalization from two-jet normalization and canonical Riccati calculus
statement:
  The precise 2-jet normalization theorem plus the pullback formula and canonical Riccati identities give the existence of a metric-recovering upper-half-plane normalization. Thus every point of the Schwarzian branch lies in a local upper-half-plane normalization whose Poincaré pullback metric equals the original conformal metric.
proof:
  Apply [two-jet normalization and metric recovery give a metric-recovering upper-half-plane normalization](lean:hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetRiccatiCalculusBoundary).
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetCanonicalRiccatiBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalRiccatiBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetRiccatiCalculusBoundary
    hJet B.toRiccatiCalculusBoundary

/--
%%handwave
name:
  Existence of a metric-recovering upper-half-plane normalization from two-jet normalization and the second pullback identity
statement:
  The precise 2-jet normalization theorem plus the second pullback identity and canonical Riccati identities give the existence of a metric-recovering upper-half-plane normalization. Thus every point of the Schwarzian branch lies in a local upper-half-plane normalization whose Poincaré pullback metric equals the original conformal metric.
proof:
  Apply [two-jet normalization and metric recovery give a metric-recovering upper-half-plane normalization](lean:hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet).
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetSecondExpressionBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalPullbackSecondExpressionCanonicalRiccatiBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
    hJet B.recoversMetric

/--
%%handwave
name:
  Existence of a metric-recovering upper-half-plane normalization from two-jet normalization and the third-derivative identity
statement:
  The precise 2-jet normalization theorem plus the third-derivative identity and canonical Riccati identities give the existence of a metric-recovering upper-half-plane normalization. Thus every point of the Schwarzian branch lies in a local upper-half-plane normalization whose Poincaré pullback metric equals the original conformal metric.
proof:
  Apply [two-jet normalization and metric recovery give a metric-recovering upper-half-plane normalization](lean:hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet).
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetThirdDerivativeBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalPullbackThirdDerivativeCanonicalRiccatiBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
    hJet B.recoversMetric

/--
%%handwave
name:
  Existence of a metric-recovering upper-half-plane normalization from two-jet normalization and affine derivative identities
statement:
  The precise 2-jet normalization theorem plus the affine derivative identities and canonical Riccati identities give the existence of a metric-recovering upper-half-plane normalization. Thus every point of the Schwarzian branch lies in a local upper-half-plane normalization whose Poincaré pullback metric equals the original conformal metric.
proof:
  Apply [two-jet normalization and metric recovery give a metric-recovering upper-half-plane normalization](lean:hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet).
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetAffineDerivativeBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalPullbackAffineDerivativeCanonicalRiccatiBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
    hJet B.recoversMetric

/--
%%handwave
name:
  Existence of a metric-recovering upper-half-plane normalization from two-jet normalization and derivative identification
statement:
  The precise 2-jet normalization theorem plus the derivative identification and canonical Riccati identities give the existence of a metric-recovering upper-half-plane normalization. Thus every point of the Schwarzian branch lies in a local upper-half-plane normalization whose Poincaré pullback metric equals the original conformal metric.
proof:
  Apply [two-jet normalization and metric recovery give a metric-recovering upper-half-plane normalization](lean:hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet).
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetDerivIdentifiedBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalRiccatiBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
    hJet B.recoversMetric

/--
%%handwave
name:
  Existence of a metric-recovering upper-half-plane normalization from two-jet normalization, derivative identification, and Wirtinger–Riccati uniqueness
statement:
  The precise 2-jet normalization theorem plus the derivative identification and the corrected Wirtinger–Riccati equation give the existence of a metric-recovering upper-half-plane normalization. Thus every point of the Schwarzian branch lies in a local upper-half-plane normalization whose Poincaré pullback metric equals the original conformal metric.
proof:
  Apply [two-jet normalization and metric recovery give a metric-recovering upper-half-plane normalization](lean:hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet).
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJetDerivIdentifiedMetricWirtingerBoundary
    (hJet : HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem)
    (B :
      HyperbolicTwoJetCanonicalPullbackDerivIdentifiedCanonicalMetricWirtingerRiccatiBoundaryTheorems) :
    HyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem :=
  hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet
    hJet B.recoversMetric

/--
%%handwave
name:
  Existence of a metric-recovering upper-half-plane normalization from two-jet normalization, affine derivative identities, and Wirtinger–Riccati uniqueness
statement:
  The precise 2-jet normalization theorem plus actual affine pullback derivatives and corrected Wirtinger-Riccati uniqueness give the existence of a metric-recovering upper-half-plane normalization. Thus every point of the Schwarzian branch lies in a local upper-half-plane normalization whose Poincaré pullback metric equals the original conformal metric.
proof:
  Apply [two-jet normalization and metric recovery give a metric-recovering upper-half-plane normalization](lean:hyperbolicProjectiveDevelopingMapAdmitsMetricRecoveringNormalizationTheorem_of_twoJet).
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
%%handwave
name:
  Local existence for the Schwarzian linear ODE from existence of a normalized Frobenius pair
statement:
  The Frobenius-pair existence theorem implies the normalized linear ODE local existence theorem used by the Schwarzian chart construction. For each \(z_0\) in the coordinate domain there is an open neighborhood \(U\) and a normalized fundamental pair for \(y''+\tfrac12 qy=0\) on \(U\).
proof:
  Take the convergent Frobenius solution pair, use its centered disk of convergence as \(U\), and pass to the normalized fundamental pair.
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
%%handwave
name:
  Local solvability of the holomorphic Schwarzian equation from local existence for the Schwarzian linear ODE
statement:
  Local existence of normalized solution pairs implies local solvability of the Schwarzian equation. For every \(z_0\) in the coordinate domain there is a local Schwarzian ODE chart whose domain contains \(z_0\).
proof:
  Choose the normalized fundamental pair on \(U\) and form its Schwarzian linear-ODE frame; the resulting chart still contains the base point.
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
%%handwave
name:
  Local solvability of the holomorphic Schwarzian equation from existence of a normalized Frobenius pair
statement:
  The power-series/Frobenius existence theorem directly gives local solvability of the Schwarzian equation. For every \(z_0\) in the coordinate domain there is a local Schwarzian ODE chart whose domain contains \(z_0\).
proof:
  Combine [a Frobenius pair gives a normalized local solution pair for \(y''+\tfrac12 qy=0\)](lean:holomorphicSchwarzianLinearODELocalExistence_of_frobeniusPairExistence) with [normalized local ODE solutions give a local Schwarzian chart](lean:holomorphicSchwarzianLocallySolvableTheorem_of_linearODELocalExistence).
-/
theorem holomorphicSchwarzianLocallySolvableTheorem_of_frobeniusPairExistence
    (h : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    HolomorphicSchwarzianLocallySolvableTheorem :=
  holomorphicSchwarzianLocallySolvableTheorem_of_linearODELocalExistence
    (holomorphicSchwarzianLinearODELocalExistence_of_frobeniusPairExistence h)

/--
%%handwave
name:
  A local Schwarzian ODE chart from local solvability of the Schwarzian equation
statement:
  Apply the local Schwarzian ODE existence theorem to a chosen coefficient. For every \(z_0\) in the coordinate domain there is a local Schwarzian ODE chart whose domain contains \(z_0\).
proof:
  Specialize the assumed local existence statement to the chosen coefficient and base point.
-/
theorem localSchwarzianODEChart_of_localSolvability
    (h : HolomorphicSchwarzianLocallySolvableTheorem)
    {u : LocalConformalFactor} (S : LocalSchwarzianData u) ⦃z : ℂ⦄
    (hz : z ∈ u.coordinateDomain) :
    ∃ C : LocalSchwarzianODEChart S, z ∈ C.domain :=
  h S hz

/--
%%handwave
name:
  Local projective developing maps for a holomorphic Schwarzian from local solvability of the Schwarzian equation
statement:
  Local Schwarzian solvability gives local projective developing maps. For every \(z_0\) in the coordinate domain there is a local projective developing map defined at \(z_0\).
proof:
  Choose a local Schwarzian ODE chart and take the projective ratio of its normalized solution frame.
-/
theorem holomorphicSchwarzianLocalProjectiveDevelopingMapTheorem_of_localSolvability
    (h : HolomorphicSchwarzianLocallySolvableTheorem) :
    HolomorphicSchwarzianLocalProjectiveDevelopingMapTheorem := by
  intro u S z hz
  rcases h S hz with ⟨C, hzC⟩
  exact ⟨C.toLocalProjectiveDevelopingMap, hzC⟩

/--
%%handwave
name:
  Local projective developing maps for a holomorphic Schwarzian from existence of a normalized Frobenius pair
statement:
  Frobenius-pair existence gives local projective developing maps. For every \(z_0\) in the coordinate domain there is a local projective developing map defined at \(z_0\).
proof:
  Combine [normalized local ODE solutions give a local Schwarzian chart](lean:holomorphicSchwarzianLocallySolvableTheorem_of_frobeniusPairExistence) with [local Schwarzian solvability gives a local projective developing map](lean:holomorphicSchwarzianLocalProjectiveDevelopingMapTheorem_of_localSolvability).
-/
theorem holomorphicSchwarzianLocalProjectiveDevelopingMapTheorem_of_frobeniusPairExistence
    (h : HolomorphicSchwarzianFrobeniusPairExistenceTheorem) :
    HolomorphicSchwarzianLocalProjectiveDevelopingMapTheorem :=
  holomorphicSchwarzianLocalProjectiveDevelopingMapTheorem_of_localSolvability
    (holomorphicSchwarzianLocallySolvableTheorem_of_frobeniusPairExistence h)

/--
%%handwave
name:
  A local projective developing map from local solvability of the Schwarzian equation
statement:
  Apply the local projective-developing-map theorem to a chosen coefficient. For every \(z_0\) in the coordinate domain there is a local projective developing map defined at \(z_0\).
proof:
  Specialize the assumed local existence statement to the chosen coefficient and base point.
-/
theorem localProjectiveDevelopingMap_of_localSolvability
    (h : HolomorphicSchwarzianLocalProjectiveDevelopingMapTheorem)
    {u : LocalConformalFactor} (S : LocalSchwarzianData u) ⦃z : ℂ⦄
    (hz : z ∈ u.coordinateDomain) :
    ∃ D : LocalProjectiveDevelopingMap S, z ∈ D.domain :=
  h S hz

end

end JJMath
