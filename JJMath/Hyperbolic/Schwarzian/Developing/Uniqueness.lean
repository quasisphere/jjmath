import JJMath.Hyperbolic.Schwarzian.Developing.RealMobiusTransitions

/-!
# Split Schwarzian developing-map constructions
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

def PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        IsPreconnected (H₁.domain ∩ H₂.domain) →
          H₁.HasPointedRealMobiusTransition H₂ A z₀ →
            ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
              H₂.upperHalfPlaneMap z =
                realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z)

/--
The equality locus of a pointed real-Mobius comparison, viewed as a subset of
the common overlap.
-/
def pointedRealMobiusTransitionEqualitySet
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) :
    Set {z : ℂ // z ∈ H₁.domain ∩ H₂.domain} :=
  {z | H₂.upperHalfPlaneMap (z : ℂ) =
      realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap (z : ℂ))}

/--
The one-jet equality locus of a pointed real-Mobius comparison, viewed as a
subset of the common overlap.

This is the right equality locus for local uniqueness: matching only the value
at a point is not enough, while matching value and complex derivative is.
-/
def pointedRealMobiusTransitionOneJetEqualitySet
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) :
    Set {z : ℂ // z ∈ H₁.domain ∩ H₂.domain} :=
  {z | H₂.upperHalfPlaneMap (z : ℂ) =
        realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap (z : ℂ)) ∧
      deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (z : ℂ) =
        deriv
          (fun w : ℂ ↦ (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
          (z : ℂ)}

/--
The two-jet equality locus of a pointed real-Mobius comparison, viewed as a
subset of the common overlap.

The extra second-derivative condition is mathematically essential for bare
Schwarzian uniqueness: the Schwarzian equation is invariant under complex
Mobius postcomposition, and a complex Mobius transformation can fix a point
with derivative `1` without being the identity.  For metric-recovering
upper-half-plane branches, the missing second-jet agreement is expected to
come from differentiating the common Poincare pullback density.
-/
def pointedRealMobiusTransitionTwoJetEqualitySet
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) :
    Set {z : ℂ // z ∈ H₁.domain ∩ H₂.domain} :=
  {z | H₂.upperHalfPlaneMap (z : ℂ) =
        realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap (z : ℂ)) ∧
      deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (z : ℂ) =
        deriv
          (fun w : ℂ ↦ (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
          (z : ℂ) ∧
      deriv (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H₂.upperHalfPlaneMap t : ℂ)) w)
          (z : ℂ) =
        deriv
          (fun w : ℂ ↦
            deriv
              (fun t : ℂ ↦
                (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap t) : ℂ))
              w)
          (z : ℂ)}

/--
Analytic clopen target for the connected-overlap real-transition argument.

The closed part should come from continuity of the two upper-half-plane-valued
maps; the open part is the local uniqueness/identity-principle step for the
metric-recovering Schwarzian branches.
-/
def PointedRealMobiusTransitionEqualitySetIsClopenTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          IsClopen (pointedRealMobiusTransitionEqualitySet H₁ H₂ A)

/--
Analytic clopen target for the one-jet equality locus in the connected-overlap
real-transition argument.
-/
def PointedRealMobiusTransitionOneJetEqualitySetIsClopenTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          IsClopen (pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A)

/-- Closedness target for the pointed real-Mobius equality locus in the overlap. -/
def PointedRealMobiusTransitionEqualitySetIsClosedTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          IsClosed (pointedRealMobiusTransitionEqualitySet H₁ H₂ A)

/-- Closedness target for the pointed real-Mobius one-jet equality locus. -/
def PointedRealMobiusTransitionOneJetEqualitySetIsClosedTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          IsClosed (pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A)

/--
Continuity target sufficient for closedness of the pointed real-Mobius
equality locus.
-/
def PointedRealMobiusTransitionEqualitySetContinuityTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          Continuous
            (fun z : {z : ℂ // z ∈ H₁.domain ∩ H₂.domain} ↦
              H₂.upperHalfPlaneMap (z : ℂ)) ∧
          Continuous
            (fun z : {z : ℂ // z ∈ H₁.domain ∩ H₂.domain} ↦
              realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap (z : ℂ)))

/--
Continuity of the compared branch maps makes the equality locus closed in the
overlap.
-/
theorem pointedRealMobiusTransitionEqualitySetIsClosedTheorem_of_continuity
    (hCont : PointedRealMobiusTransitionEqualitySetContinuityTheorem) :
    PointedRealMobiusTransitionEqualitySetIsClosedTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ hu hpoint
  rcases hCont H₁ H₂ A z₀ hu hpoint with ⟨h₂, hA⟩
  simpa [pointedRealMobiusTransitionEqualitySet] using isClosed_eq h₂ hA

/--
Derivative-continuity target for the one-jet equality locus in the overlap.
-/
def PointedRealMobiusTransitionOneJetDerivativeContinuityTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          Continuous
            (fun z : {z : ℂ // z ∈ H₁.domain ∩ H₂.domain} ↦
              deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (z : ℂ)) ∧
          Continuous
            (fun z : {z : ℂ // z ∈ H₁.domain ∩ H₂.domain} ↦
              deriv
                (fun w : ℂ ↦
                  (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
                (z : ℂ))

/--
Continuity of the complex derivative of an upper-half-plane branch on its own
domain.
-/
def LocalUpperHalfPlaneDevelopingMapComplexDerivativeContinuousOnDomainTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S),
      ContinuousOn
        (fun z : ℂ ↦ deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z)
        H.domain

/--
Continuity of the stored affine derivative of an upper-half-plane branch on
its domain.
-/
def LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S),
      ContinuousOn (fun z : ℂ ↦ H.projective.affineMapDeriv z) H.domain

/--
Continuity of the stored affine derivative gives continuity of the actual
complex derivative of the upper-half-plane branch.
-/
theorem localUpperHalfPlaneDevelopingMapComplexDerivativeContinuousOnDomainTheorem_of_affineDerivativeContinuous
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem) :
    LocalUpperHalfPlaneDevelopingMapComplexDerivativeContinuousOnDomainTheorem := by
  intro u S H
  exact (hAffine H).congr (fun z hz ↦ by
    exact H.upperHalfPlane_deriv_eq_projectiveDeriv z hz)

/--
Continuity of the derivative of a real-Mobius postcomposition of the first
branch on the common overlap.
-/
def PointedRealMobiusTransitionPostcompositionDerivativeContinuityTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          Continuous
            (fun z : {z : ℂ // z ∈ H₁.domain ∩ H₂.domain} ↦
              deriv
                (fun w : ℂ ↦
                  (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
                (z : ℂ))

/--
Branch derivative continuity and postcomposition derivative continuity give
the derivative-continuity target for the one-jet equality locus.
-/
theorem pointedRealMobiusTransitionOneJetDerivativeContinuityTheorem_of_branch_and_postcomposition
    (hBranchDeriv : LocalUpperHalfPlaneDevelopingMapComplexDerivativeContinuousOnDomainTheorem)
    (hPost :
      PointedRealMobiusTransitionPostcompositionDerivativeContinuityTheorem) :
    PointedRealMobiusTransitionOneJetDerivativeContinuityTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ hu hpoint
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  have h₂_on_overlap :
      ContinuousOn
        (fun z : ℂ ↦ deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z)
        overlap :=
    (hBranchDeriv H₂).mono (fun z hz ↦ hz.2)
  have h₂ :
      Continuous
        (fun z : overlap ↦
          deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (z : ℂ)) := by
    simpa [Set.restrict] using
      (continuousOn_iff_continuous_restrict.mp h₂_on_overlap)
  exact ⟨h₂, hPost H₁ H₂ A z₀ hu hpoint⟩

/--
Value continuity and derivative continuity make the one-jet equality locus
closed in the overlap.
-/
theorem pointedRealMobiusTransitionOneJetEqualitySetIsClosedTheorem_of_continuity
    (hValue : PointedRealMobiusTransitionEqualitySetContinuityTheorem)
    (hDeriv : PointedRealMobiusTransitionOneJetDerivativeContinuityTheorem) :
    PointedRealMobiusTransitionOneJetEqualitySetIsClosedTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ hu hpoint
  rcases hValue H₁ H₂ A z₀ hu hpoint with ⟨h₂, hA⟩
  rcases hDeriv H₁ H₂ A z₀ hu hpoint with ⟨hd₂, hdA⟩
  have hValueClosed :
      IsClosed
        {z : {z : ℂ // z ∈ H₁.domain ∩ H₂.domain} |
          H₂.upperHalfPlaneMap (z : ℂ) =
            realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap (z : ℂ))} :=
    isClosed_eq h₂ hA
  have hDerivClosed :
      IsClosed
        {z : {z : ℂ // z ∈ H₁.domain ∩ H₂.domain} |
          deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (z : ℂ) =
            deriv
              (fun w : ℂ ↦
                (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
              (z : ℂ)} :=
    isClosed_eq hd₂ hdA
  simpa [pointedRealMobiusTransitionOneJetEqualitySet, Set.setOf_and] using
    hValueClosed.inter hDerivClosed

/-- Continuity of an upper-half-plane branch on its own domain. -/
def LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S),
      Continuous (fun z : {z : ℂ // z ∈ H.domain} ↦ H.upperHalfPlaneMap (z : ℂ))

/-- Continuity of an upper-half-plane branch as a complex-valued map on its domain. -/
def LocalUpperHalfPlaneDevelopingMapComplexContinuousOnDomainTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S),
      ContinuousOn (fun z : ℂ ↦ (H.upperHalfPlaneMap z : ℂ)) H.domain

/-- `C¹` regularity of an upper-half-plane branch as a complex-valued map on its domain. -/
def LocalUpperHalfPlaneDevelopingMapComplexContDiffOnDomainTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S),
      ContDiffOn ℝ 1 (fun z : ℂ ↦ (H.upperHalfPlaneMap z : ℂ)) H.domain

/--
Complex-valued continuity of a branch on its domain gives continuity of the
upper-half-plane-valued restricted branch.
-/
theorem localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem_of_complexContinuousOn
    (hComplex : LocalUpperHalfPlaneDevelopingMapComplexContinuousOnDomainTheorem) :
    LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem := by
  intro u S H
  let f : ℂ → ℂ := fun z ↦ (H.upperHalfPlaneMap z : ℂ)
  have hf : Continuous (H.domain.restrict f) :=
    continuousOn_iff_continuous_restrict.mp (hComplex H)
  exact continuous_induced_rng.mpr (by
    simpa [Function.comp_def, f, Set.restrict] using hf)

/-- `C¹` regularity of branches gives branch-domain continuity. -/
theorem localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem_of_complexContDiffOn
    (hContDiff : LocalUpperHalfPlaneDevelopingMapComplexContDiffOnDomainTheorem) :
    LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem :=
  localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem_of_complexContinuousOn
    (by
      intro u S H
      exact (hContDiff H).continuousOn)

/--
The actual nonzero derivative stored by every upper-half-plane developing
branch gives branch-domain continuity.
-/
theorem localUpperHalfPlaneDevelopingMapComplexContinuousOnDomainTheorem :
    LocalUpperHalfPlaneDevelopingMapComplexContinuousOnDomainTheorem := by
  intro u S H z hz
  let f : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  have hf_ne : deriv f z ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, f] at hpos
    exact Complex.normSq_pos.mp hpos
  exact ((differentiableAt_of_deriv_ne_zero hf_ne).hasDerivAt).continuousAt.continuousWithinAt

/-- Upper-half-plane developing branches are continuous on their domains. -/
theorem localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem :
    LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem :=
  localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem_of_complexContinuousOn
    localUpperHalfPlaneDevelopingMapComplexContinuousOnDomainTheorem

/-- Continuity of every fixed real-Mobius action on the upper half-plane. -/
def RealMobiusRepresentativeActionContinuousTheorem : Prop :=
  ∀ A : RealMobiusRepresentative, Continuous (realMobiusRepresentativeAction A)

/-- Fixed real-Mobius actions are continuous on the upper half-plane. -/
theorem realMobiusRepresentativeActionContinuousTheorem :
    RealMobiusRepresentativeActionContinuousTheorem :=
  realMobiusRepresentativeAction_continuous

/--
Domain continuity of branches and continuity of real-Mobius actions imply the
overlap-continuity target for the equality locus.
-/
theorem pointedRealMobiusTransitionEqualitySetContinuityTheorem_of_branch_and_action_continuity
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAction : RealMobiusRepresentativeActionContinuousTheorem) :
    PointedRealMobiusTransitionEqualitySetContinuityTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ _hu _hpoint
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  let toH₁Domain : overlap → {z : ℂ // z ∈ H₁.domain} :=
    fun z ↦ ⟨(z : ℂ), z.property.1⟩
  let toH₂Domain : overlap → {z : ℂ // z ∈ H₂.domain} :=
    fun z ↦ ⟨(z : ℂ), z.property.2⟩
  have htoH₁ : Continuous toH₁Domain := by
    exact continuous_subtype_val.subtype_mk (fun z ↦ z.property.1)
  have htoH₂ : Continuous toH₂Domain := by
    exact continuous_subtype_val.subtype_mk (fun z ↦ z.property.2)
  have h₂ :
      Continuous
        (fun z : overlap ↦ H₂.upperHalfPlaneMap (z : ℂ)) := by
    simpa [toH₂Domain] using (hBranch H₂).comp htoH₂
  have h₁ :
      Continuous
        (fun z : overlap ↦ H₁.upperHalfPlaneMap (z : ℂ)) := by
    simpa [toH₁Domain] using (hBranch H₁).comp htoH₁
  exact ⟨h₂, (hAction A).comp h₁⟩

/--
Branch-domain continuity plus real-Mobius action continuity make the pointed
equality locus closed in the overlap.
-/
theorem pointedRealMobiusTransitionEqualitySetIsClosedTheorem_of_branch_and_action_continuity
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAction : RealMobiusRepresentativeActionContinuousTheorem) :
    PointedRealMobiusTransitionEqualitySetIsClosedTheorem :=
  pointedRealMobiusTransitionEqualitySetIsClosedTheorem_of_continuity
    (pointedRealMobiusTransitionEqualitySetContinuityTheorem_of_branch_and_action_continuity
      hBranch hAction)

/--
Branch-domain continuity alone makes the pointed equality locus closed, since
fixed real-Mobius actions are continuous.
-/
theorem pointedRealMobiusTransitionEqualitySetIsClosedTheorem_of_branch_continuity
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem) :
    PointedRealMobiusTransitionEqualitySetIsClosedTheorem :=
  pointedRealMobiusTransitionEqualitySetIsClosedTheorem_of_branch_and_action_continuity
    hBranch realMobiusRepresentativeActionContinuousTheorem

/--
Branch-domain continuity and stored affine derivative continuity imply
continuity of the derivative of a real-Mobius postcomposition on the overlap.
-/
theorem pointedRealMobiusTransitionPostcompositionDerivativeContinuityTheorem_of_branch_continuity
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem) :
    PointedRealMobiusTransitionPostcompositionDerivativeContinuityTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ _hu _hpoint
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  let toH₁Domain : overlap → {z : ℂ // z ∈ H₁.domain} :=
    fun z ↦ ⟨(z : ℂ), z.property.1⟩
  have htoH₁ : Continuous toH₁Domain := by
    exact continuous_subtype_val.subtype_mk (fun z ↦ z.property.1)
  have hH₁ :
      Continuous (fun z : overlap ↦ H₁.upperHalfPlaneMap (z : ℂ)) := by
    simpa [toH₁Domain] using (hBranch H₁).comp htoH₁
  have hfactor :
      Continuous
        (fun z : overlap ↦
          deriv
            (fun w : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
            (H₁.upperHalfPlaneMap (z : ℂ))) :=
    (realMobiusRepresentativeAction_deriv_continuous A).comp hH₁
  have hbranchDerivOnOverlap :
      ContinuousOn
        (fun z : ℂ ↦ deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ)) z)
        overlap :=
    (localUpperHalfPlaneDevelopingMapComplexDerivativeContinuousOnDomainTheorem_of_affineDerivativeContinuous
      hAffine H₁).mono (fun z hz ↦ hz.1)
  have hbranchDeriv :
      Continuous
        (fun z : overlap ↦
          deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ)) (z : ℂ)) := by
    simpa [Set.restrict] using
      (continuousOn_iff_continuous_restrict.mp hbranchDerivOnOverlap)
  have hprod :
      Continuous
        (fun z : overlap ↦
          deriv
            (fun w : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
            (H₁.upperHalfPlaneMap (z : ℂ)) *
          deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ)) (z : ℂ)) :=
    hfactor.mul hbranchDeriv
  have htarget_eq :
      (fun z : overlap ↦
        deriv
          (fun w : ℂ ↦
            (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
          (z : ℂ))
      =
      (fun z : overlap ↦
        deriv
          (fun w : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
          (H₁.upperHalfPlaneMap (z : ℂ)) *
        deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ)) (z : ℂ)) := by
    funext z
    exact realMobiusBranchPostcompositionDerivativeChainRuleTheorem H₁ A z.property.1
  rw [htarget_eq]
  exact hprod

/--
Branch-domain continuity and stored affine derivative continuity make the
one-jet equality locus closed.
-/
theorem pointedRealMobiusTransitionOneJetEqualitySetIsClosedTheorem_of_branch_continuity
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem) :
    PointedRealMobiusTransitionOneJetEqualitySetIsClosedTheorem :=
  pointedRealMobiusTransitionOneJetEqualitySetIsClosedTheorem_of_continuity
    (pointedRealMobiusTransitionEqualitySetContinuityTheorem_of_branch_and_action_continuity
      hBranch realMobiusRepresentativeActionContinuousTheorem)
    (pointedRealMobiusTransitionOneJetDerivativeContinuityTheorem_of_branch_and_postcomposition
      (localUpperHalfPlaneDevelopingMapComplexDerivativeContinuousOnDomainTheorem_of_affineDerivativeContinuous
        hAffine)
      (pointedRealMobiusTransitionPostcompositionDerivativeContinuityTheorem_of_branch_continuity
        hBranch hAffine))

/-- Openness target for the pointed real-Mobius equality locus in the overlap. -/
def PointedRealMobiusTransitionEqualitySetIsOpenTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          IsOpen (pointedRealMobiusTransitionEqualitySet H₁ H₂ A)

/-- Openness target for the pointed real-Mobius one-jet equality locus. -/
def PointedRealMobiusTransitionOneJetEqualitySetIsOpenTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          IsOpen (pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A)

/--
Local uniqueness target for the pointed real-Mobius one-jet comparison.

At any point of the overlap where the value and derivative of the two compared
branches agree, the agreement should hold on an ambient open neighborhood
inside the overlap.  This is the analytic identity-principle input behind
openness of the one-jet equality locus.
-/
def PointedRealMobiusTransitionOneJetLocalUniquenessTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
            H₂.upperHalfPlaneMap z =
                realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z) →
            deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z =
                deriv
                  (fun w : ℂ ↦
                    (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
                  z →
              ∃ U : Set ℂ,
                IsOpen U ∧ z ∈ U ∧ U ⊆ H₁.domain ∩ H₂.domain ∧
                  ∀ w, w ∈ U →
                    H₂.upperHalfPlaneMap w =
                        realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) ∧
                    deriv (fun t : ℂ ↦ (H₂.upperHalfPlaneMap t : ℂ)) w =
                    deriv
                      (fun t : ℂ ↦
                        (realMobiusRepresentativeAction A
                          (H₁.upperHalfPlaneMap t) : ℂ))
                      w

/--
Coefficient agreement on overlaps for metric-recovering branch data.

For branches known to come from the canonical metric Schwarzian of the same
conformal factor, this is formal.  It is separated out because the bare
`LocalUpperHalfPlaneDevelopingMap` structure intentionally allows arbitrary
Schwarzian data.
-/
def MetricRecoveringUpperHalfPlaneBranchesHaveSameSchwarzianCoefficientOnOverlapTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂),
      u.SolvesLiouvilleEquation →
        ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
          S₁.coefficient z = S₂.coefficient z

/--
Metric-Schwarzian identifications for two branches over the same conformal
factor imply coefficient agreement on their overlap.
-/
theorem sameSchwarzianCoefficientOnOverlap_of_originalMetricIdentifications
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hS₁ : LocalOriginalMetricSchwarzianIdentification S₁)
    (hS₂ : LocalOriginalMetricSchwarzianIdentification S₂) :
    ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
      S₁.coefficient z = S₂.coefficient z := by
  intro z hz₁ _hz₂
  have hzcoord : z ∈ u.coordinateDomain :=
    H₁.projective.domain_subset hz₁
  rw [hS₁.coefficient_eq_metric z hzcoord, hS₂.coefficient_eq_metric z hzcoord]

/--
Local one-jet uniqueness assuming the two branch Schwarzian coefficients agree
on the overlap.

This is the Schwarzian/ODE identity-principle core: after coefficient
agreement and one-jet agreement at a point, equality should persist locally.
-/
def PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          (∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
            S₁.coefficient z = S₂.coefficient z) →
          ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
            H₂.upperHalfPlaneMap z =
                realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z) →
            deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z =
                deriv
                  (fun w : ℂ ↦
                    (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
                  z →
              ∃ U : Set ℂ,
                IsOpen U ∧ z ∈ U ∧ U ⊆ H₁.domain ∩ H₂.domain ∧
                  ∀ w, w ∈ U →
                    H₂.upperHalfPlaneMap w =
                        realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) ∧
                    deriv (fun t : ℂ ↦ (H₂.upperHalfPlaneMap t : ℂ)) w =
                        deriv
                          (fun t : ℂ ↦
                            (realMobiusRepresentativeAction A
                              (H₁.upperHalfPlaneMap t) : ℂ))
                          w

/--
The metric-recovery bridge from a pointed hyperbolic one-jet match to the
second-derivative equality needed by Schwarzian uniqueness.

This is the precise place where the Poincare pullback formula should be
differentiated: for a holomorphic `ℍ`-valued local isometry,
`u_z = (F'' / F' + i F' / Im F) / 2`, so two branches recovering the same
metric and sharing value and first derivative at a point have the same second
derivative there.
-/
def PointedRealMobiusTransitionMetricOneJetDeterminesSecondJetTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          (∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
            S₁.coefficient z = S₂.coefficient z) →
          ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
            H₂.upperHalfPlaneMap z =
                realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z) →
            deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z =
                deriv
                  (fun w : ℂ ↦
                    (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
                  z →
              deriv (fun w : ℂ ↦
                    deriv (fun t : ℂ ↦ (H₂.upperHalfPlaneMap t : ℂ)) w) z =
                deriv
                  (fun w : ℂ ↦
                    deriv
                      (fun t : ℂ ↦
                        (realMobiusRepresentativeAction A
                        (H₁.upperHalfPlaneMap t) : ℂ))
                      w)
                  z

/--
The first-Wirtinger expression attached to an upper-half-plane branch.

For a branch `F : U → ℍ` pulling back the Poincare metric to `e^{2u}|dz|²`,
this is the expected value of `u_z`.
-/
def localUpperHalfPlaneDevelopingMapFirstWirtingerExpression
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) (z : ℂ) : ℂ :=
  (deriv (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z /
    deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z +
    Complex.I * deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z /
      (((H.upperHalfPlaneMap z : ℂ).im : ℝ) : ℂ)) / 2

/--
The Schwarzian expression built from Lean's actual iterated complex
derivatives of a scalar map.
-/
def actualSchwarzian (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  schwarzianExpression
    (fun w : ℂ ↦ deriv f w)
    (fun w : ℂ ↦ deriv (fun t : ℂ ↦ deriv f t) w)
    (fun w : ℂ ↦
      deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) w)
    z

/--
The first-Wirtinger expression after postcomposing an upper-half-plane branch
by a real Mobius transformation.
-/
def realMobiusPostcompositionFirstWirtingerExpression
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S)
    (A : RealMobiusRepresentative) (z : ℂ) : ℂ :=
  (deriv
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
          w) z /
    deriv
      (fun w : ℂ ↦
        (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ)) z +
    Complex.I *
      deriv
        (fun w : ℂ ↦
          (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ)) z /
      ((((realMobiusRepresentativeAction A (H.upperHalfPlaneMap z) : ℍ) : ℂ).im : ℝ) :
        ℂ)) / 2

/--
Branch-level first-Wirtinger pullback formula.

This is the local analytic boundary obtained by differentiating the Poincare
pullback formula for a metric-recovering upper-half-plane branch.
-/
def LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) (z : ℂ),
      u.SolvesLiouvilleEquation →
        z ∈ H.domain →
          u.wirtingerZ z =
            localUpperHalfPlaneDevelopingMapFirstWirtingerExpression H z

/--
Squared-density derivative form of the branch-level first-Wirtinger pullback
formula.

This is the cleaner formula obtained before taking the logarithmic derivative
of `ρ = exp(2u)`: `∂z ρ = ρ (F''/F' + i F'/Im F)`.
-/
def LocalUpperHalfPlaneDevelopingMapDensitySqDerivativeFormulaTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) (z : ℂ),
      u.SolvesLiouvilleEquation →
        z ∈ H.domain →
          frechetDZValue (fun w : ℂ ↦ (u.densitySq w : ℂ)) z =
            (u.densitySq z : ℂ) *
              (deriv
                  (fun w : ℂ ↦
                    deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z /
                deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z +
                Complex.I * deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z /
                  (((H.upperHalfPlaneMap z : ℂ).im : ℝ) : ℂ))

/--
The squared-density derivative formula implies the logarithmic
first-Wirtinger formula.
-/
theorem localUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem_of_densitySqDerivative
    (hρ :
      LocalUpperHalfPlaneDevelopingMapDensitySqDerivativeFormulaTheorem) :
    LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem := by
  intro u S H z hu hz
  have hDomain : z ∈ u.coordinateDomain := H.projective.domain_subset hz
  have hlogDiff : DifferentiableAt ℝ u.logDensity z :=
    (u.logDensity_contDiffOn.differentiableOn (by norm_num) z hDomain).differentiableAt
      (u.isOpen_coordinateDomain.mem_nhds hDomain)
  have hDensityDiff : DifferentiableAt ℝ u.densitySq z := by
    simpa [LocalConformalFactor.densitySq] using
      ((hlogDiff.const_mul (2 : ℝ)).exp)
  rw [LocalConformalFactor.wirtingerZ]
  change frechetDZValue (fun w : ℂ ↦ (u.logDensity w : ℂ)) z =
    localUpperHalfPlaneDevelopingMapFirstWirtingerExpression H z
  rw [show (fun w : ℂ ↦ (u.logDensity w : ℂ)) =
      (fun w : ℂ ↦ (((1 / 2 : ℝ) * Real.log (u.densitySq w) : ℝ) : ℂ)) by
        ext w
        simp [LocalConformalFactor.densitySq]]
  rw [frechetDZValue_complex_ofReal_half_log_of_differentiableAt
    (ρ := u.densitySq) (z₀ := z) hDensityDiff (u.densitySq_pos z)]
  rw [hρ H z hu hz]
  have hρ_ne : (u.densitySq z : ℂ) ≠ 0 := by
    exact_mod_cast (u.densitySq_pos z).ne'
  dsimp [localUpperHalfPlaneDevelopingMapFirstWirtingerExpression]
  field_simp [hρ_ne]

/--
Real Mobius postcomposition preserves the first-Wirtinger pullback expression.

This isolates the hyperbolic-isometry calculation needed in the real-transition
uniqueness proof.
-/
def RealMobiusPostcompositionPreservesPullbackFirstWirtingerFormulaTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S)
    (A : RealMobiusRepresentative) (z : ℂ),
      u.SolvesLiouvilleEquation →
        z ∈ H.domain →
          u.wirtingerZ z =
            localUpperHalfPlaneDevelopingMapFirstWirtingerExpression H z →
            u.wirtingerZ z =
              realMobiusPostcompositionFirstWirtingerExpression H A z

/--
Pure expression invariance for the first-Wirtinger pullback term under real
Mobius postcomposition.

This is the remaining algebraic/chain-rule calculation behind
`RealMobiusPostcompositionPreservesPullbackFirstWirtingerFormulaTheorem`.
-/
def RealMobiusPostcompositionFirstWirtingerExpressionInvariantTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S)
    (A : RealMobiusRepresentative) (z : ℂ),
      z ∈ H.domain →
        realMobiusPostcompositionFirstWirtingerExpression H A z =
          localUpperHalfPlaneDevelopingMapFirstWirtingerExpression H z

/--
Second-derivative chain rule for postcomposition by a real Mobius map.

This is the genuine second-order calculus input needed for invariance of the
first-Wirtinger expression.
-/
def RealMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S)
    (A : RealMobiusRepresentative) (z : ℂ),
      z ∈ H.domain →
        deriv
          (fun w : ℂ ↦
            deriv
              (fun t : ℂ ↦
                (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
              w) z =
          deriv
            (fun w : ℂ ↦
              deriv
                (fun t : ℂ ↦
                  (realMobiusRepresentativeAction A
                    ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
                w)
            (H.upperHalfPlaneMap z) *
            deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z ^ 2 +
          deriv
            (fun w : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
            (H.upperHalfPlaneMap z) *
          deriv (fun w : ℂ ↦
              deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z

/--
Third-derivative chain rule for postcomposition by a real Mobius map.

Together with the already-proved first- and second-order chain rules, this is
the remaining calculus input needed to prove actual Schwarzian invariance by
the standard formula
`(M ∘ F)''' = M'''(F)(F')^3 + 3 M''(F)F'F'' + M'(F)F'''`.
-/
def RealMobiusBranchPostcompositionThirdDerivativeChainRuleTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S)
    (A : RealMobiusRepresentative) (z : ℂ),
      z ∈ H.domain →
        deriv
          (fun w : ℂ ↦
            deriv
              (fun t : ℂ ↦
                deriv
                  (fun s : ℂ ↦
                    (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
                  t)
              w) z =
          deriv
            (fun w : ℂ ↦
              deriv
                (fun t : ℂ ↦
                  deriv
                    (fun s : ℂ ↦
                      (realMobiusRepresentativeAction A
                        ((UpperHalfPlane.ofComplex : ℂ → ℍ) s) : ℂ))
                    t)
                w)
            (H.upperHalfPlaneMap z) *
              deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z ^ 3 +
          3 *
            deriv
              (fun w : ℂ ↦
                deriv
                  (fun t : ℂ ↦
                    (realMobiusRepresentativeAction A
                      ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
                  w)
              (H.upperHalfPlaneMap z) *
              deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z *
              deriv
                (fun w : ℂ ↦
                  deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z +
          deriv
            (fun w : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
            (H.upperHalfPlaneMap z) *
            deriv
              (fun w : ℂ ↦
                deriv
                  (fun t : ℂ ↦
                    deriv (fun s : ℂ ↦ (H.upperHalfPlaneMap s : ℂ)) t)
                  w) z

/--
Regularity of the derivative branch needed for the second-order
postcomposition chain rule.

The derivative value is written using Lean's actual `deriv`, so this is only
the assertion that the derivative branch is genuinely differentiable at the
point.
-/
def LocalUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) {z : ℂ},
      z ∈ H.domain →
        HasDerivAt
          (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w)
          (deriv (fun w : ℂ ↦
            deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z)
          z

/--
First-derivative regularity with the symbolic second derivative as derivative.

This stronger, more geometric form simultaneously supplies the differentiable
derivative-branch input and the second-derivative identification.
-/
def LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) {z : ℂ},
      z ∈ H.domain →
        HasDerivAt
          (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w)
          (H.projective.affineMapSecondDeriv z)
          z

/--
Second-derivative regularity with the symbolic third derivative as derivative.
-/
def LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) {z : ℂ},
      z ∈ H.domain →
        HasDerivAt
          (fun w : ℂ ↦
            deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ (H.upperHalfPlaneMap s : ℂ)) t) w)
          (H.projective.affineMapThirdDeriv z)
          z

/--
Projective-symbolic first-derivative regularity for upper-half-plane branches.

This is closer to the Frobenius construction: the symbolic affine derivative
field stored in the underlying projective branch has the stored symbolic
second derivative.
-/
def LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) {z : ℂ},
      z ∈ H.domain →
        HasDerivAt
          (fun w : ℂ ↦ H.projective.affineMapDeriv w)
          (H.projective.affineMapSecondDeriv z)
          z

/--
Projective-symbolic second-derivative regularity for upper-half-plane branches.
-/
def LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) {z : ℂ},
      z ∈ H.domain →
        HasDerivAt
          (fun w : ℂ ↦ H.projective.affineMapSecondDeriv w)
          (H.projective.affineMapThirdDeriv z)
          z

/--
Fixed-branch projective-symbolic derivative regularity.

This is the local version of the two global projective derivative interfaces:
it is the exact information produced for each branch in the strengthened
Frobenius normalization atlas.
-/
structure LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) : Prop where
  /-- The stored affine derivative has the stored second derivative. -/
  projectiveFirstDerivative_hasDerivAt :
    ∀ {z : ℂ}, z ∈ H.domain →
      HasDerivAt
        (fun w : ℂ ↦ H.projective.affineMapDeriv w)
        (H.projective.affineMapSecondDeriv z)
        z
  /-- The stored second derivative has the stored third derivative. -/
  projectiveSecondDerivative_hasDerivAt :
    ∀ {z : ℂ}, z ∈ H.domain →
      HasDerivAt
        (fun w : ℂ ↦ H.projective.affineMapSecondDeriv w)
        (H.projective.affineMapThirdDeriv z)
        z

namespace LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/-- Fixed-branch projective first-derivative regularity gives actual first-derivative regularity. -/
theorem firstDerivative_hasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    {z : ℂ} (hz : z ∈ H.domain) :
    HasDerivAt
      (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w)
      (H.projective.affineMapSecondDeriv z)
      z := by
  have hEq :
      (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w)
        =ᶠ[nhds z]
      (fun w : ℂ ↦ H.projective.affineMapDeriv w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    simpa using H.upperHalfPlane_deriv_eq_projectiveDeriv w hw
  exact (R.projectiveFirstDerivative_hasDerivAt hz).congr_of_eventuallyEq hEq

/--
Fixed-branch projective derivative regularity gives actual second-derivative
regularity.
-/
theorem secondDerivative_hasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    {z : ℂ} (hz : z ∈ H.domain) :
    HasDerivAt
      (fun w : ℂ ↦
        deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ (H.upperHalfPlaneMap s : ℂ)) t) w)
      (H.projective.affineMapThirdDeriv z)
      z := by
  have hEq :
      (fun w : ℂ ↦
        deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ (H.upperHalfPlaneMap s : ℂ)) t) w)
        =ᶠ[nhds z]
      (fun w : ℂ ↦ H.projective.affineMapSecondDeriv w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    exact (R.firstDerivative_hasDerivAt hw).deriv
  exact (R.projectiveSecondDerivative_hasDerivAt hz).congr_of_eventuallyEq hEq

/--
Fixed-branch projective derivative regularity gives the differentiability
interface for the actual derivative branch.
-/
theorem derivative_hasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    {z : ℂ} (hz : z ∈ H.domain) :
    HasDerivAt
      (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w)
      (deriv (fun w : ℂ ↦
        deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z)
      z := by
  have h := R.firstDerivative_hasDerivAt hz
  convert h using 1
  exact h.deriv

/-- Fixed-branch derivative regularity gives continuity of the stored affine derivative. -/
theorem affineDerivative_continuousOn
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H) :
    ContinuousOn (fun z : ℂ ↦ H.projective.affineMapDeriv z) H.domain := by
  have hActual :
      ContinuousOn
        (fun z : ℂ ↦ deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z)
        H.domain := by
    intro z hz
    exact (R.firstDerivative_hasDerivAt hz).continuousAt.continuousWithinAt
  exact hActual.congr (fun z hz ↦ by
    exact (H.upperHalfPlane_deriv_eq_projectiveDeriv z hz).symm)

end LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Coefficient-aware local uniqueness with only fixed-pair projective derivative
regularity.

This is the final local identity-principle shape needed by the derivative-data
normalization atlas: the two compared branches carry their own derivative
regularity data, rather than relying on a global theorem for every possible
upper-half-plane branch.
-/
def PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁ →
        LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂ →
          u.SolvesLiouvilleEquation →
            H₁.HasPointedRealMobiusTransition H₂ A z₀ →
              (∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
                S₁.coefficient z = S₂.coefficient z) →
              ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
                H₂.upperHalfPlaneMap z =
                    realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z) →
                deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z =
                    deriv
                      (fun w : ℂ ↦
                        (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
                      z →
                  ∃ U : Set ℂ,
                    IsOpen U ∧ z ∈ U ∧ U ⊆ H₁.domain ∩ H₂.domain ∧
                      ∀ w, w ∈ U →
                        H₂.upperHalfPlaneMap w =
                            realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) ∧
                        deriv (fun t : ℂ ↦ (H₂.upperHalfPlaneMap t : ℂ)) w =
                            deriv
                              (fun t : ℂ ↦
                                (realMobiusRepresentativeAction A
                                  (H₁.upperHalfPlaneMap t) : ℂ))
                              w

/--
Fixed-pair projective derivative regularity makes the one-jet equality locus
closed on the overlap.
-/
theorem pointedRealMobiusTransitionOneJetEqualitySet_isClosed_of_pairProjectiveDerivative
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (hu : u.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂) :
    IsClosed (pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A) := by
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  have hValue :
      Continuous
        (fun z : overlap ↦ H₂.upperHalfPlaneMap (z : ℂ)) ∧
      Continuous
        (fun z : overlap ↦
          realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap (z : ℂ))) :=
    pointedRealMobiusTransitionEqualitySetContinuityTheorem_of_branch_and_action_continuity
      localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem
      realMobiusRepresentativeActionContinuousTheorem
      H₁ H₂ A z₀ hu hpoint
  rcases hValue with ⟨h₂, hA⟩
  have hH₂DerivOnOverlap :
      ContinuousOn
        (fun z : ℂ ↦ deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z)
        overlap := by
    have hOn :
        ContinuousOn
          (fun z : ℂ ↦ deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z)
          H₂.domain :=
      R₂.affineDerivative_continuousOn.congr (fun z hz ↦ by
        exact H₂.upperHalfPlane_deriv_eq_projectiveDeriv z hz)
    exact hOn.mono (fun z hz ↦ hz.2)
  have hd₂ :
      Continuous
        (fun z : overlap ↦
          deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (z : ℂ)) := by
    simpa [Set.restrict] using
      (continuousOn_iff_continuous_restrict.mp hH₂DerivOnOverlap)
  let toH₁Domain : overlap → {z : ℂ // z ∈ H₁.domain} :=
    fun z ↦ ⟨(z : ℂ), z.property.1⟩
  have htoH₁ : Continuous toH₁Domain := by
    exact continuous_subtype_val.subtype_mk (fun z ↦ z.property.1)
  have hH₁ :
      Continuous (fun z : overlap ↦ H₁.upperHalfPlaneMap (z : ℂ)) := by
    simpa [toH₁Domain] using
      (localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem H₁).comp htoH₁
  have hfactor :
      Continuous
        (fun z : overlap ↦
          deriv
            (fun w : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
            (H₁.upperHalfPlaneMap (z : ℂ))) :=
    (realMobiusRepresentativeAction_deriv_continuous A).comp hH₁
  have hH₁DerivOnOverlap :
      ContinuousOn
        (fun z : ℂ ↦ deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ)) z)
        overlap := by
    have hOn :
        ContinuousOn
          (fun z : ℂ ↦ deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ)) z)
          H₁.domain :=
      R₁.affineDerivative_continuousOn.congr (fun z hz ↦ by
        exact H₁.upperHalfPlane_deriv_eq_projectiveDeriv z hz)
    exact hOn.mono (fun z hz ↦ hz.1)
  have hbranchDeriv :
      Continuous
        (fun z : overlap ↦
          deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ)) (z : ℂ)) := by
    simpa [Set.restrict] using
      (continuousOn_iff_continuous_restrict.mp hH₁DerivOnOverlap)
  have hprod :
      Continuous
        (fun z : overlap ↦
          deriv
            (fun w : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
            (H₁.upperHalfPlaneMap (z : ℂ)) *
          deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ)) (z : ℂ)) :=
    hfactor.mul hbranchDeriv
  have htarget_eq :
      (fun z : overlap ↦
        deriv
          (fun w : ℂ ↦
            (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
          (z : ℂ))
      =
      (fun z : overlap ↦
        deriv
          (fun w : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
          (H₁.upperHalfPlaneMap (z : ℂ)) *
        deriv (fun w : ℂ ↦ (H₁.upperHalfPlaneMap w : ℂ)) (z : ℂ)) := by
    funext z
    exact realMobiusBranchPostcompositionDerivativeChainRuleTheorem H₁ A z.property.1
  have hdA :
      Continuous
        (fun z : overlap ↦
          deriv
            (fun w : ℂ ↦
              (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
            (z : ℂ)) := by
    rw [htarget_eq]
    exact hprod
  have hValueClosed :
      IsClosed
        {z : overlap |
          H₂.upperHalfPlaneMap (z : ℂ) =
            realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap (z : ℂ))} :=
    isClosed_eq h₂ hA
  have hDerivClosed :
      IsClosed
        {z : overlap |
          deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) (z : ℂ) =
            deriv
              (fun w : ℂ ↦
                (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
              (z : ℂ)} :=
    isClosed_eq hd₂ hdA
  simpa [pointedRealMobiusTransitionOneJetEqualitySet, Set.setOf_and] using
    hValueClosed.inter hDerivClosed

/--
For one fixed pair of branches, coefficient agreement and the pair-shaped
local uniqueness theorem make the one-jet equality locus open.
-/
theorem pointedRealMobiusTransitionOneJetEqualitySet_isOpen_of_pairProjectiveDerivative_coefficientAgreement
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (hu : u.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem) :
    IsOpen (pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A) := by
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  let E : Set overlap := pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A
  rw [isOpen_iff_forall_mem_open]
  intro z hzE
  rcases hUnique H₁ H₂ A z₀ R₁ R₂ hu hpoint hCoeff (z : ℂ)
      z.property.1 z.property.2 hzE.1 hzE.2 with
    ⟨U, hUopen, hzU, hUsubset, hUeq⟩
  refine ⟨Subtype.val ⁻¹' U, ?_, hUopen.preimage continuous_subtype_val, hzU⟩
  intro y hy
  exact hUeq (y : ℂ) hy

/--
Fixed-pair connected-overlap extension from projective derivative regularity,
coefficient agreement, and the pair-shaped local uniqueness theorem.
-/
theorem pointedRealMobiusTransition_extendsOnPreconnectedOverlap_of_pairProjectiveDerivative_coefficientAgreement
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem)
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : u.SolvesLiouvilleEquation)
    (hconn : IsPreconnected (H₁.domain ∩ H₂.domain))
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z) :
    ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
      H₂.upperHalfPlaneMap z =
        realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z) := by
  intro z hz₁ hz₂
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  let E : Set overlap := pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A
  haveI : PreconnectedSpace overlap := Subtype.preconnectedSpace hconn
  have hClosed : IsClosed E :=
    pointedRealMobiusTransitionOneJetEqualitySet_isClosed_of_pairProjectiveDerivative
      H₁ H₂ A z₀ hu hpoint R₁ R₂
  have hOpen : IsOpen E :=
    pointedRealMobiusTransitionOneJetEqualitySet_isOpen_of_pairProjectiveDerivative_coefficientAgreement
      H₁ H₂ A z₀ hu hpoint R₁ R₂ hCoeff hUnique
  have hE : IsClopen E := ⟨hClosed, hOpen⟩
  have hbase_mem_overlap : z₀ ∈ overlap := ⟨hpoint.1, hpoint.2.1⟩
  have hbase_mem_E : (⟨z₀, hbase_mem_overlap⟩ : overlap) ∈ E := by
    simpa [E, pointedRealMobiusTransitionOneJetEqualitySet] using hpoint.2.2
  have hE_univ : E = Set.univ :=
    IsClopen.eq_univ hE ⟨⟨z₀, hbase_mem_overlap⟩, hbase_mem_E⟩
  have hz_mem_overlap : z ∈ overlap := ⟨hz₁, hz₂⟩
  have hz_mem_E : (⟨z, hz_mem_overlap⟩ : overlap) ∈ E := by
    rw [hE_univ]
    exact Set.mem_univ _
  exact hz_mem_E.1

/--
%%handwave
name:
  Extension of a real Möbius comparison across an overlap
statement:
  Let $F_1,F_2$ be regular local maps to $\mathbb H$ on domains whose
  intersection $W$ is preconnected. Suppose their Schwarzian coefficients
  agree on $W$, and that for some $A\in\mathrm{PSL}_2(\mathbb R)$ the maps
  $F_2$ and $A\circ F_1$ have the same value and first derivative at
  $z_0\in W$. If equality of these one-jets propagates locally, then
  $$F_2=A\circ F_1$$
  throughout $W$, with equality of first derivatives as well.
proof:
  The locus in $W$ where both the values and first derivatives agree is
  nonempty. Derivative regularity makes it closed, while the local
  Schwarzian identity principle makes it open. Preconnectedness therefore
  forces this locus to be all of $W$.
-/
theorem pointedRealMobiusTransition_oneJetExtendsOnPreconnectedOverlap_of_pairProjectiveDerivative_coefficientAgreement
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem)
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (R₁ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₁)
    (R₂ : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H₂)
    (hu : u.SolvesLiouvilleEquation)
    (hconn : IsPreconnected (H₁.domain ∩ H₂.domain))
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z) :
    ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
      H₂.upperHalfPlaneMap z =
          realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z) ∧
        deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z =
          deriv
            (fun w : ℂ ↦
              (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
            z := by
  intro z hz₁ hz₂
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  let E : Set overlap := pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A
  haveI : PreconnectedSpace overlap := Subtype.preconnectedSpace hconn
  have hClosed : IsClosed E :=
    pointedRealMobiusTransitionOneJetEqualitySet_isClosed_of_pairProjectiveDerivative
      H₁ H₂ A z₀ hu hpoint R₁ R₂
  have hOpen : IsOpen E :=
    pointedRealMobiusTransitionOneJetEqualitySet_isOpen_of_pairProjectiveDerivative_coefficientAgreement
      H₁ H₂ A z₀ hu hpoint R₁ R₂ hCoeff hUnique
  have hE : IsClopen E := ⟨hClosed, hOpen⟩
  have hbase_mem_overlap : z₀ ∈ overlap := ⟨hpoint.1, hpoint.2.1⟩
  have hbase_mem_E : (⟨z₀, hbase_mem_overlap⟩ : overlap) ∈ E := by
    simpa [E, pointedRealMobiusTransitionOneJetEqualitySet] using hpoint.2.2
  have hE_univ : E = Set.univ :=
    IsClopen.eq_univ hE ⟨⟨z₀, hbase_mem_overlap⟩, hbase_mem_E⟩
  have hz_mem_overlap : z ∈ overlap := ⟨hz₁, hz₂⟩
  have hz_mem_E : (⟨z, hz_mem_overlap⟩ : overlap) ∈ E := by
    rw [hE_univ]
    exact Set.mem_univ _
  simpa [E, pointedRealMobiusTransitionOneJetEqualitySet] using hz_mem_E

/--
Projective-symbolic first-derivative regularity implies the actual
first-derivative regularity of the upper-half-plane branch.
-/
theorem localUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem_of_projectiveFirstDerivative
    (hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem) :
    LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem := by
  intro u S H z hz
  have hEq :
      (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w)
        =ᶠ[nhds z]
      (fun w : ℂ ↦ H.projective.affineMapDeriv w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    simpa using H.upperHalfPlane_deriv_eq_projectiveDeriv w hw
  exact (hProjFirst H hz).congr_of_eventuallyEq hEq

/--
Projective-symbolic second-derivative regularity, together with the
projective-symbolic first-derivative bridge, implies actual second-derivative
regularity of the upper-half-plane branch.
-/
theorem localUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem_of_projectiveFirstSecondDerivative
    (hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem)
    (hProjSecond :
      LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem) :
    LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem := by
  intro u S H z hz
  have hFirst : LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem :=
    localUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem_of_projectiveFirstDerivative
      hProjFirst
  have hEq :
      (fun w : ℂ ↦
        deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ (H.upperHalfPlaneMap s : ℂ)) t) w)
        =ᶠ[nhds z]
      (fun w : ℂ ↦ H.projective.affineMapSecondDeriv w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    exact (hFirst H hw).deriv
  exact (hProjSecond H hz).congr_of_eventuallyEq hEq

/--
The stronger first-derivative regularity package implies the derivative
branch differentiability interface used in the real-Mobius second-order chain
rule.
-/
theorem localUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem_of_firstDerivative
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem) :
    LocalUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem := by
  intro u S H z hz
  have h := hFirst H hz
  rw [h.deriv]
  exact h

/--
First-derivative regularity makes the stored affine derivative continuous on
the branch domain.
-/
theorem localUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem_of_firstDerivative
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem) :
    LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem := by
  intro u S H
  have hActual :
      ContinuousOn
        (fun z : ℂ ↦ deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z)
        H.domain := by
    intro z hz
    exact (hFirst H hz).continuousAt.continuousWithinAt
  exact hActual.congr (fun z hz ↦ by
    exact (H.upperHalfPlane_deriv_eq_projectiveDeriv z hz).symm)

/--
The second-order real-Mobius branch chain rule follows from differentiability
of the branch derivative.
-/
theorem realMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem_of_branchDerivativeHasDerivAt
    (hBranchDeriv :
      LocalUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem) :
    RealMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem := by
  intro u S H A z hz
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let M' : ℂ → ℂ := fun w ↦ deriv M w
  let F' : ℂ → ℂ := fun w ↦ deriv F w
  let F₁ : ℂ := deriv F z
  let F₂ : ℂ := deriv F' z
  let α : ℂ := deriv M (F z)
  let β : ℂ := deriv M' (F z)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hF : HasDerivAt F F₁ z :=
    (differentiableAt_of_deriv_ne_zero hF₁_ne).hasDerivAt
  have hM' : HasDerivAt M' β (F z) := by
    have h :=
      realMobiusRepresentativeAction_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hβ := realMobiusRepresentativeAction_second_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', F, β] using hβ.symm)
  have hM'comp : HasDerivAt (fun w ↦ M' (F w)) (β * F₁) z :=
    hM'.comp z hF
  have hF' : HasDerivAt F' F₂ z := by
    simpa [F', F₂, F] using hBranchDeriv H hz
  have hprod :
      HasDerivAt (fun w ↦ M' (F w) * F' w)
        (β * F₁ ^ 2 + α * F₂) z := by
    have h := hM'comp.mul hF'
    convert h using 1
    simp [F₁, F₂, α, F', M']
    ring
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
          w) =ᶠ[nhds z]
        (fun w : ℂ ↦ M' (F w) * F' w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    simpa [F, F', M, M'] using
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H A hw
  calc
    deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
            w) z =
        deriv (fun w : ℂ ↦ M' (F w) * F' w) z := hEq.deriv_eq
    _ = β * F₁ ^ 2 + α * F₂ := hprod.deriv

namespace LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Fixed-branch projective derivative regularity gives the second-order chain
rule for postcomposition by a real Mobius transformation.
-/
theorem realMobiusPostcompositionSecondDerivativeChainRule
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    deriv
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
          w) z =
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
            w)
        (H.upperHalfPlaneMap z) *
        deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z ^ 2 +
      deriv
        (fun w : ℂ ↦
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
        (H.upperHalfPlaneMap z) *
      deriv (fun w : ℂ ↦
          deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z := by
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let M' : ℂ → ℂ := fun w ↦ deriv M w
  let F' : ℂ → ℂ := fun w ↦ deriv F w
  let F₁ : ℂ := deriv F z
  let F₂ : ℂ := deriv F' z
  let α : ℂ := deriv M (F z)
  let β : ℂ := deriv M' (F z)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hF : HasDerivAt F F₁ z :=
    (differentiableAt_of_deriv_ne_zero hF₁_ne).hasDerivAt
  have hM' : HasDerivAt M' β (F z) := by
    have h :=
      realMobiusRepresentativeAction_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hβ := realMobiusRepresentativeAction_second_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', F, β] using hβ.symm)
  have hM'comp : HasDerivAt (fun w ↦ M' (F w)) (β * F₁) z :=
    hM'.comp z hF
  have hF' : HasDerivAt F' F₂ z := by
    simpa [F', F₂, F] using R.derivative_hasDerivAt hz
  have hprod :
      HasDerivAt (fun w ↦ M' (F w) * F' w)
        (β * F₁ ^ 2 + α * F₂) z := by
    have h := hM'comp.mul hF'
    convert h using 1
    simp [F₁, F₂, α, F', M']
    ring
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
          w) =ᶠ[nhds z]
        (fun w : ℂ ↦ M' (F w) * F' w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    simpa [F, F', M, M'] using
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H A hw
  calc
    deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
            w) z =
        deriv (fun w : ℂ ↦ M' (F w) * F' w) z := hEq.deriv_eq
    _ = β * F₁ ^ 2 + α * F₂ := hprod.deriv

end LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
The third-order real-Mobius branch chain rule follows from first- and
second-derivative regularity of the upper-half-plane branch.
-/
theorem realMobiusBranchPostcompositionThirdDerivativeChainRuleTheorem_of_first_secondDerivative
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecond :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem) :
    RealMobiusBranchPostcompositionThirdDerivativeChainRuleTheorem := by
  intro u S H A z hz
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let G : ℂ → ℂ :=
    fun w ↦ (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ)
  let M' : ℂ → ℂ := fun w ↦ deriv M w
  let M'' : ℂ → ℂ := fun w ↦ deriv M' w
  let F' : ℂ → ℂ := fun w ↦ deriv F w
  let F'' : ℂ → ℂ := fun w ↦ deriv F' w
  let F₁ : ℂ := deriv F z
  let F₂ : ℂ := deriv F' z
  let F₃ : ℂ := deriv F'' z
  let α : ℂ := deriv M (F z)
  let β : ℂ := deriv M' (F z)
  let γ : ℂ := deriv M'' (F z)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hF : HasDerivAt F F₁ z :=
    (differentiableAt_of_deriv_ne_zero hF₁_ne).hasDerivAt
  have hF' : HasDerivAt F' F₂ z := by
    have h := hFirst H hz
    convert h using 1
    exact h.deriv
  have hF'' : HasDerivAt F'' F₃ z := by
    have h := hSecond H hz
    convert h using 1
    exact h.deriv
  have hM' : HasDerivAt M' β (F z) := by
    have h :=
      realMobiusRepresentativeAction_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hβ := realMobiusRepresentativeAction_second_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', F, β] using hβ.symm)
  have hM'' : HasDerivAt M'' γ (F z) := by
    have h :=
      realMobiusRepresentativeAction_second_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hγ := realMobiusRepresentativeAction_third_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', M'', F, γ] using hγ.symm)
  have hterm₁ :
      HasDerivAt (fun w ↦ M'' (F w) * F' w ^ 2)
        (γ * F₁ ^ 3 + 2 * β * F₁ * F₂) z := by
    have hM''comp : HasDerivAt (fun w ↦ M'' (F w)) (γ * F₁) z :=
      hM''.comp z hF
    have hF'sq : HasDerivAt (fun w ↦ F' w ^ 2) (2 * F₁ * F₂) z := by
      simpa [F₁, F₂, pow_one, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm]
        using hF'.pow 2
    have h := hM''comp.mul hF'sq
    convert h using 1
    ring
  have hterm₂ :
      HasDerivAt (fun w ↦ M' (F w) * F'' w)
        (β * F₁ * F₂ + α * F₃) z := by
    have hM'comp : HasDerivAt (fun w ↦ M' (F w)) (β * F₁) z :=
      hM'.comp z hF
    have h := hM'comp.mul hF''
    convert h using 1
  have hsum :
      HasDerivAt
        (fun w ↦ M'' (F w) * F' w ^ 2 + M' (F w) * F'' w)
        (γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃) z := by
    have h := hterm₁.add hterm₂
    convert h using 1
    ring
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            deriv
              (fun s : ℂ ↦
                (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
              t)
          w) =ᶠ[nhds z]
        (fun w : ℂ ↦ M'' (F w) * F' w ^ 2 + M' (F w) * F'' w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    simpa [G, M, M', M'', F, F', F''] using
      (realMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem_of_branchDerivativeHasDerivAt
        (localUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem_of_firstDerivative
          hFirst)) H A w hw
  calc
    deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              deriv
                (fun s : ℂ ↦
                  (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
                t)
            w)
        z =
        deriv (fun w : ℂ ↦ M'' (F w) * F' w ^ 2 + M' (F w) * F'' w) z :=
      hEq.deriv_eq
    _ = γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃ := hsum.deriv

namespace LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Fixed-branch projective derivative regularity gives the third-order chain rule
for postcomposition by a real Mobius transformation.
-/
theorem realMobiusPostcompositionThirdDerivativeChainRule
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    deriv
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            deriv
              (fun s : ℂ ↦
                (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
              t)
          w) z =
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              deriv
                (fun s : ℂ ↦
                  (realMobiusRepresentativeAction A
                    ((UpperHalfPlane.ofComplex : ℂ → ℍ) s) : ℂ))
                t)
            w)
        (H.upperHalfPlaneMap z) *
          deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z ^ 3 +
      3 *
        deriv
          (fun w : ℂ ↦
            deriv
              (fun t : ℂ ↦
                (realMobiusRepresentativeAction A
                  ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
              w)
          (H.upperHalfPlaneMap z) *
          deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z *
          deriv
            (fun w : ℂ ↦
              deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z +
      deriv
        (fun w : ℂ ↦
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
        (H.upperHalfPlaneMap z) *
        deriv
          (fun w : ℂ ↦
            deriv
              (fun t : ℂ ↦
                deriv (fun s : ℂ ↦ (H.upperHalfPlaneMap s : ℂ)) t)
              w) z := by
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let G : ℂ → ℂ :=
    fun w ↦ (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ)
  let M' : ℂ → ℂ := fun w ↦ deriv M w
  let M'' : ℂ → ℂ := fun w ↦ deriv M' w
  let F' : ℂ → ℂ := fun w ↦ deriv F w
  let F'' : ℂ → ℂ := fun w ↦ deriv F' w
  let F₁ : ℂ := deriv F z
  let F₂ : ℂ := deriv F' z
  let F₃ : ℂ := deriv F'' z
  let α : ℂ := deriv M (F z)
  let β : ℂ := deriv M' (F z)
  let γ : ℂ := deriv M'' (F z)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hF : HasDerivAt F F₁ z :=
    (differentiableAt_of_deriv_ne_zero hF₁_ne).hasDerivAt
  have hF' : HasDerivAt F' F₂ z := by
    simpa [F', F₂, F] using R.derivative_hasDerivAt hz
  have hF'' : HasDerivAt F'' F₃ z := by
    have h := R.secondDerivative_hasDerivAt hz
    convert h using 1
    exact h.deriv
  have hM' : HasDerivAt M' β (F z) := by
    have h :=
      realMobiusRepresentativeAction_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hβ := realMobiusRepresentativeAction_second_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', F, β] using hβ.symm)
  have hM'' : HasDerivAt M'' γ (F z) := by
    have h :=
      realMobiusRepresentativeAction_second_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hγ := realMobiusRepresentativeAction_third_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', M'', F, γ] using hγ.symm)
  have hterm₁ :
      HasDerivAt (fun w ↦ M'' (F w) * F' w ^ 2)
        (γ * F₁ ^ 3 + 2 * β * F₁ * F₂) z := by
    have hM''comp : HasDerivAt (fun w ↦ M'' (F w)) (γ * F₁) z :=
      hM''.comp z hF
    have hF'sq : HasDerivAt (fun w ↦ F' w ^ 2) (2 * F₁ * F₂) z := by
      simpa [F₁, F₂, pow_one, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm]
        using hF'.pow 2
    have h := hM''comp.mul hF'sq
    convert h using 1
    ring
  have hterm₂ :
      HasDerivAt (fun w ↦ M' (F w) * F'' w)
        (β * F₁ * F₂ + α * F₃) z := by
    have hM'comp : HasDerivAt (fun w ↦ M' (F w)) (β * F₁) z :=
      hM'.comp z hF
    have h := hM'comp.mul hF''
    convert h using 1
  have hsum :
      HasDerivAt
        (fun w ↦ M'' (F w) * F' w ^ 2 + M' (F w) * F'' w)
        (γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃) z := by
    have h := hterm₁.add hterm₂
    convert h using 1
    ring
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            deriv
              (fun s : ℂ ↦
                (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
              t)
          w) =ᶠ[nhds z]
        (fun w : ℂ ↦ M'' (F w) * F' w ^ 2 + M' (F w) * F'' w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    simpa [G, M, M', M'', F, F', F''] using
      R.realMobiusPostcompositionSecondDerivativeChainRule A hw
  calc
    deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              deriv
                (fun s : ℂ ↦
                  (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
                t)
            w)
        z =
        deriv (fun w : ℂ ↦ M'' (F w) * F' w ^ 2 + M' (F w) * F'' w) z :=
      hEq.deriv_eq
    _ = γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃ := hsum.deriv

end LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
First derivative regularity for a real-Mobius postcomposition of an
upper-half-plane branch.
-/
theorem realMobiusPostcompositionFirstDerivativeHasDerivAt_of_firstDerivative
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    HasDerivAt
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
          w)
      (deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
            w)
        z)
      z := by
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let M' : ℂ → ℂ := fun w ↦ deriv M w
  let F' : ℂ → ℂ := fun w ↦ deriv F w
  let F₁ : ℂ := deriv F z
  let F₂ : ℂ := deriv F' z
  let α : ℂ := deriv M (F z)
  let β : ℂ := deriv M' (F z)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hF : HasDerivAt F F₁ z :=
    (differentiableAt_of_deriv_ne_zero hF₁_ne).hasDerivAt
  have hM' : HasDerivAt M' β (F z) := by
    have h :=
      realMobiusRepresentativeAction_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hβ := realMobiusRepresentativeAction_second_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', F, β] using hβ.symm)
  have hM'comp : HasDerivAt (fun w ↦ M' (F w)) (β * F₁) z :=
    hM'.comp z hF
  have hF' : HasDerivAt F' F₂ z := by
    have h := hFirst H hz
    convert h using 1
    exact h.deriv
  have hprod :
      HasDerivAt (fun w ↦ M' (F w) * F' w)
        (β * F₁ ^ 2 + α * F₂) z := by
    have h := hM'comp.mul hF'
    convert h using 1
    ring
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
          w) =ᶠ[nhds z]
        (fun w : ℂ ↦ M' (F w) * F' w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    simpa [F, F', M, M'] using
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H A hw
  have hactual :
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
            w)
        z =
        β * F₁ ^ 2 + α * F₂ := by
    simpa [β, α, F₁, F₂, F, M, M'] using
      (realMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem_of_branchDerivativeHasDerivAt
        (localUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem_of_firstDerivative
          hFirst)) H A z hz
  exact (hprod.congr_of_eventuallyEq hEq).congr_deriv hactual.symm

/--
Second derivative regularity for a real-Mobius postcomposition of an
upper-half-plane branch.
-/
theorem realMobiusPostcompositionSecondDerivativeHasDerivAt_of_first_secondDerivative
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecond :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem)
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    HasDerivAt
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            deriv
              (fun s : ℂ ↦
                (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
              t)
          w)
      (deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              deriv
                (fun s : ℂ ↦
                  (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
                t)
            w)
        z)
      z := by
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let M' : ℂ → ℂ := fun w ↦ deriv M w
  let M'' : ℂ → ℂ := fun w ↦ deriv M' w
  let F' : ℂ → ℂ := fun w ↦ deriv F w
  let F'' : ℂ → ℂ := fun w ↦ deriv F' w
  let F₁ : ℂ := deriv F z
  let F₂ : ℂ := deriv F' z
  let F₃ : ℂ := deriv F'' z
  let α : ℂ := deriv M (F z)
  let β : ℂ := deriv M' (F z)
  let γ : ℂ := deriv M'' (F z)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hF : HasDerivAt F F₁ z :=
    (differentiableAt_of_deriv_ne_zero hF₁_ne).hasDerivAt
  have hF' : HasDerivAt F' F₂ z := by
    have h := hFirst H hz
    convert h using 1
    exact h.deriv
  have hF'' : HasDerivAt F'' F₃ z := by
    have h := hSecond H hz
    convert h using 1
    exact h.deriv
  have hM' : HasDerivAt M' β (F z) := by
    have h :=
      realMobiusRepresentativeAction_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hβ := realMobiusRepresentativeAction_second_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', F, β] using hβ.symm)
  have hM'' : HasDerivAt M'' γ (F z) := by
    have h :=
      realMobiusRepresentativeAction_second_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hγ := realMobiusRepresentativeAction_third_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', M'', F, γ] using hγ.symm)
  have hterm₁ :
      HasDerivAt (fun w ↦ M'' (F w) * F' w ^ 2)
        (γ * F₁ ^ 3 + 2 * β * F₁ * F₂) z := by
    have hM''comp : HasDerivAt (fun w ↦ M'' (F w)) (γ * F₁) z :=
      hM''.comp z hF
    have hF'sq : HasDerivAt (fun w ↦ F' w ^ 2) (2 * F₁ * F₂) z := by
      simpa [F₁, F₂, pow_one, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm]
        using hF'.pow 2
    have h := hM''comp.mul hF'sq
    convert h using 1
    ring
  have hterm₂ :
      HasDerivAt (fun w ↦ M' (F w) * F'' w)
        (β * F₁ * F₂ + α * F₃) z := by
    have hM'comp : HasDerivAt (fun w ↦ M' (F w)) (β * F₁) z :=
      hM'.comp z hF
    have h := hM'comp.mul hF''
    convert h using 1
  have hsum :
      HasDerivAt
        (fun w ↦ M'' (F w) * F' w ^ 2 + M' (F w) * F'' w)
        (γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃) z := by
    have h := hterm₁.add hterm₂
    convert h using 1
    ring
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            deriv
              (fun s : ℂ ↦
                (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
              t)
          w) =ᶠ[nhds z]
        (fun w : ℂ ↦ M'' (F w) * F' w ^ 2 + M' (F w) * F'' w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    simpa [M, M', M'', F, F', F''] using
      (realMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem_of_branchDerivativeHasDerivAt
        (localUpperHalfPlaneDevelopingMapDerivativeHasDerivAtTheorem_of_firstDerivative
          hFirst)) H A w hw
  have hactual :
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              deriv
                (fun s : ℂ ↦
                  (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
                t)
            w)
        z =
        γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃ := by
    simpa [M, M', M'', F, F', F'', γ, β, α, F₁, F₂, F₃] using
      (realMobiusBranchPostcompositionThirdDerivativeChainRuleTheorem_of_first_secondDerivative
        hFirst hSecond) H A z hz
  exact (hsum.congr_of_eventuallyEq hEq).congr_deriv hactual.symm

namespace LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Fixed-branch projective derivative regularity gives first-derivative
regularity for a real-Mobius postcomposition.
-/
theorem realMobiusPostcomposition_firstDerivativeHasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    HasDerivAt
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
          w)
      (deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
            w)
        z)
      z := by
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let M' : ℂ → ℂ := fun w ↦ deriv M w
  let F' : ℂ → ℂ := fun w ↦ deriv F w
  let F₁ : ℂ := deriv F z
  let F₂ : ℂ := deriv F' z
  let α : ℂ := deriv M (F z)
  let β : ℂ := deriv M' (F z)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hF : HasDerivAt F F₁ z :=
    (differentiableAt_of_deriv_ne_zero hF₁_ne).hasDerivAt
  have hM' : HasDerivAt M' β (F z) := by
    have h :=
      realMobiusRepresentativeAction_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hβ := realMobiusRepresentativeAction_second_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', F, β] using hβ.symm)
  have hM'comp : HasDerivAt (fun w ↦ M' (F w)) (β * F₁) z :=
    hM'.comp z hF
  have hF' : HasDerivAt F' F₂ z := by
    simpa [F', F₂, F] using R.derivative_hasDerivAt hz
  have hprod :
      HasDerivAt (fun w ↦ M' (F w) * F' w)
        (β * F₁ ^ 2 + α * F₂) z := by
    have h := hM'comp.mul hF'
    convert h using 1
    ring
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
          w) =ᶠ[nhds z]
        (fun w : ℂ ↦ M' (F w) * F' w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    simpa [F, F', M, M'] using
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H A hw
  have hactual :
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
            w)
        z =
        β * F₁ ^ 2 + α * F₂ := by
    simpa [β, α, F₁, F₂, F, M, M'] using
      R.realMobiusPostcompositionSecondDerivativeChainRule A hz
  exact (hprod.congr_of_eventuallyEq hEq).congr_deriv hactual.symm

/--
Fixed-branch projective derivative regularity gives second-derivative
regularity for a real-Mobius postcomposition.
-/
theorem realMobiusPostcomposition_secondDerivativeHasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    HasDerivAt
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            deriv
              (fun s : ℂ ↦
                (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
              t)
          w)
      (deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              deriv
                (fun s : ℂ ↦
                  (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
                t)
            w)
        z)
      z := by
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let M' : ℂ → ℂ := fun w ↦ deriv M w
  let M'' : ℂ → ℂ := fun w ↦ deriv M' w
  let F' : ℂ → ℂ := fun w ↦ deriv F w
  let F'' : ℂ → ℂ := fun w ↦ deriv F' w
  let F₁ : ℂ := deriv F z
  let F₂ : ℂ := deriv F' z
  let F₃ : ℂ := deriv F'' z
  let α : ℂ := deriv M (F z)
  let β : ℂ := deriv M' (F z)
  let γ : ℂ := deriv M'' (F z)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hF : HasDerivAt F F₁ z :=
    (differentiableAt_of_deriv_ne_zero hF₁_ne).hasDerivAt
  have hF' : HasDerivAt F' F₂ z := by
    simpa [F', F₂, F] using R.derivative_hasDerivAt hz
  have hF'' : HasDerivAt F'' F₃ z := by
    have h := R.secondDerivative_hasDerivAt hz
    convert h using 1
    exact h.deriv
  have hM' : HasDerivAt M' β (F z) := by
    have h :=
      realMobiusRepresentativeAction_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hβ := realMobiusRepresentativeAction_second_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', F, β] using hβ.symm)
  have hM'' : HasDerivAt M'' γ (F z) := by
    have h :=
      realMobiusRepresentativeAction_second_deriv_hasDerivAt A (H.upperHalfPlaneMap z)
    have hγ := realMobiusRepresentativeAction_third_deriv A (H.upperHalfPlaneMap z)
    exact h.congr_deriv (by simpa [M, M', M'', F, γ] using hγ.symm)
  have hterm₁ :
      HasDerivAt (fun w ↦ M'' (F w) * F' w ^ 2)
        (γ * F₁ ^ 3 + 2 * β * F₁ * F₂) z := by
    have hM''comp : HasDerivAt (fun w ↦ M'' (F w)) (γ * F₁) z :=
      hM''.comp z hF
    have hF'sq : HasDerivAt (fun w ↦ F' w ^ 2) (2 * F₁ * F₂) z := by
      simpa [F₁, F₂, pow_one, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm]
        using hF'.pow 2
    have h := hM''comp.mul hF'sq
    convert h using 1
    ring
  have hterm₂ :
      HasDerivAt (fun w ↦ M' (F w) * F'' w)
        (β * F₁ * F₂ + α * F₃) z := by
    have hM'comp : HasDerivAt (fun w ↦ M' (F w)) (β * F₁) z :=
      hM'.comp z hF
    have h := hM'comp.mul hF''
    convert h using 1
  have hsum :
      HasDerivAt
        (fun w ↦ M'' (F w) * F' w ^ 2 + M' (F w) * F'' w)
        (γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃) z := by
    have h := hterm₁.add hterm₂
    convert h using 1
    ring
  have hEq :
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            deriv
              (fun s : ℂ ↦
                (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
              t)
          w) =ᶠ[nhds z]
        (fun w : ℂ ↦ M'' (F w) * F' w ^ 2 + M' (F w) * F'' w) := by
    filter_upwards [H.projective.isOpen_domain.mem_nhds hz] with w hw
    simpa [M, M', M'', F, F', F''] using
      R.realMobiusPostcompositionSecondDerivativeChainRule A hw
  have hactual :
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              deriv
                (fun s : ℂ ↦
                  (realMobiusRepresentativeAction A (H.upperHalfPlaneMap s) : ℂ))
                t)
            w)
        z =
        γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃ := by
    simpa [M, M', M'', F, F', F'', γ, β, α, F₁, F₂, F₃] using
      R.realMobiusPostcompositionThirdDerivativeChainRule A hz
  exact (hsum.congr_of_eventuallyEq hEq).congr_deriv hactual.symm

end LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
The one-variable identity saying that the Poincare first-Wirtinger expression
is invariant under a fixed real Mobius map.
-/
def RealMobiusFirstWirtingerMultiplierIdentityTheorem : Prop :=
  ∀ (A : RealMobiusRepresentative) (p : ℍ),
    let α : ℂ :=
      deriv
        (fun w : ℂ ↦
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
        p
    let β : ℂ :=
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
            w)
        p
    β / α + Complex.I * α /
      ((((realMobiusRepresentativeAction A p : ℍ) : ℂ).im : ℝ) : ℂ) =
        Complex.I / ((((p : ℍ) : ℂ).im : ℝ) : ℂ)

/--
Pure denominator algebra form of the real-Mobius first-Wirtinger multiplier
identity.

The analytic inputs `m'(z) = (cz+d)^{-2}`, `m''(z) = -2c(cz+d)^{-3}`, and
`Im(mz) = Im(z)/|cz+d|²` are proved separately; this target is only the final
complex-number simplification.
-/
def RealMobiusFirstWirtingerDenominatorAlgebraTheorem : Prop :=
  ∀ (A : RealMobiusRepresentative) (p : ℍ),
    let δ : ℂ := UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p
    let c : ℂ := ((A : GL (Fin 2) ℝ) 1 0 : ℂ)
    let y : ℂ := ((((p : ℍ) : ℂ).im : ℝ) : ℂ)
    (-2 * c / δ ^ 3) / (δ ^ 2)⁻¹ +
        Complex.I * (δ ^ 2)⁻¹ / (y / (Complex.normSq δ : ℂ)) =
      Complex.I / y

private theorem realMobius_firstWirtinger_denominator_algebra_of_re_im
    (a c y : ℝ) (hy : (y : ℂ) ≠ 0)
    (hδ : (a : ℂ) + (c : ℂ) * (y : ℂ) * Complex.I ≠ 0) :
    let δ : ℂ := (a : ℂ) + (c : ℂ) * (y : ℂ) * Complex.I
    (-2 * (c : ℂ) / δ ^ 3) / (δ ^ 2)⁻¹ +
        Complex.I * (δ ^ 2)⁻¹ / ((y : ℂ) / (Complex.normSq δ : ℂ)) =
      Complex.I / (y : ℂ) := by
  have hnorm :
      (Complex.normSq ((a : ℂ) + (c : ℂ) * (y : ℂ) * Complex.I) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr hδ).ne'
  field_simp [hy, hδ, hnorm]
  rw [show Complex.normSq ((a : ℂ) + (c : ℂ) * (y : ℂ) * Complex.I) =
      a ^ 2 + (c * y) ^ 2 by
    simpa [mul_assoc] using Complex.normSq_add_mul_I a (c * y)]
  ring_nf
  rw [Complex.I_sq, Complex.I_pow_three]
  push_cast
  ring_nf

/-- Real Mobius transformations satisfy the denominator algebra identity. -/
theorem realMobiusFirstWirtingerDenominatorAlgebraTheorem :
    RealMobiusFirstWirtingerDenominatorAlgebraTheorem := by
  intro A p
  let g : GL (Fin 2) ℝ := (A : GL (Fin 2) ℝ)
  let a : ℝ := g 1 0 * (p : ℂ).re + g 1 1
  let c : ℝ := g 1 0
  let y : ℝ := (p : ℂ).im
  have hy : (y : ℂ) ≠ 0 := by
    exact_mod_cast (show y ≠ 0 by simpa [y] using p.im_ne_zero)
  have hden :
      UpperHalfPlane.denom g p =
        (a : ℂ) + (c : ℂ) * (y : ℂ) * Complex.I := by
    dsimp [UpperHalfPlane.denom, a, c, y]
    rw [show (p : ℂ) = (p : ℂ).re + (p : ℂ).im * Complex.I from
      (Complex.re_add_im (p : ℂ)).symm]
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    push_cast
    ring_nf
  have hδ :
      (a : ℂ) + (c : ℂ) * (y : ℂ) * Complex.I ≠ 0 := by
    rw [← hden]
    exact UpperHalfPlane.denom_ne_zero g p
  have hAlg :=
    realMobius_firstWirtinger_denominator_algebra_of_re_im a c y hy hδ
  simpa [g, a, c, y, hden] using hAlg

/--
The denominator algebra identity implies the scalar real-Mobius multiplier
identity.
-/
theorem realMobiusFirstWirtingerMultiplierIdentityTheorem_of_denominatorAlgebra
    (hAlg : RealMobiusFirstWirtingerDenominatorAlgebraTheorem) :
    RealMobiusFirstWirtingerMultiplierIdentityTheorem := by
  intro A p
  let δ : ℂ := UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p
  let c : ℂ := ((A : GL (Fin 2) ℝ) 1 0 : ℂ)
  let y : ℂ := ((((p : ℍ) : ℂ).im : ℝ) : ℂ)
  have hα :
      deriv
        (fun w : ℂ ↦
          (realMobiusRepresentativeAction A
            ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
        p = (δ ^ 2)⁻¹ := by
    simpa [δ] using realMobiusRepresentativeAction_deriv A p
  have hβ :
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A
                ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
            w)
        p =
        -2 * c / δ ^ 3 := by
    simpa [δ, c] using realMobiusRepresentativeAction_second_deriv A p
  have hIm :
      ((((realMobiusRepresentativeAction A p : ℍ) : ℂ).im : ℝ) : ℂ) =
        y / (Complex.normSq δ : ℂ) := by
    have him_real :
        ((realMobiusRepresentativeAction A p : ℂ).im : ℝ) =
          ((p : ℂ).im : ℝ) / Complex.normSq δ := by
      simpa [realMobiusRepresentativeAction, δ] using
        (UpperHalfPlane.im_smul_eq_div_normSq (g := A) (z := p))
    simpa [y] using congrArg (fun r : ℝ ↦ (r : ℂ)) him_real
  rw [hα, hβ, hIm]
  simpa [δ, c, y] using hAlg A p

/-- Real Mobius transformations satisfy the scalar first-Wirtinger multiplier identity. -/
theorem realMobiusFirstWirtingerMultiplierIdentityTheorem :
    RealMobiusFirstWirtingerMultiplierIdentityTheorem :=
  realMobiusFirstWirtingerMultiplierIdentityTheorem_of_denominatorAlgebra
    realMobiusFirstWirtingerDenominatorAlgebraTheorem

private theorem realMobiusPostcomposition_firstWirtinger_algebra
    {α β F₁ F₂ Yp Yq : ℂ}
    (hα : α ≠ 0) (hF₁ : F₁ ≠ 0) (hYp : Yp ≠ 0) (hYq : Yq ≠ 0)
    (hId : β / α + Complex.I * α / Yq = Complex.I / Yp) :
    ((β * F₁ ^ 2 + α * F₂) / (α * F₁) +
        Complex.I * (α * F₁) / Yq) / 2 =
      (F₂ / F₁ + Complex.I * F₁ / Yp) / 2 := by
  have hcore :
      (β * F₁ ^ 2 + α * F₂) / (α * F₁) +
          Complex.I * (α * F₁) / Yq =
        F₂ / F₁ + Complex.I * F₁ / Yp := by
    calc
      (β * F₁ ^ 2 + α * F₂) / (α * F₁) +
          Complex.I * (α * F₁) / Yq =
          F₂ / F₁ + (β / α + Complex.I * α / Yq) * F₁ := by
        field_simp [hα, hF₁, hYq]
        ring
      _ = F₂ / F₁ + Complex.I * F₁ / Yp := by
        rw [hId]
        field_simp [hYp]
  rw [hcore]

/--
The second-order chain rule and the real-Mobius multiplier identity imply
invariance of the first-Wirtinger expression.
-/
theorem realMobiusPostcompositionFirstWirtingerExpressionInvariantTheorem_of_secondChainRule_multiplierIdentity
    (hSecondChain :
      RealMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem)
    (hMultiplier :
      RealMobiusFirstWirtingerMultiplierIdentityTheorem) :
    RealMobiusPostcompositionFirstWirtingerExpressionInvariantTheorem := by
  intro u S H A z hz
  let F₁ : ℂ := deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z
  let F₂ : ℂ :=
    deriv (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z
  let α : ℂ :=
    deriv
      (fun w : ℂ ↦
        (realMobiusRepresentativeAction A
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
      (H.upperHalfPlaneMap z)
  let β : ℂ :=
    deriv
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
          w)
      (H.upperHalfPlaneMap z)
  let Yp : ℂ := ((((H.upperHalfPlaneMap z : ℍ) : ℂ).im : ℝ) : ℂ)
  let Yq : ℂ :=
    ((((realMobiusRepresentativeAction A (H.upperHalfPlaneMap z) : ℍ) : ℂ).im : ℝ) :
      ℂ)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hα_ne : α ≠ 0 := by
    simpa [α] using
      realMobiusRepresentativeAction_deriv_ne_zero A (H.upperHalfPlaneMap z)
  have hYp_ne : Yp ≠ 0 := by
    simpa [Yp] using
      (show ((((H.upperHalfPlaneMap z : ℍ) : ℂ).im : ℂ) ≠ 0) by
        exact_mod_cast (H.upperHalfPlaneMap z).im_ne_zero)
  have hYq_ne : Yq ≠ 0 := by
    simpa [Yq] using
      (show
        ((((realMobiusRepresentativeAction A (H.upperHalfPlaneMap z) : ℍ) : ℂ).im :
          ℂ) ≠ 0) by
        exact_mod_cast
          (realMobiusRepresentativeAction A (H.upperHalfPlaneMap z)).im_ne_zero)
  have hG₁ :
      deriv
        (fun w : ℂ ↦
          (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ))
        z =
        α * F₁ := by
    simpa [α, F₁] using
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H A hz
  have hG₂ :
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
            w) z =
        β * F₁ ^ 2 + α * F₂ := by
    simpa [β, α, F₁, F₂] using hSecondChain H A z hz
  have hId :
      β / α + Complex.I * α / Yq = Complex.I / Yp := by
    simpa [β, α, Yq, Yp] using hMultiplier A (H.upperHalfPlaneMap z)
  rw [realMobiusPostcompositionFirstWirtingerExpression,
    localUpperHalfPlaneDevelopingMapFirstWirtingerExpression, hG₁, hG₂]
  exact
    realMobiusPostcomposition_firstWirtinger_algebra
      hα_ne hF₁_ne hYp_ne hYq_ne hId

/--
The real-Mobius multiplier identity is now proved, so expression invariance
only needs the second-order branch chain rule.
-/
theorem realMobiusPostcompositionFirstWirtingerExpressionInvariantTheorem_of_secondChainRule
    (hSecondChain :
      RealMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem) :
    RealMobiusPostcompositionFirstWirtingerExpressionInvariantTheorem :=
  realMobiusPostcompositionFirstWirtingerExpressionInvariantTheorem_of_secondChainRule_multiplierIdentity
    hSecondChain realMobiusFirstWirtingerMultiplierIdentityTheorem

namespace LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Fixed-branch projective derivative regularity gives pointwise invariance of
the first-Wirtinger expression under real Mobius postcomposition.
-/
theorem realMobiusPostcomposition_firstWirtingerExpression
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    realMobiusPostcompositionFirstWirtingerExpression H A z =
      localUpperHalfPlaneDevelopingMapFirstWirtingerExpression H z := by
  let F₁ : ℂ := deriv (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z
  let F₂ : ℂ :=
    deriv (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z
  let α : ℂ :=
    deriv
      (fun w : ℂ ↦
        (realMobiusRepresentativeAction A
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
      (H.upperHalfPlaneMap z)
  let β : ℂ :=
    deriv
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
          w)
      (H.upperHalfPlaneMap z)
  let Yp : ℂ := ((((H.upperHalfPlaneMap z : ℍ) : ℂ).im : ℝ) : ℂ)
  let Yq : ℂ :=
    ((((realMobiusRepresentativeAction A (H.upperHalfPlaneMap z) : ℍ) : ℂ).im : ℝ) :
      ℂ)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hα_ne : α ≠ 0 := by
    simpa [α] using
      realMobiusRepresentativeAction_deriv_ne_zero A (H.upperHalfPlaneMap z)
  have hYp_ne : Yp ≠ 0 := by
    simpa [Yp] using
      (show ((((H.upperHalfPlaneMap z : ℍ) : ℂ).im : ℂ) ≠ 0) by
        exact_mod_cast (H.upperHalfPlaneMap z).im_ne_zero)
  have hYq_ne : Yq ≠ 0 := by
    simpa [Yq] using
      (show
        ((((realMobiusRepresentativeAction A (H.upperHalfPlaneMap z) : ℍ) : ℂ).im :
          ℂ) ≠ 0) by
        exact_mod_cast
          (realMobiusRepresentativeAction A (H.upperHalfPlaneMap z)).im_ne_zero)
  have hG₁ :
      deriv
        (fun w : ℂ ↦
          (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ))
        z =
        α * F₁ := by
    simpa [α, F₁] using
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H A hz
  have hG₂ :
      deriv
        (fun w : ℂ ↦
          deriv
            (fun t : ℂ ↦
              (realMobiusRepresentativeAction A (H.upperHalfPlaneMap t) : ℂ))
            w) z =
        β * F₁ ^ 2 + α * F₂ := by
    simpa [β, α, F₁, F₂] using
      R.realMobiusPostcompositionSecondDerivativeChainRule A hz
  have hId :
      β / α + Complex.I * α / Yq = Complex.I / Yp := by
    simpa [β, α, Yq, Yp] using
      realMobiusFirstWirtingerMultiplierIdentityTheorem A (H.upperHalfPlaneMap z)
  rw [realMobiusPostcompositionFirstWirtingerExpression,
    localUpperHalfPlaneDevelopingMapFirstWirtingerExpression, hG₁, hG₂]
  exact
    realMobiusPostcomposition_firstWirtinger_algebra
      hα_ne hF₁_ne hYp_ne hYq_ne hId

end LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Expression invariance under real Mobius postcomposition gives preservation of
the branch first-Wirtinger pullback formula.
-/
theorem realMobiusPostcompositionPreservesPullbackFirstWirtingerFormulaTheorem_of_expressionInvariant
    (hInv :
      RealMobiusPostcompositionFirstWirtingerExpressionInvariantTheorem) :
    RealMobiusPostcompositionPreservesPullbackFirstWirtingerFormulaTheorem := by
  intro u S H A z _hu hz hFirst
  rw [hInv H A z hz]
  exact hFirst

/--
First-Wirtinger pullback formula for a pointed real-Mobius comparison.

The two formulas say that both the second branch and the real-Mobius
postcomposition of the first branch recover the same canonical derivative
`u_z` through
`(F'' / F' + i F' / Im F) / 2`.
-/
def PointedRealMobiusTransitionPullbackFirstWirtingerFormulaTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          (∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
            S₁.coefficient z = S₂.coefficient z) →
          ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
            H₂.upperHalfPlaneMap z =
                realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z) →
            deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z =
                deriv
                  (fun w : ℂ ↦
                    (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
                  z →
              u.wirtingerZ z =
                  (deriv
                      (fun w : ℂ ↦
                        deriv (fun t : ℂ ↦ (H₂.upperHalfPlaneMap t : ℂ)) w) z /
                    deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z +
                    Complex.I * deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z /
                      (((H₂.upperHalfPlaneMap z : ℂ).im : ℝ) : ℂ)) / 2 ∧
                u.wirtingerZ z =
                  (deriv
                      (fun w : ℂ ↦
                        deriv
                          (fun t : ℂ ↦
                            (realMobiusRepresentativeAction A
                              (H₁.upperHalfPlaneMap t) : ℂ))
                          w) z /
                    deriv
                      (fun w : ℂ ↦
                        (realMobiusRepresentativeAction A
                          (H₁.upperHalfPlaneMap w) : ℂ)) z +
                    Complex.I *
                      deriv
                        (fun w : ℂ ↦
                          (realMobiusRepresentativeAction A
                            (H₁.upperHalfPlaneMap w) : ℂ)) z /
                      ((((realMobiusRepresentativeAction A
                        (H₁.upperHalfPlaneMap z) : ℍ) : ℂ).im : ℝ) : ℂ)) / 2

/--
The broad comparison first-Wirtinger formula follows from a branch-level
pullback formula and real-Mobius invariance of that formula.
-/
theorem pointedRealMobiusTransitionPullbackFirstWirtingerFormulaTheorem_of_branchFormula_postcomposition
    (hBranch :
      LocalUpperHalfPlaneDevelopingMapPullbackFirstWirtingerFormulaTheorem)
    (hPost :
      RealMobiusPostcompositionPreservesPullbackFirstWirtingerFormulaTheorem) :
    PointedRealMobiusTransitionPullbackFirstWirtingerFormulaTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ hu _hpoint _hCoeff z hz₁ hz₂ _hval _hderiv
  constructor
  · simpa [localUpperHalfPlaneDevelopingMapFirstWirtingerExpression] using
      hBranch H₂ z hu hz₂
  · have hH₁ :
        u.wirtingerZ z =
          localUpperHalfPlaneDevelopingMapFirstWirtingerExpression H₁ z :=
      hBranch H₁ z hu hz₁
    simpa [realMobiusPostcompositionFirstWirtingerExpression] using
      hPost H₁ A z hu hz₁ hH₁

/--
The first-Wirtinger pullback formula gives the metric second-jet bridge.

Once the two compared maps have the same value and first derivative, the two
displayed formulas for `u_z` differ only in the second-derivative term.  Since
the first derivative is nonzero, the second derivatives agree.
-/
theorem pointedRealMobiusTransitionMetricOneJetDeterminesSecondJetTheorem_of_pullbackFirstWirtingerFormula
    (hFormula :
      PointedRealMobiusTransitionPullbackFirstWirtingerFormulaTheorem) :
    PointedRealMobiusTransitionMetricOneJetDeterminesSecondJetTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ hu hpoint hCoeff z hz₁ hz₂ hval hderiv
  rcases hFormula H₁ H₂ A z₀ hu hpoint hCoeff z hz₁ hz₂ hval hderiv with
    ⟨h₂, hA⟩
  let F' : ℂ := deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z
  let F'' : ℂ :=
    deriv (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H₂.upperHalfPlaneMap t : ℂ)) w) z
  let G' : ℂ :=
    deriv
      (fun w : ℂ ↦
        (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ)) z
  let G'' : ℂ :=
    deriv
      (fun w : ℂ ↦
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap t) : ℂ))
          w) z
  let Y : ℂ := (((H₂.upperHalfPlaneMap z : ℂ).im : ℝ) : ℂ)
  have hF'_ne : F' ≠ 0 := by
    have hF'_eq :
        F' = H₂.projective.affineMapDeriv z := by
      simpa [F'] using H₂.upperHalfPlane_deriv_eq_projectiveDeriv z hz₂
    rw [hF'_eq]
    exact H₂.projective.affineMapDeriv_ne_zero z hz₂
  have hvalue_complex :
      ((H₂.upperHalfPlaneMap z : ℍ) : ℂ) =
        ((realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z) : ℍ) : ℂ) :=
    congrArg (fun p : ℍ ↦ (p : ℂ)) hval
  have hterms :
      (F'' / F' + Complex.I * F' / Y) / 2 =
        (G'' / F' + Complex.I * F' / Y) / 2 := by
    have hraw := h₂.symm.trans hA
    simpa [F', F'', G', G'', Y, hderiv.symm, hvalue_complex.symm] using hraw
  have hsum :
      F'' / F' + Complex.I * F' / Y =
        G'' / F' + Complex.I * F' / Y := by
    have hmul := congrArg (fun x : ℂ ↦ (2 : ℂ) * x) hterms
    simpa [div_eq_mul_inv, mul_add, add_comm, add_left_comm, add_assoc] using hmul
  have hdiv : F'' / F' = G'' / F' := by
    exact add_right_cancel hsum
  have hsecond : F'' = G'' := by
    rwa [div_left_inj' hF'_ne] at hdiv
  simpa [F'', G''] using hsecond

/--
Schwarzian local uniqueness with the correct two-jet input.

After coefficient agreement, equality of value, first derivative, and second
derivative at a point should force local equality of the compared branches.
This is the ordinary local uniqueness theorem for the Schwarzian differential
equation, with the Mobius ambiguity removed by the two-jet.
-/
def PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          (∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
            S₁.coefficient z = S₂.coefficient z) →
          ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
            H₂.upperHalfPlaneMap z =
                realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z) →
            deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z =
                deriv
                  (fun w : ℂ ↦
                    (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
                  z →
            deriv (fun w : ℂ ↦
                  deriv (fun t : ℂ ↦ (H₂.upperHalfPlaneMap t : ℂ)) w) z =
                deriv
                  (fun w : ℂ ↦
                    deriv
                      (fun t : ℂ ↦
                        (realMobiusRepresentativeAction A
                          (H₁.upperHalfPlaneMap t) : ℂ))
                      w)
                  z →
              ∃ U : Set ℂ,
                IsOpen U ∧ z ∈ U ∧ U ⊆ H₁.domain ∩ H₂.domain ∧
                  ∀ w, w ∈ U →
                    H₂.upperHalfPlaneMap w =
                        realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) ∧
                    deriv (fun t : ℂ ↦ (H₂.upperHalfPlaneMap t : ℂ)) w =
                        deriv
                          (fun t : ℂ ↦
                            (realMobiusRepresentativeAction A
                              (H₁.upperHalfPlaneMap t) : ℂ))
                          w

/--
Value-only form of the two-jet Schwarzian local uniqueness target.

The analytic identity principle only has to prove equality of the two branch
values on a small open neighborhood.  Once that is known, derivative equality
on the same neighborhood is a formal consequence of local equality.
-/
def PointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ),
      u.SolvesLiouvilleEquation →
        H₁.HasPointedRealMobiusTransition H₂ A z₀ →
          (∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
            S₁.coefficient z = S₂.coefficient z) →
          ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
            H₂.upperHalfPlaneMap z =
                realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z) →
            deriv (fun w : ℂ ↦ (H₂.upperHalfPlaneMap w : ℂ)) z =
                deriv
                  (fun w : ℂ ↦
                    (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ))
                  z →
            deriv (fun w : ℂ ↦
                  deriv (fun t : ℂ ↦ (H₂.upperHalfPlaneMap t : ℂ)) w) z =
                deriv
                  (fun w : ℂ ↦
                    deriv
                      (fun t : ℂ ↦
                        (realMobiusRepresentativeAction A
                          (H₁.upperHalfPlaneMap t) : ℂ))
                      w)
                  z →
              ∃ U : Set ℂ,
                IsOpen U ∧ z ∈ U ∧ U ⊆ H₁.domain ∩ H₂.domain ∧
                  ∀ w, w ∈ U →
                    H₂.upperHalfPlaneMap w =
                      realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w)

/--
Scalar Schwarzian two-jet local uniqueness.

This is the plain one-variable identity-principle boundary: on an open set,
two scalar maps with the same actual Schwarzian and the same value, first
derivative, and second derivative at a point agree locally.
-/
def ScalarSchwarzianTwoJetValueLocalUniquenessTheorem : Prop :=
  ∀ (f g : ℂ → ℂ) (U : Set ℂ) (z : ℂ),
    IsOpen U →
      z ∈ U →
        (∀ w, w ∈ U → deriv f w ≠ 0) →
          (∀ w, w ∈ U → deriv g w ≠ 0) →
            (∀ w, w ∈ U → actualSchwarzian f w = actualSchwarzian g w) →
              f z = g z →
                deriv f z = deriv g z →
                  deriv (fun w : ℂ ↦ deriv f w) z =
                    deriv (fun w : ℂ ↦ deriv g w) z →
                    ∃ V : Set ℂ,
                      IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
                        ∀ w, w ∈ V → f w = g w

/--
Regular scalar Schwarzian two-jet local uniqueness.

This is the same identity-principle boundary as
`ScalarSchwarzianTwoJetValueLocalUniquenessTheorem`, but with explicit local
regularity hypotheses for the first and second derivative branches.  These
are exactly the hypotheses supplied by the upper-half-plane branch packages.
-/
def ScalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem : Prop :=
  ∀ (f g : ℂ → ℂ) (U : Set ℂ) (z : ℂ),
    IsOpen U →
      z ∈ U →
        (∀ w, w ∈ U → deriv f w ≠ 0) →
          (∀ w, w ∈ U → deriv g w ≠ 0) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv f t)
                (deriv (fun t : ℂ ↦ deriv f t) w) w) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
                (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) w) w) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv g t)
                (deriv (fun t : ℂ ↦ deriv g t) w) w) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t)
                (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t) w) w) →
            (∀ w, w ∈ U → actualSchwarzian f w = actualSchwarzian g w) →
              f z = g z →
                deriv f z = deriv g z →
                  deriv (fun w : ℂ ↦ deriv f w) z =
                    deriv (fun w : ℂ ↦ deriv g w) z →
                    ∃ V : Set ℂ,
                      IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
                        ∀ w, w ∈ V → f w = g w

/-- The scalar pre-Schwarzian expression `f'' / f'`. -/
def scalarPreSchwarzian (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv (fun w : ℂ ↦ deriv f w) z / deriv f z

/--
Schwarzian equality determines the pre-Schwarzian locally after the second
jet has been fixed.

This is the Riccati/linear first-order part of scalar Schwarzian uniqueness:
if two regular maps have the same Schwarzian and their pre-Schwarzians agree
at the base point, then the pre-Schwarzians agree on a neighborhood.
-/
def ScalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem : Prop :=
  ∀ (f g : ℂ → ℂ) (U : Set ℂ) (z : ℂ),
    IsOpen U →
      z ∈ U →
        (∀ w, w ∈ U → deriv f w ≠ 0) →
          (∀ w, w ∈ U → deriv g w ≠ 0) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv f t)
                (deriv (fun t : ℂ ↦ deriv f t) w) w) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
                (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) w) w) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv g t)
                (deriv (fun t : ℂ ↦ deriv g t) w) w) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t)
                (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t) w) w) →
            (∀ w, w ∈ U → actualSchwarzian f w = actualSchwarzian g w) →
              scalarPreSchwarzian f z = scalarPreSchwarzian g z →
                ∃ V : Set ℂ,
                  IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
                    ∀ w, w ∈ V →
                      scalarPreSchwarzian f w = scalarPreSchwarzian g w

/--
Equal pre-Schwarzians and equal initial value/derivative determine the maps
locally.

This is the final integration step after the Riccati reduction.
-/
def ScalarPreSchwarzianValueDerivativeLocalUniquenessTheorem : Prop :=
  ∀ (f g : ℂ → ℂ) (U : Set ℂ) (z : ℂ),
    IsOpen U →
      z ∈ U →
        (∀ w, w ∈ U → deriv f w ≠ 0) →
          (∀ w, w ∈ U → deriv g w ≠ 0) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv f t)
                (deriv (fun t : ℂ ↦ deriv f t) w) w) →
            (∀ w, w ∈ U →
              HasDerivAt
                (fun t : ℂ ↦ deriv g t)
                (deriv (fun t : ℂ ↦ deriv g t) w) w) →
            (∀ w, w ∈ U →
              scalarPreSchwarzian f w = scalarPreSchwarzian g w) →
                f z = g z →
                  deriv f z = deriv g z →
                    ∃ V : Set ℂ,
                      IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
                        ∀ w, w ∈ V → f w = g w

/--
Concrete integration theorem for equal pre-Schwarzians.

On a small ball, the quotient `f' / g'` has zero derivative.  It is therefore
constant by mathlib's derivative-zero identity principle; the initial first
derivative makes that constant equal to one, and a second application of the
same identity principle to `f` and `g` gives local equality.
-/
theorem scalarPreSchwarzianValueDerivativeLocalUniquenessTheorem_of_derivativeQuotient :
    ScalarPreSchwarzianValueDerivativeLocalUniquenessTheorem := by
  intro f g U z hU hz hf_ne hg_ne hf₁ hg₁ hpre hval hderiv
  have hnhds : U ∈ nhds z := hU.mem_nhds hz
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr_pos, hr_subset⟩
  let V : Set ℂ := Metric.ball z r
  have hVopen : IsOpen V := Metric.isOpen_ball
  have hzV : z ∈ V := Metric.mem_ball_self hr_pos
  have hVpre : IsPreconnected V := (convex_ball z r).isPreconnected
  have hVsubset : V ⊆ U := hr_subset
  let q : ℂ → ℂ := fun w ↦ deriv f w / deriv g w
  have hq_differentiableOn : DifferentiableOn ℂ q V := by
    intro w hw
    exact ((hf₁ w (hVsubset hw)).differentiableAt.div
      (hg₁ w (hVsubset hw)).differentiableAt (hg_ne w (hVsubset hw))).differentiableWithinAt
  have hq_deriv_zero : V.EqOn (deriv q) 0 := by
    intro w hw
    change deriv q w = (0 : ℂ)
    have hf_at := hf₁ w (hVsubset hw)
    have hg_at := hg₁ w (hVsubset hw)
    have hg_nonzero : deriv g w ≠ 0 := hg_ne w (hVsubset hw)
    have hf_nonzero : deriv f w ≠ 0 := hf_ne w (hVsubset hw)
    have hpre_w := hpre w (hVsubset hw)
    have hdiv :
        deriv (fun t : ℂ ↦ deriv f t) w / deriv f w =
          deriv (fun t : ℂ ↦ deriv g t) w / deriv g w := by
      simpa [scalarPreSchwarzian] using hpre_w
    have hnum :
        deriv (fun t : ℂ ↦ deriv f t) w * deriv g w -
            deriv f w * deriv (fun t : ℂ ↦ deriv g t) w = 0 := by
      apply sub_eq_zero.mpr
      simpa [mul_comm] using (div_eq_div_iff hf_nonzero hg_nonzero).mp hdiv
    have hderiv_q :
        deriv q w =
          (deriv (fun t : ℂ ↦ deriv f t) w * deriv g w -
              deriv f w * deriv (fun t : ℂ ↦ deriv g t) w) /
            deriv g w ^ 2 := by
      simpa [q] using
        (deriv_div hf_at.differentiableAt hg_at.differentiableAt hg_nonzero)
    rw [hderiv_q, hnum, zero_div]
  have hq_const :
      ∀ w ∈ V, q w = q z :=
    fun w hw ↦ hVopen.is_const_of_deriv_eq_zero hVpre hq_differentiableOn
      hq_deriv_zero hw hzV
  have hq_one : ∀ w ∈ V, q w = 1 := by
    intro w hw
    calc
      q w = q z := hq_const w hw
      _ = 1 := by
        have hgz : deriv g z ≠ 0 := hg_ne z hz
        calc
          q z = deriv f z / deriv g z := rfl
          _ = deriv g z / deriv g z := by rw [hderiv]
          _ = 1 := div_self hgz
  have hderiv_eq_on : V.EqOn (deriv f) (deriv g) := by
    intro w hw
    have hg_nonzero : deriv g w ≠ 0 := hg_ne w (hVsubset hw)
    have hq_eq := hq_one w hw
    dsimp [q] at hq_eq
    exact (div_eq_one_iff_eq hg_nonzero).mp hq_eq
  have hf_diff : DifferentiableOn ℂ f V := by
    intro w hw
    exact (differentiableAt_of_deriv_ne_zero (hf_ne w (hVsubset hw))).differentiableWithinAt
  have hg_diff : DifferentiableOn ℂ g V := by
    intro w hw
    exact (differentiableAt_of_deriv_ne_zero (hg_ne w (hVsubset hw))).differentiableWithinAt
  have heq_on : V.EqOn f g :=
    hVopen.eqOn_of_deriv_eq hVpre hf_diff hg_diff hderiv_eq_on hzV hval
  exact ⟨V, hVopen, hzV, hVsubset, fun w hw ↦ heq_on hw⟩

/--
Zero-uniqueness for the linear first-order equation obeyed by the
pre-Schwarzian difference.

The coefficient is written as an arbitrary function `a`; the scalar
Schwarzian calculation below supplies
`a = (scalarPreSchwarzian f + scalarPreSchwarzian g) / 2`.
-/
def ScalarPreSchwarzianRiccatiZeroLocalUniquenessTheorem : Prop :=
  ∀ (a α : ℂ → ℂ) (U : Set ℂ) (z : ℂ),
    IsOpen U →
      z ∈ U →
        (∀ w, w ∈ U → HasDerivAt α (a w * α w) w) →
          α z = 0 →
            ∃ V : Set ℂ,
              IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
                ∀ w, w ∈ V → α w = 0

/--
Local integrating-factor existence for the scalar first-order equation
`α' = a α`, stated on a small ball.
-/
def ScalarPreSchwarzianRiccatiIntegratingFactorBallExistenceTheorem : Prop :=
  ∀ (a : ℂ → ℂ) (U : Set ℂ) (z : ℂ),
    IsOpen U →
      z ∈ U →
        ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ U ∧
          ∃ μ : ℂ → ℂ,
            (∀ w, w ∈ Metric.ball z r → μ w ≠ 0) ∧
              ∀ w, w ∈ Metric.ball z r →
                HasDerivAt μ (-(a w) * μ w) w

/--
Local primitive existence for the scalar pre-Schwarzian Riccati coefficient,
stated on a ball.
-/
def ScalarPreSchwarzianRiccatiPrimitiveBallExistenceTheorem : Prop :=
  ∀ (a : ℂ → ℂ) (U : Set ℂ) (z : ℂ),
    IsOpen U →
      z ∈ U →
        ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ U ∧
          ∃ A : ℂ → ℂ,
            ∀ w, w ∈ Metric.ball z r → HasDerivAt A (a w) w

/--
A local primitive gives a nonvanishing local integrating factor by
`μ = exp(-A)`.
-/
theorem scalarPreSchwarzianRiccatiIntegratingFactorBallExistenceTheorem_of_primitive
    (hPrim :
      ScalarPreSchwarzianRiccatiPrimitiveBallExistenceTheorem) :
    ScalarPreSchwarzianRiccatiIntegratingFactorBallExistenceTheorem := by
  intro a U z hU hz
  rcases hPrim a U z hU hz with ⟨r, hr_pos, hball_subset, A, hA_deriv⟩
  refine ⟨r, hr_pos, hball_subset, (fun w : ℂ ↦ Complex.exp (-(A w))), ?_, ?_⟩
  · intro w _hw
    exact Complex.exp_ne_zero (-(A w))
  · intro w hw
    have hneg : HasDerivAt (fun t : ℂ ↦ -(A t)) (-(a w)) w :=
      (hA_deriv w hw).neg
    have hexp := hneg.cexp
    convert hexp using 1
    ring

/--
Mathlib's disk primitive theorem gives a primitive on a small ball for every
coefficient which is complex differentiable on the ambient open set.
-/
theorem scalarPreSchwarzianRiccatiPrimitiveBallExistence_of_differentiableOn
    {a : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U)
    (ha : DifferentiableOn ℂ a U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ U ∧
      ∃ A : ℂ → ℂ,
        ∀ w, w ∈ Metric.ball z r → HasDerivAt A (a w) w := by
  rcases Metric.mem_nhds_iff.mp (hU.mem_nhds hz) with ⟨r, hr_pos, hball_subset⟩
  have ha_ball : DifferentiableOn ℂ a (Metric.ball z r) :=
    ha.mono hball_subset
  rcases ha_ball.isExactOn_ball with ⟨A, hA⟩
  exact ⟨r, hr_pos, hball_subset, A, hA⟩

/--
An integrating factor proves zero-uniqueness for the scalar Riccati/linear
equation.  The product `μ α` has zero derivative on a small ball, hence is
constant; since `α` vanishes at the base point and `μ` is nonzero, `α`
vanishes throughout the ball.
-/
theorem scalarPreSchwarzianRiccatiZeroLocalUniquenessTheorem_of_integratingFactor
    (hIF :
      ScalarPreSchwarzianRiccatiIntegratingFactorBallExistenceTheorem) :
    ScalarPreSchwarzianRiccatiZeroLocalUniquenessTheorem := by
  intro a α U z hU hz hα_deriv hα₀
  rcases hIF a U z hU hz with ⟨r, hr_pos, hball_subset, μ, hμ_ne, hμ_deriv⟩
  let V : Set ℂ := Metric.ball z r
  have hVopen : IsOpen V := Metric.isOpen_ball
  have hzV : z ∈ V := Metric.mem_ball_self hr_pos
  have hVpre : IsPreconnected V := (convex_ball z r).isPreconnected
  let product : ℂ → ℂ := fun w ↦ μ w * α w
  have hproduct_deriv : V.EqOn (deriv product) 0 := by
    intro w hw
    change deriv product w = (0 : ℂ)
    have hprod :
        HasDerivAt product
          ((-(a w) * μ w) * α w + μ w * (a w * α w)) w := by
      simpa [product] using
        (hμ_deriv w hw).mul (hα_deriv w (hball_subset hw))
    rw [hprod.deriv]
    ring
  have hproduct_diff : DifferentiableOn ℂ product V := by
    intro w hw
    have hprod :
        HasDerivAt product
          ((-(a w) * μ w) * α w + μ w * (a w * α w)) w := by
      simpa [product] using
        (hμ_deriv w hw).mul (hα_deriv w (hball_subset hw))
    exact hprod.differentiableAt.differentiableWithinAt
  have hproduct_const : ∀ w ∈ V, product w = product z :=
    fun w hw ↦ hVopen.is_const_of_deriv_eq_zero hVpre hproduct_diff
      hproduct_deriv hw hzV
  refine ⟨V, hVopen, hzV, hball_subset, ?_⟩
  intro w hw
  have hprod_zero : product w = 0 := by
    calc
      product w = product z := hproduct_const w hw
      _ = 0 := by simp [product, hα₀]
  have hμw : μ w ≠ 0 := hμ_ne w hw
  exact (mul_eq_zero.mp (by simpa [product] using hprod_zero)).resolve_left hμw

/--
Zero-uniqueness for `α' = a α` when the coefficient is complex
differentiable on the ambient open set.  This combines mathlib's primitive
theorem on balls with the integrating-factor argument.
-/
theorem scalarPreSchwarzianRiccatiZeroLocalUniqueness_of_differentiableCoefficient
    {a α : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U)
    (ha : DifferentiableOn ℂ a U)
    (hα_deriv : ∀ w, w ∈ U → HasDerivAt α (a w * α w) w)
    (hα₀ : α z = 0) :
    ∃ V : Set ℂ,
      IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
        ∀ w, w ∈ V → α w = 0 := by
  rcases scalarPreSchwarzianRiccatiPrimitiveBallExistence_of_differentiableOn
      hU hz ha with
    ⟨r, hr_pos, hball_subset, A, hA_deriv⟩
  let V : Set ℂ := Metric.ball z r
  let μ : ℂ → ℂ := fun w ↦ Complex.exp (-(A w))
  have hμ_ne : ∀ w, w ∈ V → μ w ≠ 0 := by
    intro w _hw
    exact Complex.exp_ne_zero (-(A w))
  have hμ_deriv : ∀ w, w ∈ V → HasDerivAt μ (-(a w) * μ w) w := by
    intro w hw
    have hneg : HasDerivAt (fun t : ℂ ↦ -(A t)) (-(a w)) w :=
      (hA_deriv w hw).neg
    have hexp := hneg.cexp
    convert hexp using 1
    ring
  let product : ℂ → ℂ := fun w ↦ μ w * α w
  have hVopen : IsOpen V := Metric.isOpen_ball
  have hzV : z ∈ V := Metric.mem_ball_self hr_pos
  have hVpre : IsPreconnected V := (convex_ball z r).isPreconnected
  have hproduct_deriv : V.EqOn (deriv product) 0 := by
    intro w hw
    change deriv product w = (0 : ℂ)
    have hprod :
        HasDerivAt product
          ((-(a w) * μ w) * α w + μ w * (a w * α w)) w := by
      simpa [product] using
        (hμ_deriv w hw).mul (hα_deriv w (hball_subset hw))
    rw [hprod.deriv]
    ring
  have hproduct_diff : DifferentiableOn ℂ product V := by
    intro w hw
    have hprod :
        HasDerivAt product
          ((-(a w) * μ w) * α w + μ w * (a w * α w)) w := by
      simpa [product] using
        (hμ_deriv w hw).mul (hα_deriv w (hball_subset hw))
    exact hprod.differentiableAt.differentiableWithinAt
  have hproduct_const : ∀ w ∈ V, product w = product z :=
    fun w hw ↦ hVopen.is_const_of_deriv_eq_zero hVpre hproduct_diff
      hproduct_deriv hw hzV
  refine ⟨V, hVopen, hzV, hball_subset, ?_⟩
  intro w hw
  have hprod_zero : product w = 0 := by
    calc
      product w = product z := hproduct_const w hw
      _ = 0 := by simp [product, hα₀]
  exact (mul_eq_zero.mp (by simpa [product] using hprod_zero)).resolve_left
    (hμ_ne w hw)

/--
Derivative formula for the scalar pre-Schwarzian:
`(f'' / f')' = S(f) + (1 / 2) (f'' / f')^2`.
-/
theorem scalarPreSchwarzian_hasDerivAt
    {f : ℂ → ℂ} {z : ℂ}
    (hf_ne : deriv f z ≠ 0)
    (hf₁ :
      HasDerivAt
        (fun t : ℂ ↦ deriv f t)
        (deriv (fun t : ℂ ↦ deriv f t) z) z)
    (hf₂ :
      HasDerivAt
        (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
        (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) z) z) :
    HasDerivAt
      (fun t : ℂ ↦ scalarPreSchwarzian f t)
      (actualSchwarzian f z + (1 / 2 : ℂ) * (scalarPreSchwarzian f z) ^ 2)
      z := by
  have hq :
      HasDerivAt
        (fun t : ℂ ↦
          deriv (fun s : ℂ ↦ deriv f s) t / deriv f t)
        ((deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) z *
              deriv f z -
            deriv (fun t : ℂ ↦ deriv f t) z *
              deriv (fun t : ℂ ↦ deriv f t) z) /
          deriv f z ^ 2)
        z :=
    hf₂.div hf₁ hf_ne
  convert hq using 1
  rw [actualSchwarzian, schwarzianExpression, scalarPreSchwarzian]
  field_simp [hf_ne]
  ring_nf

/--
Equal Schwarzians give the Riccati equation for the pre-Schwarzian
difference.
-/
theorem scalarPreSchwarzian_difference_hasDerivAt_of_actualSchwarzian_eq
    {f g : ℂ → ℂ} {z : ℂ}
    (hf_ne : deriv f z ≠ 0)
    (hg_ne : deriv g z ≠ 0)
    (hf₁ :
      HasDerivAt
        (fun t : ℂ ↦ deriv f t)
        (deriv (fun t : ℂ ↦ deriv f t) z) z)
    (hf₂ :
      HasDerivAt
        (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
        (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) z) z)
    (hg₁ :
      HasDerivAt
        (fun t : ℂ ↦ deriv g t)
        (deriv (fun t : ℂ ↦ deriv g t) z) z)
    (hg₂ :
      HasDerivAt
        (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t)
        (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t) z) z)
    (hschw : actualSchwarzian f z = actualSchwarzian g z) :
    HasDerivAt
      (fun t : ℂ ↦ scalarPreSchwarzian f t - scalarPreSchwarzian g t)
      (((scalarPreSchwarzian f z + scalarPreSchwarzian g z) / 2) *
        (scalarPreSchwarzian f z - scalarPreSchwarzian g z))
      z := by
  have hfP := scalarPreSchwarzian_hasDerivAt hf_ne hf₁ hf₂
  have hgP := scalarPreSchwarzian_hasDerivAt hg_ne hg₁ hg₂
  have hsub := hfP.sub hgP
  convert hsub using 1
  ring_nf
  rw [hschw]
  ring

/--
The algebraic Riccati equation plus zero-uniqueness implies the
pre-Schwarzian equality step.
-/
theorem scalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem_of_riccatiZero
    (hZero :
      ScalarPreSchwarzianRiccatiZeroLocalUniquenessTheorem) :
    ScalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem := by
  intro f g U z hU hz hf_ne hg_ne hf₁ hf₂ hg₁ hg₂ hschw hpre₀
  let α : ℂ → ℂ := fun w ↦ scalarPreSchwarzian f w - scalarPreSchwarzian g w
  let a : ℂ → ℂ := fun w ↦ (scalarPreSchwarzian f w + scalarPreSchwarzian g w) / 2
  have hα_deriv : ∀ w, w ∈ U → HasDerivAt α (a w * α w) w := by
    intro w hw
    simpa [α, a] using
      (scalarPreSchwarzian_difference_hasDerivAt_of_actualSchwarzian_eq
        (hf_ne w hw) (hg_ne w hw)
        (hf₁ w hw) (hf₂ w hw) (hg₁ w hw) (hg₂ w hw)
        (hschw w hw))
  have hα₀ : α z = 0 := by
    simpa [α] using sub_eq_zero.mpr hpre₀
  rcases hZero a α U z hU hz hα_deriv hα₀ with
    ⟨V, hVopen, hzV, hVsubset, hα_zero⟩
  refine ⟨V, hVopen, hzV, hVsubset, ?_⟩
  intro w hw
  have h := hα_zero w hw
  simpa [α] using sub_eq_zero.mp h

/--
%%handwave
name:
  Schwarzian uniqueness for the pre-Schwarzian
statement:
  Let $f$ and $g$ be locally univalent holomorphic maps on an open set $U$,
  with derivatives through order three on $U$. If
  $\{f,z\}=\{g,z\}$ on $U$ and
  $f''(z_0)/f'(z_0)=g''(z_0)/g'(z_0)$, then on some neighborhood $V$ of
  $z_0$ one has
  $$\frac{f''}{f'}=\frac{g''}{g'}.$$
proof:
  For $\alpha=f''/f'-g''/g'$ and
  $a=\tfrac12(f''/f'+g''/g')$, equality of Schwarzians gives
  $\alpha'=a\alpha$. On a small disk, a primitive of $a$ produces an
  integrating factor, so the solution with $\alpha(z_0)=0$ vanishes
  identically.
-/
theorem scalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem_proved :
    ScalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem := by
  intro f g U z hU hz hf_ne hg_ne hf₁ hf₂ hg₁ hg₂ hschw hpre₀
  let α : ℂ → ℂ := fun w ↦ scalarPreSchwarzian f w - scalarPreSchwarzian g w
  let a : ℂ → ℂ := fun w ↦ (scalarPreSchwarzian f w + scalarPreSchwarzian g w) / 2
  have hPf :
      DifferentiableOn ℂ (fun w ↦ scalarPreSchwarzian f w) U := by
    intro w hw
    exact (scalarPreSchwarzian_hasDerivAt (hf_ne w hw) (hf₁ w hw) (hf₂ w hw)).differentiableAt.differentiableWithinAt
  have hPg :
      DifferentiableOn ℂ (fun w ↦ scalarPreSchwarzian g w) U := by
    intro w hw
    exact (scalarPreSchwarzian_hasDerivAt (hg_ne w hw) (hg₁ w hw) (hg₂ w hw)).differentiableAt.differentiableWithinAt
  have ha : DifferentiableOn ℂ a U := by
    intro w hw
    exact ((hPf w hw).add (hPg w hw)).div_const 2
  have hα_deriv : ∀ w, w ∈ U → HasDerivAt α (a w * α w) w := by
    intro w hw
    simpa [α, a] using
      (scalarPreSchwarzian_difference_hasDerivAt_of_actualSchwarzian_eq
        (hf_ne w hw) (hg_ne w hw)
        (hf₁ w hw) (hf₂ w hw) (hg₁ w hw) (hg₂ w hw)
        (hschw w hw))
  have hα₀ : α z = 0 := by
    simpa [α] using sub_eq_zero.mpr hpre₀
  rcases scalarPreSchwarzianRiccatiZeroLocalUniqueness_of_differentiableCoefficient
      hU hz ha hα_deriv hα₀ with
    ⟨V, hVopen, hzV, hVsubset, hα_zero⟩
  refine ⟨V, hVopen, hzV, hVsubset, ?_⟩
  intro w hw
  have h := hα_zero w hw
  simpa [α] using sub_eq_zero.mp h

/--
The Riccati pre-Schwarzian reduction plus the final integration step imply
the regular scalar Schwarzian two-jet uniqueness theorem.
-/
theorem scalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem_of_preSchwarzian
    (hPre :
      ScalarSchwarzianC3ToPreSchwarzianLocalUniquenessTheorem)
    (hInt :
      ScalarPreSchwarzianValueDerivativeLocalUniquenessTheorem) :
    ScalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem := by
  intro f g U z hU hz hf_ne hg_ne hf₁ hf₂ hg₁ hg₂ hschw hval hderiv hsecond
  have hpre₀ : scalarPreSchwarzian f z = scalarPreSchwarzian g z := by
    unfold scalarPreSchwarzian
    rw [hderiv, hsecond]
  rcases hPre f g U z hU hz hf_ne hg_ne hf₁ hf₂ hg₁ hg₂ hschw hpre₀ with
    ⟨W, hWopen, hzW, hWsubset, hpreW⟩
  have hf_ne_W : ∀ w, w ∈ W → deriv f w ≠ 0 := fun w hw ↦ hf_ne w (hWsubset hw)
  have hg_ne_W : ∀ w, w ∈ W → deriv g w ≠ 0 := fun w hw ↦ hg_ne w (hWsubset hw)
  have hf₁_W :
      ∀ w, w ∈ W →
        HasDerivAt
          (fun t : ℂ ↦ deriv f t)
          (deriv (fun t : ℂ ↦ deriv f t) w) w :=
    fun w hw ↦ hf₁ w (hWsubset hw)
  have hg₁_W :
      ∀ w, w ∈ W →
        HasDerivAt
          (fun t : ℂ ↦ deriv g t)
          (deriv (fun t : ℂ ↦ deriv g t) w) w :=
    fun w hw ↦ hg₁ w (hWsubset hw)
  rcases hInt f g W z hWopen hzW hf_ne_W hg_ne_W hf₁_W hg₁_W hpreW hval hderiv with
    ⟨V, hVopen, hzV, hVsubsetW, hVeq⟩
  exact ⟨V, hVopen, hzV, fun w hw ↦ hWsubset (hVsubsetW hw), hVeq⟩

/-- The broad scalar uniqueness theorem implies the explicit-regularity version. -/
theorem scalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem_of_scalar
    (hScalar : ScalarSchwarzianTwoJetValueLocalUniquenessTheorem) :
    ScalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem := by
  intro f g U z hU hz hf_ne hg_ne _hf₁ _hf₂ _hg₁ _hg₂ hschw hval hderiv hsecond
  exact hScalar f g U z hU hz hf_ne hg_ne hschw hval hderiv hsecond

/--
Actual-Schwarzian equation for an upper-half-plane developing branch.

This connects the symbolic Schwarzian data stored by
`LocalProjectiveDevelopingMap` with the actual iterated derivatives used by
the scalar identity principle.
-/
def LocalUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) (z : ℂ),
      z ∈ H.domain →
        actualSchwarzian (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z =
          S.coefficient z

/--
Second-derivative identification for upper-half-plane branches.

The actual derivative of the actual first derivative agrees with the symbolic
second derivative stored by the projective branch.
-/
def LocalUpperHalfPlaneDevelopingMapSecondDerivativeIdentificationTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) (z : ℂ),
      z ∈ H.domain →
        deriv (fun w : ℂ ↦ deriv (fun t : ℂ ↦ (H.upperHalfPlaneMap t : ℂ)) w) z =
          H.projective.affineMapSecondDeriv z

/--
Third-derivative identification for upper-half-plane branches.

The actual derivative of the actual second derivative agrees with the symbolic
third derivative stored by the projective branch.
-/
def LocalUpperHalfPlaneDevelopingMapThirdDerivativeIdentificationTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) (z : ℂ),
      z ∈ H.domain →
        deriv
          (fun w : ℂ ↦
            deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ (H.upperHalfPlaneMap s : ℂ)) t) w)
          z =
          H.projective.affineMapThirdDeriv z

/--
First-derivative regularity gives the second-derivative identification by
taking Lean's `deriv`.
-/
theorem localUpperHalfPlaneDevelopingMapSecondDerivativeIdentificationTheorem_of_firstDerivative
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem) :
    LocalUpperHalfPlaneDevelopingMapSecondDerivativeIdentificationTheorem := by
  intro u S H z hz
  exact (hFirst H hz).deriv

/--
Second-derivative regularity gives the third-derivative identification by
taking Lean's `deriv`.
-/
theorem localUpperHalfPlaneDevelopingMapThirdDerivativeIdentificationTheorem_of_secondDerivative
    (hSecond :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem) :
    LocalUpperHalfPlaneDevelopingMapThirdDerivativeIdentificationTheorem := by
  intro u S H z hz
  exact (hSecond H hz).deriv

/--
The branch actual-Schwarzian equation follows from the usual second- and
third-derivative identifications against the symbolic projective fields.
-/
theorem localUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem_of_second_third
    (hSecond :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeIdentificationTheorem)
    (hThird :
      LocalUpperHalfPlaneDevelopingMapThirdDerivativeIdentificationTheorem) :
    LocalUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem := by
  intro u S H z hz
  rw [actualSchwarzian, schwarzianExpression,
    H.upperHalfPlane_deriv_eq_projectiveDeriv z hz,
    hSecond H z hz, hThird H z hz]
  rw [← schwarzianExpression]
  exact H.projective.schwarzian_eq_coefficient z hz

/--
The branch actual-Schwarzian equation follows from first- and second-derivative
regularity with the stored symbolic second and third derivatives.
-/
theorem localUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem_of_first_second_derivative
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecond :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem) :
    LocalUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem :=
  localUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem_of_second_third
    (localUpperHalfPlaneDevelopingMapSecondDerivativeIdentificationTheorem_of_firstDerivative
      hFirst)
    (localUpperHalfPlaneDevelopingMapThirdDerivativeIdentificationTheorem_of_secondDerivative
      hSecond)

namespace LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Fixed-branch projective derivative regularity identifies the actual Schwarzian
of that branch with its stored symbolic Schwarzian coefficient.
-/
theorem actualSchwarzian_eq_coefficient
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    {z : ℂ} (hz : z ∈ H.domain) :
    actualSchwarzian (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z =
      S.coefficient z := by
  rw [actualSchwarzian, schwarzianExpression,
    H.upperHalfPlane_deriv_eq_projectiveDeriv z hz,
    (R.firstDerivative_hasDerivAt hz).deriv,
    (R.secondDerivative_hasDerivAt hz).deriv]
  rw [← schwarzianExpression]
  exact H.projective.schwarzian_eq_coefficient z hz

end LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Actual-Schwarzian equation after real-Mobius postcomposition.

This is the corresponding symbolic-to-actual and Mobius-invariance bridge for
the postcomposed first branch appearing in the real-transition comparison.
-/
def RealMobiusPostcompositionActualSchwarzianEquationTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) (A : RealMobiusRepresentative)
    (z : ℂ),
      z ∈ H.domain →
        actualSchwarzian
          (fun w : ℂ ↦
            (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ))
          z = S.coefficient z

/--
Actual-Schwarzian invariance under real-Mobius postcomposition of an
upper-half-plane branch.
-/
def RealMobiusPostcompositionActualSchwarzianInvariantTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (H : LocalUpperHalfPlaneDevelopingMap S) (A : RealMobiusRepresentative)
    (z : ℂ),
      z ∈ H.domain →
        actualSchwarzian
          (fun w : ℂ ↦
          (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ))
          z =
        actualSchwarzian (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z

/--
Real Mobius transformations have zero actual Schwarzian in their affine
upper-half-plane coordinate.
-/
def RealMobiusActualSchwarzianZeroTheorem : Prop :=
  ∀ (A : RealMobiusRepresentative) (p : ℍ),
    actualSchwarzian
      (fun w : ℂ ↦
        (realMobiusRepresentativeAction A
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ))
      p = 0

/-- Real Mobius transformations have zero actual Schwarzian. -/
theorem realMobiusActualSchwarzianZeroTheorem :
    RealMobiusActualSchwarzianZeroTheorem := by
  intro A p
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let δ : ℂ := UpperHalfPlane.denom (A : GL (Fin 2) ℝ) p
  let c : ℂ := ((A : GL (Fin 2) ℝ) 1 0 : ℂ)
  have hδ_ne : δ ≠ 0 := by
    simpa [δ] using UpperHalfPlane.denom_ne_zero (A : GL (Fin 2) ℝ) p
  have h₁ : deriv M p = (δ ^ 2)⁻¹ := by
    simpa [M, δ] using realMobiusRepresentativeAction_deriv A p
  have h₂ :
      deriv (fun w : ℂ ↦ deriv M w) p = -2 * c / δ ^ 3 := by
    simpa [M, δ, c] using realMobiusRepresentativeAction_second_deriv A p
  have h₃ :
      deriv (fun w : ℂ ↦ deriv (fun t : ℂ ↦ deriv M t) w) p =
        6 * c ^ 2 / δ ^ 4 := by
    simpa [M, δ, c] using realMobiusRepresentativeAction_third_deriv A p
  rw [actualSchwarzian, schwarzianExpression, h₁, h₂, h₃]
  field_simp [hδ_ne]
  ring

private theorem actualSchwarzian_postcomposition_algebra
    {α β γ F₁ F₂ F₃ : ℂ}
    (hα : α ≠ 0) (hF₁ : F₁ ≠ 0)
    (hM : γ / α - 3 / 2 * (β / α) ^ 2 = 0) :
    (γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃) / (α * F₁) -
        3 / 2 * ((β * F₁ ^ 2 + α * F₂) / (α * F₁)) ^ 2 =
      F₃ / F₁ - 3 / 2 * (F₂ / F₁) ^ 2 := by
  have hαF₁ : α * F₁ ≠ 0 := mul_ne_zero hα hF₁
  have hsplit :
      (γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃) / (α * F₁) -
          3 / 2 * ((β * F₁ ^ 2 + α * F₂) / (α * F₁)) ^ 2 =
        F₃ / F₁ + (γ / α - 3 / 2 * (β / α) ^ 2) * F₁ ^ 2 -
          3 / 2 * (F₂ / F₁) ^ 2 := by
    field_simp [hα, hF₁, hαF₁]
    ring
  rw [hsplit, hM]
  ring

/--
Actual Schwarzian invariance is reduced to the ordinary third-order chain
rule and the fact that real Mobius maps have zero Schwarzian.
-/
theorem realMobiusPostcompositionActualSchwarzianInvariantTheorem_of_thirdChainRule_zero
    (hSecondChain :
      RealMobiusBranchPostcompositionSecondDerivativeChainRuleTheorem)
    (hThirdChain :
      RealMobiusBranchPostcompositionThirdDerivativeChainRuleTheorem)
    (hZero : RealMobiusActualSchwarzianZeroTheorem) :
    RealMobiusPostcompositionActualSchwarzianInvariantTheorem := by
  intro u S H A z hz
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let G : ℂ → ℂ :=
    fun w ↦ (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ)
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let F₁ : ℂ := deriv F z
  let F₂ : ℂ := deriv (fun w ↦ deriv F w) z
  let F₃ : ℂ := deriv (fun w ↦ deriv (fun t ↦ deriv F t) w) z
  let α : ℂ := deriv M (F z)
  let β : ℂ := deriv (fun w ↦ deriv M w) (F z)
  let γ : ℂ := deriv (fun w ↦ deriv (fun t ↦ deriv M t) w) (F z)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hα_ne : α ≠ 0 := by
    simpa [α, M, F] using
      realMobiusRepresentativeAction_deriv_ne_zero A (H.upperHalfPlaneMap z)
  have hG₁ :
      deriv G z = α * F₁ := by
    simpa [G, M, F, α, F₁] using
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H A hz
  have hG₂ :
      deriv (fun w ↦ deriv G w) z = β * F₁ ^ 2 + α * F₂ := by
    simpa [G, M, F, β, α, F₁, F₂] using hSecondChain H A z hz
  have hG₃ :
      deriv (fun w ↦ deriv (fun t ↦ deriv G t) w) z =
        γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃ := by
    simpa [G, M, F, γ, β, α, F₁, F₂, F₃] using hThirdChain H A z hz
  have hM :
      γ / α - 3 / 2 * (β / α) ^ 2 = 0 := by
    have h := hZero A (H.upperHalfPlaneMap z)
    simpa [actualSchwarzian, schwarzianExpression, M, F, γ, β, α] using h
  rw [actualSchwarzian, schwarzianExpression, hG₁, hG₂, hG₃]
  exact actualSchwarzian_postcomposition_algebra hα_ne hF₁_ne hM

namespace LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Fixed-branch projective derivative regularity proves actual-Schwarzian
invariance under postcomposition by a real Mobius transformation.
-/
theorem realMobiusPostcomposition_actualSchwarzian
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    actualSchwarzian
      (fun w : ℂ ↦
        (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ))
      z =
    actualSchwarzian (fun w : ℂ ↦ (H.upperHalfPlaneMap w : ℂ)) z := by
  let F : ℂ → ℂ := fun w ↦ (H.upperHalfPlaneMap w : ℂ)
  let G : ℂ → ℂ :=
    fun w ↦ (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ)
  let M : ℂ → ℂ :=
    fun w ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) w) : ℂ)
  let F₁ : ℂ := deriv F z
  let F₂ : ℂ := deriv (fun w ↦ deriv F w) z
  let F₃ : ℂ := deriv (fun w ↦ deriv (fun t ↦ deriv F t) w) z
  let α : ℂ := deriv M (F z)
  let β : ℂ := deriv (fun w ↦ deriv M w) (F z)
  let γ : ℂ := deriv (fun w ↦ deriv (fun t ↦ deriv M t) w) (F z)
  have hF₁_ne : F₁ ≠ 0 := by
    have hpos := H.upperHalfPlaneDerivativeNormSq_pos hz
    dsimp [complexDerivativeNormSq, F, F₁] at hpos
    exact Complex.normSq_pos.mp hpos
  have hα_ne : α ≠ 0 := by
    simpa [α, M, F] using
      realMobiusRepresentativeAction_deriv_ne_zero A (H.upperHalfPlaneMap z)
  have hG₁ :
      deriv G z = α * F₁ := by
    simpa [G, M, F, α, F₁] using
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H A hz
  have hG₂ :
      deriv (fun w ↦ deriv G w) z = β * F₁ ^ 2 + α * F₂ := by
    simpa [G, M, F, β, α, F₁, F₂] using
      R.realMobiusPostcompositionSecondDerivativeChainRule A hz
  have hG₃ :
      deriv (fun w ↦ deriv (fun t ↦ deriv G t) w) z =
        γ * F₁ ^ 3 + 3 * β * F₁ * F₂ + α * F₃ := by
    simpa [G, M, F, γ, β, α, F₁, F₂, F₃] using
      R.realMobiusPostcompositionThirdDerivativeChainRule A hz
  have hM :
      γ / α - 3 / 2 * (β / α) ^ 2 = 0 := by
    have h := realMobiusActualSchwarzianZeroTheorem A (H.upperHalfPlaneMap z)
    simpa [actualSchwarzian, schwarzianExpression, M, F, γ, β, α] using h
  rw [actualSchwarzian, schwarzianExpression, hG₁, hG₂, hG₃]
  exact actualSchwarzian_postcomposition_algebra hα_ne hF₁_ne hM

/--
Fixed-branch projective derivative regularity gives the Schwarzian equation
for a real-Mobius postcomposition of a metric-recovering branch.
-/
theorem realMobiusPostcomposition_actualSchwarzian_eq_coefficient
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {H : LocalUpperHalfPlaneDevelopingMap S}
    (R : LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity H)
    (A : RealMobiusRepresentative) {z : ℂ} (hz : z ∈ H.domain) :
    actualSchwarzian
      (fun w : ℂ ↦
        (realMobiusRepresentativeAction A (H.upperHalfPlaneMap w) : ℂ))
      z =
    S.coefficient z := by
  rw [R.realMobiusPostcomposition_actualSchwarzian A hz]
  exact R.actualSchwarzian_eq_coefficient hz

end LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity

/--
Actual-Schwarzian invariance plus the branch actual-Schwarzian equation gives
the postcomposition actual-Schwarzian equation.
-/
theorem realMobiusPostcompositionActualSchwarzianEquationTheorem_of_invariant
    (hBranch :
      LocalUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem)
    (hInv :
      RealMobiusPostcompositionActualSchwarzianInvariantTheorem) :
    RealMobiusPostcompositionActualSchwarzianEquationTheorem := by
  intro u S H A z hz
  rw [hInv H A z hz]
  exact hBranch H z hz

/--
The scalar Schwarzian uniqueness theorem implies the value-only pointed
real-Mobius local uniqueness statement, once both compared branches are known
to satisfy the corresponding actual Schwarzian equations.
-/
theorem pointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem_of_actualSchwarzian
    (hBranch :
      LocalUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem)
    (hPost :
      RealMobiusPostcompositionActualSchwarzianEquationTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetValueLocalUniquenessTheorem) :
      PointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ _hu _hpoint hCoeff z hz₁ hz₂ hval hderiv hsecond
  let f : ℂ → ℂ := fun w ↦ (H₂.upperHalfPlaneMap w : ℂ)
  let g : ℂ → ℂ :=
    fun w ↦ (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ)
  let U : Set ℂ := H₁.domain ∩ H₂.domain
  have hUopen : IsOpen U := H₁.projective.isOpen_domain.inter H₂.projective.isOpen_domain
  have hzU : z ∈ U := ⟨hz₁, hz₂⟩
  have hf_ne : ∀ w, w ∈ U → deriv f w ≠ 0 := by
    intro w hw
    have hpos := H₂.upperHalfPlaneDerivativeNormSq_pos hw.2
    dsimp [complexDerivativeNormSq, f] at hpos
    exact Complex.normSq_pos.mp hpos
  have hg_ne : ∀ w, w ∈ U → deriv g w ≠ 0 := by
    intro w hw
    have hchain :=
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H₁ A hw.1
    have hα :
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
          (H₁.upperHalfPlaneMap w) ≠ 0 :=
      realMobiusRepresentativeAction_deriv_ne_zero A (H₁.upperHalfPlaneMap w)
    have hF :
        deriv (fun t : ℂ ↦ (H₁.upperHalfPlaneMap t : ℂ)) w ≠ 0 := by
      have hpos := H₁.upperHalfPlaneDerivativeNormSq_pos hw.1
      dsimp [complexDerivativeNormSq] at hpos
      exact Complex.normSq_pos.mp hpos
    rw [show deriv g w =
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap t) : ℂ))
          w by rfl]
    rw [hchain]
    exact mul_ne_zero hα hF
  have hschw : ∀ w, w ∈ U → actualSchwarzian f w = actualSchwarzian g w := by
    intro w hw
    calc
      actualSchwarzian f w = S₂.coefficient w := by
        simpa [f] using hBranch H₂ w hw.2
      _ = S₁.coefficient w := (hCoeff w hw.1 hw.2).symm
      _ = actualSchwarzian g w := by
        simpa [g] using (hPost H₁ A w hw.1).symm
  rcases hScalar f g U z hUopen hzU hf_ne hg_ne hschw
      (by simpa [f, g] using congrArg (fun p : ℍ ↦ (p : ℂ)) hval)
      (by simpa [f, g] using hderiv)
      (by simpa [f, g] using hsecond) with
    ⟨V, hVopen, hzV, hVsubset, hVeq⟩
  refine ⟨V, hVopen, hzV, hVsubset, ?_⟩
  intro w hw
  exact UpperHalfPlane.coe_inj.mp (by simpa [f, g] using hVeq w hw)

/--
Version of the value-local real-transition uniqueness bridge using the
regular scalar Schwarzian identity principle.  The required C³ hypotheses are
supplied by the branch first/second-derivative packages and the corresponding
real-Mobius postcomposition regularity lemmas.
-/
theorem pointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem_of_actualSchwarzian_c3
    (hBranch :
      LocalUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem)
    (hPost :
      RealMobiusPostcompositionActualSchwarzianEquationTheorem)
    (hFirst :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem)
    (hSecond :
      LocalUpperHalfPlaneDevelopingMapSecondDerivativeHasDerivAtTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetC3ValueLocalUniquenessTheorem) :
      PointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ _hu _hpoint hCoeff z hz₁ hz₂ hval hderiv hsecond
  let f : ℂ → ℂ := fun w ↦ (H₂.upperHalfPlaneMap w : ℂ)
  let g : ℂ → ℂ :=
    fun w ↦ (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap w) : ℂ)
  let U : Set ℂ := H₁.domain ∩ H₂.domain
  have hUopen : IsOpen U := H₁.projective.isOpen_domain.inter H₂.projective.isOpen_domain
  have hzU : z ∈ U := ⟨hz₁, hz₂⟩
  have hf_ne : ∀ w, w ∈ U → deriv f w ≠ 0 := by
    intro w hw
    have hpos := H₂.upperHalfPlaneDerivativeNormSq_pos hw.2
    dsimp [complexDerivativeNormSq, f] at hpos
    exact Complex.normSq_pos.mp hpos
  have hg_ne : ∀ w, w ∈ U → deriv g w ≠ 0 := by
    intro w hw
    have hchain :=
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H₁ A hw.1
    have hα :
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A
              ((UpperHalfPlane.ofComplex : ℂ → ℍ) t) : ℂ))
          (H₁.upperHalfPlaneMap w) ≠ 0 :=
      realMobiusRepresentativeAction_deriv_ne_zero A (H₁.upperHalfPlaneMap w)
    have hF :
        deriv (fun t : ℂ ↦ (H₁.upperHalfPlaneMap t : ℂ)) w ≠ 0 := by
      have hpos := H₁.upperHalfPlaneDerivativeNormSq_pos hw.1
      dsimp [complexDerivativeNormSq] at hpos
      exact Complex.normSq_pos.mp hpos
    rw [show deriv g w =
        deriv
          (fun t : ℂ ↦
            (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap t) : ℂ))
          w by rfl]
    rw [hchain]
    exact mul_ne_zero hα hF
  have hf₁ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv f t)
          (deriv (fun t : ℂ ↦ deriv f t) w) w := by
    intro w hw
    have h := hFirst H₂ hw.2
    convert h using 1
    exact h.deriv
  have hf₂ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t)
          (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv f s) t) w) w := by
    intro w hw
    have h := hSecond H₂ hw.2
    convert h using 1
    exact h.deriv
  have hg₁ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv g t)
          (deriv (fun t : ℂ ↦ deriv g t) w) w := by
    intro w hw
    simpa [g] using
      realMobiusPostcompositionFirstDerivativeHasDerivAt_of_firstDerivative
        hFirst H₁ A hw.1
  have hg₂ :
      ∀ w, w ∈ U →
        HasDerivAt
          (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t)
          (deriv (fun t : ℂ ↦ deriv (fun s : ℂ ↦ deriv g s) t) w) w := by
    intro w hw
    simpa [g] using
      realMobiusPostcompositionSecondDerivativeHasDerivAt_of_first_secondDerivative
        hFirst hSecond H₁ A hw.1
  have hschw : ∀ w, w ∈ U → actualSchwarzian f w = actualSchwarzian g w := by
    intro w hw
    calc
      actualSchwarzian f w = S₂.coefficient w := by
        simpa [f] using hBranch H₂ w hw.2
      _ = S₁.coefficient w := (hCoeff w hw.1 hw.2).symm
      _ = actualSchwarzian g w := by
        simpa [g] using (hPost H₁ A w hw.1).symm
  rcases hScalar f g U z hUopen hzU hf_ne hg_ne hf₁ hf₂ hg₁ hg₂ hschw
      (by simpa [f, g] using congrArg (fun p : ℍ ↦ (p : ℂ)) hval)
      (by simpa [f, g] using hderiv)
      (by simpa [f, g] using hsecond) with
    ⟨V, hVopen, hzV, hVsubset, hVeq⟩
  refine ⟨V, hVopen, hzV, hVsubset, ?_⟩
  intro w hw
  exact UpperHalfPlane.coe_inj.mp (by simpa [f, g] using hVeq w hw)

/--
Version of the value-local real-transition uniqueness bridge using the pure
actual-Schwarzian invariance theorem for real-Mobius postcomposition.
-/
theorem pointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem_of_actualSchwarzian_invariant
    (hBranch :
      LocalUpperHalfPlaneDevelopingMapActualSchwarzianEquationTheorem)
    (hInv :
      RealMobiusPostcompositionActualSchwarzianInvariantTheorem)
    (hScalar :
      ScalarSchwarzianTwoJetValueLocalUniquenessTheorem) :
    PointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem :=
  pointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem_of_actualSchwarzian
    hBranch
    (realMobiusPostcompositionActualSchwarzianEquationTheorem_of_invariant
      hBranch hInv)
    hScalar

/--
The value-only two-jet identity principle implies the one-jet version used by
the clopen propagation argument.  Derivative equality follows from local
equality on the open neighborhood.
-/
theorem pointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem_of_value
    (hValue :
      PointedRealMobiusTransitionTwoJetValueLocalUniquenessWithCoefficientAgreementTheorem) :
    PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ hu hpoint hCoeff z hz₁ hz₂ hval hderiv hsecond
  rcases hValue H₁ H₂ A z₀ hu hpoint hCoeff z hz₁ hz₂ hval hderiv hsecond with
    ⟨U, hUopen, hzU, hUsubset, hUeq⟩
  refine ⟨U, hUopen, hzU, hUsubset, ?_⟩
  intro w hw
  constructor
  · exact hUeq w hw
  · let F : ℂ → ℂ := fun t ↦ (H₂.upperHalfPlaneMap t : ℂ)
    let G : ℂ → ℂ :=
      fun t ↦ (realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap t) : ℂ)
    have hEq : F =ᶠ[nhds w] G := by
      filter_upwards [hUopen.mem_nhds hw] with t ht
      exact congrArg (fun p : ℍ ↦ (p : ℂ)) (hUeq t ht)
    simpa [F, G] using hEq.deriv_eq

/--
Metric second-jet recovery plus two-jet Schwarzian uniqueness gives the
coefficient-aware one-jet local uniqueness theorem used by the clopen
real-transition argument.
-/
theorem pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem_of_metricSecondJet_twoJetUniqueness
    (hSecond :
      PointedRealMobiusTransitionMetricOneJetDeterminesSecondJetTheorem)
    (hTwoJet :
      PointedRealMobiusTransitionTwoJetLocalUniquenessWithCoefficientAgreementTheorem) :
    PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ hu hpoint hCoeff z hz₁ hz₂ hval hderiv
  exact hTwoJet H₁ H₂ A z₀ hu hpoint hCoeff z hz₁ hz₂ hval hderiv
    (hSecond H₁ H₂ A z₀ hu hpoint hCoeff z hz₁ hz₂ hval hderiv)

/--
Coefficient agreement plus the coefficient-aware local uniqueness theorem
gives the broad local one-jet uniqueness target.
-/
theorem pointedRealMobiusTransitionOneJetLocalUniquenessTheorem_of_coefficientAgreement
    (hCoeff :
      MetricRecoveringUpperHalfPlaneBranchesHaveSameSchwarzianCoefficientOnOverlapTheorem)
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem) :
    PointedRealMobiusTransitionOneJetLocalUniquenessTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ hu hpoint z hz₁ hz₂ hval hderiv
  exact hUnique H₁ H₂ A z₀ hu hpoint (hCoeff H₁ H₂ hu) z hz₁ hz₂ hval hderiv

/--
Ambient local uniqueness of one-jet comparisons implies openness of the
one-jet equality locus in the overlap.
-/
theorem pointedRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_localUniqueness
    (hLocal : PointedRealMobiusTransitionOneJetLocalUniquenessTheorem) :
    PointedRealMobiusTransitionOneJetEqualitySetIsOpenTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ hu hpoint
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  let E : Set overlap := pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A
  rw [isOpen_iff_forall_mem_open]
  intro z hzE
  rcases hLocal H₁ H₂ A z₀ hu hpoint (z : ℂ) z.property.1 z.property.2
      hzE.1 hzE.2 with
    ⟨U, hUopen, hzU, hUsubset, hUeq⟩
  refine ⟨Subtype.val ⁻¹' U, ?_, hUopen.preimage continuous_subtype_val, hzU⟩
  intro y hy
  have hyEq := hUeq (y : ℂ) hy
  exact hyEq

/--
For one fixed pair of branches, coefficient agreement and the
coefficient-aware local uniqueness theorem make the one-jet equality locus
open.
-/
theorem pointedRealMobiusTransitionOneJetEqualitySet_isOpen_of_coefficientAgreement
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (hu : u.SolvesLiouvilleEquation)
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z)
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem) :
    IsOpen (pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A) := by
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  let E : Set overlap := pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A
  rw [isOpen_iff_forall_mem_open]
  intro z hzE
  rcases hUnique H₁ H₂ A z₀ hu hpoint hCoeff (z : ℂ) z.property.1
      z.property.2 hzE.1 hzE.2 with
    ⟨U, hUopen, hzU, hUsubset, hUeq⟩
  refine ⟨Subtype.val ⁻¹' U, ?_, hUopen.preimage continuous_subtype_val, hzU⟩
  intro y hy
  exact hUeq (y : ℂ) hy

/-- Closedness plus openness gives the clopen equality-locus target. -/
theorem pointedRealMobiusTransitionEqualitySetIsClopenTheorem_of_closed_open
    (hClosed : PointedRealMobiusTransitionEqualitySetIsClosedTheorem)
    (hOpen : PointedRealMobiusTransitionEqualitySetIsOpenTheorem) :
    PointedRealMobiusTransitionEqualitySetIsClopenTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ hu hpoint
  exact ⟨hClosed H₁ H₂ A z₀ hu hpoint, hOpen H₁ H₂ A z₀ hu hpoint⟩

/-- Closedness plus openness gives the clopen one-jet equality-locus target. -/
theorem pointedRealMobiusTransitionOneJetEqualitySetIsClopenTheorem_of_closed_open
    (hClosed : PointedRealMobiusTransitionOneJetEqualitySetIsClosedTheorem)
    (hOpen : PointedRealMobiusTransitionOneJetEqualitySetIsOpenTheorem) :
    PointedRealMobiusTransitionOneJetEqualitySetIsClopenTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ hu hpoint
  exact ⟨hClosed H₁ H₂ A z₀ hu hpoint, hOpen H₁ H₂ A z₀ hu hpoint⟩

/--
If the pointed equality locus is clopen in the overlap, then preconnectedness
propagates the pointed one-jet comparison across the whole overlap.
-/
theorem pointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_equalitySetClopen
    (hClopen : PointedRealMobiusTransitionEqualitySetIsClopenTheorem) :
    PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ hu hconn hpoint z hz₁ hz₂
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  let E : Set overlap := pointedRealMobiusTransitionEqualitySet H₁ H₂ A
  haveI : PreconnectedSpace overlap := Subtype.preconnectedSpace hconn
  have hE : IsClopen E := hClopen H₁ H₂ A z₀ hu hpoint
  have hbase_mem_overlap : z₀ ∈ overlap := ⟨hpoint.1, hpoint.2.1⟩
  have hbase_mem_E : (⟨z₀, hbase_mem_overlap⟩ : overlap) ∈ E := by
    simpa [E, pointedRealMobiusTransitionEqualitySet] using hpoint.2.2.1
  have hE_univ : E = Set.univ :=
    IsClopen.eq_univ hE ⟨⟨z₀, hbase_mem_overlap⟩, hbase_mem_E⟩
  have hz_mem_overlap : z ∈ overlap := ⟨hz₁, hz₂⟩
  have hz_mem_E : (⟨z, hz_mem_overlap⟩ : overlap) ∈ E := by
    rw [hE_univ]
    exact Set.mem_univ _
  simpa [E, pointedRealMobiusTransitionEqualitySet] using hz_mem_E

/--
If the pointed one-jet equality locus is clopen in the overlap, then
preconnectedness propagates the pointed one-jet comparison across the whole
overlap.
-/
theorem pointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySetClopen
    (hClopen : PointedRealMobiusTransitionOneJetEqualitySetIsClopenTheorem) :
    PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem := by
  intro u S₁ S₂ H₁ H₂ A z₀ hu hconn hpoint z hz₁ hz₂
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  let E : Set overlap := pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A
  haveI : PreconnectedSpace overlap := Subtype.preconnectedSpace hconn
  have hE : IsClopen E := hClopen H₁ H₂ A z₀ hu hpoint
  have hbase_mem_overlap : z₀ ∈ overlap := ⟨hpoint.1, hpoint.2.1⟩
  have hbase_mem_E : (⟨z₀, hbase_mem_overlap⟩ : overlap) ∈ E := by
    simpa [E, pointedRealMobiusTransitionOneJetEqualitySet] using hpoint.2.2
  have hE_univ : E = Set.univ :=
    IsClopen.eq_univ hE ⟨⟨z₀, hbase_mem_overlap⟩, hbase_mem_E⟩
  have hz_mem_overlap : z ∈ overlap := ⟨hz₁, hz₂⟩
  have hz_mem_E : (⟨z, hz_mem_overlap⟩ : overlap) ∈ E := by
    rw [hE_univ]
    exact Set.mem_univ _
  exact hz_mem_E.1

/--
Closedness and openness of the pointed equality locus imply connected-overlap
extension.
-/
theorem pointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_equalitySet_closed_open
    (hClosed : PointedRealMobiusTransitionEqualitySetIsClosedTheorem)
    (hOpen : PointedRealMobiusTransitionEqualitySetIsOpenTheorem) :
    PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem :=
  pointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_equalitySetClopen
    (pointedRealMobiusTransitionEqualitySetIsClopenTheorem_of_closed_open
      hClosed hOpen)

/--
Closedness and openness of the pointed one-jet equality locus imply
connected-overlap extension.
-/
theorem pointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySet_closed_open
    (hClosed : PointedRealMobiusTransitionOneJetEqualitySetIsClosedTheorem)
    (hOpen : PointedRealMobiusTransitionOneJetEqualitySetIsOpenTheorem) :
    PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem :=
  pointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySetClopen
    (pointedRealMobiusTransitionOneJetEqualitySetIsClopenTheorem_of_closed_open
      hClosed hOpen)

/--
Closedness plus local one-jet uniqueness imply connected-overlap extension.
-/
theorem pointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySet_closed_localUniqueness
    (hClosed : PointedRealMobiusTransitionOneJetEqualitySetIsClosedTheorem)
    (hLocal : PointedRealMobiusTransitionOneJetLocalUniquenessTheorem) :
    PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem :=
  pointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySet_closed_open
    hClosed
    (pointedRealMobiusTransitionOneJetEqualitySetIsOpenTheorem_of_localUniqueness
      hLocal)

/--
Branch regularity plus local one-jet uniqueness imply connected-overlap
extension.
-/
theorem pointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_branch_continuity_localUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hLocal : PointedRealMobiusTransitionOneJetLocalUniquenessTheorem) :
    PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem :=
  pointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySet_closed_localUniqueness
    (pointedRealMobiusTransitionOneJetEqualitySetIsClosedTheorem_of_branch_continuity
      hBranch hAffine)
    hLocal

/--
Fixed-pair connected-overlap extension from branch regularity, coefficient
agreement, and the coefficient-aware one-jet uniqueness theorem.
-/
theorem pointedRealMobiusTransition_extendsOnPreconnectedOverlap_of_branch_continuity_coefficientAgreement
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem)
    {u : LocalConformalFactor} {S₁ S₂ : LocalSchwarzianData u}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (A : RealMobiusRepresentative) (z₀ : ℂ)
    (hu : u.SolvesLiouvilleEquation)
    (hconn : IsPreconnected (H₁.domain ∩ H₂.domain))
    (hpoint : H₁.HasPointedRealMobiusTransition H₂ A z₀)
    (hCoeff :
      ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
        S₁.coefficient z = S₂.coefficient z) :
    ∀ z, z ∈ H₁.domain → z ∈ H₂.domain →
      H₂.upperHalfPlaneMap z =
        realMobiusRepresentativeAction A (H₁.upperHalfPlaneMap z) := by
  intro z hz₁ hz₂
  let overlap : Set ℂ := H₁.domain ∩ H₂.domain
  let E : Set overlap := pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A
  haveI : PreconnectedSpace overlap := Subtype.preconnectedSpace hconn
  have hClosed :
      IsClosed E :=
    pointedRealMobiusTransitionOneJetEqualitySetIsClosedTheorem_of_branch_continuity
      hBranch hAffine H₁ H₂ A z₀ hu hpoint
  have hOpen : IsOpen E :=
    pointedRealMobiusTransitionOneJetEqualitySet_isOpen_of_coefficientAgreement
      H₁ H₂ A z₀ hu hpoint hCoeff hUnique
  have hE : IsClopen E := ⟨hClosed, hOpen⟩
  have hbase_mem_overlap : z₀ ∈ overlap := ⟨hpoint.1, hpoint.2.1⟩
  have hbase_mem_E : (⟨z₀, hbase_mem_overlap⟩ : overlap) ∈ E := by
    simpa [E, pointedRealMobiusTransitionOneJetEqualitySet] using hpoint.2.2
  have hE_univ : E = Set.univ :=
    IsClopen.eq_univ hE ⟨⟨z₀, hbase_mem_overlap⟩, hbase_mem_E⟩
  have hz_mem_overlap : z ∈ overlap := ⟨hz₁, hz₂⟩
  have hz_mem_E : (⟨z, hz_mem_overlap⟩ : overlap) ∈ E := by
    rw [hE_univ]
    exact Set.mem_univ _
  exact hz_mem_E.1

/--
Pointed real-Mobius one-jet normalization plus connected-overlap extension
give the nonempty-overlap branch real-transition theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_pointed
    (hPoint :
      MetricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem := by
  intro u S₁ S₂ H₁ H₂ hu hconn hne
  rcases hne with ⟨z₀, hz₀₁, hz₀₂⟩
  rcases hPoint H₁ H₂ hu hz₀₁ hz₀₂ with ⟨A, hA⟩
  exact ⟨A, hExtend H₁ H₂ A z₀ hu hconn hA⟩

/--
Pointed one-jet transitivity from equal hyperbolic derivative norms, together
with connected-overlap extension, gives the nonempty-overlap branch
real-transition theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_hyperbolicDerivativeNorm
    (hNorm :
      PointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_pointed
    (metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_hyperbolicDerivativeNorm
      hNorm)
    hExtend

/--
Value transitivity, stabilizer tangent transitivity, and connected-overlap
extension give the nonempty-overlap branch real-transition theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_value_stabilizer
    (hValue : RealMobiusValueTransitivityOnUpperHalfPlaneTheorem)
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_pointed
    (metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem_of_value_stabilizer
      hValue hStabilizer)
    hExtend

/--
With value transitivity proved explicitly, stabilizer tangent transitivity and
connected-overlap extension give the nonempty-overlap branch real-transition
theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_stabilizer
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_value_stabilizer
    realMobiusValueTransitivityOnUpperHalfPlaneTheorem hStabilizer hExtend

/--
Rotation tangent transitivity at `i`, transport to arbitrary stabilizers, and
connected-overlap extension give the nonempty-overlap branch real-transition
theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_rotations
    (hRot : RealMobiusRotationAtITangentTransitivityTheorem)
    (hTransport : RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_stabilizer
    (hTransport hRot) hExtend

/--
The unit-complex rotation multiplier theorem, transport to arbitrary
stabilizers, and connected-overlap extension give the nonempty-overlap branch
real-transition theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_unitMultiplier
    (hUnit : UnitComplexRotationMultiplierTheorem)
    (hTransport : RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_rotations
    (realMobiusRotationAtITangentTransitivityTheorem_of_unitMultiplier hUnit)
    hTransport hExtend

/--
Since rotation tangent transitivity at `i` is proved, stabilizer transport and
connected-overlap extension give the nonempty-overlap branch real-transition
theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_rotationTransport
    (hTransport : RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_rotations
    realMobiusRotationAtITangentTransitivityTheorem hTransport hExtend

/--
After the pointed theorem is proved, connected-overlap extension is the only
remaining input for the nonempty-overlap branch real-transition theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_extension
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_pointed
    metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem
    hExtend

/--
Branch regularity and local one-jet uniqueness give real-Mobius transitions on
nonempty preconnected overlaps.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_branch_continuity_localUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hLocal : PointedRealMobiusTransitionOneJetLocalUniquenessTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_extension
    (pointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem_of_branch_continuity_localUniqueness
      hBranch hAffine hLocal)

/--
The nonempty-overlap branch uniqueness target implies the older branch-level
target; empty overlaps are discharged by vacuity.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_nonemptyOverlap
    (h :
      MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem := by
  intro u S₁ S₂ H₁ H₂ hu hconn
  by_cases hne : Set.Nonempty (H₁.domain ∩ H₂.domain)
  · exact h H₁ H₂ hu hconn hne
  · refine ⟨1, ?_⟩
    intro z hz₁ hz₂
    exfalso
    exact hne ⟨z, ⟨hz₁, hz₂⟩⟩

/--
The pointed normalization and extension formulation implies the older
branch-level real-transition theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_pointed
    (hPoint :
      MetricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_nonemptyOverlap
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_pointed
      hPoint hExtend)

/--
Branch regularity and local one-jet uniqueness imply the older branch-level
real-transition theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_branch_continuity_localUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hLocal : PointedRealMobiusTransitionOneJetLocalUniquenessTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_nonemptyOverlap
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_branch_continuity_localUniqueness
      hBranch hAffine hLocal)

/--
The equal-hyperbolic-derivative-norm one-jet transitivity theorem plus
connected-overlap extension implies the older branch-level real-transition
theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_hyperbolicDerivativeNorm
    (hNorm :
      PointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_nonemptyOverlap
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_hyperbolicDerivativeNorm
      hNorm hExtend)

/--
Value transitivity, stabilizer tangent transitivity, and connected-overlap
extension imply the older branch-level real-transition theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_value_stabilizer
    (hValue : RealMobiusValueTransitivityOnUpperHalfPlaneTheorem)
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_nonemptyOverlap
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_value_stabilizer
      hValue hStabilizer hExtend)

/--
With value transitivity proved explicitly, stabilizer tangent transitivity and
connected-overlap extension imply the older branch-level real-transition
theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_stabilizer
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_value_stabilizer
    realMobiusValueTransitivityOnUpperHalfPlaneTheorem hStabilizer hExtend

/--
Rotation tangent transitivity at `i`, transport to arbitrary stabilizers, and
connected-overlap extension imply the older branch-level real-transition
theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_rotations
    (hRot : RealMobiusRotationAtITangentTransitivityTheorem)
    (hTransport : RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_stabilizer
    (hTransport hRot) hExtend

/--
The unit-complex rotation multiplier theorem, transport to arbitrary
stabilizers, and connected-overlap extension imply the older branch-level
real-transition theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_unitMultiplier
    (hUnit : UnitComplexRotationMultiplierTheorem)
    (hTransport : RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_rotations
    (realMobiusRotationAtITangentTransitivityTheorem_of_unitMultiplier hUnit)
    hTransport hExtend

/--
Since rotation tangent transitivity at `i` is proved, stabilizer transport and
connected-overlap extension imply the older branch-level real-transition
theorem.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_rotationTransport
    (hTransport : RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_rotations
    realMobiusRotationAtITangentTransitivityTheorem hTransport hExtend

/--
For the older branch-level real-transition theorem, connected-overlap
extension is now the only remaining input.
-/
theorem metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_extension
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem :=
  metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem_of_pointed
    metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem
    hExtend

end

end JJMath
