import JJMath.Hyperbolic.Schwarzian.Developing.PullbackLiouville

/-!
# Split Schwarzian developing-map constructions
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

/--
A pointwise local family of metric-recovering Schwarzian normalizations on one
coordinate domain, before imposing connectedness of overlaps.

This is the direct output of the local Schwarzian ODE existence theorem plus
the metric-recovering Mobius-normalization theorem: around every point there is
a normalized `ℍ`-valued branch recovering the metric.  The remaining atlas
shrink is to arrange preconnected pairwise overlaps.
-/
structure LocalMetricRecoveringSchwarzianPreAtlas
    (u : LocalConformalFactor) where
  /-- The local Schwarzian data chosen near each point. -/
  schwarzianAt : u.coordinateDomain → LocalSchwarzianData u
  /-- The local projective Schwarzian solution chosen near each point. -/
  projectiveAt : ∀ z : u.coordinateDomain, LocalProjectiveDevelopingMap (schwarzianAt z)
  /-- The metric-recovering Mobius normalization of each local solution. -/
  normalizationAt :
    ∀ z : u.coordinateDomain, LocalMetricRecoveringUpperHalfPlaneNormalization (projectiveAt z)
  /-- The chosen normalized branch at `z` is defined at `z`. -/
  mem_normalized_domain :
    ∀ z : u.coordinateDomain, (z : ℂ) ∈ (normalizationAt z).normalized.domain

namespace LocalMetricRecoveringSchwarzianPreAtlas

/-- The normalized upper-half-plane branch chosen near a point. -/
def normalizedBranch {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianPreAtlas u) (z : u.coordinateDomain) :
    LocalUpperHalfPlaneDevelopingMap (A.schwarzianAt z) :=
  (A.normalizationAt z).normalized

/-- The normalized branches cover the coordinate domain. -/
theorem mem_normalizedBranch_domain {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianPreAtlas u)
    (z : u.coordinateDomain) :
    (z : ℂ) ∈ (A.normalizedBranch z).domain :=
  A.mem_normalized_domain z

end LocalMetricRecoveringSchwarzianPreAtlas

/--
A pointwise metric-recovering Schwarzian pre-atlas whose branch domains are
already ball-shaped.

This is the natural output of the two-jet construction: for each base point we
choose the shrunk two-jet normalization itself, so its ball-domain witness is
retained instead of imposing a universal condition on every possible pre-atlas.
-/
structure LocalMetricRecoveringSchwarzianBallPreAtlas
    (u : LocalConformalFactor) extends LocalMetricRecoveringSchwarzianPreAtlas u where
  /-- Each chosen normalized branch domain is a complex metric ball. -/
  ball_domain :
    ∀ z : u.coordinateDomain,
      ∃ c r, (toLocalMetricRecoveringSchwarzianPreAtlas.normalizationAt z).normalized.domain =
        Metric.ball c r

namespace LocalMetricRecoveringSchwarzianBallPreAtlas

/-- Forget the ball-domain witnesses. -/
def toPreAtlas {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianBallPreAtlas u) :
    LocalMetricRecoveringSchwarzianPreAtlas u :=
  A.toLocalMetricRecoveringSchwarzianPreAtlas

/-- The ball-domain witnesses imply preconnected overlaps by mathlib convexity. -/
theorem overlap_preconnected {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianBallPreAtlas u) :
    ∀ z w : u.coordinateDomain, IsPreconnected
      ((A.normalizationAt z).normalized.domain ∩
        (A.normalizationAt w).normalized.domain) := by
  intro z w
  rcases A.ball_domain z with ⟨cz, rz, hz⟩
  rcases A.ball_domain w with ⟨cw, rw, hw⟩
  rw [hz, hw]
  exact ((convex_ball cz rz).inter (convex_ball cw rw)).isPreconnected

end LocalMetricRecoveringSchwarzianBallPreAtlas

/--
A local atlas of metric-recovering Schwarzian normalizations on one coordinate
domain.

This is the local object needed before analytic continuation: each point of the
coordinate domain gets a Schwarzian coefficient, a projective solution of the
Schwarzian ODE, and a Mobius postcomposition that normalizes that solution to
an `ℍ`-valued metric-recovering branch.  The overlap preconnectedness field is
the geometric hypothesis under which a single real Mobius transition is
expected on each overlap.
-/
structure LocalMetricRecoveringSchwarzianNormalizationAtlas
    (u : LocalConformalFactor) where
  /-- The local Schwarzian data chosen near each point. -/
  schwarzianAt : u.coordinateDomain → LocalSchwarzianData u
  /-- The local projective Schwarzian solution chosen near each point. -/
  projectiveAt : ∀ z : u.coordinateDomain, LocalProjectiveDevelopingMap (schwarzianAt z)
  /-- The metric-recovering Mobius normalization of each local solution. -/
  normalizationAt :
    ∀ z : u.coordinateDomain, LocalMetricRecoveringUpperHalfPlaneNormalization (projectiveAt z)
  /-- The chosen normalized branch at `z` is defined at `z`, for points in the coordinate domain. -/
  mem_normalized_domain :
    ∀ z : u.coordinateDomain, (z : ℂ) ∈ (normalizationAt z).normalized.domain
  /-- Overlaps of chosen normalized branches are preconnected. -/
  overlap_preconnected :
    ∀ z w : u.coordinateDomain, IsPreconnected
      ((normalizationAt z).normalized.domain ∩ (normalizationAt w).normalized.domain)

namespace LocalMetricRecoveringSchwarzianNormalizationAtlas

/-- Forget overlap connectedness, retaining the pointwise normalized branches. -/
def toPreAtlas {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianNormalizationAtlas u) :
    LocalMetricRecoveringSchwarzianPreAtlas u where
  schwarzianAt := A.schwarzianAt
  projectiveAt := A.projectiveAt
  normalizationAt := A.normalizationAt
  mem_normalized_domain := A.mem_normalized_domain

/-- Upgrade a pre-atlas to an atlas once preconnected overlaps have been supplied. -/
def ofPreAtlas {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianPreAtlas u)
    (hOverlap :
      ∀ z w : u.coordinateDomain, IsPreconnected
        ((A.normalizationAt z).normalized.domain ∩
          (A.normalizationAt w).normalized.domain)) :
    LocalMetricRecoveringSchwarzianNormalizationAtlas u where
  schwarzianAt := A.schwarzianAt
  projectiveAt := A.projectiveAt
  normalizationAt := A.normalizationAt
  mem_normalized_domain := A.mem_normalized_domain
  overlap_preconnected := hOverlap

/-- The normalized upper-half-plane branch chosen near a point. -/
def normalizedBranch {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianNormalizationAtlas u) (z : u.coordinateDomain) :
    LocalUpperHalfPlaneDevelopingMap (A.schwarzianAt z) :=
  (A.normalizationAt z).normalized

/-- The normalized branches cover the coordinate domain. -/
theorem mem_normalizedBranch_domain {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianNormalizationAtlas u)
    (z : u.coordinateDomain) :
    (z : ℂ) ∈ (A.normalizedBranch z).domain :=
  A.mem_normalized_domain z

/--
The local real-transition theorem supplies real Mobius transitions between all
normalized branches in the atlas.
-/
theorem normalizedBranch_transition_realMobius
    (h : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) (z w : u.coordinateDomain) :
    (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch w) :=
  h (A.normalizedBranch z) (A.normalizedBranch w) hu (A.overlap_preconnected z w)

/--
Equivalently, the chosen Mobius-normalized projective solutions have real
Mobius transitions on overlaps.
-/
theorem normalization_transition_realMobius
    (h : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) (z w : u.coordinateDomain) :
    (A.normalizationAt z).HasRealMobiusTransition (A.normalizationAt w) :=
  LocalMetricRecoveringUpperHalfPlaneNormalization.hasRealMobiusTransition_of_branches
    h (A.normalizationAt z) (A.normalizationAt w) hu (A.overlap_preconnected z w)

end LocalMetricRecoveringSchwarzianNormalizationAtlas

/--
A metric-recovering Schwarzian normalization atlas that keeps the stronger
metric-Schwarzian data at each chosen center.

The older `LocalMetricRecoveringSchwarzianNormalizationAtlas` stores only the
underlying `LocalSchwarzianData`, so it forgets the proof that each
coefficient is the canonical metric Schwarzian of `u`.  This strengthened
atlas retains those witnesses, which makes coefficient agreement on overlaps
formal.
-/
structure LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas
    (u : LocalConformalFactor) where
  /-- Metric-Schwarzian data chosen near each point. -/
  metricSchwarzianAt : u.coordinateDomain → LocalMetricSchwarzianData u
  /-- The local projective Schwarzian solution chosen near each point. -/
  projectiveAt :
    ∀ z : u.coordinateDomain,
      LocalProjectiveDevelopingMap ((metricSchwarzianAt z).toLocalSchwarzianData)
  /-- The metric-recovering Mobius normalization of each local solution. -/
  normalizationAt :
    ∀ z : u.coordinateDomain,
      LocalMetricRecoveringUpperHalfPlaneNormalization (projectiveAt z)
  /-- The chosen normalized branch at `z` is defined at `z`. -/
  mem_normalized_domain :
    ∀ z : u.coordinateDomain, (z : ℂ) ∈ (normalizationAt z).normalized.domain
  /-- Overlaps of chosen normalized branches are preconnected. -/
  overlap_preconnected :
    ∀ z w : u.coordinateDomain, IsPreconnected
      ((normalizationAt z).normalized.domain ∩ (normalizationAt w).normalized.domain)

namespace LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas

/-- The underlying Schwarzian data of a metric-data normalization atlas. -/
def schwarzianAt {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas u)
    (z : u.coordinateDomain) : LocalSchwarzianData u :=
  (A.metricSchwarzianAt z).toLocalSchwarzianData

/-- The normalized upper-half-plane branch chosen near a point. -/
def normalizedBranch {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas u)
    (z : u.coordinateDomain) :
    LocalUpperHalfPlaneDevelopingMap (A.schwarzianAt z) :=
  (A.normalizationAt z).normalized

/-- Forget the metric-Schwarzian witnesses. -/
def toLocalMetricRecoveringSchwarzianNormalizationAtlas {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas u) :
    LocalMetricRecoveringSchwarzianNormalizationAtlas u where
  schwarzianAt := A.schwarzianAt
  projectiveAt := A.projectiveAt
  normalizationAt := A.normalizationAt
  mem_normalized_domain := A.mem_normalized_domain
  overlap_preconnected := A.overlap_preconnected

/-- The metric-Schwarzian witnesses make branch coefficient agreement formal. -/
theorem sameSchwarzianCoefficientOnOverlap {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas u)
    (z w : u.coordinateDomain) :
    ∀ x, x ∈ (A.normalizedBranch z).domain →
      x ∈ (A.normalizedBranch w).domain →
        (A.schwarzianAt z).coefficient x = (A.schwarzianAt w).coefficient x :=
  sameSchwarzianCoefficientOnOverlap_of_originalMetricIdentifications
    (A.normalizedBranch z) (A.normalizedBranch w)
    (A.metricSchwarzianAt z).originalMetricIdentification
    (A.metricSchwarzianAt w).originalMetricIdentification

/--
For metric-data normalization atlases, branch regularity and the
coefficient-aware Schwarzian one-jet uniqueness theorem give real Mobius
transitions on nonempty overlaps.
-/
theorem hasOverlappingOffDiagonalRealTransitions_of_branchContinuity_affineDerivative_oneJetUniqueness
    (hBranch : LocalUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem)
    (hAffine :
      LocalUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem)
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) :
    ∀ z w : u.coordinateDomain, z ≠ w →
      Set.Nonempty ((A.normalizedBranch z).domain ∩ (A.normalizedBranch w).domain) →
        (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch w) := by
  intro z w _hzw hne
  rcases hne with ⟨z₀, hz₀z, hz₀w⟩
  rcases metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem
      (A.normalizedBranch z) (A.normalizedBranch w) hu hz₀z hz₀w with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  exact pointedRealMobiusTransition_extendsOnPreconnectedOverlap_of_branch_continuity_coefficientAgreement
    hBranch hAffine hUnique
    (A.normalizedBranch z) (A.normalizedBranch w) M z₀ hu
    (A.overlap_preconnected z w) hM
    (A.sameSchwarzianCoefficientOnOverlap z w)

/--
For metric-data normalization atlases, the symbolic projective derivative
package supplies the branch regularity and coefficient-aware one-jet uniqueness
needed for real Mobius transitions on nonempty overlaps.  The coefficient
agreement itself is supplied by the metric-Schwarzian witnesses stored in the
atlas.
-/
theorem hasOverlappingOffDiagonalRealTransitions_of_projectiveFirstSecondDerivative_scalarClosed
    (hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem)
    (hProjSecond :
      LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) :
    ∀ z w : u.coordinateDomain, z ≠ w →
      Set.Nonempty ((A.normalizedBranch z).domain ∩ (A.normalizedBranch w).domain) →
        (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch w) := by
  have hFirst :
      LocalUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem :=
    localUpperHalfPlaneDevelopingMapFirstDerivativeHasDerivAtTheorem_of_projectiveFirstDerivative
      hProjFirst
  exact
    A.hasOverlappingOffDiagonalRealTransitions_of_branchContinuity_affineDerivative_oneJetUniqueness
      localUpperHalfPlaneDevelopingMapContinuousOnDomainTheorem
      (localUpperHalfPlaneDevelopingMapAffineDerivativeContinuousOnDomainTheorem_of_firstDerivative
        hFirst)
      (pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementTheorem_of_projectiveFirstSecondDerivative_scalarClosed
        hProjFirst hProjSecond)
      hu

end LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas

/--
A metric-Schwarzian normalization atlas that also keeps the projective
derivative algebra for each selected normalized branch.

The preceding metric-data atlas is enough to make coefficient agreement on
overlaps formal.  This strengthened version additionally records the two
symbolic derivative facts needed by the real-transition uniqueness stack:
the stored affine derivative differentiates to the stored second derivative,
and the stored second derivative differentiates to the stored third derivative.
-/
structure LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas
    (u : LocalConformalFactor)
    extends LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas u where
  /-- The stored first projective derivative has the stored second derivative. -/
  projectiveFirstDerivative_hasDerivAt :
    ∀ z : u.coordinateDomain, ∀ x : ℂ,
      x ∈ (toLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.normalizedBranch z).domain →
        HasDerivAt
          (fun w : ℂ ↦
            (toLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.normalizedBranch z).projective.affineMapDeriv w)
          ((toLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.normalizedBranch z).projective.affineMapSecondDeriv x)
          x
  /-- The stored second projective derivative has the stored third derivative. -/
  projectiveSecondDerivative_hasDerivAt :
    ∀ z : u.coordinateDomain, ∀ x : ℂ,
      x ∈ (toLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.normalizedBranch z).domain →
        HasDerivAt
          (fun w : ℂ ↦
            (toLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.normalizedBranch z).projective.affineMapSecondDeriv w)
          ((toLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas.normalizedBranch z).projective.affineMapThirdDeriv x)
          x

namespace LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas

/-- Forget derivative algebra, retaining only the metric-Schwarzian data atlas. -/
def toMetricDataAtlas {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas u) :
    LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas u :=
  A.toLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas

/-- The normalized branch chosen by a derivative-data atlas. -/
def normalizedBranch {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas u)
    (z : u.coordinateDomain) :
    LocalUpperHalfPlaneDevelopingMap (A.toMetricDataAtlas.schwarzianAt z) :=
  A.toMetricDataAtlas.normalizedBranch z

/--
Each normalized branch in a derivative-data atlas carries the fixed-branch
projective derivative regularity package.
-/
theorem normalizedBranch_projectiveDerivativeRegularity {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas u)
    (z : u.coordinateDomain) :
    LocalUpperHalfPlaneDevelopingMapProjectiveDerivativeRegularity
      (A.normalizedBranch z) where
  projectiveFirstDerivative_hasDerivAt := by
    intro x hx
    simpa [normalizedBranch, toMetricDataAtlas] using
      A.projectiveFirstDerivative_hasDerivAt z x hx
  projectiveSecondDerivative_hasDerivAt := by
    intro x hx
    simpa [normalizedBranch, toMetricDataAtlas] using
      A.projectiveSecondDerivative_hasDerivAt z x hx

/-- Coefficient agreement on overlaps is inherited from the metric-data atlas. -/
theorem sameSchwarzianCoefficientOnOverlap {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas u)
    (z w : u.coordinateDomain) :
    ∀ x, x ∈ (A.normalizedBranch z).domain →
      x ∈ (A.normalizedBranch w).domain →
        (A.toMetricDataAtlas.schwarzianAt z).coefficient x =
          (A.toMetricDataAtlas.schwarzianAt w).coefficient x :=
  A.toMetricDataAtlas.sameSchwarzianCoefficientOnOverlap z w

/--
The derivative-data atlas reduces nonempty-overlap real transitions to the
pair-shaped coefficient-aware local uniqueness theorem.
-/
theorem hasOverlappingOffDiagonalRealTransitionOneJets_of_pairProjectiveDerivativeUniqueness
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) :
    ∀ z w : u.coordinateDomain, z ≠ w →
      Set.Nonempty ((A.normalizedBranch z).domain ∩ (A.normalizedBranch w).domain) →
        ∃ M : RealMobiusRepresentative,
          ∀ x, x ∈ (A.normalizedBranch z).domain →
            x ∈ (A.normalizedBranch w).domain →
              (A.normalizedBranch w).upperHalfPlaneMap x =
                  realMobiusRepresentativeAction M
                    ((A.normalizedBranch z).upperHalfPlaneMap x) ∧
                deriv
                    (fun t : ℂ ↦
                      ((A.normalizedBranch w).upperHalfPlaneMap t : ℂ)) x =
                  deriv
                    (fun t : ℂ ↦
                      (realMobiusRepresentativeAction M
                        ((A.normalizedBranch z).upperHalfPlaneMap t) : ℂ)) x := by
  intro z w _hzw hne
  rcases hne with ⟨z₀, hz₀z, hz₀w⟩
  rcases metricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem
      (A.normalizedBranch z) (A.normalizedBranch w) hu hz₀z hz₀w with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  exact
    pointedRealMobiusTransition_oneJetExtendsOnPreconnectedOverlap_of_pairProjectiveDerivative_coefficientAgreement
      hUnique
      (A.normalizedBranch z) (A.normalizedBranch w) M z₀
      (A.normalizedBranch_projectiveDerivativeRegularity z)
      (A.normalizedBranch_projectiveDerivativeRegularity w)
      hu (A.overlap_preconnected z w) hM
      (A.sameSchwarzianCoefficientOnOverlap z w)

/--
Derivative-data normalization atlases have full one-jet real-Mobius
comparisons between every pair of selected normalized branches.

The diagonal case is the identity Mobius transformation, empty overlaps are
vacuous, and the only genuine analytic case is the off-diagonal nonempty
overlap handled by the fixed-pair one-jet clopen theorem.
-/
theorem transition_realMobiusOneJets_of_pairProjectiveDerivativeUniqueness
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) :
    ∀ z w : u.coordinateDomain,
      ∃ M : RealMobiusRepresentative,
        ∀ x, x ∈ (A.normalizedBranch z).domain →
          x ∈ (A.normalizedBranch w).domain →
            (A.normalizedBranch w).upperHalfPlaneMap x =
                realMobiusRepresentativeAction M
                  ((A.normalizedBranch z).upperHalfPlaneMap x) ∧
              deriv
                  (fun t : ℂ ↦
                    ((A.normalizedBranch w).upperHalfPlaneMap t : ℂ)) x =
                deriv
                  (fun t : ℂ ↦
                    (realMobiusRepresentativeAction M
                      ((A.normalizedBranch z).upperHalfPlaneMap t) : ℂ)) x := by
  intro z w
  by_cases hzw : z = w
  · subst w
    refine ⟨1, ?_⟩
    intro x _hxz _hxw
    simp [realMobiusRepresentativeAction_one]
  · by_cases hne :
      Set.Nonempty ((A.normalizedBranch z).domain ∩ (A.normalizedBranch w).domain)
    · exact
        A.hasOverlappingOffDiagonalRealTransitionOneJets_of_pairProjectiveDerivativeUniqueness
          hUnique hu z w hzw hne
    · refine ⟨1, ?_⟩
      intro x hxz hxw
      exfalso
      exact hne ⟨x, ⟨hxz, hxw⟩⟩

/--
Derivative-data normalization atlases have value-level real-Mobius transitions
between every pair of selected normalized branches, by forgetting the
derivative component of the all-pairs one-jet comparison.
-/
theorem transition_realMobius_of_pairProjectiveDerivativeUniqueness
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) :
    ∀ z w : u.coordinateDomain,
      (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch w) := by
  intro z w
  rcases A.transition_realMobiusOneJets_of_pairProjectiveDerivativeUniqueness
      hUnique hu z w with
    ⟨M, hM⟩
  exact ⟨M, fun x hxz hxw ↦ (hM x hxz hxw).1⟩

/--
The derivative-data atlas reduces nonempty-overlap real transitions to the
pair-shaped coefficient-aware local uniqueness theorem.
-/
theorem hasOverlappingOffDiagonalRealTransitions_of_pairProjectiveDerivativeUniqueness
    (hUnique :
      PointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) :
    ∀ z w : u.coordinateDomain, z ≠ w →
      Set.Nonempty ((A.normalizedBranch z).domain ∩ (A.normalizedBranch w).domain) →
        (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch w) := by
  intro z w hzw hne
  rcases A.hasOverlappingOffDiagonalRealTransitionOneJets_of_pairProjectiveDerivativeUniqueness
      hUnique hu z w hzw hne with
    ⟨M, hM⟩
  exact ⟨M, fun x hxz hxw ↦ (hM x hxz hxw).1⟩

/--
The derivative-data atlas can use the proved global projective-derivative
Schwarzian uniqueness route through its pair-shaped transition interface.
-/
theorem hasOverlappingOffDiagonalRealTransitions_of_projectiveFirstSecondDerivative_scalarClosed
    (hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem)
    (hProjSecond :
      LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) :
    ∀ z w : u.coordinateDomain, z ≠ w →
      Set.Nonempty ((A.normalizedBranch z).domain ∩ (A.normalizedBranch w).domain) →
        (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch w) :=
  A.hasOverlappingOffDiagonalRealTransitions_of_pairProjectiveDerivativeUniqueness
    (pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem_of_projectiveFirstSecondDerivative_scalarClosed
      hProjFirst hProjSecond)
    hu

/--
The derivative-data atlas can use the proved projective-derivative
Schwarzian uniqueness route to propagate the full one-jet comparison on
nonempty overlaps.
-/
theorem hasOverlappingOffDiagonalRealTransitionOneJets_of_projectiveFirstSecondDerivative_scalarClosed
    (hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem)
    (hProjSecond :
      LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) :
    ∀ z w : u.coordinateDomain, z ≠ w →
      Set.Nonempty ((A.normalizedBranch z).domain ∩ (A.normalizedBranch w).domain) →
        ∃ M : RealMobiusRepresentative,
          ∀ x, x ∈ (A.normalizedBranch z).domain →
            x ∈ (A.normalizedBranch w).domain →
              (A.normalizedBranch w).upperHalfPlaneMap x =
                  realMobiusRepresentativeAction M
                    ((A.normalizedBranch z).upperHalfPlaneMap x) ∧
                deriv
                    (fun t : ℂ ↦
                      ((A.normalizedBranch w).upperHalfPlaneMap t : ℂ)) x =
                  deriv
                    (fun t : ℂ ↦
                      (realMobiusRepresentativeAction M
                        ((A.normalizedBranch z).upperHalfPlaneMap t) : ℂ)) x :=
  A.hasOverlappingOffDiagonalRealTransitionOneJets_of_pairProjectiveDerivativeUniqueness
    (pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem_of_projectiveFirstSecondDerivative_scalarClosed
      hProjFirst hProjSecond)
    hu

/--
The proved projective-derivative Schwarzian uniqueness route gives full
one-jet real-Mobius comparisons between every pair of selected normalized
branches in a derivative-data atlas.
-/
theorem transition_realMobiusOneJets_of_projectiveFirstSecondDerivative_scalarClosed
    (hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem)
    (hProjSecond :
      LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) :
    ∀ z w : u.coordinateDomain,
      ∃ M : RealMobiusRepresentative,
        ∀ x, x ∈ (A.normalizedBranch z).domain →
          x ∈ (A.normalizedBranch w).domain →
            (A.normalizedBranch w).upperHalfPlaneMap x =
                realMobiusRepresentativeAction M
                  ((A.normalizedBranch z).upperHalfPlaneMap x) ∧
              deriv
                  (fun t : ℂ ↦
                    ((A.normalizedBranch w).upperHalfPlaneMap t : ℂ)) x =
                deriv
                  (fun t : ℂ ↦
                    (realMobiusRepresentativeAction M
                      ((A.normalizedBranch z).upperHalfPlaneMap t) : ℂ)) x :=
  A.transition_realMobiusOneJets_of_pairProjectiveDerivativeUniqueness
    (pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem_of_projectiveFirstSecondDerivative_scalarClosed
      hProjFirst hProjSecond)
    hu

/--
The proved projective-derivative Schwarzian uniqueness route gives value-level
real-Mobius transitions between every pair of selected normalized branches in a
derivative-data atlas.
-/
theorem transition_realMobius_of_projectiveFirstSecondDerivative_scalarClosed
    (hProjFirst :
      LocalUpperHalfPlaneDevelopingMapProjectiveFirstDerivativeHasDerivAtTheorem)
    (hProjSecond :
      LocalUpperHalfPlaneDevelopingMapProjectiveSecondDerivativeHasDerivAtTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) :
    ∀ z w : u.coordinateDomain,
      (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch w) :=
  A.transition_realMobius_of_pairProjectiveDerivativeUniqueness
    (pointedRealMobiusTransitionOneJetLocalUniquenessWithCoefficientAgreementAndPairProjectiveDerivativeTheorem_of_projectiveFirstSecondDerivative_scalarClosed
      hProjFirst hProjSecond)
    hu

end LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas

/--
Atlas-level off-diagonal real-transition target for metric-recovering branches.

The diagonal case of a local normalization atlas is formal: it is the identity
real Mobius transformation on one branch.  Thus the genuine local uniqueness
input only needs to handle distinct chosen centers.
-/
def MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianNormalizationAtlas u),
      u.SolvesLiouvilleEquation →
        ∀ z w : u.coordinateDomain, z ≠ w →
          (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch w)

/--
Overlapping atlas-level off-diagonal real-transition target for
metric-recovering branches.

On empty overlaps the real-Mobius transition predicate is vacuous, so the
geometric local uniqueness input only needs to handle distinct selected
centers whose normalized branch domains actually meet.
-/
def MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem :
    Prop :=
  ∀ {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianNormalizationAtlas u),
      u.SolvesLiouvilleEquation →
        ∀ z w : u.coordinateDomain, z ≠ w →
          Set.Nonempty ((A.normalizedBranch z).domain ∩ (A.normalizedBranch w).domain) →
            (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch w)

/--
The older branch-level real-transition uniqueness theorem implies the sharper
atlas-level off-diagonal target.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_branches
    (h : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem := by
  intro u A hu z w _hzw
  exact A.normalizedBranch_transition_realMobius h hu z w

/--
The branch-level real-transition uniqueness theorem also implies the
overlapping-only off-diagonal target.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_branches
    (h : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem := by
  intro u A hu z w _hzw _hne
  exact A.normalizedBranch_transition_realMobius h hu z w

/--
The nonempty-overlap branch-level target gives the overlapping off-diagonal
atlas target directly.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_branchNonemptyOverlap
    (h :
      MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem := by
  intro u A hu z w _hzw hne
  exact h (A.normalizedBranch z) (A.normalizedBranch w) hu
    (A.overlap_preconnected z w) hne

/--
Overlapping off-diagonal real-transition uniqueness gives the older
off-diagonal target, since empty overlaps impose no transition condition.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_overlappingOffDiagonal
    (hOverlap :
      MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem := by
  intro u A hu z w hzw
  by_cases hne :
      Set.Nonempty ((A.normalizedBranch z).domain ∩ (A.normalizedBranch w).domain)
  · exact hOverlap A hu z w hzw hne
  · refine ⟨1, ?_⟩
    intro ξ hξz hξw
    exfalso
    exact hne ⟨ξ, ⟨hξz, hξw⟩⟩

/--
The nonempty-overlap branch-level target also gives the off-diagonal atlas
target, with empty overlaps handled formally.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_branchNonemptyOverlap
    (h :
      MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem :=
  metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_overlappingOffDiagonal
    (metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_branchNonemptyOverlap
      h)

/--
The pointed branch-level formulation gives the overlapping off-diagonal atlas
target.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_pointed
    (hPoint :
      MetricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem :=
  metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_branchNonemptyOverlap
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_pointed
      hPoint hExtend)

/--
The pointed branch-level formulation gives the off-diagonal atlas target.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_pointed
    (hPoint :
      MetricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem :=
  metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_branchNonemptyOverlap
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_pointed
      hPoint hExtend)

/--
Equal-hyperbolic-derivative-norm one-jet transitivity plus connected-overlap
extension gives the overlapping off-diagonal atlas target.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_hyperbolicDerivativeNorm
    (hNorm :
      PointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem :=
  metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_branchNonemptyOverlap
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_hyperbolicDerivativeNorm
      hNorm hExtend)

/--
Equal-hyperbolic-derivative-norm one-jet transitivity plus connected-overlap
extension gives the off-diagonal atlas target.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_hyperbolicDerivativeNorm
    (hNorm :
      PointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem :=
  metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_branchNonemptyOverlap
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_hyperbolicDerivativeNorm
      hNorm hExtend)

/--
Value transitivity, stabilizer tangent transitivity, and connected-overlap
extension give the overlapping off-diagonal atlas target.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_value_stabilizer
    (hValue : RealMobiusValueTransitivityOnUpperHalfPlaneTheorem)
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem :=
  metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_branchNonemptyOverlap
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_value_stabilizer
      hValue hStabilizer hExtend)

/--
Value transitivity, stabilizer tangent transitivity, and connected-overlap
extension give the off-diagonal atlas target.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_value_stabilizer
    (hValue : RealMobiusValueTransitivityOnUpperHalfPlaneTheorem)
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem :=
  metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_branchNonemptyOverlap
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_value_stabilizer
      hValue hStabilizer hExtend)

/--
With value transitivity proved explicitly, stabilizer tangent transitivity and
connected-overlap extension give the overlapping off-diagonal atlas target.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_stabilizer
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem :=
  metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_value_stabilizer
    realMobiusValueTransitivityOnUpperHalfPlaneTheorem hStabilizer hExtend

/--
With value transitivity proved explicitly, stabilizer tangent transitivity and
connected-overlap extension give the off-diagonal atlas target.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_stabilizer
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem :=
  metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_value_stabilizer
    realMobiusValueTransitivityOnUpperHalfPlaneTheorem hStabilizer hExtend

/--
Since rotation tangent transitivity at `i` is proved, stabilizer transport and
connected-overlap extension give the overlapping off-diagonal atlas target.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_rotationTransport
    (hTransport : RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem :=
  metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_branchNonemptyOverlap
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_rotationTransport
      hTransport hExtend)

/--
Since rotation tangent transitivity at `i` is proved, stabilizer transport and
connected-overlap extension give the off-diagonal atlas target.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_rotationTransport
    (hTransport : RealMobiusStabilizerAdjustsPointedDerivativeFromRotationsTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem :=
  metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_branchNonemptyOverlap
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_rotationTransport
      hTransport hExtend)

/--
Connected-overlap extension alone now gives the overlapping off-diagonal atlas
transition target.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_extension
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem :=
  metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_branchNonemptyOverlap
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_extension
      hExtend)

/--
Connected-overlap extension alone now gives the off-diagonal atlas transition
target.
-/
theorem metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_extension
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem :=
  metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_branchNonemptyOverlap
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_extension
      hExtend)

/--
Off-diagonal real-transition uniqueness gives all transitions in a local
normalization atlas, since a branch has identity transition to itself.
-/
theorem localMetricRecoveringSchwarzianNormalizationAtlas_transition_realMobius_of_offDiagonal
    (hOff :
      MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) :
    ∀ z w : u.coordinateDomain,
      (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch w) := by
  intro z w
  by_cases hzw : z = w
  · subst w
    exact LocalUpperHalfPlaneDevelopingMap.hasRealMobiusTransition_self
      (A.normalizedBranch z)
  · exact hOff A hu z w hzw

/--
Overlapping off-diagonal real-transition uniqueness gives all transitions in a
local normalization atlas.  The diagonal case is identity, and the
off-diagonal empty-overlap case is vacuous.
-/
theorem localMetricRecoveringSchwarzianNormalizationAtlas_transition_realMobius_of_overlappingOffDiagonal
    (hOverlap :
      MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) :
    ∀ z w : u.coordinateDomain,
      (A.normalizedBranch z).HasRealMobiusTransition (A.normalizedBranch w) :=
  localMetricRecoveringSchwarzianNormalizationAtlas_transition_realMobius_of_offDiagonal
    (metricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem_of_overlappingOffDiagonal
      hOverlap) A hu

/--
A local Schwarzian normalization atlas whose normalized branches have real
Mobius transitions on overlaps.

This is the coordinate-domain analogue of `HyperbolicLocalModelAtlas`, but it
remembers that the local maps came from Schwarzian ODE solutions and Mobius
postcomposition normalizations.
-/
structure LocalRealSchwarzianNormalizationAtlas (u : LocalConformalFactor)
    extends LocalMetricRecoveringSchwarzianNormalizationAtlas u where
  /-- The normalized branches differ by real Mobius transformations on overlaps. -/
  transition_realMobius :
    ∀ z w : u.coordinateDomain,
      (toLocalMetricRecoveringSchwarzianNormalizationAtlas.normalizedBranch z).HasRealMobiusTransition
        (toLocalMetricRecoveringSchwarzianNormalizationAtlas.normalizedBranch w)

namespace LocalRealSchwarzianNormalizationAtlas

/-- Forget the real-transition witnesses, retaining only the metric-recovering normalized atlas. -/
def toMetricRecoveringAtlas {u : LocalConformalFactor}
    (A : LocalRealSchwarzianNormalizationAtlas u) :
    LocalMetricRecoveringSchwarzianNormalizationAtlas u :=
  A.toLocalMetricRecoveringSchwarzianNormalizationAtlas

/--
Build a real-transition Schwarzian normalization atlas from a metric-recovering
normalization atlas and the local uniqueness theorem for `ℍ`-valued
metric-recovering branches.
-/
def ofMetricRecoveringAtlas
    (h : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) :
    LocalRealSchwarzianNormalizationAtlas u where
  toLocalMetricRecoveringSchwarzianNormalizationAtlas := A
  transition_realMobius := A.normalizedBranch_transition_realMobius h hu

/--
Build a real-transition Schwarzian normalization atlas from a
metric-recovering normalization atlas and the off-diagonal local uniqueness
target.
-/
def ofMetricRecoveringAtlasOffDiagonal
    (hOff :
      MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) :
    LocalRealSchwarzianNormalizationAtlas u where
  toLocalMetricRecoveringSchwarzianNormalizationAtlas := A
  transition_realMobius :=
    localMetricRecoveringSchwarzianNormalizationAtlas_transition_realMobius_of_offDiagonal
      hOff A hu

/--
Build a real-transition Schwarzian normalization atlas from a
metric-recovering normalization atlas and the overlapping off-diagonal local
uniqueness target.
-/
def ofMetricRecoveringAtlasOverlappingOffDiagonal
    (hOverlap :
      MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem)
    {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianNormalizationAtlas u)
    (hu : u.SolvesLiouvilleEquation) :
    LocalRealSchwarzianNormalizationAtlas u where
  toLocalMetricRecoveringSchwarzianNormalizationAtlas := A
  transition_realMobius :=
    localMetricRecoveringSchwarzianNormalizationAtlas_transition_realMobius_of_overlappingOffDiagonal
      hOverlap A hu

/-- Forget the Schwarzian-normalization provenance and keep an `ℍ`-branch atlas. -/
def toLocalRealUpperHalfPlaneBranchAtlas {u : LocalConformalFactor}
    (A : LocalRealSchwarzianNormalizationAtlas u) :
    LocalRealUpperHalfPlaneBranchAtlas u where
  schwarzianAt := A.schwarzianAt
  branchAt := fun z ↦ A.normalizedBranch z
  mem_branchAt_domain := A.mem_normalizedBranch_domain
  overlap_preconnected := A.overlap_preconnected
  transition_realMobius := A.transition_realMobius

/--
When the conformal coordinate domain is all of `ℂ`, a real Schwarzian
normalization atlas gives a coordinate-level Poincare pullback formula atlas.
-/
def toCoordinateUpperHalfPlanePullbackFormulaAtlas {u : LocalConformalFactor}
    (A : LocalRealSchwarzianNormalizationAtlas u) (g : HyperbolicMetric ℂ)
    (hDomain : u.coordinateDomain = Set.univ)
    (hMetric :
      ∀ z, z ∈ u.coordinateDomain →
        g.toConformalMetric.densitySqInChart (OpenPartialHomeomorph.refl ℂ) (by simp) z =
          u.densitySq z) :
    CoordinateUpperHalfPlanePullbackFormulaAtlas ℂ g :=
  A.toLocalRealUpperHalfPlaneBranchAtlas.toCoordinateUpperHalfPlanePullbackFormulaAtlas
    g hDomain hMetric

/--
When the conformal coordinate domain is all of `ℂ`, a real Schwarzian
normalization atlas gives a local Liouville developing-solution atlas.
-/
def toLocalLiouvilleDevelopingSolutionAtlas {u : LocalConformalFactor}
    (A : LocalRealSchwarzianNormalizationAtlas u) (g : HyperbolicMetric ℂ)
    (hu : u.SolvesLiouvilleEquation)
    (hDomain : u.coordinateDomain = Set.univ)
    (hMetric :
      ∀ z, z ∈ u.coordinateDomain →
        g.toConformalMetric.densitySqInChart (OpenPartialHomeomorph.refl ℂ) (by simp) z =
          u.densitySq z) :
    LocalLiouvilleDevelopingSolutionAtlas ℂ g :=
  A.toLocalRealUpperHalfPlaneBranchAtlas.toLocalLiouvilleDevelopingSolutionAtlas
    g hu hDomain hMetric

end LocalRealSchwarzianNormalizationAtlas

/--
The local normalized-Schwarzian-atlas target: a hyperbolic Liouville factor
admits a cover by metric-recovering Mobius normalizations of Schwarzian ODE
solutions.
-/
def HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem :
    Prop :=
  ∀ (u : LocalConformalFactor),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalMetricRecoveringSchwarzianPreAtlas u)

/--
The sharper local pre-atlas target: produce a particular pointwise
metric-recovering Schwarzian pre-atlas whose normalized domains are balls.
-/
def HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem :
    Prop :=
  ∀ (u : LocalConformalFactor),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalMetricRecoveringSchwarzianBallPreAtlas u)

/-- Ball pre-atlases forget to ordinary metric-recovering pre-atlases. -/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem_of_ballPreAtlas
    (hBallPre :
      HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem := by
  intro u hu
  rcases hBallPre u hu with ⟨A⟩
  exact ⟨A.toPreAtlas⟩

/--
The overlap-shrinking target for metric-recovering Schwarzian pre-atlases.

After pointwise normalized branches have been chosen, one still needs to shrink
or choose them so that pairwise overlaps are preconnected.  That connectedness
is the hypothesis needed for the real-Mobius transition uniqueness theorem.
-/
def MetricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem : Prop :=
  ∀ {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianPreAtlas u),
      ∀ z w : u.coordinateDomain, IsPreconnected
        ((A.normalizationAt z).normalized.domain ∩
          (A.normalizationAt w).normalized.domain)

/--
Ball-domain version of the overlap-shrinking target.

This is often the natural geometric output of local shrinking: every
metric-recovering normalized branch domain is a complex metric ball.
-/
def MetricRecoveringSchwarzianPreAtlasHasBallDomainsTheorem : Prop :=
  ∀ {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianPreAtlas u),
      ∀ z : u.coordinateDomain,
        ∃ c r, (A.normalizationAt z).normalized.domain = Metric.ball c r

/--
Ball-shaped normalized domains give preconnected overlaps.  The proof is
entirely mathlib: balls in a normed vector space are convex, intersections of
convex sets are convex, and convex sets are preconnected.
-/
theorem metricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem_of_ballDomains
    (hBall : MetricRecoveringSchwarzianPreAtlasHasBallDomainsTheorem) :
    MetricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem := by
  intro u A z w
  rcases hBall A z with ⟨cz, rz, hz⟩
  rcases hBall A w with ⟨cw, rw, hw⟩
  rw [hz, hw]
  exact ((convex_ball cz rz).inter (convex_ball cw rw)).isPreconnected

/--
The local normalized-Schwarzian-atlas target: a hyperbolic Liouville factor
admits a cover by metric-recovering Mobius normalizations of Schwarzian ODE
solutions, with preconnected overlaps.
-/
def HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :
    Prop :=
  ∀ (u : LocalConformalFactor),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalMetricRecoveringSchwarzianNormalizationAtlas u)

/--
Pre-atlases plus the overlap-shrinking target give the normalized-Schwarzian
atlas target.
-/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_preAtlas
    (hPre : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem)
    (hOverlap : MetricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem := by
  intro u hu
  rcases hPre u hu with ⟨A⟩
  exact ⟨LocalMetricRecoveringSchwarzianNormalizationAtlas.ofPreAtlas A (hOverlap A)⟩

/--
Ball pre-atlases upgrade directly to normalized Schwarzian atlases; the overlap
preconnectedness is derived from the retained ball witnesses.
-/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_ballPreAtlas
    (hBallPre :
      HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianBallPreAtlasTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem := by
  intro u hu
  rcases hBallPre u hu with ⟨A⟩
  exact ⟨LocalMetricRecoveringSchwarzianNormalizationAtlas.ofPreAtlas
    A.toPreAtlas A.overlap_preconnected⟩

/--
Pre-atlases plus ball-shaped normalized branch domains give the
normalized-Schwarzian atlas target.
-/
theorem hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_preAtlasBallDomains
    (hPre : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianPreAtlasTheorem)
    (hBall : MetricRecoveringSchwarzianPreAtlasHasBallDomainsTheorem) :
    HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem_of_preAtlas
    hPre
    (metricRecoveringSchwarzianPreAtlasHasPreconnectedOverlapsTheorem_of_ballDomains
      hBall)

/--
The real-overlap refinement of the local normalized-Schwarzian-atlas target.
-/
def HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem :
    Prop :=
  ∀ (u : LocalConformalFactor),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalRealSchwarzianNormalizationAtlas u)

/--
Metric-recovering Schwarzian normalization atlases plus the real-transition
uniqueness theorem give atlases whose overlaps are real Mobius.
-/
theorem hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem := by
  intro u hu
  rcases hAtlas u hu with ⟨A⟩
  exact ⟨LocalRealSchwarzianNormalizationAtlas.ofMetricRecoveringAtlas hTransition A hu⟩

/--
Metric-recovering Schwarzian normalization atlases plus off-diagonal
real-transition uniqueness give atlases whose overlaps are real Mobius.
-/
theorem hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_offDiagonal
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hOff :
      MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem := by
  intro u hu
  rcases hAtlas u hu with ⟨A⟩
  exact ⟨LocalRealSchwarzianNormalizationAtlas.ofMetricRecoveringAtlasOffDiagonal
    hOff A hu⟩

/--
Metric-recovering Schwarzian normalization atlases plus overlapping
off-diagonal real-transition uniqueness give atlases whose overlaps are real
Mobius.  The diagonal case and empty-overlap off-diagonal case are formal.
-/
theorem hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_overlappingOffDiagonal
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hOverlap :
      MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem := by
  intro u hu
  rcases hAtlas u hu with ⟨A⟩
  exact ⟨LocalRealSchwarzianNormalizationAtlas.ofMetricRecoveringAtlasOverlappingOffDiagonal
    hOverlap A hu⟩

/--
Metric-recovering Schwarzian normalization atlases plus the branch-level
nonempty-overlap transition theorem give atlases whose overlaps are real
Mobius.
-/
theorem hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_branchNonemptyOverlap
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hTransition :
      MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem) :
    HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_overlappingOffDiagonal
    hAtlas
    (metricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem_of_branchNonemptyOverlap
      hTransition)

/--
Metric-recovering Schwarzian normalization atlases plus pointed branch-level
real-transition uniqueness give atlases whose overlaps are real Mobius.
-/
theorem hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_pointed
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hPoint :
      MetricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_branchNonemptyOverlap
    hAtlas
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_pointed
      hPoint hExtend)

/--
Metric-recovering Schwarzian normalization atlases plus equal-hyperbolic-norm
one-jet transitivity and connected-overlap extension give real Mobius
transitions.
-/
theorem hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_hyperbolicDerivativeNorm
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hNorm :
      PointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_branchNonemptyOverlap
    hAtlas
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_hyperbolicDerivativeNorm
      hNorm hExtend)

/--
Metric-recovering Schwarzian normalization atlases plus value transitivity,
stabilizer tangent transitivity, and connected-overlap extension give real
Mobius transitions.
-/
theorem hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_value_stabilizer
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hValue : RealMobiusValueTransitivityOnUpperHalfPlaneTheorem)
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_branchNonemptyOverlap
    hAtlas
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_value_stabilizer
      hValue hStabilizer hExtend)

/--
With value transitivity proved explicitly, metric-recovering Schwarzian
normalization atlases plus stabilizer tangent transitivity and
connected-overlap extension give real Mobius transitions.
-/
theorem hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_stabilizer
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_value_stabilizer
    hAtlas realMobiusValueTransitivityOnUpperHalfPlaneTheorem hStabilizer hExtend

/--
Once metric-recovering Schwarzian normalization atlases are constructed,
connected-overlap extension is the only remaining input for real Mobius
transitions.
-/
theorem hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_extension
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_branchNonemptyOverlap
    hAtlas
    (metricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem_of_extension
      hExtend)

/--
The local branch-atlas consequence: hyperbolic Liouville data produces local
upper-half-plane branches with real Mobius overlaps once the Schwarzian
normalization atlas has been constructed.
-/
def HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem : Prop :=
  ∀ (u : LocalConformalFactor),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalRealUpperHalfPlaneBranchAtlas u)

/--
Real Schwarzian normalization atlases forget to real upper-half-plane branch
atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_realSchwarzian
    (h : HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem := by
  intro u hu
  rcases h u hu with ⟨A⟩
  exact ⟨A.toLocalRealUpperHalfPlaneBranchAtlas⟩

/--
Metric-recovering Schwarzian normalization atlases plus the real-transition
uniqueness theorem give real upper-half-plane branch atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_realSchwarzian
    (hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering
      hAtlas hTransition)

/--
Metric-recovering Schwarzian normalization atlases plus off-diagonal
real-transition uniqueness give real upper-half-plane branch atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering_offDiagonal
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hOff :
      MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_realSchwarzian
    (hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_offDiagonal
      hAtlas hOff)

/--
Metric-recovering Schwarzian normalization atlases plus overlapping
off-diagonal real-transition uniqueness give real upper-half-plane branch
atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering_overlappingOffDiagonal
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hOverlap :
      MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_realSchwarzian
    (hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_overlappingOffDiagonal
      hAtlas hOverlap)

/--
Metric-recovering Schwarzian normalization atlases plus the branch-level
nonempty-overlap transition theorem give real upper-half-plane branch atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering_branchNonemptyOverlap
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hTransition :
      MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsOnNonemptyOverlapTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_realSchwarzian
    (hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_branchNonemptyOverlap
      hAtlas hTransition)

/--
Metric-recovering Schwarzian normalization atlases plus pointed branch-level
real-transition uniqueness give real upper-half-plane branch atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering_pointed
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hPoint :
      MetricRecoveringUpperHalfPlaneBranchesAdmitPointedRealMobiusTransitionTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_realSchwarzian
    (hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_pointed
      hAtlas hPoint hExtend)

/--
Metric-recovering Schwarzian normalization atlases plus equal-hyperbolic-norm
one-jet transitivity and connected-overlap extension give real
upper-half-plane branch atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering_hyperbolicDerivativeNorm
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hNorm :
      PointedRealMobiusTransitionOfEqualHyperbolicDerivativeNormTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_realSchwarzian
    (hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_hyperbolicDerivativeNorm
      hAtlas hNorm hExtend)

/--
Metric-recovering Schwarzian normalization atlases plus value transitivity,
stabilizer tangent transitivity, and connected-overlap extension give real
upper-half-plane branch atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering_value_stabilizer
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hValue : RealMobiusValueTransitivityOnUpperHalfPlaneTheorem)
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_realSchwarzian
    (hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_value_stabilizer
      hAtlas hValue hStabilizer hExtend)

/--
With value transitivity proved explicitly, metric-recovering Schwarzian
normalization atlases plus stabilizer tangent transitivity and
connected-overlap extension give real upper-half-plane branch atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering_stabilizer
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hStabilizer : RealMobiusStabilizerAdjustsPointedDerivativeTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_realSchwarzian
    (hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_stabilizer
      hAtlas hStabilizer hExtend)

/--
Once metric-recovering Schwarzian normalization atlases are constructed,
connected-overlap extension is the only remaining input for real upper-half-
plane branch atlases.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering_extension
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hExtend : PointedRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
  hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_realSchwarzian
    (hyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem_of_metricRecovering_extension
      hAtlas hExtend)

/--
Coordinate pullback-formula consequence of the local Schwarzian branch theorem
on a global coordinate domain.

This is the handoff from the local Schwarzian construction back to the existing
local-model pipeline, in the special case where the single conformal coordinate
domain is all of `ℂ`.
-/
def HyperbolicLiouvilleProducesCoordinateUpperHalfPlanePullbackFormulaAtlasOnUnivTheorem :
    Prop :=
  ∀ (u : LocalConformalFactor) (g : HyperbolicMetric ℂ),
    u.SolvesLiouvilleEquation →
      u.coordinateDomain = Set.univ →
        (∀ z, z ∈ u.coordinateDomain →
          g.toConformalMetric.densitySqInChart (OpenPartialHomeomorph.refl ℂ) (by simp) z =
            u.densitySq z) →
          Nonempty (CoordinateUpperHalfPlanePullbackFormulaAtlas ℂ g)

/--
Local Liouville developing-solution consequence of the local Schwarzian branch
theorem on a global coordinate domain.

Compared with the coordinate pullback-formula consequence, this retains the
restricted conformal factors and their Liouville equations on each branch
domain.
-/
def HyperbolicLiouvilleProducesLocalLiouvilleDevelopingSolutionAtlasOnUnivTheorem :
    Prop :=
  ∀ (u : LocalConformalFactor) (g : HyperbolicMetric ℂ),
    u.SolvesLiouvilleEquation →
      u.coordinateDomain = Set.univ →
        (∀ z, z ∈ u.coordinateDomain →
          g.toConformalMetric.densitySqInChart (OpenPartialHomeomorph.refl ℂ) (by simp) z =
            u.densitySq z) →
          Nonempty (LocalLiouvilleDevelopingSolutionAtlas ℂ g)

/--
Local upper-half-plane model consequence of the local Schwarzian branch theorem
on a global coordinate domain.
-/
def HyperbolicLiouvilleProducesUpperHalfPlaneLocalModelsOnUnivTheorem :
    Prop :=
  ∀ (u : LocalConformalFactor) (g : HyperbolicMetric ℂ),
    u.SolvesLiouvilleEquation →
      u.coordinateDomain = Set.univ →
        (∀ z, z ∈ u.coordinateDomain →
          g.toConformalMetric.densitySqInChart (OpenPartialHomeomorph.refl ℂ) (by simp) z =
            u.densitySq z) →
          g.HasUpperHalfPlaneLocalModels

/--
Local real upper-half-plane branch atlases give coordinate Poincare pullback
formula atlases on a global coordinate domain.
-/
theorem hyperbolicLiouvilleProducesCoordinateUpperHalfPlanePullbackFormulaAtlasOnUnivTheorem_of_realBranches
    (h : HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem) :
    HyperbolicLiouvilleProducesCoordinateUpperHalfPlanePullbackFormulaAtlasOnUnivTheorem := by
  intro u g hu hDomain hMetric
  rcases h u hu with ⟨A⟩
  exact ⟨A.toCoordinateUpperHalfPlanePullbackFormulaAtlas g hDomain hMetric⟩

/--
Local real upper-half-plane branch atlases give local Liouville developing
solution atlases on a global coordinate domain.
-/
theorem hyperbolicLiouvilleProducesLocalLiouvilleDevelopingSolutionAtlasOnUnivTheorem_of_realBranches
    (h : HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem) :
    HyperbolicLiouvilleProducesLocalLiouvilleDevelopingSolutionAtlasOnUnivTheorem := by
  intro u g hu hDomain hMetric
  rcases h u hu with ⟨A⟩
  exact ⟨A.toLocalLiouvilleDevelopingSolutionAtlas g hu hDomain hMetric⟩

/--
Local real upper-half-plane branch atlases give local upper-half-plane models
on a global coordinate domain.
-/
theorem hyperbolicLiouvilleProducesUpperHalfPlaneLocalModelsOnUnivTheorem_of_realBranches
    (h : HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem) :
    HyperbolicLiouvilleProducesUpperHalfPlaneLocalModelsOnUnivTheorem := by
  intro u g hu hDomain hMetric
  exact HyperbolicMetric.hasUpperHalfPlaneLocalModels_of_hasLocalLiouvilleDevelopingSolutionAtlas
    ((hyperbolicLiouvilleProducesLocalLiouvilleDevelopingSolutionAtlasOnUnivTheorem_of_realBranches h)
      u g hu hDomain hMetric)

/--
The local Liouville developing-solution consequence implies the coordinate
pullback-formula consequence.
-/
theorem hyperbolicLiouvilleProducesCoordinateUpperHalfPlanePullbackFormulaAtlasOnUnivTheorem_of_localLiouville
    (h : HyperbolicLiouvilleProducesLocalLiouvilleDevelopingSolutionAtlasOnUnivTheorem) :
    HyperbolicLiouvilleProducesCoordinateUpperHalfPlanePullbackFormulaAtlasOnUnivTheorem := by
  intro u g hu hDomain hMetric
  exact HyperbolicMetric.hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasLocalLiouvilleDevelopingSolutionAtlas
    (h u g hu hDomain hMetric)

/--
The local Liouville developing-solution consequence implies local
upper-half-plane model existence.
-/
theorem hyperbolicLiouvilleProducesUpperHalfPlaneLocalModelsOnUnivTheorem_of_localLiouville
    (h : HyperbolicLiouvilleProducesLocalLiouvilleDevelopingSolutionAtlasOnUnivTheorem) :
    HyperbolicLiouvilleProducesUpperHalfPlaneLocalModelsOnUnivTheorem := by
  intro u g hu hDomain hMetric
  exact HyperbolicMetric.hasUpperHalfPlaneLocalModels_of_hasLocalLiouvilleDevelopingSolutionAtlas
    (h u g hu hDomain hMetric)

/--
Metric-recovering Schwarzian normalization atlases plus real-transition
uniqueness give the coordinate pullback-formula atlas on a global coordinate
domain.
-/
theorem hyperbolicLiouvilleProducesCoordinateUpperHalfPlanePullbackFormulaAtlasOnUnivTheorem_of_metricRecovering
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesCoordinateUpperHalfPlanePullbackFormulaAtlasOnUnivTheorem :=
  hyperbolicLiouvilleProducesCoordinateUpperHalfPlanePullbackFormulaAtlasOnUnivTheorem_of_realBranches
    (hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering
      hAtlas hTransition)

/--
Metric-recovering Schwarzian normalization atlases plus real-transition
uniqueness give the local Liouville developing-solution atlas on a global
coordinate domain.
-/
theorem hyperbolicLiouvilleProducesLocalLiouvilleDevelopingSolutionAtlasOnUnivTheorem_of_metricRecovering
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalLiouvilleDevelopingSolutionAtlasOnUnivTheorem :=
  hyperbolicLiouvilleProducesLocalLiouvilleDevelopingSolutionAtlasOnUnivTheorem_of_realBranches
    (hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering
      hAtlas hTransition)

/--
Metric-recovering Schwarzian normalization atlases plus real-transition
uniqueness give local upper-half-plane models on a global coordinate domain.
-/
theorem hyperbolicLiouvilleProducesUpperHalfPlaneLocalModelsOnUnivTheorem_of_metricRecovering
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hTransition : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem) :
    HyperbolicLiouvilleProducesUpperHalfPlaneLocalModelsOnUnivTheorem :=
  hyperbolicLiouvilleProducesUpperHalfPlaneLocalModelsOnUnivTheorem_of_localLiouville
    (hyperbolicLiouvilleProducesLocalLiouvilleDevelopingSolutionAtlasOnUnivTheorem_of_metricRecovering
      hAtlas hTransition)

/--
Metric-recovering Schwarzian normalization atlases plus overlapping
off-diagonal real-transition uniqueness give the coordinate pullback-formula
atlas on a global coordinate domain.
-/
theorem hyperbolicLiouvilleProducesCoordinateUpperHalfPlanePullbackFormulaAtlasOnUnivTheorem_of_metricRecovering_overlappingOffDiagonal
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hOverlap :
      MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem) :
    HyperbolicLiouvilleProducesCoordinateUpperHalfPlanePullbackFormulaAtlasOnUnivTheorem :=
  hyperbolicLiouvilleProducesCoordinateUpperHalfPlanePullbackFormulaAtlasOnUnivTheorem_of_realBranches
    (hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering_overlappingOffDiagonal
      hAtlas hOverlap)

/--
Metric-recovering Schwarzian normalization atlases plus overlapping
off-diagonal real-transition uniqueness give the local Liouville
developing-solution atlas on a global coordinate domain.
-/
theorem hyperbolicLiouvilleProducesLocalLiouvilleDevelopingSolutionAtlasOnUnivTheorem_of_metricRecovering_overlappingOffDiagonal
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hOverlap :
      MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem) :
    HyperbolicLiouvilleProducesLocalLiouvilleDevelopingSolutionAtlasOnUnivTheorem :=
  hyperbolicLiouvilleProducesLocalLiouvilleDevelopingSolutionAtlasOnUnivTheorem_of_realBranches
    (hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_metricRecovering_overlappingOffDiagonal
      hAtlas hOverlap)

/--
Metric-recovering Schwarzian normalization atlases plus overlapping
off-diagonal real-transition uniqueness give local upper-half-plane models on
a global coordinate domain.
-/
theorem hyperbolicLiouvilleProducesUpperHalfPlaneLocalModelsOnUnivTheorem_of_metricRecovering_overlappingOffDiagonal
    (hAtlas : HyperbolicLiouvilleProducesLocalMetricRecoveringSchwarzianNormalizationAtlasTheorem)
    (hOverlap :
      MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem) :
    HyperbolicLiouvilleProducesUpperHalfPlaneLocalModelsOnUnivTheorem :=
  hyperbolicLiouvilleProducesUpperHalfPlaneLocalModelsOnUnivTheorem_of_localLiouville
    (hyperbolicLiouvilleProducesLocalLiouvilleDevelopingSolutionAtlasOnUnivTheorem_of_metricRecovering_overlappingOffDiagonal
      hAtlas hOverlap)

namespace LocalSchwarzianODEChart

/-- Projectivize the affine Schwarzian ODE chart to a local projective developing map. -/
def toLocalProjectiveDevelopingMap
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (C : LocalSchwarzianODEChart S) :
    LocalProjectiveDevelopingMap S where
  domain := C.domain
  isOpen_domain := C.isOpen_domain
  domain_subset := C.domain_subset
  affineMap := C.localMap
  projectiveMap := fun z ↦ (C.localMap z : RiemannSphere)
  projectiveMap_eq_affine := by
    intro z hz
    rfl
  projectiveMap_ne_infty := by
    intro z hz
    exact OnePoint.coe_ne_infty _
  affineMapDeriv := C.frame.localMapDeriv
  affineMapSecondDeriv := C.frame.localMapSecondDeriv
  affineMapThirdDeriv := C.frame.localMapThirdDeriv
  affineMapDeriv_ne_zero := C.localMapDeriv_ne_zero
  schwarzian_eq_coefficient := C.schwarzian_eq_coefficient

end LocalSchwarzianODEChart

namespace CenteredNormalizedSchwarzianFrobeniusPair

/--
A shrunk centered Frobenius pair gives the local Schwarzian ODE chart directly.

This is the concrete local developing-coordinate constructor before
projectivizing to the Riemann sphere.
-/
def toLocalSchwarzianODEChart
    {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a) :
    LocalSchwarzianODEChart S where
  domain := centeredBallDomain z₀ P.radius
  isOpen_domain := isOpen_centeredBallDomain z₀ P.radius
  domain_subset := P.domain_subset
  frame := P.toNormalizedSchwarzianLinearODESolutionPair.toSchwarzianLinearODEFrame

/-- Projectivize the local developing coordinate obtained from a Frobenius pair. -/
def toLocalProjectiveDevelopingMap
    {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a) :
    LocalProjectiveDevelopingMap S :=
  P.toLocalSchwarzianODEChart.toLocalProjectiveDevelopingMap

/--
The projective developing map produced from a centered Frobenius pair has a
continuous affine coordinate on its domain.
-/
theorem toLocalProjectiveDevelopingMap_affineMap_continuousAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    {z : ℂ} (hz : z ∈ P.toLocalProjectiveDevelopingMap.domain) :
    ContinuousAt P.toLocalProjectiveDevelopingMap.affineMap z := by
  simpa [toLocalProjectiveDevelopingMap, toLocalSchwarzianODEChart,
    LocalSchwarzianODEChart.toLocalProjectiveDevelopingMap,
    LocalSchwarzianODEChart.localMap,
    NormalizedSchwarzianLinearODESolutionPair.toSchwarzianLinearODEFrame,
    SchwarzianLinearODESolutionPair.toSchwarzianLinearODEFrame,
    SchwarzianLinearODESolutionPair.localMap] using
      P.localMap_continuousAt hz

/--
The projective developing map produced from a centered Frobenius pair has a
`C^3` affine coordinate on its domain.
-/
theorem toLocalProjectiveDevelopingMap_affineMap_contDiffOn
    {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a) :
    ContDiffOn ℝ 3 P.toLocalProjectiveDevelopingMap.affineMap
      P.toLocalProjectiveDevelopingMap.domain := by
  simpa [toLocalProjectiveDevelopingMap, toLocalSchwarzianODEChart,
    LocalSchwarzianODEChart.toLocalProjectiveDevelopingMap,
    LocalSchwarzianODEChart.localMap,
    NormalizedSchwarzianLinearODESolutionPair.toSchwarzianLinearODEFrame,
    SchwarzianLinearODESolutionPair.toSchwarzianLinearODEFrame,
    SchwarzianLinearODESolutionPair.localMap] using
      P.localMap_contDiffOn

/--
The symbolic first derivative branch of the projective developing map produced
from a centered Frobenius pair is `C^3` on its domain.
-/
theorem toLocalProjectiveDevelopingMap_affineMapDeriv_contDiffOn
    {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a) :
    ContDiffOn ℝ 3
      (fun z : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv z)
      P.toLocalProjectiveDevelopingMap.domain := by
  simpa [toLocalProjectiveDevelopingMap, toLocalSchwarzianODEChart,
    LocalSchwarzianODEChart.toLocalProjectiveDevelopingMap,
    LocalSchwarzianODEChart.localMap,
    NormalizedSchwarzianLinearODESolutionPair.toSchwarzianLinearODEFrame,
    SchwarzianLinearODESolutionPair.toSchwarzianLinearODEFrame,
    SchwarzianLinearODESolutionPair.localMapDeriv,
    SchwarzianLinearODESolutionPair.wronskian] using
      P.localMapDeriv_contDiffOn

/--
The projective developing map produced from a centered Frobenius pair has the
expected actual affine derivative, provided each individual centered solution
has its stored actual derivative.
-/
theorem toLocalProjectiveDevelopingMap_affineMap_hasDerivAt_of_solutionHasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    (hSolDeriv : CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem)
    {z : ℂ} (hz : z ∈ P.toLocalProjectiveDevelopingMap.domain) :
    HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
      (P.toLocalProjectiveDevelopingMap.affineMapDeriv z) z := by
  simpa [toLocalProjectiveDevelopingMap, toLocalSchwarzianODEChart,
    LocalSchwarzianODEChart.toLocalProjectiveDevelopingMap,
    LocalSchwarzianODEChart.localMap,
    NormalizedSchwarzianLinearODESolutionPair.toSchwarzianLinearODEFrame,
    SchwarzianLinearODESolutionPair.toSchwarzianLinearODEFrame,
    SchwarzianLinearODESolutionPair.localMap,
    SchwarzianLinearODESolutionPair.localMapDeriv,
    SchwarzianLinearODESolutionPair.wronskian] using
      P.localMap_hasDerivAt_of_solutionHasDerivAt hSolDeriv hz

/--
The projective developing map produced from a centered Frobenius pair has the
expected derivative of its first derivative branch, provided each centered
solution has its stored first and second actual derivatives.
-/
theorem toLocalProjectiveDevelopingMap_affineMapDeriv_hasDerivAt_of_solutionHasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    (hSolDeriv : CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem)
    (hSolSecondDeriv : CenteredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem)
    {z : ℂ} (hz : z ∈ P.toLocalProjectiveDevelopingMap.domain) :
    HasDerivAt (fun w : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv w)
      (P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv z) z := by
  simpa [toLocalProjectiveDevelopingMap, toLocalSchwarzianODEChart,
    LocalSchwarzianODEChart.toLocalProjectiveDevelopingMap,
    LocalSchwarzianODEChart.localMap,
    NormalizedSchwarzianLinearODESolutionPair.toSchwarzianLinearODEFrame,
    SchwarzianLinearODESolutionPair.toSchwarzianLinearODEFrame,
    SchwarzianLinearODESolutionPair.localMapDeriv,
    SchwarzianLinearODESolutionPair.localMapSecondDeriv,
    SchwarzianLinearODESolutionPair.wronskian] using
      P.localMapDeriv_hasDerivAt_of_solutionHasDerivAt
        hSolDeriv hSolSecondDeriv hz

/--
The projective developing map produced from a centered Frobenius pair has the
expected derivative of its second derivative branch, provided each centered
solution has its stored first and second actual derivatives.
-/
theorem toLocalProjectiveDevelopingMap_affineMapSecondDeriv_hasDerivAt_of_solutionHasDerivAt
    {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    (hSolDeriv : CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem)
    (hSolSecondDeriv : CenteredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem)
    {z : ℂ} (hz : z ∈ P.toLocalProjectiveDevelopingMap.domain) :
    HasDerivAt (fun w : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w)
      (P.toLocalProjectiveDevelopingMap.affineMapThirdDeriv z) z := by
  simpa [toLocalProjectiveDevelopingMap, toLocalSchwarzianODEChart,
    LocalSchwarzianODEChart.toLocalProjectiveDevelopingMap,
    LocalSchwarzianODEChart.localMap,
    NormalizedSchwarzianLinearODESolutionPair.toSchwarzianLinearODEFrame,
    SchwarzianLinearODESolutionPair.toSchwarzianLinearODEFrame,
    SchwarzianLinearODESolutionPair.localMapSecondDeriv,
    SchwarzianLinearODESolutionPair.localMapThirdDeriv,
    SchwarzianLinearODESolutionPair.wronskian] using
      P.localMapSecondDeriv_hasDerivAt_of_solutionHasDerivAt
        hSolDeriv hSolSecondDeriv hz

end CenteredNormalizedSchwarzianFrobeniusPair

/--
The analytic local existence theorem still to be instantiated: every
holomorphic Schwarzian coefficient is locally solved by a ratio of two
independent solutions of `y'' + (1 / 2) q y = 0`.
-/
def HolomorphicSchwarzianLocallySolvableTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u) ⦃z : ℂ⦄,
    z ∈ u.coordinateDomain →
      ∃ C : LocalSchwarzianODEChart S, z ∈ C.domain

/--
Local projective developing-map existence: every holomorphic Schwarzian
coefficient has a local projective coordinate solving that Schwarzian equation.
-/
def HolomorphicSchwarzianLocalProjectiveDevelopingMapTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u) ⦃z : ℂ⦄,
    z ∈ u.coordinateDomain →
      ∃ D : LocalProjectiveDevelopingMap S, z ∈ D.domain

/--
Hyperbolic branch-selection theorem for a projective Schwarzian coordinate.

This is deliberately not asserted for arbitrary projective Schwarzians.  In the
hyperbolic case the Schwarzian coordinate must be normalized or post-composed
by a Mobius transformation so that the finite affine chart lands in `ℍ`, and
then the Poincare pullback squared-density formula must be verified.
-/
def HyperbolicProjectiveDevelopingMapLiftsToUpperHalfPlaneTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    (D : LocalProjectiveDevelopingMap S) ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ D.domain →
      ∃ H : LocalUpperHalfPlaneDevelopingMap S, H.projective = D ∧ z ∈ H.domain

/--
Existence of the hyperbolic base two-jet, using the canonical Frechet-Wirtinger
field `u.wirtingerZ`.
-/
def HyperbolicSchwarzianBaseJetExistenceTheorem : Prop :=
  ∀ {u : LocalConformalFactor} ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ u.coordinateDomain →
      Nonempty (HyperbolicSchwarzianBaseJet u z)

/-- The base jet is obtained from the canonical Frechet-Wirtinger derivative. -/
theorem hyperbolicSchwarzianBaseJetExistenceTheorem :
    HyperbolicSchwarzianBaseJetExistenceTheorem := by
  intro u z _hu _hz
  exact ⟨{
    uZ := u.wirtingerZ z
    agrees_with_logDensity_derivative := rfl
  }⟩

/--
Projective finite two-jet transitivity for Mobius postcomposition.

At a point where the original projective coordinate is locally univalent, a
Mobius transformation can be chosen so that the postcomposed finite affine
coordinate realizes any prescribed nondegenerate finite two-jet.  In normal
form, if the source jet is `(a,b,c)` and the target jet is `(p,q,r)`, the
postcomposing map is
`w ↦ p + B (w - a) / (1 + κ (w - a))`, with
`B = q / b` and
`κ = -((r - B*c) / b^2) / (2*B)`.
-/
def LocalProjectiveMobiusTwoJetTransitivityTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) ⦃z : ℂ⦄,
    z ∈ D.domain → ∀ target : NondegenerateFiniteTwoJet,
      ∃ N : LocalProjectiveMobiusTwoJetNormalization D z target,
        z ∈ N.domain

/--
Sharp remaining projective postcomposition construction boundary.

The finite two-jet algebra is no longer part of the hypothesis: the
postcomposition is required to be the explicit normal-form representative
constructed from the source and target two-jets.  What remains below this
boundary is the geometric construction of the shrunk projective developing map
obtained by postcomposition and the Schwarzian/chain-rule invariance facts.
-/
def LocalProjectiveNormalFormPostcompositionTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) ⦃z : ℂ⦄
    (hz : z ∈ D.domain) (target : NondegenerateFiniteTwoJet),
      ∃ N : LocalProjectiveMobiusTwoJetNormalization D z target,
        z ∈ N.domain ∧
          N.postcomposition =
            (D.finiteTwoJet hz).postcompositionNormalFormRepresentative target

/--
Still sharper normal-form postcomposition construction target.

Compared with `LocalProjectiveNormalFormPostcompositionTheorem`, this asks only
for the actual postcomposed projective map and the chain-rule values at the
base point.  The target two-jet equations are then proved by
`LocalProjectiveNormalFormPostcompositionData.toMobiusTwoJetNormalization`.
-/
def LocalProjectiveNormalFormPostcompositionDataTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) ⦃z : ℂ⦄
    (hz : z ∈ D.domain) (target : NondegenerateFiniteTwoJet),
      Nonempty (LocalProjectiveNormalFormPostcompositionData D z hz target)

/--
Most explicit normal-form postcomposition construction target.

The postcomposed affine coordinate and its first two symbolic derivative fields
are fixed by formula.  The remaining inputs are a pole-avoiding open shrink,
the base-point containment, and the Schwarzian-invariance calculation for the
explicit derivative fields.
-/
def LocalProjectiveNormalFormPostcompositionExplicitDataTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) ⦃z : ℂ⦄
    (hz : z ∈ D.domain) (target : NondegenerateFiniteTwoJet),
      Nonempty (LocalProjectiveNormalFormPostcompositionExplicitData D z hz target)

/--
Continuity boundary for local projective developing affine coordinates.

This is separated from the Mobius algebra: once the affine chart is continuous
at a base point, Lean proves the pole-avoiding shrink for the normal-form
postcomposition.
-/
def LocalProjectiveDevelopingMapAffineContinuousAtTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) ⦃z : ℂ⦄,
    z ∈ D.domain → ContinuousAt D.affineMap z

/--
Continuity for the local projective developing maps that actually come from
the centered Frobenius construction.

This is a proved replacement for the intentionally broad
`LocalProjectiveDevelopingMapAffineContinuousAtTheorem` when the projective map
is constructed as a ratio of the two Frobenius solutions.
-/
def LocalProjectiveFrobeniusDevelopingMapAffineContinuousAtTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄,
      z ∈ P.toLocalProjectiveDevelopingMap.domain →
        ContinuousAt P.toLocalProjectiveDevelopingMap.affineMap z

/--
Actual differentiability boundary for local projective developing maps that
come from the centered Frobenius construction.

This is the natural remaining analytic target below the upper-half-plane
normalization: prove the quotient rule for the ratio of the two convergent
Frobenius solutions, with the symbolic first derivative already stored in the
projective map.
-/
def LocalProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄,
      z ∈ P.toLocalProjectiveDevelopingMap.domain →
        HasDerivAt P.toLocalProjectiveDevelopingMap.affineMap
          (P.toLocalProjectiveDevelopingMap.affineMapDeriv z) z

/--
Actual differentiability boundary for the first affine derivative of local
projective developing maps that come from the centered Frobenius construction.
-/
def LocalProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄,
      z ∈ P.toLocalProjectiveDevelopingMap.domain →
        HasDerivAt (fun w : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapDeriv w)
          (P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv z) z

/--
Actual differentiability boundary for the second affine derivative of local
projective developing maps that come from the centered Frobenius construction.
-/
def LocalProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄,
      z ∈ P.toLocalProjectiveDevelopingMap.domain →
        HasDerivAt (fun w : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w)
          (P.toLocalProjectiveDevelopingMap.affineMapThirdDeriv z) z

/--
The centered Frobenius construction gives projective developing maps with
continuous affine coordinates.
-/
theorem localProjectiveFrobeniusDevelopingMapAffineContinuousAtTheorem :
    LocalProjectiveFrobeniusDevelopingMapAffineContinuousAtTheorem := by
  intro u S z₀ a P z hz
  exact P.toLocalProjectiveDevelopingMap_affineMap_continuousAt hz

/--
The individual Frobenius-solution derivative theorem proves the quotient-rule
boundary for Frobenius projective developing maps.
-/
theorem localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem_of_solutionHasDerivAt
    (hSolDeriv : CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem) :
    LocalProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem := by
  intro u S z₀ a P z hz
  exact P.toLocalProjectiveDevelopingMap_affineMap_hasDerivAt_of_solutionHasDerivAt
    hSolDeriv hz

/--
For Frobenius projective developing maps, the affine coordinate has the stored
first derivative.
-/
theorem localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem :
    LocalProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem :=
  localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem_of_solutionHasDerivAt
    centeredSchwarzianFrobeniusSolutionHasDerivAtTheorem

/--
The individual Frobenius-solution first- and second-derivative theorems prove
the quotient-rule boundary for the first affine derivative of Frobenius
projective developing maps.
-/
theorem localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem_of_solutionHasDerivAt
    (hSolDeriv : CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem)
    (hSolSecondDeriv : CenteredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem) :
    LocalProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem := by
  intro u S z₀ a P z hz
  exact
    P.toLocalProjectiveDevelopingMap_affineMapDeriv_hasDerivAt_of_solutionHasDerivAt
      hSolDeriv hSolSecondDeriv hz

/--
The scalar power-series derivative bridge proves the first-derivative
differentiability boundary for Frobenius projective developing maps.
-/
theorem localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    (hScalarDeriv : ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem) :
    LocalProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem :=
  localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem_of_solutionHasDerivAt
    (centeredSchwarzianFrobeniusSolutionHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
      hScalarDeriv)
    (centeredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
      hScalarDeriv)

/--
For Frobenius projective developing maps, the affine first-derivative field has
the stored second derivative.
-/
theorem localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem :
    LocalProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem :=
  localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    scalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem

/--
The individual Frobenius-solution first- and second-derivative theorems also
prove the quotient-rule boundary for the second affine derivative of Frobenius
projective developing maps.
-/
theorem localProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem_of_solutionHasDerivAt
    (hSolDeriv : CenteredSchwarzianFrobeniusSolutionHasDerivAtTheorem)
    (hSolSecondDeriv : CenteredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem) :
    LocalProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem := by
  intro u S z₀ a P z hz
  exact
    P.toLocalProjectiveDevelopingMap_affineMapSecondDeriv_hasDerivAt_of_solutionHasDerivAt
      hSolDeriv hSolSecondDeriv hz

/--
The scalar power-series derivative bridge proves the second-derivative
differentiability boundary for Frobenius projective developing maps.
-/
theorem localProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    (hScalarDeriv : ScalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem) :
    LocalProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem :=
  localProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem_of_solutionHasDerivAt
    (centeredSchwarzianFrobeniusSolutionHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
      hScalarDeriv)
    (centeredSchwarzianFrobeniusSolutionDerivHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
      hScalarDeriv)

/--
For Frobenius projective developing maps, the affine second-derivative field
has the stored third derivative.
-/
theorem localProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem :
    LocalProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem :=
  localProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    scalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem

/--
Schwarzian invariance boundary for explicit normal-form postcomposition.

The domain shrink and denominator nonvanishing are already packaged in
`LocalProjectiveNormalFormPoleAvoidingShrink`; this target asks only for the
third symbolic derivative and the Schwarzian equality for the explicit
postcomposed first and second derivative fields.
-/
def LocalProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    (D : LocalProjectiveDevelopingMap S) ⦃z : ℂ⦄
    (hz : z ∈ D.domain) (target : NondegenerateFiniteTwoJet)
    (P : LocalProjectiveNormalFormPoleAvoidingShrink D z hz target),
      ∃ affineMapThirdDeriv : ℂ → ℂ,
        ∀ w, w ∈ P.domain →
          schwarzianExpression
              (D.normalFormPostcompositionAffineMapDeriv hz target)
              (D.normalFormPostcompositionAffineMapSecondDeriv hz target)
              affineMapThirdDeriv w =
            S.coefficient w

/--
Explicit normal-form Mobius postcomposition preserves the symbolic Schwarzian
coefficient.
-/
theorem localProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem :
    LocalProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem := by
  intro u S D z hz target P
  refine ⟨D.normalFormPostcompositionAffineMapThirdDeriv hz target, ?_⟩
  intro w hw
  calc
    schwarzianExpression
        (D.normalFormPostcompositionAffineMapDeriv hz target)
        (D.normalFormPostcompositionAffineMapSecondDeriv hz target)
        (D.normalFormPostcompositionAffineMapThirdDeriv hz target) w
        =
          schwarzianExpression D.affineMapDeriv D.affineMapSecondDeriv
            D.affineMapThirdDeriv w :=
          D.schwarzianExpression_normalFormPostcomposition_eq hz
            (P.domain_subset_original hw) target (P.denominator_ne_zero w hw)
    _ = S.coefficient w :=
          D.schwarzian_eq_coefficient w (P.domain_subset_original hw)

/--
Frobenius-specific explicit normal-form postcomposition target.

Here the continuity input needed to avoid the Mobius pole is no longer a
separate hypothesis: it is proved for the projective map coming from the
Frobenius solution pair.  The explicit Schwarzian-invariance calculation for
normal-form postcomposition is now proved internally.
-/
def LocalProjectiveFrobeniusNormalFormPostcompositionExplicitDataTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄
    (hz : z ∈ P.toLocalProjectiveDevelopingMap.domain)
    (target : NondegenerateFiniteTwoJet),
      Nonempty
        (LocalProjectiveNormalFormPostcompositionExplicitData
          P.toLocalProjectiveDevelopingMap z hz target)

/--
Frobenius-specific canonical explicit normal-form postcomposition target.

This strengthens `LocalProjectiveFrobeniusNormalFormPostcompositionExplicitDataTheorem`:
the stored third derivative is required to be the explicit normal-form
chain-rule third derivative, not merely some field making the Schwarzian
equation true.
-/
def LocalProjectiveFrobeniusNormalFormCanonicalPostcompositionExplicitDataTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄
    (hz : z ∈ P.toLocalProjectiveDevelopingMap.domain)
    (target : NondegenerateFiniteTwoJet),
      ∃ E :
        LocalProjectiveNormalFormPostcompositionExplicitData
          P.toLocalProjectiveDevelopingMap z hz target,
        ∀ w : ℂ,
          E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv w =
            (P.toLocalProjectiveDevelopingMap.normalFormPostcompositionAffineMapThirdDeriv
              hz target) w

/--
Frobenius-specific upper-half-plane landing for the explicit normal-form
hyperbolic target.

The output is still a finite projective branch plus a landing ball, not yet a
full `LocalUpperHalfPlaneProjectiveNormalization`: the latter additionally
requires actual derivative-equality fields.  This isolates the purely
topological landing part.
-/
def LocalProjectiveFrobeniusNormalFormUpperHalfPlaneLandingTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄
    (hz : z ∈ P.toLocalProjectiveDevelopingMap.domain)
    (J : HyperbolicSchwarzianBaseJet u z),
      ∃ E :
        LocalProjectiveNormalFormPostcompositionExplicitData
          P.toLocalProjectiveDevelopingMap z hz J.toNondegenerateFiniteTwoJet,
        ∃ r : ℝ, 0 < r ∧
          ∀ w, w ∈ Metric.ball z r →
            0 < (E.toLocalProjectiveDevelopingMap.affineMap w).im

/--
Frobenius-specific canonical landing theorem.

It returns a landing ball inside the canonical explicit-data domain and
remembers that the stored third derivative is the normal-form chain-rule field
on that ball.
-/
def LocalProjectiveFrobeniusNormalFormCanonicalLandingTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄
    (hz : z ∈ P.toLocalProjectiveDevelopingMap.domain)
    (J : HyperbolicSchwarzianBaseJet u z),
      ∃ E :
        LocalProjectiveNormalFormPostcompositionExplicitData
          P.toLocalProjectiveDevelopingMap z hz J.toNondegenerateFiniteTwoJet,
        ∃ r : ℝ, 0 < r ∧
          Metric.ball z r ⊆ E.domain ∧
          (∀ w, w ∈ Metric.ball z r →
            0 < (E.toLocalProjectiveDevelopingMap.affineMap w).im) ∧
          (∀ w, w ∈ Metric.ball z r →
            E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv w =
              (P.toLocalProjectiveDevelopingMap.normalFormPostcompositionAffineMapThirdDeriv
                hz J.toNondegenerateFiniteTwoJet) w)

/--
Frobenius-specific remaining lift boundary after the topological landing ball
has been proved.

This is now the sharp local red piece for upper-half-plane normalization:
given explicit normal-form data and a ball inside its domain on which the
affine coordinate lands in `ℍ`, produce the actual `ℍ`-valued lift and the two
derivative-identification fields required by
`LocalUpperHalfPlaneProjectiveNormalization`.
-/
def LocalProjectiveFrobeniusNormalFormUpperHalfPlaneLiftTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄
    (hz : z ∈ P.toLocalProjectiveDevelopingMap.domain)
    (J : HyperbolicSchwarzianBaseJet u z)
    (E :
      LocalProjectiveNormalFormPostcompositionExplicitData
        P.toLocalProjectiveDevelopingMap z hz J.toNondegenerateFiniteTwoJet)
    (r : ℝ),
      0 < r →
        Metric.ball z r ⊆ E.domain →
          (∀ w, w ∈ Metric.ball z r →
            0 < (E.toLocalProjectiveDevelopingMap.affineMap w).im) →
            Nonempty (LocalProjectiveNormalFormUpperHalfPlaneLiftData E r)

/--
Frobenius-specific derivative-identification boundary after the actual
`ℍ`-valued lift has been constructed from the landing proof.

This is sharper than `LocalProjectiveFrobeniusNormalFormUpperHalfPlaneLiftTheorem`:
the topological lift to `ℍ` is no longer an assumption.  The only requested
field is that the symbolic derivative of the explicit normal-form branch agrees
with its actual complex derivative on the landing ball.
-/
def LocalProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄
    (hz : z ∈ P.toLocalProjectiveDevelopingMap.domain)
    (J : HyperbolicSchwarzianBaseJet u z)
    (E :
      LocalProjectiveNormalFormPostcompositionExplicitData
        P.toLocalProjectiveDevelopingMap z hz J.toNondegenerateFiniteTwoJet)
    (r : ℝ),
      0 < r →
        Metric.ball z r ⊆ E.domain →
          (∀ w, w ∈ Metric.ball z r →
            0 < (E.toLocalProjectiveDevelopingMap.affineMap w).im) →
            Nonempty (LocalProjectiveNormalFormDerivativeIdentificationData E r)

/--
Frobenius-specific second-derivative identification boundary after the actual
`ℍ`-valued lift has been constructed from the landing proof.

This strengthens `LocalProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem`:
besides identifying the derivative of the normal-form affine branch, it also
identifies the derivative of the normal-form first-derivative branch with the
stored second derivative.
-/
def LocalProjectiveFrobeniusNormalFormSecondDerivativeIdentificationTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄
    (hz : z ∈ P.toLocalProjectiveDevelopingMap.domain)
    (J : HyperbolicSchwarzianBaseJet u z)
    (E :
      LocalProjectiveNormalFormPostcompositionExplicitData
        P.toLocalProjectiveDevelopingMap z hz J.toNondegenerateFiniteTwoJet)
    (r : ℝ),
      0 < r →
        Metric.ball z r ⊆ E.domain →
          (∀ w, w ∈ Metric.ball z r →
            0 < (E.toLocalProjectiveDevelopingMap.affineMap w).im) →
            Nonempty (LocalProjectiveNormalFormSecondDerivativeIdentificationData E r)

/--
Frobenius-specific third-derivative identification boundary for explicit
normal-form branches whose stored third derivative is the explicit
normal-form chain-rule third derivative on the landing ball.
-/
def LocalProjectiveFrobeniusNormalFormThirdDerivativeIdentificationTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄
    (hz : z ∈ P.toLocalProjectiveDevelopingMap.domain)
    (J : HyperbolicSchwarzianBaseJet u z)
    (E :
      LocalProjectiveNormalFormPostcompositionExplicitData
        P.toLocalProjectiveDevelopingMap z hz J.toNondegenerateFiniteTwoJet)
    (r : ℝ),
      0 < r →
        Metric.ball z r ⊆ E.domain →
          (∀ w, w ∈ Metric.ball z r →
            0 < (E.toLocalProjectiveDevelopingMap.affineMap w).im) →
            (∀ w, w ∈ Metric.ball z r →
              E.toLocalProjectiveDevelopingMap.affineMapThirdDeriv w =
                (P.toLocalProjectiveDevelopingMap.normalFormPostcompositionAffineMapThirdDeriv
                  hz J.toNondegenerateFiniteTwoJet) w) →
            Nonempty (LocalProjectiveNormalFormThirdDerivativeIdentificationData E r)

/--
Canonical Frobenius third-derivative identification theorem.

This packages the canonical explicit-data construction, the upper-half-plane
landing ball, and the normal-form third-derivative identification data into a
single theorem-shaped output.
-/
def LocalProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄
    (hz : z ∈ P.toLocalProjectiveDevelopingMap.domain)
    (J : HyperbolicSchwarzianBaseJet u z),
      ∃ E :
        LocalProjectiveNormalFormPostcompositionExplicitData
          P.toLocalProjectiveDevelopingMap z hz J.toNondegenerateFiniteTwoJet,
        ∃ r : ℝ, 0 < r ∧
          Metric.ball z r ⊆ E.domain ∧
          (∀ w, w ∈ Metric.ball z r →
            0 < (E.toLocalProjectiveDevelopingMap.affineMap w).im) ∧
          Nonempty (LocalProjectiveNormalFormThirdDerivativeIdentificationData E r)

/--
Frobenius-specific construction of the full two-jet upper-half-plane
normalization.

Unlike `LocalProjectiveFrobeniusNormalFormUpperHalfPlaneLandingTheorem`, this
packages the restricted branch as a `LocalHyperbolicTwoJetUpperHalfPlaneNormalization`;
unlike the older broad upper-half-plane landing target, it keeps the remaining
derivative-identification input separate and only asks for it on the landing
ball.
-/
def LocalProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄
    (_hz : z ∈ P.toLocalProjectiveDevelopingMap.domain)
    (J : HyperbolicSchwarzianBaseJet u z),
      ∃ N :
        LocalHyperbolicTwoJetUpperHalfPlaneNormalization
          P.toLocalProjectiveDevelopingMap z,
        N.jet = J ∧ z ∈ N.domain

/--
Frobenius-specific sharp normal-form postcomposition theorem.

This is the constructed-map version of
`LocalProjectiveNormalFormPostcompositionTheorem`: it asks for transitivity
only for projective coordinates produced by the Frobenius Schwarzian ODE.
-/
def LocalProjectiveFrobeniusNormalFormPostcompositionTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄
    (hz : z ∈ P.toLocalProjectiveDevelopingMap.domain)
    (target : NondegenerateFiniteTwoJet),
      ∃ N :
        LocalProjectiveMobiusTwoJetNormalization
          P.toLocalProjectiveDevelopingMap z target,
        z ∈ N.domain ∧
          N.postcomposition =
            (P.toLocalProjectiveDevelopingMap.finiteTwoJet hz
              ).postcompositionNormalFormRepresentative target

/--
Frobenius-specific finite two-jet transitivity by Mobius postcomposition.
-/
def LocalProjectiveFrobeniusMobiusTwoJetTransitivityTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄,
    z ∈ P.toLocalProjectiveDevelopingMap.domain →
      ∀ target : NondegenerateFiniteTwoJet,
        ∃ N :
          LocalProjectiveMobiusTwoJetNormalization
            P.toLocalProjectiveDevelopingMap z target,
          z ∈ N.domain

/--
For Frobenius-produced projective maps, Schwarzian invariance alone gives the
explicit normal-form postcomposition data: the continuity/pole-avoidance part
is already proved from the convergent solution series.
-/
theorem localProjectiveFrobeniusNormalFormPostcompositionExplicitDataTheorem_of_schwarzian
    (hSchwarzian :
      LocalProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem) :
    LocalProjectiveFrobeniusNormalFormPostcompositionExplicitDataTheorem := by
  intro u S z₀ a P z hz target
  have hCont :
      ContinuousAt P.toLocalProjectiveDevelopingMap.affineMap z :=
    P.toLocalProjectiveDevelopingMap_affineMap_continuousAt hz
  rcases LocalProjectiveNormalFormPoleAvoidingShrink.exists_of_affineMap_continuousAt
      (D := P.toLocalProjectiveDevelopingMap) (z₀ := z) (hz₀ := hz)
      (target := target) hCont with ⟨shrink⟩
  rcases hSchwarzian P.toLocalProjectiveDevelopingMap hz target shrink with
    ⟨third, hthird⟩
  exact ⟨shrink.toExplicitData third hthird⟩

/--
For Frobenius-produced projective maps, explicit normal-form postcomposition
data is now available without an extra Schwarzian-invariance hypothesis.
-/
theorem localProjectiveFrobeniusNormalFormPostcompositionExplicitDataTheorem :
    LocalProjectiveFrobeniusNormalFormPostcompositionExplicitDataTheorem :=
  localProjectiveFrobeniusNormalFormPostcompositionExplicitDataTheorem_of_schwarzian
    localProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem

/--
For Frobenius-produced projective maps, the canonical explicit normal-form
postcomposition data is available, and it stores the actual normal-form
chain-rule third derivative.
-/
theorem localProjectiveFrobeniusNormalFormCanonicalPostcompositionExplicitDataTheorem :
    LocalProjectiveFrobeniusNormalFormCanonicalPostcompositionExplicitDataTheorem := by
  intro u S z₀ a P z hz target
  have hCont :
      ContinuousAt P.toLocalProjectiveDevelopingMap.affineMap z :=
    P.toLocalProjectiveDevelopingMap_affineMap_continuousAt hz
  rcases LocalProjectiveNormalFormPoleAvoidingShrink.exists_of_affineMap_continuousAt
      (D := P.toLocalProjectiveDevelopingMap) (z₀ := z) (hz₀ := hz)
      (target := target) hCont with ⟨shrink⟩
  exact ⟨shrink.toCanonicalExplicitData,
    fun w ↦ shrink.toCanonicalExplicitData_affineMapThirdDeriv_eq w⟩

/--
For Frobenius-produced maps, explicit normal-form Schwarzian invariance gives
the topological upper-half-plane landing ball for the hyperbolic target
normalization.
-/
theorem localProjectiveFrobeniusNormalFormUpperHalfPlaneLandingTheorem_of_schwarzian
    (hSchwarzian :
      LocalProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem) :
    LocalProjectiveFrobeniusNormalFormUpperHalfPlaneLandingTheorem := by
  intro u S z₀ a P z hz J
  rcases
      localProjectiveFrobeniusNormalFormPostcompositionExplicitDataTheorem_of_schwarzian
        hSchwarzian P hz J.toNondegenerateFiniteTwoJet with
    ⟨E⟩
  rcases E.exists_ball_mapsTo_upperHalfPlane_of_targetValue_eq_I
      (P.toLocalProjectiveDevelopingMap_affineMap_continuousAt hz)
      (by
        simp [HyperbolicSchwarzianBaseJet.toNondegenerateFiniteTwoJet,
          HyperbolicSchwarzianBaseJet.targetValue]) with
    ⟨r, hr_pos, hmaps⟩
  exact ⟨E, r, hr_pos, hmaps⟩

/--
%%handwave
name:
  Upper-half-plane landing after normalization
statement:
  Let $f$ be the quotient of a normalized Frobenius pair for a holomorphic
  Schwarzian coefficient, and fix $z_0$ in its domain. There is a Möbius
  transformation $M$ realizing the hyperbolic target two-jet at $z_0$ and a
  radius $r>0$ such that
  $\operatorname{Im}(M\circ f)(z)>0$ whenever $|z-z_0|<r$.
proof:
  The explicit two-jet normal form has no pole at $f(z_0)$ and sends
  $f(z_0)$ to $i$. Continuity first gives a pole-free neighborhood and then,
  because the upper half-plane is open and contains $i$, a smaller ball on
  which the imaginary part is positive.
-/
theorem localProjectiveFrobeniusNormalFormUpperHalfPlaneLandingTheorem :
    LocalProjectiveFrobeniusNormalFormUpperHalfPlaneLandingTheorem :=
  localProjectiveFrobeniusNormalFormUpperHalfPlaneLandingTheorem_of_schwarzian
    localProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem

/--
For Frobenius-produced maps, the canonical explicit normal-form branch lands
in the upper half-plane on a ball contained in its domain, and it keeps the
canonical third-derivative field.
-/
theorem localProjectiveFrobeniusNormalFormCanonicalLandingTheorem :
    LocalProjectiveFrobeniusNormalFormCanonicalLandingTheorem := by
  intro u S z₀ a P z hz J
  rcases localProjectiveFrobeniusNormalFormCanonicalPostcompositionExplicitDataTheorem
      P hz J.toNondegenerateFiniteTwoJet with
    ⟨E, hthird⟩
  rcases E.exists_ball_subset_domain_mapsTo_upperHalfPlane_of_targetValue_eq_I
      (P.toLocalProjectiveDevelopingMap_affineMap_continuousAt hz)
      (by
        simp [HyperbolicSchwarzianBaseJet.toNondegenerateFiniteTwoJet,
          HyperbolicSchwarzianBaseJet.targetValue]) with
    ⟨r, hr_pos, hsubset, hmaps⟩
  exact ⟨E, r, hr_pos, hsubset, hmaps, fun w _hw ↦ hthird w⟩

/--
Derivative-identification data gives the full upper-half-plane lift boundary:
the `ℍ`-valued map itself is built from the landing proof.
-/
theorem localProjectiveFrobeniusNormalFormUpperHalfPlaneLiftTheorem_of_derivativeIdentification
    (hDeriv : LocalProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem) :
    LocalProjectiveFrobeniusNormalFormUpperHalfPlaneLiftTheorem := by
  intro u S z₀ a P z hz J E r hr_pos hsubset hmaps
  rcases hDeriv P hz J E r hr_pos hsubset hmaps with ⟨A⟩
  exact ⟨E.liftDataOfDerivativeIdentification hmaps A⟩

/--
The remaining derivative-identification data for the explicit normal-form
branch follows from the actual derivative of the underlying Frobenius ratio.
-/
theorem localProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem_of_affineHasDerivAt
    (hBase : LocalProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem) :
    LocalProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem := by
  intro u S z₀ a P z hz J E r _hr_pos hsubset _hmaps
  refine ⟨{
    affineMap_hasDerivAt := ?_
    deriv_eq_projectiveDeriv := ?_
  }⟩
  · intro w hw
    have hwE : w ∈ E.domain := hsubset hw
    exact E.affineMap_hasDerivAt_of_original hwE
      (hBase P (E.domain_subset_original hwE))
  · intro w hw
    have hwE : w ∈ E.domain := hsubset hw
    exact E.deriv_eq_affineMapDeriv_of_original_hasDerivAt hwE
      (hBase P (E.domain_subset_original hwE))

/--
The second-derivative identification data for the explicit normal-form branch
follows from the actual derivative of the underlying Frobenius ratio and of
its first derivative.
-/
theorem localProjectiveFrobeniusNormalFormSecondDerivativeIdentificationTheorem_of_affineHasDerivAt
    (hBase : LocalProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem)
    (hBaseDeriv : LocalProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem) :
    LocalProjectiveFrobeniusNormalFormSecondDerivativeIdentificationTheorem := by
  intro u S z₀ a P z hz J E r _hr_pos hsubset _hmaps
  exact ⟨E.secondDerivativeIdentificationDataOfOriginalHasDerivAt
    hsubset
    (fun w hw ↦ hBase P (E.domain_subset_original (hsubset hw)))
    (fun w hw ↦ hBaseDeriv P (E.domain_subset_original (hsubset hw)))⟩

/--
Second-derivative identification implies first-derivative identification by
forgetting the derivative of the derivative branch.
-/
theorem localProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem_of_secondDerivativeIdentification
    (hSecond : LocalProjectiveFrobeniusNormalFormSecondDerivativeIdentificationTheorem) :
    LocalProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem := by
  intro u S z₀ a P z hz J E r hr_pos hsubset hmaps
  rcases hSecond P hz J E r hr_pos hsubset hmaps with ⟨A⟩
  exact ⟨A.toDerivativeIdentificationData⟩

/--
For Frobenius-produced maps, the explicit normal-form derivative field agrees
with the actual derivative on the landing ball.
-/
theorem localProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem :
    LocalProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem :=
  localProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem_of_secondDerivativeIdentification
    (localProjectiveFrobeniusNormalFormSecondDerivativeIdentificationTheorem_of_affineHasDerivAt
      localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem
      localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem)

/--
For Frobenius-produced maps, the explicit normal-form first-derivative branch
also has the stored second derivative on the landing ball.
-/
theorem localProjectiveFrobeniusNormalFormSecondDerivativeIdentificationTheorem :
    LocalProjectiveFrobeniusNormalFormSecondDerivativeIdentificationTheorem :=
  localProjectiveFrobeniusNormalFormSecondDerivativeIdentificationTheorem_of_affineHasDerivAt
    localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem
    localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem

/--
The third-derivative identification data for explicit normal-form branches
follows from the actual derivative of the underlying Frobenius ratio through
its second derivative branch, once the stored third derivative is the explicit
normal-form chain-rule field.
-/
theorem localProjectiveFrobeniusNormalFormThirdDerivativeIdentificationTheorem_of_affineHasDerivAt
    (hBase : LocalProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem)
    (hBaseDeriv : LocalProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem)
    (hBaseSecondDeriv :
      LocalProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem) :
    LocalProjectiveFrobeniusNormalFormThirdDerivativeIdentificationTheorem := by
  intro u S z₀ a P z hz J E r _hr_pos hsubset _hmaps hthird
  exact ⟨E.thirdDerivativeIdentificationDataOfOriginalHasDerivAt
    hsubset
    hthird
    (fun w hw ↦ hBase P (E.domain_subset_original (hsubset hw)))
    (fun w hw ↦ hBaseDeriv P (E.domain_subset_original (hsubset hw)))
    (fun w hw ↦ hBaseSecondDeriv P (E.domain_subset_original (hsubset hw)))⟩

/--
For Frobenius-produced maps, normal-form branches with the explicit
chain-rule third derivative identify actual derivatives through the second
derivative branch on the landing ball.
-/
theorem localProjectiveFrobeniusNormalFormThirdDerivativeIdentificationTheorem :
    LocalProjectiveFrobeniusNormalFormThirdDerivativeIdentificationTheorem :=
  localProjectiveFrobeniusNormalFormThirdDerivativeIdentificationTheorem_of_affineHasDerivAt
    localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem
    localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem
    localProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem

/--
The canonical explicit normal-form construction provides a landing ball and
derivative identification through the second derivative branch.
-/
theorem localProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem :
    LocalProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem := by
  intro u S z₀ a P z hz J
  rcases localProjectiveFrobeniusNormalFormCanonicalLandingTheorem P hz J with
    ⟨E, r, hr_pos, hsubset, hmaps, hthird⟩
  rcases localProjectiveFrobeniusNormalFormThirdDerivativeIdentificationTheorem
      P hz J E r hr_pos hsubset hmaps hthird with
    ⟨A⟩
  exact ⟨E, r, hr_pos, hsubset, hmaps, ⟨A⟩⟩

/--
For Frobenius-produced maps, the explicit normal-form upper-half-plane lift
data is available on the landing ball.
-/
theorem localProjectiveFrobeniusNormalFormUpperHalfPlaneLiftTheorem :
    LocalProjectiveFrobeniusNormalFormUpperHalfPlaneLiftTheorem :=
  localProjectiveFrobeniusNormalFormUpperHalfPlaneLiftTheorem_of_derivativeIdentification
    localProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem

/--
The explicit-data construction, the strengthened landing ball inside the
explicit domain, and the remaining lift data give the full Frobenius
upper-half-plane two-jet normalization.
-/
theorem localProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem_of_lift
    (hLift : LocalProjectiveFrobeniusNormalFormUpperHalfPlaneLiftTheorem) :
    LocalProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem := by
  intro u S z₀ a P z hz J
  rcases localProjectiveFrobeniusNormalFormPostcompositionExplicitDataTheorem
      P hz J.toNondegenerateFiniteTwoJet with
    ⟨E⟩
  rcases E.exists_ball_subset_domain_mapsTo_upperHalfPlane_of_targetValue_eq_I
      (P.toLocalProjectiveDevelopingMap_affineMap_continuousAt hz)
      (by
        simp [HyperbolicSchwarzianBaseJet.toNondegenerateFiniteTwoJet,
          HyperbolicSchwarzianBaseJet.targetValue]) with
    ⟨r, hr_pos, hsubset, hmaps⟩
  rcases hLift P hz J E r hr_pos hsubset hmaps with ⟨L⟩
  let N :=
    L.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization hr_pos hsubset
  exact ⟨N, rfl, N.base_mem⟩

/--
The Frobenius upper-half-plane normalization route expressed through actual
derivative identification for the explicit normal-form affine branch.
-/
theorem localProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem_of_derivativeIdentification
    (hDeriv : LocalProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem) :
    LocalProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem :=
  localProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem_of_lift
    (localProjectiveFrobeniusNormalFormUpperHalfPlaneLiftTheorem_of_derivativeIdentification
      hDeriv)

/--
Canonical third-derivative identification gives the full Frobenius
upper-half-plane two-jet normalization by forgetting to the derivative
identification needed for the `ℍ`-valued lift.
-/
theorem localProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem_of_canonicalThirdDerivativeIdentification
    (hThird :
      LocalProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem) :
    LocalProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem := by
  intro u S z₀ a P z hz J
  rcases hThird P hz J with ⟨E, r, hr_pos, hsubset, hmaps, ⟨A⟩⟩
  let L : LocalProjectiveNormalFormUpperHalfPlaneLiftData E r :=
    E.liftDataOfDerivativeIdentification hmaps A.toDerivativeIdentificationData
  let N := L.toLocalHyperbolicTwoJetUpperHalfPlaneNormalization hr_pos hsubset
  exact ⟨N, rfl, N.base_mem⟩

/--
The current sharp Frobenius upper-half-plane normalization route expressed in
terms of the intrinsic derivative target for the Frobenius ratio itself.
-/
theorem localProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem_of_affineHasDerivAt
    (hBase : LocalProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem) :
    LocalProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem :=
  localProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem_of_derivativeIdentification
    (localProjectiveFrobeniusNormalFormDerivativeIdentificationTheorem_of_affineHasDerivAt
      hBase)

/--
%%handwave
name:
  Hyperbolic two-jet normalization
statement:
  Let $f$ be a local projective coordinate obtained as a ratio of the
  normalized Frobenius solutions for the metric Schwarzian of $u$, and let
  $z_0$ lie in its domain. After Möbius postcomposition and restriction to a
  smaller ball, one obtains a holomorphic map $F : V \to \mathbb H$ with
  $F(z_0)=i$, $F'(z_0)=e^{u(z_0)}$, and
  $F''(z_0)=F'(z_0)(2u_z(z_0)-iF'(z_0))$.
proof:
  For source and target two-jets $(a,b,c)$ and $(p,q,r)$, use the explicit
  normal form $M(w)=p+B(w-a)/(1+\kappa(w-a))$, where $B=q/b$ and
  $\kappa=-(r-Bc)/(2Bb^2)$. Its value and first two chain-rule derivatives
  realize the target jet. The denominator equals $1$ at the base point, so
  continuity gives a pole-free neighborhood; because the target value is
  $i$, a further shrinking lands in $\mathbb H$. The differentiated Frobenius
  series identify the recorded derivatives with the actual derivatives.
-/
theorem localProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem :
    LocalProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem :=
  localProjectiveFrobeniusNormalFormUpperHalfPlaneNormalizationTheorem_of_canonicalThirdDerivativeIdentification
    localProjectiveFrobeniusNormalFormCanonicalThirdDerivativeIdentificationTheorem

/--
The Frobenius explicit-data construction implies the Frobenius sharp
normal-form postcomposition theorem.
-/
theorem localProjectiveFrobeniusNormalFormPostcompositionTheorem_of_explicit
    (hExplicit :
      LocalProjectiveFrobeniusNormalFormPostcompositionExplicitDataTheorem) :
    LocalProjectiveFrobeniusNormalFormPostcompositionTheorem := by
  intro u S z₀ a P z hz target
  rcases hExplicit P hz target with ⟨E⟩
  let data : LocalProjectiveNormalFormPostcompositionData
      P.toLocalProjectiveDevelopingMap z hz target :=
    E.toPostcompositionData
  refine ⟨data.toMobiusTwoJetNormalization, ?_, ?_⟩
  · exact data.base_mem
  · exact data.toMobiusTwoJetNormalization_postcomposition

/--
For Frobenius-produced projective maps, the proved Schwarzian-invariance
calculation implies sharp normal-form postcomposition.
-/
theorem localProjectiveFrobeniusNormalFormPostcompositionTheorem_of_schwarzian
    (hSchwarzian :
      LocalProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem) :
    LocalProjectiveFrobeniusNormalFormPostcompositionTheorem :=
  localProjectiveFrobeniusNormalFormPostcompositionTheorem_of_explicit
    (localProjectiveFrobeniusNormalFormPostcompositionExplicitDataTheorem_of_schwarzian
      hSchwarzian)

/--
For Frobenius-produced projective maps, sharp normal-form postcomposition is
now available without an extra Schwarzian-invariance hypothesis.
-/
theorem localProjectiveFrobeniusNormalFormPostcompositionTheorem :
    LocalProjectiveFrobeniusNormalFormPostcompositionTheorem :=
  localProjectiveFrobeniusNormalFormPostcompositionTheorem_of_schwarzian
    localProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem

/--
Sharp Frobenius normal-form postcomposition implies the older Frobenius
finite two-jet transitivity statement.
-/
theorem localProjectiveFrobeniusMobiusTwoJetTransitivityTheorem_of_normalFormPostcomposition
    (hPostcompose : LocalProjectiveFrobeniusNormalFormPostcompositionTheorem) :
    LocalProjectiveFrobeniusMobiusTwoJetTransitivityTheorem := by
  intro u S z₀ a P z hz target
  rcases hPostcompose P hz target with ⟨N, hNz, _hpost⟩
  exact ⟨N, hNz⟩

/--
For Frobenius-produced projective maps, Schwarzian invariance of explicit
normal-form postcomposition implies finite two-jet transitivity.
-/
theorem localProjectiveFrobeniusMobiusTwoJetTransitivityTheorem_of_schwarzian
    (hSchwarzian :
      LocalProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem) :
    LocalProjectiveFrobeniusMobiusTwoJetTransitivityTheorem :=
  localProjectiveFrobeniusMobiusTwoJetTransitivityTheorem_of_normalFormPostcomposition
    (localProjectiveFrobeniusNormalFormPostcompositionTheorem_of_schwarzian
      hSchwarzian)

/--
For Frobenius-produced projective maps, finite two-jet transitivity by Mobius
postcomposition is now available without an extra Schwarzian-invariance
hypothesis.
-/
theorem localProjectiveFrobeniusMobiusTwoJetTransitivityTheorem :
    LocalProjectiveFrobeniusMobiusTwoJetTransitivityTheorem :=
  localProjectiveFrobeniusMobiusTwoJetTransitivityTheorem_of_schwarzian
    localProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem

/--
Affine continuity plus explicit Schwarzian invariance gives the explicit
normal-form postcomposition data theorem.
-/
theorem localProjectiveNormalFormPostcompositionExplicitDataTheorem_of_continuousAt_schwarzian
    (hCont : LocalProjectiveDevelopingMapAffineContinuousAtTheorem)
    (hSchwarzian :
      LocalProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem) :
    LocalProjectiveNormalFormPostcompositionExplicitDataTheorem := by
  intro u S D z hz target
  rcases LocalProjectiveNormalFormPoleAvoidingShrink.exists_of_affineMap_continuousAt
      (D := D) (z₀ := z) (hz₀ := hz) (target := target) (hCont D hz) with ⟨P⟩
  rcases hSchwarzian D hz target P with ⟨third, hthird⟩
  exact ⟨P.toExplicitData third hthird⟩

/--
The explicit-data normal-form construction implies the data-level construction.
-/
theorem localProjectiveNormalFormPostcompositionDataTheorem_of_explicit
    (hExplicit : LocalProjectiveNormalFormPostcompositionExplicitDataTheorem) :
    LocalProjectiveNormalFormPostcompositionDataTheorem := by
  intro u S D z hz target
  rcases hExplicit D hz target with ⟨E⟩
  exact ⟨E.toPostcompositionData⟩

/--
The data-level normal-form postcomposition construction implies the sharp
normal-form postcomposition theorem.
-/
theorem localProjectiveNormalFormPostcompositionTheorem_of_data
    (hData : LocalProjectiveNormalFormPostcompositionDataTheorem) :
    LocalProjectiveNormalFormPostcompositionTheorem := by
  intro u S D z hz target
  rcases hData D hz target with ⟨P⟩
  refine ⟨P.toMobiusTwoJetNormalization, ?_, ?_⟩
  · exact P.base_mem
  · exact P.toMobiusTwoJetNormalization_postcomposition

/--
The sharp normal-form postcomposition construction implies the older finite
two-jet transitivity boundary.
-/
theorem localProjectiveMobiusTwoJetTransitivityTheorem_of_normalFormPostcomposition
    (hPostcompose : LocalProjectiveNormalFormPostcompositionTheorem) :
    LocalProjectiveMobiusTwoJetTransitivityTheorem := by
  intro u S D z hz target
  rcases hPostcompose D hz target with ⟨N, hNz, _hpost⟩
  exact ⟨N, hNz⟩

/--
The data-level normal-form postcomposition construction implies the older
finite two-jet transitivity boundary.
-/
theorem localProjectiveMobiusTwoJetTransitivityTheorem_of_normalFormPostcompositionData
    (hData : LocalProjectiveNormalFormPostcompositionDataTheorem) :
    LocalProjectiveMobiusTwoJetTransitivityTheorem :=
  localProjectiveMobiusTwoJetTransitivityTheorem_of_normalFormPostcomposition
    (localProjectiveNormalFormPostcompositionTheorem_of_data hData)

/--
The explicit-data normal-form postcomposition construction implies the older
finite two-jet transitivity boundary.
-/
theorem localProjectiveMobiusTwoJetTransitivityTheorem_of_normalFormPostcompositionExplicit
    (hExplicit : LocalProjectiveNormalFormPostcompositionExplicitDataTheorem) :
    LocalProjectiveMobiusTwoJetTransitivityTheorem :=
  localProjectiveMobiusTwoJetTransitivityTheorem_of_normalFormPostcompositionData
    (localProjectiveNormalFormPostcompositionDataTheorem_of_explicit hExplicit)

/--
Affine continuity and Schwarzian invariance of explicit normal-form
postcomposition imply the older finite two-jet transitivity boundary.
-/
theorem localProjectiveMobiusTwoJetTransitivityTheorem_of_continuousAt_schwarzian
    (hCont : LocalProjectiveDevelopingMapAffineContinuousAtTheorem)
    (hSchwarzian :
      LocalProjectiveNormalFormPostcompositionSchwarzianInvariantTheorem) :
    LocalProjectiveMobiusTwoJetTransitivityTheorem :=
  localProjectiveMobiusTwoJetTransitivityTheorem_of_normalFormPostcompositionExplicit
    (localProjectiveNormalFormPostcompositionExplicitDataTheorem_of_continuousAt_schwarzian
      hCont hSchwarzian)

/--
A continuous complex-valued map whose imaginary part is positive at a base
point maps a small metric ball into the upper half-plane.
-/
theorem exists_ball_mapsTo_upperHalfPlane_of_continuousAt
    {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : ContinuousAt f z₀) (hpos : 0 < (f z₀).im) :
    ∃ r : ℝ, 0 < r ∧ ∀ z, z ∈ Metric.ball z₀ r → 0 < (f z).im := by
  have hopen : IsOpen {w : ℂ | 0 < w.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hpre : f ⁻¹' {w : ℂ | 0 < w.im} ∈ nhds z₀ :=
    hf.preimage_mem_nhds (hopen.mem_nhds hpos)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨r, hr_pos, hr_subset⟩
  exact ⟨r, hr_pos, by
    intro z hz
    exact hr_subset hz⟩

/--
A continuous complex-valued map normalized to take value `i` maps a small
metric ball into the upper half-plane.
-/
theorem exists_ball_mapsTo_upperHalfPlane_of_continuousAt_eq_I
    {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : ContinuousAt f z₀) (hvalue : f z₀ = Complex.I) :
    ∃ r : ℝ, 0 < r ∧ ∀ z, z ∈ Metric.ball z₀ r → 0 < (f z).im := by
  apply exists_ball_mapsTo_upperHalfPlane_of_continuousAt hf
  simp [hvalue]

/--
The hyperbolic upper-half-plane landing theorem after precise projective
two-jet normalization.

This is the place where the analytic argument should show that the Mobius
normal form determined by the hyperbolic jet can be restricted to a
metric ball on which the affine coordinate lands in `ℍ`.
-/
def HyperbolicProjectiveTwoJetNormalizationLandsInUpperHalfPlaneTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z : ℂ}
    (J : HyperbolicSchwarzianBaseJet u z)
    (N : LocalProjectiveMobiusTwoJetNormalization D z J.toNondegenerateFiniteTwoJet),
    u.SolvesLiouvilleEquation →
      ∃ H : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z,
        H.normalized.projective = N.projective ∧ z ∈ H.domain

/--
Precise Mobius-normalization existence target.

After solving the Schwarzian equation projectively, choose a Mobius
postcomposition so that the resulting `ℍ`-valued branch realizes the
hyperbolic base 2-jet:

* value `i`;
* first derivative `exp (u z₀)`, positive real;
* second derivative
  `exp (u z₀) * (2 * u_z(z₀) - i * exp (u z₀))`.

This theorem only chooses the normalized branch and records the 2-jet.  The
separate theorem `HyperbolicTwoJetNormalizationRecoversMetricTheorem` is the
analytic uniqueness statement that this 2-jet normalization recovers the
original metric.
-/
def HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    (D : LocalProjectiveDevelopingMap S) ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ D.domain →
      ∃ N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z,
        z ∈ N.domain

/--
Base-jet existence, projective two-jet transitivity, and upper-half-plane
landing imply the precise hyperbolic two-jet normalization theorem.
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem_of_projectiveTwoJet
    (hBase : HyperbolicSchwarzianBaseJetExistenceTheorem)
    (hMobius : LocalProjectiveMobiusTwoJetTransitivityTheorem)
    (hUpper : HyperbolicProjectiveTwoJetNormalizationLandsInUpperHalfPlaneTheorem) :
    HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem := by
  intro u S D z hu hz
  rcases hBase hu (D.domain_subset hz) with ⟨J⟩
  rcases hMobius D hz J.toNondegenerateFiniteTwoJet with ⟨P, _hPz⟩
  rcases hUpper S J P hu with ⟨H, _hHP, hHz⟩
  exact ⟨H, hHz⟩

/--
Projective two-jet transitivity and upper-half-plane landing imply the precise
hyperbolic two-jet normalization theorem; the canonical base jet is constructed
internally.
-/
theorem hyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem_of_projectiveTwoJetLanding
    (hMobius : LocalProjectiveMobiusTwoJetTransitivityTheorem)
    (hUpper : HyperbolicProjectiveTwoJetNormalizationLandsInUpperHalfPlaneTheorem) :
    HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem := by
  intro u S D z hu hz
  rcases hyperbolicSchwarzianBaseJetExistenceTheorem hu (D.domain_subset hz) with ⟨J⟩
  rcases hMobius D hz J.toNondegenerateFiniteTwoJet with ⟨P, _hPz⟩
  rcases hUpper S J P hu with ⟨H, _hHP, hHz⟩
  exact ⟨H, hHz⟩

/--
Frobenius-produced local projective maps admit the prescribed hyperbolic
two-jet normalization.

This is the constructed-map analogue of
`HyperbolicProjectiveDevelopingMapAdmitsTwoJetNormalizationTheorem`: instead of
assuming Mobius two-jet transitivity for arbitrary projective developing maps,
it keeps the centered Frobenius pair in the output and uses the
Frobenius-specific transitivity theorem.
-/
def HyperbolicLiouvilleProducesFrobeniusTwoJetNormalizationsTheorem : Prop :=
  ∀ (u : LocalConformalFactor) ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ u.coordinateDomain →
      ∃ (S : LocalSchwarzianData u) (a : ℕ → ℂ)
        (P :
          CenteredNormalizedSchwarzianFrobeniusPair
            S.coefficient u.coordinateDomain z a)
        (N :
          LocalHyperbolicTwoJetUpperHalfPlaneNormalization
            P.toLocalProjectiveDevelopingMap z),
          z ∈ N.domain

/--
The Poincare pullback of a two-jet normalized upper-half-plane branch gives a
competing Liouville solution with the same Schwarzian data and the same
normalized base data.

This sharper theorem target contains the direct calculation
`v = log |F'| - log Im(F)`: it proves the Liouville equation for `v`, computes
its Schwarzian coefficient, and checks from the prescribed two-jet that
`v(z₀)=u(z₀)` and `v_z(z₀)=u_z(z₀)`.
-/
def HyperbolicTwoJetPullbackLiouvilleFormulaTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicPullbackLiouvilleFormulaData N)

/--
Sharper canonical pullback formula theorem.

This version fixes the logarithmic density to
`(1 / 2) log (|F'|² / (Im F)²)`, so the squared-density pullback formula is
proved by the canonical positivity/logarithm lemmas rather than stored as a
separate analytic obligation.
-/
def HyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackLiouvilleFormulaData N)

/--
The sharpened canonical pullback core theorem.

Compared with `HyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem`, this
asks for the two concrete geometric calculations: the Laplacian of the
Poincare pullback log-density and the equality between its metric Schwarzian
and the branch Schwarzian.  The remaining quotient/log/base-jet algebra is
proved by Lean.
-/
def HyperbolicTwoJetCanonicalPullbackCoreTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackCoreData N)

/--
Canonical pullback theorem with the Poincare Laplacian calculation reduced to
the mixed-Wirtinger identity
`∂_{\bar z} ∂_z v = (1 / 4) |F'|² / (Im F)²`.
-/
def HyperbolicTwoJetCanonicalPullbackMixedWirtingerLaplacianTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackMixedWirtingerLaplacianData N)

/--
Canonical pullback theorem with the Poincare mixed Laplacian calculation
reduced to differentiating the explicit first pullback Wirtinger expression.
-/
def HyperbolicTwoJetCanonicalPullbackMixedExpressionTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackMixedExpressionData N)

/--
Canonical pullback theorem with the Schwarzian side reduced to the explicit
first and second Wirtinger formulas for the canonical Poincare pullback
log-density.
-/
def HyperbolicTwoJetCanonicalPullbackWirtingerFormulaTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackWirtingerFormulaData N)

/--
Canonical pullback theorem with the first Wirtinger formula replaced by the
pointwise squared-density derivative formula.
-/
def HyperbolicTwoJetCanonicalPullbackDensityDerivativeTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackDensityDerivativeData N)

/--
Canonical pullback theorem where the second Wirtinger formula is reduced to
the Frechet derivative of the explicit first Wirtinger expression.
-/
def HyperbolicTwoJetCanonicalPullbackSecondExpressionTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackSecondExpressionData N)

/--
Canonical pullback theorem where the second-expression derivative is proved
from actual branch derivative identities through `F''`.
-/
def HyperbolicTwoJetCanonicalPullbackThirdDerivativeTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackThirdDerivativeData N)

/--
Canonical pullback theorem where the upper-half-plane branch derivative is
reduced to the affine projective branch derivative.
-/
def HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackAffineDerivativeData N)

/--
Canonical pullback theorem where actual affine branch derivative data are
separated from the geometric Poincare Laplacian identity.
-/
def HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackAffineDerivativeAlgebraData N)

/-- The full affine-derivative theorem forgets to affine derivative algebra. -/
theorem hyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem_of_affineDerivative
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem) :
    HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.toAffineDerivativeAlgebraData⟩

/--
Canonical pullback theorem for the regularity side of the normalized Poincare
pullback calculation.
-/
def HyperbolicTwoJetCanonicalPullbackRegularityTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackRegularityData N)

/--
Canonical pullback theorem for the algebraic identification of the stored
affine derivatives with mathlib's `deriv` operator.
-/
def HyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackFirstDerivativeIdentificationData N)

/--
Canonical pullback theorem for identifying the derivative of the stored
first-derivative affine branch.
-/
def HyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackSecondDerivativeIdentificationData N)

/--
Canonical pullback theorem for identifying the derivative of the stored
second-derivative affine branch.
-/
def HyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackThirdDerivativeIdentificationData N)

/--
Canonical pullback theorem for the algebraic identification of all stored
affine derivatives with mathlib's `deriv` operator.
-/
def HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackDerivativeIdentificationData N)

/--
The three separate affine derivative-identification theorems give the bundled
derivative-identification theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem_of_first_second_third
    (hFirst : HyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem)
    (hSecond : HyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem)
    (hThird : HyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem := by
  intro u S D z₀ N hu
  rcases hFirst S N hu with ⟨I₁⟩
  rcases hSecond S N hu with ⟨I₂⟩
  rcases hThird S N hu with ⟨I₃⟩
  exact ⟨I₁.withSecondAndThird I₂ I₃⟩

/-- The bundled derivative-identification theorem forgets to the first level. -/
theorem hyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem_of_derivativeIdentification
    (hId : HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem) :
    HyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem := by
  intro u S D z₀ N hu
  rcases hId S N hu with ⟨I⟩
  exact ⟨I.toFirstDerivativeIdentificationData⟩

/-- The bundled derivative-identification theorem forgets to the second level. -/
theorem hyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem_of_derivativeIdentification
    (hId : HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem) :
    HyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem := by
  intro u S D z₀ N hu
  rcases hId S N hu with ⟨I⟩
  exact ⟨I.toSecondDerivativeIdentificationData⟩

/-- The bundled derivative-identification theorem forgets to the third level. -/
theorem hyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem_of_derivativeIdentification
    (hId : HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem) :
    HyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem := by
  intro u S D z₀ N hu
  rcases hId S N hu with ⟨I⟩
  exact ⟨I.toThirdDerivativeIdentificationData⟩

/--
Canonical pullback theorem where affine branch derivatives are identified with
mathlib's `deriv` operator.
-/
def HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackDerivativeAlgebraData N)

/--
Regularity plus derivative identification give the derivative-algebra theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem_of_regularity_and_derivativeIdentification
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hId : HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem := by
  intro u S D z₀ N hu
  rcases hReg S N hu with ⟨R⟩
  rcases hId S N hu with ⟨I⟩
  exact ⟨R.withDerivativeIdentification I⟩

/--
Regularity plus the three affine derivative-identification levels give the
derivative-algebra theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem_of_regularity_first_second_third
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hFirst : HyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem)
    (hSecond : HyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem)
    (hThird : HyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem :=
  hyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem_of_regularity_and_derivativeIdentification
    hReg
    (hyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem_of_first_second_third
      hFirst hSecond hThird)

/-- The derivative-algebra theorem forgets to the regularity theorem. -/
theorem hyperbolicTwoJetCanonicalPullbackRegularityTheorem_of_derivativeAlgebra
    (hAlg : HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem) :
    HyperbolicTwoJetCanonicalPullbackRegularityTheorem := by
  intro u S D z₀ N hu
  rcases hAlg S N hu with ⟨A⟩
  exact ⟨A.toRegularityData⟩

/-- The derivative-algebra theorem forgets to the derivative-identification theorem. -/
theorem hyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem_of_derivativeAlgebra
    (hAlg : HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem := by
  intro u S D z₀ N hu
  rcases hAlg S N hu with ⟨A⟩
  exact ⟨A.toDerivativeIdentificationData⟩

/--
Actual affine derivative algebra implies the derivative-algebra theorem by
identifying mathlib's `deriv` values from the supplied `HasDerivAt` proofs.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem_of_affineDerivativeAlgebra
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.toDerivativeAlgebraData⟩

/--
Derivative algebra gives actual affine derivative algebra.  This removes the
need to pair derivative algebra with a separate Poincare Laplacian theorem:
after converting to actual `HasDerivAt` data, the mixed-expression calculation
supplies that Laplacian field internally.
-/
theorem hyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem_of_derivativeAlgebra
    (hAlg : HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem) :
    HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem := by
  intro u S D z₀ N hu
  rcases hAlg S N hu with ⟨A⟩
  exact ⟨A.toAffineDerivativeAlgebraData⟩

/--
Actual affine derivative algebra directly supplies the regularity side of the
canonical pullback derivative-algebra package.
-/
theorem hyperbolicTwoJetCanonicalPullbackRegularityTheorem_of_affineDerivativeAlgebra
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem) :
    HyperbolicTwoJetCanonicalPullbackRegularityTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.toRegularityData⟩

/--
Canonical pullback theorem for the geometric Laplacian identity
`Δ log(|F'| / Im F) = |F'|² / (Im F)²`.
-/
def HyperbolicTwoJetCanonicalPullbackLaplacianTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      ∀ z, z ∈ N.domain →
      Laplacian.laplacian N.pullbackLogDensity z =
        N.pullbackDensitySq z

/--
Actual affine derivative algebra implies the Poincare Laplacian theorem via
the explicit mixed-expression derivative calculation.
-/
theorem hyperbolicTwoJetCanonicalPullbackLaplacianTheorem_of_affineDerivativeAlgebra
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem) :
    HyperbolicTwoJetCanonicalPullbackLaplacianTheorem := by
  intro u S D z₀ N hu z hz
  rcases hA S N hu with ⟨A⟩
  exact A.toCoreData.laplacian_eq_pullbackDensitySq z hz

/--
Canonical pullback theorem where affine branch derivatives are identified with
mathlib's `deriv` operator and the Poincare Laplacian calculation is included.
-/
def HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackDerivIdentifiedData N)

/--
Affine derivative algebra plus the geometric Laplacian identity give the full
affine-derivative canonical pullback theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem_of_affineDerivativeAlgebra_and_laplacian
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem)
    (hLap : HyperbolicTwoJetCanonicalPullbackLaplacianTheorem) :
    HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.withLaplacian (hLap S N hu)⟩

/--
Actual affine derivative algebra gives the full affine-derivative canonical
pullback theorem; the Poincare Laplacian field is supplied by the explicit
mixed-expression calculation.
-/
theorem hyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem_of_affineDerivativeAlgebra
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem) :
    HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.withLaplacian A.toCoreData.laplacian_eq_pullbackDensitySq⟩

/--
Actual affine derivative algebra plus the geometric Laplacian identity give the
derivative-identified canonical pullback theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_affineDerivativeAlgebra_and_laplacian
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem)
    (hLap : HyperbolicTwoJetCanonicalPullbackLaplacianTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨(A.withLaplacian (hLap S N hu)).toDerivIdentifiedData⟩

/--
Actual affine derivative algebra gives the derivative-identified canonical
pullback theorem, with the Poincare Laplacian field obtained internally.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_affineDerivativeAlgebra
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨(A.withLaplacian A.toCoreData.laplacian_eq_pullbackDensitySq).toDerivIdentifiedData⟩

/--
Derivative algebra plus the geometric Laplacian identity give the
derivative-identified canonical pullback theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_derivativeAlgebra_and_laplacian
    (hAlg : HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem)
    (hLap : HyperbolicTwoJetCanonicalPullbackLaplacianTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem := by
  intro u S D z₀ N hu
  rcases hAlg S N hu with ⟨A⟩
  exact ⟨A.withLaplacian (hLap S N hu)⟩

/--
Derivative algebra gives the derivative-identified canonical pullback theorem
without a separate Poincare Laplacian input, by first converting to actual
affine derivative algebra.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_derivativeAlgebra
    (hAlg : HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem :=
  hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_affineDerivativeAlgebra
    (hyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem_of_derivativeAlgebra
      hAlg)

/--
Regularity, derivative identification, and the geometric Laplacian identity
give the derivative-identified canonical pullback theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_regularity_derivativeIdentification_and_laplacian
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hId : HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem)
    (hLap : HyperbolicTwoJetCanonicalPullbackLaplacianTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem :=
  hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_derivativeAlgebra_and_laplacian
    (hyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem_of_regularity_and_derivativeIdentification
      hReg hId)
    hLap

/--
Regularity and derivative identification give the derivative-identified
canonical pullback theorem.  The Poincare Laplacian calculation is obtained
internally from the resulting derivative algebra.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_regularity_derivativeIdentification
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hId : HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem :=
  hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_derivativeAlgebra
    (hyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem_of_regularity_and_derivativeIdentification
      hReg hId)

/--
Regularity, the three derivative-identification levels, and the geometric
Laplacian identity give the derivative-identified canonical pullback theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_regularity_first_second_third_laplacian
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hFirst : HyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem)
    (hSecond : HyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem)
    (hThird : HyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem)
    (hLap : HyperbolicTwoJetCanonicalPullbackLaplacianTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem :=
  hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_regularity_derivativeIdentification_and_laplacian
    hReg
    (hyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem_of_first_second_third
      hFirst hSecond hThird)
    hLap

/--
Regularity and the three derivative-identification levels give the
derivative-identified canonical pullback theorem.  The Poincare Laplacian
calculation is supplied internally by the derivative-algebra route.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_regularity_first_second_third
    (hReg : HyperbolicTwoJetCanonicalPullbackRegularityTheorem)
    (hFirst : HyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem)
    (hSecond : HyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem)
    (hThird : HyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem :=
  hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_regularity_derivativeIdentification
    hReg
    (hyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem_of_first_second_third
      hFirst hSecond hThird)

/--
The derivative-identified canonical pullback theorem forgets to the derivative
algebra part.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem_of_derivIdentified
    (hD : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem := by
  intro u S D z₀ N hu
  rcases hD S N hu with ⟨A⟩
  exact ⟨A.toDerivativeAlgebraData⟩

/-- The derivative-identified theorem forgets to the regularity theorem. -/
theorem hyperbolicTwoJetCanonicalPullbackRegularityTheorem_of_derivIdentified
    (hD : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem) :
    HyperbolicTwoJetCanonicalPullbackRegularityTheorem := by
  intro u S D z₀ N hu
  rcases hD S N hu with ⟨A⟩
  exact ⟨A.toRegularityData⟩

/-- The derivative-identified theorem forgets to the derivative-identification theorem. -/
theorem hyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem_of_derivIdentified
    (hD : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem := by
  intro u S D z₀ N hu
  rcases hD S N hu with ⟨A⟩
  exact ⟨A.toDerivativeIdentificationData⟩

/--
The derivative-identified canonical pullback theorem forgets to the geometric
Laplacian identity.
-/
theorem hyperbolicTwoJetCanonicalPullbackLaplacianTheorem_of_derivIdentified
    (hD : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem) :
    HyperbolicTwoJetCanonicalPullbackLaplacianTheorem := by
  intro u S D z₀ N hu z hz
  rcases hD S N hu with ⟨A⟩
  exact A.laplacian_eq_pullbackDensitySq z hz

/--
Canonical pullback theorem where the first-derivative side is reduced to actual
branch derivative statements.
-/
def HyperbolicTwoJetCanonicalPullbackBranchDerivativeTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicCanonicalPullbackBranchDerivativeData N)

/--
Affine projective derivative data imply the third-derivative theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackThirdDerivativeTheorem_of_affineDerivative
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem) :
    HyperbolicTwoJetCanonicalPullbackThirdDerivativeTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.toThirdDerivativeData⟩

/--
Derivative-identification data imply the affine-derivative theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem_of_derivIdentified
    (hA : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem) :
    HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.toAffineDerivativeData⟩

/--
Actual affine `HasDerivAt` data imply the derivative-identified theorem via
mathlib's `HasDerivAt.deriv`.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_affineDerivative
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.toDerivIdentifiedData⟩

/--
Actual affine `HasDerivAt` data imply the derivative-algebra theorem by
forgetting the Laplacian field.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem_of_affineDerivative
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem :=
  hyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem_of_derivIdentified
    (hyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem_of_affineDerivative hA)

/--
Actual affine `HasDerivAt` data imply the derivative-identification theorem by
forgetting regularity and the Laplacian field.
-/
theorem hyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem_of_affineDerivative
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem) :
    HyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem :=
  hyperbolicTwoJetCanonicalPullbackDerivativeIdentificationTheorem_of_derivativeAlgebra
    (hyperbolicTwoJetCanonicalPullbackDerivativeAlgebraTheorem_of_affineDerivative hA)

/--
Actual affine `HasDerivAt` data directly supply the regularity side of the
canonical pullback derivative-algebra package.
-/
theorem hyperbolicTwoJetCanonicalPullbackRegularityTheorem_of_affineDerivative
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem) :
    HyperbolicTwoJetCanonicalPullbackRegularityTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.toRegularityData⟩

/--
Actual affine `HasDerivAt` data give the first derivative-identification
theorem directly.
-/
theorem hyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem_of_affineDerivative
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem) :
    HyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.toFirstDerivativeIdentificationData⟩

/--
Actual affine `HasDerivAt` data give the second derivative-identification
theorem directly.
-/
theorem hyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem_of_affineDerivative
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem) :
    HyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.toSecondDerivativeIdentificationData⟩

/--
Actual affine `HasDerivAt` data give the third derivative-identification
theorem directly.
-/
theorem hyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem_of_affineDerivative
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem) :
    HyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.toThirdDerivativeIdentificationData⟩

/--
Actual affine derivative algebra gives the first derivative-identification
theorem directly.
-/
theorem hyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem_of_affineDerivativeAlgebra
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem) :
    HyperbolicTwoJetCanonicalPullbackFirstDerivativeIdentificationTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.toFirstDerivativeIdentificationData⟩

/--
Actual affine derivative algebra gives the second derivative-identification
theorem directly.
-/
theorem hyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem_of_affineDerivativeAlgebra
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem) :
    HyperbolicTwoJetCanonicalPullbackSecondDerivativeIdentificationTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.toSecondDerivativeIdentificationData⟩

/--
Actual affine derivative algebra gives the third derivative-identification
theorem directly.
-/
theorem hyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem_of_affineDerivativeAlgebra
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem) :
    HyperbolicTwoJetCanonicalPullbackThirdDerivativeIdentificationTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.toThirdDerivativeIdentificationData⟩

/--
Actual branch derivatives through `F''` imply the explicit first-expression
derivative theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackSecondExpressionTheorem_of_thirdDerivative
    (hT : HyperbolicTwoJetCanonicalPullbackThirdDerivativeTheorem) :
    HyperbolicTwoJetCanonicalPullbackSecondExpressionTheorem := by
  intro u S D z₀ N hu
  rcases hT S N hu with ⟨T⟩
  exact ⟨T.toSecondExpressionData⟩

/--
The explicit first-expression derivative theorem implies the actual branch
derivative theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackBranchDerivativeTheorem_of_secondExpression
    (hE : HyperbolicTwoJetCanonicalPullbackSecondExpressionTheorem) :
    HyperbolicTwoJetCanonicalPullbackBranchDerivativeTheorem := by
  intro u S D z₀ N hu
  rcases hE S N hu with ⟨E⟩
  exact ⟨E.toBranchDerivativeData⟩

/--
Actual branch derivative data imply the squared-density derivative theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackDensityDerivativeTheorem_of_branchDerivative
    (hB : HyperbolicTwoJetCanonicalPullbackBranchDerivativeTheorem) :
    HyperbolicTwoJetCanonicalPullbackDensityDerivativeTheorem := by
  intro u S D z₀ N hu
  rcases hB S N hu with ⟨B⟩
  exact ⟨B.toDensityDerivativeData⟩

/--
The squared-density derivative pullback theorem implies the explicit
Wirtinger-formula theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackWirtingerFormulaTheorem_of_densityDerivative
    (hP : HyperbolicTwoJetCanonicalPullbackDensityDerivativeTheorem) :
    HyperbolicTwoJetCanonicalPullbackWirtingerFormulaTheorem := by
  intro u S D z₀ N hu
  rcases hP S N hu with ⟨P⟩
  exact ⟨P.toWirtingerFormulaData⟩

/--
The explicit Wirtinger-formula pullback theorem implies the canonical core
theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackCoreTheorem_of_wirtingerFormula
    (hW : HyperbolicTwoJetCanonicalPullbackWirtingerFormulaTheorem) :
    HyperbolicTwoJetCanonicalPullbackCoreTheorem := by
  intro u S D z₀ N hu
  rcases hW S N hu with ⟨W⟩
  exact ⟨W.toCoreData⟩

/--
The mixed-Wirtinger Laplacian pullback theorem implies the canonical core
theorem by the general `∂_{\bar z} ∂_z = (1 / 4) Δ` bridge.
-/
theorem hyperbolicTwoJetCanonicalPullbackCoreTheorem_of_mixedWirtingerLaplacian
    (hM : HyperbolicTwoJetCanonicalPullbackMixedWirtingerLaplacianTheorem) :
    HyperbolicTwoJetCanonicalPullbackCoreTheorem := by
  intro u S D z₀ N hu
  rcases hM S N hu with ⟨M⟩
  exact ⟨M.toCoreData⟩

/--
The explicit mixed-expression theorem implies the mixed-Wirtinger Laplacian
theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackMixedWirtingerLaplacianTheorem_of_mixedExpression
    (hM : HyperbolicTwoJetCanonicalPullbackMixedExpressionTheorem) :
    HyperbolicTwoJetCanonicalPullbackMixedWirtingerLaplacianTheorem := by
  intro u S D z₀ N hu
  rcases hM S N hu with ⟨M⟩
  exact ⟨M.toMixedWirtingerLaplacianData⟩

/--
Actual affine derivative algebra proves the explicit mixed-expression pullback
theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackMixedExpressionTheorem_of_affineDerivativeAlgebra
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem) :
    HyperbolicTwoJetCanonicalPullbackMixedExpressionTheorem := by
  intro u S D z₀ N hu
  rcases hA S N hu with ⟨A⟩
  exact ⟨A.toMixedExpressionData⟩

/--
The explicit mixed-expression theorem implies the canonical core theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackCoreTheorem_of_mixedExpression
    (hM : HyperbolicTwoJetCanonicalPullbackMixedExpressionTheorem) :
    HyperbolicTwoJetCanonicalPullbackCoreTheorem :=
  hyperbolicTwoJetCanonicalPullbackCoreTheorem_of_mixedWirtingerLaplacian
    (hyperbolicTwoJetCanonicalPullbackMixedWirtingerLaplacianTheorem_of_mixedExpression hM)

/--
Actual affine derivative algebra implies the canonical core theorem; the
Poincare Laplacian calculation is obtained from the explicit mixed-expression
derivative calculation.
-/
theorem hyperbolicTwoJetCanonicalPullbackCoreTheorem_of_affineDerivativeAlgebra
    (hA : HyperbolicTwoJetCanonicalPullbackAffineDerivativeAlgebraTheorem) :
    HyperbolicTwoJetCanonicalPullbackCoreTheorem :=
  hyperbolicTwoJetCanonicalPullbackCoreTheorem_of_mixedExpression
    (hyperbolicTwoJetCanonicalPullbackMixedExpressionTheorem_of_affineDerivativeAlgebra hA)

/--
The core canonical pullback theorem implies the canonical pullback Liouville
formula theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem_of_core
    (hCore : HyperbolicTwoJetCanonicalPullbackCoreTheorem) :
    HyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem := by
  intro u S D z₀ N hu
  rcases hCore S N hu with ⟨C⟩
  exact ⟨C.toFormulaData⟩

/--
The explicit Wirtinger-formula pullback theorem implies the canonical pullback
Liouville formula theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem_of_wirtingerFormula
    (hW : HyperbolicTwoJetCanonicalPullbackWirtingerFormulaTheorem) :
    HyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem :=
  hyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem_of_core
    (hyperbolicTwoJetCanonicalPullbackCoreTheorem_of_wirtingerFormula hW)

/--
The squared-density derivative pullback theorem implies the canonical pullback
Liouville formula theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem_of_densityDerivative
    (hP : HyperbolicTwoJetCanonicalPullbackDensityDerivativeTheorem) :
    HyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem :=
  hyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem_of_wirtingerFormula
    (hyperbolicTwoJetCanonicalPullbackWirtingerFormulaTheorem_of_densityDerivative hP)

/--
Derivative-identified affine branch data imply the third-derivative pullback
theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackThirdDerivativeTheorem_of_derivIdentified
    (hD : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem) :
    HyperbolicTwoJetCanonicalPullbackThirdDerivativeTheorem :=
  hyperbolicTwoJetCanonicalPullbackThirdDerivativeTheorem_of_affineDerivative
    (hyperbolicTwoJetCanonicalPullbackAffineDerivativeTheorem_of_derivIdentified hD)

/--
Derivative-identified affine branch data imply the second-expression pullback
theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackSecondExpressionTheorem_of_derivIdentified
    (hD : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem) :
    HyperbolicTwoJetCanonicalPullbackSecondExpressionTheorem :=
  hyperbolicTwoJetCanonicalPullbackSecondExpressionTheorem_of_thirdDerivative
    (hyperbolicTwoJetCanonicalPullbackThirdDerivativeTheorem_of_derivIdentified hD)

/--
Derivative-identified affine branch data imply the branch-derivative pullback
theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackBranchDerivativeTheorem_of_derivIdentified
    (hD : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem) :
    HyperbolicTwoJetCanonicalPullbackBranchDerivativeTheorem :=
  hyperbolicTwoJetCanonicalPullbackBranchDerivativeTheorem_of_secondExpression
    (hyperbolicTwoJetCanonicalPullbackSecondExpressionTheorem_of_derivIdentified hD)

/--
Derivative-identified affine branch data imply the squared-density derivative
pullback theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackDensityDerivativeTheorem_of_derivIdentified
    (hD : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem) :
    HyperbolicTwoJetCanonicalPullbackDensityDerivativeTheorem :=
  hyperbolicTwoJetCanonicalPullbackDensityDerivativeTheorem_of_branchDerivative
    (hyperbolicTwoJetCanonicalPullbackBranchDerivativeTheorem_of_derivIdentified hD)

/--
Derivative-identified affine branch data imply the Wirtinger-formula pullback
theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackWirtingerFormulaTheorem_of_derivIdentified
    (hD : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem) :
    HyperbolicTwoJetCanonicalPullbackWirtingerFormulaTheorem :=
  hyperbolicTwoJetCanonicalPullbackWirtingerFormulaTheorem_of_densityDerivative
    (hyperbolicTwoJetCanonicalPullbackDensityDerivativeTheorem_of_derivIdentified hD)

/--
Derivative-identified affine branch data imply the canonical core pullback
theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackCoreTheorem_of_derivIdentified
    (hD : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem) :
    HyperbolicTwoJetCanonicalPullbackCoreTheorem :=
  hyperbolicTwoJetCanonicalPullbackCoreTheorem_of_wirtingerFormula
    (hyperbolicTwoJetCanonicalPullbackWirtingerFormulaTheorem_of_derivIdentified hD)

/--
Derivative-identified affine branch data imply the canonical pullback
Liouville formula theorem.
-/
theorem hyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem_of_derivIdentified
    (hD : HyperbolicTwoJetCanonicalPullbackDerivIdentifiedTheorem) :
    HyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem :=
  hyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem_of_core
    (hyperbolicTwoJetCanonicalPullbackCoreTheorem_of_derivIdentified hD)

/--
The canonical pullback formula theorem implies the older explicit formula
theorem.
-/
theorem hyperbolicTwoJetPullbackLiouvilleFormulaTheorem_of_canonical
    (hCanonical : HyperbolicTwoJetCanonicalPullbackLiouvilleFormulaTheorem) :
    HyperbolicTwoJetPullbackLiouvilleFormulaTheorem := by
  intro u S D z₀ N hu
  rcases hCanonical S N hu with ⟨P⟩
  exact ⟨P.toFormulaData⟩

/--
The Poincare pullback of a two-jet normalized upper-half-plane branch gives a
competing Liouville solution with the same Schwarzian data and the same
normalized base data.

This is the older packaged target, retained for downstream compatibility.  The
sharper formula target above constructs this package from an explicit
log-density formula.
-/
def HyperbolicTwoJetPullbackLiouvilleCandidateTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalHyperbolicPullbackLiouvilleCandidate N)

/--
The explicit Poincare pullback formula theorem implies the older pullback
candidate theorem.
-/
theorem hyperbolicTwoJetPullbackLiouvilleCandidateTheorem_of_formula
    (hFormula : HyperbolicTwoJetPullbackLiouvilleFormulaTheorem) :
    HyperbolicTwoJetPullbackLiouvilleCandidateTheorem := by
  intro u S D z₀ N hu
  rcases hFormula S N hu with ⟨P⟩
  exact ⟨LocalHyperbolicPullbackLiouvilleCandidate.ofFormulaData P⟩

/--
The normalized local domains may be chosen to be complex metric balls.

This is the concrete shrinking form that automatically implies the
preconnected-domain condition used by local uniqueness.
-/
def HyperbolicTwoJetNormalizationHasBallDomainTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
      ∃ c r, N.domain = Metric.ball c r

/-- Two-jet normalizations are packaged after shrinking to metric balls. -/
theorem hyperbolicTwoJetNormalizationHasBallDomainTheorem :
    HyperbolicTwoJetNormalizationHasBallDomainTheorem := by
  intro u S D z₀ N
  rcases N.domain_eq_ball with ⟨c, r, hdomain⟩
  exact ⟨c, r, by
    simpa [LocalHyperbolicTwoJetUpperHalfPlaneNormalization.domain] using hdomain⟩

/--
The normalized local domains may be chosen connected enough for local
uniqueness.

This is deliberately separated from the uniqueness theorem: in practice it is
usually discharged by shrinking to a ball around the base point.
-/
def HyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
      IsPreconnected N.domain

/-- Ball-shaped normalized domains are preconnected by mathlib. -/
theorem hyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem_of_ballDomain
    (hBallDomain : HyperbolicTwoJetNormalizationHasBallDomainTheorem) :
    HyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem := by
  intro u S D z₀ N
  rcases hBallDomain S N with ⟨c, r, hdomain⟩
  rw [hdomain]
  exact Metric.isPreconnected_ball

/--
The complete local Cauchy data for the Liouville-Schwarzian uniqueness
argument.

The analytic proof should use these fields as follows.  Both log-densities
solve the hyperbolic Liouville equation on the same preconnected domain; their
Schwarzian projective-connection coefficient agrees; and the base value plus
the first Wirtinger derivative agree at `z₀`.  This is the local initial-value
uniqueness problem for the Liouville-Schwarzian system.
-/
structure LocalLiouvilleSchwarzianUniquenessData
    {u : LocalConformalFactor} {S : LocalSchwarzianData u}
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀)
    (C : LocalHyperbolicPullbackLiouvilleCandidate N) where
  /-- The original conformal factor solves Liouville. -/
  original_solvesLiouville : u.SolvesLiouvilleEquation
  /-- The pullback conformal factor solves Liouville. -/
  pullback_solvesLiouville : C.conformalFactor.SolvesLiouvilleEquation
  /-- The local domain is preconnected. -/
  domain_preconnected : IsPreconnected N.domain
  /-- The pullback conformal factor is defined on the normalized domain. -/
  pullback_domain_eq : C.conformalFactor.coordinateDomain = N.domain
  /-- The two factors determine the same Schwarzian projective-connection coefficient. -/
  same_schwarzian_coefficient :
    ∀ z, z ∈ N.domain →
      LocalSchwarzianData.metricSchwarzianCoefficient
          C.conformalFactor.halfSchwarzianCoefficient z =
        S.coefficient z
  /-- The base log-density values agree. -/
  base_logDensity_eq :
    C.conformalFactor.logDensity z₀ = u.logDensity z₀
  /-- The base first Wirtinger derivatives agree. -/
  base_uZ_eq :
    C.conformalFactor.wirtingerZ z₀ = u.wirtingerZ z₀

end

end JJMath
