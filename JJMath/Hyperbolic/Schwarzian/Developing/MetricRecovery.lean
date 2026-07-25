import JJMath.Hyperbolic.Schwarzian.Developing.PullbackLiouville

/-!
# Split Schwarzian developing-map constructions
-/

namespace JJMath

open UpperHalfPlane

noncomputable section





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

/-- The normalized upper-half-plane branch chosen near a point.
%%handwave
name:
  Normalized branch selected by a Schwarzian atlas
statement:
  At each coordinate point, a metric-recovering Schwarzian atlas selects the upper-half-plane branch obtained from its projective solution and Möbius normalization.
-/
def normalizedBranch {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianNormalizationAtlas u) (z : u.coordinateDomain) :
    LocalUpperHalfPlaneDevelopingMap (A.schwarzianAt z) :=
  (A.normalizationAt z).normalized

/--
The normalized branches cover the coordinate domain.

%%handwave
name:
  A normalized Schwarzian atlas covers its centers
statement:
  For every metric-recovering Schwarzian normalization atlas A and every center z, the selected normalized upper-half-plane branch at z is defined at z.
proof:
  Unpack the base-point coverage field of the normalization atlas.
-/
theorem mem_normalizedBranch_domain {u : LocalConformalFactor}
    (A : LocalMetricRecoveringSchwarzianNormalizationAtlas u)
    (z : u.coordinateDomain) :
    (z : ℂ) ∈ (A.normalizedBranch z).domain :=
  A.mem_normalized_domain z

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

/-- The underlying Schwarzian data of a metric-data normalization atlas.
%%handwave
name:
  Schwarzian data underlying metric-Schwarzian data
statement:
  At each center, forget the metric-identification witness and retain the holomorphic Schwarzian coefficient selected by the metric-data atlas.
-/
def schwarzianAt {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas u)
    (z : u.coordinateDomain) : LocalSchwarzianData u :=
  (A.metricSchwarzianAt z).toLocalSchwarzianData

/-- The normalized upper-half-plane branch chosen near a point.
%%handwave
name:
  Normalized branch selected by a metric-Schwarzian atlas
statement:
  At each coordinate point, the metric-Schwarzian atlas selects the upper-half-plane branch of its metric-recovering normalization.
-/
def normalizedBranch {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas u)
    (z : u.coordinateDomain) :
    LocalUpperHalfPlaneDevelopingMap (A.schwarzianAt z) :=
  (A.normalizationAt z).normalized

/-- Forget the metric-Schwarzian witnesses.
%%handwave
name:
  Normalization atlas underlying a metric-Schwarzian atlas
statement:
  Forgetting the proof that each coefficient is the metric Schwarzian retains the selected Schwarzian data, projective maps, normalized branches, coverage, and overlap connectedness.
-/
def toLocalMetricRecoveringSchwarzianNormalizationAtlas {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas u) :
    LocalMetricRecoveringSchwarzianNormalizationAtlas u where
  schwarzianAt := A.schwarzianAt
  projectiveAt := A.projectiveAt
  normalizationAt := A.normalizationAt
  mem_normalized_domain := A.mem_normalized_domain
  overlap_preconnected := A.overlap_preconnected

/--
The metric-Schwarzian witnesses make branch coefficient agreement formal.

%%handwave
name:
  Metric-Schwarzian branches have the same coefficient on overlaps
statement:
  For two normalized branches selected from metric-Schwarzian data for the same conformal factor u, their Schwarzian coefficients agree at every point in the overlap of their domains.
proof:
  Each chosen coefficient equals the canonical metric Schwarzian coefficient of u, so both sides equal the same value pointwise.
-/
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

/-- Forget derivative algebra, retaining only the metric-Schwarzian data atlas.
%%handwave
name:
  Metric-data atlas underlying a derivative-data atlas
statement:
  Forgetting the first- through third-derivative identities retains the metric-Schwarzian normalization atlas with the same branches and overlaps.
-/
def toMetricDataAtlas {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas u) :
    LocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas u :=
  A.toLocalMetricSchwarzianDataRecoveringSchwarzianNormalizationAtlas

/-- The normalized branch chosen by a derivative-data atlas.
%%handwave
name:
  Normalized branch selected by a derivative-data atlas
statement:
  At each center, a derivative-data atlas uses the normalized upper-half-plane branch of its underlying metric-Schwarzian atlas.
-/
def normalizedBranch {u : LocalConformalFactor}
    (A : LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas u)
    (z : u.coordinateDomain) :
    LocalUpperHalfPlaneDevelopingMap (A.toMetricDataAtlas.schwarzianAt z) :=
  A.toMetricDataAtlas.normalizedBranch z

/--
Each normalized branch in a derivative-data atlas carries the fixed-branch
projective derivative regularity package.

%%handwave
name:
  Projective derivative regularity of each selected branch
statement:
  Every normalized branch in a derivative-data metric-Schwarzian atlas has actual derivatives f₁′ = f₂ and f₂′ = f₃ throughout its domain.
proof:
  Read the two derivative identities stored at the chosen center and transport them through the definition of the selected normalized branch.
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

/--
Coefficient agreement on overlaps is inherited from the metric-data atlas.

%%handwave
name:
  Overlapping developing branches have the same Schwarzian coefficient
statement:
  Any two branches in a derivative-data metric-Schwarzian atlas have equal Schwarzian coefficients at every point of their domain overlap.
proof:
  Forget the derivative fields and use the fact that both coefficients equal the canonical metric Schwarzian of the same conformal factor.
-/
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

%%handwave
name:
  Off-diagonal overlapping branches admit a real Möbius one-jet comparison
statement:
  For distinct selected normalized branches F and G with nonempty overlap, there is a real Möbius map M such that G = M ∘ F and G′ = (M ∘ F)′ throughout the overlap.
proof:
  Match the two branches at one overlap point, then use their stored projective derivative regularity, common Schwarzian coefficient, and preconnectedness to propagate equality of values and derivatives.
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

%%handwave
name:
  All branch pairs admit a real Möbius one-jet comparison
statement:
  For every pair of selected normalized branches F and G in a derivative-data atlas, there is a real Möbius map M such that G = M ∘ F and G′ = (M ∘ F)′ throughout their overlap.
proof:
  Use the identity map for equal branches, vacuity for empty overlaps, and coefficient-aware one-jet propagation on a nonempty off-diagonal overlap.
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

%%handwave
name:
  All branch pairs admit a real Möbius transition
statement:
  For every pair of selected normalized branches F and G in a derivative-data atlas, there is a real Möbius map M with G = M ∘ F throughout their overlap.
proof:
  Obtain the real Möbius one-jet comparison and forget its derivative equality.
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

end LocalMetricSchwarzianDerivativeDataRecoveringSchwarzianNormalizationAtlas

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

/-- Forget the Schwarzian-normalization provenance and keep an `ℍ`-branch atlas.
%%handwave
name:
  Real upper-half-plane atlas underlying a real Schwarzian atlas
statement:
  Forgetting the projective ODE and normalization provenance retains the chosen upper-half-plane branches, their coverage and connected overlaps, and their real Möbius transitions.
-/
def toLocalRealUpperHalfPlaneBranchAtlas {u : LocalConformalFactor}
    (A : LocalRealSchwarzianNormalizationAtlas u) :
    LocalRealUpperHalfPlaneBranchAtlas u where
  schwarzianAt := A.schwarzianAt
  branchAt := fun z ↦ A.normalizedBranch z
  mem_branchAt_domain := A.mem_normalizedBranch_domain
  overlap_preconnected := A.overlap_preconnected
  transition_realMobius := A.transition_realMobius

end LocalRealSchwarzianNormalizationAtlas

/--
The real-overlap refinement of the local normalized-Schwarzian-atlas target.

%%handwave
name:
  Existence of a real Schwarzian normalization atlas
statement:
  This proposition asserts that every hyperbolic Liouville factor admits a metric-recovering Schwarzian normalization atlas whose branch transitions lie in $\mathrm{PSL}_2(\mathbb R)$.
-/
def HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem :
    Prop :=
  ∀ (u : LocalConformalFactor),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalRealSchwarzianNormalizationAtlas u)

/--
The local branch-atlas consequence: hyperbolic Liouville data produces local
upper-half-plane branches with real Mobius overlaps once the Schwarzian
normalization atlas has been constructed.

%%handwave
name:
  Existence of a real upper-half-plane branch atlas
statement:
  This proposition asserts that every solution of $\Delta u=e^{2u}$ admits local metric-recovering branches to $\mathbb H$ with real Möbius transitions on their overlaps.
-/
def HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem : Prop :=
  ∀ (u : LocalConformalFactor),
    u.SolvesLiouvilleEquation →
      Nonempty (LocalRealUpperHalfPlaneBranchAtlas u)

/--
Real Schwarzian normalization atlases forget to real upper-half-plane branch
atlases.

%%handwave
name:
  Real Schwarzian atlases give upper-half-plane branch atlases
statement:
  If every Liouville solution admits a metric-recovering Schwarzian normalization atlas with real Möbius transitions, then every such solution admits an upper-half-plane branch atlas with the same domains and transitions.
proof:
  Forget the chosen Schwarzian ODE and normalization provenance while retaining each upper-half-plane branch, its domain, and its real transition maps.
-/
theorem hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem_of_realSchwarzian
    (h : HyperbolicLiouvilleProducesLocalRealSchwarzianNormalizationAtlasTheorem) :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem := by
  intro u hu
  rcases h u hu with ⟨A⟩
  exact ⟨A.toLocalRealUpperHalfPlaneBranchAtlas⟩

namespace LocalSchwarzianODEChart

/-- Projectivize the affine Schwarzian ODE chart to a local projective developing map.
%%handwave
name:
  Projective developing map associated to a Schwarzian ODE chart
statement:
  A local solution quotient $f$ of the Schwarzian ODE determines a projective branch $z\mapsto[f(z):1]$ with its first three derivative fields and Schwarzian coefficient.
-/
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

%%handwave
name:
  Local Schwarzian ODE chart from a centered Frobenius pair
statement:
  A nondegenerate centered normalized Frobenius pair determines on its centered ball the Schwarzian ODE chart whose coordinate is the quotient of its two solutions.
-/
def toLocalSchwarzianODEChart
    {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a) :
    LocalSchwarzianODEChart S where
  domain := centeredBallDomain z₀ P.radius
  isOpen_domain := isOpen_centeredBallDomain z₀ P.radius
  domain_subset := P.domain_subset
  frame := P.toNormalizedSchwarzianLinearODESolutionPair.toSchwarzianLinearODEFrame

/-- Projectivize the local developing coordinate obtained from a Frobenius pair.
%%handwave
name:
  Projective developing map from a centered Frobenius pair
statement:
  A centered normalized Frobenius pair determines the projective developing branch obtained by projectivizing its local solution quotient.
-/
def toLocalProjectiveDevelopingMap
    {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a) :
    LocalProjectiveDevelopingMap S :=
  P.toLocalSchwarzianODEChart.toLocalProjectiveDevelopingMap

/--
The projective developing map produced from a centered Frobenius pair has a
continuous affine coordinate on its domain.

%%handwave
name:
  Continuity of a Frobenius projective coordinate
statement:
  If f = y₁/y₂ is the projective coordinate determined by a centered normalized Frobenius pair, then f is continuous at every point of its ball domain.
proof:
  Identify the projective affine coordinate with the quotient of the two Frobenius solutions and use the established continuity of that quotient.
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

%%handwave
name:
  Smoothness of a Frobenius projective coordinate
statement:
  If f = y₁/y₂ is the projective coordinate determined by a centered normalized Frobenius pair, then f is C³ on its ball domain.
proof:
  After identifying f with the Frobenius quotient, apply the proved C³ regularity of that quotient.
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

%%handwave
name:
  Smoothness of the derivative of a Frobenius projective coordinate
statement:
  For a centered normalized Frobenius pair, the stored derivative f₁ of the projective quotient f is C³ on its ball domain.
proof:
  Rewrite f₁ by the Wronskian quotient formula and apply its established C³ regularity.
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

%%handwave
name:
  The derivative of a Frobenius projective coordinate
statement:
  If the two centered Frobenius solutions have their prescribed actual derivatives, then the projective quotient f satisfies f′(z) = f₁(z) at every point z of its ball domain.
proof:
  Apply the quotient rule to f = y₁/y₂, using nonvanishing of the denominator and the assumed actual derivatives of the two solutions.
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

%%handwave
name:
  The second derivative of a Frobenius projective coordinate
statement:
  If the centered Frobenius solutions have their prescribed first and second derivatives, then the stored derivative f₁ of their projective quotient satisfies f₁′(z) = f₂(z) throughout the ball domain.
proof:
  Differentiate the Wronskian quotient formula for f₁ using the assumed solution derivatives and the Schwarzian differential equation.
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

%%handwave
name:
  The third derivative of a Frobenius projective coordinate
statement:
  If the centered Frobenius solutions have their prescribed first and second derivatives, then the stored second derivative f₂ of their projective quotient satisfies f₂′(z) = f₃(z) throughout the ball domain.
proof:
  Differentiate the explicit formula for f₂ and simplify with the solution differential equation and the Wronskian formula.
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
Existence of the hyperbolic base two-jet, using the canonical Frechet-Wirtinger
field `u.wirtingerZ`.

%%handwave
name:
  Existence of the canonical hyperbolic base two-jet
statement:
  This proposition asserts that at each point of a hyperbolic Liouville factor, the normalized jet with value $i$, first derivative $e^{u}$, and compatible second derivative determined by $u_z$ is nondegenerate.
-/
def HyperbolicSchwarzianBaseJetExistenceTheorem : Prop :=
  ∀ {u : LocalConformalFactor} ⦃z : ℂ⦄,
    u.SolvesLiouvilleEquation → z ∈ u.coordinateDomain →
      Nonempty (HyperbolicSchwarzianBaseJet u z)

/--
The base jet is obtained from the canonical Frechet-Wirtinger derivative.

%%handwave
name:
  Existence of the hyperbolic Schwarzian base jet
statement:
  If u solves Δu = e^{2u} and z lies in its coordinate domain, then the finite two-jet with value i, first derivative e^{u(z)}, and second derivative e^{u(z)}(2u_z(z) − i e^{u(z)}) is defined and nondegenerate.
proof:
  Use the canonical Wirtinger derivative u_z(z); positivity of e^{u(z)} supplies nondegeneracy, and the compatibility field is immediate.
-/
theorem hyperbolicSchwarzianBaseJetExistenceTheorem :
    HyperbolicSchwarzianBaseJetExistenceTheorem := by
  intro u z _hu _hz
  exact ⟨{
    uZ := u.wirtingerZ z
    agrees_with_logDensity_derivative := rfl
  }⟩

/--
Actual differentiability boundary for local projective developing maps that
come from the centered Frobenius construction.

This is the natural remaining analytic target below the upper-half-plane
normalization: prove the quotient rule for the ratio of the two convergent
Frobenius solutions, with the symbolic first derivative already stored in the
projective map.

%%handwave
name:
  Actual first derivative of a Frobenius projective coordinate
statement:
  This proposition asserts that the affine coordinate $f=y_1/y_0$ of every centered Frobenius pair has its stored quotient expression as its actual complex derivative on the centered ball.
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

%%handwave
name:
  Actual second derivative of a Frobenius projective coordinate
statement:
  This proposition asserts that the stored first derivative of every Frobenius projective coordinate differentiates to its stored second derivative throughout the ball domain.
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

%%handwave
name:
  Actual third derivative of a Frobenius projective coordinate
statement:
  This proposition asserts that the stored second derivative of every Frobenius projective coordinate differentiates to its stored third derivative throughout the ball domain.
-/
def LocalProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem : Prop :=
  ∀ {u : LocalConformalFactor} {S : LocalSchwarzianData u} {z₀ : ℂ} {a : ℕ → ℂ}
    (P : CenteredNormalizedSchwarzianFrobeniusPair S.coefficient u.coordinateDomain z₀ a)
    ⦃z : ℂ⦄,
      z ∈ P.toLocalProjectiveDevelopingMap.domain →
        HasDerivAt (fun w : ℂ ↦ P.toLocalProjectiveDevelopingMap.affineMapSecondDeriv w)
          (P.toLocalProjectiveDevelopingMap.affineMapThirdDeriv z) z

/--
The individual Frobenius-solution derivative theorem proves the quotient-rule
boundary for Frobenius projective developing maps.

%%handwave
name:
  The first derivative of every Frobenius projective coordinate
statement:
  Every such projective coordinate satisfies f′ = f₁ throughout its ball domain.
proof:
  Apply the quotient rule using the assumed actual derivatives of the two Frobenius solutions.
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

%%handwave
name:
  The first derivative of every Frobenius projective coordinate
statement:
  Every such projective coordinate satisfies f′ = f₁ throughout its ball domain.
proof:
  Apply the established scalar power-series differentiation theorem and the resulting quotient-rule identity.
-/
theorem localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem :
    LocalProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem :=
  localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem_of_solutionHasDerivAt
    centeredSchwarzianFrobeniusSolutionHasDerivAtTheorem

/--
The individual Frobenius-solution first- and second-derivative theorems prove
the quotient-rule boundary for the first affine derivative of Frobenius
projective developing maps.

%%handwave
name:
  The second derivative of every Frobenius projective coordinate
statement:
  Every such projective coordinate satisfies f₁′ = f₂ throughout its ball domain.
proof:
  Differentiate the quotient and its first derivative using the assumed actual first and second derivatives of the Frobenius solutions.
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

%%handwave
name:
  The second derivative of every Frobenius projective coordinate
statement:
  Every such projective coordinate satisfies f₁′ = f₂ throughout its ball domain.
proof:
  The scalar power-series differentiation theorem supplies the actual derivatives of the Frobenius solutions; substitute them into the corresponding quotient-rule calculation.
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

%%handwave
name:
  The second derivative of every Frobenius projective coordinate
statement:
  Every such projective coordinate satisfies f₁′ = f₂ throughout its ball domain.
proof:
  Apply the established scalar power-series differentiation theorem and the resulting quotient-rule identity.
-/
theorem localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem :
    LocalProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem :=
  localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    scalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem

/--
The individual Frobenius-solution first- and second-derivative theorems also
prove the quotient-rule boundary for the second affine derivative of Frobenius
projective developing maps.

%%handwave
name:
  The third derivative of every Frobenius projective coordinate
statement:
  Every such projective coordinate satisfies f₂′ = f₃ throughout its ball domain.
proof:
  Differentiate the quotient formulas through second order using the assumed actual first and second derivatives of the Frobenius solutions.
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

%%handwave
name:
  The third derivative of every Frobenius projective coordinate
statement:
  Every such projective coordinate satisfies f₂′ = f₃ throughout its ball domain.
proof:
  The scalar power-series differentiation theorem supplies the actual derivatives of the Frobenius solutions; substitute them into the corresponding quotient-rule calculation.
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

%%handwave
name:
  The third derivative of every Frobenius projective coordinate
statement:
  Every such projective coordinate satisfies f₂′ = f₃ throughout its ball domain.
proof:
  Apply the established scalar power-series differentiation theorem and the resulting quotient-rule identity.
-/
theorem localProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem :
    LocalProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem :=
  localProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem_of_scalarFormalPowerSeriesDeriv
    scalarFormalPowerSeriesDerivHasFPowerSeriesOnBallTheorem

/--
Frobenius-specific canonical explicit normal-form postcomposition target.

This strengthens `LocalProjectiveFrobeniusNormalFormPostcompositionExplicitDataTheorem`:
the stored third derivative is required to be the explicit normal-form
chain-rule third derivative, not merely some field making the Schwarzian
equation true.

%%handwave
name:
  Canonical explicit normal form for a Frobenius projective coordinate
statement:
  This proposition asserts that a Frobenius projective branch and a target two-jet admit the canonical Möbius postcomposition whose stored third derivative equals the explicit third-order chain-rule expression.
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
Frobenius-specific canonical landing theorem.

It returns a landing ball inside the canonical explicit-data domain and
remembers that the stored third derivative is the normal-form chain-rule field
on that ball.

%%handwave
name:
  Canonical upper-half-plane landing ball for a Frobenius normal form
statement:
  This proposition asserts that the canonical normal form matching the hyperbolic base jet maps some ball about the base point into $\mathbb H$ and retains the explicit third-derivative formula there.
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
Frobenius-specific third-derivative identification boundary for explicit
normal-form branches whose stored third derivative is the explicit
normal-form chain-rule third derivative on the landing ball.

%%handwave
name:
  Third-derivative identification for a Frobenius normal form
statement:
  This proposition asserts that on a landing ball, a canonical Frobenius normal-form branch whose third derivative is the explicit chain-rule field carries the complete first-, second-, and third-derivative identification data.
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
For Frobenius-produced projective maps, the canonical explicit normal-form
postcomposition data is available, and it stores the actual normal-form
chain-rule third derivative.

%%handwave
name:
  Canonical Frobenius normal forms have an explicit third-order Möbius postcomposition
statement:
  For every projective coordinate f obtained from a centered Frobenius pair and every nondegenerate target two-jet, the explicit normal-form postcomposition M ∘ f is defined on a pole-free open shrink, has the target chain-rule jet, and carries its canonical third derivative.
proof:
  Continuity gives a neighborhood avoiding the unique Möbius pole. Use the explicit normal-form formulas for M, its first three derivatives, and the resulting Schwarzian identity.
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
For Frobenius-produced maps, the canonical explicit normal-form branch lands
in the upper half-plane on a ball contained in its domain, and it keeps the
canonical third-derivative field.

%%handwave
name:
  Canonical normal-form landing in the upper half-plane
statement:
  For every projective coordinate f obtained from a centered Frobenius pair and the hyperbolic target jet at z₀, the canonical normal-form branch M ∘ f maps a ball B(z₀,r) contained in its pole-free domain into ℍ and retains the canonical third derivative.
proof:
  Construct the canonical pole-free branch. Since its base value is i, continuity and openness of ℍ give a smaller ball mapping to ℍ; retain the canonical third-derivative formula.
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
The third-derivative identification data for explicit normal-form branches
follows from the actual derivative of the underlying Frobenius ratio through
its second derivative branch, once the stored third derivative is the explicit
normal-form chain-rule field.

%%handwave
name:
  Third-order derivative identification for a normal-form branch
statement:
  For every projective coordinate f obtained from a centered Frobenius pair, the explicit normal-form branch on its landing ball satisfies (M ∘ f)′, (M ∘ f)″, and (M ∘ f)‴ equal to the stored chain-rule derivative fields through third order.
proof:
  Apply the chain rule through third order to the actual derivatives f′ = f₁, f₁′ = f₂, and f₂′ = f₃, and use the explicit normal-form third derivative.
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

%%handwave
name:
  Third-order derivative identification for a normal-form branch
statement:
  For every projective coordinate f obtained from a centered Frobenius pair, the explicit normal-form branch on its landing ball satisfies (M ∘ f)′, (M ∘ f)″, and (M ∘ f)‴ equal to the stored chain-rule derivative fields through third order.
proof:
  Apply the chain rule through third order to the actual derivatives f′ = f₁, f₁′ = f₂, and f₂′ = f₃, and use the explicit normal-form third derivative.
-/
theorem localProjectiveFrobeniusNormalFormThirdDerivativeIdentificationTheorem :
    LocalProjectiveFrobeniusNormalFormThirdDerivativeIdentificationTheorem :=
  localProjectiveFrobeniusNormalFormThirdDerivativeIdentificationTheorem_of_affineHasDerivAt
    localProjectiveFrobeniusDevelopingMapAffineHasDerivAtTheorem
    localProjectiveFrobeniusDevelopingMapAffineDerivHasDerivAtTheorem
    localProjectiveFrobeniusDevelopingMapAffineSecondDerivHasDerivAtTheorem

/--
The normalized local domains may be chosen to be complex metric balls.

This is the concrete shrinking form that automatically implies the
preconnected-domain condition used by local uniqueness.

%%handwave
name:
  Ball domains for hyperbolic two-jet normalizations
statement:
  This proposition asserts that the domain of every hyperbolic two-jet normalization is a complex metric ball.
-/
def HyperbolicTwoJetNormalizationHasBallDomainTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
      ∃ c r, N.domain = Metric.ball c r

/--
Two-jet normalizations are packaged after shrinking to metric balls.

%%handwave
name:
  Two-jet normalizations have ball domains
statement:
  The domain of every normalized upper-half-plane branch obtained from a hyperbolic two-jet normalization is a complex metric ball.
proof:
  Unpack the ball-domain witness stored in the normalization and rewrite its domain by that equality.
-/
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

%%handwave
name:
  Preconnected domains for hyperbolic two-jet normalizations
statement:
  This proposition asserts that the domain of every hyperbolic two-jet normalization is preconnected.
-/
def HyperbolicTwoJetNormalizationHasPreconnectedDomainTheorem : Prop :=
  ∀ {u : LocalConformalFactor} (S : LocalSchwarzianData u)
    {D : LocalProjectiveDevelopingMap S} {z₀ : ℂ}
    (N : LocalHyperbolicTwoJetUpperHalfPlaneNormalization D z₀),
      IsPreconnected N.domain

/--
Ball-shaped normalized domains are preconnected by mathlib.

%%handwave
name:
  Ball-shaped normalization domains are preconnected
statement:
  If every hyperbolic two-jet normalization has a metric-ball domain, then every such normalization domain is preconnected.
proof:
  Rewrite the domain as a metric ball and use preconnectedness of metric balls.
-/
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
