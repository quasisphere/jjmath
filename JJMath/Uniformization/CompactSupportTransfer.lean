import JJMath.Manifold.DeRhamPoincare
import JJMath.Manifold.SmoothImplicitLevel
import JJMath.Manifold.OneFormPeriod
import JJMath.Analysis.Sobolev.Rellich
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Compactly supported transport of planar top-degree densities

This file develops the coordinate calculation used to move a compactly
supported two-form through a relatively compact corridor.  The first step is
the explicit rectangle construction: subtract a product density with the
same horizontal mass, then integrate the resulting zero-mean density in the
horizontal direction and the remaining marginal in the vertical direction.
-/

open Set MeasureTheory
open scoped Interval Manifold ContDiff Topology

namespace JJMath.Uniformization

noncomputable section

/-! ## Extension by zero from an open submanifold -/

open JJMath.Manifold

universe u v w z

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M]
variable {ι : Type z}

/-- The ambient image of a compact set in an open submanifold. -/
def smoothFormCompactCore
    (U : TopologicalSpace.Opens M) (K : Set U) : Set M :=
  (fun x : U ↦ (x : M)) '' K

omit [T2Space M] in
/-- The ambient image of a compact subset of an open submanifold is
compact. -/
theorem smoothFormCompactCore_isCompact
    (U : TopologicalSpace.Opens M) (K : Set U) (hK : IsCompact K) :
    IsCompact (smoothFormCompactCore U K) := by
  exact hK.image continuous_subtype_val

/-- Regard an ambient set contained in an open set as a set in the open
submanifold. -/
def smoothFormCompactCoreInOpen
    (V : TopologicalSpace.Opens M) (C : Set M) : Set V :=
  {x | (x : M) ∈ C}

omit [T2Space M] in
/-- Passing an ambient set into an open submanifold and then back to the
ambient manifold recovers it, provided it lies in that open set. -/
theorem smoothFormCompactCore_coreInOpen
    (V : TopologicalSpace.Opens M) (C : Set M) (hCV : C ⊆ V) :
    smoothFormCompactCore V (smoothFormCompactCoreInOpen V C) = C := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hCV hx⟩, hx, rfl⟩

omit [T2Space M] in
/-- A compact ambient set contained in an open set remains compact when
regarded as a subset of that open submanifold. -/
theorem smoothFormCompactCoreInOpen_isCompact
    (V : TopologicalSpace.Opens M) (C : Set M) (hC : IsCompact C)
    (hCV : C ⊆ V) :
    IsCompact (smoothFormCompactCoreInOpen V C) := by
  rw [Subtype.isCompact_iff]
  simpa [smoothFormCompactCore] using
    (show IsCompact (smoothFormCompactCore V
      (smoothFormCompactCoreInOpen V C)) from by
        rw [smoothFormCompactCore_coreInOpen V C hCV]
        exact hC)

omit [T2Space M] in
/-- The ambient compact core lies in the original open set. -/
theorem smoothFormCompactCore_subset
    (U : TopologicalSpace.Opens M) (K : Set U) :
    smoothFormCompactCore U K ⊆ U := by
  rintro _ ⟨x, _hx, rfl⟩
  exact x.2

/-- A compact core in an open submanifold has closed ambient image. -/
theorem smoothFormCompactCore_isClosed
    (U : TopologicalSpace.Opens M) (K : Set U) (hK : IsCompact K) :
    IsClosed (smoothFormCompactCore U K) := by
  exact (hK.image continuous_subtype_val).isClosed

/-- The ambient open set complementary to a compact support core. -/
def smoothFormCompactExteriorOpen
    (U : TopologicalSpace.Opens M) (K : Set U) (hK : IsCompact K) :
    TopologicalSpace.Opens M :=
  ⟨(smoothFormCompactCore U K)ᶜ,
    (smoothFormCompactCore_isClosed U K hK).isOpen_compl⟩

/-- An open submanifold and the exterior of one of its compact subsets cover
the ambient manifold. -/
theorem smoothFormCompact_open_cover
    (U : TopologicalSpace.Opens M) (K : Set U) (hK : IsCompact K) :
    U ⊔ smoothFormCompactExteriorOpen U K hK = ⊤ := by
  ext x
  change (x ∈ U ∨ x ∈ (smoothFormCompactCore U K)ᶜ) ↔ True
  rw [iff_true]
  by_cases hxU : x ∈ U
  · exact Or.inl hxU
  · exact Or.inr fun hxcore ↦
      hxU (smoothFormCompactCore_subset U K hxcore)

/-- A local form supported in a compact core restricts to zero on the
overlap with the core's exterior. -/
theorem smoothFormCompact_overlap_eq_zero
    (U : TopologicalSpace.Opens M) (K : Set U) (hK : IsCompact K)
    {n : ℕ} (alpha : SmoothForms (I := I) (M := U) ℝ n)
    (hzero : ∀ x : U, x ∉ K → alpha.toFun x = 0) :
    restrictSmoothFormsOfLE (I := I) (A := ℝ)
        (W := (U ⊓ smoothFormCompactExteriorOpen U K hK :
          TopologicalSpace.Opens M))
        (V := U) inf_le_left n alpha = 0 := by
  apply DifferentialForm.ext
  intro x
  let xU : U := TopologicalSpace.Opens.inclusion inf_le_left x
  have hxUK : xU ∉ K := by
    intro hxK
    have hxcore : (x : M) ∈ smoothFormCompactCore U K := by
      refine ⟨xU, hxK, ?_⟩
      rfl
    exact x.2.2 hxcore
  have hz := hzero xU hxUK
  simp only [restrictSmoothFormsOfLE]
  change (alpha.toFun xU).compContinuousLinearMap _ = 0
  rw [hz]
  rfl

/-- The local form and zero satisfy the Mayer--Vietoris overlap condition. -/
theorem smoothFormCompact_mayerVietorisDifference_eq_zero
    (U : TopologicalSpace.Opens M) (K : Set U) (hK : IsCompact K)
    {n : ℕ} (alpha : SmoothForms (I := I) (M := U) ℝ n)
    (hzero : ∀ x : U, x ∉ K → alpha.toFun x = 0) :
    deRhamMayerVietorisSmoothDifference (I := I) (A := ℝ)
      U (smoothFormCompactExteriorOpen U K hK) n (alpha, 0) = 0 := by
  rw [deRhamMayerVietorisSmoothDifference]
  simp only [map_zero, sub_zero]
  exact smoothFormCompact_overlap_eq_zero I U K hK alpha hzero

/-- Extend a smooth form supported in a compact subset of an open
submanifold by zero to the ambient manifold. -/
noncomputable def smoothFormCompactZeroExtension
    (U : TopologicalSpace.Opens M) (K : Set U) (hK : IsCompact K)
    {n : ℕ} (alpha : SmoothForms (I := I) (M := U) ℝ n)
    (hzero : ∀ x : U, x ∉ K → alpha.toFun x = 0) :
    SmoothForms (I := I) (M := M) ℝ n :=
  smoothFormsTwoOpenGlue (I := I) (A := ℝ)
    U (smoothFormCompactExteriorOpen U K hK)
    (smoothFormCompact_open_cover U K hK) alpha 0
    (smoothFormCompact_mayerVietorisDifference_eq_zero
      I U K hK alpha hzero)

/-- Extension by zero restricts to the original form on its open domain. -/
theorem smoothFormCompactZeroExtension_restrict
    (U : TopologicalSpace.Opens M) (K : Set U) (hK : IsCompact K)
    {n : ℕ} (alpha : SmoothForms (I := I) (M := U) ℝ n)
    (hzero : ∀ x : U, x ∉ K → alpha.toFun x = 0) :
    restrictSmoothFormsToOpen (I := I) (A := ℝ) U n
        (smoothFormCompactZeroExtension I U K hK alpha hzero) = alpha := by
  rw [smoothFormCompactZeroExtension,
    restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_left]

/-- Extension by zero restricts to zero outside its compact core. -/
theorem smoothFormCompactZeroExtension_restrict_exterior
    (U : TopologicalSpace.Opens M) (K : Set U) (hK : IsCompact K)
    {n : ℕ} (alpha : SmoothForms (I := I) (M := U) ℝ n)
    (hzero : ∀ x : U, x ∉ K → alpha.toFun x = 0) :
    restrictSmoothFormsToOpen (I := I) (A := ℝ)
        (smoothFormCompactExteriorOpen U K hK) n
        (smoothFormCompactZeroExtension I U K hK alpha hzero) = 0 := by
  rw [smoothFormCompactZeroExtension,
    restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_right]

/-- Extension by zero vanishes pointwise outside the ambient image of its
compact support core. -/
theorem smoothFormCompactZeroExtension_toFun_eq_zero_of_not_mem_core
    (U : TopologicalSpace.Opens M) (K : Set U) (hK : IsCompact K)
    {n : ℕ} (alpha : SmoothForms (I := I) (M := U) ℝ n)
    (hzero : ∀ x : U, x ∉ K → alpha.toFun x = 0)
    (x : M) (hx : x ∉ smoothFormCompactCore U K) :
    (smoothFormCompactZeroExtension I U K hK alpha hzero).toFun x = 0 := by
  by_cases hxU : x ∈ U
  · let xU : U := ⟨x, hxU⟩
    have hxK : xU ∉ K := by
      intro hxK
      exact hx ⟨xU, hxK, rfl⟩
    have hres := smoothFormCompactZeroExtension_restrict
      I U K hK alpha hzero
    have hpoint := congrArg
      (fun omega : SmoothForms (I := I) (M := U) ℝ n => omega.toFun xU)
      hres
    change
      ((smoothFormCompactZeroExtension I U K hK alpha hzero).toFun x).compContinuousLinearMap
            (mfderiv I I (fun y : U => (y : M)) xU) =
        alpha.toFun xU at hpoint
    rw [hzero xU hxK] at hpoint
    exact continuousAlternatingMap_compContinuousLinearMap_injective
      (mfderiv I I (fun y : U => (y : M)) xU)
      (mfderiv_subtypeVal_surjective (I := I) U xU) hpoint
  · have hxext : x ∈ smoothFormCompactExteriorOpen U K hK := hx
    exact smoothForms_eq_zero_of_restrictSmoothFormsToOpen_zero_eq_at
      (I := I) (A := ℝ) (smoothFormCompactExteriorOpen U K hK)
      (smoothFormCompactZeroExtension I U K hK alpha hzero)
      (smoothFormCompactZeroExtension_restrict_exterior
        I U K hK alpha hzero) hxext

omit [T2Space M] in
/-- Restricting an ambient form to an open submanifold preserves pointwise
vanishing. -/
theorem restrictSmoothFormsToOpen_toFun_eq_zero_of_ambient_eq_zero
    (U : TopologicalSpace.Opens M) {n : ℕ}
    (beta : SmoothForms (I := I) (M := M) ℝ n)
    (x : U) (hx : beta.toFun (x : M) = 0) :
    (restrictSmoothFormsToOpen (I := I) (A := ℝ) U n beta).toFun x = 0 := by
  change (beta.toFun (x : M)).compContinuousLinearMap _ = 0
  rw [hx]
  rfl

/-- Extending the restriction of an ambient form by zero recovers the form
when its support lies in the chosen compact core. -/
theorem smoothFormCompactZeroExtension_restrict_eq_self
    (U : TopologicalSpace.Opens M) (K : Set U) (hK : IsCompact K)
    {n : ℕ} (beta : SmoothForms (I := I) (M := M) ℝ n)
    (hzero : ∀ x : M, x ∉ smoothFormCompactCore U K → beta.toFun x = 0) :
    smoothFormCompactZeroExtension I U K hK
        (restrictSmoothFormsToOpen (I := I) (A := ℝ) U n beta)
        (by
          intro x hx
          apply restrictSmoothFormsToOpen_toFun_eq_zero_of_ambient_eq_zero I
          apply hzero
          intro hcore
          obtain ⟨y, hyK, hyx⟩ := hcore
          apply hx
          have : y = x := Subtype.ext hyx
          simpa [this] using hyK) = beta := by
  let V := smoothFormCompactExteriorOpen U K hK
  apply sub_eq_zero.mp
  apply smoothForms_eq_zero_of_restrictions_eq_zero
    (I := I) (A := ℝ) U V (smoothFormCompact_open_cover U K hK) n
  · rw [map_sub, smoothFormCompactZeroExtension_restrict]
    exact sub_self _
  · rw [map_sub, smoothFormCompactZeroExtension_restrict_exterior]
    apply sub_eq_zero.mpr
    apply DifferentialForm.ext
    intro x
    have hxzero : beta.toFun (x : M) = 0 := hzero (x : M) x.2
    symm
    exact restrictSmoothFormsToOpen_toFun_eq_zero_of_ambient_eq_zero
      I V beta x hxzero

/-- Compactly supported extension by zero respects equality of the local
forms. -/
theorem smoothFormCompactZeroExtension_congr
    (U : TopologicalSpace.Opens M) (K : Set U) (hK : IsCompact K)
    {n : ℕ} {alpha beta : SmoothForms (I := I) (M := U) ℝ n}
    (h : alpha = beta)
    (halpha : ∀ x : U, x ∉ K → alpha.toFun x = 0)
    (hbeta : ∀ x : U, x ∉ K → beta.toFun x = 0) :
    smoothFormCompactZeroExtension I U K hK alpha halpha =
      smoothFormCompactZeroExtension I U K hK beta hbeta := by
  subst beta
  rfl

/-- Compactly supported extension by zero preserves subtraction. -/
theorem smoothFormCompactZeroExtension_sub
    (U : TopologicalSpace.Opens M) (K : Set U) (hK : IsCompact K)
    {n : ℕ} (alpha beta : SmoothForms (I := I) (M := U) ℝ n)
    (halpha : ∀ x : U, x ∉ K → alpha.toFun x = 0)
    (hbeta : ∀ x : U, x ∉ K → beta.toFun x = 0) :
    smoothFormCompactZeroExtension I U K hK (alpha - beta)
        (fun x hx ↦ by
          change alpha.toFun x - beta.toFun x = 0
          rw [halpha x hx, hbeta x hx, sub_self]) =
      smoothFormCompactZeroExtension I U K hK alpha halpha -
        smoothFormCompactZeroExtension I U K hK beta hbeta := by
  let V := smoothFormCompactExteriorOpen U K hK
  apply sub_eq_zero.mp
  apply smoothForms_eq_zero_of_restrictions_eq_zero
    (I := I) (A := ℝ) U V (smoothFormCompact_open_cover U K hK) n
  · rw [map_sub, map_sub,
      smoothFormCompactZeroExtension_restrict,
      smoothFormCompactZeroExtension_restrict,
      smoothFormCompactZeroExtension_restrict]
    abel
  · rw [map_sub, map_sub,
      smoothFormCompactZeroExtension_restrict_exterior,
      smoothFormCompactZeroExtension_restrict_exterior,
      smoothFormCompactZeroExtension_restrict_exterior]
    simp

/-- The exterior derivative of a smooth form supported in a compact core also
vanishes outside that core. -/
theorem deRhamDifferential_toFun_eq_zero_of_not_mem_compact
    (U : TopologicalSpace.Opens M) (K : Set U) (hK : IsCompact K)
    {n : ℕ} (alpha : SmoothForms (I := I) (M := U) ℝ n)
    (hzero : ∀ x : U, x ∉ K → alpha.toFun x = 0)
    (x : U) (hx : x ∉ K) :
    (deRhamDifferential (I := I) (M := U) (A := ℝ) n alpha).toFun x = 0 := by
  have hxcompl : x ∈ Kᶜ := hx
  have hlocal : ∀ᶠ y in 𝓝 x,
      alpha.toFun y = (0 : SmoothForms (I := I) (M := U) ℝ n).toFun y := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxcompl] with y hy
    simp [hzero y hy]
  rw [deRhamDifferential_toFun_eq_of_eventuallyEq
    (I := I) alpha 0 hlocal]
  have hd0 : deRhamDifferential (I := I) (M := U) (A := ℝ) n
      (0 : SmoothForms (I := I) (M := U) ℝ n) = 0 :=
    LinearMap.map_zero _
  simpa using congrArg (fun theta ↦ theta.toFun x) hd0

/-- Exterior differentiation commutes with compactly supported extension by
zero from an open submanifold. -/
theorem deRhamDifferential_smoothFormCompactZeroExtension
    (U : TopologicalSpace.Opens M) (K : Set U) (hK : IsCompact K)
    {n : ℕ} (alpha : SmoothForms (I := I) (M := U) ℝ n)
    (hzero : ∀ x : U, x ∉ K → alpha.toFun x = 0) :
    deRhamDifferential (I := I) (M := M) (A := ℝ) n
        (smoothFormCompactZeroExtension I U K hK alpha hzero) =
      smoothFormCompactZeroExtension I U K hK
        (deRhamDifferential (I := I) (M := U) (A := ℝ) n alpha)
        (deRhamDifferential_toFun_eq_zero_of_not_mem_compact
          I U K hK alpha hzero) := by
  let V := smoothFormCompactExteriorOpen U K hK
  let lhs := deRhamDifferential (I := I) (M := M) (A := ℝ) n
    (smoothFormCompactZeroExtension I U K hK alpha hzero)
  let rhs := smoothFormCompactZeroExtension I U K hK
    (deRhamDifferential (I := I) (M := U) (A := ℝ) n alpha)
    (deRhamDifferential_toFun_eq_zero_of_not_mem_compact
      I U K hK alpha hzero)
  have hsub : lhs - rhs = 0 := by
    apply smoothForms_eq_zero_of_restrictions_eq_zero
      (I := I) (A := ℝ) U V (smoothFormCompact_open_cover U K hK) (n + 1)
    · change restrictSmoothFormsToOpen (I := I) (A := ℝ) U (n + 1)
          (lhs - rhs) = 0
      rw [map_sub]
      change
        restrictSmoothFormsToOpen (I := I) (A := ℝ) U (n + 1)
            (deRhamDifferential (I := I) (M := M) (A := ℝ) n
              (smoothFormCompactZeroExtension I U K hK alpha hzero)) -
          restrictSmoothFormsToOpen (I := I) (A := ℝ) U (n + 1) rhs = 0
      dsimp only [rhs]
      rw [← deRhamDifferential_restrictSmoothFormsToOpen,
        smoothFormCompactZeroExtension_restrict,
        smoothFormCompactZeroExtension_restrict]
      exact sub_self _
    · change restrictSmoothFormsToOpen (I := I) (A := ℝ) V (n + 1)
          (lhs - rhs) = 0
      rw [map_sub]
      change
        restrictSmoothFormsToOpen (I := I) (A := ℝ) V (n + 1)
            (deRhamDifferential (I := I) (M := M) (A := ℝ) n
              (smoothFormCompactZeroExtension I U K hK alpha hzero)) -
          restrictSmoothFormsToOpen (I := I) (A := ℝ) V (n + 1) rhs = 0
      dsimp only [rhs]
      rw [← deRhamDifferential_restrictSmoothFormsToOpen,
        smoothFormCompactZeroExtension_restrict_exterior,
        smoothFormCompactZeroExtension_restrict_exterior]
      have hd0 : deRhamDifferential (I := I) (M := V) (A := ℝ) n
          (0 : SmoothForms (I := I) (M := V) ℝ n) = 0 :=
        LinearMap.map_zero _
      simpa using hd0
  exact sub_eq_zero.mp hsub

/-! ## Locally finite sums of smooth forms -/

/-- The ordinary support of a differential form's dependent coefficient
field. -/
def smoothFormSupport {n : ℕ}
    (omega : SmoothForms (I := I) (M := M) ℝ n) : Set M :=
  {x | omega.toFun x ≠ 0}

/-- The closed support of a differential form. -/
def smoothFormTSupport {n : ℕ}
    (omega : SmoothForms (I := I) (M := M) ℝ n) : Set M :=
  closure (smoothFormSupport I omega)

omit [T2Space M] in
/-- The support of the exterior derivative lies in the closed support of the
original form. -/
theorem deRhamDifferential_support_subset_tsupport
    {n : ℕ} (omega : SmoothForms (I := I) (M := M) ℝ n) :
    smoothFormSupport I
        (deRhamDifferential (I := I) (M := M) (A := ℝ) n omega) ⊆
      smoothFormTSupport I omega := by
  intro x hx
  by_contra hxSupport
  have hlocal : ∀ᶠ y in nhds x,
      omega.toFun y = (0 : SmoothForms (I := I) (M := M) ℝ n).toFun y := by
    filter_upwards [IsClosed.compl_mem_nhds isClosed_closure hxSupport] with y hy
    change omega.toFun y = 0
    by_contra hne
    exact hy (subset_closure hne)
  have hd := deRhamDifferential_toFun_eq_of_eventuallyEq
    (I := I) omega 0 hlocal
  apply hx
  rw [hd]
  have hd0 : deRhamDifferential (I := I) (M := M) (A := ℝ) n
      (0 : SmoothForms (I := I) (M := M) ℝ n) = 0 :=
    LinearMap.map_zero _
  simpa using congrArg (fun eta ↦ eta.toFun x) hd0

omit [IsManifold I ∞ M] [T2Space M] in
/-- Evaluation of a finite sum of smooth forms is the finite sum of their
pointwise values. -/
theorem smoothForms_finset_sum_toFun
    {n : ℕ} (omega : ι → SmoothForms (I := I) (M := M) ℝ n)
    (s : Finset ι) (x : M) :
    (∑ i ∈ s, omega i).toFun x = ∑ i ∈ s, (omega i).toFun x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      change (omega i).toFun x + (∑ j ∈ s, omega j).toFun x = _
      rw [ih]

/-- The pointwise locally finite sum of smooth differential forms. -/
noncomputable def smoothFormsLocallyFiniteFinsum
    {n : ℕ} (omega : ι → SmoothForms (I := I) (M := M) ℝ n)
    (hloc : LocallyFinite (fun i ↦ smoothFormTSupport I (omega i))) :
    SmoothForms (I := I) (M := M) ℝ n where
  toFun := fun x ↦ ∑ᶠ i, (omega i).toFun x
  isContMDiff := by
    apply isContMDiffForm_of_locally_eventuallyEq_smoothForms (I := I)
    intro x
    rcases hloc x with ⟨U, hU, hfin⟩
    let s : Finset ι := hfin.toFinset
    have hs : ∀ᶠ y in nhds x,
        {i | (omega i).toFun y ≠ 0} ⊆ s := by
      filter_upwards [hU] with y hy i hi
      rw [show s = hfin.toFinset by rfl, hfin.coe_toFinset]
      exact ⟨y, subset_closure hi, hy⟩
    refine ⟨(∑ i ∈ s, omega i), ?_⟩
    filter_upwards [hs] with y hy
    rw [finsum_eq_sum_of_support_subset _ hy]
    exact (smoothForms_finset_sum_toFun I omega s y).symm

omit [T2Space M] in
@[simp]
theorem smoothFormsLocallyFiniteFinsum_toFun
    {n : ℕ} (omega : ι → SmoothForms (I := I) (M := M) ℝ n)
    (hloc : LocallyFinite (fun i ↦ smoothFormTSupport I (omega i))) (x : M) :
    (smoothFormsLocallyFiniteFinsum I omega hloc).toFun x =
      ∑ᶠ i, (omega i).toFun x :=
  rfl

omit [T2Space M] in
/-- Exterior differentiation commutes with a locally finite sum of smooth
forms. -/
theorem deRhamDifferential_smoothFormsLocallyFiniteFinsum
    {n : ℕ} (omega : ι → SmoothForms (I := I) (M := M) ℝ n)
    (hloc : LocallyFinite (fun i ↦ smoothFormTSupport I (omega i))) :
    deRhamDifferential (I := I) (M := M) (A := ℝ) n
        (smoothFormsLocallyFiniteFinsum I omega hloc) =
      smoothFormsLocallyFiniteFinsum I
        (fun i ↦ deRhamDifferential (I := I) (M := M) (A := ℝ) n (omega i))
        (hloc.subset (fun i ↦
          (closure_minimal
            (deRhamDifferential_support_subset_tsupport I (omega i))
            isClosed_closure))) := by
  let hlocD : LocallyFinite (fun i ↦ smoothFormTSupport I
      (deRhamDifferential (I := I) (M := M) (A := ℝ) n (omega i))) :=
    hloc.subset (fun i ↦
      (closure_minimal
        (deRhamDifferential_support_subset_tsupport I (omega i))
        isClosed_closure))
  apply DifferentialForm.ext
  intro x
  rcases hloc x with ⟨U, hU, hfin⟩
  let s : Finset ι := hfin.toFinset
  have hs : ∀ᶠ y in nhds x,
      {i | (omega i).toFun y ≠ 0} ⊆ s := by
    filter_upwards [hU] with y hy i hi
    rw [show s = hfin.toFinset by rfl, hfin.coe_toFinset]
    exact ⟨y, subset_closure hi, hy⟩
  let eta : SmoothForms (I := I) (M := M) ℝ n := (∑ i ∈ s, omega i)
  have hlocal : ∀ᶠ y in nhds x,
      (smoothFormsLocallyFiniteFinsum I omega hloc).toFun y = eta.toFun y := by
    filter_upwards [hs] with y hy
    change (∑ᶠ i, (omega i).toFun y) = _
    rw [finsum_eq_sum_of_support_subset _ hy]
    exact (smoothForms_finset_sum_toFun I omega s y).symm
  rw [deRhamDifferential_toFun_eq_of_eventuallyEq
    (I := I) (smoothFormsLocallyFiniteFinsum I omega hloc) eta hlocal]
  change
    (deRhamDifferential (I := I) (M := M) (A := ℝ) n eta).toFun x =
      ∑ᶠ i,
        (deRhamDifferential (I := I) (M := M) (A := ℝ) n (omega i)).toFun x
  have hsupportD : Function.support (fun i ↦
      (deRhamDifferential (I := I) (M := M) (A := ℝ) n (omega i)).toFun x) ⊆
      s := by
    intro i hi
    by_contra his
    have hzero : ∀ᶠ y in nhds x,
        (omega i).toFun y =
          (0 : SmoothForms (I := I) (M := M) ℝ n).toFun y := by
      filter_upwards [hs] with y hy
      change (omega i).toFun y = 0
      by_contra hne
      exact his (hy hne)
    have hd := deRhamDifferential_toFun_eq_of_eventuallyEq
      (I := I) (omega i) 0 hzero
    apply hi
    change
      (deRhamDifferential (I := I) (M := M) (A := ℝ) n (omega i)).toFun x = 0
    rw [hd]
    have hd0 : deRhamDifferential (I := I) (M := M) (A := ℝ) n
        (0 : SmoothForms (I := I) (M := M) ℝ n) = 0 :=
      LinearMap.map_zero _
    have hd0x := congrArg (fun theta ↦ theta.toFun x) hd0
    exact hd0x
  rw [finsum_eq_sum_of_support_subset _ hsupportD]
  have hdeta : deRhamDifferential (I := I) (M := M) (A := ℝ) n eta =
      ∑ i ∈ s,
        deRhamDifferential (I := I) (M := M) (A := ℝ) n (omega i) := by
    dsimp [eta]
    exact map_sum (deRhamDifferential (I := I) (M := M) (A := ℝ) n) _ _
  rw [hdeta]
  exact smoothForms_finset_sum_toFun I
    (fun i ↦ deRhamDifferential (I := I) (M := M) (A := ℝ) n (omega i)) s x

/-- A finite-support telescoping sum on the natural numbers. -/
theorem finsum_nat_sub_succ_eq_of_eventually_zero
    {A : Type*} [AddCommGroup A] (f : ℕ → A)
    (hf : ∃ N : ℕ, ∀ n ≥ N, f n = 0) :
    ∑ᶠ n : ℕ, (f n - f (n + 1)) = f 0 := by
  rcases hf with ⟨N, hN⟩
  have hsupp : Function.support (fun n : ℕ ↦ f n - f (n + 1)) ⊆
      Finset.range N := by
    intro n hn
    simp only [Function.mem_support] at hn
    by_contra hnrange
    have hNn : N ≤ n := Nat.le_of_not_gt (by simpa using hnrange)
    rw [hN n hNn, hN (n + 1) (hNn.trans (Nat.le_add_right n 1))] at hn
    exact hn (sub_self 0)
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [Finset.sum_range_sub']
  rw [hN N le_rfl, sub_zero]

omit [T2Space M] in
/-- A locally finite chain of primitives for successive differences gives a
primitive of its first term when the transported remainders escape every
point. -/
theorem exists_smoothForm_primitive_of_locallyFinite_telescope
    {n : ℕ}
    (beta : ℕ → SmoothForms (I := I) (M := M) ℝ (n + 1))
    (eta : ℕ → SmoothForms (I := I) (M := M) ℝ n)
    (hloc : LocallyFinite (fun k ↦ smoothFormTSupport I (eta k)))
    (hd : ∀ k : ℕ,
      deRhamDifferential (I := I) (M := M) (A := ℝ) n (eta k) =
        beta k - beta (k + 1))
    (hbeta : ∀ x : M, ∃ N : ℕ, ∀ k ≥ N, (beta k).toFun x = 0) :
    ∃ theta : SmoothForms (I := I) (M := M) ℝ n,
      deRhamDifferential (I := I) (M := M) (A := ℝ) n theta = beta 0 := by
  let theta := smoothFormsLocallyFiniteFinsum I eta hloc
  refine ⟨theta, ?_⟩
  rw [show deRhamDifferential (I := I) (M := M) (A := ℝ) n theta =
      smoothFormsLocallyFiniteFinsum I
        (fun k ↦ deRhamDifferential (I := I) (M := M) (A := ℝ) n (eta k))
        (hloc.subset (fun k ↦ closure_minimal
          (deRhamDifferential_support_subset_tsupport I (eta k))
          isClosed_closure)) by
    exact deRhamDifferential_smoothFormsLocallyFiniteFinsum I eta hloc]
  apply DifferentialForm.ext
  intro x
  rw [smoothFormsLocallyFiniteFinsum_toFun]
  have hpoint : ∀ k : ℕ,
      (deRhamDifferential (I := I) (M := M) (A := ℝ) n (eta k)).toFun x =
        (beta k).toFun x - (beta (k + 1)).toFun x := by
    intro k
    rw [hd]
    rfl
  rw [finsum_congr hpoint]
  exact finsum_nat_sub_succ_eq_of_eventually_zero
    (fun k ↦ (beta k).toFun x) (hbeta x)

/-! ## The planar compact-support calculation -/

/-! ### A canonical normalized density on an interval -/

/-- The left endpoint of the middle third of a real interval. -/
noncomputable def intervalMiddleLeft (a b : ℝ) : ℝ :=
  (2 * a + b) / 3

/-- The right endpoint of the middle third of a real interval. -/
noncomputable def intervalMiddleRight (a b : ℝ) : ℝ :=
  (a + 2 * b) / 3

/-- A smooth step whose entire transition occurs in the middle third of the
interval from `a` to `b`. -/
noncomputable def intervalMiddleStep (a b : ℝ) (x : ℝ) : ℝ :=
  Real.smoothTransition
    ((x - intervalMiddleLeft a b) /
      (intervalMiddleRight a b - intervalMiddleLeft a b))

/-- The derivative of the middle-third step.  This is the canonical density
used by the compact-support primitive. -/
noncomputable def intervalNormalizingDensity (a b : ℝ) (x : ℝ) : ℝ :=
  fderiv ℝ (intervalMiddleStep a b) x 1

/-- The middle-third step is smooth. -/
theorem intervalMiddleStep_contDiff {a b : ℝ} :
    ContDiff ℝ ∞ (intervalMiddleStep a b) := by
  unfold intervalMiddleStep
  fun_prop

/-- The canonical normalizing density is smooth. -/
theorem intervalNormalizingDensity_contDiff {a b : ℝ} :
    ContDiff ℝ ∞ (intervalNormalizingDensity a b) := by
  unfold intervalNormalizingDensity
  exact ((intervalMiddleStep_contDiff (a := a) (b := b)).fderiv_right
    (m := ∞) (by simp)).clm_apply contDiff_const

/-- The middle-third step is zero to the left of its transition. -/
theorem intervalMiddleStep_eq_zero_of_le_left {a b x : ℝ}
    (hab : a < b) (h : x ≤ intervalMiddleLeft a b) :
    intervalMiddleStep a b x = 0 := by
  unfold intervalMiddleStep
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg
  · exact sub_nonpos.2 h
  · unfold intervalMiddleLeft intervalMiddleRight
    linarith

/-- The middle-third step is one to the right of its transition. -/
theorem intervalMiddleStep_eq_one_of_right_le {a b x : ℝ}
    (hab : a < b) (h : intervalMiddleRight a b ≤ x) :
    intervalMiddleStep a b x = 1 := by
  unfold intervalMiddleStep
  apply Real.smoothTransition.one_of_one_le
  have hden : 0 < intervalMiddleRight a b - intervalMiddleLeft a b := by
    unfold intervalMiddleLeft intervalMiddleRight
    linarith
  rw [le_div_iff₀ hden]
  linarith

/-- The canonical density vanishes strictly to the left of its transition
interval. -/
theorem intervalNormalizingDensity_eq_zero_of_lt_left {a b x : ℝ}
    (hab : a < b) (hx : x < intervalMiddleLeft a b) :
    intervalNormalizingDensity a b x = 0 := by
  have heq : intervalMiddleStep a b =ᶠ[nhds x] (fun _ : ℝ ↦ 0) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact intervalMiddleStep_eq_zero_of_le_left hab hy.le
  unfold intervalNormalizingDensity
  rw [heq.fderiv_eq]
  simp

/-- The canonical density vanishes strictly to the right of its transition
interval. -/
theorem intervalNormalizingDensity_eq_zero_of_right_lt {a b x : ℝ}
    (hab : a < b) (hx : intervalMiddleRight a b < x) :
    intervalNormalizingDensity a b x = 0 := by
  have heq : intervalMiddleStep a b =ᶠ[nhds x] (fun _ : ℝ ↦ 1) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact intervalMiddleStep_eq_one_of_right_le hab hy.le
  unfold intervalNormalizingDensity
  rw [heq.fderiv_eq]
  simp

/-- The closed support of the canonical density lies in the open interval. -/
theorem intervalNormalizingDensity_tsupport_subset {a b : ℝ} (hab : a < b) :
    tsupport (intervalNormalizingDensity a b) ⊆ Ioo a b := by
  have hsupp : Function.support (intervalNormalizingDensity a b) ⊆
      Icc (intervalMiddleLeft a b) (intervalMiddleRight a b) := by
    intro x hx
    by_contra hxIcc
    simp only [mem_Icc, not_and_or, not_le] at hxIcc
    rcases hxIcc with hxleft | hxright
    · exact hx (intervalNormalizingDensity_eq_zero_of_lt_left hab hxleft)
    · exact hx (intervalNormalizingDensity_eq_zero_of_right_lt hab hxright)
  refine (closure_minimal hsupp isClosed_Icc).trans ?_
  intro x hx
  unfold intervalMiddleLeft intervalMiddleRight at hx
  constructor <;> linarith [hx.1, hx.2]

/-- The canonical density has interval integral one. -/
theorem intervalNormalizingDensity_integral_eq_one {a b : ℝ} (hab : a < b) :
    ∫ x in a..b, intervalNormalizingDensity a b x = 1 := by
  have hFTC := intervalIntegral.integral_deriv_of_contDiffOn_Icc
    (f := intervalMiddleStep a b)
    ((intervalMiddleStep_contDiff (a := a) (b := b)).of_le
      (by norm_num)).contDiffOn hab.le
  have hconvert : (∫ x in a..b, intervalNormalizingDensity a b x) =
      ∫ x in a..b, deriv (intervalMiddleStep a b) x := by
    apply intervalIntegral.integral_congr
    intro x _hx
    exact fderiv_apply_one_eq_deriv
  rw [hconvert, hFTC, intervalMiddleStep_eq_one_of_right_le hab,
    intervalMiddleStep_eq_zero_of_le_left hab]
  · norm_num
  · unfold intervalMiddleLeft
    linarith
  · unfold intervalMiddleRight
    linarith

/-- The product of the canonical densities in two coordinate intervals. -/
noncomputable def planarRectangleNormalizingDensity
    (a b c d : ℝ) (p : ℝ × ℝ) : ℝ :=
  intervalNormalizingDensity a b p.1 *
    intervalNormalizingDensity c d p.2

/-- The canonical rectangle density is smooth. -/
theorem planarRectangleNormalizingDensity_contDiff
    {a b c d : ℝ} :
    ContDiff ℝ ∞ (planarRectangleNormalizingDensity a b c d) := by
  unfold planarRectangleNormalizingDensity
  exact
    (intervalNormalizingDensity_contDiff.comp contDiff_fst).mul
      (intervalNormalizingDensity_contDiff.comp contDiff_snd)

/-- The closed support of the canonical rectangle density lies in the open
rectangle. -/
theorem planarRectangleNormalizingDensity_tsupport_subset
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    tsupport (planarRectangleNormalizingDensity a b c d) ⊆
      Set.Ioo a b ×ˢ Set.Ioo c d := by
  intro p hp
  have hpFirst : p ∈ tsupport
      (fun q : ℝ × ℝ ↦ intervalNormalizingDensity a b q.1) :=
    tsupport_mul_subset_left hp
  have hpSecond : p ∈ tsupport
      (fun q : ℝ × ℝ ↦ intervalNormalizingDensity c d q.2) :=
    tsupport_mul_subset_right hp
  have hx : p.1 ∈ tsupport (intervalNormalizingDensity a b) :=
    tsupport_comp_subset_preimage (f := Prod.fst)
      (intervalNormalizingDensity a b) continuous_fst hpFirst
  have hy : p.2 ∈ tsupport (intervalNormalizingDensity c d) :=
    tsupport_comp_subset_preimage (f := Prod.snd)
      (intervalNormalizingDensity c d) continuous_snd hpSecond
  exact ⟨intervalNormalizingDensity_tsupport_subset hab hx,
    intervalNormalizingDensity_tsupport_subset hcd hy⟩

/-- The horizontal marginal of a planar coefficient on a fixed interval. -/
def planarHorizontalMarginal (a b : ℝ) (f : ℝ × ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x in a..b, f (x, y)

/-- Every horizontal slice of the canonical rectangle density integrates to
the vertical density. -/
theorem planarHorizontalMarginal_rectangleNormalizingDensity
    {a b c d y : ℝ} (hab : a < b) :
    planarHorizontalMarginal a b
        (planarRectangleNormalizingDensity a b c d) y =
      intervalNormalizingDensity c d y := by
  unfold planarHorizontalMarginal planarRectangleNormalizingDensity
  change (∫ x in a..b,
    intervalNormalizingDensity a b x * intervalNormalizingDensity c d y) = _
  rw [intervalIntegral.integral_mul_const,
    intervalNormalizingDensity_integral_eq_one hab, one_mul]

/-- The canonical rectangle density has total iterated integral one. -/
theorem planarRectangleNormalizingDensity_total_eq_one
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ∫ y in c..d, planarHorizontalMarginal a b
        (planarRectangleNormalizingDensity a b c d) y = 1 := by
  simp_rw [planarHorizontalMarginal_rectangleNormalizingDensity hab]
  exact intervalNormalizingDensity_integral_eq_one hcd

/-- A smooth planar coefficient has a smooth horizontal marginal. -/
theorem planarHorizontalMarginal_contDiff
    {a b : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (planarHorizontalMarginal a b f) := by
  rw [← contDiffOn_univ]
  have hsmooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ f (p.2, p.1)) :=
    hf.comp (by fun_prop)
  have h := JJMath.Manifold.contDiffOn_intervalIntegral_of_contDiffOn_prod_Icc
    (E := ℝ) (F := ℝ) isOpen_univ hab hsmooth.contDiffOn
  simpa [planarHorizontalMarginal] using h

/-! ### Removing the mass of a planar density -/

/-- The total iterated integral of a coefficient over a rectangle. -/
noncomputable def planarRectangleMass
    (a b c d : ℝ) (f : ℝ × ℝ → ℝ) : ℝ :=
  ∫ y in c..d, planarHorizontalMarginal a b f y

/-- Subtract the canonical rectangle density carrying the same total mass. -/
noncomputable def planarMassTransportRemainder
    (a b c d : ℝ) (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  f p - planarRectangleMass a b c d f *
    planarRectangleNormalizingDensity a b c d p

/-- The zero-mass remainder is smooth. -/
theorem planarMassTransportRemainder_contDiff
    {a b c d : ℝ} {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (planarMassTransportRemainder a b c d f) := by
  unfold planarMassTransportRemainder
  exact hf.sub
    (contDiff_const.mul planarRectangleNormalizingDensity_contDiff)

/-- Removing the mass does not enlarge a rectangular support bound. -/
theorem planarMassTransportRemainder_tsupport_subset
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {f : ℝ × ℝ → ℝ}
    (hfrect : tsupport f ⊆ Ioo a b ×ˢ Ioo c d) :
    tsupport (planarMassTransportRemainder a b c d f) ⊆
      Ioo a b ×ˢ Ioo c d := by
  intro p hp
  have hp' : p ∈ tsupport f ∪ tsupport
      (fun q : ℝ × ℝ ↦ planarRectangleMass a b c d f *
        planarRectangleNormalizingDensity a b c d q) := by
    exact tsupport_sub f _
      (by simpa [planarMassTransportRemainder] using hp)
  rcases hp' with hpf | hpDensity
  · exact hfrect hpf
  · exact planarRectangleNormalizingDensity_tsupport_subset hab hcd
      (tsupport_mul_subset_right hpDensity)

/-- The horizontal marginal of the zero-mass remainder is the original
marginal minus the transported product density. -/
theorem planarHorizontalMarginal_massTransportRemainder
    {a b c d y : ℝ} (hab : a < b)
    {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    planarHorizontalMarginal a b
        (planarMassTransportRemainder a b c d f) y =
      planarHorizontalMarginal a b f y -
        planarRectangleMass a b c d f *
          intervalNormalizingDensity c d y := by
  have hfint : IntervalIntegrable (fun x ↦ f (x, y)) volume a b :=
    (hf.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  have hρint : IntervalIntegrable
      (intervalNormalizingDensity a b) volume a b :=
    intervalNormalizingDensity_contDiff.continuous.intervalIntegrable a b
  unfold planarHorizontalMarginal planarMassTransportRemainder
  change (∫ x in a..b,
    f (x, y) - planarRectangleMass a b c d f *
      (intervalNormalizingDensity a b x *
        intervalNormalizingDensity c d y)) = _
  rw [intervalIntegral.integral_sub hfint]
  · rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_mul_const]
    rw [intervalNormalizingDensity_integral_eq_one hab]
    ring
  · exact (hρint.mul_const _).const_mul _

/-- The mass-transport remainder has total mass zero. -/
theorem planarMassTransportRemainder_total_eq_zero
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∫ y in c..d, planarHorizontalMarginal a b
        (planarMassTransportRemainder a b c d f) y = 0 := by
  simp_rw [planarHorizontalMarginal_massTransportRemainder hab hf.continuous]
  have hfMarg : IntervalIntegrable
      (planarHorizontalMarginal a b f) volume c d :=
    (planarHorizontalMarginal_contDiff hab.le hf).continuous.intervalIntegrable c d
  have hρ : IntervalIntegrable
      (intervalNormalizingDensity c d) volume c d :=
    intervalNormalizingDensity_contDiff.continuous.intervalIntegrable c d
  rw [intervalIntegral.integral_sub hfMarg (hρ.const_mul _)]
  rw [intervalIntegral.integral_const_mul,
    intervalNormalizingDensity_integral_eq_one hcd]
  simp [planarRectangleMass]

/-! ### Moving mass into a smaller target rectangle -/

/-- The canonical interval density also integrates to one over any strictly
larger interval containing its support. -/
theorem intervalNormalizingDensity_integral_eq_one_of_outer
    {A a b B : ℝ} (hAa : A < a) (hab : a < b) (hbB : b < B) :
    ∫ x in A..B, intervalNormalizingDensity a b x = 1 := by
  have hsuppSmall : Function.support (intervalNormalizingDensity a b) ⊆
      Ioc a b := by
    exact subset_closure.trans
      ((intervalNormalizingDensity_tsupport_subset hab).trans
        (fun x hx => ⟨hx.1, hx.2.le⟩))
  have hsuppOuter : Function.support (intervalNormalizingDensity a b) ⊆
      Ioc A B := by
    exact subset_closure.trans
      ((intervalNormalizingDensity_tsupport_subset hab).trans
        (fun x hx => ⟨hAa.trans hx.1, hx.2.trans hbB |>.le⟩))
  rw [intervalIntegral.integral_eq_integral_of_support_subset hsuppOuter,
    ← intervalIntegral.integral_eq_integral_of_support_subset hsuppSmall,
    intervalNormalizingDensity_integral_eq_one hab]

/-- Integrating a target rectangle density horizontally over a larger outer
interval gives its vertical density. -/
theorem planarHorizontalMarginal_rectangleNormalizingDensity_of_outer
    {A B a b c d y : ℝ} (hAa : A < a) (hab : a < b) (hbB : b < B) :
    planarHorizontalMarginal A B
        (planarRectangleNormalizingDensity a b c d) y =
      intervalNormalizingDensity c d y := by
  unfold planarHorizontalMarginal planarRectangleNormalizingDensity
  change (∫ x in A..B,
    intervalNormalizingDensity a b x * intervalNormalizingDensity c d y) = _
  rw [intervalIntegral.integral_mul_const,
    intervalNormalizingDensity_integral_eq_one_of_outer hAa hab hbB, one_mul]

/-- A target rectangle density has total mass one when integrated over a
strictly larger outer rectangle. -/
theorem planarRectangleNormalizingDensity_total_eq_one_of_outer
    {A B C D a b c d : ℝ}
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hCc : C < c) (hcd : c < d) (hdD : d < D) :
    ∫ y in C..D, planarHorizontalMarginal A B
        (planarRectangleNormalizingDensity a b c d) y = 1 := by
  simp_rw [planarHorizontalMarginal_rectangleNormalizingDensity_of_outer
    hAa hab hbB]
  exact intervalNormalizingDensity_integral_eq_one_of_outer hCc hcd hdD

/-- Remove the mass of a coefficient in an outer rectangle and place that
mass into an independently chosen inner target rectangle. -/
noncomputable def planarMassTransportRemainderTo
    (A B C D a b c d : ℝ) (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  f p - planarRectangleMass A B C D f *
    planarRectangleNormalizingDensity a b c d p

/-- The two-rectangle mass-transport remainder is smooth. -/
theorem planarMassTransportRemainderTo_contDiff
    {A B C D a b c d : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (planarMassTransportRemainderTo A B C D a b c d f) := by
  unfold planarMassTransportRemainderTo
  exact hf.sub
    (contDiff_const.mul planarRectangleNormalizingDensity_contDiff)

/-- If both the original support and target rectangle lie in the outer
rectangle, the two-rectangle remainder remains supported there. -/
theorem planarMassTransportRemainderTo_tsupport_subset
    {A B C D a b c d : ℝ}
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hCc : C < c) (hcd : c < d) (hdD : d < D)
    {f : ℝ × ℝ → ℝ}
    (hfrect : tsupport f ⊆ Ioo A B ×ˢ Ioo C D) :
    tsupport (planarMassTransportRemainderTo A B C D a b c d f) ⊆
      Ioo A B ×ˢ Ioo C D := by
  intro p hp
  have hp' : p ∈ tsupport f ∪ tsupport
      (fun q : ℝ × ℝ ↦ planarRectangleMass A B C D f *
        planarRectangleNormalizingDensity a b c d q) := by
    exact tsupport_sub f _
      (by simpa [planarMassTransportRemainderTo] using hp)
  rcases hp' with hpf | hpDensity
  · exact hfrect hpf
  · have hpTarget := planarRectangleNormalizingDensity_tsupport_subset
      hab hcd (tsupport_mul_subset_right hpDensity)
    exact ⟨⟨hAa.trans hpTarget.1.1, hpTarget.1.2.trans hbB⟩,
      ⟨hCc.trans hpTarget.2.1, hpTarget.2.2.trans hdD⟩⟩

/-- The horizontal marginal of the two-rectangle remainder is the original
marginal minus the transported vertical density. -/
theorem planarHorizontalMarginal_massTransportRemainderTo
    {A B C D a b c d y : ℝ}
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    planarHorizontalMarginal A B
        (planarMassTransportRemainderTo A B C D a b c d f) y =
      planarHorizontalMarginal A B f y -
        planarRectangleMass A B C D f *
          intervalNormalizingDensity c d y := by
  have hfint : IntervalIntegrable (fun x ↦ f (x, y)) volume A B :=
    (hf.comp (continuous_id.prodMk continuous_const)).intervalIntegrable A B
  have hρint : IntervalIntegrable
      (intervalNormalizingDensity a b) volume A B :=
    intervalNormalizingDensity_contDiff.continuous.intervalIntegrable A B
  unfold planarHorizontalMarginal planarMassTransportRemainderTo
  change (∫ x in A..B,
    f (x, y) - planarRectangleMass A B C D f *
      (intervalNormalizingDensity a b x *
        intervalNormalizingDensity c d y)) = _
  rw [intervalIntegral.integral_sub hfint]
  · rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_mul_const]
    rw [intervalNormalizingDensity_integral_eq_one_of_outer hAa hab hbB]
    ring
  · exact (hρint.mul_const _).const_mul _

/-- Moving the mass into an inner target rectangle leaves a zero-total-mass
remainder on the outer rectangle. -/
theorem planarMassTransportRemainderTo_total_eq_zero
    {A B C D a b c d : ℝ}
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hCc : C < c) (hcd : c < d) (hdD : d < D)
    {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∫ y in C..D, planarHorizontalMarginal A B
        (planarMassTransportRemainderTo A B C D a b c d f) y = 0 := by
  have hmarginal : Continuous (planarHorizontalMarginal A B f) :=
    (planarHorizontalMarginal_contDiff
      (le_of_lt ((hAa.trans hab).trans hbB)) hf).continuous
  have hmarginalInt : IntervalIntegrable
      (planarHorizontalMarginal A B f) volume C D :=
    hmarginal.intervalIntegrable C D
  have hρint : IntervalIntegrable
      (intervalNormalizingDensity c d) volume C D :=
    intervalNormalizingDensity_contDiff.continuous.intervalIntegrable C D
  simp_rw [planarHorizontalMarginal_massTransportRemainderTo
    hAa hab hbB hf.continuous]
  rw [intervalIntegral.integral_sub hmarginalInt (hρint.const_mul _)]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalNormalizingDensity_integral_eq_one_of_outer hCc hcd hdD]
  simp [planarRectangleMass]

/-- The closed support of the horizontal marginal is contained in the
projection of the closed support of the planar coefficient. -/
theorem tsupport_planarHorizontalMarginal_subset_snd_image
    (a b : ℝ) {f : ℝ × ℝ → ℝ} (hfc : HasCompactSupport f) :
    tsupport (planarHorizontalMarginal a b f) ⊆
      Prod.snd '' tsupport f := by
  have hcompact : IsCompact (Prod.snd '' tsupport f) :=
    hfc.image continuous_snd
  apply closure_minimal _ hcompact.isClosed
  intro y hy
  by_contra hyimage
  apply hy
  unfold planarHorizontalMarginal
  have hzero : ∫ _x in a..b, (0 : ℝ) = 0 := by simp
  rw [← hzero]
  apply intervalIntegral.integral_congr
  intro x _hx
  apply image_eq_zero_of_notMem_tsupport
  intro hxy
  exact hyimage ⟨(x, y), hxy, rfl⟩

/-- A rectangular support bound descends to the horizontal marginal. -/
theorem tsupport_planarHorizontalMarginal_subset_Ioo
    (a b c d : ℝ) {f : ℝ × ℝ → ℝ}
    (hfc : HasCompactSupport f)
    (hrect : tsupport f ⊆ Set.Ioo a b ×ˢ Set.Ioo c d) :
    tsupport (planarHorizontalMarginal a b f) ⊆ Set.Ioo c d := by
  refine (tsupport_planarHorizontalMarginal_subset_snd_image a b hfc).trans ?_
  rintro y ⟨p, hp, rfl⟩
  exact (hrect hp).2

/-- Remove the horizontal marginal using a fixed density of integral one. -/
def planarZeroHorizontalMarginalAdjustment
    (a b : ℝ) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  f p - ρ p.1 * planarHorizontalMarginal a b f p.2

/-- The adjusted coefficient is smooth. -/
theorem planarZeroHorizontalMarginalAdjustment_contDiff
    {a b : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (planarZeroHorizontalMarginalAdjustment a b f ρ) := by
  unfold planarZeroHorizontalMarginalAdjustment
  exact hf.sub
    ((hρ.comp contDiff_fst).mul
      ((planarHorizontalMarginal_contDiff hab hf).comp contDiff_snd))

/-- After subtracting the normalized product density, every horizontal slice
has integral zero. -/
theorem planarZeroHorizontalMarginalAdjustment_intervalIntegral_eq_zero
    {a b : ℝ} {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hf : Continuous f) (hρ : Continuous ρ)
    (hρone : ∫ x in a..b, ρ x = 1) (y : ℝ) :
    ∫ x in a..b, planarZeroHorizontalMarginalAdjustment a b f ρ (x, y) = 0 := by
  have hfint : IntervalIntegrable (fun x ↦ f (x, y)) volume a b :=
    (hf.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  have hρint : IntervalIntegrable ρ volume a b :=
    hρ.intervalIntegrable a b
  change ∫ x in a..b,
    f (x, y) - ρ x * planarHorizontalMarginal a b f y = 0
  rw [intervalIntegral.integral_sub hfint
    (hρint.mul_const (planarHorizontalMarginal a b f y))]
  rw [intervalIntegral.integral_mul_const]
  simp [planarHorizontalMarginal, hρone]

/-- If the original coefficient and the normalizing density are supported in
the rectangle interior, so is the adjusted coefficient. -/
theorem tsupport_planarZeroHorizontalMarginalAdjustment_subset
    {a b c d : ℝ} {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hfc : HasCompactSupport f)
    (hfrect : tsupport f ⊆ Set.Ioo a b ×ˢ Set.Ioo c d)
    (hρsupport : tsupport ρ ⊆ Set.Ioo a b) :
    tsupport (planarZeroHorizontalMarginalAdjustment a b f ρ) ⊆
      Set.Ioo a b ×ˢ Set.Ioo c d := by
  intro p hp
  have hp' : p ∈ tsupport f ∪
      tsupport (fun q : ℝ × ℝ ↦
        ρ q.1 * planarHorizontalMarginal a b f q.2) := by
    exact tsupport_sub f
      (fun q : ℝ × ℝ ↦ ρ q.1 * planarHorizontalMarginal a b f q.2)
      (by simpa [planarZeroHorizontalMarginalAdjustment] using hp)
  rcases hp' with hpf | hpProduct
  · exact hfrect hpf
  · have hpρcomp : p ∈ tsupport (fun q : ℝ × ℝ ↦ ρ q.1) :=
      tsupport_mul_subset_left hpProduct
    have hpmargcomp : p ∈
        tsupport (fun q : ℝ × ℝ ↦ planarHorizontalMarginal a b f q.2) :=
      tsupport_mul_subset_right hpProduct
    have hpρ : p.1 ∈ tsupport ρ :=
      tsupport_comp_subset_preimage (f := Prod.fst) ρ continuous_fst hpρcomp
    have hpmarg : p.2 ∈ tsupport (planarHorizontalMarginal a b f) :=
      tsupport_comp_subset_preimage (f := Prod.snd)
        (planarHorizontalMarginal a b f) continuous_snd hpmargcomp
    exact ⟨hρsupport hpρ,
      tsupport_planarHorizontalMarginal_subset_Ioo a b c d hfc hfrect hpmarg⟩

/-- Integrate the zero-horizontal-marginal adjustment from the left endpoint
to the current horizontal coordinate. -/
def planarHorizontalPrimitive
    (a b : ℝ) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ x in a..p.1,
    planarZeroHorizontalMarginalAdjustment a b f ρ (x, p.2)

/-- The horizontal primitive is jointly smooth in both coordinates. -/
theorem planarHorizontalPrimitive_contDiff
    {a b : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (planarHorizontalPrimitive a b f ρ) := by
  let h : ℝ × ℝ → ℝ := planarZeroHorizontalMarginalAdjustment a b f ρ
  have hh : ContDiff ℝ ∞ h :=
    planarZeroHorizontalMarginalAdjustment_contDiff hab hf hρ
  let G : (ℝ × ℝ) × ℝ → ℝ := fun q ↦
    h ((q.1.1 - a) * q.2 + a, q.1.2)
  have hG : ContDiff ℝ ∞ G := by
    dsimp only [G]
    exact hh.comp (by fun_prop)
  have hIntegral : ContDiff ℝ ∞
      (fun p : ℝ × ℝ ↦ ∫ t in (0 : ℝ)..1, G (p, t)) := by
    rw [← contDiffOn_univ]
    exact JJMath.Manifold.contDiffOn_intervalIntegral_of_contDiffOn_prod_Icc
      (E := ℝ × ℝ) (F := ℝ) isOpen_univ zero_le_one hG.contDiffOn
  have hscaled : ContDiff ℝ ∞
      (fun p : ℝ × ℝ ↦
        (p.1 - a) * (∫ t in (0 : ℝ)..1, G (p, t))) := by
    fun_prop
  rw [show planarHorizontalPrimitive a b f ρ =
      (fun p : ℝ × ℝ ↦
        (p.1 - a) * (∫ t in (0 : ℝ)..1, G (p, t))) by
    funext p
    dsimp only [planarHorizontalPrimitive, G, h]
    symm
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (intervalIntegral.smul_integral_comp_mul_add
        (a := (0 : ℝ)) (b := 1)
        (fun x : ℝ ↦ planarZeroHorizontalMarginalAdjustment a b f ρ (x, p.2))
        (p.1 - a) a)]
  exact hscaled

/-- The horizontal derivative of the horizontal primitive is the adjusted
coefficient. -/
theorem planarHorizontalPrimitive_fderiv_fst
    {a b : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hρ : ContDiff ℝ ∞ ρ)
    (p : ℝ × ℝ) :
    fderiv ℝ (planarHorizontalPrimitive a b f ρ) p (1, 0) =
      planarZeroHorizontalMarginalAdjustment a b f ρ p := by
  let Q : ℝ × ℝ → ℝ := planarHorizontalPrimitive a b f ρ
  let h : ℝ × ℝ → ℝ := planarZeroHorizontalMarginalAdjustment a b f ρ
  have hQ : ContDiff ℝ ∞ Q :=
    planarHorizontalPrimitive_contDiff hab hf hρ
  have hh : ContDiff ℝ ∞ h :=
    planarZeroHorizontalMarginalAdjustment_contDiff hab hf hρ
  have hcurve : HasFDerivAt (fun x : ℝ ↦ (x, p.2))
      (ContinuousLinearMap.inl ℝ ℝ ℝ) p.1 :=
    hasFDerivAt_prodMk_left p.1 p.2
  have hQat : HasFDerivAt Q (fderiv ℝ Q p) p :=
    (hQ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp := hQat.comp p.1 hcurve
  have hslice : ContDiff ℝ ∞ (fun x : ℝ ↦ h (x, p.2)) :=
    hh.comp (by fun_prop)
  have hFTC : HasDerivAt
      (fun x : ℝ ↦ ∫ t in a..x, h (t, p.2)) (h p) p.1 :=
    JJMath.Uniformization.realPrimitive_hasDerivAt_of_contDiff hslice a p.1
  have hmaps := hcomp.unique hFTC
  have happ := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hmaps
  simpa [Q, h, planarHorizontalPrimitive] using happ

/-- The horizontal primitive remains compactly supported in the original
rectangle interior.  The zero horizontal marginal is what makes it vanish
again after passing the right edge of the support. -/
theorem planarHorizontalPrimitive_hasCompactSupport_and_tsupport_subset
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfrect : tsupport f ⊆ Set.Ioo a b ×ˢ Set.Ioo c d)
    (hρ : ContDiff ℝ ∞ ρ)
    (hρsupport : tsupport ρ ⊆ Set.Ioo a b)
    (hρone : ∫ x in a..b, ρ x = 1) :
    HasCompactSupport (planarHorizontalPrimitive a b f ρ) ∧
      tsupport (planarHorizontalPrimitive a b f ρ) ⊆
        Set.Ioo a b ×ˢ Set.Ioo c d := by
  let h : ℝ × ℝ → ℝ := planarZeroHorizontalMarginalAdjustment a b f ρ
  have hh : ContDiff ℝ ∞ h :=
    planarZeroHorizontalMarginalAdjustment_contDiff hab.le hf hρ
  have hhrect : tsupport h ⊆ Set.Ioo a b ×ˢ Set.Ioo c d :=
    tsupport_planarZeroHorizontalMarginalAdjustment_subset
      hfc hfrect hρsupport
  have hhc : HasCompactSupport h := by
    apply IsCompact.of_isClosed_subset
      (isCompact_Icc.prod isCompact_Icc) (isClosed_tsupport h)
    exact hhrect.trans (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  let Kx : Set ℝ := Prod.fst '' tsupport h
  let Ky : Set ℝ := Prod.snd '' tsupport h
  have hKxCompact : IsCompact Kx := hhc.image continuous_fst
  have hKyCompact : IsCompact Ky := hhc.image continuous_snd
  have hKxSubset : Kx ⊆ Set.Ioo a b := by
    rintro x ⟨p, hp, rfl⟩
    exact (hhrect hp).1
  have hKySubset : Ky ⊆ Set.Ioo c d := by
    rintro y ⟨p, hp, rfl⟩
    exact (hhrect hp).2
  rcases isCompact_subset_Ioo_exists_Ioo_subset
      hKxCompact hab hKxSubset with
    ⟨a₀, b₀, haa₀, ha₀b₀, hb₀b, hKx₀⟩
  rcases isCompact_subset_Ioo_exists_Ioo_subset
      hKyCompact hcd hKySubset with
    ⟨c₀, d₀, hcc₀, hc₀d₀, hd₀d, hKy₀⟩
  have hsupport : Function.support (planarHorizontalPrimitive a b f ρ) ⊆
      Set.Icc a₀ b₀ ×ˢ Set.Icc c₀ d₀ := by
    intro p hp
    have hybounds : p.2 ∈ Set.Icc c₀ d₀ := by
      by_contra hy
      have hyout : p.2 < c₀ ∨ d₀ < p.2 := by
        by_cases hc₀y : c₀ ≤ p.2
        · exact Or.inr (lt_of_not_ge fun hyd₀ ↦ hy ⟨hc₀y, hyd₀⟩)
        · exact Or.inl (lt_of_not_ge hc₀y)
      have hsliceZero : ∀ x : ℝ, h (x, p.2) = 0 := by
        intro x
        apply image_eq_zero_of_notMem_tsupport
        intro hxy
        have hpKy : p.2 ∈ Ky := ⟨(x, p.2), hxy, rfl⟩
        have hpIoo := hKy₀ hpKy
        rcases hyout with hylt | hygt
        · exact (not_lt_of_ge hpIoo.1.le) hylt
        · exact (not_lt_of_ge hpIoo.2.le) hygt
      apply hp
      unfold planarHorizontalPrimitive
      change ∫ x in a..p.1, h (x, p.2) = 0
      simp_rw [hsliceZero]
      simp
    have hφsmooth : ContDiff ℝ ∞ (fun x : ℝ ↦ h (x, p.2)) :=
      hh.comp (by fun_prop)
    have hφsupport : tsupport (fun x : ℝ ↦ h (x, p.2)) ⊆ Set.Ioo a₀ b₀ := by
      intro x hx
      have hxy : (x, p.2) ∈ tsupport h :=
        tsupport_comp_subset_preimage
          (f := fun x : ℝ ↦ (x, p.2)) h (by fun_prop) hx
      exact hKx₀ ⟨(x, p.2), hxy, rfl⟩
    have hφint : ∀ u v : ℝ,
        IntervalIntegrable (fun x : ℝ ↦ h (x, p.2)) volume u v :=
      fun u v ↦ hφsmooth.continuous.intervalIntegrable u v
    have hφmean : ∫ x in a..b, h (x, p.2) = 0 := by
      exact planarZeroHorizontalMarginalAdjustment_intervalIntegral_eq_zero
        hf.continuous hρ.continuous hρone p.2
    have hxbounds : p.1 ∈ Set.Icc a₀ b₀ := by
      by_contra hx
      have hxout : p.1 < a₀ ∨ b₀ < p.1 := by
        by_cases ha₀x : a₀ ≤ p.1
        · exact Or.inr (lt_of_not_ge fun hxb₀ ↦ hx ⟨ha₀x, hxb₀⟩)
        · exact Or.inl (lt_of_not_ge ha₀x)
      apply hp
      unfold planarHorizontalPrimitive
      change ∫ x in a..p.1, h (x, p.2) = 0
      rcases hxout with hxlt | hxgt
      · exact realPrimitive_eq_zero_of_le_support_left_of_tsupport_subset_Ioo
          haa₀.le hxlt.le hφsupport
      · exact realPrimitive_eq_zero_of_support_right_le_of_tsupport_subset_Ioo
          hb₀b.le hxgt.le hφsupport hφint hφmean
    exact ⟨hxbounds, hybounds⟩
  have htsupport : tsupport (planarHorizontalPrimitive a b f ρ) ⊆
      Set.Icc a₀ b₀ ×ˢ Set.Icc c₀ d₀ :=
    closure_minimal hsupport (isClosed_Icc.prod isClosed_Icc)
  constructor
  · exact IsCompact.of_isClosed_subset
      (isCompact_Icc.prod isCompact_Icc)
      (isClosed_tsupport (planarHorizontalPrimitive a b f ρ)) htsupport
  · refine htsupport.trans ?_
    rintro p ⟨hx, hy⟩
    exact ⟨⟨lt_of_lt_of_le haa₀ hx.1, lt_of_le_of_lt hx.2 hb₀b⟩,
      ⟨lt_of_lt_of_le hcc₀ hy.1, lt_of_le_of_lt hy.2 hd₀d⟩⟩

/-- Integrate the horizontal marginal in the vertical direction. -/
def planarVerticalMarginalPrimitive
    (a b c : ℝ) (f : ℝ × ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t in c..y, planarHorizontalMarginal a b f t

/-- The vertical marginal primitive is smooth. -/
theorem planarVerticalMarginalPrimitive_contDiff
    {a b c : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (planarVerticalMarginalPrimitive a b c f) := by
  exact realPrimitive_contDiff_of_contDiff
    (planarHorizontalMarginal_contDiff hab hf) c

/-- If the total iterated integral is zero, the vertical marginal primitive
is compactly supported in the vertical interval. -/
theorem planarVerticalMarginalPrimitive_hasCompactSupport_and_tsupport_subset
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfrect : tsupport f ⊆ Set.Ioo a b ×ˢ Set.Ioo c d)
    (htotal : ∫ y in c..d, planarHorizontalMarginal a b f y = 0) :
    HasCompactSupport (planarVerticalMarginalPrimitive a b c f) ∧
      tsupport (planarVerticalMarginalPrimitive a b c f) ⊆ Set.Ioo c d := by
  let g : ℝ → ℝ := planarHorizontalMarginal a b f
  have hg : ContDiff ℝ ∞ g :=
    planarHorizontalMarginal_contDiff hab.le hf
  have hgsupport : tsupport g ⊆ Set.Ioo c d :=
    tsupport_planarHorizontalMarginal_subset_Ioo a b c d hfc hfrect
  have hgc : HasCompactSupport g := by
    apply IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport g)
    exact hgsupport.trans Ioo_subset_Icc_self
  have hgint : ∀ u v : ℝ, IntervalIntegrable g volume u v :=
    fun u v ↦ hg.continuous.intervalIntegrable u v
  have hsupport :=
    realPrimitive_tsupport_subset_interior_uIcc_of_tsupport_subset_Ioo
      hcd hgc hgsupport hgint htotal
  have hsupport' : tsupport (planarVerticalMarginalPrimitive a b c f) ⊆
      Set.Ioo c d := by
    simpa [planarVerticalMarginalPrimitive, g, Set.uIcc_of_le hcd.le,
      interior_Icc] using hsupport
  constructor
  · apply IsCompact.of_isClosed_subset isCompact_Icc
      (isClosed_tsupport (planarVerticalMarginalPrimitive a b c f))
    exact hsupport'.trans Ioo_subset_Icc_self
  · exact hsupport'

/-- The coefficient of the horizontal part of the desired primitive. -/
def planarVerticalPrimitiveCoefficient
    (a b c : ℝ) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ)
    (p : ℝ × ℝ) : ℝ :=
  -(ρ p.1 * planarVerticalMarginalPrimitive a b c f p.2)

/-- The vertical correction coefficient is smooth. -/
theorem planarVerticalPrimitiveCoefficient_contDiff
    {a b c : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (planarVerticalPrimitiveCoefficient a b c f ρ) := by
  unfold planarVerticalPrimitiveCoefficient
  exact ((hρ.comp contDiff_fst).mul
    ((planarVerticalMarginalPrimitive_contDiff hab hf).comp contDiff_snd)).neg

/-- The vertical derivative of the vertical correction coefficient is minus
the product density removed from the horizontal slices. -/
theorem planarVerticalPrimitiveCoefficient_fderiv_snd
    {a b c : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hρ : ContDiff ℝ ∞ ρ)
    (p : ℝ × ℝ) :
    fderiv ℝ (planarVerticalPrimitiveCoefficient a b c f ρ) p (0, 1) =
      -ρ p.1 * planarHorizontalMarginal a b f p.2 := by
  let P : ℝ × ℝ → ℝ := planarVerticalPrimitiveCoefficient a b c f ρ
  let g : ℝ → ℝ := planarHorizontalMarginal a b f
  have hP : ContDiff ℝ ∞ P :=
    planarVerticalPrimitiveCoefficient_contDiff hab hf hρ
  have hg : ContDiff ℝ ∞ g := planarHorizontalMarginal_contDiff hab hf
  have hcurve : HasFDerivAt (fun y : ℝ ↦ (p.1, y))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) p.2 :=
    hasFDerivAt_prodMk_right p.1 p.2
  have hPat : HasFDerivAt P (fderiv ℝ P p) p :=
    (hP.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp := hPat.comp p.2 hcurve
  have hFTC : HasDerivAt
      (fun y : ℝ ↦ -ρ p.1 * (∫ t in c..y, g t))
      (-ρ p.1 * g p.2) p.2 := by
    exact (realPrimitive_hasDerivAt_of_contDiff hg c p.2).const_mul (-ρ p.1)
  have hFTC' : HasDerivAt (P ∘ fun y : ℝ ↦ (p.1, y))
      (-ρ p.1 * g p.2) p.2 := by
    simpa [P, g, planarVerticalPrimitiveCoefficient,
      planarVerticalMarginalPrimitive, Function.comp_def, neg_mul] using hFTC
  have hmaps := hcomp.unique hFTC'
  have happ := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hmaps
  simpa [P, g, planarVerticalPrimitiveCoefficient,
    planarVerticalMarginalPrimitive] using happ

/-- The vertical correction coefficient has compact support in the same
rectangle. -/
theorem planarVerticalPrimitiveCoefficient_hasCompactSupport_and_tsupport_subset
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfrect : tsupport f ⊆ Set.Ioo a b ×ˢ Set.Ioo c d)
    (hρsupport : tsupport ρ ⊆ Set.Ioo a b)
    (htotal : ∫ y in c..d, planarHorizontalMarginal a b f y = 0) :
    HasCompactSupport (planarVerticalPrimitiveCoefficient a b c f ρ) ∧
      tsupport (planarVerticalPrimitiveCoefficient a b c f ρ) ⊆
        Set.Ioo a b ×ˢ Set.Ioo c d := by
  have hH := planarVerticalMarginalPrimitive_hasCompactSupport_and_tsupport_subset
    hab hcd hf hfc hfrect htotal
  have hsupport : tsupport (planarVerticalPrimitiveCoefficient a b c f ρ) ⊆
      Set.Ioo a b ×ˢ Set.Ioo c d := by
    intro p hp
    have hpProduct : p ∈ tsupport (fun q : ℝ × ℝ ↦
        ρ q.1 * planarVerticalMarginalPrimitive a b c f q.2) := by
      change p ∈ tsupport (-(fun q : ℝ × ℝ ↦
        ρ q.1 * planarVerticalMarginalPrimitive a b c f q.2)) at hp
      rw [tsupport_neg] at hp
      exact hp
    have hpρcomp : p ∈ tsupport (fun q : ℝ × ℝ ↦ ρ q.1) :=
      tsupport_mul_subset_left
        (f := fun q : ℝ × ℝ ↦ ρ q.1)
        (g := fun q : ℝ × ℝ ↦ planarVerticalMarginalPrimitive a b c f q.2)
        hpProduct
    have hpHcomp : p ∈
        tsupport (fun q : ℝ × ℝ ↦ planarVerticalMarginalPrimitive a b c f q.2) :=
      tsupport_mul_subset_right
        (f := fun q : ℝ × ℝ ↦ ρ q.1)
        (g := fun q : ℝ × ℝ ↦ planarVerticalMarginalPrimitive a b c f q.2)
        hpProduct
    have hpρ : p.1 ∈ tsupport ρ :=
      tsupport_comp_subset_preimage (f := Prod.fst) ρ continuous_fst hpρcomp
    have hpH : p.2 ∈ tsupport (planarVerticalMarginalPrimitive a b c f) :=
      tsupport_comp_subset_preimage (f := Prod.snd)
        (planarVerticalMarginalPrimitive a b c f) continuous_snd hpHcomp
    exact ⟨hρsupport hpρ, hH.2 hpH⟩
  constructor
  · apply IsCompact.of_isClosed_subset
      (isCompact_Icc.prod isCompact_Icc)
      (isClosed_tsupport (planarVerticalPrimitiveCoefficient a b c f ρ))
    exact hsupport.trans (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  · exact hsupport

/-- The two coefficient functions satisfy the planar curl identity. -/
theorem planarCompactSupportPrimitive_curl_eq
    {a b c : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hρ : ContDiff ℝ ∞ ρ)
    (p : ℝ × ℝ) :
    fderiv ℝ (planarHorizontalPrimitive a b f ρ) p (1, 0) -
        fderiv ℝ (planarVerticalPrimitiveCoefficient a b c f ρ) p (0, 1) =
      f p := by
  rw [planarHorizontalPrimitive_fderiv_fst hab hf hρ,
    planarVerticalPrimitiveCoefficient_fderiv_snd hab hf hρ]
  unfold planarZeroHorizontalMarginalAdjustment
  ring

/-- The constant covector with coefficients (P,dx+Q,dy). -/
def planarCoordinateCovector (P Q : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  P p • ContinuousLinearMap.fst ℝ ℝ ℝ +
    Q p • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Regard the coordinate covector as a one-form coefficient. -/
def planarPrimitiveOneFormCoefficient
    (a b c : ℝ) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ) (p : ℝ × ℝ) :
    (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ (0 : Fin 1)
    (planarCoordinateCovector
      (planarVerticalPrimitiveCoefficient a b c f ρ)
      (planarHorizontalPrimitive a b f ρ) p)

/-- The coefficient field of the coordinate primitive is smooth. -/
theorem planarPrimitiveOneFormCoefficient_contDiff
    {a b c : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (planarPrimitiveOneFormCoefficient a b c f ρ) := by
  have hP := planarVerticalPrimitiveCoefficient_contDiff (c := c) hab hf hρ
  have hQ := planarHorizontalPrimitive_contDiff hab hf hρ
  unfold planarPrimitiveOneFormCoefficient planarCoordinateCovector
  exact (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := ℝ × ℝ) (F := ℝ) (0 : Fin 1)).contDiff.comp
    (by fun_prop)

/-- Under the zero-total-mass hypothesis, the full one-form coefficient is
compactly supported in the original rectangle interior. -/
theorem planarPrimitiveOneFormCoefficient_hasCompactSupport_and_tsupport_subset
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfrect : tsupport f ⊆ Set.Ioo a b ×ˢ Set.Ioo c d)
    (hρ : ContDiff ℝ ∞ ρ)
    (hρsupport : tsupport ρ ⊆ Set.Ioo a b)
    (hρone : ∫ x in a..b, ρ x = 1)
    (htotal : ∫ y in c..d, planarHorizontalMarginal a b f y = 0) :
    HasCompactSupport (planarPrimitiveOneFormCoefficient a b c f ρ) ∧
      tsupport (planarPrimitiveOneFormCoefficient a b c f ρ) ⊆
        Set.Ioo a b ×ˢ Set.Ioo c d := by
  let P : ℝ × ℝ → ℝ := planarVerticalPrimitiveCoefficient a b c f ρ
  let Q : ℝ × ℝ → ℝ := planarHorizontalPrimitive a b f ρ
  have hP := planarVerticalPrimitiveCoefficient_hasCompactSupport_and_tsupport_subset
    hab hcd hf hfc hfrect hρsupport htotal
  have hQ := planarHorizontalPrimitive_hasCompactSupport_and_tsupport_subset
    hab hcd hf hfc hfrect hρ hρsupport hρone
  have hsupport :
      Function.support (planarPrimitiveOneFormCoefficient a b c f ρ) ⊆
        tsupport P ∪ tsupport Q := by
    intro p hp
    by_contra hpUnion
    have hpP : p ∉ tsupport P := fun hp' ↦ hpUnion (Or.inl hp')
    have hpQ : p ∉ tsupport Q := fun hp' ↦ hpUnion (Or.inr hp')
    have hPzero : P p = 0 := image_eq_zero_of_notMem_tsupport hpP
    have hQzero : Q p = 0 := image_eq_zero_of_notMem_tsupport hpQ
    apply hp
    simp [planarPrimitiveOneFormCoefficient, planarCoordinateCovector,
      P, Q, hPzero, hQzero]
    exact (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := ℝ × ℝ) (F := ℝ) (0 : Fin 1)).map_zero
  have htsupport : tsupport (planarPrimitiveOneFormCoefficient a b c f ρ) ⊆
      tsupport P ∪ tsupport Q :=
    closure_minimal hsupport
      ((isClosed_tsupport P).union (isClosed_tsupport Q))
  have hrect : tsupport (planarPrimitiveOneFormCoefficient a b c f ρ) ⊆
      Set.Ioo a b ×ˢ Set.Ioo c d := by
    refine htsupport.trans ?_
    rintro p (hp | hp)
    · exact hP.2 hp
    · exact hQ.2 hp
  constructor
  · apply IsCompact.of_isClosed_subset
      (isCompact_Icc.prod isCompact_Icc)
      (isClosed_tsupport (planarPrimitiveOneFormCoefficient a b c f ρ))
    exact hrect.trans (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  · exact hrect

/-- The full coordinate plane, regarded as an open subset of itself. -/
def planarModelOpen : TopologicalSpace.Opens (ℝ × ℝ) := ⊤

/-- The compactly supported coordinate one-form produced by the rectangle
construction. -/
noncomputable def planarCompactSupportPrimitiveOneForm
    (a b c : ℝ) (hab : a ≤ b) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hρ : ContDiff ℝ ∞ ρ) :
    JJMath.Manifold.SmoothForms
      (I := modelWithCornersSelf ℝ (ℝ × ℝ)) (M := planarModelOpen) ℝ 1 where
  toFun := fun p ↦ planarPrimitiveOneFormCoefficient a b c f ρ (p : ℝ × ℝ)
  isContMDiff := by
    apply JJMath.Manifold.isContMDiffForm_modelOpen_of_contDiffOn_coeff
      (E := ℝ × ℝ) planarModelOpen 1
    refine (planarPrimitiveOneFormCoefficient_contDiff
      (c := c) hab hf hρ).contDiffOn.congr ?_
    intro x _hx
    simp [JJMath.Manifold.modelOpenFormCoeffExtension, planarModelOpen]

/-- The positively oriented coordinate basis of the plane. -/
def planarOrientedBasis : Fin 2 → ℝ × ℝ
  | 0 => (1, 0)
  | 1 => (0, 1)

@[simp]
theorem planarPrimitiveOneFormCoefficient_removeNth_zero
    (a b c : ℝ) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ) (p : ℝ × ℝ) :
    planarPrimitiveOneFormCoefficient a b c f ρ p
        (Fin.removeNth (0 : Fin 2) planarOrientedBasis) =
      planarHorizontalPrimitive a b f ρ p := by
  have htail : Fin.tail planarOrientedBasis =
      (fun _ : Fin 1 ↦ ((0, 1) : ℝ × ℝ)) := by
    funext i
    fin_cases i
    rfl
  rw [show Fin.removeNth (0 : Fin 2) planarOrientedBasis =
      Fin.tail planarOrientedBasis by rfl, htail]
  change planarCoordinateCovector
      (planarVerticalPrimitiveCoefficient a b c f ρ)
      (planarHorizontalPrimitive a b f ρ) p (0, 1) = _
  simp [planarCoordinateCovector]

@[simp]
theorem planarPrimitiveOneFormCoefficient_removeNth_one
    (a b c : ℝ) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ) (p : ℝ × ℝ) :
    planarPrimitiveOneFormCoefficient a b c f ρ p
        (Fin.removeNth (1 : Fin 2) planarOrientedBasis) =
      planarVerticalPrimitiveCoefficient a b c f ρ p := by
  have hremove : Fin.removeNth (1 : Fin 2) planarOrientedBasis =
      (fun _ : Fin 1 ↦ ((1, 0) : ℝ × ℝ)) := by
    funext i
    fin_cases i
    rfl
  rw [hremove]
  change planarCoordinateCovector
      (planarVerticalPrimitiveCoefficient a b c f ρ)
      (planarHorizontalPrimitive a b f ρ) p (1, 0) = _
  simp [planarCoordinateCovector]

/-- Evaluating the exterior derivative of the coordinate primitive on the
oriented basis recovers the original planar coefficient. -/
theorem deRhamDifferential_planarCompactSupportPrimitiveOneForm_apply_basis
    {a b c : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hρ : ContDiff ℝ ∞ ρ)
    (p : planarModelOpen) :
    (JJMath.Manifold.deRhamDifferential
        (I := modelWithCornersSelf ℝ (ℝ × ℝ))
        (M := planarModelOpen) (A := ℝ) 1
        (planarCompactSupportPrimitiveOneForm a b c hab f ρ hf hρ)).toFun p
        planarOrientedBasis = f (p : ℝ × ℝ) := by
  rw [JJMath.Manifold.deRhamDifferential_modelOpen_toFun]
  have hcoeff :
      JJMath.Manifold.modelOpenFormCoeffExtension
          (E := ℝ × ℝ) planarModelOpen 1
          (fun y ↦ JJMath.Manifold.smoothFormModelCoeff
            (E := ℝ × ℝ) planarModelOpen 1
              (planarCompactSupportPrimitiveOneForm a b c hab f ρ hf hρ) y) =
        planarPrimitiveOneFormCoefficient a b c f ρ := by
    funext x
    simp [JJMath.Manifold.modelOpenFormCoeffExtension,
      JJMath.Manifold.smoothFormModelCoeff, planarModelOpen,
      planarCompactSupportPrimitiveOneForm]
  rw [hcoeff]
  change
    extDerivWithin (planarPrimitiveOneFormCoefficient a b c f ρ)
      (planarModelOpen : Set (ℝ × ℝ))
        (p : ℝ × ℝ) planarOrientedBasis = f (p : ℝ × ℝ)
  change
    extDerivWithin (planarPrimitiveOneFormCoefficient a b c f ρ)
      Set.univ (p : ℝ × ℝ) planarOrientedBasis = f (p : ℝ × ℝ)
  rw [extDerivWithin_univ]
  rw [extDeriv_apply
    ((planarPrimitiveOneFormCoefficient_contDiff
      (c := c) hab hf hρ).differentiable (by simp)).differentiableAt]
  rw [Fin.sum_univ_two]
  have hzero :
      (fun x : ℝ × ℝ ↦
        planarPrimitiveOneFormCoefficient a b c f ρ x
          (Fin.removeNth (0 : Fin 2) planarOrientedBasis)) =
        planarHorizontalPrimitive a b f ρ := by
    funext x
    exact planarPrimitiveOneFormCoefficient_removeNth_zero a b c f ρ x
  have hone :
      (fun x : ℝ × ℝ ↦
        planarPrimitiveOneFormCoefficient a b c f ρ x
          (Fin.removeNth (1 : Fin 2) planarOrientedBasis)) =
        planarVerticalPrimitiveCoefficient a b c f ρ := by
    funext x
    exact planarPrimitiveOneFormCoefficient_removeNth_one a b c f ρ x
  rw [hzero, hone]
  norm_num [planarOrientedBasis]
  change
    fderiv ℝ (planarHorizontalPrimitive a b f ρ) (p : ℝ × ℝ) (1, 0) -
      fderiv ℝ (planarVerticalPrimitiveCoefficient a b c f ρ)
        (p : ℝ × ℝ) (0, 1) = f (p : ℝ × ℝ)
  exact planarCompactSupportPrimitive_curl_eq hab hf hρ (p : ℝ × ℝ)

/-! ## Complex-coordinate wrapper -/

/-- The planar primitive covector written on the complex coordinate plane. -/
def complexPlanarPrimitiveCovector
    (a b c : ℝ) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ) (z : ℂ) :
    ℂ →L[ℝ] ℝ :=
  planarVerticalPrimitiveCoefficient a b c f ρ (Complex.equivRealProdCLM z) •
      Complex.reCLM +
    planarHorizontalPrimitive a b f ρ (Complex.equivRealProdCLM z) •
      Complex.imCLM

/-- Regard the complex-coordinate covector as a one-form coefficient. -/
def complexPlanarPrimitiveOneFormCoefficient
    (a b c : ℝ) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ) (z : ℂ) :
    ℂ [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℝ (0 : Fin 1)
    (complexPlanarPrimitiveCovector a b c f ρ z)

/-- The complex-coordinate coefficient field is smooth. -/
theorem complexPlanarPrimitiveOneFormCoefficient_contDiff
    {a b c : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (complexPlanarPrimitiveOneFormCoefficient a b c f ρ) := by
  have hP := planarVerticalPrimitiveCoefficient_contDiff (c := c) hab hf hρ
  have hQ := planarHorizontalPrimitive_contDiff hab hf hρ
  unfold complexPlanarPrimitiveOneFormCoefficient complexPlanarPrimitiveCovector
  exact (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := ℂ) (F := ℝ) (0 : Fin 1)).contDiff.comp
    (by fun_prop)

/-- The complex-coordinate one-form coefficient has compact support in the
inverse image of the original rectangle. -/
theorem complexPlanarPrimitiveOneFormCoefficient_hasCompactSupport_and_tsupport_subset
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfrect : tsupport f ⊆ Set.Ioo a b ×ˢ Set.Ioo c d)
    (hρ : ContDiff ℝ ∞ ρ)
    (hρsupport : tsupport ρ ⊆ Set.Ioo a b)
    (hρone : ∫ x in a..b, ρ x = 1)
    (htotal : ∫ y in c..d, planarHorizontalMarginal a b f y = 0) :
    HasCompactSupport (complexPlanarPrimitiveOneFormCoefficient a b c f ρ) ∧
      tsupport (complexPlanarPrimitiveOneFormCoefficient a b c f ρ) ⊆
        Complex.equivRealProdCLM ⁻¹' (Set.Ioo a b ×ˢ Set.Ioo c d) := by
  let P : ℝ × ℝ → ℝ := planarVerticalPrimitiveCoefficient a b c f ρ
  let Q : ℝ × ℝ → ℝ := planarHorizontalPrimitive a b f ρ
  have hP := planarVerticalPrimitiveCoefficient_hasCompactSupport_and_tsupport_subset
    hab hcd hf hfc hfrect hρsupport htotal
  have hQ := planarHorizontalPrimitive_hasCompactSupport_and_tsupport_subset
    hab hcd hf hfc hfrect hρ hρsupport hρone
  let KP : Set ℂ := Complex.equivRealProdCLM ⁻¹' tsupport P
  let KQ : Set ℂ := Complex.equivRealProdCLM ⁻¹' tsupport Q
  have hsupport :
      Function.support (complexPlanarPrimitiveOneFormCoefficient a b c f ρ) ⊆
        KP ∪ KQ := by
    intro z hz
    by_contra hzUnion
    have hzP : z ∉ KP := fun hz' ↦ hzUnion (Or.inl hz')
    have hzQ : z ∉ KQ := fun hz' ↦ hzUnion (Or.inr hz')
    have hPzero : P (Complex.equivRealProdCLM z) = 0 :=
      image_eq_zero_of_notMem_tsupport hzP
    have hQzero : Q (Complex.equivRealProdCLM z) = 0 :=
      image_eq_zero_of_notMem_tsupport hzQ
    have hPzero' :
        planarVerticalPrimitiveCoefficient a b c f ρ (z.re, z.im) = 0 := by
      simpa [P] using hPzero
    have hQzero' : planarHorizontalPrimitive a b f ρ (z.re, z.im) = 0 := by
      simpa [Q] using hQzero
    apply hz
    simp [complexPlanarPrimitiveOneFormCoefficient,
      complexPlanarPrimitiveCovector, hPzero', hQzero']
    exact (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := ℂ) (F := ℝ) (0 : Fin 1)).map_zero
  have hclosedP : IsClosed KP :=
    (isClosed_tsupport P).preimage Complex.equivRealProdCLM.continuous
  have hclosedQ : IsClosed KQ :=
    (isClosed_tsupport Q).preimage Complex.equivRealProdCLM.continuous
  have htsupport : tsupport (complexPlanarPrimitiveOneFormCoefficient a b c f ρ) ⊆
      KP ∪ KQ := closure_minimal hsupport (hclosedP.union hclosedQ)
  have hrect : tsupport (complexPlanarPrimitiveOneFormCoefficient a b c f ρ) ⊆
      Complex.equivRealProdCLM ⁻¹' (Set.Ioo a b ×ˢ Set.Ioo c d) := by
    refine htsupport.trans ?_
    rintro z (hz | hz)
    · exact hP.2 hz
    · exact hQ.2 hz
  have hcompactRectangle : IsCompact
      (Complex.equivRealProdCLM ⁻¹' (Set.Icc a b ×ˢ Set.Icc c d)) :=
    Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.2
      (isCompact_Icc.prod isCompact_Icc)
  constructor
  · apply IsCompact.of_isClosed_subset hcompactRectangle
      (isClosed_tsupport (complexPlanarPrimitiveOneFormCoefficient a b c f ρ))
    exact hrect.trans (preimage_mono
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
  · exact hrect

/-- The full complex coordinate plane as an open model subset. -/
def complexPlanarModelOpen : TopologicalSpace.Opens ℂ := ⊤

/-! ## Full-plane charts subordinate to an open set -/

/-- A smooth map whose image lies in an open set is smooth as a map to the
corresponding open submanifold. -/
theorem ContMDiff.codRestrict_open_aux
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H G M N : Type*}
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [TopologicalSpace N]
    {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ F G}
    [ChartedSpace H M] [ChartedSpace G N]
    {n : WithTop ℕ∞} {f : M → N}
    (hf : ContMDiff I J n f) (U : TopologicalSpace.Opens N)
    (hmem : ∀ x, f x ∈ U) :
    ContMDiff I J n (fun x => (⟨f x, hmem x⟩ : U)) := by
  classical
  intro x
  let qU : U := ⟨f x, hmem x⟩
  let retract : N → U := fun y =>
    if hy : y ∈ U then ⟨y, hy⟩ else qU
  have hretract : ContMDiffAt J J n retract (f x) := by
    rw [← contMDiffAt_subtype_iff (U := U) (x := qU)]
    have heq : (fun y : U => retract y) = id := by
      funext y
      simp [retract]
    rw [heq]
    exact contMDiffAt_id
  have hcomp := hretract.comp x (hf x)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [retract, hmem]

/-- The usual radial diffeomorphism from the plane onto an open ball, as a
partial diffeomorphism of the ambient plane. -/
noncomputable def complexUnivBallPartialDiffeomorph
    (c : ℂ) (r : ℝ) (hr : 0 < r) :
    PartialDiffeomorph SurfaceRealModel SurfaceRealModel ℂ ℂ ∞ where
  toPartialEquiv := (OpenPartialHomeomorph.univBall c r).toPartialEquiv
  open_source := (OpenPartialHomeomorph.univBall c r).open_source
  open_target := (OpenPartialHomeomorph.univBall c r).open_target
  contMDiffOn_toFun := by
    exact (OpenPartialHomeomorph.contDiff_univBall
      (n := (⊤ : ℕ∞))).contMDiff.contMDiffOn
  contMDiffOn_invFun := by
    rw [OpenPartialHomeomorph.univBall_target c hr]
    exact (OpenPartialHomeomorph.contDiffOn_univBall_symm
      (n := (⊤ : ℕ∞))).contMDiffOn

/-- The radial partial diffeomorphism is defined on the whole plane. -/
theorem complexUnivBallPartialDiffeomorph_source
    (c : ℂ) (r : ℝ) (hr : 0 < r) :
    (complexUnivBallPartialDiffeomorph c r hr).source = univ := by
  exact OpenPartialHomeomorph.univBall_source c r

/-- The target of the radial partial diffeomorphism is the prescribed open
ball. -/
theorem complexUnivBallPartialDiffeomorph_target
    (c : ℂ) (r : ℝ) (hr : 0 < r) :
    (complexUnivBallPartialDiffeomorph c r hr).target = Metric.ball c r := by
  exact OpenPartialHomeomorph.univBall_target c hr

/-- A partial diffeomorphism whose target is the whole complex plane induces
a diffeomorphism from its open source to the full planar model open set. -/
noncomputable def partialDiffeomorphSourceToComplexPlanarModelOpen
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (T : PartialDiffeomorph SurfaceRealModel SurfaceRealModel X ℂ ∞)
    (htarget : T.target = univ) :
    (⟨T.source, T.open_source⟩ : TopologicalSpace.Opens X) ≃ₘ⟮
      SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen := by
  classical
  let U : TopologicalSpace.Opens X := ⟨T.source, T.open_source⟩
  let equiv : U ≃ complexPlanarModelOpen :=
    { toFun := fun x => ⟨T x, trivial⟩
      invFun := fun z => ⟨T.invFun (z : ℂ), by
        apply T.map_target
        rw [htarget]
        exact mem_univ _⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact T.left_inv x.2
      right_inv := by
        intro z
        apply Subtype.ext
        apply T.right_inv
        rw [htarget]
        exact mem_univ _ }
  have htoRaw : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun x : U => T (x : X)) := by
    intro x
    have hT : ContMDiffAt SurfaceRealModel SurfaceRealModel ∞ T (x : X) :=
      T.contMDiffOn_toFun.contMDiffAt
        (T.open_source.mem_nhds x.2)
    exact hT.comp x (contMDiff_subtype_val x)
  have hto : ContMDiff SurfaceRealModel SurfaceRealModel ∞ equiv :=
    ContMDiff.codRestrict_open_aux htoRaw complexPlanarModelOpen
      (fun _ => trivial)
  have hinvRaw : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun z : complexPlanarModelOpen => T.invFun (z : ℂ)) := by
    intro z
    have hz : (z : ℂ) ∈ T.target := by
      rw [htarget]
      exact mem_univ _
    have hT : ContMDiffAt SurfaceRealModel SurfaceRealModel ∞
        T.invFun (z : ℂ) :=
      T.contMDiffOn_invFun.contMDiffAt (T.open_target.mem_nhds hz)
    exact hT.comp z (contMDiff_subtype_val z)
  have hinv : ContMDiff SurfaceRealModel SurfaceRealModel ∞ equiv.symm :=
    ContMDiff.codRestrict_open_aux hinvRaw U (fun z => by
      apply T.map_target
      rw [htarget]
      exact mem_univ _)
  exact
    { toEquiv := equiv
      contMDiff_toFun := hto
      contMDiff_invFun := hinv }

/-- Every point of an open subset of a smooth complex surface has a smaller
coordinate neighborhood, still subordinate to that open set, which is
smoothly diffeomorphic to the whole complex plane. -/
theorem exists_complexPlanarChart_subordinate
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (W : TopologicalSpace.Opens X) (x : X) (hxW : x ∈ W) :
    ∃ (U : TopologicalSpace.Opens X), x ∈ U ∧ U ≤ W ∧
      Nonempty (U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯
        complexPlanarModelOpen) := by
  classical
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have hxsource : x ∈ e.source := mem_chart_source ℂ x
  let s : Set X := e.source ∩ (W : Set X)
  have hsopen : IsOpen s := e.open_source.inter W.isOpen
  have hssource : s ⊆ e.source := inter_subset_left
  have himageOpen : IsOpen (e '' s) :=
    e.isOpen_image_of_subset_source hsopen hssource
  have hximage : e x ∈ e '' s := ⟨x, ⟨hxsource, hxW⟩, rfl⟩
  rcases Metric.isOpen_iff.1 himageOpen (e x) hximage with
    ⟨r, hr, hball⟩
  let chartPartial : PartialDiffeomorph
      SurfaceRealModel SurfaceRealModel X ℂ ∞ :=
    partialDiffeomorphOfMemMaximalAtlas e
      (IsManifold.chart_mem_maximalAtlas
        (I := SurfaceRealModel) (n := ∞) x)
  let ballPartial := complexUnivBallPartialDiffeomorph (e x) r hr
  let T : PartialDiffeomorph SurfaceRealModel SurfaceRealModel X ℂ ∞ :=
    JJMath.Manifold.PartialDiffeomorph.trans chartPartial ballPartial.symm
  have hTtarget : T.target = univ := by
    rw [show T.target = ballPartial.symm.target ∩
        ballPartial.symm.invFun ⁻¹' chartPartial.target from
      PartialEquiv.trans_target chartPartial.toPartialEquiv
        ballPartial.symm.toPartialEquiv]
    rw [show ballPartial.symm.target = univ by
      exact complexUnivBallPartialDiffeomorph_source (e x) r hr]
    ext z
    simp only [mem_inter_iff, mem_univ, true_and]
    rw [iff_true]
    have hzball : ballPartial (z : ℂ) ∈ Metric.ball (e x) r := by
      rw [← complexUnivBallPartialDiffeomorph_target (e x) r hr]
      apply ballPartial.map_source
      rw [complexUnivBallPartialDiffeomorph_source (e x) r hr]
      exact mem_univ _
    obtain ⟨y, hyS, hyEq⟩ := hball hzball
    change ballPartial (z : ℂ) ∈ chartPartial.target
    change ballPartial (z : ℂ) ∈ e.target
    rw [← hyEq]
    exact e.map_source hyS.1
  let U : TopologicalSpace.Opens X := ⟨T.source, T.open_source⟩
  have hxU : x ∈ U := by
    change x ∈ T.source
    rw [show T.source = chartPartial.source ∩
        chartPartial ⁻¹' ballPartial.symm.source from
      PartialEquiv.trans_source chartPartial.toPartialEquiv
        ballPartial.symm.toPartialEquiv]
    refine ⟨hxsource, ?_⟩
    change e x ∈ ballPartial.target
    rw [complexUnivBallPartialDiffeomorph_target (e x) r hr]
    exact Metric.mem_ball_self hr
  have hUW : U ≤ W := by
    intro y hy
    change y ∈ T.source at hy
    rw [show T.source = chartPartial.source ∩
        chartPartial ⁻¹' ballPartial.symm.source from
      PartialEquiv.trans_source chartPartial.toPartialEquiv
        ballPartial.symm.toPartialEquiv] at hy
    have hyball : e y ∈ Metric.ball (e x) r := by
      have hytarget := hy.2
      change e y ∈ ballPartial.target at hytarget
      rwa [complexUnivBallPartialDiffeomorph_target (e x) r hr] at hytarget
    obtain ⟨z, hzS, hzy⟩ := hball hyball
    have hyz : y = z := e.injOn hy.1 hzS.1 hzy.symm
    simpa [hyz] using hzS.2
  exact ⟨U, hxU, hUW,
    ⟨partialDiffeomorphSourceToComplexPlanarModelOpen T hTtarget⟩⟩

/-- The rectangle primitive as a one-form on the complex coordinate plane. -/
noncomputable def complexPlanarCompactSupportPrimitiveOneForm
    (a b c : ℝ) (hab : a ≤ b) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hρ : ContDiff ℝ ∞ ρ) :
    JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := complexPlanarModelOpen) ℝ 1 where
  toFun := fun z ↦ complexPlanarPrimitiveOneFormCoefficient a b c f ρ (z : ℂ)
  isContMDiff := by
    apply JJMath.Manifold.isContMDiffForm_modelOpen_of_contDiffOn_coeff
      (E := ℂ) complexPlanarModelOpen 1
    refine (complexPlanarPrimitiveOneFormCoefficient_contDiff
      (c := c) hab hf hρ).contDiffOn.congr ?_
    intro z _hz
    simp [JJMath.Manifold.modelOpenFormCoeffExtension, complexPlanarModelOpen]

/-- The positively oriented real basis of the complex plane. -/
def complexPlanarOrientedBasis : Fin 2 → ℂ
  | 0 => 1
  | 1 => Complex.I

@[simp]
theorem complexPlanarPrimitiveOneFormCoefficient_removeNth_zero
    (a b c : ℝ) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ) (z : ℂ) :
    complexPlanarPrimitiveOneFormCoefficient a b c f ρ z
        (Fin.removeNth (0 : Fin 2) complexPlanarOrientedBasis) =
      planarHorizontalPrimitive a b f ρ (Complex.equivRealProdCLM z) := by
  have htail : Fin.tail complexPlanarOrientedBasis =
      (fun _ : Fin 1 ↦ Complex.I) := by
    funext i
    fin_cases i
    rfl
  rw [show Fin.removeNth (0 : Fin 2) complexPlanarOrientedBasis =
      Fin.tail complexPlanarOrientedBasis by rfl, htail]
  change complexPlanarPrimitiveCovector a b c f ρ z Complex.I = _
  simp [complexPlanarPrimitiveCovector]

@[simp]
theorem complexPlanarPrimitiveOneFormCoefficient_removeNth_one
    (a b c : ℝ) (f : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ) (z : ℂ) :
    complexPlanarPrimitiveOneFormCoefficient a b c f ρ z
        (Fin.removeNth (1 : Fin 2) complexPlanarOrientedBasis) =
      planarVerticalPrimitiveCoefficient a b c f ρ (Complex.equivRealProdCLM z) := by
  have hremove : Fin.removeNth (1 : Fin 2) complexPlanarOrientedBasis =
      (fun _ : Fin 1 ↦ (1 : ℂ)) := by
    funext i
    fin_cases i
    rfl
  rw [hremove]
  change complexPlanarPrimitiveCovector a b c f ρ z 1 = _
  simp [complexPlanarPrimitiveCovector]

/-- Differentiating after real-imaginary coordinates in the real direction
is differentiation in the first planar coordinate. -/
theorem fderiv_comp_equivRealProdCLM_apply_one
    {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (z : ℂ) :
    fderiv ℝ (fun w : ℂ ↦ g (Complex.equivRealProdCLM w)) z 1 =
      fderiv ℝ g (Complex.equivRealProdCLM z) (1, 0) := by
  have hgAt : HasFDerivAt g
      (fderiv ℝ g (Complex.equivRealProdCLM z))
      (Complex.equivRealProdCLM z) :=
    (hg.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp := hgAt.comp z Complex.equivRealProdCLM.hasFDerivAt
  have hmaps := hcomp.fderiv
  have happ := congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L 1) hmaps
  simpa [Function.comp_def] using happ

/-- Differentiating after real-imaginary coordinates in the imaginary
direction is differentiation in the second planar coordinate. -/
theorem fderiv_comp_equivRealProdCLM_apply_I
    {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (z : ℂ) :
    fderiv ℝ (fun w : ℂ ↦ g (Complex.equivRealProdCLM w)) z Complex.I =
      fderiv ℝ g (Complex.equivRealProdCLM z) (0, 1) := by
  have hgAt : HasFDerivAt g
      (fderiv ℝ g (Complex.equivRealProdCLM z))
      (Complex.equivRealProdCLM z) :=
    (hg.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp := hgAt.comp z Complex.equivRealProdCLM.hasFDerivAt
  have hmaps := hcomp.fderiv
  have happ := congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L Complex.I) hmaps
  simpa [Function.comp_def] using happ

/-- In complex coordinates, the exterior derivative still recovers the
original planar coefficient on the oriented real basis. -/
theorem deRhamDifferential_complexPlanarCompactSupportPrimitiveOneForm_apply_basis
    {a b c : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ} {ρ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hρ : ContDiff ℝ ∞ ρ)
    (z : complexPlanarModelOpen) :
    (JJMath.Manifold.deRhamDifferential
        (I := SurfaceRealModel) (M := complexPlanarModelOpen) (A := ℝ) 1
        (complexPlanarCompactSupportPrimitiveOneForm a b c hab f ρ hf hρ)).toFun z
        complexPlanarOrientedBasis = f (Complex.equivRealProdCLM (z : ℂ)) := by
  rw [JJMath.Manifold.deRhamDifferential_modelOpen_toFun]
  have hcoeff :
      JJMath.Manifold.modelOpenFormCoeffExtension
          (E := ℂ) complexPlanarModelOpen 1
          (fun y ↦ JJMath.Manifold.smoothFormModelCoeff
            (E := ℂ) complexPlanarModelOpen 1
              (complexPlanarCompactSupportPrimitiveOneForm a b c hab f ρ hf hρ) y) =
        complexPlanarPrimitiveOneFormCoefficient a b c f ρ := by
    funext w
    simp [JJMath.Manifold.modelOpenFormCoeffExtension,
      JJMath.Manifold.smoothFormModelCoeff, complexPlanarModelOpen,
      complexPlanarCompactSupportPrimitiveOneForm]
  rw [hcoeff]
  change
    extDerivWithin (complexPlanarPrimitiveOneFormCoefficient a b c f ρ)
      Set.univ (z : ℂ) complexPlanarOrientedBasis =
        f (Complex.equivRealProdCLM (z : ℂ))
  rw [extDerivWithin_univ]
  rw [extDeriv_apply
    ((complexPlanarPrimitiveOneFormCoefficient_contDiff
      (c := c) hab hf hρ).differentiable (by simp)).differentiableAt]
  rw [Fin.sum_univ_two]
  have hzero :
      (fun w : ℂ ↦
        complexPlanarPrimitiveOneFormCoefficient a b c f ρ w
          (Fin.removeNth (0 : Fin 2) complexPlanarOrientedBasis)) =
        fun w : ℂ ↦ planarHorizontalPrimitive a b f ρ
          (Complex.equivRealProdCLM w) := by
    funext w
    exact complexPlanarPrimitiveOneFormCoefficient_removeNth_zero a b c f ρ w
  have hone :
      (fun w : ℂ ↦
        complexPlanarPrimitiveOneFormCoefficient a b c f ρ w
          (Fin.removeNth (1 : Fin 2) complexPlanarOrientedBasis)) =
        fun w : ℂ ↦ planarVerticalPrimitiveCoefficient a b c f ρ
          (Complex.equivRealProdCLM w) := by
    funext w
    exact complexPlanarPrimitiveOneFormCoefficient_removeNth_one a b c f ρ w
  rw [hzero, hone]
  norm_num [complexPlanarOrientedBasis]
  have hQder := fderiv_comp_equivRealProdCLM_apply_one
    (planarHorizontalPrimitive_contDiff hab hf hρ) (z : ℂ)
  have hPder := fderiv_comp_equivRealProdCLM_apply_I
    (planarVerticalPrimitiveCoefficient_contDiff (c := c) hab hf hρ) (z : ℂ)
  change
    fderiv ℝ (fun w : ℂ ↦ planarHorizontalPrimitive a b f ρ (w.re, w.im))
        (z : ℂ) 1 +
      -fderiv ℝ
        (fun w : ℂ ↦ planarVerticalPrimitiveCoefficient a b c f ρ (w.re, w.im))
        (z : ℂ) Complex.I = f ((z : ℂ).re, (z : ℂ).im)
  have hQder' :
      fderiv ℝ (fun w : ℂ ↦ planarHorizontalPrimitive a b f ρ (w.re, w.im))
          (z : ℂ) 1 =
        fderiv ℝ (planarHorizontalPrimitive a b f ρ)
          ((z : ℂ).re, (z : ℂ).im) (1, 0) := by
    simpa using hQder
  have hPder' :
      fderiv ℝ
          (fun w : ℂ ↦ planarVerticalPrimitiveCoefficient a b c f ρ (w.re, w.im))
          (z : ℂ) Complex.I =
        fderiv ℝ (planarVerticalPrimitiveCoefficient a b c f ρ)
          ((z : ℂ).re, (z : ℂ).im) (0, 1) := by
    simpa using hPder
  rw [hQder', hPder']
  simpa [sub_eq_add_neg] using planarCompactSupportPrimitive_curl_eq
    hab hf hρ ((z : ℂ).re, (z : ℂ).im)

/-! ## Exactness of zero-mass two-forms in one complex coordinate plane -/

/-- The scalar coefficient of a two-form on the complex coordinate plane,
evaluated on the positively oriented real basis. -/
noncomputable def complexPlanarTwoFormCoefficient
    (omega : JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := complexPlanarModelOpen) ℝ 2)
    (z : ℂ) : ℝ :=
  omega.toFun ⟨z, trivial⟩ complexPlanarOrientedBasis

/-- The oriented scalar coefficient of a smooth planar two-form is smooth. -/
theorem complexPlanarTwoFormCoefficient_contDiff
    (omega : JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := complexPlanarModelOpen) ℝ 2) :
    ContDiff ℝ ∞ (complexPlanarTwoFormCoefficient omega) := by
  have hfield : ContDiff ℝ ∞
      (fun z : ℂ ↦ JJMath.Manifold.smoothFormModelCoeff (E := ℂ)
        complexPlanarModelOpen 2 omega ⟨z, trivial⟩) := by
    have h := JJMath.Manifold.contDiffOn_smoothFormModelCoeff_modelOpen
      (E := ℂ) complexPlanarModelOpen 2 omega
    have heq : JJMath.Manifold.modelOpenFormCoeffExtension (E := ℂ)
        complexPlanarModelOpen 2
          (fun x ↦ JJMath.Manifold.smoothFormModelCoeff (E := ℂ)
            complexPlanarModelOpen 2 omega x) =
        fun z : ℂ ↦ JJMath.Manifold.smoothFormModelCoeff (E := ℂ)
          complexPlanarModelOpen 2 omega ⟨z, trivial⟩ := by
      funext z
      simp [JJMath.Manifold.modelOpenFormCoeffExtension,
        complexPlanarModelOpen]
    rw [heq] at h
    exact contDiffOn_univ.mp h
  unfold complexPlanarTwoFormCoefficient
  exact (ContinuousAlternatingMap.apply ℝ ℂ ℝ
    complexPlanarOrientedBasis).contDiff.comp hfield

/-- The same scalar coefficient, written as a function of real-imaginary
coordinate pairs. -/
noncomputable def planarCoefficientOfComplexTwoForm
    (omega : JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := complexPlanarModelOpen) ℝ 2)
    (p : ℝ × ℝ) : ℝ :=
  complexPlanarTwoFormCoefficient omega
    (Complex.equivRealProdCLM.symm p)

/-- The real-pair coefficient of a smooth complex-plane two-form is smooth. -/
theorem planarCoefficientOfComplexTwoForm_contDiff
    (omega : JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := complexPlanarModelOpen) ℝ 2) :
    ContDiff ℝ ∞ (planarCoefficientOfComplexTwoForm omega) := by
  exact (complexPlanarTwoFormCoefficient_contDiff omega).comp
    Complex.equivRealProdCLM.symm.contDiff

/-- Two continuous top-degree alternating forms on the complex plane are
equal when they agree on the oriented real basis. -/
theorem complexTopDegreeContinuousAlternatingMap_ext_basis
    (omega eta : ℂ [⋀^Fin 2]→L[ℝ] ℝ)
    (h : omega complexPlanarOrientedBasis =
      eta complexPlanarOrientedBasis) :
    omega = eta := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [JJMath.Manifold.alternatingMap_eq_smulRight_basis_det
      Complex.basisOneI omega.toAlternatingMap,
    JJMath.Manifold.alternatingMap_eq_smulRight_basis_det
      Complex.basisOneI eta.toAlternatingMap]
  congr 1
  have hb : (fun i ↦ Complex.basisOneI i) =
      complexPlanarOrientedBasis := by
    funext i
    fin_cases i <;>
      simp [Complex.coe_basisOneI, complexPlanarOrientedBasis]
  simpa [hb] using h

/-- The standard oriented area form on the complex plane, viewed as a
two-dimensional real vector space. -/
noncomputable def complexPlanarAreaForm : ℂ [⋀^Fin 2]→L[ℝ] ℝ :=
  Complex.basisOneI.det.mkContinuous 2 (by
    intro m
    rw [Fin.prod_univ_two]
    change ‖(Complex.basisOneI.toMatrix m).det‖ ≤ _
    rw [Matrix.det_fin_two]
    have h00 : Complex.basisOneI.toMatrix m 0 0 = (m 0).re := by
      simp [Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr]
    have h01 : Complex.basisOneI.toMatrix m 0 1 = (m 1).re := by
      simp [Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr]
    have h10 : Complex.basisOneI.toMatrix m 1 0 = (m 0).im := by
      simp [Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr]
    have h11 : Complex.basisOneI.toMatrix m 1 1 = (m 1).im := by
      simp [Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr]
    rw [h00, h01, h10, h11]
    calc
      ‖(m 0).re * (m 1).im - (m 1).re * (m 0).im‖
          ≤ ‖(m 0).re * (m 1).im‖ + ‖(m 1).re * (m 0).im‖ :=
            norm_sub_le _ _
      _ ≤ ‖m 0‖ * ‖m 1‖ + ‖m 1‖ * ‖m 0‖ := by
        simp only [norm_mul]
        gcongr
        · exact Complex.abs_re_le_norm _
        · exact Complex.abs_im_le_norm _
        · exact Complex.abs_re_le_norm _
        · exact Complex.abs_im_le_norm _
      _ = 2 * (‖m 0‖ * ‖m 1‖) := by ring)

/-- The standard oriented area form evaluates to one on the oriented basis. -/
theorem complexPlanarAreaForm_basis :
    complexPlanarAreaForm (fun i : Fin 2 ↦ Complex.basisOneI i) = 1 := by
  change Complex.basisOneI.det (fun i : Fin 2 ↦ Complex.basisOneI i) = 1
  rw [Module.Basis.det_self]

/-- Build a planar two-form from its oriented scalar coefficient. -/
noncomputable def complexPlanarTwoFormOfCoefficient
    (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    SmoothForms (I := SurfaceRealModel)
      (M := complexPlanarModelOpen) ℝ 2 where
  toFun := fun z ↦
    f ((z : ℂ).re, (z : ℂ).im) • complexPlanarAreaForm
  isContMDiff := by
    apply isContMDiffForm_modelOpen_of_contDiffOn_coeff
      (E := ℂ) complexPlanarModelOpen 2
    have hsmooth : ContDiff ℝ ∞
        (fun z : ℂ ↦ f (z.re, z.im) • complexPlanarAreaForm) := by
      exact (hf.comp
        (Complex.reCLM.contDiff.prodMk Complex.imCLM.contDiff)).smul
          contDiff_const
    refine hsmooth.contDiffOn.congr ?_
    intro z _hz
    simp [modelOpenFormCoeffExtension, complexPlanarModelOpen]

/-- Extracting the oriented coefficient of the two-form built from a
coefficient recovers that coefficient. -/
theorem planarCoefficientOfComplexPlanarTwoFormOfCoefficient
    (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    planarCoefficientOfComplexTwoForm
      (complexPlanarTwoFormOfCoefficient f hf) = f := by
  funext p
  change (f p • complexPlanarAreaForm) complexPlanarOrientedBasis = f p
  have hb : complexPlanarOrientedBasis =
      (fun i : Fin 2 ↦ Complex.basisOneI i) := by
    funext i
    fin_cases i <;>
      simp [complexPlanarOrientedBasis, Complex.coe_basisOneI]
  have harea : complexPlanarAreaForm complexPlanarOrientedBasis = 1 := by
    rw [hb]
    exact complexPlanarAreaForm_basis
  change f p * complexPlanarAreaForm complexPlanarOrientedBasis = f p
  rw [harea, mul_one]

/-- Evaluating a two-form built from a scalar coefficient on the standard
oriented basis recovers that coefficient. -/
theorem complexPlanarTwoFormOfCoefficient_apply_basis
    (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (z : complexPlanarModelOpen) :
    (complexPlanarTwoFormOfCoefficient f hf).toFun z
        complexPlanarOrientedBasis =
      f ((z : ℂ).re, (z : ℂ).im) := by
  have h := congrFun
    (planarCoefficientOfComplexPlanarTwoFormOfCoefficient f hf)
    (Complex.equivRealProdCLM (z : ℂ))
  simpa [planarCoefficientOfComplexTwoForm,
    complexPlanarTwoFormCoefficient] using h

/-- Every planar top-degree form is recovered from its oriented scalar
coefficient. -/
theorem complexPlanarTwoFormOfPlanarCoefficient
    (omega : SmoothForms (I := SurfaceRealModel)
      (M := complexPlanarModelOpen) ℝ 2) :
    complexPlanarTwoFormOfCoefficient
        (planarCoefficientOfComplexTwoForm omega)
        (planarCoefficientOfComplexTwoForm_contDiff omega) = omega := by
  apply DifferentialForm.ext
  intro z
  apply complexTopDegreeContinuousAlternatingMap_ext_basis
  change planarCoefficientOfComplexTwoForm omega
      ((z : ℂ).re, (z : ℂ).im) *
        complexPlanarAreaForm complexPlanarOrientedBasis =
    (omega.toFun z) complexPlanarOrientedBasis
  have harea : complexPlanarAreaForm complexPlanarOrientedBasis = 1 := by
    have hb : complexPlanarOrientedBasis =
        (fun i : Fin 2 ↦ Complex.basisOneI i) := by
      funext i
      fin_cases i <;>
        simp [complexPlanarOrientedBasis, Complex.coe_basisOneI]
    rw [hb]
    exact complexPlanarAreaForm_basis
  rw [harea, mul_one]
  rfl

/-- Apply the explicit rectangle primitive to the oriented coefficient of a
two-form on the complex coordinate plane. -/
noncomputable def complexPlanarPrimitiveOfTwoForm
    (a b c : ℝ) (hab : a ≤ b)
    (omega : JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := complexPlanarModelOpen) ℝ 2)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) :
    JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := complexPlanarModelOpen) ℝ 1 :=
  complexPlanarCompactSupportPrimitiveOneForm
    a b c hab (planarCoefficientOfComplexTwoForm omega) ρ
      (planarCoefficientOfComplexTwoForm_contDiff omega) hρ

/-- On the complex coordinate plane the explicit primitive differentiates to
the original two-form. -/
theorem deRhamDifferential_complexPlanarPrimitiveOfTwoForm
    {a b c : ℝ} (hab : a ≤ b)
    (omega : JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := complexPlanarModelOpen) ℝ 2)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) :
    JJMath.Manifold.deRhamDifferential (I := SurfaceRealModel)
        (M := complexPlanarModelOpen) (A := ℝ) 1
        (complexPlanarPrimitiveOfTwoForm a b c hab omega ρ hρ) =
      omega := by
  apply DifferentialForm.ext
  intro z
  apply complexTopDegreeContinuousAlternatingMap_ext_basis
  rw [show complexPlanarPrimitiveOfTwoForm a b c hab omega ρ hρ =
      complexPlanarCompactSupportPrimitiveOneForm
        a b c hab (planarCoefficientOfComplexTwoForm omega) ρ
          (planarCoefficientOfComplexTwoForm_contDiff omega) hρ by rfl]
  have h :=
    deRhamDifferential_complexPlanarCompactSupportPrimitiveOneForm_apply_basis
      (c := c) hab (planarCoefficientOfComplexTwoForm_contDiff omega) hρ z
  simpa [planarCoefficientOfComplexTwoForm,
    complexPlanarTwoFormCoefficient] using h

/-- The compact closed rectangle used as a support core in the full complex
coordinate plane. -/
def complexPlanarRectangleCore (a b c d : ℝ) :
    Set complexPlanarModelOpen :=
  {z | Complex.equivRealProdCLM (z : ℂ) ∈
    Set.Icc a b ×ˢ Set.Icc c d}

/-- A closed coordinate rectangle is compact as a subset of the full complex
coordinate plane. -/
theorem complexPlanarRectangleCore_isCompact (a b c d : ℝ) :
    IsCompact (complexPlanarRectangleCore a b c d) := by
  rw [Subtype.isCompact_iff]
  have himage :
      ((↑) : complexPlanarModelOpen → ℂ) ''
          complexPlanarRectangleCore a b c d =
        Complex.equivRealProdCLM ⁻¹'
          (Set.Icc a b ×ˢ Set.Icc c d) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, trivial⟩, hz, rfl⟩
  rw [himage]
  exact Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.2
    (isCompact_Icc.prod isCompact_Icc)

/-- Under the rectangle support and zero-total-mass hypotheses, the explicit
primitive vanishes outside the corresponding closed rectangle. -/
theorem complexPlanarPrimitiveOfTwoForm_toFun_eq_zero_of_not_mem_rectangle
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (omega : JJMath.Manifold.SmoothForms
      (I := SurfaceRealModel) (M := complexPlanarModelOpen) ℝ 2)
    (ρ : ℝ → ℝ)
    (hfc : HasCompactSupport (planarCoefficientOfComplexTwoForm omega))
    (hfrect : tsupport (planarCoefficientOfComplexTwoForm omega) ⊆
      Set.Ioo a b ×ˢ Set.Ioo c d)
    (hρ : ContDiff ℝ ∞ ρ)
    (hρsupport : tsupport ρ ⊆ Set.Ioo a b)
    (hρone : ∫ x in a..b, ρ x = 1)
    (htotal : ∫ y in c..d,
      planarHorizontalMarginal a b
        (planarCoefficientOfComplexTwoForm omega) y = 0)
    (z : complexPlanarModelOpen)
    (hz : z ∉ complexPlanarRectangleCore a b c d) :
    (complexPlanarPrimitiveOfTwoForm a b c hab.le omega ρ hρ).toFun z = 0 := by
  have hsupp :=
    complexPlanarPrimitiveOneFormCoefficient_hasCompactSupport_and_tsupport_subset
      hab hcd (planarCoefficientOfComplexTwoForm_contDiff omega)
      hfc hfrect hρ hρsupport hρone htotal
  have hzts : (z : ℂ) ∉ tsupport
      (complexPlanarPrimitiveOneFormCoefficient a b c
        (planarCoefficientOfComplexTwoForm omega) ρ) := by
    intro hzts
    apply hz
    exact ⟨Ioo_subset_Icc_self (hsupp.2 hzts).1,
      Ioo_subset_Icc_self (hsupp.2 hzts).2⟩
  change complexPlanarPrimitiveOneFormCoefficient a b c
      (planarCoefficientOfComplexTwoForm omega) ρ (z : ℂ) = 0
  exact image_eq_zero_of_notMem_tsupport hzts

/-- The normalized two-form carrying the total mass of a planar coefficient
inside a prescribed rectangle. -/
noncomputable def complexPlanarTransportedMassTwoForm
    (a b c d : ℝ) (f : ℝ × ℝ → ℝ) :
    SmoothForms (I := SurfaceRealModel) (M := complexPlanarModelOpen) ℝ 2 :=
  complexPlanarTwoFormOfCoefficient
    (fun p ↦ planarRectangleMass a b c d f *
      planarRectangleNormalizingDensity a b c d p)
    (contDiff_const.mul planarRectangleNormalizingDensity_contDiff)

/-- An explicit compactly supported one-form that removes the mass of a
planar two-form from a rectangle and replaces it by the normalized bump in
the same rectangle. -/
noncomputable def complexPlanarMassTransportPrimitive
    (a b c d : ℝ) (hab : a < b) (f : ℝ × ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    SmoothForms (I := SurfaceRealModel) (M := complexPlanarModelOpen) ℝ 1 :=
  complexPlanarPrimitiveOfTwoForm a b c hab.le
    (complexPlanarTwoFormOfCoefficient
      (planarMassTransportRemainder a b c d f)
      (planarMassTransportRemainder_contDiff hf))
    (intervalNormalizingDensity a b)
    intervalNormalizingDensity_contDiff

/-- The planar mass-transport primitive differentiates to the original
two-form minus its normalized mass bump. -/
theorem deRhamDifferential_complexPlanarMassTransportPrimitive
    {a b c d : ℝ} (hab : a < b)
    (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    deRhamDifferential (I := SurfaceRealModel)
        (M := complexPlanarModelOpen) (A := ℝ) 1
        (complexPlanarMassTransportPrimitive a b c d hab f hf) =
      complexPlanarTwoFormOfCoefficient f hf -
        complexPlanarTransportedMassTwoForm a b c d f := by
  rw [complexPlanarMassTransportPrimitive,
    deRhamDifferential_complexPlanarPrimitiveOfTwoForm]
  apply DifferentialForm.ext
  intro z
  apply complexTopDegreeContinuousAlternatingMap_ext_basis
  change
    (complexPlanarTwoFormOfCoefficient
      (planarMassTransportRemainder a b c d f) _).toFun z
        complexPlanarOrientedBasis =
      (complexPlanarTwoFormOfCoefficient f hf).toFun z
          complexPlanarOrientedBasis -
        (complexPlanarTransportedMassTwoForm a b c d f).toFun z
          complexPlanarOrientedBasis
  rw [complexPlanarTwoFormOfCoefficient_apply_basis,
    show complexPlanarTransportedMassTwoForm a b c d f =
      complexPlanarTwoFormOfCoefficient
        (fun p ↦ planarRectangleMass a b c d f *
          planarRectangleNormalizingDensity a b c d p)
        (contDiff_const.mul planarRectangleNormalizingDensity_contDiff) by rfl,
    complexPlanarTwoFormOfCoefficient_apply_basis,
    complexPlanarTwoFormOfCoefficient_apply_basis]
  rfl

/-- The normalized transported mass two-form is supported in the chosen
closed rectangle. -/
theorem complexPlanarTransportedMassTwoForm_toFun_eq_zero_of_not_mem_rectangle
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (f : ℝ × ℝ → ℝ) (z : complexPlanarModelOpen)
    (hz : z ∉ complexPlanarRectangleCore a b c d) :
    (complexPlanarTransportedMassTwoForm a b c d f).toFun z = 0 := by
  have hp : ((z : ℂ).re, (z : ℂ).im) ∉
      tsupport (planarRectangleNormalizingDensity a b c d) := by
    intro hp
    apply hz
    have hp' := planarRectangleNormalizingDensity_tsupport_subset
      hab hcd hp
    exact ⟨Ioo_subset_Icc_self hp'.1, Ioo_subset_Icc_self hp'.2⟩
  have hzero := image_eq_zero_of_notMem_tsupport hp
  change (planarRectangleMass a b c d f *
      planarRectangleNormalizingDensity a b c d
        ((z : ℂ).re, (z : ℂ).im)) • complexPlanarAreaForm = 0
  rw [hzero, mul_zero, zero_smul]

/-- The planar mass-transport primitive is supported in the chosen closed
rectangle when the original coefficient is supported in its interior. -/
theorem complexPlanarMassTransportPrimitive_toFun_eq_zero_of_not_mem_rectangle
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfrect : tsupport f ⊆ Ioo a b ×ˢ Ioo c d)
    (z : complexPlanarModelOpen)
    (hz : z ∉ complexPlanarRectangleCore a b c d) :
    (complexPlanarMassTransportPrimitive a b c d hab f hf).toFun z = 0 := by
  let r := planarMassTransportRemainder a b c d f
  have hr : ContDiff ℝ ∞ r := planarMassTransportRemainder_contDiff hf
  have hcoeff : planarCoefficientOfComplexTwoForm
      (complexPlanarTwoFormOfCoefficient r hr) = r :=
    planarCoefficientOfComplexPlanarTwoFormOfCoefficient r hr
  have hfc : HasCompactSupport
      (planarCoefficientOfComplexTwoForm
        (complexPlanarTwoFormOfCoefficient r hr)) := by
    rw [hcoeff]
    apply IsCompact.of_isClosed_subset
      (isCompact_Icc.prod isCompact_Icc)
      (isClosed_tsupport r)
    exact (planarMassTransportRemainder_tsupport_subset hab hcd hfrect).trans
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hfrect' : tsupport (planarCoefficientOfComplexTwoForm
      (complexPlanarTwoFormOfCoefficient r hr)) ⊆
      Ioo a b ×ˢ Ioo c d := by
    rw [hcoeff]
    exact planarMassTransportRemainder_tsupport_subset hab hcd hfrect
  have htotal : ∫ y in c..d,
      planarHorizontalMarginal a b
        (planarCoefficientOfComplexTwoForm
          (complexPlanarTwoFormOfCoefficient r hr)) y = 0 := by
    rw [hcoeff]
    exact planarMassTransportRemainder_total_eq_zero hab hcd hf
  exact complexPlanarPrimitiveOfTwoForm_toFun_eq_zero_of_not_mem_rectangle
    (omega := complexPlanarTwoFormOfCoefficient r hr)
    (ρ := intervalNormalizingDensity a b)
    hab hcd hfc hfrect'
    intervalNormalizingDensity_contDiff
    (intervalNormalizingDensity_tsupport_subset hab)
    (intervalNormalizingDensity_integral_eq_one hab)
    htotal z hz

/-- The normalized target two-form for a two-rectangle transport step. -/
noncomputable def complexPlanarTransportedMassTwoFormTo
    (A B C D a b c d : ℝ) (f : ℝ × ℝ → ℝ) :
    SmoothForms (I := SurfaceRealModel) (M := complexPlanarModelOpen) ℝ 2 :=
  complexPlanarTwoFormOfCoefficient
    (fun p ↦ planarRectangleMass A B C D f *
      planarRectangleNormalizingDensity a b c d p)
    (contDiff_const.mul planarRectangleNormalizingDensity_contDiff)

/-- The compactly supported primitive which moves mass from an outer
rectangle into an inner target rectangle. -/
noncomputable def complexPlanarMassTransportPrimitiveTo
    (A B C D a b c d : ℝ) (hAB : A < B)
    (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    SmoothForms (I := SurfaceRealModel) (M := complexPlanarModelOpen) ℝ 1 :=
  complexPlanarPrimitiveOfTwoForm A B C hAB.le
    (complexPlanarTwoFormOfCoefficient
      (planarMassTransportRemainderTo A B C D a b c d f)
      (planarMassTransportRemainderTo_contDiff hf))
    (intervalNormalizingDensity A B)
    intervalNormalizingDensity_contDiff

/-- The two-rectangle transport primitive differentiates to the original
two-form minus the mass bump in the target rectangle. -/
theorem deRhamDifferential_complexPlanarMassTransportPrimitiveTo
    {A B C D a b c d : ℝ} (hAB : A < B)
    (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    deRhamDifferential (I := SurfaceRealModel)
        (M := complexPlanarModelOpen) (A := ℝ) 1
        (complexPlanarMassTransportPrimitiveTo
          A B C D a b c d hAB f hf) =
      complexPlanarTwoFormOfCoefficient f hf -
        complexPlanarTransportedMassTwoFormTo A B C D a b c d f := by
  rw [complexPlanarMassTransportPrimitiveTo,
    deRhamDifferential_complexPlanarPrimitiveOfTwoForm]
  apply DifferentialForm.ext
  intro z
  apply complexTopDegreeContinuousAlternatingMap_ext_basis
  change
    (complexPlanarTwoFormOfCoefficient
      (planarMassTransportRemainderTo A B C D a b c d f) _).toFun z
        complexPlanarOrientedBasis =
      (complexPlanarTwoFormOfCoefficient f hf).toFun z
          complexPlanarOrientedBasis -
        (complexPlanarTransportedMassTwoFormTo
          A B C D a b c d f).toFun z complexPlanarOrientedBasis
  rw [complexPlanarTwoFormOfCoefficient_apply_basis,
    show complexPlanarTransportedMassTwoFormTo A B C D a b c d f =
      complexPlanarTwoFormOfCoefficient
        (fun p ↦ planarRectangleMass A B C D f *
          planarRectangleNormalizingDensity a b c d p)
        (contDiff_const.mul planarRectangleNormalizingDensity_contDiff) by rfl,
    complexPlanarTwoFormOfCoefficient_apply_basis,
    complexPlanarTwoFormOfCoefficient_apply_basis]
  rfl

/-- The transported target two-form vanishes outside its target rectangle. -/
theorem complexPlanarTransportedMassTwoFormTo_toFun_eq_zero_of_not_mem_target
    {A B C D a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (f : ℝ × ℝ → ℝ) (z : complexPlanarModelOpen)
    (hz : z ∉ complexPlanarRectangleCore a b c d) :
    (complexPlanarTransportedMassTwoFormTo A B C D a b c d f).toFun z = 0 := by
  have hp : ((z : ℂ).re, (z : ℂ).im) ∉
      tsupport (planarRectangleNormalizingDensity a b c d) := by
    intro hp
    apply hz
    have hp' := planarRectangleNormalizingDensity_tsupport_subset hab hcd hp
    exact ⟨Ioo_subset_Icc_self hp'.1, Ioo_subset_Icc_self hp'.2⟩
  have hzero := image_eq_zero_of_notMem_tsupport hp
  change (planarRectangleMass A B C D f *
      planarRectangleNormalizingDensity a b c d
        ((z : ℂ).re, (z : ℂ).im)) • complexPlanarAreaForm = 0
  rw [hzero, mul_zero, zero_smul]

/-- The two-rectangle transport primitive is supported in the outer
rectangle when the original coefficient is supported there and the target
rectangle lies strictly inside it. -/
theorem complexPlanarMassTransportPrimitiveTo_toFun_eq_zero_of_not_mem_outer
    {A B C D a b c d : ℝ}
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hCc : C < c) (hcd : c < d) (hdD : d < D)
    (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfrect : tsupport f ⊆ Ioo A B ×ˢ Ioo C D)
    (z : complexPlanarModelOpen)
    (hz : z ∉ complexPlanarRectangleCore A B C D) :
    (complexPlanarMassTransportPrimitiveTo A B C D a b c d
      ((hAa.trans hab).trans hbB) f hf).toFun z = 0 := by
  let r := planarMassTransportRemainderTo A B C D a b c d f
  have hr : ContDiff ℝ ∞ r := planarMassTransportRemainderTo_contDiff hf
  have hcoeff : planarCoefficientOfComplexTwoForm
      (complexPlanarTwoFormOfCoefficient r hr) = r :=
    planarCoefficientOfComplexPlanarTwoFormOfCoefficient r hr
  have hAB : A < B := (hAa.trans hab).trans hbB
  have hCD : C < D := (hCc.trans hcd).trans hdD
  have hfc : HasCompactSupport
      (planarCoefficientOfComplexTwoForm
        (complexPlanarTwoFormOfCoefficient r hr)) := by
    rw [hcoeff]
    apply IsCompact.of_isClosed_subset
      (isCompact_Icc.prod isCompact_Icc) (isClosed_tsupport r)
    exact (planarMassTransportRemainderTo_tsupport_subset
      hAa hab hbB hCc hcd hdD hfrect).trans
        (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hfrect' : tsupport (planarCoefficientOfComplexTwoForm
      (complexPlanarTwoFormOfCoefficient r hr)) ⊆
      Ioo A B ×ˢ Ioo C D := by
    rw [hcoeff]
    exact planarMassTransportRemainderTo_tsupport_subset
      hAa hab hbB hCc hcd hdD hfrect
  have htotal : ∫ y in C..D,
      planarHorizontalMarginal A B
        (planarCoefficientOfComplexTwoForm
          (complexPlanarTwoFormOfCoefficient r hr)) y = 0 := by
    rw [hcoeff]
    exact planarMassTransportRemainderTo_total_eq_zero
      hAa hab hbB hCc hcd hdD hf
  exact complexPlanarPrimitiveOfTwoForm_toFun_eq_zero_of_not_mem_rectangle
    (omega := complexPlanarTwoFormOfCoefficient r hr)
    (ρ := intervalNormalizingDensity A B)
    hAB hCD hfc hfrect'
    intervalNormalizingDensity_contDiff
    (intervalNormalizingDensity_tsupport_subset hAB)
    (intervalNormalizingDensity_integral_eq_one hAB)
    htotal z hz

/-- Every point of an open subset of the real coordinate plane is surrounded
by a closed axis-parallel rectangle still contained in that open set. -/
theorem exists_closed_rectangle_subset_of_mem_open
    {O : Set (ℝ × ℝ)} (hO : IsOpen O) {p : ℝ × ℝ} (hp : p ∈ O) :
    ∃ ε : ℝ, 0 < ε ∧
      Icc (p.1 - ε) (p.1 + ε) ×ˢ Icc (p.2 - ε) (p.2 + ε) ⊆ O := by
  rcases Metric.isOpen_iff.1 hO p hp with ⟨r, hr, hball⟩
  let ε := r / 2
  refine ⟨ε, half_pos hr, ?_⟩
  intro q hq
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq]
  apply max_lt
  · rw [Real.dist_eq]
    apply lt_of_le_of_lt (abs_le.mpr ?_) (half_lt_self hr)
    constructor <;> dsimp [ε] at * <;> linarith [hq.1.1, hq.1.2]
  · rw [Real.dist_eq]
    apply lt_of_le_of_lt (abs_le.mpr ?_) (half_lt_self hr)
    constructor <;> dsimp [ε] at * <;> linarith [hq.2.1, hq.2.2]

/-! ## Transport through one complex coordinate chart -/

/-- Write a two-form on a coordinate open set as a two-form on the full
complex coordinate plane. -/
noncomputable def complexCoordinatePushforwardTwoForm
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2) :
    SmoothForms (I := SurfaceRealModel)
      (M := complexPlanarModelOpen) ℝ 2 :=
  smoothFormsPullbackDiffeomorph SurfaceRealModel I phi.symm 2 alpha

omit [T2Space M] in
/-- If a local top-degree form vanishes at the point represented by a real
coordinate pair, then the scalar coefficient of its coordinate pushforward
vanishes at that pair. -/
theorem planarCoefficientOf_complexCoordinatePushforwardTwoForm_eq_zero
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (p : ℝ × ℝ)
    (hzero : alpha.toFun
      (phi.symm ⟨Complex.equivRealProdCLM.symm p, trivial⟩) = 0) :
    planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha) p = 0 := by
  let z : complexPlanarModelOpen :=
    ⟨Complex.equivRealProdCLM.symm p, trivial⟩
  have hpush :
      (complexCoordinatePushforwardTwoForm I U phi alpha).toFun z = 0 := by
    simp only [complexCoordinatePushforwardTwoForm,
      smoothFormsPullbackDiffeomorph]
    change (alpha.toFun (phi.symm z)).compContinuousLinearMap _ = 0
    rw [show alpha.toFun (phi.symm z) = 0 by exact hzero]
    rfl
  change ((complexCoordinatePushforwardTwoForm I U phi alpha).toFun z)
      complexPlanarOrientedBasis = 0
  rw [hpush]
  rfl

omit [T2Space M] in
/-- The closed support of a coordinate coefficient lies in the coordinate
image of any closed support core for the local top-degree form. -/
theorem planarCoefficientOf_complexCoordinatePushforwardTwoForm_tsupport_subset_image
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (K : Set U) (hK : IsCompact K)
    (hzero : ∀ x : U, x ∉ K → alpha.toFun x = 0) :
    tsupport (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) ⊆
      (fun x : U => Complex.equivRealProdCLM (phi x : ℂ)) '' K := by
  let coord : U → ℝ × ℝ := fun x =>
    Complex.equivRealProdCLM (phi x : ℂ)
  have hcoord : Continuous coord := by
    fun_prop
  have hcoordK : IsCompact (coord '' K) := hK.image hcoord
  refine closure_minimal ?_ hcoordK.isClosed
  intro p hp
  have hpK : phi.symm
      (⟨Complex.equivRealProdCLM.symm p, trivial⟩ :
        complexPlanarModelOpen) ∈ K := by
    by_contra hnot
    exact hp (planarCoefficientOf_complexCoordinatePushforwardTwoForm_eq_zero
      I U phi alpha p (hzero _ hnot))
  refine ⟨phi.symm
      (⟨Complex.equivRealProdCLM.symm p, trivial⟩ :
        complexPlanarModelOpen), hpK, ?_⟩
  dsimp [coord]
  rw [phi.apply_symm_apply]
  exact Complex.equivRealProdCLM.apply_symm_apply p

omit [T2Space M] in
/-- A local top-degree form supported in a compact set has a compactly
supported scalar coefficient in any full-plane complex chart. -/
theorem planarCoefficientOf_complexCoordinatePushforwardTwoForm_hasCompactSupport
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (K : Set U) (hK : IsCompact K)
    (hzero : ∀ x : U, x ∉ K → alpha.toFun x = 0) :
    HasCompactSupport (planarCoefficientOfComplexTwoForm
      (complexCoordinatePushforwardTwoForm I U phi alpha)) := by
  let coord : U → ℝ × ℝ := fun x =>
    Complex.equivRealProdCLM (phi x : ℂ)
  have hcoord : Continuous coord := by
    fun_prop
  have hcoordK : IsCompact (coord '' K) := hK.image hcoord
  change IsCompact (tsupport (planarCoefficientOfComplexTwoForm
    (complexCoordinatePushforwardTwoForm I U phi alpha)))
  exact IsCompact.of_isClosed_subset hcoordK
    (isClosed_tsupport (planarCoefficientOfComplexTwoForm
      (complexCoordinatePushforwardTwoForm I U phi alpha)))
    (planarCoefficientOf_complexCoordinatePushforwardTwoForm_tsupport_subset_image
      I U phi alpha K hK hzero)

/-- Every compact subset of the real coordinate plane lies in the interior
of a centered square. -/
theorem exists_open_rectangle_containing_compact
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ K ⊆ Ioo (-R) R ×ˢ Ioo (-R) R := by
  obtain ⟨R, hR, hsub⟩ := hK.isBounded.subset_ball_lt 0 (0 : ℝ × ℝ)
  refine ⟨R, hR, ?_⟩
  intro p hp
  have hball := hsub hp
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def] at hball
  have hfst : |p.1| < R :=
    (le_max_left |p.1| |p.2|).trans_lt (by simpa using hball)
  have hsnd : |p.2| < R :=
    (le_max_right |p.1| |p.2|).trans_lt (by simpa using hball)
  exact ⟨abs_lt.mp hfst, abs_lt.mp hsnd⟩

/-- Every compactly supported function on the real coordinate plane is
supported in the interior of a centered square. -/
theorem exists_open_rectangle_containing_tsupport_of_hasCompactSupport
    {f : ℝ × ℝ → ℝ} (hf : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ tsupport f ⊆ Ioo (-R) R ×ˢ Ioo (-R) R := by
  exact exists_open_rectangle_containing_compact hf

/-- Pull the explicit planar mass-transport primitive back through a complex
coordinate chart. -/
noncomputable def complexCoordinateLocalMassTransportPrimitive
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b c d : ℝ) (hab : a < b)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2) :
    SmoothForms (I := I) (M := U) ℝ 1 :=
  smoothFormsPullbackDiffeomorph I SurfaceRealModel phi 1
    (complexPlanarMassTransportPrimitive a b c d hab
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha))
      (planarCoefficientOfComplexTwoForm_contDiff
        (complexCoordinatePushforwardTwoForm I U phi alpha)))

/-- The normalized transported mass two-form in the original coordinate
open set. -/
noncomputable def complexCoordinateLocalTransportedMassTwoForm
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b c d : ℝ)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2) :
    SmoothForms (I := I) (M := U) ℝ 2 :=
  smoothFormsPullbackDiffeomorph I SurfaceRealModel phi 2
    (complexPlanarTransportedMassTwoForm a b c d
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)))

omit [T2Space M] in
/-- In one coordinate chart, exterior differentiation of the transport
primitive is the original two-form minus its normalized mass bump. -/
theorem deRhamDifferential_complexCoordinateLocalMassTransportPrimitive
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {a b c d : ℝ} (hab : a < b)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2) :
    deRhamDifferential (I := I) (M := U) (A := ℝ) 1
        (complexCoordinateLocalMassTransportPrimitive
          I U phi a b c d hab alpha) =
      alpha - complexCoordinateLocalTransportedMassTwoForm
        I U phi a b c d alpha := by
  rw [complexCoordinateLocalMassTransportPrimitive,
    deRhamDifferential_smoothFormsPullbackDiffeomorph,
    deRhamDifferential_complexPlanarMassTransportPrimitive,
    map_sub, complexCoordinateLocalTransportedMassTwoForm,
    complexPlanarTwoFormOfPlanarCoefficient,
    complexCoordinatePushforwardTwoForm,
    smoothFormsPullbackDiffeomorph_comp_symm]

/-- Pull the explicit planar primitive back to the original coordinate open
set. -/
noncomputable def complexCoordinateLocalPrimitive
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b c : ℝ) (hab : a ≤ b)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) :
    SmoothForms (I := I) (M := U) ℝ 1 :=
  smoothFormsPullbackDiffeomorph I SurfaceRealModel phi 1
    (complexPlanarPrimitiveOfTwoForm a b c hab
      (complexCoordinatePushforwardTwoForm I U phi alpha) ρ hρ)

omit [T2Space M] in
/-- The coordinate-local primitive differentiates to the original two-form. -/
theorem deRhamDifferential_complexCoordinateLocalPrimitive
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {a b c : ℝ} (hab : a ≤ b)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) :
    deRhamDifferential (I := I) (M := U) (A := ℝ) 1
        (complexCoordinateLocalPrimitive I U phi a b c hab alpha ρ hρ) =
      alpha := by
  rw [complexCoordinateLocalPrimitive,
    deRhamDifferential_smoothFormsPullbackDiffeomorph,
    deRhamDifferential_complexPlanarPrimitiveOfTwoForm,
    complexCoordinatePushforwardTwoForm,
    smoothFormsPullbackDiffeomorph_comp_symm]

/-- The inverse image of a closed coordinate rectangle in a complex
coordinate open set. -/
def complexCoordinateRectangleCore
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b c d : ℝ) : Set U :=
  phi ⁻¹' complexPlanarRectangleCore a b c d

omit [IsManifold I ∞ M] [T2Space M] in
/-- The inverse image of a closed coordinate rectangle is compact. -/
theorem complexCoordinateRectangleCore_isCompact
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b c d : ℝ) :
    IsCompact (complexCoordinateRectangleCore I U phi a b c d) := by
  exact phi.toHomeomorph.isCompact_preimage.2
    (complexPlanarRectangleCore_isCompact a b c d)

omit [IsManifold I ∞ M] [T2Space M] in
/-- Around any point of a full-plane coordinate chart there is a closed
coordinate rectangle whose ambient image lies in a prescribed open set. -/
theorem exists_complexCoordinateRectangleCore_subset_open
    (U V : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    (x : U) (hxV : (x : M) ∈ V) :
    ∃ ε : ℝ, 0 < ε ∧
      smoothFormCompactCore U
        (complexCoordinateRectangleCore I U phi
          ((Complex.equivRealProdCLM (phi x : ℂ)).1 - ε)
          ((Complex.equivRealProdCLM (phi x : ℂ)).1 + ε)
          ((Complex.equivRealProdCLM (phi x : ℂ)).2 - ε)
          ((Complex.equivRealProdCLM (phi x : ℂ)).2 + ε)) ⊆ V := by
  let fromCoord : ℝ × ℝ → M := fun p =>
    ((phi.symm
      (⟨Complex.equivRealProdCLM.symm p, trivial⟩ :
        complexPlanarModelOpen) : U) : M)
  have hfrom : Continuous fromCoord := by
    exact continuous_subtype_val.comp
      (phi.symm.continuous.comp
        (Complex.equivRealProdCLM.symm.continuous.subtype_mk _))
  let O : Set (ℝ × ℝ) := fromCoord ⁻¹' (V : Set M)
  have hO : IsOpen O := V.isOpen.preimage hfrom
  let p : ℝ × ℝ := Complex.equivRealProdCLM (phi x : ℂ)
  have hpO : p ∈ O := by
    change fromCoord p ∈ V
    have hp : Complex.equivRealProdCLM.symm p = (phi x : ℂ) := by
      exact Complex.equivRealProdCLM.symm_apply_apply (phi x : ℂ)
    dsimp [fromCoord]
    rw [hp]
    simpa using hxV
  rcases exists_closed_rectangle_subset_of_mem_open hO hpO with
    ⟨ε, hε, hrect⟩
  refine ⟨ε, hε, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hycoord : Complex.equivRealProdCLM (phi y : ℂ) ∈
      Icc (p.1 - ε) (p.1 + ε) ×ˢ Icc (p.2 - ε) (p.2 + ε) := by
    simpa [complexCoordinateRectangleCore, complexPlanarRectangleCore, p] using hy
  have hmemO := hrect hycoord
  change fromCoord (Complex.equivRealProdCLM (phi y : ℂ)) ∈ V at hmemO
  have hfromeq : fromCoord (Complex.equivRealProdCLM (phi y : ℂ)) = (y : M) := by
    dsimp [fromCoord]
    have hpair : Complex.equivRealProdCLM.symm
        (((phi y : ℂ).re), ((phi y : ℂ).im)) = (phi y : ℂ) :=
      Complex.equivRealProdCLM.symm_apply_apply (phi y : ℂ)
    rw [hpair]
    exact congrArg Subtype.val (phi.symm_apply_apply y)
  rwa [hfromeq] at hmemO

omit [T2Space M] in
/-- The coordinate mass-transport primitive is supported in the chosen
closed rectangle. -/
theorem complexCoordinateLocalMassTransportPrimitive_toFun_eq_zero_of_not_mem_rectangle
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (hfrect : tsupport (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) ⊆
      Ioo a b ×ˢ Ioo c d)
    (x : U) (hx : x ∉ complexCoordinateRectangleCore I U phi a b c d) :
    (complexCoordinateLocalMassTransportPrimitive
      I U phi a b c d hab alpha).toFun x = 0 := by
  have hplane :=
    complexPlanarMassTransportPrimitive_toFun_eq_zero_of_not_mem_rectangle
      hab hcd
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha))
      (planarCoefficientOfComplexTwoForm_contDiff
        (complexCoordinatePushforwardTwoForm I U phi alpha))
      hfrect (phi x) hx
  change ((complexPlanarMassTransportPrimitive a b c d hab
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha))
      _).toFun (phi x)).compContinuousLinearMap _ = 0
  rw [hplane]
  rfl

omit [T2Space M] in
/-- The normalized transported mass two-form is supported in the chosen
closed coordinate rectangle. -/
theorem complexCoordinateLocalTransportedMassTwoForm_toFun_eq_zero_of_not_mem_rectangle
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (x : U) (hx : x ∉ complexCoordinateRectangleCore I U phi a b c d) :
    (complexCoordinateLocalTransportedMassTwoForm
      I U phi a b c d alpha).toFun x = 0 := by
  have hplane :=
    complexPlanarTransportedMassTwoForm_toFun_eq_zero_of_not_mem_rectangle
      hab hcd
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha))
      (phi x) hx
  change ((complexPlanarTransportedMassTwoForm a b c d
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha))).toFun
      (phi x)).compContinuousLinearMap _ = 0
  rw [hplane]
  rfl

omit [T2Space M] in
/-- Rectangle support of the oriented coordinate coefficient implies
rectangle support of the original top-degree form. -/
theorem complexCoordinateTwoForm_toFun_eq_zero_of_coefficient_tsupport
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {a b c d : ℝ}
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (hfrect : tsupport (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) ⊆
      Ioo a b ×ˢ Ioo c d)
    (x : U) (hx : x ∉ complexCoordinateRectangleCore I U phi a b c d) :
    alpha.toFun x = 0 := by
  let omega := complexCoordinatePushforwardTwoForm I U phi alpha
  have hp : (((phi x : complexPlanarModelOpen) : ℂ).re,
      ((phi x : complexPlanarModelOpen) : ℂ).im) ∉
        tsupport (planarCoefficientOfComplexTwoForm omega) := by
    intro hp
    apply hx
    have hp' := hfrect hp
    exact ⟨Ioo_subset_Icc_self hp'.1, Ioo_subset_Icc_self hp'.2⟩
  have hcoeff : planarCoefficientOfComplexTwoForm omega
      (((phi x : complexPlanarModelOpen) : ℂ).re,
        ((phi x : complexPlanarModelOpen) : ℂ).im) = 0 :=
    image_eq_zero_of_notMem_tsupport hp
  have homega : omega.toFun (phi x) = 0 := by
    apply complexTopDegreeContinuousAlternatingMap_ext_basis
    change planarCoefficientOfComplexTwoForm omega
      (((phi x : complexPlanarModelOpen) : ℂ).re,
        ((phi x : complexPlanarModelOpen) : ℂ).im) = 0
    exact hcoeff
  have hrec := congrArg
    (fun theta : SmoothForms (I := I) (M := U) ℝ 2 ↦ theta.toFun x)
    (smoothFormsPullbackDiffeomorph_comp_symm
      I SurfaceRealModel phi alpha)
  change ((omega.toFun (phi x)).compContinuousLinearMap _) =
    alpha.toFun x at hrec
  rw [homega] at hrec
  simpa using hrec.symm

/-! ### Transport between two rectangles in one coordinate chart -/

/-- Pull back the explicit primitive which replaces the mass in an outer
coordinate rectangle by a normalized bump in an inner target rectangle. -/
noncomputable def complexCoordinateLocalMassTransportPrimitiveTo
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    (A B C D a b c d : ℝ) (hAB : A < B)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2) :
    SmoothForms (I := I) (M := U) ℝ 1 :=
  smoothFormsPullbackDiffeomorph I SurfaceRealModel phi 1
    (complexPlanarMassTransportPrimitiveTo A B C D a b c d hAB
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha))
      (planarCoefficientOfComplexTwoForm_contDiff
        (complexCoordinatePushforwardTwoForm I U phi alpha)))

/-- The normalized target bump of a two-rectangle coordinate transport. -/
noncomputable def complexCoordinateLocalTransportedMassTwoFormTo
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    (A B C D a b c d : ℝ)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2) :
    SmoothForms (I := I) (M := U) ℝ 2 :=
  smoothFormsPullbackDiffeomorph I SurfaceRealModel phi 2
    (complexPlanarTransportedMassTwoFormTo A B C D a b c d
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)))

omit [T2Space M] in
/-- In a coordinate chart, the two-rectangle transport primitive
differentiates to the original form minus its target bump. -/
theorem deRhamDifferential_complexCoordinateLocalMassTransportPrimitiveTo
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {A B C D a b c d : ℝ} (hAB : A < B)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2) :
    deRhamDifferential (I := I) (M := U) (A := ℝ) 1
        (complexCoordinateLocalMassTransportPrimitiveTo
          I U phi A B C D a b c d hAB alpha) =
      alpha - complexCoordinateLocalTransportedMassTwoFormTo
        I U phi A B C D a b c d alpha := by
  rw [complexCoordinateLocalMassTransportPrimitiveTo,
    deRhamDifferential_smoothFormsPullbackDiffeomorph,
    deRhamDifferential_complexPlanarMassTransportPrimitiveTo,
    map_sub, complexCoordinateLocalTransportedMassTwoFormTo,
    complexPlanarTwoFormOfPlanarCoefficient,
    complexCoordinatePushforwardTwoForm,
    smoothFormsPullbackDiffeomorph_comp_symm]

omit [T2Space M] in
/-- The pulled-back two-rectangle primitive vanishes off its outer
coordinate rectangle. -/
theorem complexCoordinateLocalMassTransportPrimitiveTo_toFun_eq_zero_of_not_mem_outer
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {A B C D a b c d : ℝ}
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hCc : C < c) (hcd : c < d) (hdD : d < D)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (hfrect : tsupport (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) ⊆
      Ioo A B ×ˢ Ioo C D)
    (x : U) (hx : x ∉ complexCoordinateRectangleCore I U phi A B C D) :
    (complexCoordinateLocalMassTransportPrimitiveTo I U phi
      A B C D a b c d ((hAa.trans hab).trans hbB) alpha).toFun x = 0 := by
  have hplane :=
    complexPlanarMassTransportPrimitiveTo_toFun_eq_zero_of_not_mem_outer
      hAa hab hbB hCc hcd hdD
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha))
      (planarCoefficientOfComplexTwoForm_contDiff
        (complexCoordinatePushforwardTwoForm I U phi alpha))
      hfrect (phi x) hx
  change ((complexPlanarMassTransportPrimitiveTo A B C D a b c d
      ((hAa.trans hab).trans hbB)
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha))
      _).toFun (phi x)).compContinuousLinearMap _ = 0
  rw [hplane]
  rfl

omit [T2Space M] in
/-- The target bump of a two-rectangle coordinate transport vanishes off
the target rectangle. -/
theorem complexCoordinateLocalTransportedMassTwoFormTo_toFun_eq_zero_of_not_mem_target
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {A B C D a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (x : U) (hx : x ∉ complexCoordinateRectangleCore I U phi a b c d) :
    (complexCoordinateLocalTransportedMassTwoFormTo
      I U phi A B C D a b c d alpha).toFun x = 0 := by
  have hplane :=
    complexPlanarTransportedMassTwoFormTo_toFun_eq_zero_of_not_mem_target
      (A := A) (B := B) (C := C) (D := D) hab hcd
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha))
      (phi x) hx
  change ((complexPlanarTransportedMassTwoFormTo A B C D a b c d
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha))).toFun
      (phi x)).compContinuousLinearMap _ = 0
  rw [hplane]
  rfl

omit [IsManifold I ∞ M] [T2Space M] in
/-- Strict containment of coordinate rectangles gives containment of their
closed inverse-image cores. -/
theorem complexCoordinateRectangleCore_target_subset_outer
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {A B C D a b c d : ℝ}
    (hAa : A < a) (hbB : b < B) (hCc : C < c) (hdD : d < D) :
    complexCoordinateRectangleCore I U phi a b c d ⊆
      complexCoordinateRectangleCore I U phi A B C D := by
  intro x hx
  exact ⟨⟨hAa.le.trans hx.1.1, hx.1.2.trans hbB.le⟩,
    ⟨hCc.le.trans hx.2.1, hx.2.2.trans hdD.le⟩⟩

/-- Extend a two-rectangle coordinate transport primitive by zero to the
ambient surface. -/
noncomputable def complexCoordinateGlobalMassTransportPrimitiveTo
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {A B C D a b c d : ℝ}
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hCc : C < c) (hcd : c < d) (hdD : d < D)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (hfrect : tsupport (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) ⊆
      Ioo A B ×ˢ Ioo C D) :
    SmoothForms (I := I) (M := M) ℝ 1 :=
  smoothFormCompactZeroExtension I U
    (complexCoordinateRectangleCore I U phi A B C D)
    (complexCoordinateRectangleCore_isCompact I U phi A B C D)
    (complexCoordinateLocalMassTransportPrimitiveTo I U phi
      A B C D a b c d ((hAa.trans hab).trans hbB) alpha)
    (complexCoordinateLocalMassTransportPrimitiveTo_toFun_eq_zero_of_not_mem_outer
      I U phi hAa hab hbB hCc hcd hdD alpha hfrect)

/-- A global coordinate transport primitive vanishes outside its coordinate
open set. -/
theorem complexCoordinateGlobalMassTransportPrimitiveTo_toFun_eq_zero_of_not_mem_chart
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {A B C D a b c d : ℝ}
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hCc : C < c) (hcd : c < d) (hdD : d < D)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (hfrect : tsupport (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) ⊆
      Ioo A B ×ˢ Ioo C D)
    (x : M) (hx : x ∉ U) :
    (complexCoordinateGlobalMassTransportPrimitiveTo
      I U phi hAa hab hbB hCc hcd hdD alpha hfrect).toFun x = 0 := by
  apply smoothFormCompactZeroExtension_toFun_eq_zero_of_not_mem_core
    (alpha := complexCoordinateLocalMassTransportPrimitiveTo I U phi
      A B C D a b c d ((hAa.trans hab).trans hbB) alpha)
    I U (complexCoordinateRectangleCore I U phi A B C D)
      (complexCoordinateRectangleCore_isCompact I U phi A B C D)
      (complexCoordinateLocalMassTransportPrimitiveTo_toFun_eq_zero_of_not_mem_outer
        I U phi hAa hab hbB hCc hcd hdD alpha hfrect) x
  intro hcore
  exact hx (smoothFormCompactCore_subset U
    (complexCoordinateRectangleCore I U phi A B C D) hcore)

/-- Extend the target bump of a two-rectangle coordinate transport by zero
to the ambient surface. -/
noncomputable def complexCoordinateGlobalTransportedMassTwoFormTo
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {A B C D a b c d : ℝ}
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hCc : C < c) (hcd : c < d) (hdD : d < D)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2) :
    SmoothForms (I := I) (M := M) ℝ 2 :=
  smoothFormCompactZeroExtension I U
    (complexCoordinateRectangleCore I U phi A B C D)
    (complexCoordinateRectangleCore_isCompact I U phi A B C D)
    (complexCoordinateLocalTransportedMassTwoFormTo
      I U phi A B C D a b c d alpha)
    (fun x hx ↦
      complexCoordinateLocalTransportedMassTwoFormTo_toFun_eq_zero_of_not_mem_target
        I U phi hab hcd alpha x
        (fun htarget => hx
          (complexCoordinateRectangleCore_target_subset_outer
            I U phi hAa hbB hCc hdD htarget)))

/-- The ambient target bump of a two-rectangle coordinate transport vanishes
outside the ambient image of its target rectangle. -/
theorem complexCoordinateGlobalTransportedMassTwoFormTo_toFun_eq_zero_of_not_mem_target
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {A B C D a b c d : ℝ}
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hCc : C < c) (hcd : c < d) (hdD : d < D)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (x : M)
    (hx : x ∉ smoothFormCompactCore U
      (complexCoordinateRectangleCore I U phi a b c d)) :
    (complexCoordinateGlobalTransportedMassTwoFormTo
      I U phi hAa hab hbB hCc hcd hdD alpha).toFun x = 0 := by
  let K := complexCoordinateRectangleCore I U phi A B C D
  let beta := complexCoordinateLocalTransportedMassTwoFormTo
    I U phi A B C D a b c d alpha
  let hbeta : ∀ y : U, y ∉ K → beta.toFun y = 0 := fun y hy ↦
    complexCoordinateLocalTransportedMassTwoFormTo_toFun_eq_zero_of_not_mem_target
      I U phi hab hcd alpha y
      (fun htarget => hy
        (complexCoordinateRectangleCore_target_subset_outer
          I U phi hAa hbB hCc hdD htarget))
  by_cases hxU : x ∈ U
  · let xU : U := ⟨x, hxU⟩
    have hxTarget : xU ∉
        complexCoordinateRectangleCore I U phi a b c d := by
      intro htarget
      exact hx ⟨xU, htarget, rfl⟩
    have hlocalzero : beta.toFun xU = 0 :=
      complexCoordinateLocalTransportedMassTwoFormTo_toFun_eq_zero_of_not_mem_target
        I U phi hab hcd alpha xU hxTarget
    have hres := smoothFormCompactZeroExtension_restrict
      I U K (complexCoordinateRectangleCore_isCompact I U phi A B C D)
      beta hbeta
    have hpoint := congrArg
      (fun omega : SmoothForms (I := I) (M := U) ℝ 2 => omega.toFun xU)
      hres
    change
      ((complexCoordinateGlobalTransportedMassTwoFormTo
        I U phi hAa hab hbB hCc hcd hdD alpha).toFun x).compContinuousLinearMap
          (mfderiv I I (fun y : U => (y : M)) xU) = beta.toFun xU at hpoint
    rw [hlocalzero] at hpoint
    exact continuousAlternatingMap_compContinuousLinearMap_injective
      (mfderiv I I (fun y : U => (y : M)) xU)
      (mfderiv_subtypeVal_surjective (I := I) U xU) hpoint
  · apply smoothFormCompactZeroExtension_toFun_eq_zero_of_not_mem_core
      (alpha := beta)
      I U K (complexCoordinateRectangleCore_isCompact I U phi A B C D)
      hbeta x
    intro hxK
    exact hxU (smoothFormCompactCore_subset U K hxK)

/-- One global two-rectangle coordinate transport has derivative equal to
the original extension by zero minus the normalized target bump. -/
theorem deRhamDifferential_complexCoordinateGlobalMassTransportPrimitiveTo
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {A B C D a b c d : ℝ}
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hCc : C < c) (hcd : c < d) (hdD : d < D)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (hfrect : tsupport (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) ⊆
      Ioo A B ×ˢ Ioo C D) :
    deRhamDifferential (I := I) (M := M) (A := ℝ) 1
        (complexCoordinateGlobalMassTransportPrimitiveTo
          I U phi hAa hab hbB hCc hcd hdD alpha hfrect) =
      smoothFormCompactZeroExtension I U
          (complexCoordinateRectangleCore I U phi A B C D)
          (complexCoordinateRectangleCore_isCompact I U phi A B C D)
          alpha
          (complexCoordinateTwoForm_toFun_eq_zero_of_coefficient_tsupport
            I U phi alpha hfrect) -
        complexCoordinateGlobalTransportedMassTwoFormTo
          I U phi hAa hab hbB hCc hcd hdD alpha := by
  let K := complexCoordinateRectangleCore I U phi A B C D
  let hK := complexCoordinateRectangleCore_isCompact I U phi A B C D
  let eta := complexCoordinateLocalMassTransportPrimitiveTo I U phi
    A B C D a b c d ((hAa.trans hab).trans hbB) alpha
  let beta := complexCoordinateLocalTransportedMassTwoFormTo
    I U phi A B C D a b c d alpha
  let heta : ∀ x : U, x ∉ K → eta.toFun x = 0 :=
    complexCoordinateLocalMassTransportPrimitiveTo_toFun_eq_zero_of_not_mem_outer
      I U phi hAa hab hbB hCc hcd hdD alpha hfrect
  let hbeta : ∀ x : U, x ∉ K → beta.toFun x = 0 := fun x hx ↦
    complexCoordinateLocalTransportedMassTwoFormTo_toFun_eq_zero_of_not_mem_target
      I U phi hab hcd alpha x
      (fun htarget => hx
        (complexCoordinateRectangleCore_target_subset_outer
          I U phi hAa hbB hCc hdD htarget))
  let halpha : ∀ x : U, x ∉ K → alpha.toFun x = 0 :=
    complexCoordinateTwoForm_toFun_eq_zero_of_coefficient_tsupport
      I U phi alpha hfrect
  rw [complexCoordinateGlobalMassTransportPrimitiveTo,
    deRhamDifferential_smoothFormCompactZeroExtension]
  calc
    smoothFormCompactZeroExtension I U K hK
        (deRhamDifferential (I := I) (M := U) (A := ℝ) 1 eta)
        (deRhamDifferential_toFun_eq_zero_of_not_mem_compact
          I U K hK eta heta) =
      smoothFormCompactZeroExtension I U K hK (alpha - beta)
        (fun x hx ↦ by
          change alpha.toFun x - beta.toFun x = 0
          rw [halpha x hx, hbeta x hx, sub_self]) := by
            apply smoothFormCompactZeroExtension_congr I U K hK
            exact deRhamDifferential_complexCoordinateLocalMassTransportPrimitiveTo
              I U phi ((hAa.trans hab).trans hbB) alpha
    _ = smoothFormCompactZeroExtension I U K hK alpha halpha -
          smoothFormCompactZeroExtension I U K hK beta hbeta :=
      smoothFormCompactZeroExtension_sub I U K hK alpha beta halpha hbeta
    _ = _ := rfl

/-- If the input is the restriction of an ambient form supported in the
outer rectangle, a coordinate transport step has derivative equal to that
ambient form minus the target bump. -/
theorem deRhamDifferential_complexCoordinateGlobalMassTransportPrimitiveTo_restrict
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {A B C D a b c d : ℝ}
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hCc : C < c) (hcd : c < d) (hdD : d < D)
    (omega : SmoothForms (I := I) (M := M) ℝ 2)
    (hzero : ∀ x : M,
      x ∉ smoothFormCompactCore U
        (complexCoordinateRectangleCore I U phi A B C D) →
      omega.toFun x = 0)
    (hfrect : tsupport (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi
          (restrictSmoothFormsToOpen (I := I) (A := ℝ) U 2 omega))) ⊆
      Ioo A B ×ˢ Ioo C D) :
    deRhamDifferential (I := I) (M := M) (A := ℝ) 1
        (complexCoordinateGlobalMassTransportPrimitiveTo I U phi
          hAa hab hbB hCc hcd hdD
          (restrictSmoothFormsToOpen (I := I) (A := ℝ) U 2 omega) hfrect) =
      omega - complexCoordinateGlobalTransportedMassTwoFormTo I U phi
          hAa hab hbB hCc hcd hdD
          (restrictSmoothFormsToOpen (I := I) (A := ℝ) U 2 omega) := by
  rw [deRhamDifferential_complexCoordinateGlobalMassTransportPrimitiveTo]
  rw [smoothFormCompactZeroExtension_restrict_eq_self
    I U (complexCoordinateRectangleCore I U phi A B C D)
    (complexCoordinateRectangleCore_isCompact I U phi A B C D)
    omega hzero]

/-- Any ambient two-form supported in a compact subset of a full-plane chart
can be moved, modulo an exact form, into an arbitrary nondegenerate
coordinate rectangle in that chart. -/
theorem exists_compactSupport_transport_to_coordinateRectangle
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    (K : Set U) (hK : IsCompact K)
    (omega : SmoothForms (I := I) (M := M) ℝ 2)
    (hzero : ∀ x : M, x ∉ smoothFormCompactCore U K → omega.toFun x = 0)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ∃ (eta : SmoothForms (I := I) (M := M) ℝ 1)
        (beta : SmoothForms (I := I) (M := M) ℝ 2),
      deRhamDifferential (I := I) (M := M) (A := ℝ) 1 eta = omega - beta ∧
      (∀ x : M, x ∉ U → eta.toFun x = 0) ∧
      ∀ x : M,
        x ∉ smoothFormCompactCore U
          (complexCoordinateRectangleCore I U phi a b c d) →
        beta.toFun x = 0 := by
  let alpha := restrictSmoothFormsToOpen (I := I) (A := ℝ) U 2 omega
  have halpha : ∀ x : U, x ∉ K → alpha.toFun x = 0 := by
    intro x hx
    apply restrictSmoothFormsToOpen_toFun_eq_zero_of_ambient_eq_zero I
    apply hzero
    intro hcore
    obtain ⟨y, hyK, hyx⟩ := hcore
    apply hx
    have hy : y = x := Subtype.ext hyx
    simpa [hy] using hyK
  let coord : U → ℝ × ℝ := fun x =>
    Complex.equivRealProdCLM (phi x : ℂ)
  have hcoord : Continuous coord := by
    fun_prop
  have hcoordK : IsCompact (coord '' K) := hK.image hcoord
  obtain ⟨R, hR, hKrect⟩ :=
    exists_open_rectangle_containing_compact hcoordK
  let T := max (max |a| |b|) (max |c| |d|)
  let S := max R T + 1
  have hRS : R < S :=
    (le_max_left R T).trans_lt (lt_add_one (max R T))
  have haS : |a| < S := by
    calc
      |a| ≤ max |a| |b| := le_max_left _ _
      _ ≤ T := le_max_left _ _
      _ ≤ max R T := le_max_right _ _
      _ < S := lt_add_one _
  have hbS : |b| < S := by
    calc
      |b| ≤ max |a| |b| := le_max_right _ _
      _ ≤ T := le_max_left _ _
      _ ≤ max R T := le_max_right _ _
      _ < S := lt_add_one _
  have hcS : |c| < S := by
    calc
      |c| ≤ max |c| |d| := le_max_left _ _
      _ ≤ T := le_max_right _ _
      _ ≤ max R T := le_max_right _ _
      _ < S := lt_add_one _
  have hdS : |d| < S := by
    calc
      |d| ≤ max |c| |d| := le_max_right _ _
      _ ≤ T := le_max_right _ _
      _ ≤ max R T := le_max_right _ _
      _ < S := lt_add_one _
  have hAa : -S < a := (neg_lt_neg haS).trans_le (neg_abs_le a)
  have hbB : b < S := (le_abs_self b).trans_lt hbS
  have hCc : -S < c := (neg_lt_neg hcS).trans_le (neg_abs_le c)
  have hdD : d < S := (le_abs_self d).trans_lt hdS
  have hfrect : tsupport (planarCoefficientOfComplexTwoForm
      (complexCoordinatePushforwardTwoForm I U phi alpha)) ⊆
      Ioo (-S) S ×ˢ Ioo (-S) S := by
    intro p hp
    have hpK :=
      planarCoefficientOf_complexCoordinatePushforwardTwoForm_tsupport_subset_image
        I U phi alpha K hK halpha hp
    have hpR := hKrect hpK
    exact ⟨⟨(neg_lt_neg hRS).trans hpR.1.1, hpR.1.2.trans hRS⟩,
      ⟨(neg_lt_neg hRS).trans hpR.2.1, hpR.2.2.trans hRS⟩⟩
  have hzeroOuter : ∀ x : M,
      x ∉ smoothFormCompactCore U
        (complexCoordinateRectangleCore I U phi (-S) S (-S) S) →
      omega.toFun x = 0 := by
    intro x hxOuter
    apply hzero x
    intro hxK
    obtain ⟨y, hyK, hyx⟩ := hxK
    apply hxOuter
    refine ⟨y, ?_, hyx⟩
    have hyR : coord y ∈ Ioo (-R) R ×ˢ Ioo (-R) R :=
      hKrect ⟨y, hyK, rfl⟩
    change Complex.equivRealProdCLM (phi y : ℂ) ∈
      Icc (-S) S ×ˢ Icc (-S) S
    exact ⟨⟨((neg_lt_neg hRS).trans hyR.1.1).le,
      (hyR.1.2.trans hRS).le⟩,
      ⟨((neg_lt_neg hRS).trans hyR.2.1).le,
      (hyR.2.2.trans hRS).le⟩⟩
  let eta := complexCoordinateGlobalMassTransportPrimitiveTo I U phi
    hAa hab hbB hCc hcd hdD alpha hfrect
  let beta := complexCoordinateGlobalTransportedMassTwoFormTo I U phi
    hAa hab hbB hCc hcd hdD alpha
  refine ⟨eta, beta, ?_, ?_, ?_⟩
  · exact deRhamDifferential_complexCoordinateGlobalMassTransportPrimitiveTo_restrict
      I U phi hAa hab hbB hCc hcd hdD omega hzeroOuter hfrect
  · exact complexCoordinateGlobalMassTransportPrimitiveTo_toFun_eq_zero_of_not_mem_chart
      I U phi hAa hab hbB hCc hcd hdD alpha hfrect
  · exact complexCoordinateGlobalTransportedMassTwoFormTo_toFun_eq_zero_of_not_mem_target
      I U phi hAa hab hbB hCc hcd hdD alpha

/-- If two coordinate opens overlap, a compactly supported two-form in the
first can be moved, modulo an exact form, to a compact support core in the
second. -/
theorem exists_compactSupport_transport_across_coordinate_overlap
    (U V : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    (K : Set U) (hK : IsCompact K)
    (omega : SmoothForms (I := I) (M := M) ℝ 2)
    (hzero : ∀ x : M, x ∉ smoothFormCompactCore U K → omega.toFun x = 0)
    (x : U) (hxV : (x : M) ∈ V) :
    ∃ (eta : SmoothForms (I := I) (M := M) ℝ 1)
        (beta : SmoothForms (I := I) (M := M) ℝ 2)
        (K' : Set V),
      IsCompact K' ∧
      deRhamDifferential (I := I) (M := M) (A := ℝ) 1 eta = omega - beta ∧
      (∀ y : M, y ∉ U → eta.toFun y = 0) ∧
      ∀ y : M, y ∉ smoothFormCompactCore V K' → beta.toFun y = 0 := by
  obtain ⟨ε, hε, htargetV⟩ :=
    exists_complexCoordinateRectangleCore_subset_open I U V phi x hxV
  let p : ℝ × ℝ := Complex.equivRealProdCLM (phi x : ℂ)
  let a := p.1 - ε
  let b := p.1 + ε
  let c := p.2 - ε
  let d := p.2 + ε
  have hab : a < b := by dsimp [a, b]; linarith
  have hcd : c < d := by dsimp [c, d]; linarith
  obtain ⟨eta, beta, hd, heta, hbeta⟩ :=
    exists_compactSupport_transport_to_coordinateRectangle
      I U phi K hK omega hzero hab hcd
  let targetK := complexCoordinateRectangleCore I U phi a b c d
  let C := smoothFormCompactCore U targetK
  have hCV : C ⊆ V := by
    simpa [C, targetK, a, b, c, d, p] using htargetV
  have hCcompact : IsCompact C :=
    smoothFormCompactCore_isCompact U targetK
      (complexCoordinateRectangleCore_isCompact I U phi a b c d)
  let K' := smoothFormCompactCoreInOpen V C
  have hK' : IsCompact K' :=
    smoothFormCompactCoreInOpen_isCompact V C hCcompact hCV
  refine ⟨eta, beta, K', hK', hd, heta, ?_⟩
  intro y hy
  apply hbeta y
  intro hyTarget
  apply hy
  rw [show smoothFormCompactCore V K' = C by
    exact smoothFormCompactCore_coreInOpen V C hCV]
  exact hyTarget

/-- Along a finite chain of overlapping full-plane coordinate opens, a
compactly supported two-form can be moved, modulo an exact form, from the
first chart to a compact support core in the last chart. -/
theorem exists_compactSupport_transport_along_finite_coordinateChain
    (W : TopologicalSpace.Opens M)
    (U : ℕ → TopologicalSpace.Opens M)
    (phi : ∀ n : ℕ,
      U n ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    (hoverlap : ∀ n : ℕ, ∃ x : U n, (x : M) ∈ U (n + 1))
    (hUW : ∀ n : ℕ, U n ≤ W)
    (K : Set (U 0)) (hK : IsCompact K)
    (omega : SmoothForms (I := I) (M := M) ℝ 2)
    (hzero : ∀ x : M, x ∉ smoothFormCompactCore (U 0) K → omega.toFun x = 0)
    (n : ℕ) :
    ∃ (eta : SmoothForms (I := I) (M := M) ℝ 1)
        (beta : SmoothForms (I := I) (M := M) ℝ 2)
        (Kn : Set (U n)),
      IsCompact Kn ∧
      deRhamDifferential (I := I) (M := M) (A := ℝ) 1 eta = omega - beta ∧
      (∀ x : M, x ∉ W → eta.toFun x = 0) ∧
      ∀ x : M, x ∉ smoothFormCompactCore (U n) Kn → beta.toFun x = 0 := by
  induction n with
  | zero =>
      refine ⟨0, omega, K, hK, ?_, ?_, hzero⟩
      · rw [sub_self]
        exact LinearMap.map_zero _
      · intro x _hx
        rfl
  | succ n ih =>
      obtain ⟨eta, beta, Kn, hKn, hd, heta, hbeta⟩ := ih
      obtain ⟨x, hx⟩ := hoverlap n
      obtain ⟨etaStep, betaNext, Knext, hKnext, hdStep, hetaStep,
          hbetaNext⟩ :=
        exists_compactSupport_transport_across_coordinate_overlap
          I (U n) (U (n + 1)) (phi n) Kn hKn beta hbeta x hx
      refine ⟨eta + etaStep, betaNext, Knext, hKnext, ?_, ?_, hbetaNext⟩
      · rw [map_add, hd, hdStep]
        abel
      · intro y hyW
        change eta.toFun y + etaStep.toFun y = 0
        rw [heta y hyW, hetaStep y (fun hyUn => hyW (hUW n hyUn)), zero_add]

/-! ## Finite transport along a path -/

/-- A path in an open corridor supplies a finite chain of coordinate
transports.  The final compact support can be placed in an arbitrary target
open set containing the endpoint, while remaining inside the corridor. -/
theorem exists_compactSupport_transport_along_path
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    (W Z U0 : TopologicalSpace.Opens X)
    (phi0 : U0 ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    {x0 x1 : X} (gamma : Path x0 x1)
    (hgammaW : ∀ t : unitInterval, gamma t ∈ W)
    (hx1Z : x1 ∈ Z)
    (hx0U : x0 ∈ U0)
    (hU0W : U0 ≤ W)
    (K : Set U0) (hK : IsCompact K)
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2)
    (hzero : ∀ x : X, x ∉ smoothFormCompactCore U0 K → omega.toFun x = 0) :
    ∃ (eta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1)
        (beta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2)
        (V : TopologicalSpace.Opens X) (KV : Set V),
      x1 ∈ V ∧ V ≤ W ⊓ Z ∧
      Nonempty (V ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen) ∧
      IsCompact KV ∧
      deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1 eta =
        omega - beta ∧
      (∀ x : X, x ∉ W → eta.toFun x = 0) ∧
      ∀ x : X, x ∉ smoothFormCompactCore V KV → beta.toFun x = 0 := by
  classical
  let chartOpen : unitInterval → TopologicalSpace.Opens X := fun t =>
    Classical.choose
      (exists_complexPlanarChart_subordinate W (gamma t) (hgammaW t))
  have hgammaChart : ∀ t : unitInterval, gamma t ∈ chartOpen t := fun t =>
    (Classical.choose_spec
      (exists_complexPlanarChart_subordinate W (gamma t) (hgammaW t))).1
  have hchartW : ∀ t : unitInterval, chartOpen t ≤ W := fun t =>
    (Classical.choose_spec
      (exists_complexPlanarChart_subordinate W (gamma t) (hgammaW t))).2.1
  let chartPhi : ∀ t : unitInterval,
      chartOpen t ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯
        complexPlanarModelOpen := fun t =>
    Classical.choice
      (Classical.choose_spec
        (exists_complexPlanarChart_subordinate W (gamma t) (hgammaW t))).2.2
  let cover : unitInterval → Set unitInterval := fun t =>
    gamma ⁻¹' (chartOpen t : Set X)
  have hcoverOpen : ∀ t : unitInterval, IsOpen (cover t) := fun t =>
    (chartOpen t).isOpen.preimage gamma.continuous
  have hcover : univ ⊆ ⋃ t, cover t := by
    intro s _hs
    exact mem_iUnion.2 ⟨s, hgammaChart s⟩
  obtain ⟨time, htime0, htimeMono, ⟨m, htimeOne⟩, hinterval⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcoverOpen hcover
  let index : ℕ → unitInterval := fun n => Classical.choose (hinterval n)
  have hsub : ∀ n : ℕ,
      Icc (time n) (time (n + 1)) ⊆ cover (index n) := fun n =>
    Classical.choose_spec (hinterval n)
  let chainU : ℕ → TopologicalSpace.Opens X
    | 0 => U0
    | n + 1 => chartOpen (index n)
  let chainPhi : ∀ n : ℕ,
      chainU n ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen
    | 0 => phi0
    | n + 1 => chartPhi (index n)
  have hoverlap : ∀ n : ℕ, ∃ x : chainU n, (x : X) ∈ chainU (n + 1) := by
    intro n
    cases n with
    | zero =>
        refine ⟨⟨x0, hx0U⟩, ?_⟩
        change x0 ∈ chartOpen (index 0)
        have hmem := hsub 0
          (show time 0 ∈ Icc (time 0) (time (0 + 1)) from
            ⟨le_rfl, htimeMono (Nat.zero_le 1)⟩)
        change gamma (time 0) ∈ chartOpen (index 0) at hmem
        rw [htime0] at hmem
        simpa using hmem
    | succ n =>
        have hleft : gamma (time (n + 1)) ∈ chartOpen (index n) := by
          exact hsub n ⟨htimeMono (Nat.le_succ n), le_rfl⟩
        have hright : gamma (time (n + 1)) ∈ chartOpen (index (n + 1)) := by
          exact hsub (n + 1) ⟨le_rfl, htimeMono (Nat.le_succ (n + 1))⟩
        exact ⟨⟨gamma (time (n + 1)), hleft⟩, hright⟩
  have hchainUW : ∀ n : ℕ, chainU n ≤ W := by
    intro n
    cases n with
    | zero => exact hU0W
    | succ n => exact hchartW (index n)
  obtain ⟨eta, beta, Km, hKm, hd, heta, hbeta⟩ :=
    exists_compactSupport_transport_along_finite_coordinateChain
      SurfaceRealModel W chainU chainPhi hoverlap hchainUW
      K hK omega hzero (m + 1)
  have hx1W : x1 ∈ W := by simpa using hgammaW 1
  have hx1WZ : x1 ∈ (W ⊓ Z : TopologicalSpace.Opens X) := ⟨hx1W, hx1Z⟩
  obtain ⟨Vend, hx1Vend, hVendWZ, hphiEnd⟩ :=
    exists_complexPlanarChart_subordinate (W ⊓ Z) x1 hx1WZ
  let phiEnd : Vend ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯
      complexPlanarModelOpen := Classical.choice hphiEnd
  have hx1Selected : x1 ∈ chainU (m + 1) := by
    change x1 ∈ chartOpen (index m)
    have hm : time m = 1 := htimeOne m le_rfl
    have hm1 : time (m + 1) = 1 := htimeOne (m + 1) (Nat.le_succ m)
    have hmem := hsub m
      (show (1 : unitInterval) ∈ Icc (time m) (time (m + 1)) by
        rw [hm, hm1]
        exact ⟨le_rfl, le_rfl⟩)
    change gamma 1 ∈ chartOpen (index m) at hmem
    simpa using hmem
  obtain ⟨etaEnd, betaEnd, Kend, hKend, hdEnd, hetaEnd, hbetaEnd⟩ :=
    exists_compactSupport_transport_across_coordinate_overlap
      SurfaceRealModel (chainU (m + 1)) Vend (chainPhi (m + 1))
      Km hKm beta hbeta ⟨x1, hx1Selected⟩ hx1Vend
  refine ⟨eta + etaEnd, betaEnd, Vend, Kend, hx1Vend, hVendWZ, ⟨phiEnd⟩,
    hKend, ?_, ?_, hbetaEnd⟩
  · rw [map_add, hd, hdEnd]
    abel
  · intro y hyW
    change eta.toFun y + etaEnd.toFun y = 0
    rw [heta y hyW,
      hetaEnd y (fun hySelected => hyW (hchainUW (m + 1) hySelected)), zero_add]

/-- Extend the coordinate mass-transport primitive by zero to the ambient
manifold. -/
noncomputable def complexCoordinateGlobalMassTransportPrimitive
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (hfrect : tsupport (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) ⊆
      Ioo a b ×ˢ Ioo c d) :
    SmoothForms (I := I) (M := M) ℝ 1 :=
  smoothFormCompactZeroExtension I U
    (complexCoordinateRectangleCore I U phi a b c d)
    (complexCoordinateRectangleCore_isCompact I U phi a b c d)
    (complexCoordinateLocalMassTransportPrimitive
      I U phi a b c d hab alpha)
    (complexCoordinateLocalMassTransportPrimitive_toFun_eq_zero_of_not_mem_rectangle
      I U phi hab hcd alpha hfrect)

/-- Extend the normalized transported mass two-form by zero to the ambient
manifold. -/
noncomputable def complexCoordinateGlobalTransportedMassTwoForm
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2) :
    SmoothForms (I := I) (M := M) ℝ 2 :=
  smoothFormCompactZeroExtension I U
    (complexCoordinateRectangleCore I U phi a b c d)
    (complexCoordinateRectangleCore_isCompact I U phi a b c d)
    (complexCoordinateLocalTransportedMassTwoForm
      I U phi a b c d alpha)
    (complexCoordinateLocalTransportedMassTwoForm_toFun_eq_zero_of_not_mem_rectangle
      I U phi hab hcd alpha)

/-- One coordinate mass-transport step gives a global primitive of the
original compactly supported two-form minus its normalized replacement. -/
theorem deRhamDifferential_complexCoordinateGlobalMassTransportPrimitive
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (hfrect : tsupport (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) ⊆
      Ioo a b ×ˢ Ioo c d) :
    deRhamDifferential (I := I) (M := M) (A := ℝ) 1
        (complexCoordinateGlobalMassTransportPrimitive
          I U phi hab hcd alpha hfrect) =
      smoothFormCompactZeroExtension I U
          (complexCoordinateRectangleCore I U phi a b c d)
          (complexCoordinateRectangleCore_isCompact I U phi a b c d)
          alpha
          (complexCoordinateTwoForm_toFun_eq_zero_of_coefficient_tsupport
            I U phi alpha hfrect) -
        complexCoordinateGlobalTransportedMassTwoForm
          I U phi hab hcd alpha := by
  let K := complexCoordinateRectangleCore I U phi a b c d
  let hK := complexCoordinateRectangleCore_isCompact I U phi a b c d
  let eta := complexCoordinateLocalMassTransportPrimitive
    I U phi a b c d hab alpha
  let beta := complexCoordinateLocalTransportedMassTwoForm
    I U phi a b c d alpha
  let heta : ∀ x : U, x ∉ K → eta.toFun x = 0 :=
    complexCoordinateLocalMassTransportPrimitive_toFun_eq_zero_of_not_mem_rectangle
      I U phi hab hcd alpha hfrect
  let hbeta : ∀ x : U, x ∉ K → beta.toFun x = 0 :=
    complexCoordinateLocalTransportedMassTwoForm_toFun_eq_zero_of_not_mem_rectangle
      I U phi hab hcd alpha
  let halpha : ∀ x : U, x ∉ K → alpha.toFun x = 0 :=
    complexCoordinateTwoForm_toFun_eq_zero_of_coefficient_tsupport
      I U phi alpha hfrect
  rw [complexCoordinateGlobalMassTransportPrimitive,
    deRhamDifferential_smoothFormCompactZeroExtension]
  calc
    smoothFormCompactZeroExtension I U K hK
        (deRhamDifferential (I := I) (M := U) (A := ℝ) 1 eta)
        (deRhamDifferential_toFun_eq_zero_of_not_mem_compact
          I U K hK eta heta) =
      smoothFormCompactZeroExtension I U K hK (alpha - beta)
        (fun x hx ↦ by
          change alpha.toFun x - beta.toFun x = 0
          rw [halpha x hx, hbeta x hx, sub_self]) := by
            apply smoothFormCompactZeroExtension_congr I U K hK
            exact
              deRhamDifferential_complexCoordinateLocalMassTransportPrimitive
                I U phi hab alpha
    _ = smoothFormCompactZeroExtension I U K hK alpha halpha -
          smoothFormCompactZeroExtension I U K hK beta hbeta :=
      smoothFormCompactZeroExtension_sub I U K hK alpha beta halpha hbeta
    _ = _ := rfl

omit [T2Space M] in
/-- Under the rectangle support and zero-total-mass hypotheses, the local
primitive vanishes outside the coordinate rectangle. -/
theorem complexCoordinateLocalPrimitive_toFun_eq_zero_of_not_mem_rectangle
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (ρ : ℝ → ℝ)
    (hfrect : tsupport (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) ⊆
      Set.Ioo a b ×ˢ Set.Ioo c d)
    (hρ : ContDiff ℝ ∞ ρ)
    (hρsupport : tsupport ρ ⊆ Set.Ioo a b)
    (hρone : ∫ x in a..b, ρ x = 1)
    (htotal : ∫ y in c..d, planarHorizontalMarginal a b
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) y = 0)
    (x : U) (hx : x ∉ complexCoordinateRectangleCore I U phi a b c d) :
    (complexCoordinateLocalPrimitive I U phi a b c hab.le alpha ρ hρ).toFun x =
      0 := by
  let omega := complexCoordinatePushforwardTwoForm I U phi alpha
  have hfc : HasCompactSupport (planarCoefficientOfComplexTwoForm omega) := by
    apply IsCompact.of_isClosed_subset
      (isCompact_Icc.prod isCompact_Icc)
      (isClosed_tsupport (planarCoefficientOfComplexTwoForm omega))
    exact hfrect.trans
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hplane :=
    complexPlanarPrimitiveOfTwoForm_toFun_eq_zero_of_not_mem_rectangle
      hab hcd omega ρ hfc hfrect hρ hρsupport hρone htotal (phi x) hx
  change ((complexPlanarPrimitiveOfTwoForm a b c hab.le omega ρ hρ).toFun
      (phi x)).compContinuousLinearMap _ = 0
  rw [hplane]
  rfl

/-- The original two-form also vanishes outside the coordinate rectangle,
because it is the derivative of the supported local primitive. -/
theorem complexCoordinateTwoForm_toFun_eq_zero_of_not_mem_rectangle
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (ρ : ℝ → ℝ)
    (hfrect : tsupport (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) ⊆
      Set.Ioo a b ×ˢ Set.Ioo c d)
    (hρ : ContDiff ℝ ∞ ρ)
    (hρsupport : tsupport ρ ⊆ Set.Ioo a b)
    (hρone : ∫ x in a..b, ρ x = 1)
    (htotal : ∫ y in c..d, planarHorizontalMarginal a b
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) y = 0)
    (x : U) (hx : x ∉ complexCoordinateRectangleCore I U phi a b c d) :
    alpha.toFun x = 0 := by
  let eta := complexCoordinateLocalPrimitive
    I U phi a b c hab.le alpha ρ hρ
  have heta : ∀ z : U,
      z ∉ complexCoordinateRectangleCore I U phi a b c d →
        eta.toFun z = 0 :=
    complexCoordinateLocalPrimitive_toFun_eq_zero_of_not_mem_rectangle
      I U phi hab hcd alpha ρ hfrect hρ hρsupport hρone htotal
  have hdeta := deRhamDifferential_toFun_eq_zero_of_not_mem_compact
    I U (complexCoordinateRectangleCore I U phi a b c d)
      (complexCoordinateRectangleCore_isCompact I U phi a b c d)
      eta heta x hx
  rw [show deRhamDifferential (I := I) (M := U) (A := ℝ) 1 eta = alpha by
    exact deRhamDifferential_complexCoordinateLocalPrimitive
      I U phi hab.le alpha ρ hρ] at hdeta
  exact hdeta

/-- The global one-form obtained by extending the coordinate-local primitive
by zero. -/
noncomputable def complexCoordinateGlobalPrimitive
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (ρ : ℝ → ℝ)
    (hfrect : tsupport (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) ⊆
      Set.Ioo a b ×ˢ Set.Ioo c d)
    (hρ : ContDiff ℝ ∞ ρ)
    (hρsupport : tsupport ρ ⊆ Set.Ioo a b)
    (hρone : ∫ x in a..b, ρ x = 1)
    (htotal : ∫ y in c..d, planarHorizontalMarginal a b
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) y = 0) :
    SmoothForms (I := I) (M := M) ℝ 1 :=
  smoothFormCompactZeroExtension I U
    (complexCoordinateRectangleCore I U phi a b c d)
    (complexCoordinateRectangleCore_isCompact I U phi a b c d)
    (complexCoordinateLocalPrimitive I U phi a b c hab.le alpha ρ hρ)
    (complexCoordinateLocalPrimitive_toFun_eq_zero_of_not_mem_rectangle
      I U phi hab hcd alpha ρ hfrect hρ hρsupport hρone htotal)

/-- The exterior derivative of the global coordinate primitive is the
extension by zero of the original zero-mass two-form. -/
theorem deRhamDifferential_complexCoordinateGlobalPrimitive
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, SurfaceRealModel⟯ complexPlanarModelOpen)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (alpha : SmoothForms (I := I) (M := U) ℝ 2)
    (ρ : ℝ → ℝ)
    (hfrect : tsupport (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) ⊆
      Set.Ioo a b ×ˢ Set.Ioo c d)
    (hρ : ContDiff ℝ ∞ ρ)
    (hρsupport : tsupport ρ ⊆ Set.Ioo a b)
    (hρone : ∫ x in a..b, ρ x = 1)
    (htotal : ∫ y in c..d, planarHorizontalMarginal a b
      (planarCoefficientOfComplexTwoForm
        (complexCoordinatePushforwardTwoForm I U phi alpha)) y = 0) :
    deRhamDifferential (I := I) (M := M) (A := ℝ) 1
        (complexCoordinateGlobalPrimitive I U phi hab hcd alpha ρ hfrect
          hρ hρsupport hρone htotal) =
      smoothFormCompactZeroExtension I U
        (complexCoordinateRectangleCore I U phi a b c d)
        (complexCoordinateRectangleCore_isCompact I U phi a b c d) alpha
        (complexCoordinateTwoForm_toFun_eq_zero_of_not_mem_rectangle
          I U phi hab hcd alpha ρ hfrect hρ hρsupport hρone htotal) := by
  rw [complexCoordinateGlobalPrimitive,
    deRhamDifferential_smoothFormCompactZeroExtension]
  apply smoothFormCompactZeroExtension_congr I U
  exact deRhamDifferential_complexCoordinateLocalPrimitive
    I U phi hab.le alpha ρ hρ

end

end JJMath.Uniformization
