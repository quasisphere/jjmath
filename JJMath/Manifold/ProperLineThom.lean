import JJMath.Manifold.AnnularPeriod

/-!
# A transverse Thom form on a proper-line tube

This file constructs the standard closed one-form on `ℝ × ℝ` obtained by
differentiating a step in the second coordinate.  Its support lies in the
closed strip `ℝ × [-1,1]`, and its integral across that strip is one.  The
strip is noncompact; when a tube is placed in another manifold, closedness of
its image is the geometric condition that permits extension by zero.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

/-- The smooth model used for a product tube around a line. -/
abbrev ProperLineTubeModel :
    ModelWithCorners ℝ (ℝ × ℝ) (ℝ × ℝ) :=
  𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)

/-- The transverse step as a smooth function on the standard line tube. -/
noncomputable def properLineTransitionFunction :
    C^∞⟮ProperLineTubeModel, ℝ × ℝ; ℝ⟯ where
  val := fun p => annularStep p.2
  property := by
    exact (contDiff_annularStep.comp contDiff_snd).contMDiff

@[simp]
theorem properLineTransitionFunction_apply (p : ℝ × ℝ) :
    properLineTransitionFunction p = annularStep p.2 :=
  rfl

/-- The standard transverse Thom form on a product tube. -/
noncomputable def properLineTransitionOneForm :
    SmoothForms (I := ProperLineTubeModel) (M := ℝ × ℝ) ℝ 1 :=
  deRhamDifferential (I := ProperLineTubeModel) (M := ℝ × ℝ) (A := ℝ) 0
    (smoothRealFunctionToZeroForm (I0 := ProperLineTubeModel)
      properLineTransitionFunction)

/-- The transverse Thom form is closed. -/
theorem properLineTransitionOneForm_closed :
    deRhamDifferential
        (I := ProperLineTubeModel) (M := ℝ × ℝ) (A := ℝ) 1
        properLineTransitionOneForm = 0 := by
  exact deRhamDifferential_comp_eq_zero
    (I := ProperLineTubeModel) (M := ℝ × ℝ) (A := ℝ)
    (smoothRealFunctionToZeroForm (I0 := ProperLineTubeModel)
      properLineTransitionFunction)

/-- The transverse Thom form vanishes off the closed middle strip. -/
theorem properLineTransitionOneForm_toFun_eq_zero_of_second_not_mem_Icc
    (p : ℝ × ℝ) (hp : p.2 ∉ Set.Icc (-1 : ℝ) 1) :
    properLineTransitionOneForm.toFun p = 0 := by
  unfold properLineTransitionOneForm
  have hp' : p.2 < -1 ∨ 1 < p.2 := by
    by_cases hpneg : p.2 < -1
    · exact Or.inl hpneg
    · refine Or.inr (lt_of_not_ge ?_)
      intro hple
      exact hp ⟨le_of_not_gt hpneg, hple⟩
  rcases hp' with hpneg | hppos
  · have hlocal : ∀ᶠ q in 𝓝 p,
        (smoothRealFunctionToZeroForm (I0 := ProperLineTubeModel)
          properLineTransitionFunction).toFun q =
        (smoothRealFunctionToZeroForm (I0 := ProperLineTubeModel)
          (smoothRealConstantFunction (I0 := ProperLineTubeModel) 0)).toFun q := by
      filter_upwards
        [(isOpen_lt continuous_snd continuous_const).mem_nhds hpneg] with q hq
      ext v
      simp [properLineTransitionFunction_apply,
        annularStep_eq_zero_of_le_neg_one hq.le]
    rw [deRhamDifferential_toFun_eq_of_eventuallyEq
      (I := ProperLineTubeModel)
      (smoothRealFunctionToZeroForm (I0 := ProperLineTubeModel)
        properLineTransitionFunction)
      (smoothRealFunctionToZeroForm (I0 := ProperLineTubeModel)
        (smoothRealConstantFunction (I0 := ProperLineTubeModel) 0)) hlocal]
    rw [deRhamDifferential_smoothRealFunctionToZeroForm_const]
    rfl
  · have hlocal : ∀ᶠ q in 𝓝 p,
        (smoothRealFunctionToZeroForm (I0 := ProperLineTubeModel)
          properLineTransitionFunction).toFun q =
        (smoothRealFunctionToZeroForm (I0 := ProperLineTubeModel)
          (smoothRealConstantFunction (I0 := ProperLineTubeModel) 1)).toFun q := by
      filter_upwards
        [(isOpen_lt continuous_const continuous_snd).mem_nhds hppos] with q hq
      ext v
      simp [properLineTransitionFunction_apply,
        annularStep_eq_one_of_one_le hq.le]
    rw [deRhamDifferential_toFun_eq_of_eventuallyEq
      (I := ProperLineTubeModel)
      (smoothRealFunctionToZeroForm (I0 := ProperLineTubeModel)
        properLineTransitionFunction)
      (smoothRealFunctionToZeroForm (I0 := ProperLineTubeModel)
        (smoothRealConstantFunction (I0 := ProperLineTubeModel) 1)) hlocal]
    rw [deRhamDifferential_smoothRealFunctionToZeroForm_const]
    rfl

/-- The closed strip containing the support of the standard line-tube form. -/
def properLineTransitionCore : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Set.Icc (-1 : ℝ) 1}

theorem properLineTransitionCore_isClosed :
    IsClosed properLineTransitionCore := by
  exact isClosed_Icc.preimage continuous_snd

/-- The part of the transition strip before a chosen longitudinal
coordinate. -/
def properLineTransitionNegativeTail (R : ℝ) :
    Set properLineTransitionCore :=
  {q | (q : ℝ × ℝ).1 ≤ -R}

/-- The part of the transition strip after a chosen longitudinal
coordinate. -/
def properLineTransitionPositiveTail (R : ℝ) :
    Set properLineTransitionCore :=
  {q | R ≤ (q : ℝ × ℝ).1}

/-- The bounded middle of the transition strip is compact. -/
theorem properLineTransitionMiddle_isCompact (R : ℝ) :
    IsCompact {q : properLineTransitionCore |
      (q : ℝ × ℝ).1 ∈ Set.Icc (-R) R} := by
  rw [Subtype.isCompact_iff]
  have heq :
      ((↑) : properLineTransitionCore → ℝ × ℝ) ''
          {q : properLineTransitionCore |
            (q : ℝ × ℝ).1 ∈ Set.Icc (-R) R} =
        Set.Icc (-R) R ×ˢ Set.Icc (-1 : ℝ) 1 := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.2⟩
    · rintro ⟨hq1, hq2⟩
      exact ⟨⟨q, hq2⟩, hq1, rfl⟩
  rw [heq]
  exact isCompact_Icc.prod isCompact_Icc

/-- A map on the full transition strip is proper if its restrictions to the
two unbounded tails are proper.  The connector between the tails is confined
to a compact rectangle and therefore does not affect properness. -/
theorem isProperMap_on_properLineTransitionCore_of_tails
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [CompactlyCoherentSpace Y]
    (f : properLineTransitionCore → Y) (hf : Continuous f)
    (R : ℝ)
    (hneg : IsProperMap
      (fun q : properLineTransitionNegativeTail R ↦
        f (q : properLineTransitionCore)))
    (hpos : IsProperMap
      (fun q : properLineTransitionPositiveTail R ↦
        f (q : properLineTransitionCore))) :
    IsProperMap f := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hf, ?_⟩
  intro K hK
  let Aneg : Set properLineTransitionCore :=
    {q | q ∈ properLineTransitionNegativeTail R ∧ f q ∈ K}
  let Amid : Set properLineTransitionCore :=
    {q | (q : ℝ × ℝ).1 ∈ Set.Icc (-R) R ∧ f q ∈ K}
  let Apos : Set properLineTransitionCore :=
    {q | q ∈ properLineTransitionPositiveTail R ∧ f q ∈ K}
  have hAneg : IsCompact Aneg := by
    have hpre : IsCompact
        ((fun q : properLineTransitionNegativeTail R ↦
          f (q : properLineTransitionCore)) ⁻¹' K) :=
      hneg.isCompact_preimage hK
    have himage := hpre.image
      (continuous_subtype_val : Continuous
        (fun q : properLineTransitionNegativeTail R ↦
          (q : properLineTransitionCore)))
    have heq :
        ((fun q : properLineTransitionNegativeTail R ↦
            (q : properLineTransitionCore)) ''
          ((fun q : properLineTransitionNegativeTail R ↦
            f (q : properLineTransitionCore)) ⁻¹' K)) = Aneg := by
      ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, hz⟩
      · rintro ⟨hqTail, hqK⟩
        exact ⟨⟨q, hqTail⟩, hqK, rfl⟩
    rw [← heq]
    exact himage
  have hApos : IsCompact Apos := by
    have hpre : IsCompact
        ((fun q : properLineTransitionPositiveTail R ↦
          f (q : properLineTransitionCore)) ⁻¹' K) :=
      hpos.isCompact_preimage hK
    have himage := hpre.image
      (continuous_subtype_val : Continuous
        (fun q : properLineTransitionPositiveTail R ↦
          (q : properLineTransitionCore)))
    have heq :
        ((fun q : properLineTransitionPositiveTail R ↦
            (q : properLineTransitionCore)) ''
          ((fun q : properLineTransitionPositiveTail R ↦
            f (q : properLineTransitionCore)) ⁻¹' K)) = Apos := by
      ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, hz⟩
      · rintro ⟨hqTail, hqK⟩
        exact ⟨⟨q, hqTail⟩, hqK, rfl⟩
    rw [← heq]
    exact himage
  have hAmid : IsCompact Amid := by
    apply (properLineTransitionMiddle_isCompact R).of_isClosed_subset
    · exact (isClosed_Icc.preimage
          (continuous_fst.comp continuous_subtype_val)).inter
        (hK.isClosed.preimage hf)
    · intro q hq
      exact hq.1
  have hdecomp : f ⁻¹' K = Aneg ∪ Amid ∪ Apos := by
    ext q
    constructor
    · intro hqK
      by_cases hn : (q : ℝ × ℝ).1 ≤ -R
      · exact Or.inl (Or.inl ⟨hn, hqK⟩)
      · by_cases hp : R ≤ (q : ℝ × ℝ).1
        · exact Or.inr ⟨hp, hqK⟩
        · exact Or.inl (Or.inr
            ⟨⟨le_of_not_ge hn, le_of_not_ge hp⟩, hqK⟩)
    · rintro ((hq | hq) | hq) <;> exact hq.2
  rw [hdecomp]
  exact (hAneg.union hAmid).union hApos

section ProperLineTube

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M]

/-- The image of the middle closed strip of a product line tube. -/
def properLineTubeCore
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ) : Set M :=
  (fun p : ℝ × ℝ => ((phi.symm p : U) : M)) '' properLineTransitionCore

theorem properLineTubeCore_subset
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ) :
    properLineTubeCore I U phi ⊆ U := by
  rintro _ ⟨p, _hp, rfl⟩
  exact (phi.symm p).2

/-- Properness of the embedded middle strip makes its ambient image closed. -/
theorem properLineTubeCore_isClosed_of_proper
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hproper : IsProperMap
      (fun p : properLineTransitionCore =>
        ((phi.symm (p : ℝ × ℝ) : U) : M))) :
    IsClosed (properLineTubeCore I U phi) := by
  let f : properLineTransitionCore → M :=
    fun p => ((phi.symm (p : ℝ × ℝ) : U) : M)
  have hrange : Set.range f = properLineTubeCore I U phi := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(p : ℝ × ℝ), p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  rw [← hrange]
  exact hproper.isClosedMap.isClosed_range

/-- Tailwise properness of a product tube is enough to make its transition
core closed in the ambient manifold.  Thus arbitrary changes to the tube in
a bounded longitudinal region do not affect extension by zero. -/
theorem properLineTubeCore_isClosed_of_tail_proper
    [CompactlyCoherentSpace M]
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (R : ℝ)
    (hneg : IsProperMap
      (fun q : properLineTransitionNegativeTail R ↦
        ((phi.symm ((q : properLineTransitionCore) : ℝ × ℝ) : U) : M)))
    (hpos : IsProperMap
      (fun q : properLineTransitionPositiveTail R ↦
        ((phi.symm ((q : properLineTransitionCore) : ℝ × ℝ) : U) : M))) :
    IsClosed (properLineTubeCore I U phi) := by
  apply properLineTubeCore_isClosed_of_proper I U phi
  exact isProperMap_on_properLineTransitionCore_of_tails
    (Y := M)
    (fun q : properLineTransitionCore ↦
      ((phi.symm (q : ℝ × ℝ) : U) : M))
    (by fun_prop) R hneg hpos

/-- The open set off the closed middle strip of a product line tube. -/
def properLineTubeExteriorOpen
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi)) :
    TopologicalSpace.Opens M :=
  ⟨(properLineTubeCore I U phi)ᶜ, hcore.isOpen_compl⟩

theorem properLineTube_open_cover
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi)) :
    U ⊔ properLineTubeExteriorOpen I U phi hcore = ⊤ := by
  ext x
  change (x ∈ U ∨ x ∈ (properLineTubeCore I U phi)ᶜ) ↔ True
  rw [iff_true]
  by_cases hxU : x ∈ U
  · exact Or.inl hxU
  · exact Or.inr fun hxcore => hxU (properLineTubeCore_subset I U phi hxcore)

/-- The standard transverse form transported to a product line tube. -/
noncomputable def properLineTubeLocalOneForm
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ) :
    SmoothForms (I := I) (M := U) ℝ 1 :=
  smoothFormsPullbackDiffeomorph I ProperLineTubeModel phi 1
    properLineTransitionOneForm

theorem properLineTubeLocalOneForm_closed
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ) :
    deRhamDifferential (I := I) (M := U) (A := ℝ) 1
      (properLineTubeLocalOneForm I U phi) = 0 := by
  rw [properLineTubeLocalOneForm,
    deRhamDifferential_smoothFormsPullbackDiffeomorph,
    properLineTransitionOneForm_closed]
  exact LinearMap.map_zero _

/-- On the overlap with the exterior of the closed middle strip, the
transported form is zero. -/
theorem properLineTubeLocalOneForm_overlap_eq_zero
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi)) :
    restrictSmoothFormsOfLE (I := I) (A := ℝ)
        (W := (U ⊓ properLineTubeExteriorOpen I U phi hcore :
          TopologicalSpace.Opens M))
        (V := U) inf_le_left 1 (properLineTubeLocalOneForm I U phi) = 0 := by
  apply DifferentialForm.ext
  intro x
  ext v
  let xU : U := TopologicalSpace.Opens.inclusion inf_le_left x
  have hphi_not_core : phi xU ∉ properLineTransitionCore := by
    intro hphi
    have hxcore : (x : M) ∈ properLineTubeCore I U phi := by
      refine ⟨phi xU, hphi, ?_⟩
      simp [xU]
    exact x.2.2 hxcore
  have hzero :=
    properLineTransitionOneForm_toFun_eq_zero_of_second_not_mem_Icc
      (phi xU) (by simpa [properLineTransitionCore] using hphi_not_core)
  simp only [restrictSmoothFormsOfLE,
    properLineTubeLocalOneForm, smoothFormsPullbackDiffeomorph]
  change
    ((properLineTransitionOneForm.toFun (phi xU)).compContinuousLinearMap _)
        (_ ∘ v) = 0
  rw [hzero]
  rfl

/-- The overlap condition for gluing the line-tube form to zero. -/
theorem properLineTubeLocalOneForm_mayerVietorisDifference_eq_zero
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi)) :
    deRhamMayerVietorisSmoothDifference (I := I) (A := ℝ)
      U (properLineTubeExteriorOpen I U phi hcore) 1
      (properLineTubeLocalOneForm I U phi, 0) = 0 := by
  rw [deRhamMayerVietorisSmoothDifference]
  simp only [map_zero, sub_zero]
  exact properLineTubeLocalOneForm_overlap_eq_zero I U phi hcore

/-- The global closed one-form obtained by extending a proper-line tube form
by zero. -/
noncomputable def properLineTubeGlobalOneForm
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi)) :
    SmoothForms (I := I) (M := M) ℝ 1 :=
  smoothFormsTwoOpenGlue (I := I) (A := ℝ)
    U (properLineTubeExteriorOpen I U phi hcore)
    (properLineTube_open_cover I U phi hcore)
    (properLineTubeLocalOneForm I U phi) 0
    (properLineTubeLocalOneForm_mayerVietorisDifference_eq_zero
      I U phi hcore)

theorem properLineTubeGlobalOneForm_closed
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi)) :
    deRhamDifferential (I := I) (M := M) (A := ℝ) 1
      (properLineTubeGlobalOneForm I U phi hcore) = 0 := by
  apply smoothForms_eq_zero_of_restrictions_eq_zero
    (I := I) (A := ℝ) U (properLineTubeExteriorOpen I U phi hcore)
      (properLineTube_open_cover I U phi hcore) 2
  · rw [← deRhamDifferential_restrictSmoothFormsToOpen,
      properLineTubeGlobalOneForm,
      restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_left,
      properLineTubeLocalOneForm_closed]
  · rw [← deRhamDifferential_restrictSmoothFormsToOpen,
      properLineTubeGlobalOneForm,
      restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_right]
    exact LinearMap.map_zero _

/-- The global cohomology representative carried by a proper-line tube. -/
noncomputable def properLineTubeClosedOneForm
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi)) :
    DeRhamClosedForms (I := I) (M := M) (A := ℝ) 1 :=
  ⟨properLineTubeGlobalOneForm I U phi hcore,
    properLineTubeGlobalOneForm_closed I U phi hcore⟩

theorem properLineTubeGlobalOneForm_restrict_tube
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi)) :
    restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1
        (properLineTubeGlobalOneForm I U phi hcore) =
      properLineTubeLocalOneForm I U phi := by
  rw [properLineTubeGlobalOneForm,
    restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_left]

end ProperLineTube

/-- The affine transverse segment in the standard line tube. -/
noncomputable def properLineTransverseSimplex
    (s a b : ℝ) :
    ContMDiffSingularSimplex
      (I := ProperLineTubeModel) (M := ℝ × ℝ) 1 ∞ := by
  let G : SimplexAmbient 1 → ℝ × ℝ :=
    fun q => (s, q 0 * a + q 1 * b)
  have hsecond :
      ContDiff ℝ ∞ (fun q : SimplexAmbient 1 => q 0 * a + q 1 * b) := by
    fun_prop
  have hG :
      ContMDiff 𝓘(ℝ, SimplexAmbient 1) ProperLineTubeModel ∞ G := by
    exact (contDiff_const.prodMk hsecond).contMDiff
  exact
    { toContinuousMap :=
        ⟨fun q => G q, hG.continuous.comp continuous_subtype_val⟩
      contMDiff :=
        ⟨G, hG.contMDiffOn, fun _ => rfl⟩ }

@[simp]
theorem properLineTransverseSimplex_face_zero_apply
    (s a b : ℝ) (q : StandardSimplex 0) :
    (properLineTransverseSimplex s a b).face 0 q = (s, b) := by
  have hq : (q : SimplexAmbient 0) 0 = 1 := by
    simpa using q.2.2
  change (s, (simplexFaceMap 0 q : SimplexAmbient 1) 0 * a +
      (simplexFaceMap 0 q : SimplexAmbient 1) 1 * b) = (s, b)
  congr 1
  rw [show (simplexFaceMap 0 q : SimplexAmbient 1) 0 = 0 by
        exact simplexAmbientMap_succAbove_apply_omitted 0 q]
  rw [show (simplexFaceMap 0 q : SimplexAmbient 1) 1 =
        (q : SimplexAmbient 0) 0 by
        exact simplexAmbientMap_succAbove_apply_succAbove 0 q 0]
  simp [hq]

@[simp]
theorem properLineTransverseSimplex_face_one_apply
    (s a b : ℝ) (q : StandardSimplex 0) :
    (properLineTransverseSimplex s a b).face 1 q = (s, a) := by
  have hq : (q : SimplexAmbient 0) 0 = 1 := by
    simpa using q.2.2
  change (s, (simplexFaceMap 1 q : SimplexAmbient 1) 0 * a +
      (simplexFaceMap 1 q : SimplexAmbient 1) 1 * b) = (s, a)
  congr 1
  rw [show (simplexFaceMap 1 q : SimplexAmbient 1) 1 = 0 by
        exact simplexAmbientMap_succAbove_apply_omitted 1 q]
  rw [show (simplexFaceMap 1 q : SimplexAmbient 1) 0 =
        (q : SimplexAmbient 0) 0 by
        exact simplexAmbientMap_succAbove_apply_succAbove 1 q 0]
  simp [hq]

/-- The standard line-tube form has unit integral on a transverse segment
whose endpoints lie beyond the transition strip. -/
theorem integrate_properLineTransitionOneForm_transverse_eq_one
    (s : ℝ) {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b) :
    integrateSmoothChain (I := ProperLineTubeModel)
        properLineTransitionOneForm
        (Finsupp.single (properLineTransverseSimplex s a b) (1 : ℤ)) = 1 := by
  unfold properLineTransitionOneForm
  rw [integrateSmoothChain_deRhamDifferential_zero_single_eq_endpoint_sub
    (I := ProperLineTubeModel)]
  simp only [properLineTransverseSimplex_face_zero_apply,
    properLineTransverseSimplex_face_one_apply]
  rw [properLineTransitionFunction_apply,
    properLineTransitionFunction_apply]
  rw [annularStep_eq_zero_of_le_neg_one ha,
    annularStep_eq_one_of_one_le hb]
  norm_num

section ProperLineTubePeriod

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M]

/-- The transverse step transported to a product line tube. -/
noncomputable def properLineTubeTransitionFunction
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ) :
    C^∞⟮I, U; ℝ⟯ :=
  properLineTransitionFunction.comp phi.toContMDiffMap

theorem smoothFormsPullbackDiffeomorph_properLineTransitionZeroForm
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ) :
    smoothFormsPullbackDiffeomorph I ProperLineTubeModel phi 0
        (smoothRealFunctionToZeroForm (I0 := ProperLineTubeModel)
          properLineTransitionFunction) =
      smoothRealFunctionToZeroForm (I0 := I)
        (properLineTubeTransitionFunction I U phi) := by
  apply DifferentialForm.ext
  intro x
  ext v
  simp [smoothFormsPullbackDiffeomorph, smoothFormPullbackDiffeomorph,
    smoothDifferentialFormPullbackDiffeomorph, smoothRealFunctionToZeroForm,
    properLineTubeTransitionFunction]

theorem properLineTubeLocalOneForm_eq_d_transitionFunction
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ) :
    properLineTubeLocalOneForm I U phi =
      deRhamDifferential (I := I) (M := U) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := I)
          (properLineTubeTransitionFunction I U phi)) := by
  rw [properLineTubeLocalOneForm, properLineTransitionOneForm,
    ← deRhamDifferential_smoothFormsPullbackDiffeomorph]
  rw [smoothFormsPullbackDiffeomorph_properLineTransitionZeroForm]

/-- A transverse segment in a product line tube. -/
noncomputable def properLineTubeTransverseSimplex
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (s a b : ℝ) :
    ContMDiffSingularSimplex (I := I) (M := U) 1 ∞ := by
  let sigma := properLineTransverseSimplex s a b
  exact
    { toContinuousMap :=
        ⟨fun q => phi.symm (sigma q),
          phi.symm.continuous.comp sigma.toContinuousMap.continuous⟩
      contMDiff :=
        ⟨fun q => phi.symm (sigma.extension q),
          phi.symm.contMDiff.comp_contMDiffOn sigma.extension_contMDiffOn,
          fun q => congrArg phi.symm (sigma.extension_eq q)⟩ }

@[simp]
theorem properLineTubeTransverseSimplex_apply
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (s a b : ℝ) (q : StandardSimplex 1) :
    properLineTubeTransverseSimplex I U phi s a b q =
      phi.symm (properLineTransverseSimplex s a b q) :=
  rfl

@[simp]
theorem properLineTubeTransverseSimplex_face_zero_apply
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (s a b : ℝ) (q : StandardSimplex 0) :
    (properLineTubeTransverseSimplex I U phi s a b).face 0 q =
      phi.symm (s, b) := by
  change phi.symm ((properLineTransverseSimplex s a b).face 0 q) =
    phi.symm (s, b)
  congr 1
  simp

@[simp]
theorem properLineTubeTransverseSimplex_face_one_apply
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (s a b : ℝ) (q : StandardSimplex 0) :
    (properLineTubeTransverseSimplex I U phi s a b).face 1 q =
      phi.symm (s, a) := by
  change phi.symm ((properLineTransverseSimplex s a b).face 1 q) =
    phi.symm (s, a)
  congr 1
  simp

/-- The transported line-tube form has unit integral across the tube. -/
theorem integrate_properLineTubeLocalOneForm_transverse_eq_one
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (s : ℝ) {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b) :
    integrateSmoothChain (I := I) (properLineTubeLocalOneForm I U phi)
        (Finsupp.single (properLineTubeTransverseSimplex I U phi s a b)
          (1 : ℤ)) = 1 := by
  rw [properLineTubeLocalOneForm_eq_d_transitionFunction]
  rw [integrateSmoothChain_deRhamDifferential_zero_single_eq_endpoint_sub]
  simp [properLineTubeTransitionFunction,
    annularStep_eq_zero_of_le_neg_one ha,
    annularStep_eq_one_of_one_le hb]

/-- The extended line-tube form still has unit transverse integral. -/
theorem integrate_properLineTubeGlobalOneForm_transverse_eq_one
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi))
    (s : ℝ) {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b) :
    integrateSmoothChain (I := I)
        (properLineTubeGlobalOneForm I U phi hcore)
        (Finsupp.single
          ((properLineTubeTransverseSimplex I U phi s a b).openInclusion
            (I := I) U) (1 : ℤ)) = 1 := by
  rw [integrateSmoothChain_openInclusion_single]
  rw [properLineTubeGlobalOneForm_restrict_tube]
  exact integrate_properLineTubeLocalOneForm_transverse_eq_one
    I U phi s ha hb

/-- The extended line-tube form restricts to zero off its closed transition
core. -/
theorem properLineTubeGlobalOneForm_restrict_exterior
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi)) :
    restrictSmoothFormsToOpen (I := I) (A := ℝ)
        (properLineTubeExteriorOpen I U phi hcore) 1
        (properLineTubeGlobalOneForm I U phi hcore) = 0 := by
  rw [properLineTubeGlobalOneForm,
    restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_right]

/-- Every smooth chain outside the closed transition core has zero integral
against the extended line-tube form. -/
theorem integrate_properLineTubeGlobalOneForm_exterior_chain_eq_zero
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi))
    (c : SingularChain
      (I := I) (M := properLineTubeExteriorOpen I U phi hcore) 1 ∞) :
    integrateSmoothChain (I := I)
        (properLineTubeGlobalOneForm I U phi hcore)
        (SingularChain.openInclusion (I := I)
          (properLineTubeExteriorOpen I U phi hcore) c) = 0 := by
  rw [integrateSmoothChain_openInclusion]
  rw [properLineTubeGlobalOneForm_restrict_exterior]
  exact integrateSmoothChain_zero_form I c

/-- A chain made from one positive transverse crossing and a return chain
outside the closed transition strip has Thom period exactly one. -/
theorem integrate_properLineTubeGlobalOneForm_crossing_add_exterior_eq_one
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi))
    (s : ℝ) {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b)
    (returning : SingularChain
      (I := I) (M := properLineTubeExteriorOpen I U phi hcore) 1 ∞) :
    integrateSmoothChain (I := I)
        (properLineTubeGlobalOneForm I U phi hcore)
        (Finsupp.single
            ((properLineTubeTransverseSimplex I U phi s a b).openInclusion
              (I := I) U) (1 : ℤ) +
          SingularChain.openInclusion (I := I)
            (properLineTubeExteriorOpen I U phi hcore) returning) = 1 := by
  rw [integrateSmoothChain_add,
    integrate_properLineTubeGlobalOneForm_transverse_eq_one
      I U phi hcore s ha hb,
    integrate_properLineTubeGlobalOneForm_exterior_chain_eq_zero
      I U phi hcore returning]
  norm_num

/-- Consequently, any ambient chain admitting such a crossing--return
decomposition has Thom period one. -/
theorem integrate_properLineTubeGlobalOneForm_eq_one_of_eq_crossing_add_exterior
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi))
    (s : ℝ) {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b)
    (returning : SingularChain
      (I := I) (M := properLineTubeExteriorOpen I U phi hcore) 1 ∞)
    (c : SingularChain (I := I) (M := M) 1 ∞)
    (hc : c =
      Finsupp.single
          ((properLineTubeTransverseSimplex I U phi s a b).openInclusion
            (I := I) U) (1 : ℤ) +
        SingularChain.openInclusion (I := I)
          (properLineTubeExteriorOpen I U phi hcore) returning) :
    integrateSmoothChain (I := I)
        (properLineTubeGlobalOneForm I U phi hcore) c = 1 := by
  rw [hc]
  exact integrate_properLineTubeGlobalOneForm_crossing_add_exterior_eq_one
    I U phi hcore s ha hb returning

/-- A transverse crossing closed by a return chain outside the transition
core forces first de Rham cohomology to be nontrivial. -/
theorem not_subsingleton_deRhamH1_of_properLineTube_crossing_and_return_chain
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi))
    (s : ℝ) {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b)
    (returning : SingularChain
      (I := I) (M := properLineTubeExteriorOpen I U phi hcore) 1 ∞)
    (hcycle : boundary (I := I)
      (Finsupp.single
          ((properLineTubeTransverseSimplex I U phi s a b).openInclusion
            (I := I) U) (1 : ℤ) +
        SingularChain.openInclusion (I := I)
          (properLineTubeExteriorOpen I U phi hcore) returning) = 0) :
    ¬ Subsingleton (DeRhamCohomology (I := I) (M := M) (A := ℝ) 1) := by
  apply not_subsingleton_deRhamH1_of_crossing_and_return
    (I := I) (properLineTubeClosedOneForm I U phi hcore)
    (Finsupp.single
      ((properLineTubeTransverseSimplex I U phi s a b).openInclusion
        (I := I) U) (1 : ℤ))
    (SingularChain.openInclusion (I := I)
      (properLineTubeExteriorOpen I U phi hcore) returning) hcycle
  · exact integrate_properLineTubeGlobalOneForm_transverse_eq_one
      I U phi hcore s ha hb
  · exact integrate_properLineTubeGlobalOneForm_exterior_chain_eq_zero
      I U phi hcore returning

/-- It suffices to produce an exterior return chain whose boundary is the
negative of the transverse crossing boundary. -/
theorem not_subsingleton_deRhamH1_of_properLineTube_return_chain_boundary
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi))
    (s : ℝ) {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b)
    (returning : SingularChain
      (I := I) (M := properLineTubeExteriorOpen I U phi hcore) 1 ∞)
    (hboundary : SingularChain.openInclusion (I := I)
        (properLineTubeExteriorOpen I U phi hcore) (boundary (I := I) returning) =
      -boundary (I := I)
        (Finsupp.single
          ((properLineTubeTransverseSimplex I U phi s a b).openInclusion
            (I := I) U) (1 : ℤ))) :
    ¬ Subsingleton (DeRhamCohomology (I := I) (M := M) (A := ℝ) 1) := by
  apply not_subsingleton_deRhamH1_of_properLineTube_crossing_and_return_chain
    I U phi hcore s ha hb returning
  rw [map_add, ← SingularChain.openInclusion_boundary, hboundary]
  simp

end ProperLineTubePeriod

end
end Manifold
end JJMath
