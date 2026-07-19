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

/--
%%handwave
name:
  Formula for the transverse transition function
statement:
  At \((s,t)\in\mathbb R^2\), the transverse transition function is the
  one-variable step function \(\chi(t)\).
proof:
  This is the defining formula.
-/
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

/--
%%handwave
name:
  Closedness of the standard transverse Thom form
statement:
  The one-form \(d(\chi\circ\operatorname{pr}_2)\) on
  \(\mathbb R\times\mathbb R\) is closed.
proof:
  It is exact, and \(d^2=0\).
-/
theorem properLineTransitionOneForm_closed :
    deRhamDifferential
        (I := ProperLineTubeModel) (M := ℝ × ℝ) (A := ℝ) 1
        properLineTransitionOneForm = 0 := by
  exact deRhamDifferential_comp_eq_zero
    (I := ProperLineTubeModel) (M := ℝ × ℝ) (A := ℝ)
    (smoothRealFunctionToZeroForm (I0 := ProperLineTubeModel)
      properLineTransitionFunction)

/--
%%handwave
name:
  Support of the standard transverse Thom form
statement:
  If \(p=(s,t)\in\mathbb R^2\) and \(t\notin[-1,1]\), then
  \(d(\chi\circ\operatorname{pr}_2)_p=0\).
proof:
  On each of the regions \(t<-1\) and \(t>1\), the step function is locally
  constant, respectively equal to \(0\) and \(1\), so its differential
  vanishes.
-/
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

/--
%%handwave
name:
  Closedness of the transition strip
statement:
  The strip \(\mathbb R\times[-1,1]\) is closed in \(\mathbb R^2\).
proof:
  It is the inverse image of the closed interval \([-1,1]\) under the
  continuous second projection.
-/
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

/--
%%handwave
name:
  Compactness of a bounded transition rectangle
statement:
  For every \(R\in\mathbb R\), the subset
  \(\{(s,t):s\in[-R,R],\ t\in[-1,1]\}\) of the transition strip is compact.
proof:
  Under the subtype inclusion this set is the product of two compact closed
  intervals.
-/
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

/--
%%handwave
name:
  Properness from the two tails of a strip
statement:
  Let \(f:\mathbb R\times[-1,1]\to Y\) be continuous, where \(Y\) is Hausdorff
  and compactly coherent.  If for some \(R\) the restrictions of \(f\) to
  \(s\le -R\) and \(s\ge R\) are proper, then \(f\) is proper.
proof:
  For a compact \(K\subseteq Y\), decompose \(f^{-1}(K)\) into its two tail
  pieces and its middle piece.  The tail pieces are compact by properness, and
  the middle piece is closed in the compact rectangle
  \([-R,R]\times[-1,1]\).
-/
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

/--
%%handwave
name:
  The transition core lies in the tube
statement:
  The image in \(M\) of the strip \(\mathbb R\times[-1,1]\) under the inverse
  tube chart is contained in the tube \(U\).
proof:
  Every value of the inverse tube chart is, by definition, a point of \(U\).
-/
theorem properLineTubeCore_subset
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ) :
    properLineTubeCore I U phi ⊆ U := by
  rintro _ ⟨p, _hp, rfl⟩
  exact (phi.symm p).2

/--
%%handwave
name:
  Closed transition core from proper embedding
statement:
  If the inverse tube chart restricted to
  \(\mathbb R\times[-1,1]\) is proper as a map into the Hausdorff manifold
  \(M\), then its image in \(M\) is closed.
proof:
  A proper map into a Hausdorff space is closed, and the transition core is
  exactly its range.
-/
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

/--
%%handwave
name:
  Closed transition core from tailwise properness
statement:
  Suppose the inverse tube chart on
  \(\mathbb R\times[-1,1]\) is proper on both tails \(s\le -R\) and
  \(s\ge R\).  Then the image of the full strip is closed in \(M\).
proof:
  Tailwise properness implies properness on the full strip because the middle
  rectangle is compact; the image is then closed.
-/
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

/--
%%handwave
name:
  Cover by the tube and the exterior of its core
statement:
  If the transition core \(K\) of a tube \(U\) is closed, then
  \(U\cup(M\setminus K)=M\).
proof:
  Since \(K\subseteq U\), every point either belongs to \(U\) or lies outside
  \(K\).
-/
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

/--
%%handwave
name:
  Closedness of the transported transverse form
statement:
  The pullback to a product-line tube of the standard transverse Thom
  one-form is closed.
proof:
  Exterior differentiation commutes with pullback by the tube diffeomorphism,
  and the standard transverse form is closed.
-/
theorem properLineTubeLocalOneForm_closed
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ) :
    deRhamDifferential (I := I) (M := U) (A := ℝ) 1
      (properLineTubeLocalOneForm I U phi) = 0 := by
  rw [properLineTubeLocalOneForm,
    deRhamDifferential_smoothFormsPullbackDiffeomorph,
    properLineTransitionOneForm_closed]
  exact LinearMap.map_zero _

/--
%%handwave
name:
  Vanishing of the tube form outside the transition core
statement:
  On \(U\cap(M\setminus K)\), where \(K\) is the closed transition core, the
  transported transverse one-form restricts to zero.
proof:
  A point of this overlap maps under the tube chart outside
  \(\mathbb R\times[-1,1]\), where the standard transverse form vanishes.
-/
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

/--
%%handwave
name:
  Mayer--Vietoris compatibility for the tube form
statement:
  On the overlap of \(U\) with the exterior of its transition core, the
  difference between the transported transverse form and the zero form is
  zero.
proof:
  The transported form restricts to zero on the overlap, while the second
  local form is identically zero.
-/
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

/--
%%handwave
name:
  Closedness of the global proper-line Thom form
statement:
  The one-form obtained by gluing the transported transverse form on \(U\)
  to zero on the exterior of the transition core is closed on \(M\).
proof:
  Its restrictions to the two members of the open cover are respectively the
  closed transported form and zero; equality of the restricted differentials
  implies global closedness.
-/
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

/--
%%handwave
name:
  Restriction of the global Thom form to its tube
statement:
  The global proper-line Thom form restricts on \(U\) to the transported
  standard transverse form.
proof:
  This is the left restriction identity for the two-open-set gluing
  construction.
-/
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

/--
%%handwave
name:
  Upper endpoint of a transverse segment
statement:
  The face opposite vertex \(0\) of the affine transverse segment from
  \((s,a)\) to \((s,b)\) is the point \((s,b)\).
proof:
  On this face the barycentric coordinates are \((0,1)\).
-/
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

/--
%%handwave
name:
  Lower endpoint of a transverse segment
statement:
  The face opposite vertex \(1\) of the affine transverse segment from
  \((s,a)\) to \((s,b)\) is the point \((s,a)\).
proof:
  On this face the barycentric coordinates are \((1,0)\).
-/
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

/--
%%handwave
name:
  Unit period of the standard transverse Thom form
statement:
  If \(a\le-1\) and \(b\ge1\), then the integral of
  \(d(\chi\circ\operatorname{pr}_2)\) along the oriented segment from
  \((s,a)\) to \((s,b)\) equals \(1\).
proof:
  The fundamental theorem for exact one-forms gives
  \(\chi(b)-\chi(a)=1-0=1\).
-/
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

/--
%%handwave
name:
  Pullback of the transverse transition function
statement:
  Pulling the zero-form \(\chi\circ\operatorname{pr}_2\) back by the tube
  chart gives the zero-form whose function is
  \(\chi\circ\operatorname{pr}_2\circ\phi\).
proof:
  Evaluate both zero-forms at each point; pullback of a function is
  composition.
-/
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

/--
%%handwave
name:
  The local tube form as an exact form
statement:
  On the tube \(U\), the transported transverse one-form equals
  \(d(\chi\circ\operatorname{pr}_2\circ\phi)\).
proof:
  Exterior differentiation commutes with pullback, and pullback of the
  transverse zero-form is composition with the tube chart.
-/
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

/--
%%handwave
name:
  Formula for a transverse simplex in a tube
statement:
  The transverse simplex in \(U\) is obtained by applying the inverse tube
  chart to the affine segment from \((s,a)\) to \((s,b)\).
proof:
  This is the defining formula.
-/
@[simp]
theorem properLineTubeTransverseSimplex_apply
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (s a b : ℝ) (q : StandardSimplex 1) :
    properLineTubeTransverseSimplex I U phi s a b q =
      phi.symm (properLineTransverseSimplex s a b q) :=
  rfl

/--
%%handwave
name:
  Upper endpoint of a transported transverse segment
statement:
  The face opposite vertex \(0\) of the transported transverse segment is
  \(\phi^{-1}(s,b)\).
proof:
  The corresponding face of the standard affine segment is \((s,b)\), and
  the entire simplex is transported by \(\phi^{-1}\).
-/
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

/--
%%handwave
name:
  Lower endpoint of a transported transverse segment
statement:
  The face opposite vertex \(1\) of the transported transverse segment is
  \(\phi^{-1}(s,a)\).
proof:
  The corresponding face of the standard affine segment is \((s,a)\), and
  the entire simplex is transported by \(\phi^{-1}\).
-/
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

/--
%%handwave
name:
  Unit transverse period of the local tube form
statement:
  If \(a\le-1\) and \(b\ge1\), the integral of the local tube form along the
  transported segment from \(\phi^{-1}(s,a)\) to \(\phi^{-1}(s,b)\) equals
  \(1\).
proof:
  The local form is the differential of the transported transition function,
  so endpoint evaluation gives \(\chi(b)-\chi(a)=1\).
-/
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

/--
%%handwave
name:
  Unit transverse period of the global tube form
statement:
  If \(a\le-1\) and \(b\ge1\), the global proper-line Thom form integrates to
  \(1\) along the transverse segment included from \(U\) into \(M\).
proof:
  Integration after open inclusion equals integration of the restricted form,
  whose restriction to \(U\) is the local tube form with unit transverse
  period.
-/
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

/--
%%handwave
name:
  Vanishing of the global tube form on the exterior
statement:
  The global proper-line Thom form restricts to zero on the complement of
  its closed transition core.
proof:
  The form was defined there as the zero member of the two-open-set gluing.
-/
theorem properLineTubeGlobalOneForm_restrict_exterior
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi)) :
    restrictSmoothFormsToOpen (I := I) (A := ℝ)
        (properLineTubeExteriorOpen I U phi hcore) 1
        (properLineTubeGlobalOneForm I U phi hcore) = 0 := by
  rw [properLineTubeGlobalOneForm,
    restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_right]

/--
%%handwave
name:
  Zero period on chains outside the transition core
statement:
  Every smooth \(1\)-chain supported in the exterior of the closed transition
  core has integral \(0\) against the global proper-line Thom form.
proof:
  Move the integral across the open inclusion; the restricted global form is
  zero on the exterior.
-/
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

/--
%%handwave
name:
  Period of a crossing plus an exterior return chain
statement:
  A chain consisting of one positively oriented transverse crossing from
  level \(a\le-1\) to level \(b\ge1\), together with any return chain outside
  the transition core, has integral \(1\) against the global Thom form.
proof:
  The integral is additive.  The transverse crossing contributes \(1\), and
  the exterior return chain contributes \(0\).
-/
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

/--
%%handwave
name:
  Unit period from a crossing--return decomposition
statement:
  If an ambient \(1\)-chain is equal to one positive transverse crossing plus
  a chain lying outside the transition core, then its integral against the
  global proper-line Thom form is \(1\).
proof:
  Substitute the stated decomposition and use that a crossing has period
  \(1\) while an exterior chain has period \(0\).
-/
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

/--
%%handwave
name:
  Nontrivial first de Rham cohomology from a proper-line crossing
statement:
  Suppose a positive transverse crossing, together with a return chain outside
  the transition core, is a cycle.  Then
  \(H_{\mathrm{dR}}^1(M;\mathbb R)\) is not a singleton.
proof:
  The global Thom form is closed and has period \(1\) on this cycle: the
  crossing contributes \(1\) and the exterior return contributes \(0\).
  An exact form has zero period on cycles, so this closed form represents a
  nonzero cohomology class.
-/
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

/--
%%handwave
name:
  Nontrivial cohomology from a return chain with prescribed boundary
statement:
  Suppose a return chain outside the transition core has boundary equal, after
  inclusion in \(M\), to the negative boundary of a positive transverse
  crossing.  Then \(H_{\mathrm{dR}}^1(M;\mathbb R)\) is not a singleton.
proof:
  The crossing plus the included return chain is a cycle because their
  boundaries cancel.  Its period against the global Thom form is \(1\), so
  the preceding period obstruction gives a nonzero first de Rham class.
-/
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
