import JJMath.Manifold.OneFormPeriod
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The standard annular period form

This file constructs Hubbard's closed one-form on the standard cylinder.  It
is the differential of a smooth step function in the normal coordinate.  The
step is zero on one end of the cylinder and one on the other, so its integral
along a transverse segment is one.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

/-- The smooth model used for the standard cylinder `Circle × ℝ`. -/
abbrev AnnularCylinderModel :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 1) × ℝ)
      (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) :=
  (𝓡 1).prod 𝓘(ℝ, ℝ)

/-- A smooth step which changes from zero to one between `-1` and `1`. -/
def annularStep (y : ℝ) : ℝ :=
  Real.smoothTransition ((y + 1) / 2)

@[fun_prop]
theorem contDiff_annularStep : ContDiff ℝ ∞ annularStep := by
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_id.add contDiff_const).div_const (2 : ℝ))

@[simp]
theorem annularStep_eq_zero_of_le_neg_one {y : ℝ} (hy : y ≤ -1) :
    annularStep y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

@[simp]
theorem annularStep_eq_one_of_one_le {y : ℝ} (hy : 1 ≤ y) :
    annularStep y = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

/-- The normal-coordinate step as a smooth function on the cylinder. -/
noncomputable def annularTransitionFunction :
    C^∞⟮AnnularCylinderModel, Circle × ℝ; ℝ⟯ where
  val := fun p => annularStep p.2
  property := by
    exact contDiff_annularStep.contMDiff.comp contMDiff_snd

@[simp]
theorem annularTransitionFunction_apply (p : Circle × ℝ) :
    annularTransitionFunction p = annularStep p.2 :=
  rfl

/-- Hubbard's standard annular one-form: the differential of the normal step. -/
noncomputable def annularTransitionOneForm :
    SmoothForms (I := AnnularCylinderModel) (M := Circle × ℝ) ℝ 1 :=
  deRhamDifferential (I := AnnularCylinderModel) (M := Circle × ℝ) (A := ℝ) 0
    (smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
      annularTransitionFunction)

/-- The standard annular one-form is closed. -/
theorem annularTransitionOneForm_closed :
    deRhamDifferential (I := AnnularCylinderModel) (M := Circle × ℝ) (A := ℝ) 1
        annularTransitionOneForm = 0 := by
  exact deRhamDifferential_comp_eq_zero
    (I := AnnularCylinderModel) (M := Circle × ℝ) (A := ℝ)
    (smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
      annularTransitionFunction)

/-- The standard annular form vanishes outside the closed transition band. -/
theorem annularTransitionOneForm_toFun_eq_zero_of_second_not_mem_Icc
    (p : Circle × ℝ) (hp : p.2 ∉ Set.Icc (-1 : ℝ) 1) :
    annularTransitionOneForm.toFun p = 0 := by
  unfold annularTransitionOneForm
  have hp' : p.2 < -1 ∨ 1 < p.2 := by
    by_cases hpneg : p.2 < -1
    · exact Or.inl hpneg
    · refine Or.inr (lt_of_not_ge ?_)
      intro hple
      exact hp ⟨le_of_not_gt hpneg, hple⟩
  rcases hp' with hpneg | hppos
  · have hlocal : ∀ᶠ q in 𝓝 p,
        (smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
          annularTransitionFunction).toFun q =
        (smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
          (smoothRealConstantFunction (I0 := AnnularCylinderModel) 0)).toFun q := by
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hpneg] with q hq
      simp [annularTransitionFunction, annularStep_eq_zero_of_le_neg_one hq.le]
    rw [deRhamDifferential_toFun_eq_of_eventuallyEq
      (I := AnnularCylinderModel)
      (smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
        annularTransitionFunction)
      (smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
        (smoothRealConstantFunction (I0 := AnnularCylinderModel) 0)) hlocal]
    rw [deRhamDifferential_smoothRealFunctionToZeroForm_const]
    rfl
  · have hlocal : ∀ᶠ q in 𝓝 p,
        (smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
          annularTransitionFunction).toFun q =
        (smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
          (smoothRealConstantFunction (I0 := AnnularCylinderModel) 1)).toFun q := by
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hppos] with q hq
      simp [annularTransitionFunction, annularStep_eq_one_of_one_le hq.le]
    rw [deRhamDifferential_toFun_eq_of_eventuallyEq
      (I := AnnularCylinderModel)
      (smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
        annularTransitionFunction)
      (smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
        (smoothRealConstantFunction (I0 := AnnularCylinderModel) 1)) hlocal]
    rw [deRhamDifferential_smoothRealFunctionToZeroForm_const]
    rfl

/-- The closed band containing the support of the standard annular form. -/
def annularTransitionCore : Set (Circle × ℝ) :=
  {p | p.2 ∈ Set.Icc (-1 : ℝ) 1}

theorem annularTransitionCore_isCompact : IsCompact annularTransitionCore := by
  have hprod :
      annularTransitionCore = (Set.univ : Set Circle) ×ˢ Set.Icc (-1 : ℝ) 1 := by
    ext p
    simp [annularTransitionCore]
  rw [hprod]
  exact isCompact_univ.prod isCompact_Icc

section AnnularCollar

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M]

/-- The compact transition core of an annular collar. -/
def annularCollarCore
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) : Set M :=
  (fun p : Circle × ℝ => ((phi.symm p : U) : M)) '' annularTransitionCore

theorem annularCollarCore_isCompact
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    IsCompact (annularCollarCore I U phi) := by
  exact annularTransitionCore_isCompact.image
    (continuous_subtype_val.comp phi.symm.continuous)

theorem annularCollarCore_subset
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    annularCollarCore I U phi ⊆ U := by
  rintro _ ⟨p, _hp, rfl⟩
  exact (phi.symm p).2

/-- The open set off the compact transition core of an annular collar. -/
def annularCollarExteriorOpen
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    TopologicalSpace.Opens M :=
  ⟨(annularCollarCore I U phi)ᶜ,
    (annularCollarCore_isCompact I U phi).isClosed.isOpen_compl⟩

theorem annularCollar_open_cover
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    U ⊔ annularCollarExteriorOpen I U phi = ⊤ := by
  ext x
  change (x ∈ U ∨ x ∈ (annularCollarCore I U phi)ᶜ) ↔ True
  rw [iff_true]
  by_cases hxU : x ∈ U
  · exact Or.inl hxU
  · exact Or.inr fun hxcore => hxU (annularCollarCore_subset I U phi hxcore)

/-- The standard annular form transported to an annular collar. -/
noncomputable def annularCollarLocalOneForm
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    SmoothForms (I := I) (M := U) ℝ 1 :=
  smoothFormsPullbackDiffeomorph I AnnularCylinderModel phi 1
    annularTransitionOneForm

theorem annularCollarLocalOneForm_closed
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    deRhamDifferential (I := I) (M := U) (A := ℝ) 1
      (annularCollarLocalOneForm I U phi) = 0 := by
  rw [annularCollarLocalOneForm,
    deRhamDifferential_smoothFormsPullbackDiffeomorph,
    annularTransitionOneForm_closed]
  exact LinearMap.map_zero _

/-- On the overlap with the exterior of its transition core, the transported
annular form is zero. -/
theorem annularCollarLocalOneForm_overlap_eq_zero
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    restrictSmoothFormsOfLE (I := I) (A := ℝ)
        (W := (U ⊓ annularCollarExteriorOpen I U phi : TopologicalSpace.Opens M))
        (V := U) inf_le_left 1 (annularCollarLocalOneForm I U phi) = 0 := by
  apply DifferentialForm.ext
  intro x
  ext v
  let xU : U := TopologicalSpace.Opens.inclusion inf_le_left x
  have hphi_not_core : phi xU ∉ annularTransitionCore := by
    intro hphi
    have hxcore : (x : M) ∈ annularCollarCore I U phi := by
      refine ⟨phi xU, hphi, ?_⟩
      simp [xU]
    exact x.2.2 hxcore
  have hzero :=
    annularTransitionOneForm_toFun_eq_zero_of_second_not_mem_Icc
      (phi xU) (by simpa [annularTransitionCore] using hphi_not_core)
  simp only [restrictSmoothFormsOfLE,
    annularCollarLocalOneForm, smoothFormsPullbackDiffeomorph]
  change
    ((annularTransitionOneForm.toFun (phi xU)).compContinuousLinearMap _)
        (_ ∘ v) = 0
  rw [hzero]
  rfl

/-- The overlap condition for gluing the transported annular form to zero. -/
theorem annularCollarLocalOneForm_mayerVietorisDifference_eq_zero
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    deRhamMayerVietorisSmoothDifference (I := I) (A := ℝ)
      U (annularCollarExteriorOpen I U phi) 1
      (annularCollarLocalOneForm I U phi, 0) = 0 := by
  rw [deRhamMayerVietorisSmoothDifference]
  simp only [map_zero, sub_zero]
  exact annularCollarLocalOneForm_overlap_eq_zero I U phi

/-- The compactly supported global one-form associated with an annular
collar. -/
noncomputable def annularCollarGlobalOneForm
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    SmoothForms (I := I) (M := M) ℝ 1 :=
  smoothFormsTwoOpenGlue (I := I) (A := ℝ)
    U (annularCollarExteriorOpen I U phi)
    (annularCollar_open_cover I U phi)
    (annularCollarLocalOneForm I U phi) 0
    (annularCollarLocalOneForm_mayerVietorisDifference_eq_zero I U phi)

theorem annularCollarGlobalOneForm_closed
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    deRhamDifferential (I := I) (M := M) (A := ℝ) 1
      (annularCollarGlobalOneForm I U phi) = 0 := by
  apply smoothForms_eq_zero_of_restrictions_eq_zero
    (I := I) (A := ℝ) U (annularCollarExteriorOpen I U phi)
      (annularCollar_open_cover I U phi) 2
  · rw [← deRhamDifferential_restrictSmoothFormsToOpen,
      annularCollarGlobalOneForm,
      restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_left,
      annularCollarLocalOneForm_closed]
  · rw [← deRhamDifferential_restrictSmoothFormsToOpen,
      annularCollarGlobalOneForm,
      restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_right]
    exact LinearMap.map_zero _

/-- The global closed form represented by an annular collar. -/
noncomputable def annularCollarClosedOneForm
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    DeRhamClosedForms (I := I) (M := M) (A := ℝ) 1 :=
  ⟨annularCollarGlobalOneForm I U phi,
    annularCollarGlobalOneForm_closed I U phi⟩

end AnnularCollar

/-- The affine transverse segment in the cylinder at a fixed circle point. -/
noncomputable def annularTransverseSimplex
    (z : Circle) (a b : ℝ) :
    ContMDiffSingularSimplex
      (I := AnnularCylinderModel) (M := Circle × ℝ) 1 ∞ := by
  let G : SimplexAmbient 1 → Circle × ℝ :=
    fun q => (z, q 0 * a + q 1 * b)
  have hsecond : ContDiff ℝ ∞ (fun q : SimplexAmbient 1 => q 0 * a + q 1 * b) := by
    fun_prop
  have hG : ContMDiff 𝓘(ℝ, SimplexAmbient 1) AnnularCylinderModel ∞ G := by
    exact contMDiff_const.prodMk hsecond.contMDiff
  exact
    { toContinuousMap :=
        ⟨fun q => G q, hG.continuous.comp continuous_subtype_val⟩
      contMDiff :=
        ⟨G, hG.contMDiffOn, fun _ => rfl⟩ }

@[simp]
theorem annularTransverseSimplex_face_zero_apply
    (z : Circle) (a b : ℝ) (q : StandardSimplex 0) :
    (annularTransverseSimplex z a b).face 0 q = (z, b) := by
  have hq : (q : SimplexAmbient 0) 0 = 1 := by
    simpa using q.2.2
  change (z, (simplexFaceMap 0 q : SimplexAmbient 1) 0 * a +
      (simplexFaceMap 0 q : SimplexAmbient 1) 1 * b) = (z, b)
  congr 1
  rw [show (simplexFaceMap 0 q : SimplexAmbient 1) 0 = 0 by
        exact simplexAmbientMap_succAbove_apply_omitted 0 q]
  rw [show (simplexFaceMap 0 q : SimplexAmbient 1) 1 = (q : SimplexAmbient 0) 0 by
        exact simplexAmbientMap_succAbove_apply_succAbove 0 q 0]
  simp [hq]

@[simp]
theorem annularTransverseSimplex_face_one_apply
    (z : Circle) (a b : ℝ) (q : StandardSimplex 0) :
    (annularTransverseSimplex z a b).face 1 q = (z, a) := by
  have hq : (q : SimplexAmbient 0) 0 = 1 := by
    simpa using q.2.2
  change (z, (simplexFaceMap 1 q : SimplexAmbient 1) 0 * a +
      (simplexFaceMap 1 q : SimplexAmbient 1) 1 * b) = (z, a)
  congr 1
  rw [show (simplexFaceMap 1 q : SimplexAmbient 1) 1 = 0 by
        exact simplexAmbientMap_succAbove_apply_omitted 1 q]
  rw [show (simplexFaceMap 1 q : SimplexAmbient 1) 0 = (q : SimplexAmbient 0) 0 by
        exact simplexAmbientMap_succAbove_apply_succAbove 1 q 0]
  simp [hq]

/-- The standard annular form has unit period on every transverse segment
whose endpoints lie beyond the transition region. -/
theorem integrate_annularTransitionOneForm_transverse_eq_one
    (z : Circle) {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b) :
    integrateSmoothChain (I := AnnularCylinderModel) annularTransitionOneForm
        (Finsupp.single (annularTransverseSimplex z a b) (1 : ℤ)) = 1 := by
  unfold annularTransitionOneForm
  rw [integrateSmoothChain_deRhamDifferential_zero_single_eq_endpoint_sub
    (I := AnnularCylinderModel)]
  simp [annularTransitionFunction,
    annularStep_eq_zero_of_le_neg_one ha, annularStep_eq_one_of_one_le hb]

section AnnularCollarPeriod

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M]

/-- The normal-coordinate step transported to an annular collar. -/
noncomputable def annularCollarTransitionFunction
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    C^∞⟮I, U; ℝ⟯ :=
  annularTransitionFunction.comp phi.toContMDiffMap

/-- Pulling the standard zero-form back to a collar gives the zero-form of
the transported step function. -/
theorem smoothFormsPullbackDiffeomorph_annularTransitionZeroForm
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    smoothFormsPullbackDiffeomorph I AnnularCylinderModel phi 0
        (smoothRealFunctionToZeroForm (I0 := AnnularCylinderModel)
          annularTransitionFunction) =
      smoothRealFunctionToZeroForm (I0 := I)
        (annularCollarTransitionFunction I U phi) := by
  apply DifferentialForm.ext
  intro x
  ext v
  simp [smoothFormsPullbackDiffeomorph, smoothFormPullbackDiffeomorph,
    smoothDifferentialFormPullbackDiffeomorph, smoothRealFunctionToZeroForm,
    annularCollarTransitionFunction]

/-- On its collar, the transported annular form is the differential of the
transported step function. -/
theorem annularCollarLocalOneForm_eq_d_transitionFunction
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    annularCollarLocalOneForm I U phi =
      deRhamDifferential (I := I) (M := U) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := I)
          (annularCollarTransitionFunction I U phi)) := by
  rw [annularCollarLocalOneForm, annularTransitionOneForm,
    ← deRhamDifferential_smoothFormsPullbackDiffeomorph]
  rw [smoothFormsPullbackDiffeomorph_annularTransitionZeroForm]

/-- A transverse segment in an annular collar, obtained from the standard
affine segment by the inverse collar coordinates. -/
noncomputable def annularCollarTransverseSimplex
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) (a b : ℝ) :
    ContMDiffSingularSimplex (I := I) (M := U) 1 ∞ := by
  let sigma := annularTransverseSimplex z a b
  exact
    { toContinuousMap :=
        ⟨fun q => phi.symm (sigma q),
          phi.symm.continuous.comp sigma.toContinuousMap.continuous⟩
      contMDiff :=
        ⟨fun q => phi.symm (sigma.extension q),
          phi.symm.contMDiff.comp_contMDiffOn sigma.extension_contMDiffOn,
          fun q => congrArg phi.symm (sigma.extension_eq q)⟩ }

@[simp]
theorem annularCollarTransverseSimplex_apply
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) (a b : ℝ) (q : StandardSimplex 1) :
    annularCollarTransverseSimplex I U phi z a b q =
      phi.symm (annularTransverseSimplex z a b q) :=
  rfl

@[simp]
theorem annularCollarTransverseSimplex_face_zero_apply
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) (a b : ℝ) (q : StandardSimplex 0) :
    (annularCollarTransverseSimplex I U phi z a b).face 0 q =
      phi.symm (z, b) := by
  change phi.symm ((annularTransverseSimplex z a b).face 0 q) = phi.symm (z, b)
  congr 1
  simp

@[simp]
theorem annularCollarTransverseSimplex_face_one_apply
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) (a b : ℝ) (q : StandardSimplex 0) :
    (annularCollarTransverseSimplex I U phi z a b).face 1 q =
      phi.symm (z, a) := by
  change phi.symm ((annularTransverseSimplex z a b).face 1 q) = phi.symm (z, a)
  congr 1
  simp

/-- The transported annular form has unit integral across the collar. -/
theorem integrate_annularCollarLocalOneForm_transverse_eq_one
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b) :
    integrateSmoothChain (I := I) (annularCollarLocalOneForm I U phi)
        (Finsupp.single (annularCollarTransverseSimplex I U phi z a b)
          (1 : ℤ)) = 1 := by
  rw [annularCollarLocalOneForm_eq_d_transitionFunction]
  rw [integrateSmoothChain_deRhamDifferential_zero_single_eq_endpoint_sub]
  simp [annularCollarTransitionFunction, annularTransitionFunction,
    annularStep_eq_zero_of_le_neg_one ha, annularStep_eq_one_of_one_le hb]

/-- Restricting the global annular form to its collar recovers the transported
local form. -/
theorem annularCollarGlobalOneForm_restrict_collar
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1
        (annularCollarGlobalOneForm I U phi) =
      annularCollarLocalOneForm I U phi := by
  rw [annularCollarGlobalOneForm,
    restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_left]

/-- The global annular form restricts to zero off its compact transition
core. -/
theorem annularCollarGlobalOneForm_restrict_exterior
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ) :
    restrictSmoothFormsToOpen (I := I) (A := ℝ)
        (annularCollarExteriorOpen I U phi) 1
        (annularCollarGlobalOneForm I U phi) = 0 := by
  rw [annularCollarGlobalOneForm,
    restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_right]

/-- The compactly supported global annular form has unit integral across the
collar. -/
theorem integrate_annularCollarGlobalOneForm_transverse_eq_one
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b) :
    integrateSmoothChain (I := I) (annularCollarGlobalOneForm I U phi)
        (Finsupp.single
          ((annularCollarTransverseSimplex I U phi z a b).openInclusion
            (I := I) U) (1 : ℤ)) = 1 := by
  rw [integrateSmoothChain_openInclusion_single]
  rw [annularCollarGlobalOneForm_restrict_collar]
  exact integrate_annularCollarLocalOneForm_transverse_eq_one I U phi z ha hb

/-- Every smooth chain lying off the compact transition core has zero integral
against the global annular form. -/
theorem integrate_annularCollarGlobalOneForm_exterior_chain_eq_zero
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ)
    (c : SingularChain
      (I := I) (M := annularCollarExteriorOpen I U phi) 1 ∞) :
    integrateSmoothChain (I := I) (annularCollarGlobalOneForm I U phi)
        (SingularChain.openInclusion (I := I)
          (annularCollarExteriorOpen I U phi) c) = 0 := by
  rw [integrateSmoothChain_openInclusion]
  rw [annularCollarGlobalOneForm_restrict_exterior]
  exact integrateSmoothChain_zero_form I c

/-- Every smooth path lying off the compact transition core has zero integral
against the global annular form. -/
theorem integrate_annularCollarGlobalOneForm_exterior_eq_zero
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ)
    (sigma : ContMDiffSingularSimplex
      (I := I) (M := annularCollarExteriorOpen I U phi) 1 ∞) :
    integrateSmoothChain (I := I) (annularCollarGlobalOneForm I U phi)
        (Finsupp.single
          (sigma.openInclusion (I := I)
            (annularCollarExteriorOpen I U phi)) (1 : ℤ)) = 0 := by
  simpa using
    integrate_annularCollarGlobalOneForm_exterior_chain_eq_zero
      I U phi (Finsupp.single sigma (1 : ℤ))

/-- A transverse collar crossing closed by an arbitrary return chain outside
the compact transition core forces first de Rham cohomology to be nontrivial. -/
theorem not_subsingleton_deRhamH1_of_annularCollar_crossing_and_return_chain
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b)
    (returning : SingularChain
      (I := I) (M := annularCollarExteriorOpen I U phi) 1 ∞)
    (hcycle : boundary (I := I)
      (Finsupp.single
          ((annularCollarTransverseSimplex I U phi z a b).openInclusion
            (I := I) U) (1 : ℤ) +
        SingularChain.openInclusion (I := I)
          (annularCollarExteriorOpen I U phi) returning) = 0) :
    ¬ Subsingleton (DeRhamCohomology (I := I) (M := M) (A := ℝ) 1) := by
  apply not_subsingleton_deRhamH1_of_crossing_and_return
    (I := I) (annularCollarClosedOneForm I U phi)
    (Finsupp.single
      ((annularCollarTransverseSimplex I U phi z a b).openInclusion
        (I := I) U) (1 : ℤ))
    (SingularChain.openInclusion (I := I)
      (annularCollarExteriorOpen I U phi) returning) hcycle
  · exact integrate_annularCollarGlobalOneForm_transverse_eq_one
      I U phi z ha hb
  · exact integrate_annularCollarGlobalOneForm_exterior_chain_eq_zero
      I U phi returning

/-- It is enough to construct the exterior return chain with boundary opposite
to that of the transverse crossing; the resulting sum is automatically a
cycle and has nonzero annular period. -/
theorem not_subsingleton_deRhamH1_of_annularCollar_return_chain_boundary
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b)
    (returning : SingularChain
      (I := I) (M := annularCollarExteriorOpen I U phi) 1 ∞)
    (hboundary : SingularChain.openInclusion (I := I)
        (annularCollarExteriorOpen I U phi) (boundary (I := I) returning) =
      -boundary (I := I)
        (Finsupp.single
          ((annularCollarTransverseSimplex I U phi z a b).openInclusion
            (I := I) U) (1 : ℤ))) :
    ¬ Subsingleton (DeRhamCohomology (I := I) (M := M) (A := ℝ) 1) := by
  apply not_subsingleton_deRhamH1_of_annularCollar_crossing_and_return_chain
    I U phi z ha hb returning
  rw [map_add, ← SingularChain.openInclusion_boundary, hboundary]
  simp

/-- A transverse collar crossing closed by a return path outside the compact
transition core forces first de Rham cohomology to be nontrivial. -/
theorem not_subsingleton_deRhamH1_of_annularCollar_crossing_and_return
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, AnnularCylinderModel⟯ Circle × ℝ)
    (z : Circle) {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b)
    (returning : ContMDiffSingularSimplex
      (I := I) (M := annularCollarExteriorOpen I U phi) 1 ∞)
    (hcycle : boundary (I := I)
      (Finsupp.single
          ((annularCollarTransverseSimplex I U phi z a b).openInclusion
            (I := I) U) (1 : ℤ) +
        Finsupp.single
          (returning.openInclusion (I := I)
            (annularCollarExteriorOpen I U phi)) (1 : ℤ)) = 0) :
    ¬ Subsingleton (DeRhamCohomology (I := I) (M := M) (A := ℝ) 1) := by
  apply not_subsingleton_deRhamH1_of_annularCollar_crossing_and_return_chain
    I U phi z ha hb (Finsupp.single returning (1 : ℤ))
  simpa using hcycle

end AnnularCollarPeriod

end

end Manifold
end JJMath
