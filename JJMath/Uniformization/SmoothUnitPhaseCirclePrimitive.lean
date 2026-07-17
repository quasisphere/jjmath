import JJMath.Manifold.AnnularCohomologyMayerVietoris
import JJMath.Uniformization.PlanarVortexPair

/-!
# Circle primitives carried by smooth unit phases

A smooth complex-valued function of norm one has local real arguments.  The
two principal-logarithm cuts give a two-open cover; on their overlap the two
arguments differ locally by an integral multiple of `2 * pi`.  Consequently
their differentials glue to a global real one-form for which the original
unit phase is a smooth circle primitive.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]

/-- The principal-logarithm cut of a smooth unit phase. -/
def smoothUnitPhaseLeftOpen
  (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞) :
    TopologicalSpace.Opens M :=
  ⟨P ⁻¹' Complex.slitPlane,
    Complex.isOpen_slitPlane.preimage P.contMDiff.continuous⟩

/-- The opposite principal-logarithm cut of a smooth unit phase. -/
def smoothUnitPhaseRightOpen
  (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞) :
    TopologicalSpace.Opens M :=
  ⟨(fun x ↦ -P x) ⁻¹' Complex.slitPlane,
    Complex.isOpen_slitPlane.preimage P.contMDiff.continuous.neg⟩

theorem smoothUnitPhase_cuts_cover
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞)
    (hnorm : ∀ x : M, ‖P x‖ = 1) :
    smoothUnitPhaseLeftOpen I P ⊔ smoothUnitPhaseRightOpen I P = ⊤ := by
  ext x
  change (P x ∈ Complex.slitPlane ∨ -P x ∈ Complex.slitPlane) ↔ True
  have hne : P x ≠ 0 := by
    intro hzero
    have h := hnorm x
    rw [hzero, norm_zero] at h
    norm_num at h
  exact ⟨fun _ ↦ trivial, fun _ ↦
    Complex.mem_slitPlane_or_neg_mem_slitPlane hne⟩

/-- Smoothness of the principal logarithm after a smooth map into the slit
plane. -/
theorem contMDiff_complexLog_comp_of_mem_slitPlane
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N]
    (f : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) N ℂ ∞)
    (hf : ∀ x : N, f x ∈ Complex.slitPlane) :
    ContMDiff I (modelWithCornersSelf ℝ ℂ) ∞
      (fun x : N ↦ Complex.log (f x)) := by
  have hlogC : ContDiffOn ℂ ∞ Complex.log Complex.slitPlane :=
    (analyticOnNhd_id.clog (fun z hz ↦ hz)).contDiffOn
      Complex.isOpen_slitPlane.uniqueDiffOn
  have hlogR : ContDiffOn ℝ ∞ Complex.log Complex.slitPlane :=
    @ContDiffOn.restrict_scalars ℝ inferInstance
      ℂ inferInstance inferInstance ℂ inferInstance inferInstance
      Complex.slitPlane Complex.log ∞
      ℂ inferInstance inferInstance inferInstance
      (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ)
      inferInstance (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ)
      hlogC
  have hlogM : ContMDiffOn (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞ Complex.log Complex.slitPlane :=
    contMDiffOn_iff_contDiffOn.mpr hlogR
  rw [← contMDiffOn_univ]
  exact hlogM.comp f.contMDiff.contMDiffOn (by
    intro x _hx
    exact hf x)

/-- The principal real argument on the first logarithm cut. -/
def smoothUnitPhaseLeftArgument
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞) :
    C^∞⟮I, smoothUnitPhaseLeftOpen I P; ℝ⟯ where
  val := fun x ↦ (Complex.log (P (x : M))).im
  property := by
    let f : ContMDiffMap I (modelWithCornersSelf ℝ ℂ)
        (smoothUnitPhaseLeftOpen I P) ℂ ∞ :=
      P.comp
        { val := fun x : smoothUnitPhaseLeftOpen I P ↦ (x : M)
          property := contMDiff_subtype_val }
    have hlog := contMDiff_complexLog_comp_of_mem_slitPlane I f (fun x ↦ x.2)
    exact Complex.imCLM.contDiff.contMDiff.comp hlog

/-- The principal real argument on the opposite logarithm cut, shifted by
`pi` so that it exponentiates to the original phase rather than its negative.
-/
def smoothUnitPhaseRightArgument
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞) :
    C^∞⟮I, smoothUnitPhaseRightOpen I P; ℝ⟯ where
  val := fun x ↦ (Complex.log (-P (x : M))).im + Real.pi
  property := by
    let f : ContMDiffMap I (modelWithCornersSelf ℝ ℂ)
        (smoothUnitPhaseRightOpen I P) ℂ ∞ :=
      { val := fun x ↦ -P (x : M)
        property := (P.contMDiff.comp contMDiff_subtype_val).neg }
    have hlog := contMDiff_complexLog_comp_of_mem_slitPlane I f (fun x ↦ x.2)
    exact (Complex.imCLM.contDiff.contMDiff.comp hlog).add contMDiff_const

theorem smoothUnitPhaseLeftArgument_is_argument
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞)
    (hnorm : ∀ x : M, ‖P x‖ = 1)
    (x : smoothUnitPhaseLeftOpen I P) :
    Complex.exp ((((smoothUnitPhaseLeftArgument I P x : ℝ) : ℂ) *
        Complex.I)) = P (x : M) := by
  have hne : P (x : M) ≠ 0 := Complex.slitPlane_ne_zero x.2
  change Complex.exp ((((Complex.log (P (x : M))).im : ℝ) : ℂ) *
      Complex.I) = P (x : M)
  rw [complex_exp_im_log_mul_I_eq_div_norm hne, hnorm]
  simp

theorem smoothUnitPhaseRightArgument_is_argument
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞)
    (hnorm : ∀ x : M, ‖P x‖ = 1)
    (x : smoothUnitPhaseRightOpen I P) :
    Complex.exp ((((smoothUnitPhaseRightArgument I P x : ℝ) : ℂ) *
        Complex.I)) = P (x : M) := by
  have hne : -P (x : M) ≠ 0 := Complex.slitPlane_ne_zero x.2
  change Complex.exp ((((((Complex.log (-P (x : M))).im + Real.pi) : ℝ) : ℂ) *
      Complex.I)) = P (x : M)
  have hnormNeg : ‖-P (x : M)‖ = 1 := by simpa using hnorm (x : M)
  have hsplit :
      (((((Complex.log (-P (x : M))).im + Real.pi) : ℝ) : ℂ) * Complex.I) =
        ((((Complex.log (-P (x : M))).im : ℝ) : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add,
    complex_exp_im_log_mul_I_eq_div_norm hne, hnormNeg,
    Complex.exp_pi_mul_I]
  simp

/-- The overlap of the two principal-logarithm cuts. -/
abbrev smoothUnitPhaseOverlap
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞) :
    TopologicalSpace.Opens M :=
  smoothUnitPhaseLeftOpen I P ⊓ smoothUnitPhaseRightOpen I P

/-- On the overlap, the phase cannot lie on the real axis. -/
theorem smoothUnitPhase_im_ne_zero_on_overlap
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞)
    (x : smoothUnitPhaseOverlap I P) :
    (P (x : M)).im ≠ 0 := by
  intro him
  have hleft : 0 < (P (x : M)).re := by
    rcases (Complex.mem_slitPlane_iff.mp x.2.1) with hpos | hne
    · exact hpos
    · exact (hne him).elim
  have hright : 0 < (-P (x : M)).re := by
    rcases (Complex.mem_slitPlane_iff.mp x.2.2) with hpos | hne
    · exact hpos
    · exact (hne (by simpa using him)).elim
  have hright' : (P (x : M)).re < 0 := by simpa using hright
  linarith

/-- Difference of the two logarithmic arguments on their overlap. -/
def smoothUnitPhaseArgumentTransition
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞)
    (x : smoothUnitPhaseOverlap I P) : ℝ :=
  smoothUnitPhaseLeftArgument I P
      (TopologicalSpace.Opens.inclusion inf_le_left x) -
    smoothUnitPhaseRightArgument I P
      (TopologicalSpace.Opens.inclusion inf_le_right x)

theorem smoothUnitPhaseArgumentTransition_eq
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞)
    (x : smoothUnitPhaseOverlap I P) :
    smoothUnitPhaseArgumentTransition I P x =
      if 0 < (P (x : M)).im then 0 else -(2 * Real.pi) := by
  let z : ℂ := P (x : M)
  have hzim : z.im ≠ 0 := smoothUnitPhase_im_ne_zero_on_overlap I P x
  by_cases hpos : 0 < z.im
  · rw [if_pos hpos]
    change (Complex.log z).im - ((Complex.log (-z)).im + Real.pi) = 0
    rw [Complex.log_im, Complex.log_im]
    rw [show Complex.arg (-z) = Complex.arg z - Real.pi from
      Complex.arg_neg_eq_arg_sub_pi_of_im_pos hpos]
    ring
  · have hneg : z.im < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hzim
    rw [if_neg hpos]
    change (Complex.log z).im - ((Complex.log (-z)).im + Real.pi) =
      -(2 * Real.pi)
    rw [Complex.log_im, Complex.log_im]
    rw [show Complex.arg (-z) = Complex.arg z + Real.pi from
      Complex.arg_neg_eq_arg_add_pi_of_im_neg hneg]
    ring

/-- Which component of the two-cut overlap contains a point. -/
def smoothUnitPhaseUpperIndicator
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞)
    (x : smoothUnitPhaseOverlap I P) : ℝ :=
  if 0 < (P (x : M)).im then 1 else 0

theorem smoothUnitPhaseUpperIndicator_isLocallyConstant
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞) :
    IsLocallyConstant (smoothUnitPhaseUpperIndicator I P) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let f : smoothUnitPhaseOverlap I P → ℝ := fun y ↦ (P (y : M)).im
  have hf : Continuous f := by
    exact Complex.imCLM.continuous.comp
      (P.contMDiff.continuous.comp continuous_subtype_val)
  by_cases hx : 0 < f x
  · filter_upwards [(isOpen_lt continuous_const hf).mem_nhds hx] with y hy
    simp [smoothUnitPhaseUpperIndicator, f, hx, hy]
  · have hxne : f x ≠ 0 := smoothUnitPhase_im_ne_zero_on_overlap I P x
    have hxneg : f x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hxne
    filter_upwards [(isOpen_lt hf continuous_const).mem_nhds hxneg] with y hy
    have hynot : ¬0 < f y := not_lt.mpr hy.le
    simp [smoothUnitPhaseUpperIndicator, f, hx, hynot]

theorem smoothUnitPhaseArgumentTransition_isLocallyConstant
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞) :
    IsLocallyConstant (smoothUnitPhaseArgumentTransition I P) := by
  have h := (smoothUnitPhaseUpperIndicator_isLocallyConstant I P).comp
    (fun t : ℝ ↦ -(2 * Real.pi) * (1 - t))
  have heq : smoothUnitPhaseArgumentTransition I P =
      fun x ↦ -(2 * Real.pi) *
        (1 - smoothUnitPhaseUpperIndicator I P x) := by
    funext x
    rw [smoothUnitPhaseArgumentTransition_eq]
    by_cases hpos : 0 < (P (x : M)).im <;>
      simp [smoothUnitPhaseUpperIndicator, hpos]
  rw [heq]
  simpa only [Function.comp_def] using h

/-- The zero-form of the first logarithmic argument. -/
def smoothUnitPhaseLeftZeroForm
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞) :
    SmoothForms (I := I) (M := smoothUnitPhaseLeftOpen I P) ℝ 0 :=
  smoothRealFunctionToZeroForm (I0 := I)
    (smoothUnitPhaseLeftArgument I P)

/-- The zero-form of the second logarithmic argument. -/
def smoothUnitPhaseRightZeroForm
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞) :
    SmoothForms (I := I) (M := smoothUnitPhaseRightOpen I P) ℝ 0 :=
  smoothRealFunctionToZeroForm (I0 := I)
    (smoothUnitPhaseRightArgument I P)

/-- The locally constant overlap difference as a smooth zero-form. -/
def smoothUnitPhaseTransitionZeroForm
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞) :
    SmoothForms (I := I) (M := smoothUnitPhaseOverlap I P) ℝ 0 :=
  smoothRealFunctionToZeroForm (I0 := I)
    (smoothRealFunctionOfIsLocallyConstant I
      (smoothUnitPhaseArgumentTransition I P)
      (smoothUnitPhaseArgumentTransition_isLocallyConstant I P))

theorem smoothUnitPhase_zeroForm_difference
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞) :
    deRhamMayerVietorisSmoothDifference (I := I) (A := ℝ)
        (smoothUnitPhaseLeftOpen I P) (smoothUnitPhaseRightOpen I P) 0
        (smoothUnitPhaseLeftZeroForm I P,
          smoothUnitPhaseRightZeroForm I P) =
      smoothUnitPhaseTransitionZeroForm I P := by
  apply DifferentialForm.ext
  intro x
  ext q
  rw [show q = (fun i : Fin 0 ↦ nomatch i) from Subsingleton.elim _ _]
  simp only [deRhamMayerVietorisSmoothDifference,
    smoothUnitPhaseLeftZeroForm, smoothUnitPhaseRightZeroForm,
    smoothUnitPhaseTransitionZeroForm, smoothRealFunctionToZeroForm,
    smoothRealFunctionOfIsLocallyConstant,
    ContinuousAlternatingMap.constOfIsEmpty_apply]
  change
    (restrictSmoothFormsOfLE (I := I) (A := ℝ)
        (W := smoothUnitPhaseOverlap I P)
        (V := smoothUnitPhaseLeftOpen I P) inf_le_left 0
        (smoothUnitPhaseLeftZeroForm I P)).toFun x
          (fun i : Fin 0 ↦ nomatch i) -
      (restrictSmoothFormsOfLE (I := I) (A := ℝ)
        (W := smoothUnitPhaseOverlap I P)
        (V := smoothUnitPhaseRightOpen I P) inf_le_right 0
        (smoothUnitPhaseRightZeroForm I P)).toFun x
          (fun i : Fin 0 ↦ nomatch i) =
        smoothUnitPhaseArgumentTransition I P x
  have hleft :
      (restrictSmoothFormsOfLE (I := I) (A := ℝ)
        (W := smoothUnitPhaseOverlap I P)
        (V := smoothUnitPhaseLeftOpen I P) inf_le_left 0
        (smoothUnitPhaseLeftZeroForm I P)).toFun x
          (fun i : Fin 0 ↦ nomatch i) =
      (smoothUnitPhaseLeftZeroForm I P).toFun
        (TopologicalSpace.Opens.inclusion
          (U := smoothUnitPhaseOverlap I P)
          (V := smoothUnitPhaseLeftOpen I P) inf_le_left x)
          (fun i : Fin 0 ↦ nomatch i) := by
    change
      ((smoothUnitPhaseLeftZeroForm I P).toFun
        (TopologicalSpace.Opens.inclusion
          (U := smoothUnitPhaseOverlap I P)
          (V := smoothUnitPhaseLeftOpen I P) inf_le_left x)).compContinuousLinearMap
          (mfderiv I I (TopologicalSpace.Opens.inclusion
            (U := smoothUnitPhaseOverlap I P)
            (V := smoothUnitPhaseLeftOpen I P) inf_le_left) x)
          (fun i : Fin 0 ↦ nomatch i) = _
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact Fin.elim0 i
  have hright :
      (restrictSmoothFormsOfLE (I := I) (A := ℝ)
        (W := smoothUnitPhaseOverlap I P)
        (V := smoothUnitPhaseRightOpen I P) inf_le_right 0
        (smoothUnitPhaseRightZeroForm I P)).toFun x
          (fun i : Fin 0 ↦ nomatch i) =
      (smoothUnitPhaseRightZeroForm I P).toFun
        (TopologicalSpace.Opens.inclusion
          (U := smoothUnitPhaseOverlap I P)
          (V := smoothUnitPhaseRightOpen I P) inf_le_right x)
          (fun i : Fin 0 ↦ nomatch i) := by
    change
      ((smoothUnitPhaseRightZeroForm I P).toFun
        (TopologicalSpace.Opens.inclusion
          (U := smoothUnitPhaseOverlap I P)
          (V := smoothUnitPhaseRightOpen I P) inf_le_right x)).compContinuousLinearMap
          (mfderiv I I (TopologicalSpace.Opens.inclusion
            (U := smoothUnitPhaseOverlap I P)
            (V := smoothUnitPhaseRightOpen I P) inf_le_right) x)
          (fun i : Fin 0 ↦ nomatch i) = _
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    exact Fin.elim0 i
  rw [hleft, hright]
  rfl

/-- The differential of the first logarithmic argument. -/
def smoothUnitPhaseLeftOneForm
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞) :
    SmoothForms (I := I) (M := smoothUnitPhaseLeftOpen I P) ℝ 1 :=
  deRhamDifferential (I := I) (M := smoothUnitPhaseLeftOpen I P)
    (A := ℝ) 0 (smoothUnitPhaseLeftZeroForm I P)

/-- The differential of the second logarithmic argument. -/
def smoothUnitPhaseRightOneForm
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞) :
    SmoothForms (I := I) (M := smoothUnitPhaseRightOpen I P) ℝ 1 :=
  deRhamDifferential (I := I) (M := smoothUnitPhaseRightOpen I P)
    (A := ℝ) 0 (smoothUnitPhaseRightZeroForm I P)

theorem smoothUnitPhase_oneForm_difference_eq_zero
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞) :
    deRhamMayerVietorisSmoothDifference (I := I) (A := ℝ)
        (smoothUnitPhaseLeftOpen I P) (smoothUnitPhaseRightOpen I P) 1
        (smoothUnitPhaseLeftOneForm I P,
          smoothUnitPhaseRightOneForm I P) = 0 := by
  calc
    deRhamMayerVietorisSmoothDifference (I := I) (A := ℝ)
        (smoothUnitPhaseLeftOpen I P) (smoothUnitPhaseRightOpen I P) 1
        (smoothUnitPhaseLeftOneForm I P,
          smoothUnitPhaseRightOneForm I P) =
      deRhamDifferential (I := I) (M := smoothUnitPhaseOverlap I P)
        (A := ℝ) 0
        (deRhamMayerVietorisSmoothDifference (I := I) (A := ℝ)
          (smoothUnitPhaseLeftOpen I P) (smoothUnitPhaseRightOpen I P) 0
          (smoothUnitPhaseLeftZeroForm I P,
            smoothUnitPhaseRightZeroForm I P)) := by
              simpa [smoothUnitPhaseLeftOneForm,
                smoothUnitPhaseRightOneForm] using
                deRhamDifferential_mayerVietorisSmoothDifference
                  (I := I) (A := ℝ)
                  (smoothUnitPhaseLeftOpen I P)
                  (smoothUnitPhaseRightOpen I P) 0
                  (smoothUnitPhaseLeftZeroForm I P,
                    smoothUnitPhaseRightZeroForm I P)
    _ = deRhamDifferential (I := I) (M := smoothUnitPhaseOverlap I P)
          (A := ℝ) 0 (smoothUnitPhaseTransitionZeroForm I P) := by
            rw [smoothUnitPhase_zeroForm_difference]
    _ = 0 := deRhamDifferential_locallyConstant_zeroForm_eq_zero (I0 := I)
      (smoothUnitPhaseArgumentTransition I P)
      (smoothUnitPhaseArgumentTransition_isLocallyConstant I P)

/-- The global logarithmic one-form of a smooth unit phase, obtained by
gluing the differentials of the two principal arguments. -/
def smoothUnitPhaseOneForm
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞)
    (hnorm : ∀ x : M, ‖P x‖ = 1) :
    SmoothForms (I := I) (M := M) ℝ 1 :=
  smoothFormsTwoOpenGlue (I := I) (A := ℝ)
    (smoothUnitPhaseLeftOpen I P) (smoothUnitPhaseRightOpen I P)
    (smoothUnitPhase_cuts_cover I P hnorm)
    (smoothUnitPhaseLeftOneForm I P) (smoothUnitPhaseRightOneForm I P)
    (smoothUnitPhase_oneForm_difference_eq_zero I P)

theorem smoothUnitPhaseOneForm_restrict_left
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞)
    (hnorm : ∀ x : M, ‖P x‖ = 1) :
    restrictSmoothFormsToOpen (I := I) (A := ℝ)
        (smoothUnitPhaseLeftOpen I P) 1
        (smoothUnitPhaseOneForm I P hnorm) =
      smoothUnitPhaseLeftOneForm I P := by
  exact restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_left
    (I := I) (A := ℝ)
    (smoothUnitPhaseLeftOpen I P) (smoothUnitPhaseRightOpen I P)
    (smoothUnitPhase_cuts_cover I P hnorm)
    (smoothUnitPhaseLeftOneForm I P) (smoothUnitPhaseRightOneForm I P)
    (smoothUnitPhase_oneForm_difference_eq_zero I P)

theorem smoothUnitPhaseOneForm_restrict_right
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞)
    (hnorm : ∀ x : M, ‖P x‖ = 1) :
    restrictSmoothFormsToOpen (I := I) (A := ℝ)
        (smoothUnitPhaseRightOpen I P) 1
        (smoothUnitPhaseOneForm I P hnorm) =
      smoothUnitPhaseRightOneForm I P := by
  exact restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_right
    (I := I) (A := ℝ)
    (smoothUnitPhaseLeftOpen I P) (smoothUnitPhaseRightOpen I P)
    (smoothUnitPhase_cuts_cover I P hnorm)
    (smoothUnitPhaseLeftOneForm I P) (smoothUnitPhaseRightOneForm I P)
    (smoothUnitPhase_oneForm_difference_eq_zero I P)

/-- Every smooth unit complex phase canonically represents a real one-form
with a smooth circle-valued primitive. -/
def smoothUnitPhaseCirclePrimitive
    (P : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞)
    (hnorm : ∀ x : M, ‖P x‖ = 1) :
    SmoothCirclePrimitive I (smoothUnitPhaseOneForm I P hnorm) where
  phase := P
  locally_has_argument := by
    intro x
    by_cases hx : x ∈ smoothUnitPhaseLeftOpen I P
    · refine ⟨smoothUnitPhaseLeftOpen I P, hx,
        smoothUnitPhaseLeftArgument I P, ?_, ?_⟩
      · intro y
        exact (smoothUnitPhaseLeftArgument_is_argument I P hnorm y).symm
      · rw [smoothUnitPhaseOneForm_restrict_left]
        rfl
    · have hxright : x ∈ smoothUnitPhaseRightOpen I P := by
        have hmem : x ∈ smoothUnitPhaseLeftOpen I P ⊔
            smoothUnitPhaseRightOpen I P := by
          rw [smoothUnitPhase_cuts_cover I P hnorm]
          trivial
        exact hmem.resolve_left hx
      refine ⟨smoothUnitPhaseRightOpen I P, hxright,
        smoothUnitPhaseRightArgument I P, ?_, ?_⟩
      · intro y
        exact (smoothUnitPhaseRightArgument_is_argument I P hnorm y).symm
      · rw [smoothUnitPhaseOneForm_restrict_right]
        rfl

end

end JJMath.Uniformization
