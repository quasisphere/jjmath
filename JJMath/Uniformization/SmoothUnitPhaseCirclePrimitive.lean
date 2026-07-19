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

/--
%%handwave
name:
  The two logarithm cuts cover a unit complex phase
statement:
  Let \(P:M\to\mathbb C\) be smooth with \(|P(x)|=1\) for every \(x\).
  Then the inverse images under \(P\) and \(-P\) of the principal logarithm
  slit plane cover \(M\).
proof:
  A unit complex number is nonzero.  For every nonzero \(z\), either \(z\)
  or \(-z\) avoids the branch cut of the principal logarithm.
-/
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

/--
%%handwave
name:
  Smoothness of the principal logarithm on the slit plane
statement:
  If \(f:N\to\mathbb C\) is smooth and \(f(N)\) lies in the principal
  logarithm slit plane, then
  \[
    x\longmapsto\log(f(x))
  \]
  is smooth as a complex-valued real-smooth map.
proof:
  The principal complex logarithm is holomorphic, hence real-smooth, on the
  slit plane.  Compose its smooth restriction with \(f\).
-/
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

/--
%%handwave
name:
  The principal logarithm supplies an argument on the first cut
statement:
  On the open set where \(P\) lies in the principal slit plane, let
  \(\theta_L=\operatorname{Im}\log P\).  Then
  \[
    e^{i\theta_L(x)}=P(x).
  \]
proof:
  For nonzero \(z\), exponentiating \(i\operatorname{Im}\log z\) gives
  \(z/|z|\).  Since \(|P(x)|=1\), this is \(P(x)\).
-/
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

/--
%%handwave
name:
  The opposite logarithm cut supplies a second argument
statement:
  On the open set where \(-P\) lies in the principal slit plane, put
  \[
    \theta_R=\operatorname{Im}\log(-P)+\pi.
  \]
  Then \(e^{i\theta_R(x)}=P(x)\).
proof:
  The logarithmic term exponentiates to \(-P(x)\) because \(P\) has unit
  norm, while \(e^{i\pi}=-1\).  Their product is \(P(x)\).
-/
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

/--
%%handwave
name:
  A phase in both logarithm cuts is nonreal
statement:
  If both \(P(x)\) and \(-P(x)\) lie in the principal slit plane, then
  \[
    \operatorname{Im}P(x)\ne0.
  \]
proof:
  If the imaginary part vanished, membership of \(P(x)\) in the slit plane
  would force its real part to be positive, while membership of \(-P(x)\)
  would force it to be negative, a contradiction.
-/
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

/--
%%handwave
name:
  Transition between the two principal arguments
statement:
  On the overlap of the logarithm cuts,
  \[
    \theta_L(x)-\theta_R(x)=
    \begin{cases}
      0,&\operatorname{Im}P(x)>0,\\
      -2\pi,&\operatorname{Im}P(x)<0.
    \end{cases}
  \]
proof:
  The principal arguments of \(z\) and \(-z\) differ by \(-\pi\) in the
  upper half-plane and by \(+\pi\) in the lower half-plane.  Substitute
  these formulas into
  \(\operatorname{Arg}(z)-(\operatorname{Arg}(-z)+\pi)\).
-/
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

/--
%%handwave
name:
  Local constancy of the upper-half-plane indicator
statement:
  On the overlap of the two cuts, the function equal to \(1\) when
  \(\operatorname{Im}P>0\) and to \(0\) when
  \(\operatorname{Im}P<0\) is locally constant.
proof:
  The imaginary part of \(P\) is continuous and never vanishes on the
  overlap.  Its sign is therefore constant on a neighborhood of every
  point.
-/
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

/--
%%handwave
name:
  Local constancy of the argument transition
statement:
  The difference \(\theta_L-\theta_R\) is locally constant on the overlap
  of the two logarithm cuts.
proof:
  The transition is \(0\) on the upper-half-plane part and \(-2\pi\) on the
  lower-half-plane part.  Express it as an affine function of the locally
  constant upper-half-plane indicator.
-/
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

/--
%%handwave
name:
  Difference of the two local argument zero-forms
statement:
  On the overlap of the logarithm cuts, the Mayer--Vietoris difference of
  the zero-forms defined by \(\theta_L\) and \(\theta_R\) is the zero-form
  defined by \(\theta_L-\theta_R\).
proof:
  Evaluate both zero-forms at the unique empty tuple of tangent vectors.
  Restriction to the overlap preserves their underlying functions, so the
  difference is pointwise \(\theta_L-\theta_R\).
-/
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

/--
%%handwave
name:
  Agreement of the local argument differentials
statement:
  On the overlap of the two logarithm cuts,
  \[
    d\theta_L-d\theta_R=0.
  \]
proof:
  Exterior differentiation commutes with the Mayer--Vietoris difference.
  The zero-form difference is the locally constant transition
  \(\theta_L-\theta_R\), whose differential is zero.
-/
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

/--
%%handwave
name:
  Restriction of the global phase form to the first cut
statement:
  The global one-form obtained by gluing the local argument differentials
  restricts on the first logarithm cut to
  \[
    d\theta_L.
  \]
proof:
  This is the first restriction identity for gluing differential forms over
  a two-open cover.
-/
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

/--
%%handwave
name:
  Restriction of the global phase form to the second cut
statement:
  The global one-form obtained by gluing the local argument differentials
  restricts on the opposite logarithm cut to
  \[
    d\theta_R.
  \]
proof:
  This is the second restriction identity for the two-open gluing
  construction.
-/
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
