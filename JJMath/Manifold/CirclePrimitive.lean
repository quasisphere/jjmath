import JJMath.Manifold.ProperLinePhase

/-!
# Smooth circle primitives of real one-forms

A closed real one-form with integral periods need not have a global
real-valued primitive, but it has a circle-valued primitive.  We represent
such a primitive by its unit complex phase together with local smooth real
arguments.  The proper-line Thom form has a canonical circle primitive after
multiplication by `2 * pi`.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]

/-- The smooth real function underlying a smooth real zero-form. -/
noncomputable def smoothRealFunctionOfZeroForm
    (theta : SmoothForms (I := I) (M := M) ℝ 0) : C^∞⟮I, M; ℝ⟯ where
  val := fun x => theta.toFun x (fun i : Fin 0 => nomatch i)
  property := by
    intro x
    rw [contMDiffAt_iff_source]
    let e : OpenPartialHomeomorph M H := chartAt H x
    let L := ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℝ (Fin 0)
    let scalar : E → ℝ := fun y =>
      L.symm (coordinateExpression (I := I) (F := ℝ) (n := 0)
        theta.toFun e y)
    have hscalar : ContDiffOn ℝ ∞ scalar (e.extend I).target := by
      exact L.symm.contDiff.comp_contDiffOn
        (theta.isContMDiff e (chart_mem_atlas H x))
    have hx_target : e.extend I x ∈ (e.extend I).target := by
      exact (e.extend I).map_source (by simp [e])
    have hscalar_m : ContMDiffWithinAt (modelWithCornersSelf ℝ E)
        (modelWithCornersSelf ℝ ℝ) ∞ scalar (e.extend I).target
          (e.extend I x) :=
      (hscalar (e.extend I x) hx_target).contMDiffWithinAt
    have heq :
        (fun y : E =>
          theta.toFun ((e.extend I).symm y)
            (fun i : Fin 0 => nomatch i)) =ᶠ[
              𝓝[(e.extend I).target] (e.extend I x)] scalar := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      dsimp [scalar, L]
      change theta.toFun ((e.extend I).symm y)
          (fun i : Fin 0 => nomatch i) =
        (coordinateExpression (I := I) (F := ℝ) (n := 0)
          theta.toFun e y) (0 : Fin 0 → E)
      rw [coordinateExpression,
        ContinuousAlternatingMap.compContinuousLinearMap_apply]
      congr 1
      funext i
      exact Fin.elim0 i
    exact (hscalar_m.congr_of_eventuallyEq heq
      (heq.eq_of_nhdsWithin hx_target)).mono_of_mem_nhdsWithin
      (e.extend_target_mem_nhdsWithin (by simp [e]))

/--
%%handwave
name:
  Recovering a smooth zero-form from its scalar function
statement:
  If a smooth real zero-form \(\theta\) is evaluated on the unique empty
  tangent frame to obtain a scalar function, then converting that function
  back to a zero-form recovers \(\theta\).
proof:
  Two zero-forms are equal if their values agree at every point and empty
  tangent frame.  Alternating zero-linear maps are constant, so both values
  are the same scalar.
-/
theorem smoothRealFunctionToZeroForm_smoothRealFunctionOfZeroForm
    (theta : SmoothForms (I := I) (M := M) ℝ 0) :
    smoothRealFunctionToZeroForm (I0 := I)
        (smoothRealFunctionOfZeroForm I theta) = theta := by
  apply DifferentialForm.ext
  intro x
  ext q
  rw [show q = (fun i : Fin 0 => nomatch i) from Subsingleton.elim _ _]
  rw [smoothRealFunctionToZeroForm_toFun]
  exact ContinuousAlternatingMap.constOfIsEmpty_apply ℝ
    (TangentSpace I x) (Fin 0)
    (smoothRealFunctionOfZeroForm I theta x)
    (fun i : Fin 0 => nomatch i)

/-- A smooth circle-valued primitive of a real one-form.  The unit complex
phase is global, while a real argument is required only locally; its
differential is the given form. -/
structure SmoothCirclePrimitive
    (omega : SmoothForms (I := I) (M := M) ℝ 1) where
  phase : ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞
  locally_has_argument : ∀ x : M,
    ∃ U : TopologicalSpace.Opens M, x ∈ U ∧
      ∃ theta : C^∞⟮I, U; ℝ⟯,
        (∀ y : U,
          phase (y : M) =
            Complex.exp (((theta y : ℝ) : ℂ) * Complex.I)) ∧
        restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1 omega =
          deRhamDifferential (I := I) (M := U) (A := ℝ) 0
            (smoothRealFunctionToZeroForm (I0 := I) theta)

namespace SmoothCirclePrimitive

/--
%%handwave
name:
  Two continuous arguments of one phase differ locally by a constant
statement:
  If continuous functions \(f,g:T\to\mathbb R\) satisfy
  \(e^{if(x)}=e^{ig(x)}\) for every \(x\), then \(f-g\) is locally constant.
proof:
  At every point, \(f-g\) is an integer multiple of \(2\pi\).  Continuity
  gives a neighborhood on which its variation is less than \(2\pi\), forcing
  the integer multiple to remain unchanged.
-/
theorem isLocallyConstant_sub_of_exp_mul_I_eq
    {T : Type*} [TopologicalSpace T]
    (f g : T → ℝ) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x, Complex.exp (((f x : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((g x : ℝ) : ℂ) * Complex.I)) :
    IsLocallyConstant (fun x ↦ f x - g x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let d : T → ℝ := fun y ↦ f y - g y
  have hd : Continuous d := hf.sub hg
  have hnear : ∀ᶠ y in nhds x, dist (d y) (d x) < 2 * Real.pi := by
    have hpos : 0 < 2 * Real.pi := by positivity
    exact hd.continuousAt (Metric.ball_mem_nhds (d x) hpos)
  filter_upwards [hnear] with y hy
  rcases Complex.exp_eq_exp_iff_exists_int.mp (h x) with ⟨n, hn⟩
  rcases Complex.exp_eq_exp_iff_exists_int.mp (h y) with ⟨m, hm⟩
  have hnreal : d x = (n : ℝ) * (2 * Real.pi) := by
    have him := congrArg Complex.im hn
    dsimp [d]
    norm_num at him ⊢
    linear_combination him
  have hmreal : d y = (m : ℝ) * (2 * Real.pi) := by
    have him := congrArg Complex.im hm
    dsimp [d]
    norm_num at him ⊢
    linear_combination him
  have hmn : |((m - n : ℤ) : ℝ)| < 1 := by
    have hy' := hy
    rw [hmreal, hnreal, Real.dist_eq] at hy'
    rw [← sub_mul, ← Int.cast_sub] at hy'
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at hy'
    nlinarith [Real.pi_pos]
  have hmn_eq : m = n := by
    have hz : m - n = 0 := Int.abs_lt_one_iff.mp (by
      exact_mod_cast hmn)
    omega
  change d y = d x
  rw [hmreal, hnreal, hmn_eq]

/-- Transport a circle primitive across equality of one-forms. -/
def congr
    {omega eta : SmoothForms (I := I) (M := M) ℝ 1}
    (P : SmoothCirclePrimitive I omega) (h : omega = eta) :
    SmoothCirclePrimitive I eta := by
  rw [← h]
  exact P

/--
%%handwave
name:
  A smooth circle primitive has nonzero phase
statement:
  For every point \(x\), the complex phase of a smooth circle primitive is
  nonzero.
proof:
  Locally the phase is \(e^{i\theta}\), and the complex exponential never
  vanishes.
-/
theorem phase_ne_zero
    {omega : SmoothForms (I := I) (M := M) ℝ 1}
    (P : SmoothCirclePrimitive I omega) (x : M) :
    P.phase x ≠ 0 := by
  rcases P.locally_has_argument x with ⟨U, hxU, theta, hphase, _htheta⟩
  let xU : U := ⟨x, hxU⟩
  rw [hphase xU]
  exact Complex.exp_ne_zero _

/--
%%handwave
name:
  A smooth circle primitive has unit phase
statement:
  For every point \(x\), the phase \(P(x)\) of a smooth circle primitive
  satisfies \(\lVert P(x)\rVert=1\).
proof:
  Locally \(P=e^{i\theta}\) with real \(\theta\), whose real part in the
  exponent is zero; hence its norm is \(e^0=1\).
-/
theorem norm_phase_eq_one
    {omega : SmoothForms (I := I) (M := M) ℝ 1}
    (P : SmoothCirclePrimitive I omega) (x : M) :
    ‖P.phase x‖ = 1 := by
  rcases P.locally_has_argument x with ⟨U, hxU, theta, hphase, _htheta⟩
  let xU : U := ⟨x, hxU⟩
  rw [hphase xU, Complex.norm_exp]
  simp

/-- Reversing the orientation of a circle primitive negates its one-form. -/
noncomputable def neg
    {omega : SmoothForms (I := I) (M := M) ℝ 1}
    (P : SmoothCirclePrimitive I omega) :
    SmoothCirclePrimitive I (-omega) where
  phase :=
    { val := fun x => Complex.conjCLE (P.phase x)
      property := by
        exact Complex.conjCLE.contDiff.contMDiff.comp P.phase.contMDiff }
  locally_has_argument := by
    intro x
    rcases P.locally_has_argument x with ⟨U, hxU, theta, hphase, htheta⟩
    let thetaNeg : C^∞⟮I, U; ℝ⟯ :=
      { val := fun y => -theta y
        property := theta.contMDiff.neg }
    refine ⟨U, hxU, thetaNeg, ?_, ?_⟩
    · intro y
      change Complex.conjCLE (P.phase (y : M)) =
        Complex.exp (((thetaNeg y : ℝ) : ℂ) * Complex.I)
      rw [hphase y]
      rw [Complex.conjCLE_apply, ← Complex.exp_conj]
      congr 1
      simp [thetaNeg]
    · calc
        restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1 (-omega) =
            -restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1 omega := by
              rw [map_neg]
        _ = -deRhamDifferential (I := I) (M := U) (A := ℝ) 0
              (smoothRealFunctionToZeroForm (I0 := I) theta) := by
              rw [htheta]
        _ = deRhamDifferential (I := I) (M := U) (A := ℝ) 0
              (smoothRealFunctionToZeroForm (I0 := I) thetaNeg) := by
              rw [← map_neg]
              congr 1

/-- Multiplying a circle phase by the exponential of a global real function
adds the differential of that function to the represented one-form. -/
noncomputable def addExact
    {omega : SmoothForms (I := I) (M := M) ℝ 1}
    (P : SmoothCirclePrimitive I omega)
    (theta : C^∞⟮I, M; ℝ⟯) :
    SmoothCirclePrimitive I
      (omega + deRhamDifferential (I := I) (M := M) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := I) theta)) where
  phase :=
    { val := fun x => P.phase x *
        Complex.exp ((((theta x : ℝ) : ℂ) * Complex.I))
      property := by
        have hthetaComplex : ContMDiff I (modelWithCornersSelf ℝ ℂ) ∞
            (fun x : M => ((theta x : ℝ) : ℂ)) := by
          exact Complex.ofRealCLM.contDiff.contMDiff.comp theta.contMDiff
        have hmulI : ContMDiff (modelWithCornersSelf ℝ ℂ)
            (modelWithCornersSelf ℝ ℂ) ∞
            (fun z : ℂ => z * Complex.I) := by
          rw [contMDiff_iff_contDiff]
          fun_prop
        have hexp : ContMDiff (modelWithCornersSelf ℝ ℂ)
            (modelWithCornersSelf ℝ ℂ) ∞ Complex.exp := by
          rw [contMDiff_iff_contDiff]
          exact Complex.contDiff_exp
        have hright : ContMDiff I (modelWithCornersSelf ℝ ℂ) ∞
            (fun x : M =>
              Complex.exp ((((theta x : ℝ) : ℂ) * Complex.I))) :=
          hexp.comp (hmulI.comp hthetaComplex)
        have hpair : ContMDiff I
            ((modelWithCornersSelf ℝ ℂ).prod (modelWithCornersSelf ℝ ℂ)) ∞
            (fun x : M => (P.phase x,
              Complex.exp ((((theta x : ℝ) : ℂ) * Complex.I)))) :=
          P.phase.contMDiff.prodMk hright
        have hmul : ContMDiff
            ((modelWithCornersSelf ℝ ℂ).prod (modelWithCornersSelf ℝ ℂ))
            (modelWithCornersSelf ℝ ℂ) ∞
            (fun z : ℂ × ℂ => z.1 * z.2) := by
          rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
          exact contDiff_mul.contMDiff
        exact hmul.comp hpair }
  locally_has_argument := by
    intro x
    rcases P.locally_has_argument x with
      ⟨U, hxU, localTheta, hphase, hlocalTheta⟩
    let thetaU : C^∞⟮I, U; ℝ⟯ :=
      smoothFunctionRestrictToOpen (I := I) U theta
    let totalTheta : C^∞⟮I, U; ℝ⟯ :=
      { val := fun y => localTheta y + thetaU y
        property := localTheta.contMDiff.add thetaU.contMDiff }
    refine ⟨U, hxU, totalTheta, ?_, ?_⟩
    · intro y
      change P.phase (y : M) *
          Complex.exp ((((theta (y : M) : ℝ) : ℂ) * Complex.I)) =
        Complex.exp ((((localTheta y + theta (y : M) : ℝ) : ℝ) : ℂ) *
          Complex.I)
      rw [hphase y]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    · have hrestrictTheta :
          restrictSmoothFormsToOpen (I := I) (A := ℝ) U 0
              (smoothRealFunctionToZeroForm (I0 := I) theta) =
            smoothRealFunctionToZeroForm (I0 := I) thetaU := by
          apply DifferentialForm.ext
          intro y
          ext q
          rw [show q = (fun i : Fin 0 => nomatch i) from Subsingleton.elim _ _]
          rfl
      have hzeroAdd :
          smoothRealFunctionToZeroForm (I0 := I) totalTheta =
            smoothRealFunctionToZeroForm (I0 := I) localTheta +
              smoothRealFunctionToZeroForm (I0 := I) thetaU := by
          apply DifferentialForm.ext
          intro y
          ext q
          rw [show q = (fun i : Fin 0 => nomatch i) from Subsingleton.elim _ _]
          change localTheta y + thetaU y = localTheta y + thetaU y
          rfl
      calc
        restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1
            (omega + deRhamDifferential (I := I) (M := M) (A := ℝ) 0
              (smoothRealFunctionToZeroForm (I0 := I) theta)) =
          restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1 omega +
            restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1
              (deRhamDifferential (I := I) (M := M) (A := ℝ) 0
                (smoothRealFunctionToZeroForm (I0 := I) theta)) := by
                  rw [map_add]
        _ = deRhamDifferential (I := I) (M := U) (A := ℝ) 0
              (smoothRealFunctionToZeroForm (I0 := I) localTheta) +
            deRhamDifferential (I := I) (M := U) (A := ℝ) 0
              (restrictSmoothFormsToOpen (I := I) (A := ℝ) U 0
                (smoothRealFunctionToZeroForm (I0 := I) theta)) := by
                  rw [hlocalTheta,
                    deRhamDifferential_restrictSmoothFormsToOpen]
        _ = deRhamDifferential (I := I) (M := U) (A := ℝ) 0
              (smoothRealFunctionToZeroForm (I0 := I) localTheta) +
            deRhamDifferential (I := I) (M := U) (A := ℝ) 0
              (smoothRealFunctionToZeroForm (I0 := I) thetaU) := by
                  rw [hrestrictTheta]
        _ = deRhamDifferential (I := I) (M := U) (A := ℝ) 0
              (smoothRealFunctionToZeroForm (I0 := I) totalTheta) := by
                  rw [hzeroAdd, map_add]

/-- Adding the differential of a smooth zero-form to the represented
one-form. -/
noncomputable def addExactZeroForm
    {omega : SmoothForms (I := I) (M := M) ℝ 1}
    (P : SmoothCirclePrimitive I omega)
    (theta : SmoothForms (I := I) (M := M) ℝ 0) :
    SmoothCirclePrimitive I
      (omega + deRhamDifferential (I := I) (M := M) (A := ℝ) 0 theta) := by
  have P' := SmoothCirclePrimitive.addExact I P
    (smoothRealFunctionOfZeroForm I theta)
  exact SmoothCirclePrimitive.congr I P' (by
    rw [smoothRealFunctionToZeroForm_smoothRealFunctionOfZeroForm])

/-- Cohomologous closed one-forms have circle primitives simultaneously. -/
noncomputable def of_cohomologous
    {omega eta : DeRhamClosedForms (I := I) (M := M) (A := ℝ) 1}
    (P : SmoothCirclePrimitive I omega.1)
    (hclass :
      (DeRhamExactClosedForms (I := I) (M := M) (A := ℝ) 1).mkQ eta =
        (DeRhamExactClosedForms (I := I) (M := M) (A := ℝ) 1).mkQ omega) :
    SmoothCirclePrimitive I eta.1 := by
  have hexact :
      (eta - omega : DeRhamClosedForms (I := I) (M := M) (A := ℝ) 1) ∈
        DeRhamExactClosedForms (I := I) (M := M) (A := ℝ) 1 := by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq] at hclass
    exact hclass
  change
    (eta.1 - omega.1) ∈
      DeRhamExactForms (I := I) (M := M) (A := ℝ) 1 at hexact
  rw [DeRhamExactForms] at hexact
  let theta := Classical.choose hexact
  have htheta := Classical.choose_spec hexact
  apply SmoothCirclePrimitive.congr I
    (SmoothCirclePrimitive.addExactZeroForm I P theta)
  rw [htheta]
  module

/-- An angular circle primitive, possibly with reversed orientation, plus an
exact correction gives a circle primitive of the resulting one-form. -/
noncomputable def angularAddExact
    {eta omega : SmoothForms (I := I) (M := M) ℝ 1}
    (P : SmoothCirclePrimitive I ((2 * Real.pi) • eta))
    (theta : SmoothForms (I := I) (M := M) ℝ 0)
    (homega :
      omega = (2 * Real.pi) • eta +
        deRhamDifferential (I := I) (M := M) (A := ℝ) 0 theta ∨
      omega = -(2 * Real.pi) • eta +
        deRhamDifferential (I := I) (M := M) (A := ℝ) 0 theta) :
    SmoothCirclePrimitive I omega := by
  classical
  by_cases h : omega = (2 * Real.pi) • eta +
      deRhamDifferential (I := I) (M := M) (A := ℝ) 0 theta
  · exact SmoothCirclePrimitive.congr I
      (SmoothCirclePrimitive.addExactZeroForm I P theta) h.symm
  · have hneg : omega = -(2 * Real.pi) • eta +
        deRhamDifferential (I := I) (M := M) (A := ℝ) 0 theta :=
      homega.resolve_left h
    have Pneg : SmoothCirclePrimitive I (-(2 * Real.pi) • eta) := by
      exact SmoothCirclePrimitive.congr I
        (SmoothCirclePrimitive.neg I P) (by module)
    exact SmoothCirclePrimitive.congr I
      (SmoothCirclePrimitive.addExactZeroForm I Pneg theta) hneg.symm

end SmoothCirclePrimitive

section ProperLine

variable [T2Space M]

/-- The canonical circle primitive of `2 * pi` times the proper-line Thom
form. -/
noncomputable def properLineTubeCirclePrimitive
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi)) :
    SmoothCirclePrimitive I
      ((2 * Real.pi) • properLineTubeGlobalOneForm I U phi hcore) where
  phase := properLineTubeGlobalPhase I U phi hcore
  locally_has_argument := by
    intro x
    by_cases hxU : x ∈ U
    · refine ⟨U, hxU, properLineTubeLocalArgument I U phi, ?_, ?_⟩
      · intro y
        rw [properLineTubeGlobalPhase_eq_local I U phi hcore y.2]
        exact properLineTubeLocalPhase_eq_exp_argument I U phi y
      · calc
          restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1
              ((2 * Real.pi) • properLineTubeGlobalOneForm I U phi hcore) =
            (2 * Real.pi) •
              restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1
                (properLineTubeGlobalOneForm I U phi hcore) := by
                  rw [map_smul]
          _ = (2 * Real.pi) • properLineTubeLocalOneForm I U phi := by
                rw [properLineTubeGlobalOneForm_restrict_tube]
          _ = deRhamDifferential (I := I) (M := U) (A := ℝ) 0
              (smoothRealFunctionToZeroForm (I0 := I)
                (properLineTubeLocalArgument I U phi)) :=
                (deRhamDifferential_properLineTubeLocalArgument I U phi).symm
    · let V := properLineTubeExteriorOpen I U phi hcore
      have hxV : x ∈ V := by
        intro hxcore
        exact hxU (properLineTubeCore_subset I U phi hxcore)
      refine ⟨V, hxV,
        smoothRealConstantFunction (I0 := I) (M0 := V) 0, ?_, ?_⟩
      · intro y
        rw [properLineTubeGlobalPhase_eq_one_of_mem_exterior
          I U phi hcore y.2]
        simp
      · calc
          restrictSmoothFormsToOpen (I := I) (A := ℝ) V 1
              ((2 * Real.pi) • properLineTubeGlobalOneForm I U phi hcore) =
            (2 * Real.pi) •
              restrictSmoothFormsToOpen (I := I) (A := ℝ) V 1
                (properLineTubeGlobalOneForm I U phi hcore) := by
                  rw [map_smul]
          _ = 0 := by
                rw [properLineTubeGlobalOneForm_restrict_exterior, smul_zero]
          _ = deRhamDifferential (I := I) (M := V) (A := ℝ) 0
              (smoothRealFunctionToZeroForm (I0 := I)
                (smoothRealConstantFunction (I0 := I) (M0 := V) 0)) := by
                rw [deRhamDifferential_smoothRealFunctionToZeroForm_const]

end ProperLine

end
end Manifold
