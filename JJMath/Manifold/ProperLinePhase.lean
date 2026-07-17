import JJMath.Manifold.ProperLineThom

/-!
# The periodic phase of a proper-line Thom form

The transverse Thom form on a product tube is the differential of a smooth
step.  Although that step does not extend to a real-valued function on the
ambient manifold, its exponential does: the two constant ends differ by one,
and hence both have complex phase one.  This file constructs the resulting
global smooth phase.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

/-- The unit complex phase associated to the standard transverse step. -/
noncomputable def properLineTransitionPhase (p : ℝ × ℝ) : ℂ :=
  Complex.exp ((((2 * Real.pi) * annularStep p.2 : ℝ) : ℂ) * Complex.I)

/-- The standard transverse phase is smooth. -/
theorem properLineTransitionPhase_contMDiff :
    ContMDiff ProperLineTubeModel (modelWithCornersSelf ℝ ℂ) ∞
      properLineTransitionPhase := by
  change ContMDiff (modelWithCornersSelf ℝ (ℝ × ℝ))
    (modelWithCornersSelf ℝ ℂ) ∞ properLineTransitionPhase
  rw [contMDiff_iff_contDiff]
  unfold properLineTransitionPhase
  have hreal : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => (2 * Real.pi) * annularStep p.2) := by
    fun_prop
  exact ((Complex.ofRealCLM.contDiff.comp hreal).mul contDiff_const).cexp

/-- The standard transverse phase, bundled as a smooth function. -/
noncomputable def properLineTransitionPhaseSmooth :
    ContMDiffMap ProperLineTubeModel (modelWithCornersSelf ℝ ℂ)
      (ℝ × ℝ) ℂ ∞ where
  val := properLineTransitionPhase
  property := properLineTransitionPhase_contMDiff

@[simp]
theorem properLineTransitionPhaseSmooth_apply (p : ℝ × ℝ) :
    properLineTransitionPhaseSmooth p = properLineTransitionPhase p :=
  rfl

theorem properLineTransitionPhase_eq_one_of_second_le_neg_one
    (p : ℝ × ℝ) (hp : p.2 ≤ -1) :
    properLineTransitionPhase p = 1 := by
  simp [properLineTransitionPhase, annularStep_eq_zero_of_le_neg_one hp]

theorem properLineTransitionPhase_eq_one_of_one_le_second
    (p : ℝ × ℝ) (hp : 1 ≤ p.2) :
    properLineTransitionPhase p = 1 := by
  rw [properLineTransitionPhase, annularStep_eq_one_of_one_le hp]
  rw [show (((2 * Real.pi) * (1 : ℝ) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I by norm_num]
  simp [Complex.exp_mul_I]

theorem properLineTransitionPhase_eq_one_of_second_not_mem_Icc
    (p : ℝ × ℝ) (hp : p.2 ∉ Set.Icc (-1 : ℝ) 1) :
    properLineTransitionPhase p = 1 := by
  by_cases hneg : p.2 ≤ -1
  · exact properLineTransitionPhase_eq_one_of_second_le_neg_one p hneg
  · apply properLineTransitionPhase_eq_one_of_one_le_second
    by_contra hpos
    exact hp ⟨le_of_not_ge hneg, le_of_not_ge hpos⟩

section ProperLineTubePhase

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M]

/-- The periodic phase transported to a product line tube. -/
noncomputable def properLineTubeLocalPhase
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ) :
    ContMDiffMap I (modelWithCornersSelf ℝ ℂ) U ℂ ∞ :=
  properLineTransitionPhaseSmooth.comp phi.toContMDiffMap

@[simp]
theorem properLineTubeLocalPhase_apply
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (x : U) :
    properLineTubeLocalPhase I U phi x = properLineTransitionPhase (phi x) :=
  rfl

/-- A real argument for the periodic phase on the line tube. -/
noncomputable def properLineTubeLocalArgument
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ) :
    C^∞⟮I, U; ℝ⟯ where
  val := fun x => (2 * Real.pi) * properLineTubeTransitionFunction I U phi x
  property :=
    contMDiff_const.mul (properLineTubeTransitionFunction I U phi).contMDiff

@[simp]
theorem properLineTubeLocalArgument_apply
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (x : U) :
    properLineTubeLocalArgument I U phi x =
      (2 * Real.pi) * annularStep (phi x).2 :=
  rfl

/-- On the tube, the periodic phase is the exponential of its real argument
times the imaginary unit. -/
theorem properLineTubeLocalPhase_eq_exp_argument
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (x : U) :
    properLineTubeLocalPhase I U phi x =
      Complex.exp (((properLineTubeLocalArgument I U phi x : ℝ) : ℂ) *
        Complex.I) := by
  rfl

/-- The differential of the local argument is exactly two pi times the
transported Thom form. -/
theorem deRhamDifferential_properLineTubeLocalArgument
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ) :
    deRhamDifferential (I := I) (M := U) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := I)
          (properLineTubeLocalArgument I U phi)) =
      (2 * Real.pi) • properLineTubeLocalOneForm I U phi := by
  have hzero :
      smoothRealFunctionToZeroForm (I0 := I)
          (properLineTubeLocalArgument I U phi) =
        (2 * Real.pi) •
          smoothRealFunctionToZeroForm (I0 := I)
            (properLineTubeTransitionFunction I U phi) := by
    apply DifferentialForm.ext
    intro x
    ext q
    rw [show q = (fun i : Fin 0 => nomatch i) from Subsingleton.elim _ _]
    change (2 * Real.pi) * properLineTubeTransitionFunction I U phi x =
      (2 * Real.pi) * properLineTubeTransitionFunction I U phi x
    rfl
  rw [hzero, LinearMap.map_smul]
  rw [← properLineTubeLocalOneForm_eq_d_transitionFunction]

/-- The ambient phase obtained by using the tube phase on the tube and the
constant value one outside it. -/
noncomputable def properLineTubeGlobalPhaseFun
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (x : M) : ℂ := by
  classical
  exact if hx : x ∈ U then properLineTubeLocalPhase I U phi ⟨x, hx⟩ else 1

theorem properLineTubeGlobalPhaseFun_eq_local
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    {x : M} (hx : x ∈ U) :
    properLineTubeGlobalPhaseFun I U phi x =
      properLineTubeLocalPhase I U phi ⟨x, hx⟩ := by
  simp [properLineTubeGlobalPhaseFun, hx]

theorem properLineTubeGlobalPhaseFun_eq_one_of_mem_exterior
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi))
    {x : M} (hx : x ∈ properLineTubeExteriorOpen I U phi hcore) :
    properLineTubeGlobalPhaseFun I U phi x = 1 := by
  by_cases hxU : x ∈ U
  · rw [properLineTubeGlobalPhaseFun_eq_local I U phi hxU]
    apply properLineTransitionPhase_eq_one_of_second_not_mem_Icc
    intro hmiddle
    exact hx ⟨phi ⟨x, hxU⟩, hmiddle, by simp⟩
  · simp [properLineTubeGlobalPhaseFun, hxU]

/-- The global proper-line phase is smooth. -/
noncomputable def properLineTubeGlobalPhase
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi)) :
    ContMDiffMap I (modelWithCornersSelf ℝ ℂ) M ℂ ∞ where
  val := properLineTubeGlobalPhaseFun I U phi
  property := by
    apply contMDiff_of_contMDiffOn_union_of_isOpen
        (s := (U : Set M))
        (t := (properLineTubeExteriorOpen I U phi hcore : Set M))
    · intro x hx
      apply ContMDiffAt.contMDiffWithinAt
      let xU : U := ⟨x, hx⟩
      rw [← contMDiffAt_subtype_iff (U := U) (x := xU)]
      have heq : (fun y : U => properLineTubeGlobalPhaseFun I U phi (y : M)) =
          properLineTubeLocalPhase I U phi := by
        funext y
        exact properLineTubeGlobalPhaseFun_eq_local I U phi y.2
      rw [heq]
      exact (properLineTubeLocalPhase I U phi).contMDiff.contMDiffAt
    · have hone : ContMDiffOn I (modelWithCornersSelf ℝ ℂ) ∞
          (fun _ : M => (1 : ℂ))
          (properLineTubeExteriorOpen I U phi hcore : Set M) :=
        contMDiff_const.contMDiffOn
      exact hone.congr fun x hx =>
        (properLineTubeGlobalPhaseFun_eq_one_of_mem_exterior
          I U phi hcore hx)
    · ext x
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      by_cases hxU : x ∈ U
      · exact Or.inl hxU
      · exact Or.inr fun hxcore =>
          hxU (properLineTubeCore_subset I U phi hxcore)
    · exact U.is_open'
    · exact (properLineTubeExteriorOpen I U phi hcore).is_open'

@[simp]
theorem properLineTubeGlobalPhase_apply
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi)) (x : M) :
    properLineTubeGlobalPhase I U phi hcore x =
      properLineTubeGlobalPhaseFun I U phi x :=
  rfl

theorem properLineTubeGlobalPhase_eq_local
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi))
    {x : M} (hx : x ∈ U) :
    properLineTubeGlobalPhase I U phi hcore x =
      properLineTubeLocalPhase I U phi ⟨x, hx⟩ :=
  properLineTubeGlobalPhaseFun_eq_local I U phi hx

theorem properLineTubeGlobalPhase_eq_one_of_mem_exterior
    (U : TopologicalSpace.Opens M)
    (phi : U ≃ₘ⟮I, ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed (properLineTubeCore I U phi))
    {x : M} (hx : x ∈ properLineTubeExteriorOpen I U phi hcore) :
    properLineTubeGlobalPhase I U phi hcore x = 1 :=
  properLineTubeGlobalPhaseFun_eq_one_of_mem_exterior I U phi hcore hx

end ProperLineTubePhase

end
end Manifold
