import JJMath.Manifold.CirclePrimitive
import JJMath.Uniformization.ExteriorAngularExtension

/-!
# An alternative circle primitive of the annular angular form

The annular angular representative is obtained from Mayer--Vietoris by
differentiating two local zero-forms.  Their difference on the two components
of the overlap is respectively one and zero.  After multiplication by
`2 * pi`, their complex exponentials therefore agree and glue to a global
circle-valued primitive.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Uniformization

open JJMath.Manifold

noncomputable section

/-- The first local real argument of the normalized annular angular form. -/
noncomputable def annularAngularLeftArgument (v : Circle) :
    C^∞⟮AnnularCylinderModel, annularPunctureOpen v; ℝ⟯ where
  val := fun x => (2 * Real.pi) *
    smoothRealFunctionOfZeroForm AnnularCylinderModel
      (annularAngularConnectingData v).lift.1 x
  property := contMDiff_const.mul
    (smoothRealFunctionOfZeroForm AnnularCylinderModel
      (annularAngularConnectingData v).lift.1).contMDiff

/-- The second local real argument of the normalized annular angular form. -/
noncomputable def annularAngularRightArgument (v : Circle) :
    C^∞⟮AnnularCylinderModel, annularPunctureOpen (annularOpposite v); ℝ⟯ where
  val := fun x => (2 * Real.pi) *
    smoothRealFunctionOfZeroForm AnnularCylinderModel
      (annularAngularConnectingData v).lift.2 x
  property := contMDiff_const.mul
    (smoothRealFunctionOfZeroForm AnnularCylinderModel
      (annularAngularConnectingData v).lift.2).contMDiff

/-- The exponential of the first local argument. -/
noncomputable def annularAngularLeftPhase (v : Circle) :
    ContMDiffMap AnnularCylinderModel (modelWithCornersSelf ℝ ℂ)
      (annularPunctureOpen v) ℂ ∞ where
  val := fun x => Complex.exp
    (((annularAngularLeftArgument v x : ℝ) : ℂ) * Complex.I)
  property := by
    have harg : ContMDiff AnnularCylinderModel
        (modelWithCornersSelf ℝ ℂ) ∞
        (fun x : annularPunctureOpen v =>
          ((annularAngularLeftArgument v x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.contMDiff.comp
        (annularAngularLeftArgument v).contMDiff
    have hmul : ContMDiff (modelWithCornersSelf ℝ ℂ)
        (modelWithCornersSelf ℝ ℂ) ∞ (fun z : ℂ => z * Complex.I) := by
      rw [contMDiff_iff_contDiff]
      fun_prop
    have hexp : ContMDiff (modelWithCornersSelf ℝ ℂ)
        (modelWithCornersSelf ℝ ℂ) ∞ Complex.exp := by
      rw [contMDiff_iff_contDiff]
      exact Complex.contDiff_exp
    exact hexp.comp (hmul.comp harg)

/-- The exponential of the second local argument. -/
noncomputable def annularAngularRightPhase (v : Circle) :
    ContMDiffMap AnnularCylinderModel (modelWithCornersSelf ℝ ℂ)
      (annularPunctureOpen (annularOpposite v)) ℂ ∞ where
  val := fun x => Complex.exp
    (((annularAngularRightArgument v x : ℝ) : ℂ) * Complex.I)
  property := by
    have harg : ContMDiff AnnularCylinderModel
        (modelWithCornersSelf ℝ ℂ) ∞
        (fun x : annularPunctureOpen (annularOpposite v) =>
          ((annularAngularRightArgument v x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.contMDiff.comp
        (annularAngularRightArgument v).contMDiff
    have hmul : ContMDiff (modelWithCornersSelf ℝ ℂ)
        (modelWithCornersSelf ℝ ℂ) ∞ (fun z : ℂ => z * Complex.I) := by
      rw [contMDiff_iff_contDiff]
      fun_prop
    have hexp : ContMDiff (modelWithCornersSelf ℝ ℂ)
        (modelWithCornersSelf ℝ ℂ) ∞ Complex.exp := by
      rw [contMDiff_iff_contDiff]
      exact Complex.contDiff_exp
    exact hexp.comp (hmul.comp harg)

/-- The two local phases agree on the double-puncture overlap. -/
theorem annularAngularLocalPhases_agree (v : Circle)
    (x : annularDoublePunctureOpen v) :
    annularAngularLeftPhase v
        (TopologicalSpace.Opens.inclusion inf_le_left x) =
      annularAngularRightPhase v
        (TopologicalSpace.Opens.inclusion inf_le_right x) := by
  let a : ℝ :=
    (annularAngularConnectingData v).lift.1.toFun
      (TopologicalSpace.Opens.inclusion inf_le_left x)
      (fun i : Fin 0 => nomatch i)
  let b : ℝ :=
    (annularAngularConnectingData v).lift.2.toFun
      (TopologicalSpace.Opens.inclusion inf_le_right x)
      (fun i : Fin 0 => nomatch i)
  have hab : a - b = annularOverlapStepFunction v x := by
    simpa [a, b] using annularAngularLift_difference_apply v x
  by_cases hx : x ∈ annularOverlapPositiveSet v
  · have hab' : a = b + 1 := by
      have : a - b = 1 := by
        simpa [annularOverlapStepFunction, hx] using hab
      linarith
    change Complex.exp (((((2 * Real.pi) * a : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((((2 * Real.pi) * b : ℝ) : ℂ) * Complex.I))
    rw [hab']
    have harg :
        ((((2 * Real.pi) * (b + 1) : ℝ) : ℂ) * Complex.I) =
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I) +
            ((((2 * Real.pi) * b : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_add]
    simp [Complex.exp_mul_I]
  · have hab' : a = b := by
      have : a - b = 0 := by
        simpa [annularOverlapStepFunction, hx] using hab
      linarith
    change Complex.exp (((((2 * Real.pi) * a : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((((2 * Real.pi) * b : ℝ) : ℂ) * Complex.I))
    rw [hab']

/-- The global annular phase, defined using the first punctured chart whenever
available and the second chart at its omitted circle. -/
noncomputable def annularAngularGlobalPhaseFun (v : Circle)
    (x : Circle × ℝ) : ℂ := by
  classical
  exact if hx : x ∈ annularPunctureOpen v then
    annularAngularLeftPhase v ⟨x, hx⟩
  else
    annularAngularRightPhase v ⟨x, by
      have hcover : x ∈ annularPunctureOpen v ∨
          x ∈ annularPunctureOpen (annularOpposite v) := by
        have : x ∈ (annularPunctureOpen v ⊔
            annularPunctureOpen (annularOpposite v) :
              TopologicalSpace.Opens (Circle × ℝ)) := by
          rw [annularPunctures_cover v]
          trivial
        exact this
      exact hcover.resolve_left hx⟩

theorem annularAngularGlobalPhaseFun_eq_left (v : Circle)
    {x : Circle × ℝ} (hx : x ∈ annularPunctureOpen v) :
    annularAngularGlobalPhaseFun v x =
      annularAngularLeftPhase v ⟨x, hx⟩ := by
  simp [annularAngularGlobalPhaseFun, hx]

theorem annularAngularGlobalPhaseFun_eq_right (v : Circle)
    {x : Circle × ℝ} (hx : x ∈ annularPunctureOpen (annularOpposite v)) :
    annularAngularGlobalPhaseFun v x =
      annularAngularRightPhase v ⟨x, hx⟩ := by
  classical
  by_cases hxleft : x ∈ annularPunctureOpen v
  · rw [annularAngularGlobalPhaseFun_eq_left v hxleft]
    let y : annularDoublePunctureOpen v := ⟨x, hxleft, hx⟩
    simpa [y] using annularAngularLocalPhases_agree v y
  · simp [annularAngularGlobalPhaseFun, hxleft]

/-- The global annular phase is smooth. -/
noncomputable def annularAngularGlobalPhase (v : Circle) :
    ContMDiffMap AnnularCylinderModel (modelWithCornersSelf ℝ ℂ)
      (Circle × ℝ) ℂ ∞ where
  val := annularAngularGlobalPhaseFun v
  property := by
    apply contMDiff_of_contMDiffOn_union_of_isOpen
    · intro x hx
      apply ContMDiffAt.contMDiffWithinAt
      let xU : annularPunctureOpen v := ⟨x, hx⟩
      rw [← contMDiffAt_subtype_iff (x := xU)]
      have heq :
          (fun y : annularPunctureOpen v =>
            annularAngularGlobalPhaseFun v (y : Circle × ℝ)) =
            annularAngularLeftPhase v := by
        funext y
        exact annularAngularGlobalPhaseFun_eq_left v y.2
      rw [heq]
      exact (annularAngularLeftPhase v).contMDiff.contMDiffAt
    · intro x hx
      apply ContMDiffAt.contMDiffWithinAt
      let xU : annularPunctureOpen (annularOpposite v) := ⟨x, hx⟩
      rw [← contMDiffAt_subtype_iff (x := xU)]
      have heq :
          (fun y : annularPunctureOpen (annularOpposite v) =>
            annularAngularGlobalPhaseFun v (y : Circle × ℝ)) =
            annularAngularRightPhase v := by
        funext y
        exact annularAngularGlobalPhaseFun_eq_right v y.2
      rw [heq]
      exact (annularAngularRightPhase v).contMDiff.contMDiffAt
    · ext x
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      have hx : x ∈ (annularPunctureOpen v ⊔
          annularPunctureOpen (annularOpposite v) :
            TopologicalSpace.Opens (Circle × ℝ)) := by
        rw [annularPunctures_cover v]
        trivial
      exact hx
    · exact (annularPunctureOpen v).isOpen
    · exact (annularPunctureOpen (annularOpposite v)).isOpen

/-- The Mayer--Vietoris annular generator has its canonical circle primitive
after the standard `2 * pi` normalization. -/
noncomputable def annularAngularClosedFormCirclePrimitive (v : Circle) :
    SmoothCirclePrimitive AnnularCylinderModel
      ((2 * Real.pi) • (annularAngularClosedForm v).1) where
  phase := annularAngularGlobalPhase v
  locally_has_argument := by
    intro x
    by_cases hx : x ∈ annularPunctureOpen v
    · let U := annularPunctureOpen v
      refine ⟨U, hx, annularAngularLeftArgument v, ?_, ?_⟩
      · intro y
        exact annularAngularGlobalPhaseFun_eq_left v y.2
      · have hrest := congrArg Prod.fst
          (annularAngularConnectingData v).glued_restriction
        change restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
            U 1 ((2 * Real.pi) • (annularAngularClosedForm v).1) = _
        rw [map_smul]
        change (2 * Real.pi) •
            restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
              U 1 (annularAngularClosedForm v).1 = _
        change restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
            U 1 (annularAngularClosedForm v).1 =
          deRhamDifferential (I := AnnularCylinderModel) (M := U)
            (A := ℝ) 0 (annularAngularConnectingData v).lift.1 at hrest
        rw [hrest, ← LinearMap.map_smul]
        congr 1
        apply DifferentialForm.ext
        intro y
        ext q
        rw [show q = (fun i : Fin 0 => nomatch i) from Subsingleton.elim _ _]
        change (2 * Real.pi) *
            (annularAngularConnectingData v).lift.1.toFun y
              (fun i : Fin 0 => nomatch i) =
          (2 * Real.pi) *
            (annularAngularConnectingData v).lift.1.toFun y
              (fun i : Fin 0 => nomatch i)
        rfl
    · have hxright : x ∈ annularPunctureOpen (annularOpposite v) := by
        have hcover : x ∈ annularPunctureOpen v ∨
            x ∈ annularPunctureOpen (annularOpposite v) := by
          have : x ∈ (annularPunctureOpen v ⊔
              annularPunctureOpen (annularOpposite v) :
                TopologicalSpace.Opens (Circle × ℝ)) := by
            rw [annularPunctures_cover v]
            trivial
          exact this
        exact hcover.resolve_left hx
      let U := annularPunctureOpen (annularOpposite v)
      refine ⟨U, hxright, annularAngularRightArgument v, ?_, ?_⟩
      · intro y
        exact annularAngularGlobalPhaseFun_eq_right v y.2
      · have hrest := congrArg Prod.snd
          (annularAngularConnectingData v).glued_restriction
        change restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
            U 1 ((2 * Real.pi) • (annularAngularClosedForm v).1) = _
        rw [map_smul]
        change (2 * Real.pi) •
            restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
              U 1 (annularAngularClosedForm v).1 = _
        change restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
            U 1 (annularAngularClosedForm v).1 =
          deRhamDifferential (I := AnnularCylinderModel) (M := U)
            (A := ℝ) 0 (annularAngularConnectingData v).lift.2 at hrest
        rw [hrest, ← LinearMap.map_smul]
        congr 1
        apply DifferentialForm.ext
        intro y
        ext q
        rw [show q = (fun i : Fin 0 => nomatch i) from Subsingleton.elim _ _]
        change (2 * Real.pi) *
            (annularAngularConnectingData v).lift.2.toFun y
              (fun i : Fin 0 => nomatch i) =
          (2 * Real.pi) *
            (annularAngularConnectingData v).lift.2.toFun y
              (fun i : Fin 0 => nomatch i)
        rfl

end
end Uniformization
end JJMath
