import JJMath.Manifold.CirclePrimitive

/-!
# Uniqueness of the one-form represented by a circle phase

A smooth unit-complex phase determines its logarithmic one-form uniquely.
Indeed, any two local real arguments of the same phase differ locally by an
integer multiple of `2 * pi`, so their differentials agree.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Manifold

noncomputable section

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]

namespace SmoothCirclePrimitive

/-- A smooth circle phase represents at most one real one-form. -/
theorem oneForm_eq_of_phase_eq
    {omega eta : SmoothForms (I := I) (M := M) ℝ 1}
    (P : SmoothCirclePrimitive I omega)
    (Q : SmoothCirclePrimitive I eta)
    (hphase : ∀ x, P.phase x = Q.phase x) : omega = eta := by
  apply DifferentialForm.ext
  intro x
  rcases P.locally_has_argument x with
    ⟨U, hxU, theta, hPphase, homega⟩
  rcases Q.locally_has_argument x with
    ⟨V, hxV, psi, hQphase, heta⟩
  let W : TopologicalSpace.Opens M := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let thetaW : C^∞⟮I, W; ℝ⟯ :=
    { val := fun y ↦ theta (TopologicalSpace.Opens.inclusion inf_le_left y)
      property := theta.contMDiff.comp
        (contMDiff_inclusion (I := I) (n := ∞) inf_le_left) }
  let psiW : C^∞⟮I, W; ℝ⟯ :=
    { val := fun y ↦ psi (TopologicalSpace.Opens.inclusion inf_le_right y)
      property := psi.contMDiff.comp
        (contMDiff_inclusion (I := I) (n := ∞) inf_le_right) }
  have hexp : ∀ y : W,
      Complex.exp ((((thetaW y : ℝ) : ℂ) * Complex.I)) =
        Complex.exp ((((psiW y : ℝ) : ℂ) * Complex.I)) := by
    intro y
    change Complex.exp
        (((theta (TopologicalSpace.Opens.inclusion inf_le_left y) : ℝ) : ℂ) *
          Complex.I) =
      Complex.exp
        (((psi (TopologicalSpace.Opens.inclusion inf_le_right y) : ℝ) : ℂ) *
          Complex.I)
    rw [← hPphase (TopologicalSpace.Opens.inclusion inf_le_left y),
      ← hQphase (TopologicalSpace.Opens.inclusion inf_le_right y)]
    exact hphase (y : M)
  have hdelta : IsLocallyConstant (fun y : W ↦ thetaW y - psiW y) :=
    isLocallyConstant_sub_of_exp_mul_I_eq
      (fun y : W ↦ thetaW y) (fun y : W ↦ psiW y)
      thetaW.contMDiff.continuous psiW.contMDiff.continuous hexp
  let delta : C^∞⟮I, W; ℝ⟯ :=
    { val := fun y ↦ thetaW y - psiW y
      property := thetaW.contMDiff.sub psiW.contMDiff }
  have hdeltaSmooth :
      smoothRealFunctionOfIsLocallyConstant I
          (fun y : W ↦ thetaW y - psiW y) hdelta = delta := by
    ext y
    rfl
  have hzeroForm :
      smoothRealFunctionToZeroForm (I0 := I) delta =
        smoothRealFunctionToZeroForm (I0 := I) thetaW -
          smoothRealFunctionToZeroForm (I0 := I) psiW := by
    apply DifferentialForm.ext
    intro y
    ext q
    rw [show q = (fun i : Fin 0 ↦ nomatch i) from Subsingleton.elim _ _]
    rfl
  have hdiff :
      deRhamDifferential (I := I) (M := W) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := I) thetaW) =
        deRhamDifferential (I := I) (M := W) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := I) psiW) := by
    have hzero := deRhamDifferential_locallyConstant_zeroForm_eq_zero
      (I0 := I) (fun y : W ↦ thetaW y - psiW y) hdelta
    rw [hdeltaSmooth, hzeroForm, map_sub, sub_eq_zero] at hzero
    exact hzero
  have homegaW :
      restrictSmoothFormsToOpen (I := I) (A := ℝ) W 1 omega =
        deRhamDifferential (I := I) (M := W) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := I) thetaW) := by
    calc
      restrictSmoothFormsToOpen (I := I) (A := ℝ) W 1 omega =
          restrictSmoothFormsOfLE (I := I) (A := ℝ) inf_le_left 1
            (restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1 omega) :=
        (restrictSmoothFormsOfLE_restrictSmoothFormsToOpen_eq
          (I := I) (A := ℝ) inf_le_left omega).symm
      _ = restrictSmoothFormsOfLE (I := I) (A := ℝ) inf_le_left 1
            (deRhamDifferential (I := I) (M := U) (A := ℝ) 0
              (smoothRealFunctionToZeroForm (I0 := I) theta)) := by rw [homega]
      _ = deRhamDifferential (I := I) (M := W) (A := ℝ) 0
            (restrictSmoothFormsOfLE (I := I) (A := ℝ) inf_le_left 0
              (smoothRealFunctionToZeroForm (I0 := I) theta)) := by
        rw [deRhamDifferential_restrictSmoothFormsOfLE]
      _ = deRhamDifferential (I := I) (M := W) (A := ℝ) 0
            (smoothRealFunctionToZeroForm (I0 := I) thetaW) := by
        congr 1
  have hetaW :
      restrictSmoothFormsToOpen (I := I) (A := ℝ) W 1 eta =
        deRhamDifferential (I := I) (M := W) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := I) psiW) := by
    calc
      restrictSmoothFormsToOpen (I := I) (A := ℝ) W 1 eta =
          restrictSmoothFormsOfLE (I := I) (A := ℝ) inf_le_right 1
            (restrictSmoothFormsToOpen (I := I) (A := ℝ) V 1 eta) :=
        (restrictSmoothFormsOfLE_restrictSmoothFormsToOpen_eq
          (I := I) (A := ℝ) inf_le_right eta).symm
      _ = restrictSmoothFormsOfLE (I := I) (A := ℝ) inf_le_right 1
            (deRhamDifferential (I := I) (M := V) (A := ℝ) 0
              (smoothRealFunctionToZeroForm (I0 := I) psi)) := by rw [heta]
      _ = deRhamDifferential (I := I) (M := W) (A := ℝ) 0
            (restrictSmoothFormsOfLE (I := I) (A := ℝ) inf_le_right 0
              (smoothRealFunctionToZeroForm (I0 := I) psi)) := by
        rw [deRhamDifferential_restrictSmoothFormsOfLE]
      _ = deRhamDifferential (I := I) (M := W) (A := ℝ) 0
            (smoothRealFunctionToZeroForm (I0 := I) psiW) := by
        congr 1
  have hrestrict :
      restrictSmoothFormsToOpen (I := I) (A := ℝ) W 1 omega =
        restrictSmoothFormsToOpen (I := I) (A := ℝ) W 1 eta := by
    rw [homegaW, hetaW, hdiff]
  have hpoint := congrArg
    (fun z : SmoothForms (I := I) (M := W) ℝ 1 ↦ z.toFun ⟨x, hxW⟩)
    hrestrict
  exact continuousAlternatingMap_compContinuousLinearMap_injective
    (mfderiv I I (fun y : W ↦ (y : M)) ⟨x, hxW⟩)
    (mfderiv_subtypeVal_surjective (I := I) W ⟨x, hxW⟩) hpoint

/-- If one circle phase is obtained from another by multiplication by the
exponential of a global real function, then their represented one-forms
differ by the differential of that function. -/
theorem oneForm_eq_addExact_of_phase_eq
    {omega eta : SmoothForms (I := I) (M := M) ℝ 1}
    (P : SmoothCirclePrimitive I omega)
    (Q : SmoothCirclePrimitive I eta)
    (theta : C^∞⟮I, M; ℝ⟯)
    (hphase : ∀ x, P.phase x = Q.phase x *
      Complex.exp ((((theta x : ℝ) : ℂ) * Complex.I))) :
    omega = eta +
      deRhamDifferential (I := I) (M := M) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := I) theta) := by
  apply oneForm_eq_of_phase_eq I P (SmoothCirclePrimitive.addExact I Q theta)
  exact hphase

/-- A one-form admitting a smooth circle primitive is closed. -/
theorem isClosed
    {omega : SmoothForms (I := I) (M := M) ℝ 1}
    (P : SmoothCirclePrimitive I omega) :
    deRhamDifferential (I := I) (M := M) (A := ℝ) 1 omega = 0 := by
  apply DifferentialForm.ext
  intro x
  rcases P.locally_has_argument x with
    ⟨U, hxU, theta, _hphase, homega⟩
  have hlocalClosed :
      deRhamDifferential (I := I) (M := U) (A := ℝ) 1
          (restrictSmoothFormsToOpen (I := I) (A := ℝ) U 1 omega) = 0 := by
    rw [homega]
    exact deRhamDifferential_comp_eq_zero
      (I := I) (A := ℝ)
      (smoothRealFunctionToZeroForm (I0 := I) theta)
  have hrestrict :
      restrictSmoothFormsToOpen (I := I) (A := ℝ) U 2
          (deRhamDifferential (I := I) (M := M) (A := ℝ) 1 omega) = 0 := by
    rw [← deRhamDifferential_restrictSmoothFormsToOpen]
    exact hlocalClosed
  exact smoothForms_eq_zero_of_restrictSmoothFormsToOpen_zero_eq_at
    (I := I) (A := ℝ) U
    (deRhamDifferential (I := I) (M := M) (A := ℝ) 1 omega)
    hrestrict hxU

/-- Package the represented one-form of a circle primitive as a closed form. -/
def toClosedForm
    {omega : SmoothForms (I := I) (M := M) ℝ 1}
    (P : SmoothCirclePrimitive I omega) :
    DeRhamClosedForms (I := I) (M := M) (A := ℝ) 1 :=
  ⟨omega, P.isClosed I⟩

end SmoothCirclePrimitive

end
end JJMath.Manifold
