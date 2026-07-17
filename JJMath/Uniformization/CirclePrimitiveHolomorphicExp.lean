import JJMath.Manifold.CirclePrimitive
import JJMath.Uniformization.HarmonicConjugateDeRham

/-!
# Holomorphic exponentials from circle-valued conjugates

A harmonic function need not admit a globally real-valued harmonic conjugate.
For exponentiation it is enough that its conjugate differential admit a
circle-valued primitive.  Locally the circle argument and the imaginary part
of a holomorphic real-part branch have the same differential, so they differ
by a constant.  Multiplying the phase by the exponential of the harmonic
function is therefore locally a constant multiple of a holomorphic
exponential.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

/-- A circle-valued primitive of the conjugate differential of a harmonic
function produces a global nonvanishing holomorphic function with the
prescribed logarithmic modulus. -/
theorem harmonicConjugate_circlePrimitive_has_holomorphic_exp
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [RiemannSurface Z] [IsManifold SurfaceRealModel ∞ Z]
    {u : Z → ℝ}
    {hbranches : ∀ p : Z,
      ∃ B : SurfaceHolomorphicRealPartBranch Z u, p ∈ B.source}
    (D : HarmonicConjugateDifferentialData hbranches)
    (P : SmoothCirclePrimitive SurfaceRealModel D.omega) :
    ∃ f : Z → ℂ,
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧
        (∀ z, f z ≠ 0) ∧
          ∀ z, Real.log ‖f z‖ = u z := by
  classical
  let f : Z → ℂ := fun z => (Real.exp (u z) : ℂ) * P.phase z
  have hf_local : ∀ x : Z, ∃ W : Set Z,
      IsOpen W ∧ x ∈ W ∧
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f W := by
    intro x
    rcases hbranches x with ⟨B, hxB⟩
    rcases P.locally_has_argument x with
      ⟨U, hxU, theta, hphase, htheta⟩
    rcases (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp
        (B.source_open.inter U.isOpen |>.mem_nhds ⟨hxB, hxU⟩) with
      ⟨Wset, ⟨hWopen, hxW, hWconnected⟩, hWsubset⟩
    let W : TopologicalSpace.Opens Z := ⟨Wset, hWopen⟩
    let UB : TopologicalSpace.Opens Z := ⟨B.source, B.source_open⟩
    have hWB : W ≤ UB := fun _ hy => (hWsubset hy).1
    have hWU : W ≤ U := fun _ hy => (hWsubset hy).2
    let thetaW : SmoothForms (I := SurfaceRealModel) (M := W) ℝ 0 :=
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ) hWU 0
        (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) theta)
    let thetaB : SmoothForms (I := SurfaceRealModel) (M := UB) ℝ 0 :=
      smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
        B.imaginarySmoothFunction
    let thetaBW : SmoothForms (I := SurfaceRealModel) (M := W) ℝ 0 :=
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ) hWB 0 thetaB
    have hdtheta :
        deRhamDifferential (I := SurfaceRealModel) (M := W) (A := ℝ) 0 thetaW =
          deRhamDifferential (I := SurfaceRealModel) (M := W) (A := ℝ) 0
            thetaBW := by
      calc
        _ = restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ) hWU 1
              (deRhamDifferential (I := SurfaceRealModel) (M := U) (A := ℝ) 0
                (smoothRealFunctionToZeroForm
                  (I0 := SurfaceRealModel) theta)) :=
            deRhamDifferential_restrictSmoothFormsOfLE
              (I := SurfaceRealModel) (A := ℝ) hWU _
        _ = restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ) hWU 1
              (restrictSmoothFormsToOpen
                (I := SurfaceRealModel) (A := ℝ) U 1 D.omega) := by
            rw [← htheta]
        _ = restrictSmoothFormsToOpen
              (I := SurfaceRealModel) (A := ℝ) W 1 D.omega := by
            exact (restrictSmoothFormsToOpen_eq_restrictSmoothFormsOfLE_of_restrict_eq
              W U hWU D.omega
                (restrictSmoothFormsToOpen
                  (I := SurfaceRealModel) (A := ℝ) U 1 D.omega) rfl).symm
        _ = restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ) hWB 1
              B.imaginaryDifferential :=
            restrictSmoothFormsToOpen_eq_restrictSmoothFormsOfLE_of_restrict_eq
              W UB hWB D.omega B.imaginaryDifferential (D.restrict_eq B)
        _ = _ := by
            change restrictSmoothFormsOfLE
                (I := SurfaceRealModel) (A := ℝ) hWB 1
                (deRhamDifferential (I := SurfaceRealModel)
                  (M := UB) (A := ℝ) 0 thetaB) = _
            exact (deRhamDifferential_restrictSmoothFormsOfLE
              (I := SurfaceRealModel) (A := ℝ) hWB thetaB).symm
    let xW : W := ⟨x, hxW⟩
    let c : ℝ :=
      thetaW.toFun xW (fun i : Fin 0 => nomatch i) -
        thetaBW.toFun xW (fun i : Fin 0 => nomatch i)
    let constC : SmoothForms (I := SurfaceRealModel) (M := W) ℝ 0 :=
      smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
        (smoothRealConstantFunction (I0 := SurfaceRealModel) c)
    letI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hWconnected
    have htheta_local : thetaW = thetaBW + constC := by
      apply SmoothChainConnectivity.smoothZeroForm_eq_of_differential_eq_of_eq_at
        thetaW (thetaBW + constC) xW
      · rw [map_add,
          deRhamDifferential_smoothRealFunctionToZeroForm_const, add_zero]
        exact hdtheta
      · change _ = _ + c
        rw [show c = _ - _ by rfl, add_comm]
        exact (sub_add_cancel _ _).symm
    have htheta_value : ∀ y : W,
        theta (TopologicalSpace.Opens.inclusion hWU y) =
          (B.toSurfaceTotalFunction (y : Z)).im + c := by
      intro y
      have hval := congrArg
        (fun eta : SmoothForms (I := SurfaceRealModel) (M := W) ℝ 0 =>
          eta.toFun y (fun i : Fin 0 => nomatch i)) htheta_local
      convert hval using 1
    have hf_eq : ∀ y ∈ Wset,
        f y = Complex.exp ((c : ℂ) * Complex.I) *
          Complex.exp (B.toSurfaceTotalFunction y) := by
      intro y hy
      let yW : W := ⟨y, hy⟩
      let yU : U := TopologicalSpace.Opens.inclusion hWU yW
      have hyB : y ∈ B.source := hWB hy
      have hre := B.toSurfaceTotalFunction_re_eq hyB
      have harg := htheta_value yW
      have hphaseY := hphase yU
      dsimp [f]
      rw [show P.phase y = P.phase (yU : Z) by rfl, hphaseY]
      rw [harg]
      rw [show (Real.exp (u y) : ℂ) =
          Complex.exp ((u y : ℝ) : ℂ) by
        rw [Complex.ofReal_exp]]
      rw [← hre]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      apply Complex.ext <;> simp <;> ring
    refine ⟨Wset, hWopen, hxW, ?_⟩
    have hbranch : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
        B.toSurfaceTotalFunction Wset :=
      B.toSurfaceTotalFunction_mdifferentiableOn.mono hWB
    have hexp : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Complex.exp :=
      mdifferentiable_iff_differentiable.mpr Complex.differentiable_exp
    have htranslated : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
        (fun y => Complex.exp ((c : ℂ) * Complex.I) *
          Complex.exp (B.toSurfaceTotalFunction y)) Wset :=
      (mdifferentiableOn_const (c := Complex.exp ((c : ℂ) * Complex.I))).mul
        (hexp.comp_mdifferentiableOn hbranch)
    exact htranslated.congr hf_eq
  have hf_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
    rw [← mdifferentiableOn_univ]
    apply mdifferentiableOn_of_locally_mdifferentiableOn
    intro x _hx
    rcases hf_local x with ⟨W, hWopen, hxW, hFW⟩
    exact ⟨W, hWopen, hxW, by simpa using hFW⟩
  refine ⟨f, hf_hol, ?_, ?_⟩
  · intro z
    exact mul_ne_zero (by
      exact_mod_cast (Real.exp_ne_zero (u z)))
        (SmoothCirclePrimitive.phase_ne_zero SurfaceRealModel P z)
  · intro z
    rw [norm_mul,
      SmoothCirclePrimitive.norm_phase_eq_one SurfaceRealModel P, mul_one]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos (u z)), Real.log_exp]

end

end JJMath.Uniformization
