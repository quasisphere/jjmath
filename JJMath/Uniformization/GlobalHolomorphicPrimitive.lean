import JJMath.Uniformization.HarmonicConjugateDeRham

/-!
# Restricting a conjugate differential to a global holomorphic branch

When a harmonic real part has a single holomorphic branch on an open set,
the glued conjugate differential restricts there to the differential of that
branch's imaginary part.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

theorem mfderiv_opensInclusion_bijective
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I 1 M]
    (W U : TopologicalSpace.Opens M) (hWU : W ≤ U) (x : W) :
    Function.Bijective
      (mfderiv I I (TopologicalSpace.Opens.inclusion hWU) x) := by
  let xU : U := TopologicalSpace.Opens.inclusion hWU x
  let LWU : TangentSpace I x →L[ℝ] TangentSpace I xU :=
    mfderiv I I (TopologicalSpace.Opens.inclusion hWU) x
  let LU : TangentSpace I xU →L[ℝ] TangentSpace I (x : M) :=
    mfderiv I I (fun y : U => (y : M)) xU
  let LW : TangentSpace I x →L[ℝ] TangentSpace I (x : M) :=
    mfderiv I I (fun y : W => (y : M)) x
  have hfactor : LU.comp LWU = LW := by
    simpa [LU, LWU, LW, xU] using
      mfderiv_subtypeVal_comp_inclusion_eq (I := I) W U hWU x
  have hLU := mfderiv_subtypeVal_bijective (I := I) U xU
  have hLW := mfderiv_subtypeVal_bijective (I := I) W x
  constructor
  · intro a b hab
    apply hLW.1
    have := congrArg (fun T : TangentSpace I x →L[ℝ]
        TangentSpace I (x : M) => T) hfactor
    change LW a = LW b
    rw [← hfactor]
    exact congrArg LU hab
  · intro y
    rcases hLW.2 (LU y) with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply hLU.1
    change LU (LWU z) = LU y
    calc
      LU (LWU z) = LW z :=
        congrArg (fun T : TangentSpace I x →L[ℝ]
          TangentSpace I (x : M) => T z) hfactor
      _ = LU y := hz

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
theorem HarmonicConjugateDifferentialData.restrict_eq_globalHolomorphicRealPart
    {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [ComplexOneManifold Z] [IsManifold 𝓘(ℝ, ℂ) ∞ Z]
    {u : Z → ℝ}
    {hbranches : ∀ p : Z,
      ∃ B : SurfaceHolomorphicRealPartBranch Z u, p ∈ B.source}
    (D : HarmonicConjugateDifferentialData hbranches)
    (U : TopologicalSpace.Opens Z) (L : Z → ℂ)
    (hL : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U)
    (theta : C^∞⟮𝓘(ℝ, ℂ), U; ℝ⟯)
    (htheta : ∀ x : U, theta x = (L (x : Z)).im)
    (hre : ∀ x : U, (L (x : Z)).re = u x) :
    restrictSmoothFormsToOpen (I := 𝓘(ℝ, ℂ)) (A := ℝ) U 1 D.omega =
      deRhamDifferential (I := 𝓘(ℝ, ℂ)) (M := U) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := 𝓘(ℝ, ℂ)) theta) := by
  apply DifferentialForm.ext
  intro x
  let e : OpenPartialHomeomorph Z ℂ := chartAt ℂ (x : Z)
  have he : e ∈ atlas ℂ Z := chart_mem_atlas ℂ (x : Z)
  let Scoord : Set ℂ := e.target ∩ e.symm ⁻¹' (U : Set Z)
  have hSopen : IsOpen Scoord := by
    simpa [Scoord] using e.isOpen_inter_preimage_symm U.is_open'
  have hxS : e (x : Z) ∈ Scoord := by
    refine ⟨e.map_source (mem_chart_source ℂ (x : Z)), ?_⟩
    simpa [e.left_inv (mem_chart_source ℂ (x : Z))] using x.2
  rcases Metric.isOpen_iff.mp hSopen (e (x : Z)) hxS with
    ⟨R, hRpos, hballS⟩
  let coordinateSource : Set ℂ := Metric.ball (e (x : Z)) R
  let source : Set Z := e.source ∩ e ⁻¹' coordinateSource
  have hsourceOpen : IsOpen source :=
    e.isOpen_inter_preimage Metric.isOpen_ball
  have hcoordTarget : coordinateSource ⊆ e.target := by
    intro z hz
    exact (hballS (by simpa [coordinateSource] using hz)).1
  have hcoordU : ∀ z ∈ coordinateSource, e.symm z ∈ U := by
    intro z hz
    exact (hballS (by simpa [coordinateSource] using hz)).2
  let F : ℂ → ℂ := fun z => L (e.symm z)
  have hsymm : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm coordinateSource :=
    (mdifferentiableOn_atlas_symm (I := 𝓘(ℂ)) he).mono hcoordTarget
  have hFmdiff : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F coordinateSource := by
    have hcomp := hL.comp hsymm (by
      intro z hz
      exact hcoordU z hz)
    simpa [F, Function.comp_def] using hcomp
  have hFanalytic : AnalyticOnNhd ℂ F coordinateSource := by
    apply (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
    exact mdifferentiableOn_iff_differentiableOn.mp hFmdiff
  let B : SurfaceHolomorphicRealPartBranch Z u :=
    { source := source
      source_open := hsourceOpen
      chart := e
      chart_mem_atlas := he
      coordinateSource := coordinateSource
      coordinateSource_open := Metric.isOpen_ball
      coordinateSource_subset_chart_target := hcoordTarget
      source_eq := rfl
      potential := F
      potential_holomorphic := hFanalytic
      potential_re_eq := by
        intro z hz
        have hzTarget := hcoordTarget hz
        let zU : U := ⟨e.symm z, hcoordU z hz⟩
        simpa [F, zU, e.right_inv hzTarget] using hre zU }
  have hxB : (x : Z) ∈ B.source := by
    refine ⟨mem_chart_source ℂ (x : Z), ?_⟩
    change e (x : Z) ∈ Metric.ball (e (x : Z)) R
    exact Metric.mem_ball_self hRpos
  let W : TopologicalSpace.Opens Z := ⟨B.source, B.source_open⟩
  have hWU : W ≤ U := by
    intro y hy
    have hyChart : y ∈ e.source := hy.1
    have hyCoord : e y ∈ coordinateSource := hy.2
    have hback : e.symm (e y) ∈ U := hcoordU (e y) hyCoord
    simpa [e.left_inv hyChart] using hback
  let thetaB : SmoothForms (I := 𝓘(ℝ, ℂ)) (M := W) ℝ 0 :=
    smoothRealFunctionToZeroForm (I0 := 𝓘(ℝ, ℂ))
      B.imaginarySmoothFunction
  have hzero :
      restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWU 0
          (smoothRealFunctionToZeroForm (I0 := 𝓘(ℝ, ℂ)) theta) =
        thetaB := by
    apply DifferentialForm.ext
    intro y
    ext q
    rw [show q = (fun i : Fin 0 => nomatch i) from Subsingleton.elim _ _]
    have hyChart : (y : Z) ∈ e.source := y.2.1
    have htotal : B.toSurfaceTotalFunction (y : Z) = L (y : Z) := by
      simp [B, SurfaceHolomorphicRealPartBranch.toSurfaceTotalFunction,
        F, e.left_inv hyChart]
    have hthetaY := htheta (TopologicalSpace.Opens.inclusion hWU y)
    have him := congrArg Complex.im htotal
    simp [thetaB, restrictSmoothFormsOfLE, restrictSmoothFormOfLE,
      smoothRealFunctionToZeroForm,
      SurfaceHolomorphicRealPartBranch.imaginarySmoothFunction] at hthetaY him ⊢
    exact hthetaY.trans him.symm
  let alpha : SmoothForms (I := 𝓘(ℝ, ℂ)) (M := U) ℝ 1 :=
    restrictSmoothFormsToOpen (I := 𝓘(ℝ, ℂ)) (A := ℝ) U 1 D.omega
  let beta : SmoothForms (I := 𝓘(ℝ, ℂ)) (M := U) ℝ 1 :=
    deRhamDifferential (I := 𝓘(ℝ, ℂ)) (M := U) (A := ℝ) 0
      (smoothRealFunctionToZeroForm (I0 := 𝓘(ℝ, ℂ)) theta)
  have halpha :
      restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWU 1 alpha =
        B.imaginaryDifferential := by
    have htrans :=
      restrictSmoothFormsToOpen_eq_restrictSmoothFormsOfLE_of_restrict_eq
        W U hWU D.omega alpha rfl
    rw [← htrans]
    exact D.restrict_eq B
  have hbeta :
      restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWU 1 beta =
        B.imaginaryDifferential := by
    change restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWU 1
        (deRhamDifferential (I := 𝓘(ℝ, ℂ)) (M := U) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := 𝓘(ℝ, ℂ)) theta)) =
      deRhamDifferential (I := 𝓘(ℝ, ℂ)) (M := W) (A := ℝ) 0 thetaB
    rw [← deRhamDifferential_restrictSmoothFormsOfLE, hzero]
  have hrestr :
      restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWU 1 alpha =
        restrictSmoothFormsOfLE (I := 𝓘(ℝ, ℂ)) (A := ℝ) hWU 1 beta :=
    halpha.trans hbeta.symm
  let xW : W := ⟨(x : Z), hxB⟩
  let xU : U := TopologicalSpace.Opens.inclusion hWU xW
  have hxU : xU = x := by
    apply Subtype.ext
    rfl
  have hpoint := congrArg
    (fun eta : SmoothForms (I := 𝓘(ℝ, ℂ)) (M := W) ℝ 1 => eta.toFun xW)
    hrestr
  let Linc : TangentSpace 𝓘(ℝ, ℂ) xW →L[ℝ]
      TangentSpace 𝓘(ℝ, ℂ) xU :=
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (TopologicalSpace.Opens.inclusion hWU) xW
  apply continuousAlternatingMap_compContinuousLinearMap_injective Linc
    (mfderiv_opensInclusion_bijective
      𝓘(ℝ, ℂ) W U hWU xW).2
  simpa [alpha, beta, Linc, xU, hxU, restrictSmoothFormsOfLE,
    restrictSmoothFormOfLE] using hpoint

end
end JJMath.Uniformization
