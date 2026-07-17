import JJMath.Manifold.CirclePrimitive
import JJMath.Uniformization.CompactSupportTransfer
import JJMath.Uniformization.SmoothChainConnectivity

/-!
# Circle primitives from integral smooth periods

On a connected smooth surface, a closed one-form whose smooth singular
periods are integer multiples of two pi has a smooth circle-valued primitive.
The phase is defined by exponentiating the integral along a chosen smooth
chain from a base point.  Local Poincare primitives show that this apparently
choice-dependent definition is smooth.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]

theorem integrateSmoothChain_neg_one
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1)
    (c : SingularChain (I := SurfaceRealModel) (M := X) 1 ∞) :
    integrateSmoothChain (I := SurfaceRealModel) omega (-c) =
      -integrateSmoothChain (I := SurfaceRealModel) omega c := by
  simp [integrateSmoothChain, integrateChain, integrateChainHom]

theorem integrateSmoothChain_sub_one
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1)
    (c d : SingularChain (I := SurfaceRealModel) (M := X) 1 ∞) :
    integrateSmoothChain (I := SurfaceRealModel) omega (c - d) =
      integrateSmoothChain (I := SurfaceRealModel) omega c -
        integrateSmoothChain (I := SurfaceRealModel) omega d := by
  rw [sub_eq_add_neg, integrateSmoothChain_add,
    integrateSmoothChain_neg_one]
  rfl

/-- A closed one-form on a smooth complex surface has a real primitive on a
full-plane coordinate neighborhood.  The neighborhood also comes with smooth
chains from its marked point to all of its points. -/
theorem exists_coordinateOpen_realPrimitive_and_smoothChains
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (x : X) :
    ∃ (U : TopologicalSpace.Opens X) (hxU : x ∈ U)
        (theta : C^∞⟮SurfaceRealModel, U; ℝ⟯),
      restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) U 1 omega.1 =
          deRhamDifferential (I := SurfaceRealModel) (M := U) (A := ℝ) 0
            (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) theta) ∧
      ∀ y : U,
        SmoothChainConnectivity.SmoothChainJoined
          ⟨x, hxU⟩ y := by
  rcases exists_complexPlanarChart_subordinate
      (⊤ : TopologicalSpace.Opens X) x trivial with
    ⟨U, hxU, _hUtop, hphi⟩
  let phi := Classical.choice hphi
  let omegaU : DeRhamClosedForms
      (I := SurfaceRealModel) (M := U) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionToOpen
      (I := SurfaceRealModel) (A := ℝ) U 1 omega
  let omegaPlane : DeRhamClosedForms
      (I := SurfaceRealModel) (M := complexPlanarModelOpen) (A := ℝ) 1 :=
    deRhamClosedFormsPullbackDiffeomorph
      SurfaceRealModel SurfaceRealModel phi.symm 1 omegaU
  have hconvex : Convex ℝ (complexPlanarModelOpen : Set ℂ) := by
    simpa [complexPlanarModelOpen] using (convex_univ : Convex ℝ (univ : Set ℂ))
  rcases deRham_convex_open_closed_succ_form_has_primitive
      complexPlanarModelOpen hconvex (phi ⟨x, hxU⟩) 0 omegaPlane with
    ⟨thetaPlane, hthetaPlane⟩
  let thetaU : SmoothForms (I := SurfaceRealModel) (M := U) ℝ 0 :=
    smoothFormsPullbackDiffeomorph
      SurfaceRealModel SurfaceRealModel phi 0 thetaPlane
  let theta : C^∞⟮SurfaceRealModel, U; ℝ⟯ :=
    smoothRealFunctionOfZeroForm SurfaceRealModel thetaU
  have htheta :
      restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) U 1 omega.1 =
        deRhamDifferential (I := SurfaceRealModel) (M := U) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) theta) := by
    rw [smoothRealFunctionToZeroForm_smoothRealFunctionOfZeroForm]
    change omegaU.1 = deRhamDifferential
      (I := SurfaceRealModel) (M := U) (A := ℝ) 0 thetaU
    dsimp only [thetaU]
    rw [deRhamDifferential_smoothFormsPullbackDiffeomorph,
      hthetaPlane]
    exact (smoothFormsPullbackDiffeomorph_symm_comp
      SurfaceRealModel SurfaceRealModel phi.symm omegaU.1).symm
  let planeToOpen : ℂ → complexPlanarModelOpen := fun z => ⟨z, trivial⟩
  have hplaneToOpen : Function.Surjective planeToOpen := by
    intro z
    exact ⟨z, Subtype.ext (by rfl)⟩
  letI : ConnectedSpace complexPlanarModelOpen :=
    hplaneToOpen.connectedSpace (continuous_id.subtype_mk (fun _ => trivial))
  letI : ConnectedSpace U :=
    phi.symm.surjective.connectedSpace phi.symm.continuous
  refine ⟨U, hxU, theta, htheta, ?_⟩
  intro y
  exact SmoothChainConnectivity.smoothChainJoined_all ⟨x, hxU⟩ y

/-- Exponentiating path integrals gives a smooth circle primitive when every
smooth one-cycle has period in `2 * pi * ℤ`. -/
noncomputable def smoothCirclePrimitiveOfIntegralSmoothPeriods
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (x₀ : X)
    (hperiod : ∀ c : SingularChain
        (I := SurfaceRealModel) (M := X) 1 ∞,
      boundary (I := SurfaceRealModel) c = 0 →
        ∃ k : ℤ, integrateSmoothChain (I := SurfaceRealModel) omega.1 c =
          (2 * Real.pi) * (k : ℝ)) :
    SmoothCirclePrimitive SurfaceRealModel omega.1 := by
  let chain : X → SingularChain
      (I := SurfaceRealModel) (M := X) 1 ∞ := fun x ↦
    Classical.choose (SmoothChainConnectivity.smoothChainJoined_all x₀ x)
  have hchain : ∀ x : X, boundary (I := SurfaceRealModel) (chain x) =
      Finsupp.single
          (ContMDiffSingularSimplex.point (I := SurfaceRealModel) x) (1 : ℤ) -
        Finsupp.single
          (ContMDiffSingularSimplex.point (I := SurfaceRealModel) x₀) (1 : ℤ) :=
    fun x ↦ Classical.choose_spec
      (SmoothChainConnectivity.smoothChainJoined_all x₀ x)
  let phaseFun : X → ℂ := fun x ↦
    Complex.exp
      (((integrateSmoothChain (I := SurfaceRealModel) omega.1 (chain x) : ℝ) : ℂ) *
        Complex.I)
  have hlocal : ∀ x : X,
      ∃ (U : TopologicalSpace.Opens X) (hxU : x ∈ U)
          (theta : C^∞⟮SurfaceRealModel, U; ℝ⟯),
        (∀ y : U, phaseFun (y : X) =
          Complex.exp (((theta y : ℝ) : ℂ) * Complex.I)) ∧
        restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) U 1 omega.1 =
          deRhamDifferential (I := SurfaceRealModel) (M := U) (A := ℝ) 0
            (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) theta) := by
    intro x
    rcases exists_coordinateOpen_realPrimitive_and_smoothChains omega x with
      ⟨U, hxU, localTheta, hlocalTheta, hjoined⟩
    let xU : U := ⟨x, hxU⟩
    let offset : ℝ :=
      integrateSmoothChain (I := SurfaceRealModel) omega.1 (chain x) -
        localTheta xU
    let theta : C^∞⟮SurfaceRealModel, U; ℝ⟯ :=
      { val := fun y ↦ localTheta y + offset
        property := localTheta.contMDiff.add contMDiff_const }
    refine ⟨U, hxU, theta, ?_, ?_⟩
    · intro y
      rcases hjoined y with ⟨s, hs⟩
      let sX : SingularChain (I := SurfaceRealModel) (M := X) 1 ∞ :=
        SingularChain.openInclusion (I := SurfaceRealModel) U s
      let cycle := chain (y : X) - chain x - sX
      have hcycle : boundary (I := SurfaceRealModel) cycle = 0 := by
        change boundary (I := SurfaceRealModel) (chain (y : X) - chain x - sX) = 0
        rw [map_sub, map_sub, hchain, hchain,
          ← SingularChain.openInclusion_boundary, hs]
        simp only [SingularChain.openInclusion_sub,
          SingularChain.openInclusion_single,
          ContMDiffSingularSimplex.point_openInclusion]
        abel
      rcases hperiod cycle hcycle with ⟨k, hk⟩
      have hsIntegral :
          integrateSmoothChain (I := SurfaceRealModel) omega.1 sX =
            localTheta y - localTheta xU := by
        exact integrateSmoothChain_openInclusion_eq_endpoint_sub_of_restrict_eq_d
          SurfaceRealModel U omega.1 localTheta hlocalTheta s
          (ContMDiffSingularSimplex.point (I := SurfaceRealModel) xU)
          (ContMDiffSingularSimplex.point (I := SurfaceRealModel) y) hs
      have hk' :
          integrateSmoothChain (I := SurfaceRealModel) omega.1 (chain (y : X)) =
            (localTheta y + offset) + (2 * Real.pi) * (k : ℝ) := by
        rw [integrateSmoothChain_sub_one, integrateSmoothChain_sub_one] at hk
        rw [hsIntegral] at hk
        dsimp only [offset]
        linarith
      change Complex.exp
          (((integrateSmoothChain (I := SurfaceRealModel) omega.1
            (chain (y : X)) : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((((localTheta y + offset : ℝ) : ℂ) * Complex.I))
      rw [hk']
      push_cast
      rw [add_mul, Complex.exp_add]
      have hperiodExp :
          Complex.exp
            (((((2 : ℝ) * Real.pi * (k : ℝ)) : ℝ) : ℂ) * Complex.I) = 1 := by
        rw [show (((((2 : ℝ) * Real.pi * (k : ℝ)) : ℝ) : ℂ) * Complex.I) =
            (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
          push_cast
          ring]
        exact Complex.exp_int_mul_two_pi_mul_I k
      have hperiodExp' :
          Complex.exp (2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I) = 1 := by
        convert hperiodExp using 1 <;> push_cast <;> ring
      rw [hperiodExp', mul_one]
    · have hzeroForm :
          smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) theta =
            smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) localTheta +
              smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
                (smoothRealConstantFunction
                  (I0 := SurfaceRealModel) (M0 := U) offset) := by
        apply DifferentialForm.ext
        intro y
        ext q
        rw [show q = (fun i : Fin 0 => nomatch i) from Subsingleton.elim _ _]
        rfl
      rw [hzeroForm, map_add,
        deRhamDifferential_smoothRealFunctionToZeroForm_const, add_zero]
      exact hlocalTheta
  refine
    { phase :=
        { val := phaseFun
          property := by
            intro x
            rcases hlocal x with ⟨U, hxU, theta, hphase, _htheta⟩
            let xU : U := ⟨x, hxU⟩
            rw [← contMDiffAt_subtype_iff (U := U) (x := xU)]
            have heq : (fun y : U ↦ phaseFun (y : X)) =
                fun y : U ↦ Complex.exp (((theta y : ℝ) : ℂ) * Complex.I) := by
              funext y
              exact hphase y
            rw [heq]
            have hthetaComplex : ContMDiff SurfaceRealModel
                (modelWithCornersSelf ℝ ℂ) ∞
                (fun y : U ↦ ((theta y : ℝ) : ℂ)) :=
              Complex.ofRealCLM.contDiff.contMDiff.comp theta.contMDiff
            let mulI : ℂ →L[ℝ] ℂ :=
              (ContinuousLinearMap.mulLeftRight ℝ ℂ 1) Complex.I
            have hcomp : ContMDiff SurfaceRealModel
                (modelWithCornersSelf ℝ ℂ) ∞
                (fun y : U ↦ Complex.exp (mulI ((theta y : ℝ) : ℂ))) :=
              Complex.contDiff_exp.contMDiff.comp
                (mulI.contDiff.contMDiff.comp hthetaComplex)
            have heqMul :
                (fun y : U ↦
                  Complex.exp (((theta y : ℝ) : ℂ) * Complex.I)) =
                fun y : U ↦ Complex.exp (mulI ((theta y : ℝ) : ℂ)) := by
              funext y
              congr 1
              simp [mulI, ContinuousLinearMap.mulLeftRight_apply]
            rw [heqMul]
            exact hcomp.contMDiffAt }
      locally_has_argument := by
        intro x
        rcases hlocal x with ⟨U, hxU, theta, hphase, htheta⟩
        exact ⟨U, hxU, theta, hphase, htheta⟩ }

/-- A normalized integral generator for smooth one-cycles supplies the
integral-period hypothesis needed for a circle-valued primitive. -/
noncomputable def smoothCirclePrimitiveOfNormalizedCycleGenerator
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
    (x₀ : X)
    (gamma : SingularChain
      (I := SurfaceRealModel) (M := X) 1 ∞)
    (hgammaPeriod :
      integrateSmoothChain (I := SurfaceRealModel) omega.1 gamma =
        2 * Real.pi)
    (hgenerate : ∀ c : SingularChain
        (I := SurfaceRealModel) (M := X) 1 ∞,
      boundary (I := SurfaceRealModel) c = 0 →
        ∃ (k : ℤ) (b : SingularChain
            (I := SurfaceRealModel) (M := X) 2 ∞),
          c = k • gamma + boundary (I := SurfaceRealModel) b) :
    SmoothCirclePrimitive SurfaceRealModel omega.1 := by
  apply smoothCirclePrimitiveOfIntegralSmoothPeriods omega x₀
  intro c hc
  rcases hgenerate c hc with ⟨k, b, rfl⟩
  refine ⟨k, ?_⟩
  rw [integrateSmoothChain_add,
    integrateSmoothChain_boundary_eq_zero_of_closed, add_zero,
    integrateSmoothChain_zsmul]
  rw [hgammaPeriod]
  ring

end

end JJMath.Uniformization
