import JJMath.Uniformization.BoundaryComponentPeriod
import JJMath.Uniformization.SmoothChainConnectivity

/-!
# A primitive after cutting at a second boundary component

The compactly supported boundary-component form becomes exact after retaining
the domain, one complementary component, and the transition band around their
chosen common boundary component.  Its primitive is the transition step on
the band, zero on the domain side, and one on the complementary side.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Uniformization

noncomputable section

open JJMath.Manifold

/-- The open region obtained from a smooth domain, a transition band, and one
component of the complement of the domain closure. -/
def BoundaryComponentTransition.exactRegion
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ) :
    TopologicalSpace.Opens X :=
  ⟨(D.carrier ∪ (T.band : Set X)) ∪ V,
    (D.isOpen.union T.band.isOpen).union
      (hV.isOpen_of_isOpen isClosed_closure.isOpen_compl)⟩

/-- Extend the local step set-theoretically outside its band.  Only its germ
at points of the band will be used. -/
def BoundaryComponentTransition.stepExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) : X → ℝ :=
  Subtype.val.extend T.step 0

@[simp]
theorem BoundaryComponentTransition.stepExtension_apply_of_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) {x : X}
    (hx : x ∈ (T.band : Set X)) :
    T.stepExtension x = T.step ⟨x, hx⟩ := by
  exact Subtype.val_injective.extend_apply T.step 0 ⟨x, hx⟩

/-- The set-theoretic primitive: use the step on the band, zero on the domain
side outside the band, and one on the chosen complementary side. -/
noncomputable def BoundaryComponentTransition.exactPrimitiveFunction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) : X → ℝ := by
  classical
  exact fun x => if hx : x ∈ (T.band : Set X) then T.step ⟨x, hx⟩
    else if x ∈ D.carrier then 0 else 1

/-- The step extension is smooth at every point of its original band. -/
theorem BoundaryComponentTransition.contMDiffAt_stepExtension_of_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) {x : X}
    (hx : x ∈ (T.band : Set X)) :
    ContMDiffAt SurfaceRealModel 𝓘(ℝ, ℝ) ∞ T.stepExtension x := by
  let xb : T.band := ⟨x, hx⟩
  apply (contMDiffAt_subtype_iff (U := T.band) (x := xb)).mp
  apply (T.step.contMDiff xb).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => by
    exact T.stepExtension_apply_of_mem y.2

/-- On the retained open region, the piecewise primitive is smooth. -/
theorem BoundaryComponentTransition.contMDiff_exactPrimitiveFunction_on_exactRegion
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ) :
    ContMDiff SurfaceRealModel 𝓘(ℝ, ℝ) ∞
      (fun x : T.exactRegion V hV => T.exactPrimitiveFunction (x : X)) := by
  intro x
  apply (contMDiffAt_subtype_iff
    (U := T.exactRegion V hV) (x := x)).mpr
  by_cases hxband : (x : X) ∈ (T.band : Set X)
  · apply (T.contMDiffAt_stepExtension_of_mem hxband).congr_of_eventuallyEq
    filter_upwards [T.band.isOpen.mem_nhds hxband] with y hyband
    simp only [BoundaryComponentTransition.exactPrimitiveFunction, hyband,
      dite_true]
    exact (T.stepExtension_apply_of_mem hyband).symm
  · have hxside : (x : X) ∈ D.carrier ∨ (x : X) ∈ V := by
      rcases x.2 with hx | hxV
      · exact Or.inl (hx.resolve_right hxband)
      · exact Or.inr hxV
    rcases hxside with hxD | hxV
    · by_cases hxclosure : (x : X) ∈ closure (T.band : Set X)
      · have hxfrontier : (x : X) ∈ frontier (T.band : Set X) := by
          rw [frontier, T.band.isOpen.interior_eq]
          exact ⟨hxclosure, hxband⟩
        have hxN : (x : X) ∈ T.signed.neighborhood :=
          T.closure_subset_signed hxclosure
        have hxcoord_neg : T.signed.coordinate (x : X) < 0 :=
          (T.signed.domain_iff_neg (x : X) hxN).mp hxD
        have hxgap := T.frontier_gap (x : X) hxfrontier
        have hxcoord_lt : T.signed.coordinate (x : X) < -T.epsilon := by
          rw [abs_of_nonpos hxcoord_neg.le] at hxgap
          linarith [T.epsilon_pos]
        have hcoord_cont : ContinuousAt T.signed.coordinate (x : X) :=
          T.signed.coordinate_continuous.continuousAt
            (T.signed.neighborhood_isOpen.mem_nhds hxN)
        apply (show ContMDiffAt SurfaceRealModel 𝓘(ℝ, ℝ) ∞
            (fun _ : X => (0 : ℝ)) (x : X) from
          contMDiffAt_const).congr_of_eventuallyEq
        filter_upwards
          [D.isOpen.mem_nhds hxD,
            hcoord_cont.eventually_lt continuousAt_const hxcoord_lt] with
            y hyD hycoord
        by_cases hyband : y ∈ (T.band : Set X)
        · simp only [BoundaryComponentTransition.exactPrimitiveFunction,
              hyband, dite_true]
          exact T.step_eq_zero ⟨y, hyband⟩ hycoord.le
        · simp [BoundaryComponentTransition.exactPrimitiveFunction,
            hyband, hyD]
      · apply (show ContMDiffAt SurfaceRealModel 𝓘(ℝ, ℝ) ∞
            (fun _ : X => (0 : ℝ)) (x : X) from
          contMDiffAt_const).congr_of_eventuallyEq
        filter_upwards
          [D.isOpen.mem_nhds hxD,
            isClosed_closure.isOpen_compl.mem_nhds hxclosure] with
            y hyD hyclosure
        have hyband : y ∉ (T.band : Set X) :=
          fun hy => hyclosure (subset_closure hy)
        simp [BoundaryComponentTransition.exactPrimitiveFunction,
          hyband, hyD]
    · have hVopen : IsOpen V :=
        hV.isOpen_of_isOpen isClosed_closure.isOpen_compl
      have hxnotD : (x : X) ∉ D.carrier := by
        intro hxD
        exact hV.subset hxV (subset_closure hxD)
      by_cases hxclosure : (x : X) ∈ closure (T.band : Set X)
      · have hxfrontier : (x : X) ∈ frontier (T.band : Set X) := by
          rw [frontier, T.band.isOpen.interior_eq]
          exact ⟨hxclosure, hxband⟩
        have hxN : (x : X) ∈ T.signed.neighborhood :=
          T.closure_subset_signed hxclosure
        have hxcoord_nonneg : 0 ≤ T.signed.coordinate (x : X) := by
          exact le_of_not_gt fun hneg =>
            hxnotD ((T.signed.domain_iff_neg (x : X) hxN).mpr hneg)
        have hxnotfrontier : (x : X) ∉ frontier D.carrier := by
          intro hxfrontierD
          exact hV.subset hxV (frontier_subset_closure hxfrontierD)
        have hxcoord_ne : T.signed.coordinate (x : X) ≠ 0 := by
          intro hzero
          exact hxnotfrontier
            ((T.signed.frontier_iff_zero (x : X) hxN).mpr hzero)
        have hxcoord_pos : 0 < T.signed.coordinate (x : X) :=
          lt_of_le_of_ne hxcoord_nonneg (Ne.symm hxcoord_ne)
        have hxgap := T.frontier_gap (x : X) hxfrontier
        rw [abs_of_pos hxcoord_pos] at hxgap
        have hxcoord_gt : T.epsilon < T.signed.coordinate (x : X) := by
          linarith [T.epsilon_pos]
        have hcoord_cont : ContinuousAt T.signed.coordinate (x : X) :=
          T.signed.coordinate_continuous.continuousAt
            (T.signed.neighborhood_isOpen.mem_nhds hxN)
        apply (show ContMDiffAt SurfaceRealModel 𝓘(ℝ, ℝ) ∞
            (fun _ : X => (1 : ℝ)) (x : X) from
          contMDiffAt_const).congr_of_eventuallyEq
        filter_upwards
          [hVopen.mem_nhds hxV,
            continuousAt_const.eventually_lt hcoord_cont hxcoord_gt] with
            y hyV hycoord
        have hynotD : y ∉ D.carrier := by
          intro hyD
          exact hV.subset hyV (subset_closure hyD)
        by_cases hyband : y ∈ (T.band : Set X)
        · simp only [BoundaryComponentTransition.exactPrimitiveFunction,
              hyband, dite_true]
          exact T.step_eq_one ⟨y, hyband⟩ hycoord.le
        · simp [BoundaryComponentTransition.exactPrimitiveFunction,
            hyband, hynotD]
      · apply (show ContMDiffAt SurfaceRealModel 𝓘(ℝ, ℝ) ∞
            (fun _ : X => (1 : ℝ)) (x : X) from
          contMDiffAt_const).congr_of_eventuallyEq
        filter_upwards
          [hVopen.mem_nhds hxV,
            isClosed_closure.isOpen_compl.mem_nhds hxclosure] with
            y hyV hyclosure
        have hynotD : y ∉ D.carrier := by
          intro hyD
          exact hV.subset hyV (subset_closure hyD)
        have hyband : y ∉ (T.band : Set X) :=
          fun hy => hyclosure (subset_closure hy)
        simp [BoundaryComponentTransition.exactPrimitiveFunction,
          hyband, hynotD]

/-- The smooth primitive of the boundary-component form on the retained
domain-band-component region. -/
noncomputable def BoundaryComponentTransition.exactPrimitive
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ) :
    C^∞⟮SurfaceRealModel, T.exactRegion V hV; ℝ⟯ where
  val := fun x => T.exactPrimitiveFunction (x : X)
  property := T.contMDiff_exactPrimitiveFunction_on_exactRegion V hV

/-- If a form on a larger open set restricts to zero on a smaller open set,
then it vanishes at every point of the smaller set. -/
theorem smoothForms_toFun_eq_zero_of_restrictSmoothFormsOfLE_eq_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {W V : TopologicalSpace.Opens X} (hWV : W ≤ V) {n : ℕ}
    (omega : SmoothForms (I := SurfaceRealModel) (M := V) ℝ n)
    (hzero : restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ)
      hWV n omega = 0)
    (x : V) (hxW : (x : X) ∈ W) :
    omega.toFun x = 0 := by
  let xW : W := ⟨(x : X), hxW⟩
  have hxinc : TopologicalSpace.Opens.inclusion hWV xW = x := by
    apply Subtype.ext
    rfl
  have hpoint := congrArg
    (fun form : SmoothForms (I := SurfaceRealModel) (M := W) ℝ n =>
      form.toFun xW) hzero
  change (omega.toFun (TopologicalSpace.Opens.inclusion hWV xW)).compContinuousLinearMap
      (mfderiv SurfaceRealModel SurfaceRealModel
        (TopologicalSpace.Opens.inclusion hWV) xW) = 0 at hpoint
  rw [hxinc] at hpoint
  exact continuousAlternatingMap_compContinuousLinearMap_injective
    (mfderiv SurfaceRealModel SurfaceRealModel
      (TopologicalSpace.Opens.inclusion hWV) xW)
    ((mfderiv_opens_inclusion_isInvertible
      (I := SurfaceRealModel) W V hWV xW).surjective)
    hpoint

/-- The exact-region primitive restricts to the original transition step on
the band. -/
theorem BoundaryComponentTransition.restrict_exactPrimitive_zeroForm_band
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ) :
    let hband : T.band ≤ T.exactRegion V hV := fun _ hx => Or.inl (Or.inr hx)
    restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ)
        hband 0
        (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
          (T.exactPrimitive V hV)) =
      smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) T.step := by
  dsimp only
  apply DifferentialForm.ext
  intro x
  ext v
  simp [restrictSmoothFormsOfLE, restrictSmoothFormOfLE,
    smoothRealFunctionToZeroForm,
    BoundaryComponentTransition.exactPrimitive,
    BoundaryComponentTransition.exactPrimitiveFunction]

/-- On the transition band, the restriction of the global form is the
differential of the exact-region primitive. -/
theorem BoundaryComponentTransition.restrict_globalOneForm_exactRegion_band_eq_d
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ) :
    let hband : T.band ≤ T.exactRegion V hV := fun _ hx => Or.inl (Or.inr hx)
    restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ)
        hband 1
        (restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ)
          (T.exactRegion V hV) 1 T.globalOneForm) =
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ)
        hband 1
        (deRhamDifferential (I := SurfaceRealModel)
          (M := T.exactRegion V hV) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
            (T.exactPrimitive V hV))) := by
  dsimp only
  rw [restrictSmoothFormsOfLE_restrictSmoothFormsToOpen_eq,
    T.globalOneForm_restrict_band,
    ← deRhamDifferential_restrictSmoothFormsOfLE]
  rw [T.restrict_exactPrimitive_zeroForm_band]
  rfl

/-- Away from the transition band, the exact-region primitive is locally
constant. -/
theorem BoundaryComponentTransition.exactPrimitiveFunction_eventuallyEq_const_of_not_mem_band
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (x : T.exactRegion V hV) (hxband : (x : X) ∉ (T.band : Set X)) :
    ∃ c : ℝ, T.exactPrimitiveFunction =ᶠ[𝓝 (x : X)] fun _ => c := by
  have hxside : (x : X) ∈ D.carrier ∨ (x : X) ∈ V := by
    rcases x.2 with hx | hxV
    · exact Or.inl (hx.resolve_right hxband)
    · exact Or.inr hxV
  rcases hxside with hxD | hxV
  · refine ⟨0, ?_⟩
    by_cases hxclosure : (x : X) ∈ closure (T.band : Set X)
    · have hxfrontier : (x : X) ∈ frontier (T.band : Set X) := by
        rw [frontier, T.band.isOpen.interior_eq]
        exact ⟨hxclosure, hxband⟩
      have hxN : (x : X) ∈ T.signed.neighborhood :=
        T.closure_subset_signed hxclosure
      have hxcoord_neg : T.signed.coordinate (x : X) < 0 :=
        (T.signed.domain_iff_neg (x : X) hxN).mp hxD
      have hxgap := T.frontier_gap (x : X) hxfrontier
      rw [abs_of_nonpos hxcoord_neg.le] at hxgap
      have hxcoord_lt : T.signed.coordinate (x : X) < -T.epsilon := by
        linarith [T.epsilon_pos]
      have hcoord_cont : ContinuousAt T.signed.coordinate (x : X) :=
        T.signed.coordinate_continuous.continuousAt
          (T.signed.neighborhood_isOpen.mem_nhds hxN)
      filter_upwards
        [D.isOpen.mem_nhds hxD,
          hcoord_cont.eventually_lt continuousAt_const hxcoord_lt] with
          y hyD hycoord
      by_cases hyband : y ∈ (T.band : Set X)
      · simp only [BoundaryComponentTransition.exactPrimitiveFunction,
            hyband, dite_true]
        exact T.step_eq_zero ⟨y, hyband⟩ hycoord.le
      · simp [BoundaryComponentTransition.exactPrimitiveFunction,
          hyband, hyD]
    · filter_upwards
        [D.isOpen.mem_nhds hxD,
          isClosed_closure.isOpen_compl.mem_nhds hxclosure] with
          y hyD hyclosure
      have hyband : y ∉ (T.band : Set X) :=
        fun hy => hyclosure (subset_closure hy)
      simp [BoundaryComponentTransition.exactPrimitiveFunction,
        hyband, hyD]
  · refine ⟨1, ?_⟩
    have hVopen : IsOpen V :=
      hV.isOpen_of_isOpen isClosed_closure.isOpen_compl
    by_cases hxclosure : (x : X) ∈ closure (T.band : Set X)
    · have hxfrontier : (x : X) ∈ frontier (T.band : Set X) := by
        rw [frontier, T.band.isOpen.interior_eq]
        exact ⟨hxclosure, hxband⟩
      have hxN : (x : X) ∈ T.signed.neighborhood :=
        T.closure_subset_signed hxclosure
      have hxnotD : (x : X) ∉ D.carrier := by
        intro hxD
        exact hV.subset hxV (subset_closure hxD)
      have hxcoord_nonneg : 0 ≤ T.signed.coordinate (x : X) :=
        le_of_not_gt fun hneg =>
          hxnotD ((T.signed.domain_iff_neg (x : X) hxN).mpr hneg)
      have hxnotfrontier : (x : X) ∉ frontier D.carrier := by
        intro hxfrontierD
        exact hV.subset hxV (frontier_subset_closure hxfrontierD)
      have hxcoord_ne : T.signed.coordinate (x : X) ≠ 0 := by
        intro hzero
        exact hxnotfrontier
          ((T.signed.frontier_iff_zero (x : X) hxN).mpr hzero)
      have hxcoord_pos : 0 < T.signed.coordinate (x : X) :=
        lt_of_le_of_ne hxcoord_nonneg (Ne.symm hxcoord_ne)
      have hxgap := T.frontier_gap (x : X) hxfrontier
      rw [abs_of_pos hxcoord_pos] at hxgap
      have hxcoord_gt : T.epsilon < T.signed.coordinate (x : X) := by
        linarith [T.epsilon_pos]
      have hcoord_cont : ContinuousAt T.signed.coordinate (x : X) :=
        T.signed.coordinate_continuous.continuousAt
          (T.signed.neighborhood_isOpen.mem_nhds hxN)
      filter_upwards
        [hVopen.mem_nhds hxV,
          continuousAt_const.eventually_lt hcoord_cont hxcoord_gt] with
          y hyV hycoord
      have hynotD : y ∉ D.carrier := by
        intro hyD
        exact hV.subset hyV (subset_closure hyD)
      by_cases hyband : y ∈ (T.band : Set X)
      · simp only [BoundaryComponentTransition.exactPrimitiveFunction,
            hyband, dite_true]
        exact T.step_eq_one ⟨y, hyband⟩ hycoord.le
      · simp [BoundaryComponentTransition.exactPrimitiveFunction,
          hyband, hynotD]
    · filter_upwards
        [hVopen.mem_nhds hxV,
          isClosed_closure.isOpen_compl.mem_nhds hxclosure] with
          y hyV hyclosure
      have hynotD : y ∉ D.carrier := by
        intro hyD
        exact hV.subset hyV (subset_closure hyD)
      have hyband : y ∉ (T.band : Set X) :=
        fun hy => hyclosure (subset_closure hy)
      simp [BoundaryComponentTransition.exactPrimitiveFunction,
        hyband, hynotD]

/-- Off the transition band, the differential of the exact-region primitive
vanishes. -/
theorem BoundaryComponentTransition.deRhamDifferential_exactPrimitive_toFun_eq_zero_of_not_mem_band
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (x : T.exactRegion V hV) (hxband : (x : X) ∉ (T.band : Set X)) :
    (deRhamDifferential (I := SurfaceRealModel)
      (M := T.exactRegion V hV) (A := ℝ) 0
      (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
        (T.exactPrimitive V hV))).toFun x = 0 := by
  rcases T.exactPrimitiveFunction_eventuallyEq_const_of_not_mem_band
      V hV x hxband with ⟨c, hc⟩
  let constant : C^∞⟮SurfaceRealModel, T.exactRegion V hV; ℝ⟯ :=
    smoothRealConstantFunction (I0 := SurfaceRealModel) c
  have hzeroForms : ∀ᶠ y in 𝓝 x,
      (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
        (T.exactPrimitive V hV)).toFun y =
      (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) constant).toFun y := by
    have hc' := (continuous_subtype_val.tendsto x) hc
    filter_upwards [hc'] with y hy
    change T.exactPrimitiveFunction (y : X) = c at hy
    change ContinuousAlternatingMap.constOfIsEmpty ℝ
        (TangentSpace SurfaceRealModel y) (Fin 0)
          (T.exactPrimitiveFunction (y : X)) =
      ContinuousAlternatingMap.constOfIsEmpty ℝ
        (TangentSpace SurfaceRealModel y) (Fin 0) c
    rw [hy]
  rw [deRhamDifferential_toFun_eq_of_eventuallyEq
    (I := SurfaceRealModel)
    (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
      (T.exactPrimitive V hV))
    (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) constant)
    hzeroForms]
  rw [deRhamDifferential_smoothRealFunctionToZeroForm_const
    (I0 := SurfaceRealModel) (M0 := T.exactRegion V hV) c]
  rfl

/--
%%handwave
name:
  Exactness of the boundary-component form on its transition region
statement:
  Let \(D\) be a smooth domain, let \(B\) be a chosen frontier component,
  and let \(V\) be an adjacent component of \(X\setminus\overline D\).  On
  the open region \(W=D\cup N(B)\cup V\), the compactly supported transition
  form \(\omega_B\) satisfies
  \[
    \omega_B|_W=dh,
  \]
  where \(h\) is its globally defined transition primitive on \(W\).
proof:
  On the transition band this is the defining derivative identity.  Outside
  the compact core, both \(\omega_B\) and \(dh\) vanish; equality on these
  two regions gives equality throughout \(W\).
-/
theorem BoundaryComponentTransition.restrict_globalOneForm_exactRegion_eq_d
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ) :
    restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ)
        (T.exactRegion V hV) 1 T.globalOneForm =
      deRhamDifferential (I := SurfaceRealModel)
        (M := T.exactRegion V hV) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
          (T.exactPrimitive V hV)) := by
  let W := T.exactRegion V hV
  let hband : T.band ≤ W := fun x hx => Or.inl (Or.inr hx)
  let omegaW := restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ)
    W 1 T.globalOneForm
  let dH := deRhamDifferential (I := SurfaceRealModel) (M := W) (A := ℝ) 0
    (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
      (T.exactPrimitive V hV))
  have hband_eq : restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ)
      hband 1 omegaW =
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ)
        hband 1 dH := by
    exact T.restrict_globalOneForm_exactRegion_band_eq_d V hV
  apply DifferentialForm.ext
  intro x
  by_cases hxband : (x : X) ∈ (T.band : Set X)
  · let eta : SmoothForms (I := SurfaceRealModel) (M := W) ℝ 1 :=
      omegaW - dH
    have heta_restrict :
        restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ)
          hband 1 eta = 0 := by
      rw [map_sub, hband_eq, sub_self]
    have heta_zero :=
      smoothForms_toFun_eq_zero_of_restrictSmoothFormsOfLE_eq_zero
        hband eta heta_restrict x hxband
    change omegaW.toFun x - dH.toFun x = 0 at heta_zero
    exact sub_eq_zero.mp heta_zero
  · have hxcore : (x : X) ∉ T.core := by
      intro hxcore
      exact hxband (T.core_subset_band hxcore)
    have hxext : (x : X) ∈ T.exteriorOpen := hxcore
    have hglobal_zero : T.globalOneForm.toFun (x : X) = 0 :=
      smoothForms_eq_zero_of_restrictSmoothFormsToOpen_zero_eq_at
        (I := SurfaceRealModel) (A := ℝ) T.exteriorOpen T.globalOneForm
        T.globalOneForm_restrict_exterior hxext
    have homegaW_zero : omegaW.toFun x = 0 := by
      simp only [omegaW]
      change (T.globalOneForm.toFun (x : X)).compContinuousLinearMap
          (mfderiv SurfaceRealModel SurfaceRealModel
            (fun y : W => (y : X)) x) = 0
      rw [hglobal_zero]
      rfl
    have hdH_zero : dH.toFun x = 0 := by
      exact T.deRhamDifferential_exactPrimitive_toFun_eq_zero_of_not_mem_band
        V hV x hxband
    rw [homegaW_zero, hdH_zero]

/-- On the domain side and outside the compact transition core, the primitive
has value zero. -/
theorem BoundaryComponentTransition.exactPrimitive_eq_zero_of_mem_domain_of_not_mem_core
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (x : T.exactRegion V hV) (hxD : (x : X) ∈ D.carrier)
    (hxcore : (x : X) ∉ T.core) :
    T.exactPrimitive V hV x = 0 := by
  by_cases hxband : (x : X) ∈ (T.band : Set X)
  · have hxclosure : (x : X) ∈ closure (T.band : Set X) :=
      subset_closure hxband
    have hxabs : T.epsilon < |T.signed.coordinate (x : X)| := by
      exact lt_of_not_ge fun hle => hxcore ⟨hxclosure, hle⟩
    have hxN : (x : X) ∈ T.signed.neighborhood :=
      T.closure_subset_signed hxclosure
    have hxneg : T.signed.coordinate (x : X) < 0 :=
      (T.signed.domain_iff_neg (x : X) hxN).mp hxD
    rw [abs_of_nonpos hxneg.le] at hxabs
    rw [show T.exactPrimitive V hV x =
      T.exactPrimitiveFunction (x : X) by rfl]
    simp only [BoundaryComponentTransition.exactPrimitiveFunction,
      hxband, dite_true]
    exact T.step_eq_zero ⟨(x : X), hxband⟩ (by linarith)
  · simp [BoundaryComponentTransition.exactPrimitive,
      BoundaryComponentTransition.exactPrimitiveFunction, hxband, hxD]

/-- On the chosen complementary side and outside the compact transition
core, the primitive has value one. -/
theorem BoundaryComponentTransition.exactPrimitive_eq_one_of_mem_component_of_not_mem_core
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (x : T.exactRegion V hV) (hxV : (x : X) ∈ V)
    (hxcore : (x : X) ∉ T.core) :
    T.exactPrimitive V hV x = 1 := by
  have hxnotD : (x : X) ∉ D.carrier := by
    intro hxD
    exact hV.subset hxV (subset_closure hxD)
  by_cases hxband : (x : X) ∈ (T.band : Set X)
  · have hxclosure : (x : X) ∈ closure (T.band : Set X) :=
      subset_closure hxband
    have hxabs : T.epsilon < |T.signed.coordinate (x : X)| := by
      exact lt_of_not_ge fun hle => hxcore ⟨hxclosure, hle⟩
    have hxN : (x : X) ∈ T.signed.neighborhood :=
      T.closure_subset_signed hxclosure
    have hxnonneg : 0 ≤ T.signed.coordinate (x : X) :=
      le_of_not_gt fun hneg =>
        hxnotD ((T.signed.domain_iff_neg (x : X) hxN).mpr hneg)
    rw [abs_of_nonneg hxnonneg] at hxabs
    rw [show T.exactPrimitive V hV x =
      T.exactPrimitiveFunction (x : X) by rfl]
    simp only [BoundaryComponentTransition.exactPrimitiveFunction,
      hxband, dite_true]
    exact T.step_eq_one ⟨(x : X), hxband⟩ hxabs.le
  · simp [BoundaryComponentTransition.exactPrimitive,
      BoundaryComponentTransition.exactPrimitiveFunction, hxband, hxnotD]

/--
%%handwave
name:
  Smooth chains across an exact transition region
statement:
  Let \(D\) be preconnected, let \(V\) be an adjacent component of
  \(X\setminus\overline D\), and let \(W=D\cup N(B)\cup V\) be the exact
  transition region about an incident frontier component \(B\).  For every
  \(a\in D\) and \(b\in V\), there is a finite smooth singular one-chain
  \(c\) in \(W\) with
  \[
    \partial c=b-a.
  \]
proof:
  The component of the transition band containing the chosen frontier point
  meets both \(D\) and \(V\).  Preconnectedness of these three overlapping
  pieces places \(a\) and \(b\) in one connected open component of \(W\),
  where smooth-chain connectivity supplies \(c\).
-/
theorem BoundaryComponentTransition.exists_exactRegion_chain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p)
    (hDpre : IsPreconnected D.carrier)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (hpV : (p : X) ∈ frontier V)
    (a b : X) (haD : a ∈ D.carrier) (hbV : b ∈ V) :
    ∃ c : SingularChain
        (I := SurfaceRealModel) (M := T.exactRegion V hV) 1 ∞,
      boundary (I := SurfaceRealModel) c =
        Finsupp.single (ContMDiffSingularSimplex.point
          (I := SurfaceRealModel)
          (⟨b, Or.inr hbV⟩ : T.exactRegion V hV)) (1 : ℤ) -
        Finsupp.single (ContMDiffSingularSimplex.point
          (I := SurfaceRealModel)
          (⟨a, Or.inl (Or.inl haD)⟩ : T.exactRegion V hV)) (1 : ℤ) := by
  let B : Set X := connectedComponentIn (T.band : Set X) (p : X)
  have hpband : (p : X) ∈ (T.band : Set X) :=
    T.component_subset ⟨p, mem_connectedComponent, rfl⟩
  have hpB : (p : X) ∈ B := mem_connectedComponentIn hpband
  have hBopen : IsOpen B := T.band.isOpen.connectedComponentIn
  have hBpre : IsPreconnected B := isPreconnected_connectedComponentIn
  have hDB : (D.carrier ∩ B).Nonempty := by
    rcases (mem_closure_iff.mp (frontier_subset_closure p.2)) B hBopen hpB with
      ⟨x, hxB, hxD⟩
    exact ⟨x, hxD, hxB⟩
  have hBV : (B ∩ V).Nonempty :=
    (mem_closure_iff.mp (frontier_subset_closure hpV)) B hBopen hpB
  have hDBpre : IsPreconnected (D.carrier ∪ B) :=
    hDpre.union' hDB hBpre
  have hDBV : ((D.carrier ∪ B) ∩ V).Nonempty := by
    rcases hBV with ⟨x, hxB, hxV⟩
    exact ⟨x, Or.inr hxB, hxV⟩
  have hSpre : IsPreconnected ((D.carrier ∪ B) ∪ V) :=
    hDBpre.union' hDBV hV.isPreconnected
  let W : TopologicalSpace.Opens X := T.exactRegion V hV
  have hSsub : (D.carrier ∪ B) ∪ V ⊆ (W : Set X) := by
    rintro x ((hxD | hxB) | hxV)
    · exact Or.inl (Or.inl hxD)
    · exact Or.inl (Or.inr (connectedComponentIn_subset _ _ hxB))
    · exact Or.inr hxV
  have haW : a ∈ (W : Set X) := Or.inl (Or.inl haD)
  have hbW : b ∈ (W : Set X) := Or.inr hbV
  have hbC : b ∈ connectedComponentIn (W : Set X) a := by
    exact hSpre.subset_connectedComponentIn
      (Or.inl (Or.inl haD)) hSsub (Or.inr hbV)
  let C : TopologicalSpace.Opens X :=
    ⟨connectedComponentIn (W : Set X) a, W.isOpen.connectedComponentIn⟩
  have haC : a ∈ (C : Set X) := mem_connectedComponentIn haW
  have hCconnected : IsConnected (C : Set X) :=
    ⟨⟨a, haC⟩, isPreconnected_connectedComponentIn⟩
  letI : ConnectedSpace C := isConnected_iff_connectedSpace.mp hCconnected
  let aC : C := ⟨a, haC⟩
  let bC : C := ⟨b, hbC⟩
  rcases SmoothChainConnectivity.smoothChainJoined_all aC bC with ⟨c, hc⟩
  have hCW : C ≤ W := connectedComponentIn_subset (W : Set X) a
  refine ⟨SingularChain.nestedOpenInclusion
    (I := SurfaceRealModel) hCW c, ?_⟩
  rw [← SingularChain.nestedOpenInclusion_boundary
    (I := SurfaceRealModel) hCW c, hc]
  simp [aC, bC]

/--
%%handwave
name:
  Two incident frontier components force nonzero first cohomology
statement:
  Let \(D\) be a preconnected smooth domain and let \(V\) be a component of
  \(X\setminus\overline D\).  If \(\partial V\) meets two distinct connected
  components of \(\partial D\), then
  \[
    H^1_{\mathrm{dR}}(X;\mathbb R)\neq0.
  \]
proof:
  Around one frontier component, the transition form has a primitive that is
  \(0\) on the domain side and \(1\) on the \(V\)-side.  Join these sides by
  a long chain in the primitive region and return near the second frontier
  component, outside the compact support of the form.  The resulting cycle
  has period \(1\).
-/
theorem BoundaryComponentTransition.not_subsingleton_deRhamH1_of_two_frontier_components
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p)
    (hDpre : IsPreconnected D.carrier)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ)
    (hpV : (p : X) ∈ frontier V)
    (q : frontier D.carrier) (hqV : (q : X) ∈ frontier V)
    (hqcomponent : q ∉ connectedComponent p) :
    ¬ Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1) := by
  have hqnotcore : (q : X) ∉ T.core := by
    intro hqcore
    have hqN : (q : X) ∈ T.signed.neighborhood :=
      T.closure_subset_signed hqcore.1
    have hqcarrier :
        (q : X) ∈ frontierComponentCarrier D.carrier p := by
      rw [← T.signed.frontier_inter]
      exact ⟨hqN, q.2⟩
    rcases hqcarrier with ⟨y, hycomponent, hyq⟩
    have hy_eq_q : y = q := Subtype.ext hyq
    exact hqcomponent (hy_eq_q ▸ hycomponent)
  have hqext : (q : X) ∈ (T.exteriorOpen : Set X) := hqnotcore
  let qE : T.exteriorOpen := ⟨(q : X), hqext⟩
  rcases SmoothChainConnectivity.exists_open_smoothChainJoined_from qE with
    ⟨O, hOopen, hqO, hjoin⟩
  let OX : Set X := Subtype.val '' O
  have hOXopen : IsOpen OX := by
    exact T.exteriorOpen.isOpen.isOpenEmbedding_subtypeVal.isOpenMap O hOopen
  have hqOX : (q : X) ∈ OX := ⟨qE, hqO, rfl⟩
  have hOD : (OX ∩ D.carrier).Nonempty :=
    (mem_closure_iff.mp (frontier_subset_closure q.2)) OX hOXopen hqOX
  have hOV : (OX ∩ V).Nonempty :=
    (mem_closure_iff.mp (frontier_subset_closure hqV)) OX hOXopen hqOX
  rcases hOD with ⟨_a, ⟨aE, haO, rfl⟩, haD⟩
  rcases hOV with ⟨_b, ⟨bE, hbO, rfl⟩, hbV⟩
  rcases SmoothChainConnectivity.smoothChainJoined_trans
      (SmoothChainConnectivity.smoothChainJoined_symm (hjoin bE hbO))
      (hjoin aE haO) with
    ⟨bridge, hbridge⟩
  rcases T.exists_exactRegion_chain hDpre V hV hpV
      (aE : X) (bE : X) haD hbV with
    ⟨long, hlong⟩
  let aU : T.exactRegion V hV :=
    ⟨(aE : X), Or.inl (Or.inl haD)⟩
  let bU : T.exactRegion V hV :=
    ⟨(bE : X), Or.inr hbV⟩
  have haPrimitive : T.exactPrimitive V hV aU = 0 :=
    T.exactPrimitive_eq_zero_of_mem_domain_of_not_mem_core
      V hV aU haD aE.2
  have hbPrimitive : T.exactPrimitive V hV bU = 1 :=
    T.exactPrimitive_eq_one_of_mem_component_of_not_mem_core
      V hV bU hbV bE.2
  apply not_subsingleton_deRhamH1_of_cut_primitive_and_zero_bridge
    (I := SurfaceRealModel) T.closedOneForm
    (T.exactRegion V hV) T.exteriorOpen (T.exactPrimitive V hV)
    (T.restrict_globalOneForm_exactRegion_eq_d V hV)
    T.globalOneForm_restrict_exterior
    long
    (ContMDiffSingularSimplex.point (I := SurfaceRealModel) aU)
    (ContMDiffSingularSimplex.point (I := SurfaceRealModel) bU)
    hlong haPrimitive hbPrimitive bridge
  rw [map_add,
      ← SingularChain.openInclusion_boundary
        (I := SurfaceRealModel) (T.exactRegion V hV) long,
      hlong,
      ← SingularChain.openInclusion_boundary
        (I := SurfaceRealModel) T.exteriorOpen bridge,
      hbridge]
  simp

/-- The frontier of a component of the complement of a smooth-domain closure
lies in the smooth frontier of the domain. -/
theorem IsComponentOf.frontier_subset_smoothBoundaryDomain_frontier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : SmoothBoundaryDomain X) (V : Set X)
    (hV : IsComponentOf V (closure D.carrier)ᶜ) :
    frontier V ⊆ frontier D.carrier := by
  have hsubset : frontier V ⊆ frontier (closure D.carrier)ᶜ :=
    hV.frontier_subset_frontier_of_isOpen isClosed_closure.isOpen_compl
  rw [frontier_compl] at hsubset
  exact hsubset.trans frontier_closure_subset

/--
%%handwave
name:
  Complementary frontiers are connected when \(H^1_{\mathrm{dR}}=0\)
statement:
  Let \(X\) be a noncompact Riemann surface with
  \(H^1_{\mathrm{dR}}(X;\mathbb R)=0\), let \(D\subseteq X\) be a nonempty
  preconnected smooth domain, and let \(V\) be a component of
  \(X\setminus\overline D\).  Then \(\partial V\) is connected.
proof:
  Choose \(p\in\partial V\).  If another point of \(\partial V\) lay in a
  different connected component of \(\partial D\), the transition-form
  construction would produce a nonzero class in
  \(H^1_{\mathrm{dR}}(X;\mathbb R)\).  Hence \(\partial V\) is precisely the
  connected frontier component containing \(p\).
-/
theorem smoothBoundaryDomain_complement_component_frontier_isConnected_of_deRhamH1_subsingleton
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (hnoncompact : ¬ CompactSpace X)
    (D : SmoothBoundaryDomain X)
    (hDnonempty : D.carrier.Nonempty)
    (hDpre : IsPreconnected D.carrier)
    (V : Set X) (hV : IsComponentOf V (closure D.carrier)ᶜ) :
    IsConnected (frontier V) := by
  rcases hV.frontier_inter_frontier_nonempty_of_compl_isClosed
      isClosed_closure (hDnonempty.mono subset_closure) with
    ⟨x, hxV, hxclosureD⟩
  have hxD : x ∈ frontier D.carrier := frontier_closure_subset hxclosureD
  let p : frontier D.carrier := ⟨x, hxD⟩
  rcases exists_boundaryComponentTransition hnoncompact D p with ⟨T⟩
  have hfrontier_eq :
      frontier V = frontierComponentCarrier D.carrier p := by
    apply Subset.antisymm
    · intro y hyV
      have hyD : y ∈ frontier D.carrier :=
        hV.frontier_subset_smoothBoundaryDomain_frontier D V hyV
      let q : frontier D.carrier := ⟨y, hyD⟩
      have hqcomponent : q ∈ connectedComponent p := by
        by_contra hqnot
        exact (T.not_subsingleton_deRhamH1_of_two_frontier_components
          hDpre V hV hxV q hyV hqnot) inferInstance
      exact ⟨q, hqcomponent, rfl⟩
    · rintro y ⟨q, hqcomponent, rfl⟩
      exact smoothBoundaryDomain_connected_boundary_component_subset_frontier_of_incident
        D p V hV hxV q hqcomponent
  rw [hfrontier_eq]
  exact (isConnected_connectedComponent (x := p)).image
    Subtype.val continuous_subtype_val.continuousOn

end
end Uniformization
end JJMath
