import JJMath.ComplexProjective.Prerequisites.RiemannSurface
import JJMath.ProjectiveGeometry.Mobius
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# The standard complex structure on the Riemann sphere

The Riemann sphere is the one-point compactification of the complex plane.  Its
standard complex atlas has the affine coordinate away from infinity and the
reciprocal coordinate away from zero.
-/

namespace JJMath

open Set
open scoped Manifold Topology

noncomputable section

local instance : DecidableEq RiemannSphere := Classical.decEq RiemannSphere

/-- Inversion on the Riemann sphere is an involution. -/
theorem riemannSphereInv_involutive : Function.Involutive riemannSphereInv := by
  intro z
  induction z using OnePoint.rec with
  | infty => simp
  | coe z =>
      by_cases hz : z = 0
      · subst z
        simp
      · rw [riemannSphereInv_coe_of_ne_zero hz]
        rw [riemannSphereInv_coe_of_ne_zero (inv_ne_zero hz)]
        simp

@[simp]
theorem riemannSphereInv_inv (z : RiemannSphere) :
    riemannSphereInv (riemannSphereInv z) = z :=
  riemannSphereInv_involutive z

/-- Inversion as a self-homeomorphism of the Riemann sphere. -/
def riemannSphereInvHomeomorph : RiemannSphere ≃ₜ RiemannSphere where
  toFun := riemannSphereInv
  invFun := riemannSphereInv
  left_inv := riemannSphereInv_involutive
  right_inv := riemannSphereInv_involutive
  continuous_toFun := riemannSphereInv_continuous
  continuous_invFun := riemannSphereInv_continuous

@[simp]
theorem riemannSphereInvHomeomorph_apply (z : RiemannSphere) :
    riemannSphereInvHomeomorph z = riemannSphereInv z :=
  rfl

/-- The affine coordinate on the finite part of the Riemann sphere. -/
def riemannSphereFiniteChart : OpenPartialHomeomorph RiemannSphere ℂ :=
  (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph
    ((↑) : ℂ → RiemannSphere)).symm

@[simp]
theorem riemannSphereFiniteChart_source :
    riemannSphereFiniteChart.source = ({OnePoint.infty} : Set RiemannSphere)ᶜ := by
  simp [riemannSphereFiniteChart, OnePoint.compl_infty]

@[simp]
theorem riemannSphereFiniteChart_target :
    riemannSphereFiniteChart.target = Set.univ := by
  simp [riemannSphereFiniteChart]

@[simp]
theorem riemannSphereFiniteChart_coe (z : ℂ) :
    riemannSphereFiniteChart (z : RiemannSphere) = z := by
  simpa [riemannSphereFiniteChart] using
    (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
      ((↑) : ℂ → RiemannSphere) OnePoint.isOpenEmbedding_coe (x := z))

@[simp]
theorem riemannSphereFiniteChart_symm_apply (z : ℂ) :
    riemannSphereFiniteChart.symm z = (z : RiemannSphere) :=
  rfl

/-- The reciprocal coordinate near infinity. -/
def riemannSphereInfinityChart : OpenPartialHomeomorph RiemannSphere ℂ :=
  riemannSphereInvHomeomorph.toOpenPartialHomeomorph.trans riemannSphereFiniteChart

@[simp]
theorem riemannSphereInfinityChart_source :
    riemannSphereInfinityChart.source = ({((0 : ℂ) : RiemannSphere)} : Set RiemannSphere)ᶜ := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp [riemannSphereInfinityChart]
  | coe z =>
      by_cases hz : z = 0
      · subst z
        simp [riemannSphereInfinityChart]
      · simp [riemannSphereInfinityChart, hz, riemannSphereInv_coe_of_ne_zero]

@[simp]
theorem riemannSphereInfinityChart_target :
    riemannSphereInfinityChart.target = Set.univ := by
  simp [riemannSphereInfinityChart]

@[simp]
theorem riemannSphereInfinityChart_symm_apply (z : ℂ) :
    riemannSphereInfinityChart.symm z = riemannSphereInv (z : RiemannSphere) :=
  rfl

@[simp]
theorem riemannSphereInfinityChart_infty :
    riemannSphereInfinityChart OnePoint.infty = 0 := by
  simp [riemannSphereInfinityChart]

@[simp]
theorem riemannSphereInfinityChart_coe_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    riemannSphereInfinityChart (z : RiemannSphere) = z⁻¹ := by
  simp [riemannSphereInfinityChart, riemannSphereInv_coe_of_ne_zero hz]

@[simp]
theorem riemannSphereInfinityChart_inv_coe (z : ℂ) :
    riemannSphereInfinityChart (riemannSphereInv (z : RiemannSphere)) = z := by
  by_cases hz : z = 0
  · subst z
    simp
  · simp [riemannSphereInv_coe_of_ne_zero hz, inv_ne_zero hz]

/-- The standard two-chart complex atlas on the Riemann sphere. -/
noncomputable instance instChartedSpaceComplexRiemannSphere :
    ChartedSpace ℂ RiemannSphere where
  atlas := {riemannSphereFiniteChart, riemannSphereInfinityChart}
  chartAt z := if z = OnePoint.infty then
      riemannSphereInfinityChart
    else
      riemannSphereFiniteChart
  mem_chart_source z := by
    by_cases hz : z = OnePoint.infty
    · subst z
      simp
    · simp [hz]
  chart_mem_atlas z := by
    by_cases hz : z = OnePoint.infty <;> simp [hz]

@[simp]
theorem chartAt_riemannSphere_infty :
    chartAt ℂ (OnePoint.infty : RiemannSphere) = riemannSphereInfinityChart := by
  rw [show chartAt ℂ (OnePoint.infty : RiemannSphere) =
    if (OnePoint.infty : RiemannSphere) = OnePoint.infty then
      riemannSphereInfinityChart else riemannSphereFiniteChart from rfl]
  simp

@[simp]
theorem chartAt_riemannSphere_coe (z : ℂ) :
    chartAt ℂ (z : RiemannSphere) = riemannSphereFiniteChart := by
  rw [show chartAt ℂ (z : RiemannSphere) =
    if (z : RiemannSphere) = OnePoint.infty then
      riemannSphereInfinityChart else riemannSphereFiniteChart from rfl]
  simp

/--
%%handwave
name:
  Standard complex structure on the Riemann sphere
statement:
  The affine coordinate \(z\) on
  \(\widehat{\mathbb C}\setminus\{\infty\}\) and the reciprocal coordinate
  \(1/z\) on \(\widehat{\mathbb C}\setminus\{0\}\) form a complex atlas on
  the one-point compactification \(\widehat{\mathbb C}\).
proof:
  The two cross-transitions are \(z\mapsto 1/z\) away from zero; the two
  self-transitions are the identity.
-/
noncomputable instance instComplexOneManifoldRiemannSphere :
    ComplexOneManifold RiemannSphere where
  toT2Space := inferInstance
  toIsManifold := by
    apply isManifold_of_contDiffOn 𝓘(ℂ) ⊤ RiemannSphere
    intro e e' he he'
    change e ∈ ({riemannSphereFiniteChart, riemannSphereInfinityChart} :
      Set (OpenPartialHomeomorph RiemannSphere ℂ)) at he
    change e' ∈ ({riemannSphereFiniteChart, riemannSphereInfinityChart} :
      Set (OpenPartialHomeomorph RiemannSphere ℂ)) at he'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he he'
    rcases he with rfl | rfl <;> rcases he' with rfl | rfl
    · refine
        (contDiff_id : ContDiff ℂ ⊤ (id : ℂ → ℂ)).contDiffOn.congr_mono ?_
          (subset_univ _)
      intro x _hx
      simp [Function.comp_def]
    · refine
        (contDiffOn_inv (𝕜 := ℂ) (𝕜' := ℂ)
          (n := (⊤ : WithTop ℕ∞))).congr_mono ?_ ?_
      · intro x hx
        simp [Function.comp_def, riemannSphereInfinityChart] at hx ⊢
        have hx0 : x ≠ 0 := by
          intro h
          subst x
          simp at hx
        simp [riemannSphereInv_coe_of_ne_zero hx0]
      · intro x hx
        simp [riemannSphereInfinityChart] at hx ⊢
        intro h
        subst x
        simp at hx
    · refine
        (contDiffOn_inv (𝕜 := ℂ) (𝕜' := ℂ)
          (n := (⊤ : WithTop ℕ∞))).congr_mono ?_ ?_
      · intro x hx
        simp [Function.comp_def, riemannSphereInfinityChart] at hx ⊢
        change ¬riemannSphereInv (x : RiemannSphere) = OnePoint.infty at hx
        change riemannSphereFiniteChart (riemannSphereInv (x : RiemannSphere)) = x⁻¹
        have hx0 : x ≠ 0 := by
          intro h
          subst x
          simp at hx
        simp [riemannSphereInv_coe_of_ne_zero hx0]
      · intro x hx
        simp [riemannSphereInfinityChart] at hx ⊢
        change ¬riemannSphereInv (x : RiemannSphere) = OnePoint.infty at hx
        intro h
        subst x
        simp at hx
    · refine
        (contDiff_id : ContDiff ℂ ⊤ (id : ℂ → ℂ)).contDiffOn.congr_mono ?_
          (subset_univ _)
      intro x _hx
      simp [Function.comp_def]

/-- The Riemann sphere is connected, hence is a Riemann surface. -/
noncomputable instance instRiemannSurfaceRiemannSphere :
    RiemannSurface RiemannSphere where
  toComplexOneManifold := inferInstance
  toConnectedSpace := inferInstance

/--
%%handwave
name:
  Holomorphic affine inclusion into the Riemann sphere
statement:
  The canonical inclusion \(\mathbb C\hookrightarrow\widehat{\mathbb C}\) is
  holomorphic for the affine and reciprocal charts on the Riemann sphere.
proof:
  It is the inverse of the affine chart, whose target is all of \(\mathbb C\).
-/
theorem riemannSphereCoe_mdifferentiable :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((↑) : ℂ → RiemannSphere) := by
  intro z
  have hmem : riemannSphereFiniteChart ∈ atlas ℂ RiemannSphere := by
    change riemannSphereFiniteChart ∈
      ({riemannSphereFiniteChart, riemannSphereInfinityChart} :
        Set (OpenPartialHomeomorph RiemannSphere ℂ))
    simp
  exact (mdifferentiableOn_atlas_symm (I := 𝓘(ℂ)) hmem z (by simp)).mdifferentiableAt
    (by simp)

/-- Translation of the affine coordinate, fixing infinity, is holomorphic on
the Riemann sphere. -/
theorem riemannSphereTranslation_mdifferentiable (a : ℂ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (riemannSphereTranslation a) := by
  intro z
  induction z using OnePoint.rec with
  | infty =>
      rw [mdifferentiableAt_iff_of_mem_source
        (mem_chart_source ℂ OnePoint.infty)
        (mem_chart_source ℂ (riemannSphereTranslation a OnePoint.infty))]
      constructor
      · exact (riemannSphereTranslation_continuous a).continuousAt
      · simp [extChartAt, Function.comp_def]
        rw [differentiableWithinAt_univ]
        have hdiff : DifferentiableAt ℂ (fun x : ℂ ↦ x / (1 + a * x)) 0 := by
          have hnum : DifferentiableAt ℂ (fun x : ℂ ↦ x) 0 := differentiableAt_id
          have hden' : DifferentiableAt ℂ (fun x : ℂ ↦ 1 + a * x) 0 := by
            fun_prop
          exact hnum.div hden' (by simp)
        refine hdiff.congr_of_eventuallyEq ?_
        have hden : ∀ᶠ x : ℂ in 𝓝 0, 1 + a * x ≠ 0 := by
          apply ContinuousAt.eventually_ne
          · fun_prop
          · simp
        filter_upwards [hden] with x hxden
        by_cases hx0 : x = 0
        · subst x
          simp
        · have hsum : x⁻¹ + a ≠ 0 := by
            intro h
            apply hxden
            calc
              1 + a * x = (x⁻¹ + a) * x := by field_simp [hx0]
              _ = 0 := by rw [h]; simp
          simp [riemannSphereInv_coe_of_ne_zero hx0, hsum]
          field_simp [hx0, hxden, hsum]
  | coe z =>
      rw [mdifferentiableAt_iff_of_mem_source
        (mem_chart_source ℂ (z : RiemannSphere))
        (mem_chart_source ℂ (riemannSphereTranslation a (z : RiemannSphere)))]
      constructor
      · exact (riemannSphereTranslation_continuous a).continuousAt
      · simp [extChartAt, Function.comp_def]
        exact differentiableAt_id.differentiableWithinAt

/-- A nonzero affine dilation, fixing infinity, is holomorphic on the Riemann
sphere. -/
theorem riemannSphereDilation_mdifferentiable {a : ℂ} (ha : a ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (riemannSphereDilation a) := by
  intro z
  induction z using OnePoint.rec with
  | infty =>
      rw [mdifferentiableAt_iff_of_mem_source
        (mem_chart_source ℂ OnePoint.infty)
        (mem_chart_source ℂ (riemannSphereDilation a OnePoint.infty))]
      constructor
      · exact (riemannSphereDilation_continuous ha).continuousAt
      · simp [extChartAt, Function.comp_def]
        have heq :
            (fun x : ℂ ↦ riemannSphereInfinityChart
              (riemannSphereDilation a (riemannSphereInv (x : RiemannSphere)))) =
              fun x : ℂ ↦ x / a := by
          funext x
          by_cases hx : x = 0
          · subst x
            simp
          · simp [riemannSphereInv_coe_of_ne_zero hx,
              mul_ne_zero ha (inv_ne_zero hx)]
            field_simp [ha, hx]
        rw [heq]
        fun_prop
  | coe z =>
      rw [mdifferentiableAt_iff_of_mem_source
        (mem_chart_source ℂ (z : RiemannSphere))
        (mem_chart_source ℂ (riemannSphereDilation a (z : RiemannSphere)))]
      constructor
      · exact (riemannSphereDilation_continuous ha).continuousAt
      · simp [extChartAt, Function.comp_def]
        fun_prop

/-- Inversion is holomorphic for the standard complex structure on the
Riemann sphere. -/
theorem riemannSphereInv_mdifferentiable :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) riemannSphereInv := by
  intro z
  induction z using OnePoint.rec with
  | infty =>
      rw [mdifferentiableAt_iff_of_mem_source
        (mem_chart_source ℂ OnePoint.infty)
        (mem_chart_source ℂ (riemannSphereInv OnePoint.infty))]
      constructor
      · exact riemannSphereInv_continuous.continuousAt
      · simp [extChartAt, Function.comp_def]
        exact differentiableAt_id.differentiableWithinAt
  | coe z =>
      by_cases hz : z = 0
      · subst z
        rw [mdifferentiableAt_iff_of_mem_source
          (mem_chart_source ℂ ((0 : ℂ) : RiemannSphere))
          (mem_chart_source ℂ (riemannSphereInv ((0 : ℂ) : RiemannSphere)))]
        constructor
        · exact riemannSphereInv_continuous.continuousAt
        · simp [extChartAt, Function.comp_def]
          exact differentiableAt_id.differentiableWithinAt
      · rw [mdifferentiableAt_iff_of_mem_source
          (mem_chart_source ℂ (z : RiemannSphere))
          (mem_chart_source ℂ (riemannSphereInv (z : RiemannSphere)))]
        constructor
        · exact riemannSphereInv_continuous.continuousAt
        · simp [extChartAt, Function.comp_def, hz]
          rw [differentiableWithinAt_univ]
          refine (differentiableAt_inv hz).congr_of_eventuallyEq ?_
          filter_upwards [eventually_ne_nhds hz] with x hx
          simp [riemannSphereInv_coe_of_ne_zero hx]

/-- Every complex Möbius representative acts holomorphically on the standard
Riemann sphere. -/
theorem mobiusRepresentative_smul_mdifferentiable (A : MobiusRepresentative) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : RiemannSphere ↦ A • z) := by
  by_cases hc : A 1 0 = 0
  · have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 ≠ 0 := by
      simpa [Matrix.det_fin_two] using A.det_ne_zero
    have ha : A 0 0 ≠ 0 := by
      intro h
      exact hdet (by simp [h, hc])
    have hd : A 1 1 ≠ 0 := by
      intro h
      exact hdet (by simp [h, hc])
    let F : RiemannSphere → RiemannSphere :=
      riemannSphereTranslation (A 0 1 / A 1 1) ∘
        riemannSphereDilation (A 0 0 / A 1 1)
    have hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
      exact (riemannSphereTranslation_mdifferentiable (A 0 1 / A 1 1)).comp
        (riemannSphereDilation_mdifferentiable (div_ne_zero ha hd))
    have hEq : (fun z : RiemannSphere ↦ A • z) = F := by
      funext z
      induction z using OnePoint.rec with
      | infty => simp [F, OnePoint.smul_infty_eq_ite, hc]
      | coe z =>
          rw [OnePoint.smul_some_eq_ite]
          simp [F, hc, hd]
          field_simp [hd]
    rw [hEq]
    exact hF
  · let Δ : ℂ := A 0 0 * A 1 1 - A 0 1 * A 1 0
    have hdet : Δ ≠ 0 := by
      simpa [Δ, Matrix.det_fin_two] using A.det_ne_zero
    have hk : -Δ / (A 1 0) ^ 2 ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr hdet) (pow_ne_zero 2 hc)
    let F : RiemannSphere → RiemannSphere :=
      riemannSphereTranslation (A 0 0 / A 1 0) ∘
        riemannSphereDilation (-Δ / (A 1 0) ^ 2) ∘
          riemannSphereInv ∘
            riemannSphereTranslation (A 1 1 / A 1 0)
    have hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
      exact (riemannSphereTranslation_mdifferentiable (A 0 0 / A 1 0)).comp
        ((riemannSphereDilation_mdifferentiable hk).comp
          (riemannSphereInv_mdifferentiable.comp
            (riemannSphereTranslation_mdifferentiable (A 1 1 / A 1 0))))
    have hEq : (fun z : RiemannSphere ↦ A • z) = F := by
      funext z
      induction z using OnePoint.rec with
      | infty => simp [F, OnePoint.smul_infty_eq_ite, hc]
      | coe z =>
          rw [OnePoint.smul_some_eq_ite]
          by_cases hden : A 1 0 * z + A 1 1 = 0
          · have htrans0 : z + A 1 1 / A 1 0 = 0 := by
              apply mul_left_cancel₀ hc
              field_simp [hc]
              simpa [mul_add, add_comm, add_left_comm, add_assoc] using hden
            simp [F, hden, htrans0]
          · have htrans_ne : z + A 1 1 / A 1 0 ≠ 0 := by
              intro hz
              apply hden
              calc
                A 1 0 * z + A 1 1 = A 1 0 * (z + A 1 1 / A 1 0) := by
                  field_simp [hc]
                _ = 0 := by simp [hz]
            simp [F, hden, htrans_ne]
            have hden' : z * A 1 0 + A 1 1 ≠ 0 := by
              simpa [mul_comm] using hden
            field_simp [hc, hden, hden', htrans_ne, Δ]
            ring
    rw [hEq]
    exact hF

/-- A Möbius representative acts by a homeomorphism of the Riemann sphere. -/
def mobiusRepresentativeHomeomorph (A : MobiusRepresentative) :
    RiemannSphere ≃ₜ RiemannSphere where
  toFun z := A • z
  invFun z := A⁻¹ • z
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := mobiusRepresentative_smul_continuous A
  continuous_invFun := mobiusRepresentative_smul_continuous A⁻¹

@[simp]
theorem mobiusRepresentativeHomeomorph_apply
    (A : MobiusRepresentative) (z : RiemannSphere) :
    mobiusRepresentativeHomeomorph A z = A • z :=
  rfl

@[simp]
theorem mobiusRepresentativeHomeomorph_symm_apply
    (A : MobiusRepresentative) (z : RiemannSphere) :
    (mobiusRepresentativeHomeomorph A).symm z = A⁻¹ • z :=
  rfl

/-- Möbius representatives act by holomorphic local diffeomorphisms of the
standard sphere. -/
theorem mobiusRepresentative_openPartialHomeomorph_mdifferentiable
    (A : MobiusRepresentative) :
    (mobiusRepresentativeHomeomorph A).toOpenPartialHomeomorph.MDifferentiable
      𝓘(ℂ) 𝓘(ℂ) := by
  constructor
  · simpa using (mobiusRepresentative_smul_mdifferentiable A).mdifferentiableOn
  · simpa using (mobiusRepresentative_smul_mdifferentiable A⁻¹).mdifferentiableOn

end

end JJMath
