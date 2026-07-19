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

/--
%%handwave
name:
  Inversion on the Riemann sphere is involutive
statement:
  For every \(z\in\widehat{\mathbb C}\), applying spherical inversion twice gives
  \(\iota(\iota(z))=z\).
proof:
  Separate infinity from finite points.  At a finite point, split off \(z=0\);
  otherwise the conclusion is the identity \((z^{-1})^{-1}=z\).
-/
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

/--
%%handwave
name:
  Double spherical inversion
statement:
  For every \(z\in\widehat{\mathbb C}\), one has \(\iota(\iota(z))=z\).
proof:
  This is the pointwise form of [spherical inversion is involutive](lean:JJMath.riemannSphereInv_involutive).
-/
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

/--
%%handwave
name:
  The inversion homeomorphism acts by inversion
statement:
  For \(z\in\widehat{\mathbb C}\), the self-homeomorphism defined by spherical
  inversion sends \(z\) to \(\iota(z)\).
proof:
  This is the defining formula for the homeomorphism.
-/
@[simp]
theorem riemannSphereInvHomeomorph_apply (z : RiemannSphere) :
    riemannSphereInvHomeomorph z = riemannSphereInv z :=
  rfl

/-- The affine coordinate on the finite part of the Riemann sphere. -/
def riemannSphereFiniteChart : OpenPartialHomeomorph RiemannSphere ℂ :=
  (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph
    ((↑) : ℂ → RiemannSphere)).symm

/--
%%handwave
name:
  Domain of the affine chart
statement:
  The source of the affine chart on \(\widehat{\mathbb C}\) is exactly
  \(\widehat{\mathbb C}\setminus\{\infty\}\).
proof:
  The affine chart is the inverse of the open embedding
  \(\mathbb C\hookrightarrow\widehat{\mathbb C}\), whose image is the complement of infinity.
-/
@[simp]
theorem riemannSphereFiniteChart_source :
    riemannSphereFiniteChart.source = ({OnePoint.infty} : Set RiemannSphere)ᶜ := by
  simp [riemannSphereFiniteChart, OnePoint.compl_infty]

/--
%%handwave
name:
  Range of the affine chart
statement:
  The affine chart maps onto all of \(\mathbb C\).
proof:
  It is the inverse partial homeomorphism of the inclusion
  \(\mathbb C\hookrightarrow\widehat{\mathbb C}\).
-/
@[simp]
theorem riemannSphereFiniteChart_target :
    riemannSphereFiniteChart.target = Set.univ := by
  simp [riemannSphereFiniteChart]

/--
%%handwave
name:
  Affine coordinate of a finite point
statement:
  For every \(z\in\mathbb C\), the affine chart sends the corresponding finite
  point of \(\widehat{\mathbb C}\) to \(z\).
proof:
  Apply the left-inverse identity for the open embedding of the finite plane.
-/
@[simp]
theorem riemannSphereFiniteChart_coe (z : ℂ) :
    riemannSphereFiniteChart (z : RiemannSphere) = z := by
  simpa [riemannSphereFiniteChart] using
    (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
      ((↑) : ℂ → RiemannSphere) OnePoint.isOpenEmbedding_coe (x := z))

/--
%%handwave
name:
  Inverse affine chart
statement:
  For every \(z\in\mathbb C\), the inverse affine chart sends \(z\) to its
  canonical finite point in \(\widehat{\mathbb C}\).
proof:
  This is the defining inverse map of the affine chart.
-/
@[simp]
theorem riemannSphereFiniteChart_symm_apply (z : ℂ) :
    riemannSphereFiniteChart.symm z = (z : RiemannSphere) :=
  rfl

/-- The reciprocal coordinate near infinity. -/
def riemannSphereInfinityChart : OpenPartialHomeomorph RiemannSphere ℂ :=
  riemannSphereInvHomeomorph.toOpenPartialHomeomorph.trans riemannSphereFiniteChart

/--
%%handwave
name:
  Domain of the reciprocal chart
statement:
  The source of the reciprocal chart is
  \(\widehat{\mathbb C}\setminus\{0\}\).
proof:
  Check infinity and finite points separately; for a finite point, inversion
  lands in the affine chart exactly when the point is nonzero.
-/
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

/--
%%handwave
name:
  Range of the reciprocal chart
statement:
  The reciprocal chart maps onto all of \(\mathbb C\).
proof:
  Spherical inversion is a homeomorphism and the affine chart has full target.
-/
@[simp]
theorem riemannSphereInfinityChart_target :
    riemannSphereInfinityChart.target = Set.univ := by
  simp [riemannSphereInfinityChart]

/--
%%handwave
name:
  Inverse reciprocal chart
statement:
  For every \(z\in\mathbb C\), the inverse reciprocal chart sends \(z\) to the
  spherical inverse of its finite point.
proof:
  This is the inverse formula for the composite of spherical inversion with
  the affine chart.
-/
@[simp]
theorem riemannSphereInfinityChart_symm_apply (z : ℂ) :
    riemannSphereInfinityChart.symm z = riemannSphereInv (z : RiemannSphere) :=
  rfl

/--
%%handwave
name:
  Reciprocal coordinate of infinity
statement:
  The reciprocal chart sends \(\infty\in\widehat{\mathbb C}\) to \(0\in\mathbb C\).
proof:
  Spherical inversion sends infinity to zero, after which the affine chart is the identity.
-/
@[simp]
theorem riemannSphereInfinityChart_infty :
    riemannSphereInfinityChart OnePoint.infty = 0 := by
  simp [riemannSphereInfinityChart]

/--
%%handwave
name:
  Reciprocal coordinate of a nonzero finite point
statement:
  If \(z\in\mathbb C\setminus\{0\}\), then the reciprocal chart of the
  corresponding point of \(\widehat{\mathbb C}\) is \(z^{-1}\).
proof:
  Substitute the finite-point formula for spherical inversion into the affine chart.
-/
@[simp]
theorem riemannSphereInfinityChart_coe_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    riemannSphereInfinityChart (z : RiemannSphere) = z⁻¹ := by
  simp [riemannSphereInfinityChart, riemannSphereInv_coe_of_ne_zero hz]

/--
%%handwave
name:
  Reciprocal chart after spherical inversion
statement:
  For every \(z\in\mathbb C\), the reciprocal chart of the spherical inverse
  of the finite point \(z\) equals \(z\).
proof:
  If \(z=0\), simplify directly; otherwise use the reciprocal formulas and
  \((z^{-1})^{-1}=z\).
-/
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

/--
%%handwave
name:
  The chart at infinity is the reciprocal chart
statement:
  In the standard two-chart atlas on \(\widehat{\mathbb C}\), the chart selected
  at infinity is the reciprocal chart.
proof:
  Evaluate the defining case distinction for the chosen chart at infinity.
-/
@[simp]
theorem chartAt_riemannSphere_infty :
    chartAt ℂ (OnePoint.infty : RiemannSphere) = riemannSphereInfinityChart := by
  rw [show chartAt ℂ (OnePoint.infty : RiemannSphere) =
    if (OnePoint.infty : RiemannSphere) = OnePoint.infty then
      riemannSphereInfinityChart else riemannSphereFiniteChart from rfl]
  simp

/--
%%handwave
name:
  The chart at a finite point is the affine chart
statement:
  For every \(z\in\mathbb C\), the chart selected at the corresponding finite
  point of \(\widehat{\mathbb C}\) is the affine chart.
proof:
  A finite point is not infinity, so the defining case distinction selects the affine chart.
-/
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

/--
%%handwave
name:
  Affine translations are holomorphic on the Riemann sphere
statement:
  For each \(a\in\mathbb C\), the map \(z\mapsto z+a\) on finite points,
  extended by \(\infty\mapsto\infty\), is holomorphic on \(\widehat{\mathbb C}\).
proof:
  At finite points the affine-coordinate expression is a translation.  At
  infinity the reciprocal-coordinate expression is \(w\mapsto w/(1+aw)\),
  which is holomorphic near \(w=0\).
-/
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

/--
%%handwave
name:
  Nonzero dilations are holomorphic on the Riemann sphere
statement:
  If \(a\in\mathbb C^\times\), the map \(z\mapsto az\) on finite points,
  extended by \(\infty\mapsto\infty\), is holomorphic on \(\widehat{\mathbb C}\).
proof:
  In the affine chart the map is \(z\mapsto az\), while in the reciprocal chart
  at infinity it is \(w\mapsto w/a\); both expressions are holomorphic.
-/
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

/--
%%handwave
name:
  Spherical inversion is holomorphic
statement:
  The involution exchanging (0) and \(\infty\) and sending each
  \(z\in\mathbb C^\times\) to \(z^{-1}\) is holomorphic on
  \(\widehat{\mathbb C}\).
proof:
  At (0) and \(\infty\), use one affine and one reciprocal chart, where the
  coordinate expression is the identity.  Away from these points it is
  \(z\mapsto z^{-1}\).
-/
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

/--
%%handwave
name:
  Möbius transformations are holomorphic on the Riemann sphere
statement:
  Every matrix \(A\in\operatorname{GL}_2(\mathbb C)\) acts holomorphically on
  \(\widehat{\mathbb C}\) by its fractional-linear transformation.
proof:
  If the lower-left entry vanishes, factor the action into a nonzero dilation
  and a translation.  Otherwise factor it into two translations, inversion,
  and a nonzero dilation; the preceding holomorphicity results are stable under composition.
-/
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

/--
%%handwave
name:
  Evaluation of the Möbius homeomorphism
statement:
  For \(A\in\operatorname{GL}_2(\mathbb C)\) and
  \(z\in\widehat{\mathbb C}\), the homeomorphism associated with \(A\) sends
  \(z\) to the fractional-linear action \(A\cdot z\).
proof:
  This is the defining forward map of the homeomorphism.
-/
@[simp]
theorem mobiusRepresentativeHomeomorph_apply
    (A : MobiusRepresentative) (z : RiemannSphere) :
    mobiusRepresentativeHomeomorph A z = A • z :=
  rfl

/--
%%handwave
name:
  Evaluation of the inverse Möbius homeomorphism
statement:
  For \(A\in\operatorname{GL}_2(\mathbb C)\) and
  \(z\in\widehat{\mathbb C}\), the inverse homeomorphism sends \(z\) to
  \(A^{-1}\cdot z\).
proof:
  This is the defining inverse map of the Möbius homeomorphism.
-/
@[simp]
theorem mobiusRepresentativeHomeomorph_symm_apply
    (A : MobiusRepresentative) (z : RiemannSphere) :
    (mobiusRepresentativeHomeomorph A).symm z = A⁻¹ • z :=
  rfl

/--
%%handwave
name:
  Möbius transformations are holomorphic local diffeomorphisms
statement:
  For every \(A\in\operatorname{GL}_2(\mathbb C)\), both the Möbius
  homeomorphism of \(\widehat{\mathbb C}\) induced by \(A\) and its inverse are
  holomorphic on their full domains.
proof:
  Apply [Möbius transformations are holomorphic on the Riemann sphere](lean:JJMath.mobiusRepresentative_smul_mdifferentiable) to \(A\) and \(A^{-1}\).
-/
theorem mobiusRepresentative_openPartialHomeomorph_mdifferentiable
    (A : MobiusRepresentative) :
    (mobiusRepresentativeHomeomorph A).toOpenPartialHomeomorph.MDifferentiable
      𝓘(ℂ) 𝓘(ℂ) := by
  constructor
  · simpa using (mobiusRepresentative_smul_mdifferentiable A).mdifferentiableOn
  · simpa using (mobiusRepresentative_smul_mdifferentiable A⁻¹).mdifferentiableOn

end

end JJMath
