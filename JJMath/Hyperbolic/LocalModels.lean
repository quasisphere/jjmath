import JJMath.Hyperbolic.DevelopingMap
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Local upper-half-plane models for hyperbolic metrics

This file records the intermediate geometric data behind the developing-map
theorem for hyperbolic metrics.  The intended mathematical route is:

1. a curvature `-1` conformal metric has local isometries to `ℍ`;
2. overlaps differ by real Mobius transformations;
3. analytic continuation on the universal cover produces a developing map and
   holonomy.

The analytic assertions are packaged as explicit theorem inputs, with data
organized so later files can supply concrete PDE, local-isometry, and monodromy
proofs.
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold MatrixGroups

noncomputable section

/--
Concrete local-isometry certificate for a local upper-half-plane coordinate.

The surface map is represented in an explicit complex coordinate by a map
`localMap : coordinateDomain → ℍ`.  The old theorem-style projections below
recover holomorphicity, local-biholomorphism, and the Poincare pullback formula
from this concrete coordinate package.
-/
structure HyperbolicLocalChartLocalIsometryData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) (domain : Set X) (toUpperHalfPlane : X → ℍ) where
  /-- The coordinate domain in `ℂ`. -/
  coordinateDomain : Set ℂ
  /-- The coordinate domain is open. -/
  isOpen_coordinateDomain : IsOpen coordinateDomain
  /-- The local complex coordinate on the surface domain. -/
  coordinate : X → ℂ
  /-- The chart in which the coordinate formula is written. -/
  chart : OpenPartialHomeomorph X ℂ
  /-- The chosen chart belongs to the complex atlas. -/
  chart_mem_atlas : chart ∈ atlas ℂ X
  /-- The surface domain lies in the source of the chosen chart. -/
  domain_subset_chart_source : domain ⊆ chart.source
  /-- The stored coordinate agrees with the chosen chart on the surface domain. -/
  coordinate_eq_chart : Set.EqOn coordinate chart domain
  /-- Points in the surface domain lie in the coordinate domain. -/
  coordinate_mem_domain : ∀ x, x ∈ domain → coordinate x ∈ coordinateDomain
  /-- The upper-half-plane-valued coordinate expression. -/
  localMap : ℂ → ℍ
  /-- The surface map agrees with the coordinate expression on the domain. -/
  toUpperHalfPlane_eq :
    ∀ x, x ∈ domain → toUpperHalfPlane x = localMap (coordinate x)
  /-- The coordinate expression is holomorphic on its coordinate domain. -/
  holomorphic_on_domain :
    ∀ z, z ∈ coordinateDomain →
      DifferentiableAt ℂ (fun w : ℂ ↦ (localMap w : ℂ)) z
  /-- The coordinate expression has nonzero derivative on the surface domain. -/
  local_biholomorph_on_domain :
    ∀ x, x ∈ domain →
      deriv (fun z : ℂ ↦ (localMap z : ℂ)) (coordinate x) ≠ 0
  /-- The local map pulls back the Poincare metric to `g` on its domain. -/
  pulls_back_metric_on_domain :
    ∀ x, x ∈ domain →
      g.toConformalMetric.densitySqInChart chart chart_mem_atlas (coordinate x) =
        Complex.normSq (deriv (fun z : ℂ ↦ (localMap z : ℂ)) (coordinate x)) /
          ((toUpperHalfPlane x : ℂ).im ^ 2)

/--
A local upper-half-plane coordinate for a hyperbolic metric.

The intended meaning is that `toUpperHalfPlane` is holomorphic and locally
isometric on `domain`, so that it pulls the Poincare metric back to `g`.
-/
structure HyperbolicLocalChart (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) where
  /-- The open set on which the local model is defined. -/
  domain : Set X
  /-- The local model domain is open. -/
  isOpen_domain : IsOpen domain
  /-- The local map to the upper half-plane. -/
  toUpperHalfPlane : X → ℍ
  /-- Holomorphicity, local-biholomorphism, and metric-pullback data. -/
  local_isometry :
    HyperbolicLocalChartLocalIsometryData X g domain toUpperHalfPlane

namespace HyperbolicLocalChart

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/-- The local map is holomorphic on its domain. -/
def holomorphic_on_domain (U : HyperbolicLocalChart X g) : Prop :=
  ∀ z, z ∈ U.local_isometry.coordinateDomain →
    DifferentiableAt ℂ (fun w : ℂ ↦ (U.local_isometry.localMap w : ℂ)) z

/-- The local map is a local diffeomorphism/local biholomorphism on its domain. -/
def local_biholomorph_on_domain (U : HyperbolicLocalChart X g) : Prop :=
  ∀ x, x ∈ U.domain →
    deriv (fun z : ℂ ↦ (U.local_isometry.localMap z : ℂ))
      (U.local_isometry.coordinate x) ≠ 0

/-- The local map pulls back the Poincare metric to `g` on its domain. -/
def pulls_back_metric_on_domain (U : HyperbolicLocalChart X g) : Prop :=
  ∀ x, x ∈ U.domain →
    g.toConformalMetric.densitySqInChart U.local_isometry.chart
        U.local_isometry.chart_mem_atlas (U.local_isometry.coordinate x) =
      Complex.normSq
          (deriv (fun z : ℂ ↦ (U.local_isometry.localMap z : ℂ))
            (U.local_isometry.coordinate x)) /
        ((U.toUpperHalfPlane x : ℂ).im ^ 2)

/-- The coordinate expression for a local hyperbolic chart. -/
def coordinateLocalMap (U : HyperbolicLocalChart X g) : ℂ → ℍ :=
  U.local_isometry.localMap

/-- The local chart agrees with its stored coordinate expression on the domain. -/
theorem toUpperHalfPlane_eq_coordinateLocalMap
    (U : HyperbolicLocalChart X g) {x : X} (hx : x ∈ U.domain) :
    U.toUpperHalfPlane x =
      U.coordinateLocalMap (U.local_isometry.coordinate x) :=
  U.local_isometry.toUpperHalfPlane_eq x hx

/-- The stored coordinate expression of a local hyperbolic chart is continuous. -/
theorem coordinateLocalMap_continuousAt
    (U : HyperbolicLocalChart X g) {z : ℂ}
    (hz : z ∈ U.local_isometry.coordinateDomain) :
    ContinuousAt U.coordinateLocalMap z := by
  rw [UpperHalfPlane.isOpenEmbedding_coe.isInducing.continuousAt_iff]
  exact (U.local_isometry.holomorphic_on_domain z hz).continuousAt

/-- The chosen coordinate of a local hyperbolic chart is continuous along the chart domain. -/
theorem coordinate_continuousWithinAt
    (U : HyperbolicLocalChart X g) {x : X} (hx : x ∈ U.domain) :
    ContinuousWithinAt U.local_isometry.coordinate U.domain x := by
  have hxchart : x ∈ U.local_isometry.chart.source :=
    U.local_isometry.domain_subset_chart_source hx
  have hchart :
      ContinuousWithinAt U.local_isometry.chart U.domain x :=
    (U.local_isometry.chart.continuousAt hxchart).continuousWithinAt
  exact hchart.congr
    (fun y hy => U.local_isometry.coordinate_eq_chart hy)
    (U.local_isometry.coordinate_eq_chart hx)

/-- A local hyperbolic chart is continuous along its domain. -/
theorem toUpperHalfPlane_continuousWithinAt
    (U : HyperbolicLocalChart X g) {x : X} (hx : x ∈ U.domain) :
    ContinuousWithinAt U.toUpperHalfPlane U.domain x := by
  have hcoord :=
    U.coordinate_continuousWithinAt hx
  have hlocal :
      ContinuousAt U.coordinateLocalMap (U.local_isometry.coordinate x) :=
    U.coordinateLocalMap_continuousAt (U.local_isometry.coordinate_mem_domain x hx)
  have hcomp :
      ContinuousWithinAt
        (fun y : X => U.coordinateLocalMap (U.local_isometry.coordinate y))
        U.domain x :=
    hlocal.comp_continuousWithinAt hcoord
  exact hcomp.congr
    (fun y hy => U.toUpperHalfPlane_eq_coordinateLocalMap hy)
    (U.toUpperHalfPlane_eq_coordinateLocalMap hx)

/-- A local hyperbolic chart is continuous at points of its open domain. -/
theorem toUpperHalfPlane_continuousAt
    (U : HyperbolicLocalChart X g) {x : X} (hx : x ∈ U.domain) :
    ContinuousAt U.toUpperHalfPlane x :=
  (U.toUpperHalfPlane_continuousWithinAt hx).continuousAt
    (U.isOpen_domain.mem_nhds hx)

/-- Real-Mobius postcomposition preserves continuity of a local hyperbolic chart. -/
theorem realMobius_postcomp_continuousAt
    (U : HyperbolicLocalChart X g) (A : RealMobiusRepresentative)
    {x : X} (hx : x ∈ U.domain) :
    ContinuousAt (fun x : X =>
      realMobiusRepresentativeAction A (U.toUpperHalfPlane x)) x :=
  (realMobiusRepresentativeAction_continuous A).continuousAt.comp
    (U.toUpperHalfPlane_continuousAt hx)

/-- A local hyperbolic chart is holomorphic in the ambient `chartAt` coordinate. -/
theorem coordinateExpressionAt_differentiableAt
    [ComplexOneManifold X] (U : HyperbolicLocalChart X g) {x₀ : X}
    (hx₀ : x₀ ∈ U.domain) :
    DifferentiableAt ℂ
      (fun z : ℂ => (U.toUpperHalfPlane ((chartAt ℂ x₀).symm z) : ℂ))
      ((chartAt ℂ x₀) x₀) := by
  let L := U.local_isometry
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀
  let z₀ : ℂ := e x₀
  let τ : ℂ → ℂ := fun z => L.chart (e.symm z)
  have hz₀_target : z₀ ∈ e.target := by
    dsimp [z₀, e]
    exact mem_chart_target ℂ x₀
  have hsymm_z₀ : e.symm z₀ = x₀ := by
    dsimp [z₀, e]
    exact (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)
  have hx₀_Lsource : x₀ ∈ L.chart.source := L.domain_subset_chart_source hx₀
  have hτ_point : τ z₀ = L.coordinate x₀ := by
    dsimp [τ]
    rw [hsymm_z₀]
    exact (L.coordinate_eq_chart hx₀).symm
  have hdomain :
      ∀ᶠ z in nhds z₀, e.symm z ∈ U.domain :=
    (e.tendsto_symm (mem_chart_source ℂ x₀))
      (U.isOpen_domain.mem_nhds hx₀)
  have hExpr :
      (fun z : ℂ => (U.toUpperHalfPlane (e.symm z) : ℂ)) =ᶠ[nhds z₀]
        (fun z : ℂ => (L.localMap (τ z) : ℂ)) := by
    filter_upwards [hdomain] with z hz
    dsimp [τ]
    rw [L.toUpperHalfPlane_eq (e.symm z) hz]
    rw [L.coordinate_eq_chart hz]
  have hτ_mdiff :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) τ z₀ := by
    have hchart_mdiff :
        MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) L.chart (e.symm z₀) := by
      rw [hsymm_z₀]
      exact mdifferentiableAt_atlas L.chart_mem_atlas hx₀_Lsource
    dsimp [τ]
    exact
      hchart_mdiff.comp z₀
        (mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x₀) hz₀_target)
  have hτ_diff : DifferentiableAt ℂ τ z₀ := hτ_mdiff.differentiableAt
  have hlocal_diff :
      DifferentiableAt ℂ (fun z : ℂ => (L.localMap z : ℂ))
        (L.coordinate x₀) :=
    L.holomorphic_on_domain (L.coordinate x₀)
      (L.coordinate_mem_domain x₀ hx₀)
  have hlocal_diff_at_τ :
      DifferentiableAt ℂ (fun z : ℂ => (L.localMap z : ℂ)) (τ z₀) := by
    simpa [hτ_point] using hlocal_diff
  have hcomp :
      DifferentiableAt ℂ (fun z : ℂ => (L.localMap (τ z) : ℂ)) z₀ := by
    simpa [Function.comp_def] using hlocal_diff_at_τ.comp z₀ hτ_diff
  exact hcomp.congr_of_eventuallyEq hExpr

/-- Real-Mobius postcomposition of a local chart is holomorphic in ambient coordinates. -/
theorem realMobius_postcomp_coordinateExpressionAt_differentiableAt
    [ComplexOneManifold X] (U : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) {x₀ : X} (hx₀ : x₀ ∈ U.domain) :
    DifferentiableAt ℂ
      (fun z : ℂ =>
        (realMobiusRepresentativeAction A
          (U.toUpperHalfPlane ((chartAt ℂ x₀).symm z)) : ℂ))
      ((chartAt ℂ x₀) x₀) := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀
  let z₀ : ℂ := e x₀
  let F : ℂ → ℂ := fun z => (U.toUpperHalfPlane (e.symm z) : ℂ)
  have hsymm_z₀ : e.symm z₀ = x₀ := by
    dsimp [z₀, e]
    exact (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)
  have hF :
      DifferentiableAt ℂ F z₀ := by
    simpa [F, e, z₀] using U.coordinateExpressionAt_differentiableAt hx₀
  have hF_point : F z₀ = (U.toUpperHalfPlane x₀ : ℂ) := by
    dsimp [F]
    rw [hsymm_z₀]
  let M : ℂ → ℂ := fun w =>
    (realMobiusRepresentativeAction A (UpperHalfPlane.ofComplex w) : ℂ)
  have hM :
      DifferentiableAt ℂ M (F z₀) := by
    simpa [M, hF_point] using
      realMobiusRepresentativeAction_differentiableAt A
        (U.toUpperHalfPlane x₀)
  have hcomp : DifferentiableAt ℂ (fun z => M (F z)) z₀ :=
    hM.comp z₀ hF
  simpa [M, F, e, z₀, Function.comp_def] using hcomp

/--
Real-Mobius postcomposition of a local chart is holomorphic in any chosen
source chart coordinate, at points whose inverse image lies in the local chart
domain.
-/
theorem realMobius_postcomp_coordinateExpression_differentiableAt
    [ComplexOneManifold X] (U : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hdomain : e.symm z ∈ U.domain) :
    DifferentiableAt ℂ
      (fun w : ℂ =>
        (realMobiusRepresentativeAction A
          (U.toUpperHalfPlane (e.symm w)) : ℂ))
      z := by
  let L := U.local_isometry
  let τ : ℂ → ℂ := fun w => L.chart (e.symm w)
  let F : ℂ → ℂ := fun w => (U.toUpperHalfPlane (e.symm w) : ℂ)
  let M : ℂ → ℂ := fun w =>
    (realMobiusRepresentativeAction A (UpperHalfPlane.ofComplex w) : ℂ)
  have hx_Lsource : e.symm z ∈ L.chart.source :=
    L.domain_subset_chart_source hdomain
  have hsymm_tendsto :
      Filter.Tendsto e.symm (nhds z) (nhds (e.symm z)) := by
    simpa [e.right_inv hz] using e.tendsto_symm (e.map_target hz)
  have hτ_point : τ z = L.coordinate (e.symm z) := by
    dsimp [τ]
    exact (L.coordinate_eq_chart hdomain).symm
  have hdomain_event :
      ∀ᶠ w in nhds z, e.symm w ∈ U.domain :=
    hsymm_tendsto (U.isOpen_domain.mem_nhds hdomain)
  have hF_event :
      F =ᶠ[nhds z] fun w : ℂ => (L.localMap (τ w) : ℂ) := by
    filter_upwards [hdomain_event] with w hw
    dsimp [F, τ]
    rw [L.toUpperHalfPlane_eq (e.symm w) hw]
    rw [L.coordinate_eq_chart hw]
  have hτ_mdiff :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) τ z := by
    have hchart_mdiff :
        MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) L.chart (e.symm z) :=
      mdifferentiableAt_atlas L.chart_mem_atlas hx_Lsource
    exact hchart_mdiff.comp z (mdifferentiableAt_atlas_symm he hz)
  have hτ_diff : DifferentiableAt ℂ τ z := hτ_mdiff.differentiableAt
  have hlocal_diff :
      DifferentiableAt ℂ (fun w : ℂ => (L.localMap w : ℂ))
        (L.coordinate (e.symm z)) :=
    L.holomorphic_on_domain (L.coordinate (e.symm z))
      (L.coordinate_mem_domain (e.symm z) hdomain)
  have hlocal_diff_at_τ :
      DifferentiableAt ℂ (fun w : ℂ => (L.localMap w : ℂ)) (τ z) := by
    simpa [hτ_point] using hlocal_diff
  have hF : DifferentiableAt ℂ F z := by
    have hcomp :
        DifferentiableAt ℂ (fun w : ℂ => (L.localMap (τ w) : ℂ)) z := by
      simpa [Function.comp_def] using hlocal_diff_at_τ.comp z hτ_diff
    exact hcomp.congr_of_eventuallyEq hF_event
  have hF_point : F z = (U.toUpperHalfPlane (e.symm z) : ℂ) := rfl
  have hM :
      DifferentiableAt ℂ M (F z) := by
    simpa [M, hF_point] using
      realMobiusRepresentativeAction_differentiableAt A
        (U.toUpperHalfPlane (e.symm z))
  have hcomp : DifferentiableAt ℂ (fun w => M (F w)) z :=
    hM.comp z hF
  simpa [M, F, Function.comp_def] using hcomp

/--
Two local hyperbolic charts have real-Mobius transition on their overlap.

For now we use an `SL(2, ℝ)` representative because mathlib has its action on
`ℍ`; quotienting gives the corresponding `PSL(2, ℝ)` transition.
-/
def HasRealMobiusTransition (U V : HyperbolicLocalChart X g) : Prop :=
  ∃ A : RealMobiusRepresentative,
    ∀ x, x ∈ U.domain → x ∈ V.domain →
      V.toUpperHalfPlane x = realMobiusRepresentativeAction A (U.toUpperHalfPlane x)

/--
Local real-Mobius transition data near one point of a hyperbolic local-chart
overlap.

This is the componentwise form needed by analytic continuation and projective
atlas compatibility: the representative is allowed to be chosen after fixing
an overlap point and a neighborhood of that point.
-/
structure LocalRealMobiusTransitionData (U V : HyperbolicLocalChart X g) (x : X) where
  /-- A surface neighborhood on which the representative is valid. -/
  neighborhood : Set X
  /-- The neighborhood is open in the surface topology. -/
  isOpen_neighborhood : IsOpen neighborhood
  /-- The selected overlap point lies in the neighborhood. -/
  mem_neighborhood : x ∈ neighborhood
  /-- The neighborhood lies in the chart-domain overlap. -/
  subset_overlap : neighborhood ⊆ U.domain ∩ V.domain
  /-- A real Mobius representative for the local transition. -/
  representative : RealMobiusRepresentative
  /-- The representative gives the transition on this neighborhood. -/
  transition_eq :
    ∀ y, y ∈ neighborhood →
      V.toUpperHalfPlane y =
        realMobiusRepresentativeAction representative (U.toUpperHalfPlane y)

/--
Two hyperbolic local charts have local real-Mobius transitions if every point
of their overlap has a neighborhood on which the transition is represented by
some real Mobius transformation.
-/
def HasLocalRealMobiusTransition (U V : HyperbolicLocalChart X g) : Prop :=
  ∀ x, x ∈ U.domain ∩ V.domain →
    Nonempty (LocalRealMobiusTransitionData U V x)

/-- A global real-Mobius transition gives local transition data at every point. -/
theorem hasLocalRealMobiusTransition_of_hasRealMobiusTransition
    {U V : HyperbolicLocalChart X g}
    (h : U.HasRealMobiusTransition V) :
    U.HasLocalRealMobiusTransition V := by
  intro x hx
  rcases h with ⟨A, hA⟩
  exact ⟨
    { neighborhood := U.domain ∩ V.domain
      isOpen_neighborhood := U.isOpen_domain.inter V.isOpen_domain
      mem_neighborhood := hx
      subset_overlap := fun y hy ↦ hy
      representative := A
      transition_eq := by
        intro y hy
        exact hA y hy.1 hy.2 }⟩

/-- Every local hyperbolic chart has the identity real-Mobius transition to itself. -/
theorem hasRealMobiusTransition_self (U : HyperbolicLocalChart X g) :
    U.HasRealMobiusTransition U := by
  refine ⟨1, ?_⟩
  intro x _hx _hx'
  simp [realMobiusRepresentativeAction_one]

/-- Every local hyperbolic chart has the identity local real-Mobius transition to itself. -/
theorem hasLocalRealMobiusTransition_self (U : HyperbolicLocalChart X g) :
    U.HasLocalRealMobiusTransition U :=
  hasLocalRealMobiusTransition_of_hasRealMobiusTransition
    (hasRealMobiusTransition_self U)

end HyperbolicLocalChart

/--
An atlas of local upper-half-plane models for a hyperbolic metric.

This is the formal home for the local theorem that curvature `-1` conformal
metrics are locally isometric to the Poincare half-plane.
-/
structure HyperbolicLocalModelAtlas (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) where
  /-- A chosen local hyperbolic chart near each point. -/
  chartAt : X → HyperbolicLocalChart X g
  /-- The chosen chart at `x` is defined at `x`. -/
  mem_chartAt_domain : ∀ x, x ∈ (chartAt x).domain
  /-- Any two chosen charts differ by a real Mobius transformation on overlaps. -/
  transition_realMobius :
    ∀ x y, (chartAt x).HasRealMobiusTransition (chartAt y)

namespace HyperbolicLocalModelAtlas

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/-- The local model chart centered at a point. -/
def chartNear (A : HyperbolicLocalModelAtlas X g) (x : X) : HyperbolicLocalChart X g :=
  A.chartAt x

theorem mem_chartNear_domain (A : HyperbolicLocalModelAtlas X g) (x : X) :
    x ∈ (A.chartNear x).domain :=
  A.mem_chartAt_domain x

theorem chartNear_transition_realMobius (A : HyperbolicLocalModelAtlas X g) (x y : X) :
    (A.chartNear x).HasRealMobiusTransition (A.chartNear y) :=
  A.transition_realMobius x y

end HyperbolicLocalModelAtlas

/--
An atlas of local upper-half-plane models whose overlaps are represented
locally by real Mobius transformations.

This is the componentwise analytic-continuation input: the representative may
depend on the connected component or on a smaller neighborhood of an overlap
point, which is the natural boundary for continuation.
-/
structure HyperbolicLocalModelLocalTransitionAtlas
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) where
  /-- A chosen local hyperbolic chart near each point. -/
  chartAt : X → HyperbolicLocalChart X g
  /-- The chosen chart at `x` is defined at `x`. -/
  mem_chartAt_domain : ∀ x, x ∈ (chartAt x).domain
  /-- Any two chosen charts differ locally by real Mobius transformations. -/
  transition_localRealMobius :
    ∀ x y, (chartAt x).HasLocalRealMobiusTransition (chartAt y)

namespace HyperbolicLocalModelLocalTransitionAtlas

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/-- The local model chart centered at a point. -/
def chartNear (A : HyperbolicLocalModelLocalTransitionAtlas X g) (x : X) :
    HyperbolicLocalChart X g :=
  A.chartAt x

theorem mem_chartNear_domain (A : HyperbolicLocalModelLocalTransitionAtlas X g) (x : X) :
    x ∈ (A.chartNear x).domain :=
  A.mem_chartAt_domain x

theorem chartNear_transition_localRealMobius
    (A : HyperbolicLocalModelLocalTransitionAtlas X g) (x y : X) :
    (A.chartNear x).HasLocalRealMobiusTransition (A.chartNear y) :=
  A.transition_localRealMobius x y

end HyperbolicLocalModelLocalTransitionAtlas

namespace HyperbolicLocalModelAtlas

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/--
Forget a global overlap representative to the local transition data it
induces at each point of the overlap.
-/
def toLocalTransitionAtlas (A : HyperbolicLocalModelAtlas X g) :
    HyperbolicLocalModelLocalTransitionAtlas X g where
  chartAt := A.chartAt
  mem_chartAt_domain := A.mem_chartAt_domain
  transition_localRealMobius := fun x y ↦
    HyperbolicLocalChart.hasLocalRealMobiusTransition_of_hasRealMobiusTransition
      (A.transition_realMobius x y)

end HyperbolicLocalModelAtlas

/--
Concrete local agreement boundary for a continued developing map and a chosen
local upper-half-plane atlas.

Around every point of the cover, the continued map agrees on a neighborhood
with one local model after postcomposition by a real Mobius representative.
-/
def HyperbolicDevelopingAgreesWithLocalModels
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}
    (localModels : HyperbolicLocalModelAtlas X g)
    (cover : SimplyConnectedCover X x₀) (dev : cover.total → ℍ) : Prop :=
  ∀ y, ∃ U : Set cover.total,
    IsOpen U ∧ y ∈ U ∧
      ∃ (x : X) (A : RealMobiusRepresentative),
        (∀ y', y' ∈ U → cover.projection y' ∈ (localModels.chartAt x).domain) ∧
          ∀ y', y' ∈ U →
            dev y' =
              realMobiusRepresentativeAction A
                ((localModels.chartAt x).toUpperHalfPlane (cover.projection y'))

namespace HyperbolicDevelopingAgreesWithLocalModels

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelAtlas X g}
    {cover : SimplyConnectedCover X x₀} {dev : cover.total → ℍ}

/-- Local agreement with local hyperbolic models forces pointwise continuity of `dev`. -/
theorem continuousAt
    (h : HyperbolicDevelopingAgreesWithLocalModels localModels cover dev)
    (y : cover.total) :
    ContinuousAt dev y := by
  rcases h y with ⟨U, hUopen, hyU, x, A, hdomain, hagree⟩
  let localModelFun : cover.total → ℍ := fun y' =>
    realMobiusRepresentativeAction A
      ((localModels.chartAt x).toUpperHalfPlane (cover.projection y'))
  have hy_domain : cover.projection y ∈ (localModels.chartAt x).domain :=
    hdomain y hyU
  have hpost :
      ContinuousAt
        (fun x' : X =>
          realMobiusRepresentativeAction A
            ((localModels.chartAt x).toUpperHalfPlane x'))
        (cover.projection y) :=
    (localModels.chartAt x).realMobius_postcomp_continuousAt A hy_domain
  have hlocal : ContinuousAt localModelFun y := by
    exact hpost.comp (cover.projection_continuousAt y)
  have heq : dev =ᶠ[nhds y] localModelFun := by
    filter_upwards [hUopen.mem_nhds hyU] with y' hy'
    exact hagree y' hy'
  exact hlocal.congr_of_eventuallyEq heq

/-- Local agreement with local hyperbolic models forces continuity of `dev`. -/
theorem continuous
    (h : HyperbolicDevelopingAgreesWithLocalModels localModels cover dev) :
    Continuous dev := by
  rw [continuous_iff_continuousAt]
  intro y
  exact h.continuousAt y

end HyperbolicDevelopingAgreesWithLocalModels

/--
The analytic-continuation package that turns local hyperbolic charts into a
single-valued developing map on a simply connected cover.
-/
structure HyperbolicDevelopingContinuationData (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] (x₀ : X)
    (g : HyperbolicMetric X) where
  /-- Local upper-half-plane models for the metric. -/
  localModels : HyperbolicLocalModelAtlas X g
  /-- The simply connected cover on which analytic continuation is single-valued. -/
  cover : SimplyConnectedCover X x₀
  /-- The analytically continued developing map. -/
  dev : cover.total → ℍ
  /-- The pullback of `g` to the cover. -/
  coverMetric : ConformalMetric cover.total
  /-- The cover metric is the pullback of the base metric along the projection. -/
  coverMetric_pullback :
    PullsBackMetric cover.projection g.toConformalMetric coverMetric
  /-- The developing map has holomorphic local-biholomorphic regularity on the cover. -/
  dev_regular : HyperbolicDevelopingMapRegularity cover dev
  /-- Lifted real holonomy obtained by monodromy of the local models. -/
  holonomyLift : RealHolonomyLift X x₀
  /-- Pullback identity: `dev^* g_ℍ = projection^* g`. -/
  pullback_metric :
    PullsBackMetric dev upperHalfPlaneConformalMetric coverMetric
  /-- Equivariance with respect to deck transformations and lifted holonomy. -/
  equivariant :
    ∀ γ y, dev (cover.deckAction γ y) = holonomyLift.upperHalfPlaneAction γ (dev y)
  /-- The developing map locally agrees with analytic continuation of the local models. -/
  agrees_with_local_models :
    HyperbolicDevelopingAgreesWithLocalModels localModels cover dev

namespace HyperbolicDevelopingContinuationData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- Continuation data supplies continuity of the continued developing map. -/
theorem dev_continuous (D : HyperbolicDevelopingContinuationData X x₀ g) :
    Continuous D.dev :=
  D.dev_regular.continuous

/-- Continuation data supplies chartwise holomorphicity of the continued developing map. -/
theorem dev_holomorphic (D : HyperbolicDevelopingContinuationData X x₀ g) :
    HyperbolicDevelopingMapHolomorphic D.cover D.dev :=
  D.dev_regular.holomorphic

/-- Forget continuation provenance and keep the lifted developing map. -/
def toLiftedHyperbolicDevelopingMap
    (D : HyperbolicDevelopingContinuationData X x₀ g) :
    LiftedHyperbolicDevelopingMap X x₀ g where
  cover := D.cover
  dev := D.dev
  coverMetric := D.coverMetric
  coverMetric_pullback := D.coverMetric_pullback
  dev_regular := D.dev_regular
  holonomyLift := D.holonomyLift
  pullback_metric := D.pullback_metric
  equivariant := D.equivariant

end HyperbolicDevelopingContinuationData

/--
The analytic-continuation step for a fixed local-model atlas.

This isolates the global monodromy theorem from the local PDE/formula work:
given local maps to `ℍ` with real-Mobius overlaps, analytic continuation on the
simply connected cover produces continuation data.
-/
structure HyperbolicLocalModelContinuationPipeline (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] (x₀ : X)
    (g : HyperbolicMetric X) where
  /-- The local upper-half-plane models to be analytically continued. -/
  localModels : HyperbolicLocalModelAtlas X g
  /-- The resulting continuation data on the simply connected cover. -/
  continuationData : HyperbolicDevelopingContinuationData X x₀ g
  /-- The continuation data is built from this local-model atlas. -/
  continuation_uses_localModels :
    continuationData.localModels = localModels

namespace HyperbolicLocalModelContinuationPipeline

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

/-- Forget the continuation package and keep only the local models. -/
def toHyperbolicLocalModelAtlas
    (P : HyperbolicLocalModelContinuationPipeline X x₀ g) :
    HyperbolicLocalModelAtlas X g :=
  P.localModels

/-- Forget the local provenance and keep the continuation data. -/
def toHyperbolicDevelopingContinuationData
    (P : HyperbolicLocalModelContinuationPipeline X x₀ g) :
    HyperbolicDevelopingContinuationData X x₀ g :=
  P.continuationData

/-- The lifted developing map produced by analytic continuation of local models. -/
def toLiftedHyperbolicDevelopingMap
    (P : HyperbolicLocalModelContinuationPipeline X x₀ g) :
    LiftedHyperbolicDevelopingMap X x₀ g :=
  P.continuationData.toLiftedHyperbolicDevelopingMap

/-- The ordinary `PSL(2, ℝ)` developing map produced by analytic continuation. -/
def toHyperbolicDevelopingMap
    (P : HyperbolicLocalModelContinuationPipeline X x₀ g) :
    HyperbolicDevelopingMap X x₀ g :=
  P.toLiftedHyperbolicDevelopingMap.toHyperbolicDevelopingMap

end HyperbolicLocalModelContinuationPipeline

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/--
Target local theorem: a hyperbolic metric admits an atlas of local isometries to
the upper half-plane.
-/
def HasUpperHalfPlaneLocalModels (g : HyperbolicMetric X) : Prop :=
  Nonempty (HyperbolicLocalModelAtlas X g)

/--
Target local theorem with the natural componentwise overlap condition: a
hyperbolic metric admits local isometries to `ℍ` whose transition maps are
locally real Mobius.
-/
def HasUpperHalfPlaneLocalTransitionModels (g : HyperbolicMetric X) : Prop :=
  Nonempty (HyperbolicLocalModelLocalTransitionAtlas X g)

omit [RiemannSurface X] in
/-- Global real-Mobius overlap data implies the local-transition version. -/
theorem hasUpperHalfPlaneLocalTransitionModels_of_hasUpperHalfPlaneLocalModels
    {g : HyperbolicMetric X}
    (h : g.HasUpperHalfPlaneLocalModels) :
    g.HasUpperHalfPlaneLocalTransitionModels :=
  h.elim fun A ↦ ⟨A.toLocalTransitionAtlas⟩

/--
Target continuation theorem: the local upper-half-plane models analytically
continue on the universal cover and produce lifted holonomy.
-/
def HasDevelopingContinuationData (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (HyperbolicDevelopingContinuationData X x₀ g)

/--
Target analytic-continuation theorem: local upper-half-plane models continue on
the simply connected cover and produce monodromy.
-/
def HasLocalModelContinuationPipeline (x₀ : X) (g : HyperbolicMetric X) : Prop :=
  Nonempty (HyperbolicLocalModelContinuationPipeline X x₀ g)

theorem hasUpperHalfPlaneLocalModels_of_hasLocalModelContinuationPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasLocalModelContinuationPipeline x₀) :
    g.HasUpperHalfPlaneLocalModels :=
  h.elim fun P ↦ ⟨P.toHyperbolicLocalModelAtlas⟩

theorem hasDevelopingContinuationData_of_hasLocalModelContinuationPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasLocalModelContinuationPipeline x₀) :
    g.HasDevelopingContinuationData x₀ :=
  h.elim fun P ↦ ⟨P.toHyperbolicDevelopingContinuationData⟩

theorem admitsLiftedDevelopingMap_of_hasDevelopingContinuationData
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingContinuationData x₀) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  h.elim fun D ↦ ⟨D.toLiftedHyperbolicDevelopingMap⟩

theorem admitsDevelopingMap_of_hasDevelopingContinuationData
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasDevelopingContinuationData x₀) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_admitsLiftedDevelopingMap
    (admitsLiftedDevelopingMap_of_hasDevelopingContinuationData h)

theorem admitsLiftedDevelopingMap_of_hasLocalModelContinuationPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasLocalModelContinuationPipeline x₀) :
    g.AdmitsLiftedDevelopingMap x₀ :=
  admitsLiftedDevelopingMap_of_hasDevelopingContinuationData
    (hasDevelopingContinuationData_of_hasLocalModelContinuationPipeline h)

theorem admitsDevelopingMap_of_hasLocalModelContinuationPipeline
    {x₀ : X} {g : HyperbolicMetric X}
    (h : g.HasLocalModelContinuationPipeline x₀) :
    g.AdmitsDevelopingMap x₀ :=
  admitsDevelopingMap_of_hasDevelopingContinuationData
    (hasDevelopingContinuationData_of_hasLocalModelContinuationPipeline h)

end HyperbolicMetric

end

end JJMath
