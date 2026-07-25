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

/-- The local map is holomorphic on its domain.
%%handwave
name:
  Holomorphicity of a hyperbolic local chart
statement:
  A local chart $U$ is holomorphic on its domain when its complex coordinate expression is differentiable at every point of its coordinate domain.
-/
def holomorphic_on_domain (U : HyperbolicLocalChart X g) : Prop :=
  ∀ z, z ∈ U.local_isometry.coordinateDomain →
    DifferentiableAt ℂ (fun w : ℂ ↦ (U.local_isometry.localMap w : ℂ)) z

/-- The local map is a local diffeomorphism/local biholomorphism on its domain.
%%handwave
name:
  Local biholomorphism property of a hyperbolic chart
statement:
  A local chart $U$ is locally biholomorphic when the derivative of its coordinate expression is nonzero at the coordinate of every point in its surface domain.
-/
def local_biholomorph_on_domain (U : HyperbolicLocalChart X g) : Prop :=
  ∀ x, x ∈ U.domain →
    deriv (fun z : ℂ ↦ (U.local_isometry.localMap z : ℂ))
      (U.local_isometry.coordinate x) ≠ 0

/-- The local map pulls back the Poincare metric to `g` on its domain.
%%handwave
name:
  Metric pullback property of a hyperbolic chart
statement:
  A local map $f$ pulls back the Poincaré metric to $g$ when the squared density of $g$ in the chosen coordinate is $|f'|^2/(\operatorname{Im}f)^2$ throughout the chart domain.
-/
def pulls_back_metric_on_domain (U : HyperbolicLocalChart X g) : Prop :=
  ∀ x, x ∈ U.domain →
    g.toConformalMetric.densitySqInChart U.local_isometry.chart
        U.local_isometry.chart_mem_atlas (U.local_isometry.coordinate x) =
      Complex.normSq
          (deriv (fun z : ℂ ↦ (U.local_isometry.localMap z : ℂ))
            (U.local_isometry.coordinate x)) /
        ((U.toUpperHalfPlane x : ℂ).im ^ 2)

/-- The coordinate expression for a local hyperbolic chart.
%%handwave
name:
  Coordinate map of a hyperbolic local chart
statement:
  The coordinate map of a hyperbolic local chart is its stored holomorphic function from the complex coordinate domain to $\mathbb H$.
-/
def coordinateLocalMap (U : HyperbolicLocalChart X g) : ℂ → ℍ :=
  U.local_isometry.localMap

/-- The local chart agrees with its stored coordinate expression on the domain.

%%handwave
name:
  A local hyperbolic chart agrees with its coordinate formula
statement:
  Let $U$ be a local upper-half-plane chart with surface coordinate $\zeta$
  and coordinate map $F$. For every $x$ in the domain of $U$, its surface map
  satisfies $U(x)=F(\zeta(x))$.
proof:
  This equality is part of the local-isometry data defining $U$.
-/
theorem toUpperHalfPlane_eq_coordinateLocalMap
    (U : HyperbolicLocalChart X g) {x : X} (hx : x ∈ U.domain) :
    U.toUpperHalfPlane x =
      U.coordinateLocalMap (U.local_isometry.coordinate x) :=
  U.local_isometry.toUpperHalfPlane_eq x hx

/-- The stored coordinate expression of a local hyperbolic chart is continuous.

%%handwave
name:
  Continuity of a local upper-half-plane coordinate map
statement:
  If $F:\Omega\to\mathbb H$ is the coordinate expression of a local
  hyperbolic chart and $z\in\Omega$, then $F$ is continuous at $z$.
proof:
  The complex-valued map underlying $F$ is holomorphic at $z$, hence
  continuous. Since the inclusion $\mathbb H\hookrightarrow\mathbb C$ is a
  topological embedding, $F$ itself is continuous at $z$.
-/
theorem coordinateLocalMap_continuousAt
    (U : HyperbolicLocalChart X g) {z : ℂ}
    (hz : z ∈ U.local_isometry.coordinateDomain) :
    ContinuousAt U.coordinateLocalMap z := by
  rw [UpperHalfPlane.isOpenEmbedding_coe.isInducing.continuousAt_iff]
  exact (U.local_isometry.holomorphic_on_domain z hz).continuousAt

/-- The chosen coordinate of a local hyperbolic chart is continuous along the chart domain.

%%handwave
name:
  Continuity of the chosen surface coordinate on its local domain
statement:
  Let $U$ be a local hyperbolic chart with surface domain $D$ and chosen
  coordinate $\zeta:D\to\mathbb C$. At every $x\in D$, the map $\zeta$ is
  continuous at $x$ relative to $D$.
proof:
  On $D$, the chosen coordinate agrees with a complex-manifold chart. That
  chart is continuous on its source, so restricting and replacing it by the
  equal map $\zeta$ gives the claim.
-/
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

/-- A local hyperbolic chart is continuous along its domain.

%%handwave
name:
  Relative continuity of a local map to the upper half-plane
statement:
  If $U:D\to\mathbb H$ is a local hyperbolic chart and $x\in D$, then $U$ is
  continuous at $x$ relative to $D$.
proof:
  On $D$ one has $U=F\circ\zeta$. The coordinate $\zeta$ is relatively
  continuous at $x$, and $F$ is continuous at $\zeta(x)$; continuity of the
  composition and the local agreement give the result.
-/
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

/-- A local hyperbolic chart is continuous at points of its open domain.

%%handwave
name:
  Continuity of a local upper-half-plane map at interior points
statement:
  If $U:D\to\mathbb H$ is a local hyperbolic chart and $x\in D$, then $U$ is
  continuous at $x$ in the ambient surface topology.
proof:
  [The map is continuous at $x$ relative to $D$](lean:JJMath.HyperbolicLocalChart.toUpperHalfPlane_continuousWithinAt), and $D$ is an open neighborhood of $x$.
-/
theorem toUpperHalfPlane_continuousAt
    (U : HyperbolicLocalChart X g) {x : X} (hx : x ∈ U.domain) :
    ContinuousAt U.toUpperHalfPlane x :=
  (U.toUpperHalfPlane_continuousWithinAt hx).continuousAt
    (U.isOpen_domain.mem_nhds hx)

/-- Real-Mobius postcomposition preserves continuity of a local hyperbolic chart.

%%handwave
name:
  Continuity after real Möbius postcomposition
statement:
  Let $U:D\to\mathbb H$ be a local hyperbolic chart and
  $A\in\mathrm{PSL}_2(\mathbb R)$. For every $x\in D$, the map
  $y\mapsto A\cdot U(y)$ is continuous at $x$.
proof:
  [The local map $U$ is continuous at $x$](lean:JJMath.HyperbolicLocalChart.toUpperHalfPlane_continuousAt), and the action of a fixed real Möbius transformation on $\mathbb H$ is continuous; compose the two maps.
-/
theorem realMobius_postcomp_continuousAt
    (U : HyperbolicLocalChart X g) (A : RealMobiusRepresentative)
    {x : X} (hx : x ∈ U.domain) :
    ContinuousAt (fun x : X =>
      realMobiusRepresentativeAction A (U.toUpperHalfPlane x)) x :=
  (realMobiusRepresentativeAction_continuous A).continuousAt.comp
    (U.toUpperHalfPlane_continuousAt hx)

/-- A local hyperbolic chart is holomorphic in the ambient `chartAt` coordinate.

%%handwave
name:
  Holomorphicity of a local hyperbolic chart in centered coordinates
statement:
  Let $X$ be a Riemann surface, $U:D\to\mathbb H$ a local hyperbolic chart,
  and $x_0\in D$. In the complex chart $e$ centered at $x_0$, the map
  $z\mapsto U(e^{-1}(z))$ is complex differentiable at $e(x_0)$.
proof:
  Near $x_0$, write $U=F\circ\zeta$, where $F$ is the stored holomorphic
  coordinate expression. The transition $\zeta\circ e^{-1}$ between the two
  complex-manifold charts is holomorphic, so the chain rule gives
  holomorphicity of $F\circ\zeta\circ e^{-1}$; local agreement identifies this
  composition with $U\circ e^{-1}$.
-/
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

/-- Real-Mobius postcomposition of a local chart is holomorphic in ambient coordinates.

%%handwave
name:
  Holomorphicity in centered coordinates after real Möbius postcomposition
statement:
  Let $U:D\to\mathbb H$ be a local hyperbolic chart, $x_0\in D$, and
  $A\in\mathrm{PSL}_2(\mathbb R)$. If $e$ is the complex chart centered at
  $x_0$, then $z\mapsto A\cdot U(e^{-1}(z))$ is complex differentiable at
  $e(x_0)$.
proof:
  [The coordinate expression $U\circ e^{-1}$ is complex differentiable at $e(x_0)$](lean:JJMath.HyperbolicLocalChart.coordinateExpressionAt_differentiableAt), and the real Möbius action is holomorphic on $\mathbb H$; apply the complex chain rule.
-/
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

%%handwave
name:
  Holomorphicity after real Möbius postcomposition in arbitrary coordinates
statement:
  Let $e$ be any complex chart on $X$, let $z$ lie in its target with
  $e^{-1}(z)$ in the domain of a local hyperbolic chart $U$, and let
  $A\in\mathrm{PSL}_2(\mathbb R)$. Then
  $w\mapsto A\cdot U(e^{-1}(w))$ is complex differentiable at $z$.
proof:
  Express $U$ as its holomorphic coordinate map composed with the transition
  from $e$ to the stored chart. This transition is holomorphic, so their
  composition is holomorphic near $z$; composing once more with the
  holomorphic Möbius action of $A$ proves the claim.
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

%%handwave
name:
  Real Möbius transition between hyperbolic charts
statement:
  Two local hyperbolic charts have a real Möbius transition when there is one $A\in\mathrm{PSL}_2(\mathbb R)$ such that $V(x)=A\cdot U(x)$ at every point of their overlap.
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

%%handwave
name:
  Locally real Möbius transition between hyperbolic charts
statement:
  Two local hyperbolic charts have locally real Möbius transition when every point of their overlap has an open neighborhood on which $V=A\cdot U$ for some $A\in\mathrm{PSL}_2(\mathbb R)$.
-/
def HasLocalRealMobiusTransition (U V : HyperbolicLocalChart X g) : Prop :=
  ∀ x, x ∈ U.domain ∩ V.domain →
    Nonempty (LocalRealMobiusTransitionData U V x)

/-- A global real-Mobius transition gives local transition data at every point.

%%handwave
name:
  A global real Möbius transition restricts to local transitions
statement:
  Suppose two local upper-half-plane charts $U$ and $V$ satisfy
  $V=A\cdot U$ throughout their overlap for one
  $A\in\mathrm{PSL}_2(\mathbb R)$. Then every point of the overlap has an open
  neighborhood on which $U$ and $V$ differ by a real Möbius transformation.
proof:
  Use the whole overlap, which is open, as the neighborhood at each point and
  retain the same representative $A$ and the same transition identity.
-/
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

/-- Every local hyperbolic chart has the identity real-Mobius transition to itself.

%%handwave
name:
  Identity transition of a local hyperbolic chart
statement:
  Every local upper-half-plane chart $U$ has a real Möbius transition to
  itself: on its domain, $U(x)=I\cdot U(x)$.
proof:
  Choose the identity matrix as the real Möbius representative; its action on
  $\mathbb H$ is the identity.
-/
theorem hasRealMobiusTransition_self (U : HyperbolicLocalChart X g) :
    U.HasRealMobiusTransition U := by
  refine ⟨1, ?_⟩
  intro x _hx _hx'
  simp [realMobiusRepresentativeAction_one]

/-- Every local hyperbolic chart has the identity local real-Mobius transition to itself.

%%handwave
name:
  Identity local transition of a hyperbolic chart
statement:
  At every point of the domain of a local upper-half-plane chart $U$, there is
  an open neighborhood on which the transition from $U$ to itself is a real
  Möbius transformation.
proof:
  [The chart has the identity real Möbius transition to itself on its entire domain](lean:JJMath.HyperbolicLocalChart.hasRealMobiusTransition_self); restrict this global identity transition locally at each point.
-/
theorem hasLocalRealMobiusTransition_self (U : HyperbolicLocalChart X g) :
    U.HasLocalRealMobiusTransition U :=
  hasLocalRealMobiusTransition_of_hasRealMobiusTransition
    (hasRealMobiusTransition_self U)

end HyperbolicLocalChart


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

end HyperbolicLocalModelLocalTransitionAtlas

namespace HyperbolicDevelopingContinuationData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

end HyperbolicDevelopingContinuationData

namespace HyperbolicLocalModelContinuationPipeline

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

end HyperbolicLocalModelContinuationPipeline

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

end HyperbolicMetric

end

end JJMath
