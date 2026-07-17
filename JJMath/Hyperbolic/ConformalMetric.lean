import JJMath.Hyperbolic.Cover
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Conformal metrics on Riemann surfaces

This file introduces a chartwise representation of conformal metrics.  A
conformal density is coordinate-dependent, so the primary data is a squared
density in each complex chart, represented by an ambient function on `ℂ` and
used only on the chart target.
-/

namespace JJMath

open scoped Manifold Topology

/--
The logarithmic conformal factor determined by a squared-density
representative in a complex chart.
-/
noncomputable def logDensityFromDensitySq (ρ : ℂ → ℝ) (z : ℂ) : ℝ :=
  Real.log (ρ z) / 2

/--
The Gaussian-curvature expression computed from a chartwise squared density:
`K = - exp (-2u) Δu`, where `u = log ρ / 2`.
-/
noncomputable def gaussianCurvatureOfDensitySq (ρ : ℂ → ℝ) (z : ℂ) : ℝ :=
  - Real.exp (-(2 * logDensityFromDensitySq ρ z)) *
    Laplacian.laplacian (logDensityFromDensitySq ρ) z

/-- The computed Gaussian curvature only depends on the density germ. -/
theorem gaussianCurvatureOfDensitySq_congr_nhds
    {ρ σ : ℂ → ℝ} {z : ℂ} (h : ρ =ᶠ[𝓝 z] σ) :
    gaussianCurvatureOfDensitySq ρ z =
      gaussianCurvatureOfDensitySq σ z := by
  have hlog :
      logDensityFromDensitySq ρ =ᶠ[𝓝 z] logDensityFromDensitySq σ := by
    filter_upwards [h] with w hw
    simp [logDensityFromDensitySq, hw]
  have hlap :
      Laplacian.laplacian (logDensityFromDensitySq ρ) z =
        Laplacian.laplacian (logDensityFromDensitySq σ) z := by
    rw [(InnerProductSpace.laplacian_congr_nhds hlog).eq_of_nhds]
  have hlogz :
      logDensityFromDensitySq ρ z = logDensityFromDensitySq σ z :=
    hlog.self_of_nhds
  simp [gaussianCurvatureOfDensitySq, hlogz, hlap]

/--
If the logarithmic density determined by a positive squared density satisfies
the Liouville equation at a point, then the corresponding curvature expression
is `-1` there.
-/
theorem gaussianCurvatureOfDensitySq_eq_minus_one_of_liouville
    {ρ : ℂ → ℝ} {z : ℂ} (hpos : 0 < ρ z)
    (hL :
      Laplacian.laplacian (logDensityFromDensitySq ρ) z = ρ z) :
    gaussianCurvatureOfDensitySq ρ z = -1 := by
  have htwo :
      2 * logDensityFromDensitySq ρ z = Real.log (ρ z) := by
    rw [logDensityFromDensitySq]
    ring
  have hexp :
      Real.exp (-(2 * logDensityFromDensitySq ρ z)) = (ρ z)⁻¹ := by
    rw [htwo, Real.exp_neg, Real.exp_log hpos]
  rw [gaussianCurvatureOfDensitySq, hL, hexp]
  field_simp [ne_of_gt hpos]

/--
Chartwise squared-density data for a conformal metric.

The function `densitySqInChart e he` is an ambient representative on `ℂ`;
the metric only uses it on `e.target`.
-/
structure ConformalMetricChartwiseDensityData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The squared density in a chosen complex chart, as an ambient representative on `ℂ`. -/
  densitySqInChart :
    (e : OpenPartialHomeomorph X ℂ) → e ∈ atlas ℂ X → ℂ → ℝ
  /-- The squared density is positive on the chart image. -/
  densitySq_pos :
    ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) z,
      z ∈ e.target → 0 < densitySqInChart e he z
  /-- Chartwise squared densities transform by the usual conformal coordinate-change law. -/
  densitySq_transition :
    ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
      (e' : OpenPartialHomeomorph X ℂ) (he' : e' ∈ atlas ℂ X) z,
        z ∈ e.target →
        e.symm z ∈ e'.source →
        densitySqInChart e he z =
          densitySqInChart e' he' (e' (e.symm z)) *
            Complex.normSq (deriv (fun w : ℂ ↦ e' (e.symm w)) z)

/--
A conformal metric on a Riemann surface, represented by chartwise positive
squared densities and named analytic obligations.

For a local coordinate `z`, the intended metric is `densitySq z |dz|^2`.
Keeping the squared density as the primary object avoids repeatedly expanding
and cancelling square roots in pullback computations.
-/
structure ConformalMetric (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The chartwise squared conformal density data. -/
  chartedDensity : ConformalMetricChartwiseDensityData X

namespace ConformalMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The squared density in a chosen chart. -/
def densitySqInChart (g : ConformalMetric X)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) : ℂ → ℝ :=
  g.chartedDensity.densitySqInChart e he

/-- Positivity of the squared density in an arbitrary chart. -/
theorem positive_densitySqInChart (g : ConformalMetric X)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) : 0 < g.densitySqInChart e he z :=
  g.chartedDensity.densitySq_pos e he z hz

/-- The chartwise coordinate-change law for squared densities. -/
theorem densitySq_transition (g : ConformalMetric X)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (e' : OpenPartialHomeomorph X ℂ) (he' : e' ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hz' : e.symm z ∈ e'.source) :
    g.densitySqInChart e he z =
      g.densitySqInChart e' he' (e' (e.symm z)) *
        Complex.normSq (deriv (fun w : ℂ ↦ e' (e.symm w)) z) :=
  g.chartedDensity.densitySq_transition e he e' he' z hz hz'

/-- Gaussian curvature computed from the density in a chosen chart. -/
noncomputable def gaussianCurvatureInChart (g : ConformalMetric X)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) : ℂ → ℝ :=
  gaussianCurvatureOfDensitySq (g.densitySqInChart e he)

/-- Smoothness of the squared density in complex charts. -/
def smooth_in_charts (g : ConformalMetric X) : Prop :=
  ∀ e he, ContDiffOn ℝ ⊤ (g.densitySqInChart e he) e.target

/--
The finite `C^3` regularity used by local Liouville/Schwarzian formulas follows
from the stored smoothness of the metric.
-/
theorem smooth_in_charts_three (g : ConformalMetric X)
    (h : g.smooth_in_charts) :
    ∀ e he, ContDiffOn ℝ 3 (g.densitySqInChart e he) e.target :=
  fun e he ↦ (h e he).of_le le_top

/-- The Gaussian-curvature predicate. -/
def curvature_eq (g : ConformalMetric X) (K : ℝ) : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) z,
    z ∈ e.target → g.gaussianCurvatureInChart e he z = K

/--
For a metric whose computed chartwise curvature is a fixed constant, the
computed curvature is independent of the chart.  This is the invariant form
used by the hyperbolic/Liouville route.
-/
theorem gaussianCurvatureInChart_eq_of_curvature_eq (g : ConformalMetric X)
    {K : ℝ} (hK : g.curvature_eq K)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (e' : OpenPartialHomeomorph X ℂ) (he' : e' ∈ atlas ℂ X) {z : ℂ}
    (hz : z ∈ e.target) (hz' : e.symm z ∈ e'.source) :
    g.gaussianCurvatureInChart e he z =
      g.gaussianCurvatureInChart e' he' (e' (e.symm z)) := by
  rw [hK e he z hz, hK e' he' (e' (e.symm z)) (e'.map_source hz')]

/-- Smoothness predicate for the chartwise squared-density metric representation. -/
def IsSmooth (g : ConformalMetric X) : Prop :=
  g.smooth_in_charts

/-- A smooth conformal metric has the finite `C^3` regularity needed downstream. -/
theorem IsSmooth.contDiffOn_three (g : ConformalMetric X) (h : g.IsSmooth) :
    ∀ e he, ContDiffOn ℝ 3 (g.densitySqInChart e he) e.target :=
  g.smooth_in_charts_three h

/-- The metric has Gaussian curvature `-1`. -/
def HasCurvatureMinusOne (g : ConformalMetric X) : Prop :=
  g.curvature_eq (-1)

end ConformalMetric

namespace PathHomotopyUniversalCover

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocallySimplyConnectedSpace X] {x₀ : X}

/--
The pullback of a conformal metric to the path-homotopy universal cover.

For a cover chart, the squared density is the base metric density in the
extracted base chart.  The transition law follows because cover coordinate
changes are locally the same as the corresponding base coordinate changes.
-/
noncomputable def pullbackConformalMetric (g : ConformalMetric X) :
    ConformalMetric (PathHomotopyUniversalCover X x₀) where
  chartedDensity :=
  { densitySqInChart := fun e he z =>
      g.densitySqInChart
        (baseChartOfCoverChart (x₀ := x₀) e he)
        (baseChartOfCoverChart_mem_atlas (x₀ := x₀) e he) z
    densitySq_pos := by
      intro e he z hz
      exact g.positive_densitySqInChart
        (baseChartOfCoverChart (x₀ := x₀) e he)
        (baseChartOfCoverChart_mem_atlas (x₀ := x₀) e he)
        (coverChart_target_subset_baseChart_target (x₀ := x₀) e he hz)
    densitySq_transition := by
      intro e he e' he' z hz hz'
      let b := baseChartOfCoverChart (x₀ := x₀) e he
      let b' := baseChartOfCoverChart (x₀ := x₀) e' he'
      have hb : b ∈ atlas ℂ X :=
        baseChartOfCoverChart_mem_atlas (x₀ := x₀) e he
      have hb' : b' ∈ atlas ℂ X :=
        baseChartOfCoverChart_mem_atlas (x₀ := x₀) e' he'
      have hbz : z ∈ b.target :=
        coverChart_target_subset_baseChart_target (x₀ := x₀) e he hz
      have hendpoint :
          endpoint (e.symm z) = b.symm z :=
        endpoint_coverChart_symm_eq_baseChart_symm (x₀ := x₀) e he hz
      have hbz' : b.symm z ∈ b'.source := by
        have hproj :
            endpoint (e.symm z) ∈ b'.source :=
          coverChart_source_projection_mem_baseChart_source (x₀ := x₀) e' he' hz'
        simpa [hendpoint] using hproj
      have hbase :=
        g.densitySq_transition b hb b' hb' (z := z) hbz hbz'
      have hpoint :
          e' (e.symm z) = b' (b.symm z) := by
        calc
          e' (e.symm z) = b' (endpoint (e.symm z)) := by
            exact coverChart_apply_eq_baseChart_apply_endpoint (x₀ := x₀) e' he' hz'
          _ = b' (b.symm z) := by
            rw [hendpoint]
      have hderiv :
          deriv (fun w : ℂ => e' (e.symm w)) z =
            deriv (fun w : ℂ => b' (b.symm w)) z :=
        Filter.EventuallyEq.deriv_eq
          (coverChart_transition_eventuallyEq_baseChart_transition
            (x₀ := x₀) e e' he he' hz hz')
      calc
        g.densitySqInChart b hb z =
            g.densitySqInChart b' hb' (b' (b.symm z)) *
              Complex.normSq (deriv (fun w : ℂ => b' (b.symm w)) z) := hbase
        _ =
            g.densitySqInChart b' hb' (e' (e.symm z)) *
              Complex.normSq (deriv (fun w : ℂ => e' (e.symm w)) z) := by
          rw [hpoint, hderiv] }

end PathHomotopyUniversalCover

/--
%%handwave
name:
  Hyperbolic metric
statement:
  A hyperbolic metric is a smooth conformal metric whose Gaussian curvature is
  everywhere $-1$. In a complex coordinate, if the squared density is
  $e^{2u}$, then the curvature is defined by
  $K = -e^{-2u}\Delta u$; the condition $K = -1$ is equivalently the
  Liouville equation $\Delta u = e^{2u}$.
-/
structure HyperbolicMetric (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The underlying conformal metric. -/
  toConformalMetric : ConformalMetric X
  /-- Smoothness of the squared conformal density. -/
  smooth : toConformalMetric.IsSmooth
  /-- Gaussian curvature is `-1`. -/
  curvature_minus_one : toConformalMetric.HasCurvatureMinusOne

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

instance : Coe (HyperbolicMetric X) (ConformalMetric X) where
  coe g := g.toConformalMetric

end HyperbolicMetric

/--
Chartwise squared-density expression for the statement that `source` is the
pullback of `target` along `f`, at one point and in one chosen source/target
chart pair.
-/
def PullsBackMetricInChartsAt {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] (f : X → Y)
    (target : ConformalMetric Y) (source : ConformalMetric X)
    (sourceChart : OpenPartialHomeomorph X ℂ) (sourceChart_mem_atlas : sourceChart ∈ atlas ℂ X)
    (targetChart : OpenPartialHomeomorph Y ℂ) (targetChart_mem_atlas : targetChart ∈ atlas ℂ Y)
    (x : X) : Prop :=
  x ∈ sourceChart.source →
    f x ∈ targetChart.source →
      ∃ (U : Set ℂ) (localMap : ℂ → ℂ),
        IsOpen U ∧
          sourceChart x ∈ U ∧
          U ⊆ sourceChart.target ∧
          Set.MapsTo sourceChart.symm U sourceChart.source ∧
          Set.MapsTo (fun z : ℂ ↦ f (sourceChart.symm z)) U targetChart.source ∧
          Set.MapsTo localMap U targetChart.target ∧
          (∀ z ∈ U, localMap z = targetChart (f (sourceChart.symm z))) ∧
          DifferentiableAt ℂ localMap (sourceChart x) ∧
          source.densitySqInChart sourceChart sourceChart_mem_atlas (sourceChart x) =
            target.densitySqInChart targetChart targetChart_mem_atlas (localMap (sourceChart x)) *
              Complex.normSq (deriv localMap (sourceChart x))

namespace PullsBackMetricInChartsAt

variable {X Y Z : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [TopologicalSpace Z] [ChartedSpace ℂ Z] {f f' : X → Y}
    {target : ConformalMetric Y} {source : ConformalMetric X}
    {sourceChart : OpenPartialHomeomorph X ℂ}
    {sourceChart_mem_atlas : sourceChart ∈ atlas ℂ X}
    {targetChart : OpenPartialHomeomorph Y ℂ}
    {targetChart_mem_atlas : targetChart ∈ atlas ℂ Y} {x : X}

/--
The chartwise pullback-metric identity is local in the source map.

If `f` and `f'` agree near `x`, any coordinate witness for `f` can be
restricted to the part of the source-coordinate neighborhood where the two
maps agree, giving the same squared-density formula for `f'`.
-/
theorem congr_of_eventuallyEq_nhds
    (h :
      PullsBackMetricInChartsAt f target source
        sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas x)
    (hff' : f =ᶠ[nhds x] f') :
    PullsBackMetricInChartsAt f' target source
      sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas x := by
  intro hx hf'x
  have hfx : f x ∈ targetChart.source := by
    simpa [hff'.eq_of_nhds] using hf'x
  rcases h hx hfx with
    ⟨U, localMap, hUopen, hxU, hUtarget, hsymm_source, hf_maps,
      hlocal_maps, hlocal_eq, hdiff, hdensity⟩
  rcases eventually_nhds_iff.mp hff' with
    ⟨N, hN_eq, hNopen, hxN⟩
  let U' : Set ℂ := U ∩ (sourceChart.target ∩ sourceChart.symm ⁻¹' N)
  refine
    ⟨U', localMap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdiff, hdensity⟩
  · exact hUopen.inter (sourceChart.isOpen_inter_preimage_symm hNopen)
  · refine ⟨hxU, sourceChart.map_source hx, ?_⟩
    simpa [sourceChart.left_inv hx] using hxN
  · intro z hz
    exact hz.2.1
  · intro z hz
    exact hsymm_source hz.1
  · intro z hz
    have hpoint : f (sourceChart.symm z) = f' (sourceChart.symm z) :=
      hN_eq (sourceChart.symm z) hz.2.2
    simpa [hpoint] using hf_maps hz.1
  · intro z hz
    exact hlocal_maps hz.1
  · intro z hz
    have hpoint : f (sourceChart.symm z) = f' (sourceChart.symm z) :=
      hN_eq (sourceChart.symm z) hz.2.2
    simpa [hpoint] using hlocal_eq z hz.1

/--
Concrete chartwise pullback-metric witnesses compose.

The intermediate chart is fixed explicitly.  The proof shrinks the source
coordinate neighborhood so that the first local coordinate expression lands in
the second witness's coordinate neighborhood, then uses the complex chain rule
and multiplicativity of `Complex.normSq`.
-/
theorem comp
    {F : Y → Z} {G : X → Y}
    {targetZ : ConformalMetric Z} {middleY : ConformalMetric Y}
    {sourceX : ConformalMetric X}
    {sourceChart : OpenPartialHomeomorph X ℂ}
    {sourceChart_mem_atlas : sourceChart ∈ atlas ℂ X}
    {middleChart : OpenPartialHomeomorph Y ℂ}
    {middleChart_mem_atlas : middleChart ∈ atlas ℂ Y}
    {targetChart : OpenPartialHomeomorph Z ℂ}
    {targetChart_mem_atlas : targetChart ∈ atlas ℂ Z} {x : X}
    (hGx : G x ∈ middleChart.source)
    (hF :
      PullsBackMetricInChartsAt F targetZ middleY
        middleChart middleChart_mem_atlas targetChart targetChart_mem_atlas (G x))
    (hG :
      PullsBackMetricInChartsAt G middleY sourceX
        sourceChart sourceChart_mem_atlas middleChart middleChart_mem_atlas x) :
    PullsBackMetricInChartsAt (fun x : X => F (G x)) targetZ sourceX
      sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas x := by
  intro hx hFGx
  rcases hG hx hGx with
    ⟨UG, localG, hUGopen, hxUG, hUGtarget, hsymm_source, hG_maps,
      hlocalG_maps, hlocalG_eq, hdiffG, hdensityG⟩
  rcases hF hGx hFGx with
    ⟨UF, localF, hUFopen, hGxUF, hUFtarget, hmiddle_symm_source, hF_maps,
      hlocalF_maps, hlocalF_eq, hdiffF, hdensityF⟩
  let z₀ : ℂ := sourceChart x
  let localMap : ℂ → ℂ := fun z => localF (localG z)
  have hlocalG_z₀ :
      localG z₀ = middleChart (G x) := by
    have h := hlocalG_eq z₀ hxUG
    simpa [z₀, sourceChart.left_inv hx] using h
  have hdiffF_at :
      DifferentiableAt ℂ localF (localG z₀) := by
    simpa [hlocalG_z₀] using hdiffF
  have hlocalG_z₀_mem : localG z₀ ∈ UF := by
    simpa [hlocalG_z₀] using hGxUF
  have hpre_mem :
      localG ⁻¹' UF ∈ nhds z₀ :=
    hdiffG.continuousAt.preimage_mem_nhds (hUFopen.mem_nhds hlocalG_z₀_mem)
  rcases mem_nhds_iff.mp hpre_mem with ⟨N, hNsub, hNopen, hz₀N⟩
  let U : Set ℂ := UG ∩ N
  refine
    ⟨U, localMap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hUGopen.inter hNopen
  · exact ⟨hxUG, hz₀N⟩
  · intro z hz
    exact hUGtarget hz.1
  · intro z hz
    exact hsymm_source hz.1
  · intro z hz
    have hlocalG_UF : localG z ∈ UF := hNsub hz.2
    have hG_source : G (sourceChart.symm z) ∈ middleChart.source :=
      hG_maps hz.1
    have hmiddle_symm :
        middleChart.symm (localG z) = G (sourceChart.symm z) := by
      have hlocal := hlocalG_eq z hz.1
      calc
        middleChart.symm (localG z) =
            middleChart.symm (middleChart (G (sourceChart.symm z))) := by
          rw [hlocal]
        _ = G (sourceChart.symm z) := middleChart.left_inv hG_source
    have hF_source := hF_maps hlocalG_UF
    simpa [hmiddle_symm] using hF_source
  · intro z hz
    exact hlocalF_maps (hNsub hz.2)
  · intro z hz
    have hlocalG_UF : localG z ∈ UF := hNsub hz.2
    have hG_source : G (sourceChart.symm z) ∈ middleChart.source :=
      hG_maps hz.1
    have hmiddle_symm :
        middleChart.symm (localG z) = G (sourceChart.symm z) := by
      have hlocal := hlocalG_eq z hz.1
      calc
        middleChart.symm (localG z) =
            middleChart.symm (middleChart (G (sourceChart.symm z))) := by
          rw [hlocal]
        _ = G (sourceChart.symm z) := middleChart.left_inv hG_source
    have hlocalF := hlocalF_eq (localG z) hlocalG_UF
    simpa [localMap, hmiddle_symm] using hlocalF
  · exact hdiffF_at.comp z₀ hdiffG
  · have hderiv :
        deriv localMap z₀ =
          deriv localF (localG z₀) * deriv localG z₀ := by
      simpa [localMap, Function.comp_def] using
        (deriv_comp z₀ hdiffF_at hdiffG)
    have hdensityF_at :
        middleY.densitySqInChart middleChart middleChart_mem_atlas (localG z₀) =
          targetZ.densitySqInChart targetChart targetChart_mem_atlas
              (localF (localG z₀)) *
            Complex.normSq (deriv localF (localG z₀)) := by
      simpa [hlocalG_z₀] using hdensityF
    calc
      sourceX.densitySqInChart sourceChart sourceChart_mem_atlas (sourceChart x) =
          middleY.densitySqInChart middleChart middleChart_mem_atlas
              (localG (sourceChart x)) *
            Complex.normSq (deriv localG (sourceChart x)) := hdensityG
      _ =
          targetZ.densitySqInChart targetChart targetChart_mem_atlas
              (localF (localG (sourceChart x))) *
            Complex.normSq (deriv localF (localG (sourceChart x))) *
              Complex.normSq (deriv localG (sourceChart x)) := by
        rw [hdensityF_at]
      _ =
          targetZ.densitySqInChart targetChart targetChart_mem_atlas
              (localMap (sourceChart x)) *
            Complex.normSq (deriv localMap (sourceChart x)) := by
        rw [hderiv, Complex.normSq_mul]
        ring

/-- The identity map has the concrete pullback witness between any two charts of one metric. -/
theorem id_map
    [ComplexOneManifold X]
    (g : ConformalMetric X)
    (sourceChart : OpenPartialHomeomorph X ℂ)
    (sourceChart_mem_atlas : sourceChart ∈ atlas ℂ X)
    (targetChart : OpenPartialHomeomorph X ℂ)
    (targetChart_mem_atlas : targetChart ∈ atlas ℂ X) (x : X) :
    PullsBackMetricInChartsAt (fun x : X => x) g g
      sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas x := by
  intro hx htargetx
  let U : Set ℂ := sourceChart.target ∩ sourceChart.symm ⁻¹' targetChart.source
  let localMap : ℂ → ℂ := fun z => targetChart (sourceChart.symm z)
  have hzx_target : sourceChart x ∈ sourceChart.target :=
    sourceChart.map_source hx
  have hsymm_x : sourceChart.symm (sourceChart x) = x :=
    sourceChart.left_inv hx
  have hzx_targetChart_source :
      sourceChart.symm (sourceChart x) ∈ targetChart.source := by
    simpa [hsymm_x] using htargetx
  refine
    ⟨U, localMap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sourceChart.isOpen_inter_preimage_symm targetChart.open_source
  · exact ⟨hzx_target, hzx_targetChart_source⟩
  · intro z hz
    exact hz.1
  · intro z hz
    exact sourceChart.map_target hz.1
  · intro z hz
    exact hz.2
  · intro z hz
    exact targetChart.map_source hz.2
  · intro z hz
    rfl
  · have hsymm_mdiff :
        MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) sourceChart.symm (sourceChart x) :=
      mdifferentiableAt_atlas_symm sourceChart_mem_atlas hzx_target
    have htarget_mdiff :
        MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
          targetChart (sourceChart.symm (sourceChart x)) := by
      simpa [hsymm_x] using
        mdifferentiableAt_atlas targetChart_mem_atlas htargetx
    exact (htarget_mdiff.comp (sourceChart x) hsymm_mdiff).differentiableAt
  · have htransition :=
      g.densitySq_transition sourceChart sourceChart_mem_atlas
        targetChart targetChart_mem_atlas (z := sourceChart x)
        hzx_target hzx_targetChart_source
    simpa [localMap, hsymm_x] using htransition

end PullsBackMetricInChartsAt

/--
`source` is the pullback of `target` along `f`.

The pullback identity is required in every source and target chart where the
point and its image are defined.  At each such point it stores a genuine local
coordinate expression on a source-chart neighborhood, the maps-to facts needed
for the expression to be meaningful, differentiability of that expression, and
the standard squared-density pullback formula.
-/
structure PullsBackMetric {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] (f : X → Y)
    (target : ConformalMetric Y) (source : ConformalMetric X) where
  /-- The pullback squared-density identity in every source/target chart pair. -/
  in_charts :
    ∀ (sourceChart : OpenPartialHomeomorph X ℂ)
      (sourceChart_mem_atlas : sourceChart ∈ atlas ℂ X)
      (targetChart : OpenPartialHomeomorph Y ℂ)
      (targetChart_mem_atlas : targetChart ∈ atlas ℂ Y) (x : X),
        PullsBackMetricInChartsAt f target source
          sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas x

namespace PullsBackMetric

variable {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] {f : X → Y}
    {target : ConformalMetric Y} {source : ConformalMetric X}

/-- The chartwise coordinate formula for pullback metrics. -/
theorem in_charts_at (h : PullsBackMetric f target source)
    (sourceChart : OpenPartialHomeomorph X ℂ)
    (sourceChart_mem_atlas : sourceChart ∈ atlas ℂ X)
    (targetChart : OpenPartialHomeomorph Y ℂ)
    (targetChart_mem_atlas : targetChart ∈ atlas ℂ Y) (x : X) :
    PullsBackMetricInChartsAt f target source
      sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas x :=
  h.in_charts sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas x

/-- Pullback-metric identities are unchanged by replacing the map locally at every point. -/
theorem congr_of_eventuallyEq_nhds {f' : X → Y}
    (h : PullsBackMetric f target source)
    (hff' : ∀ x, f =ᶠ[nhds x] f') :
    PullsBackMetric f' target source where
  in_charts := by
    intro sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas x
    exact PullsBackMetricInChartsAt.congr_of_eventuallyEq_nhds
      (h.in_charts_at sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas x)
      (hff' x)

end PullsBackMetric

namespace PathHomotopyUniversalCover

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocallySimplyConnectedSpace X] [ComplexOneManifold X] {x₀ : X}

/-- The path-homotopy cover metric really is the pullback of the base metric. -/
theorem pullsBackMetric_endpoint_pullbackConformalMetric (g : ConformalMetric X) :
    PullsBackMetric
      (endpoint : PathHomotopyUniversalCover X x₀ → X)
      g (pullbackConformalMetric (x₀ := x₀) g) where
  in_charts := by
    intro sourceChart sourceChart_mem_atlas targetChart targetChart_mem_atlas y hy hfy
    let b := baseChartOfCoverChart (x₀ := x₀) sourceChart sourceChart_mem_atlas
    let hb : b ∈ atlas ℂ X :=
      baseChartOfCoverChart_mem_atlas (x₀ := x₀) sourceChart sourceChart_mem_atlas
    let U : Set ℂ :=
      sourceChart.target ∩
        (b.target ∩ b.symm ⁻¹' targetChart.source)
    let localMap : ℂ → ℂ := fun z => targetChart (b.symm z)
    have hyb_source : endpoint y ∈ b.source :=
      coverChart_source_projection_mem_baseChart_source
        (x₀ := x₀) sourceChart sourceChart_mem_atlas hy
    have hsource_y :
        sourceChart y = b (endpoint y) :=
      coverChart_apply_eq_baseChart_apply_endpoint
        (x₀ := x₀) sourceChart sourceChart_mem_atlas hy
    have hzy_target : sourceChart y ∈ b.target := by
      rw [hsource_y]
      exact b.map_source hyb_source
    have hb_symm_y : b.symm (sourceChart y) = endpoint y := by
      rw [hsource_y]
      exact b.left_inv hyb_source
    have hzy_targetChart_source :
        b.symm (sourceChart y) ∈ targetChart.source := by
      simpa [hb_symm_y] using hfy
    refine
      ⟨U, localMap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact sourceChart.open_target.inter
        (b.isOpen_inter_preimage_symm targetChart.open_source)
    · exact ⟨sourceChart.map_source hy, hzy_target, hzy_targetChart_source⟩
    · intro z hz
      exact hz.1
    · intro z hz
      exact sourceChart.map_target hz.1
    · intro z hz
      have hendpoint :
          endpoint (sourceChart.symm z) = b.symm z :=
        endpoint_coverChart_symm_eq_baseChart_symm
          (x₀ := x₀) sourceChart sourceChart_mem_atlas hz.1
      simpa [hendpoint] using hz.2.2
    · intro z hz
      exact targetChart.map_source hz.2.2
    · intro z hz
      have hendpoint :
          endpoint (sourceChart.symm z) = b.symm z :=
        endpoint_coverChart_symm_eq_baseChart_symm
          (x₀ := x₀) sourceChart sourceChart_mem_atlas hz.1
      simp [localMap, hendpoint]
    · have hb_symm_mdiff :
          MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) b.symm (sourceChart y) :=
        mdifferentiableAt_atlas_symm hb hzy_target
      have htarget_mdiff :
          MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) targetChart (b.symm (sourceChart y)) :=
        mdifferentiableAt_atlas targetChart_mem_atlas hzy_targetChart_source
      exact (htarget_mdiff.comp (sourceChart y) hb_symm_mdiff).differentiableAt
    · have hbase :=
        g.densitySq_transition b hb targetChart targetChart_mem_atlas
          (z := sourceChart y) hzy_target hzy_targetChart_source
      simpa [pullbackConformalMetric, b, hb, localMap] using hbase

end PathHomotopyUniversalCover

end JJMath
