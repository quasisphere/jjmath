import JJMath.Uniformization.GreenFunctionCore
import JJMath.Uniformization.LiouvilleExistence
import JJMath.Uniformization.Perron
import JJMath.Uniformization.RadoSecondCountable
import JJMath.Uniformization.Sard
import JJMath.RiemannianGeometry.SurfaceMetric
import JJMath.RiemannianGeometry.SurfaceVolume

/-!
# Evans potentials from annular Perron exhaustions

This file records the low-friction construction of Evans potentials on
simply connected potential-theoretically parabolic surfaces.  The construction
uses ordinary Perron problems on bounded annuli, extracts bounded-domain
negative Green potentials, and then normalizes these potentials along a smooth
exhaustion.

The genuinely geometric and analytic inputs are kept as explicit theorem
stubs: smooth Perron exhaustions, annular smooth-boundary domains, bounded
Green potentials from annular Perron problems, and the parabolic limiting
argument.
-/

namespace JJMath

open scoped Manifold Topology ENNReal ContDiff

namespace Uniformization

/--
%%handwave
name:
  Local regular-level boundary data
statement:
  A real number is a smooth regular superlevel value of a real-valued function
  if, near every point of the corresponding level set, the superlevel and its
  boundary are cut out by a smooth real defining function with nonzero
  differential.
-/
def SmoothRegularSuperlevelBoundaryData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f : X → ℝ) (c : ℝ) : Prop :=
  ∀ x, f x = c →
    ∃ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X ∧ x ∈ e.source ∧
      ∃ r : ℂ → ℝ, ContDiffOnNhdAt r (e x) ∧
        ∃ dr : ℂ →L[ℝ] ℝ,
          HasFDerivAt r dr (e x) ∧ dr ≠ 0 ∧
            ∀ᶠ y in 𝓝 x,
              y ∈ e.source ∧
                (y ∈ {x : X | c < f x} ↔ r (e y) < 0) ∧
                  (y ∈ frontier {x : X | c < f x} ↔ r (e y) = 0)

/--
%%handwave
name:
  Smooth regular level value
statement:
  A value is a smooth regular level value of a real-valued function if, near
  every point of its level set, the coordinate expression \(c-f\) is smooth,
  has nonzero differential, and its zero set locally agrees with the frontier
  of the corresponding superlevel.
-/
def SmoothRegularLevelValue
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f : X → ℝ) (c : ℝ) : Prop :=
  ∀ x, f x = c →
    ∃ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X ∧ x ∈ e.source ∧
      ∃ r : ℂ → ℝ, r = (fun z : ℂ ↦ c - f (e.symm z)) ∧
        ContDiffOnNhdAt r (e x) ∧
          ∃ dr : ℂ →L[ℝ] ℝ,
            HasFDerivAt r dr (e x) ∧ dr ≠ 0 ∧
              ∀ᶠ y in 𝓝 x,
                y ∈ e.source ∧
                  (y ∈ frontier {x : X | c < f x} ↔ r (e y) = 0)

/--
%%handwave
name:
  Smooth coordinate-regular level value
statement:
  A value is coordinate-regular for a smooth real-valued function if, near
  every point of the corresponding level set, the coordinate expression
  \(c-f\) is smooth and has nonzero differential.
-/
def SmoothCoordinateRegularLevelValue
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f : X → ℝ) (c : ℝ) : Prop :=
  ∀ x, f x = c →
    ∃ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X ∧ x ∈ e.source ∧
      ∃ r : ℂ → ℝ, r = (fun z : ℂ ↦ c - f (e.symm z)) ∧
        ContDiffOnNhdAt r (e x) ∧
          ∃ dr : ℂ →L[ℝ] ℝ,
            HasFDerivAt r dr (e x) ∧ dr ≠ 0

/--
%%handwave
name:
  Coordinate-noncritical level value
statement:
  A value is coordinate-noncritical for a real-valued function if, at every
  point of the corresponding level set, the coordinate expression \(c-f\) has
  nonzero differential.
-/
def CoordinateNoncriticalLevelValue
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f : X → ℝ) (c : ℝ) : Prop :=
  ∀ x, f x = c →
    ∃ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X ∧ x ∈ e.source ∧
      ∃ dr : ℂ →L[ℝ] ℝ,
        HasFDerivAt (fun z : ℂ ↦ c - f (e.symm z)) dr (e x) ∧ dr ≠ 0

/--
%%handwave
name:
  Coordinate-critical level value
statement:
  A value is coordinate-critical for a real-valued function if it is attained
  at some point where, in some complex coordinate, the coordinate expression
  \(c-f\) has zero differential.
-/
def CoordinateCriticalLevelValue
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f : X → ℝ) (c : ℝ) : Prop :=
  ∃ x, f x = c ∧
    ∃ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X ∧ x ∈ e.source ∧
      ∃ dr : ℂ →L[ℝ] ℝ,
        HasFDerivAt (fun z : ℂ ↦ c - f (e.symm z)) dr (e x) ∧ dr = 0

/--
%%handwave
name:
  Smooth regular level values give boundary data
statement:
  A smooth regular level value gives the local regular-superlevel boundary
  data for the corresponding superlevel.
proof:
  Use the canonical defining function \(r=c-f\) in a coordinate chart.  The
  sign condition \(f>c\) is exactly \(r<0\), and the frontier condition is part
  of the regular-level data.
-/
theorem smoothRegularLevelValue_smoothRegularSuperlevelBoundaryData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {f : X → ℝ} {c : ℝ}
    (hregular : SmoothRegularLevelValue f c) :
    SmoothRegularSuperlevelBoundaryData f c := by
  intro x hx_level
  rcases hregular x hx_level with
    ⟨e, he, hx_source, r, hr_def, hr_smooth, dr, hr_deriv, hdr_ne, hfrontier⟩
  refine ⟨e, he, hx_source, r, hr_smooth, dr, hr_deriv, hdr_ne, ?_⟩
  filter_upwards [hfrontier] with y hy
  rcases hy with ⟨hy_source, hy_frontier⟩
  have hry : r (e y) = c - f y := by
    simp [hr_def, e.left_inv hy_source]
  refine ⟨hy_source, ?_, hy_frontier⟩
  constructor
  · intro hy_super
    rw [hry]
    linarith
  · intro hry_neg
    rw [hry] at hry_neg
    exact show c < f y by linarith

/--
%%handwave
name:
  Regular-level data gives a smooth boundary
statement:
  If a continuous real-valued function has local regular-level boundary data
  at a value, then its superlevel set at that value has smooth boundary.
proof:
  A boundary point of the superlevel maps into the boundary of the interval
  \((c,\infty)\), hence lies on the level set \(f=c\).  The prescribed local
  defining function at that level point is exactly the required smooth
  boundary chart.
-/
theorem smoothRegularSuperlevelBoundaryData_hasSmoothBoundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {f : X → ℝ} {c : ℝ} (hf_cont : Continuous f)
    (hdata : SmoothRegularSuperlevelBoundaryData f c) :
    HasSmoothBoundary {x : X | c < f x} := by
  intro x hx_frontier
  have hx_preimage :
      x ∈ f ⁻¹' frontier (Set.Ioi c) := by
    exact hf_cont.frontier_preimage_subset (Set.Ioi c) hx_frontier
  have hx_level : f x = c := by
    simpa using hx_preimage
  exact hdata x hx_level

/--
%%handwave
name:
  Local frontier congruence
statement:
  If two sets agree inside an open neighborhood of a point, then their
  frontiers agree near that point.
proof:
  Intersect both sets with the open neighborhood.  The frontier of an
  intersection with an open set, restricted back to that open set, is the
  original frontier restricted to the same open set.
-/
theorem eventually_frontier_congr_of_inter_eq
    {X : Type} [TopologicalSpace X] {s t U : Set X} {x : X}
    (hU_open : IsOpen U) (hxU : x ∈ U) (hst : s ∩ U = t ∩ U) :
    ∀ᶠ y in 𝓝 x, (y ∈ frontier s ↔ y ∈ frontier t) := by
  filter_upwards [hU_open.mem_nhds hxU] with y hyU
  have hs :
      y ∈ frontier (s ∩ U) ↔ y ∈ frontier s := by
    have h :=
      congrArg (fun A : Set X => y ∈ A)
        (frontier_inter_open_inter (s := s) (t := U) hU_open)
    simpa [hyU] using h
  have ht :
      y ∈ frontier (t ∩ U) ↔ y ∈ frontier t := by
    have h :=
      congrArg (fun A : Set X => y ∈ A)
        (frontier_inter_open_inter (s := t) (t := U) hU_open)
    simpa [hyU] using h
  rw [← hs, hst, ht]

/--
%%handwave
name:
  Local smooth-boundary data transfers across equal germs
statement:
  If two regions and their frontiers agree in a neighborhood of a boundary
  point, then a smooth defining function for one region at that point is also a
  smooth defining function for the other region.
proof:
  Reuse the same coordinate chart and defining function.  The eventual
  equalities replace the membership and frontier conditions in the local
  smooth-boundary data.
-/
theorem hasSmoothBoundary_localData_of_eventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U V : Set X} {x : X}
    (hV : HasSmoothBoundary V) (hxV : x ∈ frontier V)
    (hmem : ∀ᶠ y in 𝓝 x, (y ∈ U ↔ y ∈ V))
    (hfrontier : ∀ᶠ y in 𝓝 x, (y ∈ frontier U ↔ y ∈ frontier V)) :
    ∃ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X ∧ x ∈ e.source ∧
      ∃ r : ℂ → ℝ, ContDiffOnNhdAt r (e x) ∧
        ∃ dr : ℂ →L[ℝ] ℝ,
          HasFDerivAt r dr (e x) ∧ dr ≠ 0 ∧
            ∀ᶠ y in 𝓝 x,
              y ∈ e.source ∧
                (y ∈ U ↔ r (e y) < 0) ∧
                  (y ∈ frontier U ↔ r (e y) = 0) := by
  rcases hV x hxV with
    ⟨e, he, hx_source, r, hr_smooth, dr, hr_deriv, hdr_ne, hlocal⟩
  refine ⟨e, he, hx_source, r, hr_smooth, dr, hr_deriv, hdr_ne, ?_⟩
  filter_upwards [hlocal, hmem, hfrontier] with y hy_local hy_mem hy_frontier
  rcases hy_local with ⟨hy_source, hyV_mem, hyV_frontier⟩
  exact ⟨hy_source, hy_mem.trans hyV_mem, hy_frontier.trans hyV_frontier⟩

/--
%%handwave
name:
  A nonzero real differential is onto the line
statement:
  A nonzero real linear functional on the complex plane has full range in the
  real line.
proof:
  Choose a vector on which the functional is nonzero and rescale it to hit any
  prescribed real number.
-/
theorem realLinearFunctional_range_eq_top_of_nonzero
    (dr : ℂ →L[ℝ] ℝ) (hdr_nonzero : dr ≠ 0) :
    dr.range = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  have hz_exists : ∃ z : ℂ, dr z ≠ 0 := by
    by_contra h
    apply hdr_nonzero
    ext z
    exact not_not.mp (not_exists.mp h z)
  rcases hz_exists with ⟨z, hz⟩
  intro y
  refine ⟨(y / dr z : ℝ) • z, ?_⟩
  calc
    dr ((y / dr z : ℝ) • z) = (y / dr z : ℝ) • dr z := by
      exact map_smul dr (y / dr z : ℝ) z
    _ = (y / dr z) * dr z := by
      simp
    _ = y := by
      field_simp [hz]

/--
%%handwave
name:
  Plane regular sublevels have level frontiers
statement:
  Near a point where a smooth real function on the plane has nonzero
  differential, the frontier of the strict sublevel through that point is
  exactly the corresponding level set.
proof:
  The differential is onto the real line, so the implicit-function theorem
  gives local coordinates in which the function is the first coordinate.  In
  those coordinates the assertion is the elementary frontier computation for
  a half-line, then it is transported back by the local homeomorphism.
-/
theorem smoothPlaneRegularSublevel_eventually_frontier_eq_level
    {r : ℂ → ℝ} {z₀ : ℂ}
    (hr_smooth : ContDiffAt ℝ ∞ r z₀)
    {dr : ℂ →L[ℝ] ℝ}
    (hr_deriv : HasFDerivAt r dr z₀) (hdr_nonzero : dr ≠ 0) :
    ∀ᶠ z in 𝓝 z₀,
      (z ∈ frontier {z : ℂ | r z < r z₀} ↔ r z = r z₀) := by
  have hr_strict : HasStrictFDerivAt r dr z₀ :=
    hr_smooth.hasStrictFDerivAt' hr_deriv (by simp)
  have hdr_range : dr.range = ⊤ :=
    realLinearFunctional_range_eq_top_of_nonzero dr hdr_nonzero
  let Φ : OpenPartialHomeomorph ℂ (ℝ × dr.ker) :=
    hr_strict.implicitToOpenPartialHomeomorph r dr hdr_range
  let S : Set (ℝ × dr.ker) := {p | p.1 < r z₀}
  have hz₀_source : z₀ ∈ Φ.source :=
    hr_strict.mem_implicitToOpenPartialHomeomorph_source hdr_range
  have hpre_frontier :
      Φ.source ∩ Φ ⁻¹' frontier S =
        Φ.source ∩ frontier (Φ ⁻¹' S) :=
    Φ.preimage_frontier S
  have hpreS : Φ ⁻¹' S = {z : ℂ | r z < r z₀} := by
    ext z
    simp [S, Φ]
  have hfrontierS : frontier S = {p : ℝ × dr.ker | p.1 = r z₀} := by
    have h :
        frontier ((Prod.fst : ℝ × dr.ker → ℝ) ⁻¹' Set.Iio (r z₀)) =
          (Prod.fst : ℝ × dr.ker → ℝ) ⁻¹' frontier (Set.Iio (r z₀)) :=
      (isOpenMap_fst.preimage_frontier_eq_frontier_preimage
        continuous_fst (Set.Iio (r z₀))).symm
    simpa [S, frontier_Iio] using h
  filter_upwards [Φ.open_source.mem_nhds hz₀_source] with z hz_source
  have hmem :=
    congrArg (fun A : Set ℂ => z ∈ A) hpre_frontier
  have hz_frontier :
      z ∈ frontier (Φ ⁻¹' S) ↔ z ∈ Φ ⁻¹' frontier S := by
    simpa [hz_source] using hmem.symm
  simpa [hpreS, hfrontierS, S, Φ] using hz_frontier

/--
%%handwave
name:
  Plane regular zero sublevels have zero frontiers
statement:
  Near a regular zero of a smooth real function on the plane, the frontier of
  its negative set is exactly its zero set.
proof:
  Apply the regular-sublevel frontier theorem to the level through the base
  point.
-/
theorem smoothPlaneRegularZeroSublevel_eventually_frontier_eq_zero
    {r : ℂ → ℝ} {z₀ : ℂ}
    (hr_smooth : ContDiffAt ℝ ∞ r z₀)
    {dr : ℂ →L[ℝ] ℝ}
    (hr_deriv : HasFDerivAt r dr z₀) (hdr_nonzero : dr ≠ 0)
    (hr_zero : r z₀ = 0) :
    ∀ᶠ z in 𝓝 z₀,
      (z ∈ frontier {z : ℂ | r z < 0} ↔ r z = 0) := by
  simpa [hr_zero] using
    smoothPlaneRegularSublevel_eventually_frontier_eq_level
      hr_smooth hr_deriv hdr_nonzero

/--
%%handwave
name:
  Smooth surface functions are smooth on coordinate targets
statement:
  If a real-valued function is smooth on a Riemann surface, then in any
  complex coordinate chart its pullback to the coordinate plane is smooth on
  the target of the chart.
proof:
  Compose the smooth function with the inverse of the surface chart, viewed as
  a smooth real chart.
-/
theorem smoothFunction_chartExpression_contDiffOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {f : X → ℝ} (hf_smooth : ContMDiff SurfaceRealModel 𝓘(ℝ) ∞ f)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ atlas ℂ X) :
    ContDiffOn ℝ ∞ (fun z : ℂ ↦ f (e.symm z)) e.target := by
  letI : IsManifold SurfaceRealModel ∞ X :=
    complexOneManifold_has_real_smooth_structure X
  have hsymm : ContMDiffOn SurfaceRealModel SurfaceRealModel ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := SurfaceRealModel) (n := ∞) he)
  have hcomp : ContMDiffOn SurfaceRealModel 𝓘(ℝ, ℝ) ∞
      (fun z : ℂ ↦ f (e.symm z)) e.target := by
    exact hf_smooth.contMDiffOn.comp (t := Set.univ) hsymm
      (fun _ _ ↦ by simp)
  simpa [SurfaceRealModel] using (contMDiffOn_iff_contDiffOn.mp hcomp)

/--
%%handwave
name:
  Smooth surface functions are smooth in a chosen chart
statement:
  If a real-valued function is smooth on a Riemann surface, then in any
  complex coordinate chart the expression \(c-f\) is an ordinary smooth real
  function near every source point of the chart.
proof:
  Compose the smooth function with the inverse of the surface chart, viewed as
  a smooth real chart, and subtract from the constant \(c\).
-/
theorem smoothFunction_coordinateExpression_contDiffOnNhdAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {f : X → ℝ} (hf_smooth : ContMDiff SurfaceRealModel 𝓘(ℝ) ∞ f)
    {c : ℝ} {x : X} {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ atlas ℂ X) (hx_source : x ∈ e.source) :
    ContDiffOnNhdAt (fun z : ℂ ↦ c - f (e.symm z)) (e x) := by
  have hcd : ContDiffOn ℝ ∞ (fun z : ℂ ↦ f (e.symm z)) e.target :=
    smoothFunction_chartExpression_contDiffOn (X := X) (f := f) hf_smooth he
  have hx_target : e x ∈ e.target := e.map_source hx_source
  refine ⟨e.target, e.open_target.mem_nhds hx_target, ?_⟩
  simpa using (contDiffOn_const (c := c)).sub hcd

/--
%%handwave
name:
  Noncritical smooth levels are coordinate-regular
statement:
  For a smooth real-valued function on a Riemann surface, every
  coordinate-noncritical level value is a smooth coordinate-regular level
  value.
proof:
  The noncritical assumption gives a chart and a nonzero differential at each
  level point.  Smoothness of the coordinate expression follows from the
  manifold smoothness of the function.
-/
theorem coordinateNoncriticalLevelValue_smoothCoordinateRegularLevelValue
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {f : X → ℝ} {c : ℝ}
    (hf_smooth : ContMDiff SurfaceRealModel 𝓘(ℝ) ∞ f)
    (hnoncritical : CoordinateNoncriticalLevelValue f c) :
    SmoothCoordinateRegularLevelValue f c := by
  intro x hx_level
  rcases hnoncritical x hx_level with
    ⟨e, he, hx_source, dr, hr_deriv, hdr_ne⟩
  refine ⟨e, he, hx_source, (fun z : ℂ ↦ c - f (e.symm z)), rfl, ?_, dr, hr_deriv, hdr_ne⟩
  exact smoothFunction_coordinateExpression_contDiffOnNhdAt
    (X := X) (f := f) hf_smooth (c := c) he hx_source

/--
%%handwave
name:
  Noncritical values give coordinate-noncritical levels
statement:
  If a value is not coordinate-critical for a smooth real-valued function,
  then every point of that level has a coordinate expression with nonzero
  differential.
proof:
  At a point of the level, use the preferred complex chart.  Smoothness of the
  function gives a derivative of the coordinate expression.  If that
  derivative were zero, the value would be coordinate-critical.
-/
theorem not_coordinateCriticalLevelValue_coordinateNoncriticalLevelValue
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {f : X → ℝ} {c : ℝ}
    (hf_smooth : ContMDiff SurfaceRealModel 𝓘(ℝ) ∞ f)
    (hnotcrit : ¬ CoordinateCriticalLevelValue f c) :
    CoordinateNoncriticalLevelValue f c := by
  intro x hx_level
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have hx_source : x ∈ e.source := mem_chart_source ℂ x
  let r : ℂ → ℝ := fun z : ℂ ↦ c - f (e.symm z)
  let dr : ℂ →L[ℝ] ℝ := fderiv ℝ r (e x)
  have hr_smooth : ContDiffAt ℝ ∞ r (e x) :=
    (smoothFunction_coordinateExpression_contDiffOnNhdAt
      (X := X) (f := f) hf_smooth (c := c) he hx_source).contDiffAt
  have hr_deriv : HasFDerivAt r dr (e x) :=
    (hr_smooth.differentiableAt (by simp)).hasFDerivAt
  have hdr_ne : dr ≠ 0 := by
    intro hdr_zero
    apply hnotcrit
    exact ⟨x, hx_level, e, he, hx_source, dr, hr_deriv, hdr_zero⟩
  exact ⟨e, he, hx_source, dr, hr_deriv, hdr_ne⟩

/--
%%handwave
name:
  Coordinate-regular levels have regular frontiers
statement:
  If a value is coordinate-regular for a smooth real-valued function, then it
  is a smooth regular level value: locally, the frontier of the superlevel is
  exactly the zero set of \(c-f\).
proof:
  At a level point the differential of \(c-f\) is nonzero.  After a real
  linear change of coordinates, the implicit function theorem represents the
  level set as a smooth graph and puts the two signs of \(c-f\) on opposite
  sides of that graph.  This identifies the local frontier of the superlevel
  with the zero set.
-/
theorem smoothCoordinateRegularLevelValue_smoothRegularLevelValue
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {f : X → ℝ} {c : ℝ}
    (hregular : SmoothCoordinateRegularLevelValue f c) :
    SmoothRegularLevelValue f c := by
  intro x hx_level
  rcases hregular x hx_level with
    ⟨e, he, hx_source, r, hr_def, hr_smooth, dr, hr_deriv, hdr_ne⟩
  refine ⟨e, he, hx_source, r, hr_def, hr_smooth, dr, hr_deriv, hdr_ne, ?_⟩
  let S : Set X := {y : X | c < f y}
  let V : Set ℂ := {z : ℂ | r z < 0}
  let T : Set X := e ⁻¹' V
  have hr_zero : r (e x) = 0 := by
    simp [hr_def, e.left_inv hx_source, hx_level]
  have hlocal_eq : S ∩ e.source = T ∩ e.source := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨hyS, hy_source⟩
      refine ⟨?_, hy_source⟩
      have hry : r (e y) = c - f y := by
        simp [hr_def, e.left_inv hy_source]
      have hyS' : c < f y := by
        simpa [S] using hyS
      dsimp [T, V]
      rw [hry]
      linarith
    · intro hy
      rcases hy with ⟨hyT, hy_source⟩
      refine ⟨?_, hy_source⟩
      have hry : r (e y) = c - f y := by
        simp [hr_def, e.left_inv hy_source]
      dsimp [T, V] at hyT
      rw [hry] at hyT
      exact show c < f y by linarith
  have hfrontier_congr :
      ∀ᶠ y in 𝓝 x, (y ∈ frontier S ↔ y ∈ frontier T) :=
    eventually_frontier_congr_of_inter_eq e.open_source hx_source hlocal_eq
  have hchart_frontier :
      ∀ᶠ y in 𝓝 x, (y ∈ frontier T ↔ e y ∈ frontier V) := by
    filter_upwards [e.open_source.mem_nhds hx_source] with y hy_source
    have hmem :=
      congrArg (fun A : Set X => y ∈ A) (e.preimage_frontier V)
    have hiff :
        y ∈ frontier T ↔ y ∈ e ⁻¹' frontier V := by
      simpa [T, hy_source] using hmem.symm
    simpa [T] using hiff
  have hplane :
      ∀ᶠ y in 𝓝 x, (e y ∈ frontier V ↔ r (e y) = 0) :=
    (e.continuousAt hx_source).eventually
      (smoothPlaneRegularZeroSublevel_eventually_frontier_eq_zero
        hr_smooth.contDiffAt hr_deriv hdr_ne hr_zero)
  filter_upwards [e.open_source.mem_nhds hx_source,
    hfrontier_congr, hchart_frontier, hplane] with y hy_source hy_congr hy_chart hy_plane
  exact ⟨hy_source, hy_congr.trans (hy_chart.trans hy_plane)⟩

/--
%%handwave
name:
  Bounded smooth plane critical values have measure zero
statement:
  For a smooth real-valued function on an open subset of the complex plane,
  the set of critical values attained on any bounded subset has Lebesgue
  measure zero.
proof:
  This is the bounded local Euclidean form of Sard's theorem for a smooth map
  from the real plane to the real line.
-/
theorem smoothPlaneFunction_boundedCriticalValuesOn_volume_zero
    {g : ℂ → ℝ} {U S : Set ℂ} (hU_open : IsOpen U)
    (hS_subset : S ⊆ U) (hS_bounded : Bornology.IsBounded S)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    MeasureTheory.volume {c : ℝ | PlaneCriticalValueOn g S c} = 0 := by
  exact smoothPlaneFunction_boundedCriticalValuesOn_volume_zero_sard
    hU_open hS_subset hS_bounded hg_smooth

/--
%%handwave
name:
  Smooth plane critical values have measure zero
statement:
  For a smooth real-valued function on an open subset of the complex plane,
  the set of critical values has Lebesgue measure zero.
proof:
  Cover the open set by the countable family of its intersections with
  centered closed balls.  Sard's theorem on each bounded piece gives a null
  critical-value set, and countable subadditivity gives the result.
-/
theorem smoothPlaneFunction_criticalValuesOn_volume_zero
    {g : ℂ → ℝ} {U : Set ℂ} (hU_open : IsOpen U)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    MeasureTheory.volume {c : ℝ | PlaneCriticalValueOn g U c} = 0 := by
  let E : ℕ → Set ℝ := fun n ↦
    {c : ℝ | PlaneCriticalValueOn g (U ∩ Metric.closedBall (0 : ℂ) n) c}
  have hsubset : {c : ℝ | PlaneCriticalValueOn g U c} ⊆ ⋃ n : ℕ, E n := by
    intro c hc
    rcases hc with ⟨z, hzU, hgz, hzcrit⟩
    have hz_cover : z ∈ ⋃ n : ℕ, U ∩ Metric.closedBall (0 : ℂ) n := by
      rw [Metric.iUnion_inter_closedBall_nat]
      exact hzU
    rcases Set.mem_iUnion.mp hz_cover with ⟨n, hzn⟩
    exact Set.mem_iUnion.mpr ⟨n, z, hzn, hgz, hzcrit⟩
  have hE_zero : ∀ n, MeasureTheory.volume (E n) = 0 := by
    intro n
    have hS_subset : U ∩ Metric.closedBall (0 : ℂ) n ⊆ U :=
      Set.inter_subset_left
    have hS_bounded :
        Bornology.IsBounded (U ∩ Metric.closedBall (0 : ℂ) n) :=
      Metric.isBounded_closedBall.subset Set.inter_subset_right
    exact smoothPlaneFunction_boundedCriticalValuesOn_volume_zero
      (g := g) (U := U) (S := U ∩ Metric.closedBall (0 : ℂ) n)
      hU_open hS_subset hS_bounded hg_smooth
  exact MeasureTheory.measure_mono_null hsubset
    (MeasureTheory.measure_iUnion_null hE_zero)

/--
%%handwave
name:
  Coordinate criticality is independent of the chosen chart
statement:
  If the coordinate expression \(c-f\) has zero derivative in one chart at a
  point, then it has zero derivative in any other chart containing that point.
proof:
  On the chart overlap the two coordinate expressions differ by composition
  with the smooth transition map.  The chain rule preserves vanishing of the
  derivative, and the local identity of the two expressions transfers the
  derivative statement to the second chart.
-/
theorem coordinateCritical_chartExpression_hasFDerivAt_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {f : X → ℝ} {c : ℝ} {x : X}
    {e d : OpenPartialHomeomorph X ℂ}
    (he : e ∈ atlas ℂ X) (hx_e : x ∈ e.source)
    {dr : ℂ →L[ℝ] ℝ}
    (hr_e : HasFDerivAt (fun z : ℂ ↦ c - f (e.symm z)) dr (e x))
    (hdr : dr = 0)
    (hd : d ∈ atlas ℂ X) (hx_d : x ∈ d.source) :
    HasFDerivAt
      (fun z : ℂ ↦ c - f (d.symm z)) (0 : ℂ →L[ℝ] ℝ) (d x) := by
  letI : IsManifold SurfaceRealModel ∞ X :=
    complexOneManifold_has_real_smooth_structure X
  let r_e : ℂ → ℝ := fun z : ℂ ↦ c - f (e.symm z)
  let r_d : ℂ → ℝ := fun z : ℂ ↦ c - f (d.symm z)
  let τ : ℂ → ℂ := fun z : ℂ ↦ e (d.symm z)
  have hdx_target : d x ∈ d.target := d.map_source hx_d
  have hτ_base : τ (d x) = e x := by
    simp [τ, d.left_inv hx_d]
  have hsymm_mdiff :
      ContMDiffAt SurfaceRealModel SurfaceRealModel ∞ d.symm (d x) :=
    contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := SurfaceRealModel) (n := ∞) hd)
      hdx_target
  have hchart_mdiff :
      ContMDiffAt SurfaceRealModel SurfaceRealModel ∞ e (d.symm (d x)) := by
    have hchart :
        ContMDiffAt SurfaceRealModel SurfaceRealModel ∞ e x :=
      contMDiffAt_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := SurfaceRealModel) (n := ∞) he)
        hx_e
    simpa [d.left_inv hx_d] using hchart
  have hτ_mdiff :
      ContMDiffAt SurfaceRealModel SurfaceRealModel ∞ τ (d x) :=
    hchart_mdiff.comp (d x) hsymm_mdiff
  have hτ_smooth : ContDiffAt ℝ ∞ τ (d x) := by
    simpa [SurfaceRealModel, τ] using hτ_mdiff.contDiffAt
  have hτ_deriv : HasFDerivAt τ (fderiv ℝ τ (d x)) (d x) :=
    (hτ_smooth.differentiableAt (by simp)).hasFDerivAt
  have hr_e_at : HasFDerivAt r_e dr (τ (d x)) := by
    simpa [r_e, hτ_base] using hr_e
  have hcomp :
      HasFDerivAt (r_e ∘ τ) (dr.comp (fderiv ℝ τ (d x))) (d x) :=
    hr_e_at.comp (d x) hτ_deriv
  have hcomp_zero : HasFDerivAt (r_e ∘ τ) (0 : ℂ →L[ℝ] ℝ) (d x) := by
    simpa [hdr] using hcomp
  have he_source_nhds : d.symm ⁻¹' e.source ∈ 𝓝 (d x) :=
    (d.symm.continuousAt hdx_target).preimage_mem_nhds
      (e.open_source.mem_nhds (by simpa [d.left_inv hx_d] using hx_e))
  have hlocal : r_d =ᶠ[𝓝 (d x)] r_e ∘ τ := by
    filter_upwards [he_source_nhds] with z hz
    simp [r_d, r_e, τ, e.left_inv hz]
  simpa [r_d] using hcomp_zero.congr_of_eventuallyEq hlocal

/--
%%handwave
name:
  Coordinate critical values reduce to countably many charts
statement:
  For a smooth real-valued function on a Riemann surface, the set of
  coordinate-critical values is contained in the union of the critical-value
  sets coming from a countable preferred-coordinate cover.
proof:
  Choose a countable cover by preferred coordinate charts.  At a critical
  point, pass from the witnessing coordinate to a preferred chart containing
  that point; the transition map is a local diffeomorphism, so vanishing of
  the differential is preserved.
-/
theorem smoothFunction_coordinateCriticalValues_subset_countable_chartCriticalValues
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (f : X → ℝ) (_hf_smooth : ContMDiff SurfaceRealModel 𝓘(ℝ) ∞ f) :
    ∃ center : ℕ → X,
      {c : ℝ | CoordinateCriticalLevelValue f c} ⊆
        ⋃ n : ℕ,
          {c : ℝ |
            PlaneCriticalValueOn
              (fun z : ℂ ↦ f ((chartAt ℂ (center n)).symm z))
              (chartAt ℂ (center n)).target c} := by
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  haveI : Nonempty X := PathConnectedSpace.nonempty
  rcases exists_nat_chartAt_source_cover X with ⟨center, hcover⟩
  refine ⟨center, ?_⟩
  intro c hc
  rcases hc with ⟨x, hx_level, e, he, hx_e, dr, hr_e, hdr⟩
  have hx_cover : x ∈ ⋃ n : ℕ, (chartAt ℂ (center n)).source := by
    simp [hcover]
  rcases Set.mem_iUnion.mp hx_cover with ⟨n, hx_d⟩
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  let d : OpenPartialHomeomorph X ℂ := chartAt ℂ (center n)
  have hd : d ∈ atlas ℂ X := chart_mem_atlas ℂ (center n)
  have hrd_zero :
      HasFDerivAt
        (fun z : ℂ ↦ c - f (d.symm z)) (0 : ℂ →L[ℝ] ℝ) (d x) :=
    coordinateCritical_chartExpression_hasFDerivAt_zero
      (X := X) (f := f) (c := c) (x := x)
      (e := e) (d := d) he hx_e hr_e hdr hd hx_d
  have hg_zero :
      HasFDerivAt (fun z : ℂ ↦ f (d.symm z)) (0 : ℂ →L[ℝ] ℝ) (d x) := by
    convert hrd_zero.const_sub c using 1
    · ext z
      ring
    · simp
  refine ⟨d x, d.map_source hx_d, ?_, ?_⟩
  · simp [d, d.left_inv hx_d, hx_level]
  · simpa [d] using hg_zero.fderiv

/--
%%handwave
name:
  Coordinate-critical values have measure zero
statement:
  For a smooth real-valued function on a Riemann surface, the set of
  coordinate-critical values has Lebesgue measure zero.
proof:
  This is Sard's theorem for smooth maps from a real surface to the real line,
  applied in a countable complex-coordinate cover.
-/
theorem smoothFunction_coordinateCriticalValues_volume_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (f : X → ℝ) (hf_smooth : ContMDiff SurfaceRealModel 𝓘(ℝ) ∞ f) :
    MeasureTheory.volume {c : ℝ | CoordinateCriticalLevelValue f c} = 0 := by
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  rcases smoothFunction_coordinateCriticalValues_subset_countable_chartCriticalValues
      (X := X) f hf_smooth with
    ⟨center, hsubset⟩
  let E : ℕ → Set ℝ := fun n ↦
    {c : ℝ |
      PlaneCriticalValueOn
        (fun z : ℂ ↦ f ((chartAt ℂ (center n)).symm z))
        (chartAt ℂ (center n)).target c}
  have hE_zero : ∀ n, MeasureTheory.volume (E n) = 0 := by
    intro n
    have he : chartAt ℂ (center n) ∈ atlas ℂ X :=
      chart_mem_atlas ℂ (center n)
    have hg_smooth : ContDiffOn ℝ ∞
        (fun z : ℂ ↦ f ((chartAt ℂ (center n)).symm z))
        (chartAt ℂ (center n)).target :=
      smoothFunction_chartExpression_contDiffOn
        (X := X) (f := f) hf_smooth he
    simpa [E] using
      smoothPlaneFunction_criticalValuesOn_volume_zero
        (g := fun z : ℂ ↦ f ((chartAt ℂ (center n)).symm z))
        (U := (chartAt ℂ (center n)).target)
        (chartAt ℂ (center n)).open_target hg_smooth
  have hUnion_zero : MeasureTheory.volume (⋃ n, E n) = 0 :=
    MeasureTheory.measure_iUnion_null hE_zero
  exact MeasureTheory.measure_mono_null hsubset hUnion_zero

/--
%%handwave
name:
  Sard gives values outside the coordinate-critical image
statement:
  A smooth real-valued function on a Riemann surface has a value \(c\), with
  \(0<c<1\), which is not coordinate-critical.
proof:
  The coordinate-critical values have measure zero.  Since the interval
  \((0,1)\) has positive Lebesgue measure, it contains a value outside the
  coordinate-critical set.
-/
theorem smoothFunction_exists_nonCoordinateCriticalLevelValue
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (f : X → ℝ) (hf_smooth : ContMDiff SurfaceRealModel 𝓘(ℝ) ∞ f) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ¬ CoordinateCriticalLevelValue f c := by
  let C : Set ℝ := {c : ℝ | CoordinateCriticalLevelValue f c}
  have hC_zero : MeasureTheory.volume C = 0 :=
    smoothFunction_coordinateCriticalValues_volume_zero f hf_smooth
  by_contra hnone
  have hI_subset : Set.Ioo (0 : ℝ) 1 ⊆ C := by
    intro c hc
    by_contra hcC
    exact hnone ⟨c, hc.1, hc.2, hcC⟩
  have hI_zero : MeasureTheory.volume (Set.Ioo (0 : ℝ) 1) = 0 :=
    MeasureTheory.measure_mono_null hI_subset hC_zero
  have hI_pos : MeasureTheory.volume (Set.Ioo (0 : ℝ) 1) ≠ 0 := by
    norm_num [Real.volume_Ioo]
  exact hI_pos hI_zero

/--
%%handwave
name:
  Sard gives coordinate-noncritical level values
statement:
  A smooth real-valued function on a Riemann surface has a value \(c\), with
  \(0<c<1\), which is coordinate-noncritical.
proof:
  This is Sard's theorem for smooth maps from a real surface to the real line:
  critical values have empty interior, so some value in \((0,1)\) is regular.
  In local complex coordinates, regularity is exactly nonvanishing of the
  differential of \(c-f\).
-/
theorem smoothFunction_exists_coordinateNoncriticalLevelValue
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (f : X → ℝ) (hf_smooth : ContMDiff SurfaceRealModel 𝓘(ℝ) ∞ f) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ CoordinateNoncriticalLevelValue f c := by
  rcases smoothFunction_exists_nonCoordinateCriticalLevelValue f hf_smooth with
    ⟨c, hc_pos, hc_lt_one, hnotcrit⟩
  exact ⟨c, hc_pos, hc_lt_one,
    not_coordinateCriticalLevelValue_coordinateNoncriticalLevelValue
      hf_smooth hnotcrit⟩

/--
%%handwave
name:
  Sard gives coordinate-regular level values
statement:
  A smooth real-valued function on a Riemann surface has a value \(c\), with
  \(0<c<1\), which is coordinate-regular.
proof:
  Choose a regular value in the interval \((0,1)\) by Sard's theorem.  At
  every point of the level set, the coordinate expression \(c-f\) is smooth
  and has nonzero differential.  If the level set is empty, the condition is
  vacuous.
-/
theorem smoothFunction_exists_smoothCoordinateRegularLevelValue
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (f : X → ℝ) (hf_smooth : ContMDiff SurfaceRealModel 𝓘(ℝ) ∞ f) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ SmoothCoordinateRegularLevelValue f c := by
  rcases smoothFunction_exists_coordinateNoncriticalLevelValue f hf_smooth with
    ⟨c, hc_pos, hc_lt_one, hnoncritical⟩
  exact ⟨c, hc_pos, hc_lt_one,
    coordinateNoncriticalLevelValue_smoothCoordinateRegularLevelValue
      hf_smooth hnoncritical⟩

/--
%%handwave
name:
  Sard gives smooth regular level values
statement:
  A smooth real-valued function on a Riemann surface has a value \(c\) with
  \(0<c<1\) which is a smooth regular level value.
proof:
  Choose a regular value \(c\in(0,1)\) by Sard's theorem.  At points of the
  level set \(f=c\), the nonzero differential and the implicit function
  theorem identify the local frontier of \(\{f>c\}\) with the zero set of the
  coordinate function \(c-f\).  If the level set is empty, the condition is
  vacuous.
-/
theorem smoothFunction_exists_smoothRegularLevelValue
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (f : X → ℝ) (hf_smooth : ContMDiff SurfaceRealModel 𝓘(ℝ) ∞ f) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ SmoothRegularLevelValue f c := by
  rcases smoothFunction_exists_smoothCoordinateRegularLevelValue f hf_smooth with
    ⟨c, hc_pos, hc_lt_one, hregular⟩
  exact ⟨c, hc_pos, hc_lt_one,
    smoothCoordinateRegularLevelValue_smoothRegularLevelValue hregular⟩

/--
%%handwave
name:
  Sard gives local regular-level boundary data
statement:
  A smooth real-valued function on a Riemann surface has a value \(c\) with
  \(0<c<1\) such that the superlevel \(\{f>c\}\) has local regular-level
  boundary data.
proof:
  Choose a smooth regular level value \(c\in(0,1)\).  The canonical coordinate
  defining functions \(c-f\) then supply the local superlevel boundary data.
-/
theorem smoothFunction_exists_smoothRegularSuperlevelBoundaryData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (f : X → ℝ) (hf_smooth : ContMDiff SurfaceRealModel 𝓘(ℝ) ∞ f) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ SmoothRegularSuperlevelBoundaryData f c := by
  rcases smoothFunction_exists_smoothRegularLevelValue f hf_smooth with
    ⟨c, hc_pos, hc_lt_one, hregular⟩
  exact ⟨c, hc_pos, hc_lt_one,
    smoothRegularLevelValue_smoothRegularSuperlevelBoundaryData hregular⟩

/--
%%handwave
name:
  Smooth functions have smooth regular superlevels
statement:
  A smooth real-valued function on a Riemann surface has a superlevel
  \(\{f>c\}\), with \(0<c<1\), whose boundary is smooth.
proof:
  Choose a value \(c\in(0,1)\) with local regular-level boundary data.  The
  corresponding local defining functions give the smooth-boundary condition
  for the superlevel.
-/
theorem smoothFunction_exists_smoothRegularSuperlevel
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (f : X → ℝ) (hf_smooth : ContMDiff SurfaceRealModel 𝓘(ℝ) ∞ f) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ HasSmoothBoundary {x : X | c < f x} := by
  rcases smoothFunction_exists_smoothRegularSuperlevelBoundaryData f hf_smooth with
    ⟨c, hc_pos, hc_lt_one, hdata⟩
  exact ⟨c, hc_pos, hc_lt_one,
    smoothRegularSuperlevelBoundaryData_hasSmoothBoundary
      hf_smooth.continuous hdata⟩

/--
%%handwave
name:
  Smooth cutoff regular level gives a domain
statement:
  If a smooth function on a Riemann surface is equal to \(1\) near a nonempty
  compact set, vanishes outside a relatively compact open set, and takes
  values in \([0,1]\), then a regular superlevel set is a smooth relatively
  compact domain containing the compact set and with closure contained in the
  open set.
proof:
  Choose a smooth regular superlevel \(\{f>c\}\) with \(0<c<1\).  The cutoff is
  \(1\) on the compact set, so the compact set lies in this superlevel.  Since
  the cutoff is \(0\) off the open set, the closure of the superlevel lies in
  the open set.  Relative compactness follows because the open set has compact
  closure.
-/
theorem smoothCutoff_regularSuperlevel_smoothBoundaryDomain_between
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {K U : Set X} (_hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (_hU_open : IsOpen U) (hU_compact : IsCompact (closure U))
    (f : X → ℝ) (hf_smooth : ContMDiff SurfaceRealModel 𝓘(ℝ) ∞ f)
    (hf_one_near : ∀ᶠ x in 𝓝ˢ K, f x = 1)
    (hf_zero_off : ∀ x ∉ U, f x = 0)
    (_hf_range : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ Ω : SmoothBoundaryDomain X,
      K ⊆ Ω.carrier ∧ closure Ω.carrier ⊆ U := by
  rcases smoothFunction_exists_smoothRegularSuperlevel f hf_smooth with
    ⟨c, hc_pos, hc_lt_one, hsuperlevel_smooth⟩
  let S : Set X := {x : X | c < f x}
  have hf_cont : Continuous f := hf_smooth.continuous
  have hS_open : IsOpen S := by
    simpa [S, Set.preimage, Set.mem_setOf_eq] using
      (isOpen_Ioi : IsOpen (Set.Ioi c)).preimage hf_cont
  have hK_subset_S : K ⊆ S := by
    intro x hxK
    have hfx : f x = 1 := hf_one_near.self_of_nhdsSet x hxK
    simpa [S, hfx] using hc_lt_one
  have hS_nonempty : S.Nonempty := hK_nonempty.mono hK_subset_S
  have hclosure_le : closure S ⊆ {x : X | c ≤ f x} := by
    simpa [S] using closure_lt_subset_le continuous_const hf_cont
  have hclosure_subset_U : closure S ⊆ U := by
    intro x hx
    by_contra hxU
    have hcx : c ≤ f x := hclosure_le hx
    have hfx : f x = 0 := hf_zero_off x hxU
    linarith
  have hS_compact_closure : IsCompact (closure S) := by
    exact hU_compact.of_isClosed_subset isClosed_closure
      (fun x hx ↦ subset_closure (hclosure_subset_U hx))
  refine ⟨{
    carrier := S
    isOpen := hS_open
    nonempty := hS_nonempty
    compact_closure := hS_compact_closure
    smooth_boundary := by
      simpa [S] using hsuperlevel_smooth
  }, hK_subset_S, hclosure_subset_U⟩

/--
%%handwave
name:
  Smooth domain between a compact set and an open set
statement:
  If a nonempty compact set is contained in an open set of a Riemann surface,
  then it is contained in a smooth relatively compact domain whose closure
  still lies in the open set.
proof:
  First shrink the open set to an open neighborhood of the compact set whose
  closure is compact and still lies in the original open set.  Use the smooth
  cutoff supplied by partitions of unity for this relatively compact
  neighborhood: it is \(1\) near the compact set, \(0\) outside the shrunken
  open set, and takes values in \([0,1]\).
  Applying the regular-superlevel construction gives the required smooth
  relatively compact domain.
-/
theorem exists_smoothBoundaryDomain_between_compact_and_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {K U : Set X} (hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (hU_open : IsOpen U) (hKU : K ⊆ U) :
    ∃ Ω : SmoothBoundaryDomain X,
      K ⊆ Ω.carrier ∧ closure Ω.carrier ⊆ U := by
  letI : IsManifold SurfaceRealModel ∞ X :=
    complexOneManifold_has_real_smooth_structure X
  letI : SigmaCompactSpace X :=
    riemannSurface_sigmaCompactSpace X
  haveI : ParacompactSpace X := inferInstance
  haveI : NormalSpace X := inferInstance
  rcases exists_surface_open_between_and_isCompact_closure
      (X := X) (K := K) (U := U) hK hU_open hKU with
    ⟨V, hV_open, hKV, hV_closure_subset_U, hV_compact⟩
  have hK_closed : IsClosed K := hK.isClosed
  have hK_subset_interior_V : K ⊆ interior V := by
    intro x hx
    rw [hV_open.interior_eq]
    exact hKV hx
  rcases exists_contMDiffMap_one_nhds_of_subset_interior
      (I := SurfaceRealModel) (M := X) (n := (⊤ : ℕ∞)) (t := V)
      hK_closed hK_subset_interior_V with
    ⟨f, hf_one_near, hf_zero_off, hf_range⟩
  rcases smoothCutoff_regularSuperlevel_smoothBoundaryDomain_between
      hK hK_nonempty hV_open hV_compact
      (f := fun x ↦ f x) f.contMDiff
      hf_one_near hf_zero_off hf_range with
    ⟨Ω, hKΩ, hΩ_closure_subset_V⟩
  exact ⟨Ω, hKΩ, fun x hx ↦
    hV_closure_subset_U (subset_closure (hΩ_closure_subset_V hx))⟩

/--
%%handwave
name:
  Smooth regularization of compact exhaustions
statement:
  On a Riemann surface, every compact exhaustion can be thickened to
  a smooth relatively compact exhaustion.
proof:
  For each compact member \(K_n\), choose a smooth relatively compact domain
  whose closure lies inside the interior of a later compact member and which
  contains the previous chosen closure together with \(K_n\).  This is the
  standard regular-level construction: separate the compact set to be
  contained from the closed complement of the target open set by a smooth
  function and choose a regular value between them.  Inducting over \(n\)
  gives nested smooth domains with nested closures, and the original compact
  exhaustion ensures that their union is the whole surface.
-/
theorem compactExhaustion_has_smoothRelativelyCompactExhaustion
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (K : CompactExhaustion X) :
    Nonempty (SmoothRelativelyCompactExhaustion X) := by
  let p : X := Classical.choice (PathConnectedSpace.nonempty : Nonempty X)
  let N : ℕ := K.find p
  have hp_mem : p ∈ K N := by
    simpa [N] using K.mem_find p
  let L : ℕ → Set X := fun n ↦ K (N + n)
  have hL_compact : ∀ n : ℕ, IsCompact (L n) := by
    intro n
    exact K.isCompact (N + n)
  have hL_nonempty : ∀ n : ℕ, (L n).Nonempty := by
    intro n
    refine ⟨p, ?_⟩
    exact K.subset (Nat.le_add_right N n) hp_mem
  have hL_subset_interior_succ :
      ∀ n : ℕ, L n ⊆ interior (L (n + 1)) := by
    intro n
    simpa [L, Nat.add_assoc] using K.subset_interior_succ (N + n)
  choose Ω hKΩ hΩ_closure using
    fun n : ℕ ↦
      exists_smoothBoundaryDomain_between_compact_and_open
        (hL_compact n) (hL_nonempty n) isOpen_interior
        (hL_subset_interior_succ n)
  refine ⟨{
    domain := Ω
    monotone := ?_
    closure_subset_next := ?_
    exhausts := ?_
  }⟩
  · intro n x hx
    exact hKΩ (n + 1) (interior_subset (hΩ_closure n (subset_closure hx)))
  · intro n x hx
    exact hKΩ (n + 1) (interior_subset (hΩ_closure n hx))
  · intro x
    rcases K.exists_mem x with ⟨m, hxm⟩
    refine ⟨m + 1, hKΩ (m + 1) ?_⟩
    simpa [L, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      K.subset (Nat.le_add_left m (N + 1)) hxm

/--
%%handwave
name:
  Smooth exhaustions of noncompact surfaces
statement:
  Every noncompact Riemann surface admits a smooth relatively
  compact exhaustion.
proof:
  Choose a compact exhaustion of the surface.  Each compact member is thickened
  inside the interior of a later compact member by the smooth regular-level
  construction, and the resulting nested smooth relatively compact domains
  exhaust the surface.
-/
theorem connected_noncompact_has_smoothRelativelyCompactExhaustion
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (_hnoncompact : ¬ CompactSpace X) :
  Nonempty (SmoothRelativelyCompactExhaustion X) := by
  rcases riemannSurface_compactExhaustion X with ⟨K⟩
  exact compactExhaustion_has_smoothRelativelyCompactExhaustion K

namespace SmoothRelativelyCompactExhaustion

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/--
%%handwave
name:
  Monotonicity at arbitrary exhaustion indices
statement:
  In a smooth relatively compact exhaustion, an earlier domain is contained in
  every later domain.
proof:
  Iterate the successive containment in the definition of a smooth relatively
  compact exhaustion.
-/
theorem carrier_mono (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m ≤ n) : (E.domain m).carrier ⊆ (E.domain n).carrier := by
  refine Nat.le_induction ?base ?step n hmn
  · exact subset_rfl
  · intro k _hmk ih
    exact ih.trans (E.monotone k)

/--
%%handwave
name:
  Earlier closed exhaustion domains lie in strictly later domains
statement:
  If \(m<n\), then the closure of the \(m\)-th exhaustion domain is contained
  in the \(n\)-th exhaustion domain.
proof:
  The defining exhaustion property puts the closure of the \(m\)-th domain
  into the next domain.  Monotonicity then carries it to any still later
  domain.
-/
theorem closure_carrier_subset_of_lt
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m < n) :
    closure (E.domain m).carrier ⊆ (E.domain n).carrier := by
  exact (E.closure_subset_next m).trans
    (E.carrier_mono (Nat.succ_le_iff.mpr hmn))

/--
%%handwave
name:
  Earlier exhaustion boundaries lie in strictly later domains
statement:
  If \(m<n\), then the boundary of the \(m\)-th exhaustion domain is contained
  in the \(n\)-th exhaustion domain.
proof:
  The boundary is contained in the closure of the earlier domain, and that
  closure is contained in any strictly later exhaustion domain.
-/
theorem boundary_subset_carrier_of_lt
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m < n) :
    (E.domain m).boundary ⊆ (E.domain n).carrier := by
  intro x hx
  have hx_frontier : x ∈ frontier (E.domain m).carrier := by
    simpa [SmoothBoundaryDomain.boundary] using hx
  exact E.closure_carrier_subset_of_lt hmn (frontier_subset_closure hx_frontier)

/--
%%handwave
name:
  Compact sets enter a smooth exhaustion
statement:
  Every compact subset of a surface is contained in one member of a smooth
  relatively compact exhaustion.
proof:
  The exhaustion domains are open and cover the surface.  These open sets
  cover the compact set, so finitely many suffice.  Taking an index larger
  than all indices in that finite subcover gives one exhaustion domain
  containing the whole compact set.
-/
theorem compact_subset_domain
    (E : SmoothRelativelyCompactExhaustion X) {K : Set X}
    (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ (E.domain n).carrier := by
  classical
  let nOf : X → ℕ := fun x ↦ Classical.choose (E.exhausts x)
  have hnOf : ∀ x : X, x ∈ (E.domain (nOf x)).carrier := by
    intro x
    exact Classical.choose_spec (E.exhausts x)
  let U : X → Set X := fun x ↦ (E.domain (nOf x)).carrier
  have hU_open : ∀ x : X, IsOpen (U x) := by
    intro x
    exact (E.domain (nOf x)).isOpen
  have hcover : K ⊆ ⋃ x : X, U x := by
    intro x _hx
    exact Set.mem_iUnion.mpr ⟨x, hnOf x⟩
  rcases hK.elim_finite_subcover U hU_open hcover with ⟨t, ht⟩
  let N : ℕ := t.sup nOf
  refine ⟨N, ?_⟩
  intro x hxK
  have hxUnion : x ∈ ⋃ y ∈ t, U y := ht hxK
  rcases Set.mem_iUnion.mp hxUnion with ⟨y, hyUnion⟩
  rcases Set.mem_iUnion.mp hyUnion with ⟨hyt, hxy⟩
  exact E.carrier_mono (Finset.le_sup hyt) hxy

/--
%%handwave
name:
  Compact sets eventually stay inside a smooth exhaustion
statement:
  Once a compact set is contained in one exhaustion domain, monotonicity keeps
  it inside all later domains.
proof:
  Apply the compact-set containment theorem and then monotonicity of the
  exhaustion.
-/
theorem eventually_compact_subset_domain
    (E : SmoothRelativelyCompactExhaustion X) {K : Set X}
    (hK : IsCompact K) :
    ∀ᶠ n : ℕ in Filter.atTop, K ⊆ (E.domain n).carrier := by
  rcases E.compact_subset_domain hK with ⟨N, hN⟩
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  exact hN.trans (E.carrier_mono hn)

/--
%%handwave
name:
  Moving exhaustion boundaries eventually avoid compact sets
statement:
  If \(K\) is compact, then every sufficiently far exhaustion boundary is
  disjoint from \(K\).
proof:
  A compact set is eventually contained in the open exhaustion domain.  An
  open set is disjoint from its frontier, and the exhaustion boundary is that
  frontier.
-/
theorem eventually_boundary_disjoint_compact
    (E : SmoothRelativelyCompactExhaustion X) {K : Set X}
    (hK : IsCompact K) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ x ∈ (E.domain n).boundary, x ∉ K := by
  filter_upwards [E.eventually_compact_subset_domain hK] with n hK_subset x hx_boundary hxK
  have hx_carrier : x ∈ (E.domain n).carrier := hK_subset hxK
  have hx_frontier : x ∈ frontier (E.domain n).carrier := by
    simpa [SmoothBoundaryDomain.boundary] using hx_boundary
  have hx_inter :
      x ∈ (E.domain n).carrier ∩ frontier (E.domain n).carrier :=
    ⟨hx_carrier, hx_frontier⟩
  simp [(E.domain n).isOpen.inter_frontier_eq] at hx_inter

/--
%%handwave
name:
  Moving exhaustion boundary sequences escape compact sets
statement:
  A sequence whose \(n\)-th point lies on the \(n\)-th exhaustion boundary
  eventually leaves every compact set.
proof:
  Apply eventual disjointness of moving exhaustion boundaries from the fixed
  compact set to the chosen boundary point.
-/
theorem boundary_sequence_eventually_outside_compact
    (E : SmoothRelativelyCompactExhaustion X) {K : Set X}
    (hK : IsCompact K) (y : ℕ → X)
    (hy : ∀ n : ℕ, y n ∈ (E.domain n).boundary) :
    ∀ᶠ n : ℕ in Filter.atTop, y n ∉ K := by
  filter_upwards [E.eventually_boundary_disjoint_compact hK] with n hdisjoint
  exact hdisjoint (y n) (hy n)

/--
%%handwave
name:
  Moving boundary points eventually lie in selected outer domains
statement:
  If the \(n\)-th exhaustion boundary is eventually strictly inside the
  selected outer domain, then every chosen point on that boundary eventually
  belongs to the selected outer domain.
proof:
  A boundary point of an earlier exhaustion domain belongs to every strictly
  later exhaustion domain.  Apply this to the eventual strict inequality of
  the indices.
-/
theorem boundary_sequence_eventually_mem_selected_outer_carrier_of_eventually_lt
    (E : SmoothRelativelyCompactExhaustion X) {μ : ℕ → ℕ} {y : ℕ → X}
    (hμ_strict : ∀ᶠ n : ℕ in Filter.atTop, n < μ n)
    (hy : ∀ n : ℕ, y n ∈ (E.domain n).boundary) :
    ∀ᶠ n : ℕ in Filter.atTop, y n ∈ (E.domain (μ n)).carrier := by
  filter_upwards [hμ_strict] with n hn
  exact E.boundary_subset_carrier_of_lt hn (hy n)

/--
%%handwave
name:
  Escaping selected-domain points force selected indices to infinity
statement:
  Let points eventually lie in selected members of a smooth exhaustion.  If
  those points escape every compact set containing a fixed point of the
  exhaustion, then the selected exhaustion indices tend to infinity.
proof:
  Fix one exhaustion domain.  Its closure is compact and contains the fixed
  point.  Escaping points are eventually outside this compact set.  If a
  selected index were still no larger than the fixed index, monotonicity would
  put the point inside the fixed domain and hence inside its closure, a
  contradiction.
-/
theorem selected_indices_tendsto_atTop_of_eventual_domain_and_escape
    (E : SmoothRelativelyCompactExhaustion X) {p : X}
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier)
    {μ : ℕ → ℕ} {x : ℕ → X}
    (hdomain :
      ∀ᶠ j : ℕ in Filter.atTop, x j ∈ (E.domain (μ j)).carrier)
    (hescape :
      ∀ K : Set X, IsCompact K → p ∈ K →
        ∀ᶠ j : ℕ in Filter.atTop, x j ∉ K) :
    Filter.Tendsto μ Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro N
  let K : Set X := closure (E.domain N).carrier
  have hK_compact : IsCompact K := (E.domain N).compact_closure
  have hpK : p ∈ K := subset_closure (hp N)
  rcases Filter.eventually_atTop.mp
      (hdomain.and (hescape K hK_compact hpK)) with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro j hj
  rcases hM j hj with ⟨hx_domain, hx_escape⟩
  by_contra hnot
  have hμ_lt : μ j < N := Nat.lt_of_not_ge hnot
  exact hx_escape
    (subset_closure (E.carrier_mono hμ_lt.le hx_domain))

/--
%%handwave
name:
  Sequences outside matching exhaustion closures escape compact sets
statement:
  If the \(n\)-th point of a sequence lies outside the closure of the \(n\)-th
  exhaustion domain, then the sequence eventually leaves every compact set.
proof:
  A fixed compact set is eventually contained in the \(n\)-th exhaustion
  domain, hence in its closure.  This contradicts the assumed closure escape
  for all sufficiently large \(n\).
-/
theorem sequence_escaping_closures_eventually_outside_compact
    (E : SmoothRelativelyCompactExhaustion X) {K : Set X}
    (hK : IsCompact K) (x : ℕ → X)
    (hescape : ∀ n : ℕ, x n ∉ closure (E.domain n).carrier) :
    ∀ᶠ n : ℕ in Filter.atTop, x n ∉ K := by
  filter_upwards [E.eventually_compact_subset_domain hK] with n hK_subset hxK
  exact hescape n (subset_closure (hK_subset hxK))

/--
%%handwave
name:
  Complements of exhaustion domains are cocompact
statement:
  The complement of every member of a smooth relatively compact exhaustion is
  a neighborhood of infinity for the cocompact filter.
proof:
  Each exhaustion domain has compact closure.  The complement of that compact
  closure is cocompact, and it is contained in the complement of the domain.
-/
theorem compl_domain_mem_cocompact
    (E : SmoothRelativelyCompactExhaustion X) (n : ℕ) :
    (E.domain n).carrierᶜ ∈ Filter.cocompact X := by
  exact Filter.mem_of_superset
    (E.domain n).compact_closure.compl_mem_cocompact
    (by
      intro x hx hxdomain
      exact hx (subset_closure hxdomain))

/--
%%handwave
name:
  Closed exhaustion collar
statement:
  The closed collar between two members of a smooth exhaustion is the part of
  the outer domain outside the closure of the inner domain.
-/
def closedCollar (E : SmoothRelativelyCompactExhaustion X) (m n : ℕ) :
    Set X :=
  (E.domain n).carrier \ closure (E.domain m).carrier

/--
%%handwave
name:
  Closed exhaustion collars are open
statement:
  The region between the outer exhaustion domain and the closed inner
  exhaustion domain is open.
proof:
  It is the difference of the open outer domain and the closed inner closure.
-/
theorem closedCollar_isOpen
    (E : SmoothRelativelyCompactExhaustion X) (m n : ℕ) :
    IsOpen (E.closedCollar m n) := by
  exact (E.domain n).isOpen.sdiff isClosed_closure

/--
%%handwave
name:
  Closed exhaustion collars have compact closure
statement:
  The closure of an exhaustion collar is compact.
proof:
  The collar lies in the outer exhaustion domain, so its closure lies in the
  compact closure of the outer domain.
-/
theorem closedCollar_compact_closure
    (E : SmoothRelativelyCompactExhaustion X) (m n : ℕ) :
    IsCompact (closure (E.closedCollar m n)) := by
  exact (E.domain n).compact_closure.of_isClosed_subset isClosed_closure
    (closure_mono Set.diff_subset)

/--
%%handwave
name:
  Exhaustion collars lie in the outer domain
statement:
  Every point of a closed exhaustion collar belongs to its outer exhaustion
  domain.
-/
theorem closedCollar_subset_outer
    (E : SmoothRelativelyCompactExhaustion X) (m n : ℕ) :
    E.closedCollar m n ⊆ (E.domain n).carrier :=
  Set.diff_subset

/--
%%handwave
name:
  Exhaustion collars avoid points of the inner domain
statement:
  If a point lies in the inner exhaustion domain, then the closed collar
  between the inner and outer domains avoids that point.
proof:
  A point of the inner domain lies in the closure of the inner domain, while
  the collar is defined by removing that closure.
-/
theorem not_mem_closedCollar_of_mem_inner
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ} {p : X}
    (hp : p ∈ (E.domain m).carrier) :
    p ∉ E.closedCollar m n := by
  intro hp_collar
  exact hp_collar.2 (subset_closure hp)

/--
%%handwave
name:
  Exhaustion collars lie in punctured outer domains
statement:
  If the inner exhaustion domain contains the pole, then the closed collar is
  contained in the punctured outer domain.
proof:
  The collar lies in the outer domain and avoids every point of the inner
  domain, hence in particular avoids the pole.
-/
theorem closedCollar_subset_punctured_outer_of_mem_inner
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ} {p : X}
    (hp : p ∈ (E.domain m).carrier) :
    E.closedCollar m n ⊆ (E.domain n).carrier \ {p} := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro hxp
  have hxp_eq : x = p := by simpa using hxp
  have hx_closure : x ∈ closure (E.domain m).carrier := by
    rw [hxp_eq]
    exact subset_closure hp
  exact hx.2 hx_closure

/--
%%handwave
name:
  Closed exhaustion collars as Perron domains
statement:
  A nonempty closed exhaustion collar is a Perron domain.
proof:
  The collar is open and has compact closure.
-/
noncomputable def closedCollarPerronDomain
    (E : SmoothRelativelyCompactExhaustion X) (m n : ℕ)
    (hnonempty : (E.closedCollar m n).Nonempty) :
    PerronDomain X :=
  PerronDomain.ofOpenCompactClosure (E.closedCollar m n)
    (E.closedCollar_isOpen m n) hnonempty
    (E.closedCollar_compact_closure m n)

@[simp] theorem closedCollarPerronDomain_carrier
    (E : SmoothRelativelyCompactExhaustion X) (m n : ℕ)
    (hnonempty : (E.closedCollar m n).Nonempty) :
    (E.closedCollarPerronDomain m n hnonempty).carrier =
      E.closedCollar m n := by
  simp [closedCollarPerronDomain]

@[simp] theorem closedCollarPerronDomain_boundary
    (E : SmoothRelativelyCompactExhaustion X) (m n : ℕ)
    (hnonempty : (E.closedCollar m n).Nonempty) :
    (E.closedCollarPerronDomain m n hnonempty).boundary =
      frontier (E.closedCollar m n) := by
  simp [closedCollarPerronDomain]

/--
%%handwave
name:
  Frontier of an exhaustion collar lies on the two exhaustion boundaries
statement:
  Every frontier point of the closed collar between an inner and outer
  exhaustion domain lies either on the outer boundary or on the inner
  boundary.
proof:
  Write the collar as the intersection of the outer domain with the complement
  of the closed inner domain.  The frontier of an intersection is contained in
  the union of the corresponding frontiers.  The frontier of the complement is
  unchanged, and the frontier of a closure is contained in the original
  frontier.
-/
theorem frontier_closedCollar_subset_outer_boundary_or_inner_boundary
    (E : SmoothRelativelyCompactExhaustion X) (m n : ℕ) :
    frontier (E.closedCollar m n) ⊆
      (E.domain n).boundary ∪ (E.domain m).boundary := by
  intro x hx
  have hx_frontier_inter :
      x ∈ frontier
        ((E.domain n).carrier ∩ (closure (E.domain m).carrier)ᶜ) := by
    simpa [closedCollar, Set.diff_eq] using hx
  rcases
      frontier_inter_subset (E.domain n).carrier
        (closure (E.domain m).carrier)ᶜ hx_frontier_inter with
    houter | hinner
  · exact Or.inl (by
      simpa [SmoothBoundaryDomain.boundary] using houter.1)
  · have hx_inner_closure_frontier :
        x ∈ frontier (closure (E.domain m).carrier) := by
      simpa [frontier_compl] using hinner.2
    exact Or.inr (by
      simpa [SmoothBoundaryDomain.boundary] using
        frontier_closure_subset hx_inner_closure_frontier)

/--
%%handwave
name:
  Points outside an inner exhaustion domain are on its boundary or in the
  closed collar
statement:
  A point of an outer exhaustion domain that is not in the inner exhaustion
  domain either lies on the inner boundary or lies outside the closure of the
  inner domain, hence belongs to the closed collar.
proof:
  If the point lies in the closure of the inner domain, then because the inner
  domain is open and the point is not in it, the point is on the frontier.  If
  it does not lie in the closure, it is in the closed collar by definition.
-/
theorem outer_sdiff_inner_subset_inner_boundary_union_closedCollar
    (E : SmoothRelativelyCompactExhaustion X) (m n : ℕ) :
    (E.domain n).carrier \ (E.domain m).carrier ⊆
      (E.domain m).boundary ∪ E.closedCollar m n := by
  intro x hx
  by_cases hx_closure : x ∈ closure (E.domain m).carrier
  · exact Or.inl (by
      have hx_frontier : x ∈ frontier (E.domain m).carrier := by
        rw [(E.domain m).isOpen.frontier_eq]
        exact ⟨hx_closure, hx.2⟩
      simpa [SmoothBoundaryDomain.boundary] using hx_frontier)
  · exact Or.inr ⟨hx.1, hx_closure⟩

/--
%%handwave
name:
  Closure of a closed exhaustion collar lies in the closed outer domain
statement:
  The closure of the collar between two exhaustion domains lies in the closure
  of the outer domain.
proof:
  The collar is contained in the outer domain, and closure is monotone.
-/
theorem closure_closedCollar_subset_outer_closure
    (E : SmoothRelativelyCompactExhaustion X) (m n : ℕ) :
    closure (E.closedCollar m n) ⊆ closure (E.domain n).carrier :=
  closure_mono Set.diff_subset

/--
%%handwave
name:
  The pole is not in the closure of a collar outside an inner domain
statement:
  If a point lies in the inner exhaustion domain, then it is not in the
  closure of the closed collar outside that inner domain.
proof:
  The inner exhaustion domain is an open neighborhood of the point and is
  disjoint from the collar, since the collar removes the closure of the inner
  domain.
-/
theorem not_mem_closure_closedCollar_of_mem_inner
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ} {p : X}
    (hp : p ∈ (E.domain m).carrier) :
    p ∉ closure (E.closedCollar m n) := by
  intro hp_closure
  have hinner_nhds : (E.domain m).carrier ∈ 𝓝 p :=
    (E.domain m).isOpen.mem_nhds hp
  rcases mem_closure_iff_nhds.mp hp_closure
      (E.domain m).carrier hinner_nhds with
    ⟨y, hy_inner, hy_collar⟩
  exact hy_collar.2 (subset_closure hy_inner)

/--
%%handwave
name:
  Closure of a collar lies in the punctured closed outer domain
statement:
  If the inner exhaustion domain contains the pole, then the closure of the
  closed collar lies in the closure of the outer domain with the pole removed.
proof:
  The collar closure lies in the closed outer domain.  It avoids the pole
  because the inner domain is an open neighborhood of the pole disjoint from
  the collar.
-/
theorem closure_closedCollar_subset_punctured_outer_closure_of_mem_inner
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ} {p : X}
    (hp : p ∈ (E.domain m).carrier) :
    closure (E.closedCollar m n) ⊆ closure (E.domain n).carrier \ {p} := by
  intro x hx
  refine ⟨E.closure_closedCollar_subset_outer_closure m n hx, ?_⟩
  intro hxp
  have hxp_eq : x = p := by simpa using hxp
  exact (E.not_mem_closure_closedCollar_of_mem_inner (m := m) (n := n) hp)
    (by simpa [hxp_eq] using hx)

/--
%%handwave
name:
  Closed sublevels are compact when a function diverges at infinity
statement:
  If a real-valued function tends to \(+\infty\) along the cocompact filter,
  then every closed sublevel set, after adjoining one distinguished point, is
  compact.
proof:
  For a level \(a\), divergence at infinity gives a compact set outside of
  which \(u>a\).  Hence the adjoined sublevel \(\{p\}\cup\{u\le a\}\) lies in
  that compact set with \(p\) inserted.  If the adjoined sublevel is closed,
  it is a closed subset of a compact set.
-/
theorem compact_adjoined_sublevel_of_tendsto_atTop_cocompact_of_closed
    {X : Type} [TopologicalSpace X] {u : X → ℝ} {p : X} {a : ℝ}
    (hinfty : Filter.Tendsto u (Filter.cocompact X) Filter.atTop)
    (hclosed : IsClosed ({p} ∪ {x : X | u x ≤ a})) :
    IsCompact ({p} ∪ {x : X | u x ≤ a}) := by
  have hlarge : {x : X | a < u x} ∈ Filter.cocompact X :=
    hinfty.eventually_gt_atTop a
  rcases Filter.mem_cocompact.mp hlarge with ⟨K, hK_compact, hK_subset⟩
  have hsubset : {p} ∪ {x : X | u x ≤ a} ⊆ insert p K := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (by simpa using hx)
    · by_cases hxp : x = p
      · simp [hxp]
      · exact Or.inr (by
          by_contra hxK
          have hlt : a < u x := hK_subset hxK
          exact (not_lt_of_ge hx) hlt)
  exact IsCompact.of_isClosed_subset (hK_compact.insert p) hclosed hsubset

/--
%%handwave
name:
  Punctured-continuous sublevels become closed after adjoining the puncture
statement:
  If a real-valued function is continuous away from a point, then adjoining
  that point to any closed sublevel set gives a closed subset of the surface.
proof:
  The complement is the intersection of the punctured surface with the open
  superlevel set \(\{u>a\}\).  Continuity on the punctured surface makes this
  intersection open.
-/
theorem adjoined_sublevel_closed_of_continuousOn_punctured
    {X : Type} [TopologicalSpace X] [T1Space X] {u : X → ℝ} {p : X} {a : ℝ}
    (hcont : ContinuousOn u {x : X | x ≠ p}) :
    IsClosed ({p} ∪ {x : X | u x ≤ a}) := by
  rw [← isOpen_compl_iff]
  have hpunctured_open : IsOpen {x : X | x ≠ p} := by
    simpa using (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
  have hopen : IsOpen ({x : X | x ≠ p} ∩ u ⁻¹' Set.Ioi a) :=
    hcont.isOpen_inter_preimage hpunctured_open isOpen_Ioi
  convert hopen using 1
  ext x
  by_cases hxp : x = p <;> simp [hxp, not_le]

/--
%%handwave
name:
  Punctured-continuous divergent functions have compact adjoined sublevels
statement:
  If a real-valued function is continuous away from a point and tends to
  \(+\infty\) at infinity, then every sublevel set becomes compact after
  adjoining that point.
proof:
  Divergence at infinity traps each sublevel in a compact set up to the
  adjoined point.  Punctured continuity makes the adjoined sublevel closed,
  so it is compact as a closed subset of that compact trap.
-/
theorem compact_adjoined_sublevel_of_tendsto_atTop_cocompact_of_continuousOn_punctured
    {X : Type} [TopologicalSpace X] [T1Space X] {u : X → ℝ} {p : X} {a : ℝ}
    (hinfty : Filter.Tendsto u (Filter.cocompact X) Filter.atTop)
    (hcont : ContinuousOn u {x : X | x ≠ p}) :
    IsCompact ({p} ∪ {x : X | u x ≤ a}) :=
  compact_adjoined_sublevel_of_tendsto_atTop_cocompact_of_closed
    hinfty (adjoined_sublevel_closed_of_continuousOn_punctured hcont)

/--
%%handwave
name:
  Harmonic divergent functions have compact adjoined sublevels
statement:
  If a function is harmonic off a point and tends to \(+\infty\) at infinity,
  then every sublevel set becomes compact after adjoining the point.
proof:
  Harmonicity gives continuity on the punctured surface.  The compactness
  conclusion then follows from divergence at infinity and the
  punctured-continuity compactness theorem.
-/
theorem compact_adjoined_sublevel_of_tendsto_atTop_cocompact_of_harmonicOn_punctured
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T1Space X]
    {u : X → ℝ} {p : X} {a : ℝ}
    (hinfty : Filter.Tendsto u (Filter.cocompact X) Filter.atTop)
    (hharm : IsHarmonicOnSurface {x : X | x ≠ p} u) :
    IsCompact ({p} ∪ {x : X | u x ≤ a}) := by
  have hpunctured_open : IsOpen {x : X | x ≠ p} := by
    simpa using (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
  exact
    compact_adjoined_sublevel_of_tendsto_atTop_cocompact_of_continuousOn_punctured
      hinfty (harmonicOnSurface_continuousOn hpunctured_open hharm)

/--
%%handwave
name:
  Punctured-continuous superlevels become closed after adjoining the puncture
statement:
  If a real-valued function is continuous away from a point, then adjoining
  that point to any closed superlevel set gives a closed subset of the
  surface.
proof:
  The complement is the intersection of the punctured surface with the open
  sublevel set \(\{u<a\}\).  Continuity on the punctured surface makes this
  intersection open.
-/
theorem adjoined_superlevel_closed_of_continuousOn_punctured
    {X : Type} [TopologicalSpace X] [T1Space X] {u : X → ℝ} {p : X} {a : ℝ}
    (hcont : ContinuousOn u {x : X | x ≠ p}) :
    IsClosed ({p} ∪ {x : X | a ≤ u x}) := by
  rw [← isOpen_compl_iff]
  have hpunctured_open : IsOpen {x : X | x ≠ p} := by
    simpa using (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
  have hopen : IsOpen ({x : X | x ≠ p} ∩ u ⁻¹' Set.Iio a) :=
    hcont.isOpen_inter_preimage hpunctured_open isOpen_Iio
  convert hopen using 1
  ext x
  by_cases hxp : x = p <;> simp [hxp, not_le]

/--
%%handwave
name:
  Punctured-continuous functions vanishing at infinity have compact positive
  superlevels
statement:
  If a real-valued function is continuous away from a point and tends to zero
  at infinity, then every positive superlevel set becomes compact after
  adjoining that point.
proof:
  For a positive level \(a\), convergence to zero makes \(u<a\) outside a
  compact set.  Thus \(\{u\ge a\}\), up to the adjoined point, lies in that
  compact set.  Punctured continuity makes the adjoined superlevel closed.
-/
theorem compact_adjoined_superlevel_of_tendsto_zero_cocompact_of_continuousOn_punctured
    {X : Type} [TopologicalSpace X] [T1Space X] {u : X → ℝ} {p : X} {a : ℝ}
    (ha : 0 < a)
    (hzero : Filter.Tendsto u (Filter.cocompact X) (𝓝 0))
    (hcont : ContinuousOn u {x : X | x ≠ p}) :
    IsCompact ({p} ∪ {x : X | a ≤ u x}) := by
  have hsmall : {x : X | u x < a} ∈ Filter.cocompact X :=
    hzero (isOpen_Iio.mem_nhds ha)
  rcases Filter.mem_cocompact.mp hsmall with ⟨K, hK_compact, hK_subset⟩
  have hclosed : IsClosed ({p} ∪ {x : X | a ≤ u x}) :=
    adjoined_superlevel_closed_of_continuousOn_punctured hcont
  have hsubset : {p} ∪ {x : X | a ≤ u x} ⊆ insert p K := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (by simpa using hx)
    · by_cases hxp : x = p
      · simp [hxp]
      · exact Or.inr (by
          by_contra hxK
          have hlt : u x < a := hK_subset hxK
          exact (not_lt_of_ge hx) hlt)
  exact IsCompact.of_isClosed_subset (hK_compact.insert p) hclosed hsubset

/--
%%handwave
name:
  Harmonic functions vanishing at infinity have compact positive superlevels
statement:
  If a function is harmonic off a point and tends to zero at infinity, then
  every positive superlevel set becomes compact after adjoining the point.
proof:
  Harmonicity gives continuity on the punctured surface.  The compactness
  conclusion then follows from vanishing at infinity and the
  punctured-continuity compactness theorem.
-/
theorem compact_adjoined_superlevel_of_tendsto_zero_cocompact_of_harmonicOn_punctured
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T1Space X]
    {u : X → ℝ} {p : X} {a : ℝ}
    (ha : 0 < a)
    (hzero : Filter.Tendsto u (Filter.cocompact X) (𝓝 0))
    (hharm : IsHarmonicOnSurface {x : X | x ≠ p} u) :
    IsCompact ({p} ∪ {x : X | a ≤ u x}) := by
  have hpunctured_open : IsOpen {x : X | x ≠ p} := by
    simpa using (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
  exact
    compact_adjoined_superlevel_of_tendsto_zero_cocompact_of_continuousOn_punctured
      ha hzero (harmonicOnSurface_continuousOn hpunctured_open hharm)

/--
%%handwave
name:
  Tail of a smooth exhaustion
statement:
  Dropping finitely many initial domains from a smooth relatively compact
  exhaustion gives another smooth relatively compact exhaustion.
proof:
  The shifted sequence inherits the successive containment and closure
  containment from the original sequence.  It still exhausts the surface
  because any point that appears in an earlier original domain also appears in
  a sufficiently later shifted domain.
-/
noncomputable def shift (E : SmoothRelativelyCompactExhaustion X) (N : ℕ) :
    SmoothRelativelyCompactExhaustion X where
  domain n := E.domain (N + n)
  monotone := by
    intro n
    simpa [Nat.add_assoc] using E.monotone (N + n)
  closure_subset_next := by
    intro n
    simpa [Nat.add_assoc] using E.closure_subset_next (N + n)
  exhausts := by
    intro x
    rcases E.exhausts x with ⟨m, hxm⟩
    refine ⟨m, ?_⟩
    exact E.carrier_mono (Nat.le_add_left m N) hxm

@[simp] theorem shift_domain
    (E : SmoothRelativelyCompactExhaustion X) (N n : ℕ) :
    (E.shift N).domain n = E.domain (N + n) :=
  rfl

/--
%%handwave
name:
  Subsequence of a smooth exhaustion
statement:
  Passing to a strictly increasing sequence of indices in a smooth relatively
  compact exhaustion again gives a smooth relatively compact exhaustion.
proof:
  Successive closure containment is preserved because a strictly increasing
  index sequence advances by at least one at each step.  The resulting domains
  still cover the surface since the selected indices tend to infinity.
-/
noncomputable def compStrictMono (E : SmoothRelativelyCompactExhaustion X)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    SmoothRelativelyCompactExhaustion X where
  domain n := E.domain (φ n)
  monotone := by
    intro n
    exact E.carrier_mono (le_of_lt (hφ (Nat.lt_succ_self n)))
  closure_subset_next := by
    intro n x hx
    have hsucc_le : φ n + 1 ≤ φ (n + 1) :=
      Nat.succ_le_of_lt (hφ (Nat.lt_succ_self n))
    exact E.carrier_mono hsucc_le (E.closure_subset_next (φ n) hx)
  exhausts := by
    intro x
    rcases E.exhausts x with ⟨m, hxm⟩
    have hφ_ge : ∀ᶠ n : ℕ in Filter.atTop, m ≤ φ n :=
      hφ.tendsto_atTop.eventually (Filter.eventually_ge_atTop m)
    rcases Filter.eventually_atTop.mp hφ_ge with ⟨N, hN⟩
    exact ⟨N, E.carrier_mono (hN N le_rfl) hxm⟩

@[simp] theorem compStrictMono_domain
    (E : SmoothRelativelyCompactExhaustion X) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (n : ℕ) :
    (E.compStrictMono φ hφ).domain n = E.domain (φ n) :=
  rfl

end SmoothRelativelyCompactExhaustion

/--
%%handwave
name:
  Exterior smallness is vanishing at infinity
statement:
  If every positive tolerance has a compact exceptional set outside of which
  a real-valued function is within that tolerance of zero, then the function
  tends to zero along the ends of the space.
proof:
  This is the metric-neighborhood definition of convergence to zero, with
  complements of compact sets as the neighborhoods of infinity.
-/
theorem tendsto_zero_at_cocompact_of_compact_exterior_small
    {X : Type} [TopologicalSpace X] {f : X → ℝ}
    (hsmall :
      ∀ ε : ℝ, 0 < ε →
        ∃ K : Set X, IsCompact K ∧ ∀ x : X, x ∉ K → dist (f x) 0 < ε) :
    Filter.Tendsto f (Filter.cocompact X) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rcases hsmall ε hε with ⟨K, hK_compact, hK_small⟩
  exact Filter.mem_of_superset hK_compact.compl_mem_cocompact hK_small

/--
%%handwave
name:
  Exterior lower bounds give divergence to infinity
statement:
  If every real lower bound holds outside some compact subset, then a
  real-valued function tends to \(+\infty\) along the ends of the space.
proof:
  A neighborhood of \(+\infty\) contains an upper ray.  The assumed compact
  exceptional set for the endpoint of that ray gives the required cocompact
  neighborhood.
-/
theorem tendsto_atTop_at_cocompact_of_compact_exterior_large
    {X : Type} [TopologicalSpace X] {f : X → ℝ}
    (hlarge :
      ∀ A : ℝ, ∃ K : Set X, IsCompact K ∧ ∀ x : X, x ∉ K → A ≤ f x) :
    Filter.Tendsto f (Filter.cocompact X) Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro A
  rcases hlarge A with ⟨K, hK_compact, hK_large⟩
  exact Filter.mem_of_superset hK_compact.compl_mem_cocompact hK_large

/--
%%handwave
name:
  Uniform absolute bounds pass to pointwise limits
statement:
  If real-valued functions converge uniformly on a set and, at a point of the
  set, their translates are eventually bounded in absolute value by a fixed
  constant, then the translated limiting value obeys the same bound.
proof:
  Uniform convergence gives ordinary convergence at the point.  Adding a
  constant and taking absolute values preserve convergence, and the closed
  interval \((-\infty,M]\) contains the eventual values, so it contains the
  limit.
-/
theorem tendstoUniformlyOn_pointwise_norm_add_const_le_of_eventually
    {ι X : Type} {l : Filter ι} [l.NeBot]
    {K : Set X} {F : ι → X → ℝ} {f : X → ℝ}
    {x : X} (hx : x ∈ K) {c M : ℝ}
    (hconv : TendstoUniformlyOn F f l K)
    (hbound : ∀ᶠ i in l, ‖F i x + c‖ ≤ M) :
    ‖f x + c‖ ≤ M := by
  have htend :
      Filter.Tendsto (fun i : ι ↦ F i x + c) l (𝓝 (f x + c)) :=
    (hconv.tendsto_at hx).add tendsto_const_nhds
  exact le_of_tendsto htend.norm hbound

/--
%%handwave
name:
  Noncompact surfaces have a distinct base point
statement:
  A noncompact topological space has at least two points.
proof:
  If the space had at most one point, it would be finite, hence compact.
-/
theorem noncompactSpace_nontrivial
    (X : Type) [TopologicalSpace X] (hnoncompact : ¬ CompactSpace X) :
    Nontrivial X := by
  by_contra hnontrivial
  haveI : Subsingleton X := not_nontrivial_iff_subsingleton.mp hnontrivial
  haveI : Finite X := Finite.of_subsingleton
  exact hnoncompact (by infer_instance)

/--
%%handwave
name:
  The complement of a closed coordinate disk has smooth boundary
statement:
  The complement of a closed coordinate disk has smooth boundary, with local
  defining function \(R^2-\lVert z-c\rVert^2\) in the disk coordinate.
proof:
  A boundary point of the complement is a boundary point of the closed disk.
  In the defining coordinate chart, the disk is locally the Euclidean closed
  ball.  The squared-radius function is smooth, has nonzero differential on
  the circle because the radius is positive, is negative outside the closed
  ball, and vanishes exactly on the circle.
-/
theorem ClosedCoordinateDisk.compl_hasSmoothBoundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (D : ClosedCoordinateDisk X) :
    HasSmoothBoundary D.carrierᶜ := by
  intro x hx_frontier_compl
  let e : OpenPartialHomeomorph X ℂ := D.openDisk.chart
  let c : ℂ := D.openDisk.center
  let R : ℝ := D.closedRadius
  let r : ℂ → ℝ := fun z ↦ R ^ 2 - ‖z - c‖ ^ 2
  have hx_frontier : x ∈ frontier D.carrier := by
    simpa [frontier_compl] using hx_frontier_compl
  have hxD : x ∈ D.carrier :=
    (ClosedCoordinateDisk.isClosed D).frontier_subset hx_frontier
  have hxD' :
      x ∈ e.source ∩ e ⁻¹' Metric.closedBall c R := by
    simpa [e, c, R, D.carrier_eq] using hxD
  have hx_source : x ∈ e.source := hxD'.1
  have hdist_le : dist (e x) c ≤ R := by
    simpa [Metric.mem_closedBall] using hxD'.2
  have hnot_lt : ¬ dist (e x) c < R := by
    intro hlt
    have hx_open : x ∈ D.expandedOpenDisk R := by
      rw [ClosedCoordinateDisk.expandedOpenDisk]
      exact ⟨hx_source, by simpa [e, c, R, Metric.mem_ball] using hlt⟩
    have hopen : IsOpen (D.expandedOpenDisk R) :=
      D.expandedOpenDisk_isOpen R
    have hsubset : D.expandedOpenDisk R ⊆ D.carrier := by
      intro y hy
      rw [ClosedCoordinateDisk.expandedOpenDisk] at hy
      rw [D.carrier_eq]
      exact ⟨hy.1, by simpa [R] using Metric.ball_subset_closedBall hy.2⟩
    have hx_not_interior : x ∉ interior D.carrier :=
      (mem_frontier_iff_notMem_interior hxD).mp hx_frontier
    exact hx_not_interior ((interior_maximal hsubset hopen) hx_open)
  have hdist_eq : dist (e x) c = R :=
    le_antisymm hdist_le (le_of_not_gt hnot_lt)
  have hnorm_eq : ‖e x - c‖ = R := by
    simpa [dist_eq_norm] using hdist_eq
  have hr_smooth : ContDiffOnNhdAt r (e x) := by
    have hshift : ContDiff ℝ ∞ (fun z : ℂ ↦ z - c) :=
      contDiff_id.sub contDiff_const
    refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    simpa [r] using (contDiff_const.sub (hshift.norm_sq ℝ)).contDiffOn
  let v : ℂ := e x - c
  let dr : ℂ →L[ℝ] ℝ := -(2 • (((innerSL ℝ) v).comp (1 : ℂ →L[ℝ] ℂ)))
  have hshift_deriv :
      HasFDerivAt (fun z : ℂ ↦ z - c) (1 : ℂ →L[ℝ] ℂ) (e x) := by
    simpa using
      ((hasFDerivAt_id (𝕜 := ℝ) (E := ℂ) (e x)).sub_const c)
  have hr_deriv : HasFDerivAt r dr (e x) := by
    have hnorm_deriv := hshift_deriv.norm_sq
    simpa [r, dr, v] using hnorm_deriv.const_sub (R ^ 2)
  have hdr_ne : dr ≠ 0 := by
    intro hdr_zero
    have hz : dr v = 0 := by
      simp [hdr_zero]
    have hcalc : dr v = -(2 * ‖v‖ ^ 2) := by
      simp only [dr, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
      rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
      ring
    have hzero : -(2 * R ^ 2) = 0 := by
      simpa [hcalc, v, hnorm_eq] using hz
    have hRpos : 0 < R := by
      simpa [R] using D.closedRadius_pos
    have hpos : 0 < 2 * R ^ 2 := by
      nlinarith [sq_pos_of_pos hRpos]
    nlinarith
  have hsource_nhds : ∀ᶠ y in 𝓝 x, y ∈ e.source :=
    e.open_source.mem_nhds hx_source
  have hmem_event :
      ∀ᶠ y in 𝓝 x, (y ∈ D.carrierᶜ ↔ r (e y) < 0) := by
    filter_upwards [hsource_nhds] with y hy_source
    constructor
    · intro hy_notD
      have hnot_le : ¬ dist (e y) c ≤ R := by
        intro hle
        apply hy_notD
        rw [D.carrier_eq]
        exact ⟨hy_source, by simpa [e, c, R, Metric.mem_closedBall] using hle⟩
      have hlt : R < dist (e y) c := lt_of_not_ge hnot_le
      have hnorm_lt : R < ‖e y - c‖ := by
        simpa [dist_eq_norm] using hlt
      have hsq_lt : R ^ 2 < ‖e y - c‖ ^ 2 :=
        (sq_lt_sq₀ D.closedRadius_pos.le (norm_nonneg _)).mpr (by simpa [R] using hnorm_lt)
      simp [r]
      nlinarith
    · intro hrneg hyD
      have hdist_y : dist (e y) c ≤ R := by
        rw [D.carrier_eq] at hyD
        simpa [e, c, R, Metric.mem_closedBall] using hyD.2
      have hnorm_le : ‖e y - c‖ ≤ R := by
        simpa [dist_eq_norm] using hdist_y
      have hsq_le : ‖e y - c‖ ^ 2 ≤ R ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) D.closedRadius_pos.le).mpr (by simpa [R] using hnorm_le)
      simp [r] at hrneg
      nlinarith
  have hcarrier_local :
      D.carrier ∩ e.source = (e ⁻¹' Metric.closedBall c R) ∩ e.source := by
    ext y
    simp [D.carrier_eq, e, c, R, and_assoc]
  have hcarrier_frontier :
      ∀ᶠ y in 𝓝 x,
        (y ∈ frontier D.carrier ↔ y ∈ frontier (e ⁻¹' Metric.closedBall c R)) :=
    eventually_frontier_congr_of_inter_eq e.open_source hx_source hcarrier_local
  have hchart_frontier :
      ∀ᶠ y in 𝓝 x,
        (y ∈ frontier (e ⁻¹' Metric.closedBall c R) ↔
          e y ∈ frontier (Metric.closedBall c R)) := by
    filter_upwards [hsource_nhds] with y hy_source
    have hmem :=
      congrArg (fun A : Set X => y ∈ A)
        (e.preimage_frontier (Metric.closedBall c R))
    have hiff :
        e y ∈ frontier (Metric.closedBall c R) ↔
          y ∈ frontier (e ⁻¹' Metric.closedBall c R) := by
      simpa [hy_source] using hmem
    exact hiff.symm
  have hclosed_frontier :
      ∀ z : ℂ, z ∈ frontier (Metric.closedBall c R) ↔ r z = 0 := by
    intro z
    rw [frontier_closedBall c (by simpa [R] using D.closedRadius_pos.ne')]
    constructor
    · intro hz
      have hnorm : ‖z - c‖ = R := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      simp [r, hnorm]
    · intro hz
      have hsq : ‖z - c‖ ^ 2 = R ^ 2 := by
        simp [r] at hz
        nlinarith
      have hnorm : ‖z - c‖ = R :=
        (sq_eq_sq₀ (norm_nonneg _) D.closedRadius_pos.le).mp (by simpa [R] using hsq)
      simp [hnorm]
  have hfrontier_event :
      ∀ᶠ y in 𝓝 x, (y ∈ frontier D.carrierᶜ ↔ r (e y) = 0) := by
    filter_upwards [hcarrier_frontier, hchart_frontier] with y hy_carrier hy_chart
    have hcompl : y ∈ frontier D.carrierᶜ ↔ y ∈ frontier D.carrier := by
      rw [frontier_compl]
    exact hcompl.trans (hy_carrier.trans (hy_chart.trans (hclosed_frontier (e y))))
  refine ⟨e, ?_, ?_⟩
  · exact D.openDisk.chart_mem_atlas
  · refine ⟨hx_source, r, ?_, ?_⟩
    · exact hr_smooth
    · refine ⟨dr, hr_deriv, hdr_ne, ?_⟩
      filter_upwards [hsource_nhds, hmem_event, hfrontier_event] with
        y hy_source hy_mem hy_frontier
      exact ⟨hy_source, hy_mem, hy_frontier⟩

/--
%%handwave
name:
  Smooth boundary after deleting a closed disk
statement:
  If a closed coordinate disk is contained in a smooth boundary domain, then
  the complement of that disk inside the domain has smooth boundary.
proof:
  Near the original boundary, use the original smooth defining functions.
  Near the new inner boundary, use the radial coordinate defining the
  coordinate circle.  The two boundary pieces are disjoint because the closed
  disk is compactly contained in the open domain.
-/
theorem smoothBoundaryDomain_sdiff_closedCoordinateDisk_hasSmoothBoundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier) :
    HasSmoothBoundary (Ω.carrier \ D.carrier) := by
  intro x hx_frontier
  have hx_frontier_inter :
      x ∈ frontier (Ω.carrier ∩ D.carrierᶜ) := by
    simpa [Set.diff_eq] using hx_frontier
  rcases frontier_inter_subset Ω.carrier D.carrierᶜ hx_frontier_inter with hxΩ | hxDcompl
  · have hxΩ_frontier : x ∈ frontier Ω.carrier := hxΩ.1
    have hx_notD : x ∉ D.carrier := by
      intro hxD
      have hx_empty : x ∈ Ω.carrier ∩ frontier Ω.carrier :=
        ⟨hD_subset hxD, hxΩ_frontier⟩
      simp [Ω.isOpen.inter_frontier_eq] at hx_empty
    have hDcompl_event : ∀ᶠ y in 𝓝 x, y ∈ D.carrierᶜ :=
      (ClosedCoordinateDisk.isClosed D).isOpen_compl.mem_nhds hx_notD
    have hmem :
        ∀ᶠ y in 𝓝 x,
          (y ∈ Ω.carrier \ D.carrier ↔ y ∈ Ω.carrier) := by
      filter_upwards [hDcompl_event] with y hy_notD
      simp [Set.diff_eq, hy_notD]
    have hlocal_eq :
        (Ω.carrier \ D.carrier) ∩ D.carrierᶜ =
          Ω.carrier ∩ D.carrierᶜ := by
      ext y
      simp [Set.diff_eq]
    have hfrontier :
        ∀ᶠ y in 𝓝 x,
          (y ∈ frontier (Ω.carrier \ D.carrier) ↔
            y ∈ frontier Ω.carrier) :=
      eventually_frontier_congr_of_inter_eq
        (ClosedCoordinateDisk.isClosed D).isOpen_compl hx_notD hlocal_eq
    exact hasSmoothBoundary_localData_of_eventuallyEq
      Ω.smooth_boundary hxΩ_frontier hmem hfrontier
  · have hxDcompl_frontier : x ∈ frontier D.carrierᶜ := hxDcompl.2
    have hxD_frontier : x ∈ frontier D.carrier := by
      simpa [frontier_compl] using hxDcompl_frontier
    have hxD : x ∈ D.carrier :=
      (ClosedCoordinateDisk.isClosed D).frontier_subset hxD_frontier
    have hxΩ : x ∈ Ω.carrier := hD_subset hxD
    have hΩ_event : ∀ᶠ y in 𝓝 x, y ∈ Ω.carrier :=
      Ω.isOpen.mem_nhds hxΩ
    have hmem :
        ∀ᶠ y in 𝓝 x,
          (y ∈ Ω.carrier \ D.carrier ↔ y ∈ D.carrierᶜ) := by
      filter_upwards [hΩ_event] with y hyΩ
      simp [Set.diff_eq, hyΩ]
    have hlocal_eq :
        (Ω.carrier \ D.carrier) ∩ Ω.carrier =
          D.carrierᶜ ∩ Ω.carrier := by
      ext y
      simp [Set.diff_eq, and_assoc]
    have hfrontier :
        ∀ᶠ y in 𝓝 x,
          (y ∈ frontier (Ω.carrier \ D.carrier) ↔
            y ∈ frontier D.carrierᶜ) :=
      eventually_frontier_congr_of_inter_eq Ω.isOpen hxΩ hlocal_eq
    exact hasSmoothBoundary_localData_of_eventuallyEq
      (D.compl_hasSmoothBoundary) hxDcompl_frontier hmem hfrontier

/--
%%handwave
name:
  Smooth annulus inside a smooth domain
statement:
  If a closed coordinate disk lies inside a smooth boundary domain and its
  complement in the domain is nonempty, then deleting the closed disk gives
  another smooth boundary domain.
proof:
  The new domain is the old smooth domain with one compact coordinate disk
  removed.  Its boundary is the union of the old smooth boundary and the
  coordinate circle; these two pieces are disjoint because the closed disk
  lies inside the original domain.
-/
  noncomputable def smoothBoundaryDomainRemoveClosedCoordinateDisk
      {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
      (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
      (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty) :
    SmoothBoundaryDomain X where
  carrier := Ω.carrier \ D.carrier
  isOpen := by
    exact Ω.isOpen.sdiff (ClosedCoordinateDisk.isClosed D)
  nonempty := hnonempty
  compact_closure := by
    exact Ω.compact_closure.of_isClosed_subset isClosed_closure
      (closure_mono Set.diff_subset)
  smooth_boundary := by
    exact smoothBoundaryDomain_sdiff_closedCoordinateDisk_hasSmoothBoundary
      Ω D hD_subset

@[simp] theorem smoothBoundaryDomainRemoveClosedCoordinateDisk_carrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty) :
    (smoothBoundaryDomainRemoveClosedCoordinateDisk Ω D hD_subset hnonempty).carrier =
      Ω.carrier \ D.carrier := rfl

/--
%%handwave
name:
  Annular Perron domain
statement:
  The annulus obtained by deleting a closed coordinate disk from a smooth
  boundary domain is a Perron domain.
-/
  noncomputable def annularPerronDomain
      {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
      (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
      (_hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty) :
    PerronDomain X where
  carrier := Ω.carrier \ D.carrier
  isOpen := by
    exact Ω.isOpen.sdiff (ClosedCoordinateDisk.isClosed D)
  nonempty := hnonempty
  compact_closure := by
    exact Ω.compact_closure.of_isClosed_subset isClosed_closure
      (closure_mono Set.diff_subset)

@[simp] theorem annularPerronDomain_carrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty) :
    (annularPerronDomain Ω D hD_subset hnonempty).carrier =
      Ω.carrier \ D.carrier := rfl

/--
%%handwave
name:
  Open relatively compact proper regions have componentwise geometry
statement:
  In a Riemann surface, every open relatively compact proper region
  has the componentwise maximum-principle geometry.
proof:
  Around each point take the connected component of the region.  Local
  connectedness makes this component open, its closure is compact because the
  whole region has compact closure, and its frontier is nonempty because a
  nonempty proper clopen subset of a connected space cannot be the whole
  surface.  Boundary points of the component are boundary points of the
  original open region.
-/
theorem hasComponentwiseMaximumPrincipleGeometry_of_open_compactClosure_ne_univ
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {U : Set X}
    (hU_open : IsOpen U) (hU_compact : IsCompact (closure U))
    (hU_ne_univ : U ≠ Set.univ) :
    HasComponentwiseMaximumPrincipleGeometry U := by
  intro x hxU
  let C : Set X := connectedComponentIn U x
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hxC : x ∈ C := by
    dsimp [C]
    exact mem_connectedComponentIn hxU
  have hC_open : IsOpen C := by
    dsimp [C]
    exact hU_open.connectedComponentIn
  have hC_preconnected : IsPreconnected C := by
    dsimp [C]
    exact isPreconnected_connectedComponentIn
  have hC_subsetU : C ⊆ U := by
    dsimp [C]
    exact connectedComponentIn_subset U x
  have hC_compact : IsCompact (closure C) :=
    hU_compact.of_isClosed_subset isClosed_closure (closure_mono hC_subsetU)
  have hC_ne_univ : C ≠ Set.univ := by
    intro hC_univ
    exact hU_ne_univ (Set.eq_univ_of_univ_subset (by
      intro y _hy
      exact hC_subsetU (by simp [hC_univ])))
  have hC_frontier_nonempty : (frontier C).Nonempty := by
    have hC_nonempty : C.Nonempty := ⟨x, hxC⟩
    exact (nonempty_frontier_iff).2 ⟨hC_nonempty, hC_ne_univ⟩
  have hC_frontier_subset : frontier C ⊆ frontier U := by
    intro y hy
    have hy_closureU : y ∈ closure U :=
      closure_mono hC_subsetU (frontier_subset_closure hy)
    have hy_notU : y ∉ U := by
      intro hyU
      have hyC : y ∈ C :=
        mem_connectedComponentIn_of_mem_closure_of_mem hxU hyU
          (frontier_subset_closure hy)
      have hy_inter : y ∈ C ∩ frontier C := ⟨hyC, hy⟩
      rw [hC_open.inter_frontier_eq] at hy_inter
      exact hy_inter
    rw [frontier, hU_open.interior_eq]
    exact ⟨hy_closureU, hy_notU⟩
  exact ⟨C, hxC, hC_open, hC_preconnected, hC_subsetU,
    hC_compact, hC_frontier_nonempty, hC_frontier_subset⟩

/--
%%handwave
name:
  Coordinate balls with compact image closure have compact surface closure
statement:
  Let a coordinate chart contain a closed Euclidean ball in its target.  Then
  the surface preimage of the corresponding open Euclidean ball has compact
  closure.
proof:
  The preimage of the closed Euclidean ball is the image of that compact ball
  under the inverse coordinate map, hence compact.  It is closed in the
  Hausdorff surface and contains the open coordinate ball, so it contains the
  closure of the open coordinate ball.
-/
theorem openPartialHomeomorph_coordinateBall_compact_closure
    {X : Type} [TopologicalSpace X] [T2Space X]
    (e : OpenPartialHomeomorph X ℂ) {c : ℂ} {R : ℝ}
    (hclosed_target : Metric.closedBall c R ⊆ e.target) :
    IsCompact (closure (e.source ∩ e ⁻¹' Metric.ball c R)) := by
  let K : Set X := e.source ∩ e ⁻¹' Metric.closedBall c R
  have hK_compact : IsCompact K := by
    change IsCompact (e.source ∩ e ⁻¹' Metric.closedBall c R)
    rw [← e.symm_image_eq_source_inter_preimage hclosed_target]
    exact (isCompact_closedBall c R).image_of_continuousOn
      (e.continuousOn_symm.mono hclosed_target)
  have hU_subset_K :
      e.source ∩ e ⁻¹' Metric.ball c R ⊆ K := by
    intro x hx
    exact ⟨hx.1, Metric.ball_subset_closedBall hx.2⟩
  have hclosure_subset_K :
      closure (e.source ∩ e ⁻¹' Metric.ball c R) ⊆ K :=
    closure_minimal hU_subset_K hK_compact.isClosed
  exact hK_compact.of_isClosed_subset isClosed_closure hclosure_subset_K

/--
%%handwave
name:
  Closure of a compactly contained coordinate ball stays in the closed
  coordinate ball
statement:
  If a closed Euclidean ball lies in a coordinate target, then the closure of
  the corresponding surface open coordinate ball lies in the chart source and
  maps into that closed Euclidean ball.
proof:
  The surface preimage of the closed Euclidean ball is compact, hence closed,
  and it contains the open coordinate ball.  Therefore it contains the
  closure of the open coordinate ball.
-/
theorem openPartialHomeomorph_coordinateBall_closure_subset_source_inter_closedBall
    {X : Type} [TopologicalSpace X] [T2Space X]
    (e : OpenPartialHomeomorph X ℂ) {c : ℂ} {R : ℝ}
    (hclosed_target : Metric.closedBall c R ⊆ e.target) :
    closure (e.source ∩ e ⁻¹' Metric.ball c R) ⊆
      e.source ∩ e ⁻¹' Metric.closedBall c R := by
  let K : Set X := e.source ∩ e ⁻¹' Metric.closedBall c R
  have hK_compact : IsCompact K := by
    change IsCompact (e.source ∩ e ⁻¹' Metric.closedBall c R)
    rw [← e.symm_image_eq_source_inter_preimage hclosed_target]
    exact (isCompact_closedBall c R).image_of_continuousOn
      (e.continuousOn_symm.mono hclosed_target)
  have hU_subset_K :
      e.source ∩ e ⁻¹' Metric.ball c R ⊆ K := by
    intro x hx
    exact ⟨hx.1, Metric.ball_subset_closedBall hx.2⟩
  exact closure_minimal hU_subset_K hK_compact.isClosed

/--
%%handwave
name:
  Harmonic absolute boundary bounds propagate componentwise
statement:
  On an open region with componentwise maximum-principle geometry, a harmonic
  function that is continuous on the closed region and whose absolute value is
  bounded by \(M\) on the frontier has absolute value bounded by \(M\)
  throughout the region.
proof:
  Apply the componentwise maximum principle to \(f-M\) and to \(-f-M\).  The
  two resulting inequalities are equivalent to \(-M\le f\le M\), hence to the
  asserted absolute-value bound.
-/
theorem harmonicOnSurface_norm_le_of_frontier_norm_le_componentwise
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {U : Set X} {f : X → ℝ} {M : ℝ}
    (hU_geometry : HasComponentwiseMaximumPrincipleGeometry U)
    (hf_harmonic : IsHarmonicOnSurface U f)
    (hf_continuous : ContinuousOn f (closure U))
    (hfrontier : ∀ x ∈ frontier U, ‖f x‖ ≤ M) :
    ∀ x ∈ U, ‖f x‖ ≤ M := by
  have hupper_harmonic :
      IsHarmonicOnSurface U (fun x : X ↦ f x - M) :=
    harmonicOnSurface_sub hf_harmonic (harmonicOnSurface_const U M)
  have hupper_continuous :
      ContinuousOn (fun x : X ↦ f x - M) (closure U) :=
    hf_continuous.sub continuousOn_const
  have hupper_boundary :
      ∀ x ∈ frontier U, f x - M ≤ 0 := by
    intro x hx
    have hx_abs : |f x| ≤ M := by
      simpa [Real.norm_eq_abs] using hfrontier x hx
    exact sub_nonpos.mpr (abs_le.mp hx_abs).2
  have hupper :
      ∀ x ∈ U, f x - M ≤ 0 :=
    harmonic_nonpositive_of_boundary_nonpositive_componentwise
      hU_geometry hupper_harmonic hupper_continuous hupper_boundary
  have hlower_harmonic :
      IsHarmonicOnSurface U (fun x : X ↦ -f x - M) :=
    harmonicOnSurface_sub (harmonicOnSurface_neg hf_harmonic)
      (harmonicOnSurface_const U M)
  have hlower_continuous :
      ContinuousOn (fun x : X ↦ -f x - M) (closure U) :=
    hf_continuous.neg.sub continuousOn_const
  have hlower_boundary :
      ∀ x ∈ frontier U, -f x - M ≤ 0 := by
    intro x hx
    have hx_abs : |f x| ≤ M := by
      simpa [Real.norm_eq_abs] using hfrontier x hx
    have hx_ge : -M ≤ f x := (abs_le.mp hx_abs).1
    linarith
  have hlower :
      ∀ x ∈ U, -f x - M ≤ 0 :=
    harmonic_nonpositive_of_boundary_nonpositive_componentwise
      hU_geometry hlower_harmonic hlower_continuous hlower_boundary
  intro x hx
  have hx_le : f x ≤ M := by linarith [hupper x hx]
  have hx_ge : -M ≤ f x := by linarith [hlower x hx]
  simpa [Real.norm_eq_abs] using abs_le.mpr ⟨hx_ge, hx_le⟩

namespace SmoothRelativelyCompactExhaustion

/--
%%handwave
name:
  Closed exhaustion collars have componentwise maximum-principle geometry
statement:
  If the inner exhaustion domain contains a point, then the closed collar
  outside it is a proper relatively compact open region and has the
  componentwise maximum-principle geometry.
proof:
  The collar is open and has compact closure.  It is proper because it omits
  the chosen point in the inner domain.
-/
theorem closedCollar_hasComponentwiseMaximumPrincipleGeometry
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ} {p : X}
    (hp : p ∈ (E.domain m).carrier) :
    HasComponentwiseMaximumPrincipleGeometry (E.closedCollar m n) := by
  refine
    hasComponentwiseMaximumPrincipleGeometry_of_open_compactClosure_ne_univ
      (E.closedCollar_isOpen m n) (E.closedCollar_compact_closure m n) ?_
  intro hcollar_univ
  exact (E.not_mem_closedCollar_of_mem_inner hp) (by
    rw [hcollar_univ]
    exact Set.mem_univ p)

/--
%%handwave
name:
  Closed exhaustion collar Perron domains have componentwise geometry
statement:
  A nonempty closed exhaustion collar, viewed as a Perron domain, has the
  componentwise maximum-principle geometry as soon as the inner domain
  contains a point.
proof:
  This is the geometry of the underlying closed collar, rewritten through the
  Perron-domain packaging.
-/
theorem closedCollarPerronDomain_hasComponentwiseMaximumPrincipleGeometry
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ} {p : X}
    (hnonempty : (E.closedCollar m n).Nonempty)
    (hp : p ∈ (E.domain m).carrier) :
    HasComponentwiseMaximumPrincipleGeometry
      (E.closedCollarPerronDomain m n hnonempty).carrier := by
  simpa using E.closedCollar_hasComponentwiseMaximumPrincipleGeometry
    (m := m) (n := n) hp

/--
%%handwave
name:
  Outer collar boundary points have local Perron barriers
statement:
  At a point of the outer boundary of an exhaustion collar, the local Perron
  barrier for the outer exhaustion domain restricts to a local barrier for the
  collar.
proof:
  Use a smooth defining function for the outer exhaustion boundary to obtain
  an exterior tangent disk.  Since the closed collar lies in the closed outer
  exhaustion domain, the same disk is exterior to the collar and touches it
  only at the chosen boundary point.
-/
theorem closedCollarPerronDomain_outer_boundary_hasLocalPerronBarrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hnonempty : (E.closedCollar m n).Nonempty) {x : X}
    (hx_collar :
      x ∈ (E.closedCollarPerronDomain m n hnonempty).boundary)
    (hx_outer : x ∈ (E.domain n).boundary) :
    HasLocalPerronBarrierAt
      (E.closedCollarPerronDomain m n hnonempty) x := by
  let C : PerronDomain X := E.closedCollarPerronDomain m n hnonempty
  let Ωn : PerronDomain X := PerronDomain.ofSmoothBoundaryDomain (E.domain n)
  have hx_outer_frontier : x ∈ frontier (E.domain n).carrier := by
    simpa [SmoothBoundaryDomain.boundary] using hx_outer
  have hxΩn : x ∈ Ωn.boundary := by
    simpa [Ωn, PerronDomain.boundary] using hx_outer_frontier
  rcases (E.domain n).smooth_boundary x hx_outer_frontier with
    ⟨e, he, hx_source, r, hr_smooth, dr, hr_deriv, hdr_nonzero, hdefines⟩
  rcases smoothBoundaryDefiningFunction_has_exterior_tangent_disk
      Ωn hxΩn he hx_source hr_smooth.contDiffAt hr_deriv hdr_nonzero hdefines with
    ⟨N, c, R, hN_open, hxN, hN_source, hRpos, houtside_outer,
      htangent_outer⟩
  have houtside_collar :
      ∀ y ∈ closure C.carrier ∩ N, R ≤ ‖e y - c‖ := by
    intro y hy
    have hy_collar_closure : y ∈ closure (E.closedCollar m n) := by
      simpa [C] using hy.1
    have hy_outer_closure : y ∈ closure (E.domain n).carrier :=
      E.closure_closedCollar_subset_outer_closure m n hy_collar_closure
    exact houtside_outer y (by
      refine ⟨?_, hy.2⟩
      simpa [Ωn] using hy_outer_closure)
  have htangent_collar :
      ∀ y ∈ closure C.carrier ∩ N, ‖e y - c‖ = R ↔ y = x := by
    intro y hy
    have hy_collar_closure : y ∈ closure (E.closedCollar m n) := by
      simpa [C] using hy.1
    have hy_outer_closure : y ∈ closure (E.domain n).carrier :=
      E.closure_closedCollar_subset_outer_closure m n hy_collar_closure
    have hy_outer : y ∈ closure Ωn.carrier ∩ N := by
      refine ⟨?_, hy.2⟩
      simpa [Ωn] using hy_outer_closure
    constructor
    · intro hdist
      exact (htangent_outer y hy_outer).1 hdist
    · intro hyx
      rw [hyx]
      exact (htangent_outer x
        ⟨by simpa [Ωn] using frontier_subset_closure hx_outer_frontier, hxN⟩).2 rfl
  exact exteriorTangentDisk_logPotential_has_local_perron_barrier
    C hx_collar he hN_open hxN hN_source hRpos houtside_collar
      htangent_collar

/--
%%handwave
name:
  Inner collar boundary points have local Perron barriers
statement:
  At a point of the inner boundary of an exhaustion collar, reversing the
  smooth defining function for the inner exhaustion boundary gives a local
  Perron barrier for the collar.
proof:
  The collar lies on the exterior side of the inner exhaustion boundary.  A
  sign-reversed defining function therefore describes the closed side of the
  collar near the boundary point.  The tangent-disk construction for smooth
  sublevel sets gives a disk contained on the removed inner side, and its
  logarithmic potential is the required local barrier.
-/
theorem closedCollarPerronDomain_inner_boundary_hasLocalPerronBarrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hnonempty : (E.closedCollar m n).Nonempty) {x : X}
    (hx_collar :
      x ∈ (E.closedCollarPerronDomain m n hnonempty).boundary)
    (hx_inner : x ∈ (E.domain m).boundary) :
    HasLocalPerronBarrierAt
      (E.closedCollarPerronDomain m n hnonempty) x := by
  let C : PerronDomain X := E.closedCollarPerronDomain m n hnonempty
  have hx_inner_frontier : x ∈ frontier (E.domain m).carrier := by
    simpa [SmoothBoundaryDomain.boundary] using hx_inner
  rcases (E.domain m).smooth_boundary x hx_inner_frontier with
    ⟨e, he, hx_source, r, hr_smooth, dr, hr_deriv, hdr_nonzero, hdefines⟩
  rw [eventually_nhds_iff] at hdefines
  rcases hdefines with ⟨N₀, hN₀_defines, hN₀_open, hxN₀⟩
  have hx_defines := hN₀_defines x hxN₀
  have hr_zero : r (e x) = 0 :=
    hx_defines.2.2.mp hx_inner_frontier
  have hneg_smooth :
      ContDiffAt ℝ ∞ (fun z : ℂ => -r z) (e x) := by
    simpa only [Pi.neg_apply] using hr_smooth.neg.contDiffAt
  have hneg_deriv :
      HasFDerivAt (fun z : ℂ => -r z) (-dr) (e x) := by
    simpa only [Pi.neg_apply] using hr_deriv.neg
  have hneg_deriv_nonzero : (-dr) ≠ 0 := by
    intro hzero
    exact hdr_nonzero (neg_eq_zero.mp hzero)
  have hneg_zero : (fun z : ℂ => -r z) (e x) = 0 := by
    simp [hr_zero]
  rcases smoothPlaneSublevelSet_has_exterior_tangent_disk
      hneg_smooth hneg_deriv hneg_deriv_nonzero hneg_zero with
    ⟨W, c, R, hW_open, hexW, hRpos, houtside_plane, htangent_plane⟩
  let N : Set X := N₀ ∩ (e.source ∩ e ⁻¹' W)
  have hN_open : IsOpen N :=
    hN₀_open.inter (by simpa using e.isOpen_inter_preimage hW_open)
  have hxN : x ∈ N := by
    exact ⟨hxN₀, hx_source, hexW⟩
  have hN_source : N ⊆ e.source := by
    intro y hy
    exact hy.2.1
  have hclosed_side :
      ∀ y ∈ closure C.carrier ∩ N, (fun z : ℂ => -r z) (e y) ≤ 0 := by
    intro y hy
    have hy_collar_closure : y ∈ closure (E.closedCollar m n) := by
      simpa [C] using hy.1
    have hy_defines := hN₀_defines y hy.2.1
    by_contra hnot
    have hpos : 0 < -r (e y) := lt_of_not_ge hnot
    have hr_neg : r (e y) < 0 := by linarith
    have hy_inner : y ∈ (E.domain m).carrier :=
      hy_defines.2.1.mpr hr_neg
    exact (E.not_mem_closure_closedCollar_of_mem_inner
      (m := m) (n := n) hy_inner) hy_collar_closure
  have houtside_collar :
      ∀ y ∈ closure C.carrier ∩ N, R ≤ ‖e y - c‖ := by
    intro y hy
    exact houtside_plane (e y) hy.2.2.2 (hclosed_side y hy)
  have htangent_collar :
      ∀ y ∈ closure C.carrier ∩ N, ‖e y - c‖ = R ↔ y = x := by
    intro y hy
    have hy_source : y ∈ e.source := hy.2.2.1
    have hyW : e y ∈ W := hy.2.2.2
    have hplane := htangent_plane (e y) hyW (hclosed_side y hy)
    constructor
    · intro hdist
      have hey : e y = e x := hplane.1 hdist
      calc
        y = e.symm (e y) := (e.left_inv hy_source).symm
        _ = e.symm (e x) := by rw [hey]
        _ = x := e.left_inv hx_source
    · intro hyx
      rw [hyx]
      exact (htangent_plane (e x) hexW (by simp [hr_zero])).2 rfl
  exact exteriorTangentDisk_logPotential_has_local_perron_barrier
    C hx_collar he hN_open hxN hN_source hRpos houtside_collar
      htangent_collar

/--
%%handwave
name:
  Exhaustion collar boundary points have local Perron barriers
statement:
  Every boundary point of a nonempty collar between strictly nested exhaustion
  domains admits a local Perron barrier.
proof:
  The frontier of the collar is contained in the union of the outer and inner
  exhaustion boundaries.  Use the inherited outer-boundary barrier on the
  first piece and the sign-reversed inner-boundary tangent-disk barrier on the
  second piece.
-/
theorem closedCollarPerronDomain_boundary_points_have_local_barriers
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (_hmn : m < n)
    (hnonempty : (E.closedCollar m n).Nonempty) :
    ∀ x ∈ (E.closedCollarPerronDomain m n hnonempty).boundary,
      HasLocalPerronBarrierAt (E.closedCollarPerronDomain m n hnonempty) x := by
  intro x hx
  have hx_frontier : x ∈ frontier (E.closedCollar m n) := by
    simpa using hx
  rcases E.frontier_closedCollar_subset_outer_boundary_or_inner_boundary m n
      hx_frontier with hx_outer | hx_inner
  · exact E.closedCollarPerronDomain_outer_boundary_hasLocalPerronBarrier
      hnonempty hx hx_outer
  · exact E.closedCollarPerronDomain_inner_boundary_hasLocalPerronBarrier
      hnonempty hx hx_inner

/--
%%handwave
name:
  Exhaustion collar boundary points have Perron barriers
statement:
  Every boundary point of a nonempty collar between strictly nested exhaustion
  domains admits a Perron barrier.
proof:
  Globalize the local Perron barriers at each boundary point.
-/
theorem closedCollarPerronDomain_boundary_points_have_barriers
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m < n)
    (hnonempty : (E.closedCollar m n).Nonempty) :
    ∀ x ∈ (E.closedCollarPerronDomain m n hnonempty).boundary,
      HasPerronBarrierAt (E.closedCollarPerronDomain m n hnonempty) x := by
  intro x hx
  exact localPerronBarrierAt_globalizes
    (E.closedCollarPerronDomain m n hnonempty)
    (E.closedCollarPerronDomain_boundary_points_have_local_barriers
      hmn hnonempty x hx)

/--
%%handwave
name:
  Exhaustion collars are Perron-regular
statement:
  A nonempty collar between strictly nested exhaustion domains is regular for
  Perron's method.
proof:
  The collar has the componentwise maximum-principle geometry because it is a
  proper relatively compact open set.  The boundary regularity follows from
  the local barriers on the two exhaustion-boundary pieces.
-/
theorem closedCollarPerronDomain_perronRegular
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m < n)
    (hnonempty : (E.closedCollar m n).Nonempty) :
    PerronRegularBoundary (E.closedCollarPerronDomain m n hnonempty) := by
  refine ⟨?_, E.closedCollarPerronDomain_boundary_points_have_barriers
    hmn hnonempty⟩
  rcases (E.domain m).nonempty with ⟨p, hp⟩
  exact E.closedCollarPerronDomain_hasComponentwiseMaximumPrincipleGeometry
    hnonempty hp

/--
%%handwave
name:
  Inner boundary value on a closed exhaustion collar
statement:
  The inner-boundary datum for a closed exhaustion collar is one on the inner
  exhaustion boundary and zero elsewhere.
-/
noncomputable def closedCollarInnerBoundaryFunction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) (m : ℕ) : X → ℝ := by
  classical
  exact fun x ↦ if x ∈ (E.domain m).boundary then 1 else 0

/--
%%handwave
name:
  Inner collar boundary values are continuous
statement:
  On the boundary of a collar between strictly nested exhaustion domains, the
  datum equal to one on the inner boundary and zero on the outer boundary is
  continuous.
proof:
  The two boundary pieces are locally separated.  Near an inner-boundary
  point the collar boundary cannot meet the outer exhaustion boundary because
  the inner boundary lies inside the outer domain.  Near an outer-boundary
  point it cannot meet the inner boundary because the earlier closed domain is
  compactly contained in the outer domain.
-/
theorem closedCollarInnerBoundaryFunction_continuousOn_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m < n)
    (hnonempty : (E.closedCollar m n).Nonempty) :
    ContinuousOn (E.closedCollarInnerBoundaryFunction m)
      (E.closedCollarPerronDomain m n hnonempty).boundary := by
  classical
  let B : Set X := (E.closedCollarPerronDomain m n hnonempty).boundary
  have hboundary_subset :
      B ⊆ (E.domain n).boundary ∪ (E.domain m).boundary := by
    intro y hy
    have hy_frontier : y ∈ frontier (E.closedCollar m n) := by
      simpa [B] using hy
    exact E.frontier_closedCollar_subset_outer_boundary_or_inner_boundary
      m n hy_frontier
  have hinner_local :
      ∀ x ∈ B, x ∈ (E.domain m).boundary →
        ∀ᶠ y in 𝓝 x, y ∈ B → y ∈ (E.domain m).boundary := by
    intro x hxB hxinner
    have hx_outer_domain : x ∈ (E.domain n).carrier :=
      E.boundary_subset_carrier_of_lt hmn hxinner
    filter_upwards [(E.domain n).isOpen.mem_nhds hx_outer_domain]
      with y hy_outer_domain hyB
    rcases hboundary_subset hyB with hy_outer_boundary | hy_inner_boundary
    · have hy_outer_frontier : y ∈ frontier (E.domain n).carrier := by
        simpa [SmoothBoundaryDomain.boundary] using hy_outer_boundary
      have hy_inter :
          y ∈ (E.domain n).carrier ∩ frontier (E.domain n).carrier :=
        ⟨hy_outer_domain, hy_outer_frontier⟩
      exact False.elim (by
        simp [(E.domain n).isOpen.inter_frontier_eq] at hy_inter)
    · exact hy_inner_boundary
  have houter_local :
      ∀ x ∈ B, x ∉ (E.domain m).boundary →
        ∀ᶠ y in 𝓝 x, y ∈ B → y ∉ (E.domain m).boundary := by
    intro x hxB hxnotinner
    have hx_outer : x ∈ (E.domain n).boundary := by
      rcases hboundary_subset hxB with hx_outer | hx_inner
      · exact hx_outer
      · exact False.elim (hxnotinner hx_inner)
    have hx_outer_frontier : x ∈ frontier (E.domain n).carrier := by
      simpa [SmoothBoundaryDomain.boundary] using hx_outer
    have hx_not_inner_closure : x ∉ closure (E.domain m).carrier := by
      intro hx_inner_closure
      have hx_outer_domain : x ∈ (E.domain n).carrier :=
        E.closure_carrier_subset_of_lt hmn hx_inner_closure
      have hx_inter :
          x ∈ (E.domain n).carrier ∩ frontier (E.domain n).carrier :=
        ⟨hx_outer_domain, hx_outer_frontier⟩
      simp [(E.domain n).isOpen.inter_frontier_eq] at hx_inter
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx_not_inner_closure]
      with y hy_not_inner_closure _hyB hy_inner
    have hy_inner_frontier : y ∈ frontier (E.domain m).carrier := by
      simpa [SmoothBoundaryDomain.boundary] using hy_inner
    exact hy_not_inner_closure (frontier_subset_closure hy_inner_frontier)
  intro x hxB
  have hxB' : x ∈ B := by
    simpa [B] using hxB
  by_cases hxinner : x ∈ (E.domain m).boundary
  · have hconst :
        E.closedCollarInnerBoundaryFunction m
          =ᶠ[𝓝[B] x] fun _ : X => (1 : ℝ) := by
      filter_upwards [(hinner_local x hxB' hxinner).filter_mono
        nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyB
      simp [closedCollarInnerBoundaryFunction, hy hyB]
    exact continuousWithinAt_const.congr_of_eventuallyEq hconst (by
      simp [closedCollarInnerBoundaryFunction, hxinner])
  · have hconst :
        E.closedCollarInnerBoundaryFunction m
          =ᶠ[𝓝[B] x] fun _ : X => (0 : ℝ) := by
      filter_upwards [(houter_local x hxB' hxinner).filter_mono
        nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyB
      simp [closedCollarInnerBoundaryFunction, hy hyB]
    exact continuousWithinAt_const.congr_of_eventuallyEq hconst (by
      simp [closedCollarInnerBoundaryFunction, hxinner])

/--
%%handwave
name:
  Inner boundary data for a closed exhaustion collar
statement:
  The harmonic-measure boundary data on a closed exhaustion collar is one on
  the inner boundary and zero on the outer boundary.
proof:
  Continuity follows from the local separation of the two boundary pieces.
-/
noncomputable def closedCollarInnerBoundaryData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m < n)
    (hnonempty : (E.closedCollar m n).Nonempty) :
    PerronBoundaryData (E.closedCollarPerronDomain m n hnonempty) where
  toFun := E.closedCollarInnerBoundaryFunction m
  continuous_boundary :=
    E.closedCollarInnerBoundaryFunction_continuousOn_boundary hmn hnonempty

@[simp] theorem closedCollarInnerBoundaryData_eq_one_of_inner_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m < n)
    (hnonempty : (E.closedCollar m n).Nonempty)
    {x : X} (hx : x ∈ (E.domain m).boundary) :
    E.closedCollarInnerBoundaryData hmn hnonempty x = 1 := by
  classical
  simp [closedCollarInnerBoundaryData, closedCollarInnerBoundaryFunction, hx]

@[simp] theorem closedCollarInnerBoundaryData_eq_zero_of_not_inner_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m < n)
    (hnonempty : (E.closedCollar m n).Nonempty)
    {x : X} (hx : x ∉ (E.domain m).boundary) :
    E.closedCollarInnerBoundaryData hmn hnonempty x = 0 := by
  classical
  simp [closedCollarInnerBoundaryData, closedCollarInnerBoundaryFunction, hx]

/--
%%handwave
name:
  Inner harmonic measure of a closed exhaustion collar
statement:
  The inner harmonic measure of a regular closed exhaustion collar is the
  Perron solution with boundary value one on the inner boundary and zero on
  the outer boundary.
-/
noncomputable def exhaustionClosedCollarInnerHarmonicMeasure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m < n)
    (hnonempty : (E.closedCollar m n).Nonempty) : X → ℝ :=
  perronDirichletCandidate (E.closedCollarPerronDomain m n hnonempty)
    (E.closedCollarInnerBoundaryData hmn hnonempty)

/--
%%handwave
name:
  Inner harmonic measure solves the collar Dirichlet problem
statement:
  The inner harmonic measure of a closed exhaustion collar is harmonic in the
  collar, continuous on its closure, and assumes the prescribed boundary
  values.
proof:
  Apply Perron's theorem using the collar regularity proved from the local
  barriers on the two boundary components.
-/
theorem exhaustionClosedCollarInnerHarmonicMeasure_solves
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m < n)
    (hnonempty : (E.closedCollar m n).Nonempty) :
    SolvesHarmonicDirichletProblem
      (E.closedCollarPerronDomain m n hnonempty)
      (E.closedCollarInnerBoundaryData hmn hnonempty)
      (E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty) := by
  exact perron_envelope_solves_dirichlet
    (E.closedCollarPerronDomain m n hnonempty)
    (E.closedCollarPerronDomain_perronRegular hmn hnonempty)
    (E.closedCollarInnerBoundaryData hmn hnonempty)

/--
%%handwave
name:
  Inner harmonic measure is harmonic in the collar
statement:
  The inner harmonic measure is harmonic on the open collar.
-/
theorem exhaustionClosedCollarInnerHarmonicMeasure_harmonic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m < n)
    (hnonempty : (E.closedCollar m n).Nonempty) :
    IsHarmonicOnSurface (E.closedCollar m n)
      (E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty) := by
  simpa using
    (E.exhaustionClosedCollarInnerHarmonicMeasure_solves hmn hnonempty).1

/--
%%handwave
name:
  Inner harmonic measure is continuous on the closed collar
statement:
  The inner harmonic measure is continuous on the closure of the collar.
-/
theorem exhaustionClosedCollarInnerHarmonicMeasure_continuousOn_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m < n)
    (hnonempty : (E.closedCollar m n).Nonempty) :
    ContinuousOn (E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty)
      (closure (E.closedCollar m n)) := by
  simpa using
    (E.exhaustionClosedCollarInnerHarmonicMeasure_solves hmn hnonempty).2.1

/--
%%handwave
name:
  Inner harmonic measure takes values between zero and one
statement:
  The inner harmonic measure of a closed exhaustion collar lies between zero
  and one throughout the collar.
proof:
  The boundary data lies between zero and one, and the componentwise maximum
  principle applies to the Perron solution.
-/
theorem exhaustionClosedCollarInnerHarmonicMeasure_mem_Icc
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m < n)
    (hnonempty : (E.closedCollar m n).Nonempty) :
    ∀ x ∈ E.closedCollar m n,
      E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x ∈
        Set.Icc (0 : ℝ) 1 := by
  classical
  let C : PerronDomain X := E.closedCollarPerronDomain m n hnonempty
  let φ : PerronBoundaryData C := E.closedCollarInnerBoundaryData hmn hnonempty
  have hsolves :
      SolvesHarmonicDirichletProblem C φ
        (E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty) := by
    simpa [C, φ] using
      E.exhaustionClosedCollarInnerHarmonicMeasure_solves hmn hnonempty
  have hgeom : HasComponentwiseMaximumPrincipleGeometry C.carrier :=
    (E.closedCollarPerronDomain_perronRegular hmn hnonempty).1
  have hφ_nonneg : ∀ y ∈ C.boundary, (0 : ℝ) ≤ φ y := by
    intro y hy
    by_cases hinner : y ∈ (E.domain m).boundary
    · simp [φ, closedCollarInnerBoundaryData, closedCollarInnerBoundaryFunction,
        hinner]
    · simp [φ, closedCollarInnerBoundaryData, closedCollarInnerBoundaryFunction,
        hinner]
  have hφ_le_one : ∀ y ∈ C.boundary, φ y ≤ (1 : ℝ) := by
    intro y hy
    by_cases hinner : y ∈ (E.domain m).boundary
    · simp [φ, closedCollarInnerBoundaryData, closedCollarInnerBoundaryFunction,
        hinner]
    · simp [φ, closedCollarInnerBoundaryData, closedCollarInnerBoundaryFunction,
        hinner]
  have hlower :
      ∀ x ∈ C.carrier,
        (0 : ℝ) ≤ E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x :=
    le_solvesHarmonicDirichletProblem_of_boundary_le hsolves hgeom hφ_nonneg
  have hupper :
      ∀ x ∈ C.carrier,
        E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x ≤
          (1 : ℝ) :=
    solvesHarmonicDirichletProblem_le_of_boundary_le hsolves hgeom hφ_le_one
  intro x hx
  exact ⟨hlower x (by simpa [C] using hx), hupper x (by simpa [C] using hx)⟩

/--
%%handwave
name:
  Collar harmonic-measure upper comparison
statement:
  A harmonic function on a closed exhaustion collar that is bounded above by
  \(M\) on the inner boundary part and by \(0\) on the remaining collar
  boundary is bounded above by \(M\) times the inner harmonic measure
  throughout the collar.
proof:
  Subtract \(M\) times the inner harmonic measure.  The difference is harmonic
  in the collar and continuous on its closure.  On the boundary, the
  Dirichlet trace of the harmonic measure is one on the inner part and zero
  on the outer part, so the difference is nonpositive.  The componentwise
  maximum principle gives the result.
-/
theorem harmonicOn_closedCollar_le_innerBoundaryBound_mul_innerHarmonicMeasure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {m n : ℕ}
    (hmn : m < n)
    (hnonempty : (E.closedCollar m n).Nonempty)
    {u : X → ℝ} {M : ℝ}
    (hu_harmonic : IsHarmonicOnSurface (E.closedCollar m n) u)
    (hu_continuous : ContinuousOn u (closure (E.closedCollar m n)))
    (hinner :
      ∀ x ∈ (E.closedCollarPerronDomain m n hnonempty).boundary,
        x ∈ (E.domain m).boundary → u x ≤ M)
    (houter :
      ∀ x ∈ (E.closedCollarPerronDomain m n hnonempty).boundary,
        x ∉ (E.domain m).boundary → u x ≤ 0) :
    ∀ x ∈ E.closedCollar m n,
      u x ≤
        M * (E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x) := by
  classical
  let C : PerronDomain X := E.closedCollarPerronDomain m n hnonempty
  let φ : PerronBoundaryData C := E.closedCollarInnerBoundaryData hmn hnonempty
  have hω_solves :
      SolvesHarmonicDirichletProblem C φ
        (E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty) := by
    simpa [C, φ] using
      E.exhaustionClosedCollarInnerHarmonicMeasure_solves hmn hnonempty
  have hω_harmonic :
      IsHarmonicOnSurface C.carrier
        (E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty) :=
    hω_solves.1
  have hω_continuous :
      ContinuousOn (E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty)
        (closure C.carrier) :=
    hω_solves.2.1
  have hgeom : HasComponentwiseMaximumPrincipleGeometry C.carrier :=
    (E.closedCollarPerronDomain_perronRegular hmn hnonempty).1
  have hdiff_harmonic :
      IsHarmonicOnSurface C.carrier
        (fun x : X ↦
          u x - M * E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x) := by
    have huC : IsHarmonicOnSurface C.carrier u := by
      simpa [C] using hu_harmonic
    exact harmonicOnSurface_sub huC
      (harmonicOnSurface_const_mul M hω_harmonic)
  have hdiff_continuous :
      ContinuousOn
        (fun x : X ↦
          u x - M * E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x)
        (closure C.carrier) := by
    have huC : ContinuousOn u (closure C.carrier) := by
      simpa [C] using hu_continuous
    exact huC.sub (continuousOn_const.mul hω_continuous)
  have hdiff_boundary :
      ∀ x ∈ C.boundary,
        u x - M * E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x ≤ 0 := by
    intro x hxC
    have hωx :
        E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x = φ x :=
      hω_solves.2.2 x hxC
    by_cases hxinner : x ∈ (E.domain m).boundary
    · have hφx : φ x = 1 := by
        simp [φ, closedCollarInnerBoundaryData, closedCollarInnerBoundaryFunction,
          hxinner]
      have hω_one :
          E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x = 1 := by
        rw [hωx, hφx]
      have hux : u x ≤ M := hinner x (by simpa [C] using hxC) hxinner
      rw [hω_one]
      linarith
    · have hφx : φ x = 0 := by
        simp [φ, closedCollarInnerBoundaryData, closedCollarInnerBoundaryFunction,
          hxinner]
      have hω_zero :
          E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x = 0 := by
        rw [hωx, hφx]
      have hux : u x ≤ 0 := houter x (by simpa [C] using hxC) hxinner
      rw [hω_zero]
      linarith
  have hdiff_nonpositive :
      ∀ x ∈ C.carrier,
        u x - M * E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x ≤ 0 :=
    harmonic_nonpositive_of_boundary_nonpositive_componentwise
      hgeom hdiff_harmonic hdiff_continuous (by
        intro x hx
        have hxC : x ∈ C.boundary := by
          simpa [PerronDomain.boundary] using hx
        exact hdiff_boundary x hxC)
  intro x hx
  have hxC : x ∈ C.carrier := by
    simpa [C] using hx
  have h := hdiff_nonpositive x hxC
  exact sub_nonpos.mp h

end SmoothRelativelyCompactExhaustion

/--
%%handwave
name:
  Annular Perron domains have componentwise geometry
statement:
  The annulus obtained by deleting a closed coordinate disk from a smooth
  boundary domain has the componentwise maximum-principle geometry.
proof:
  The annulus is open and its closure is contained in the compact closure of
  the outer smooth domain.  It is a proper subset of the surface because the
  deleted closed coordinate disk contains its distinguished boundary point.
-/
theorem annularPerronDomain_hasComponentwiseMaximumPrincipleGeometry
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty) :
    HasComponentwiseMaximumPrincipleGeometry
      (annularPerronDomain Ω D hD_subset hnonempty).carrier := by
  rw [annularPerronDomain_carrier]
  refine hasComponentwiseMaximumPrincipleGeometry_of_open_compactClosure_ne_univ
    (U := Ω.carrier \ D.carrier) ?_ ?_ ?_
  · exact Ω.isOpen.sdiff (ClosedCoordinateDisk.isClosed D)
  · exact Ω.compact_closure.of_isClosed_subset isClosed_closure
      (closure_mono Set.diff_subset)
  · intro hU_univ
    have hD : D.positiveRealBoundaryPoint ∈ Ω.carrier \ D.carrier := by
      rw [hU_univ]
      exact Set.mem_univ _
    exact hD.2 (D.positiveRealBoundaryPoint_mem_carrier)

/--
%%handwave
name:
  Logarithmic annular boundary values
statement:
  On the annular Perron domain, prescribe the constant value \(\log r\) on
  the inner coordinate circle of radius \(r\), and value \(0\) on the outer
  boundary.
proof:
  The two boundary components are disjoint closed smooth curves, so the
  piecewise constant boundary value is continuous on the boundary.
-/
noncomputable def annularLogBoundaryFunction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : ClosedCoordinateDisk X) : X → ℝ := by
  classical
  exact fun x ↦ if x ∈ D.boundaryCircle then Real.log D.closedRadius else 0

/--
%%handwave
name:
  Frontier of a closed coordinate disk lies on its boundary circle
statement:
  The topological frontier of a closed coordinate disk is contained in the
  coordinate circle with the disk's closed radius.
proof:
  A frontier point of the compact closed disk belongs to the disk but is not
  an interior point.  If its coordinate radius were strictly smaller than the
  closed radius, the inverse image of the corresponding open Euclidean disk
  would be an open neighborhood contained in the closed disk, contradiction.
-/
theorem ClosedCoordinateDisk.frontier_carrier_subset_boundaryCircle
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (D : ClosedCoordinateDisk X) :
    frontier D.carrier ⊆ D.boundaryCircle := by
  intro x hx_frontier
  have hxD : x ∈ D.carrier :=
    (ClosedCoordinateDisk.isClosed D).frontier_subset hx_frontier
  have hx_not_interior : x ∉ interior D.carrier :=
    (mem_frontier_iff_notMem_interior hxD).mp hx_frontier
  have hxD' :
      x ∈ D.openDisk.chart.source ∩
        D.openDisk.chart ⁻¹'
          Metric.closedBall D.openDisk.center D.closedRadius := by
    simpa [D.carrier_eq] using hxD
  have hdist_le :
      dist (D.openDisk.chart x) D.openDisk.center ≤ D.closedRadius := by
    simpa [Metric.mem_closedBall] using hxD'.2
  have hnot_lt :
      ¬ dist (D.openDisk.chart x) D.openDisk.center < D.closedRadius := by
    intro hlt
    have hx_open : x ∈ D.expandedOpenDisk D.closedRadius := by
      rw [ClosedCoordinateDisk.expandedOpenDisk]
      exact ⟨hxD'.1, by simpa [Metric.mem_ball] using hlt⟩
    have hopen : IsOpen (D.expandedOpenDisk D.closedRadius) :=
      D.expandedOpenDisk_isOpen D.closedRadius
    have hsubset : D.expandedOpenDisk D.closedRadius ⊆ D.carrier := by
      intro y hy
      rw [ClosedCoordinateDisk.expandedOpenDisk] at hy
      rw [D.carrier_eq]
      exact ⟨hy.1, Metric.ball_subset_closedBall hy.2⟩
    exact hx_not_interior ((interior_maximal hsubset hopen) hx_open)
  have hdist_eq :
      dist (D.openDisk.chart x) D.openDisk.center = D.closedRadius :=
    le_antisymm hdist_le (le_of_not_gt hnot_lt)
  rw [ClosedCoordinateDisk.boundaryCircle]
  exact ⟨hxD'.1, by simpa [Metric.mem_sphere, dist_eq_norm] using hdist_eq⟩

/--
%%handwave
name:
  Non-boundary points of a closed coordinate disk are interior points
statement:
  If a point lies in a closed coordinate disk but not on its coordinate
  boundary circle, then it lies in the interior of the closed disk.
proof:
  In the defining coordinate, membership in the closed disk gives radius at
  most the closed radius.  Not being on the boundary circle makes this
  inequality strict.  The corresponding open coordinate disk of the same
  radius is an open neighborhood contained in the closed disk.
-/
theorem ClosedCoordinateDisk.mem_interior_carrier_of_mem_carrier_of_not_mem_boundaryCircle
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : ClosedCoordinateDisk X) {x : X}
    (hxD : x ∈ D.carrier) (hx_not_boundary : x ∉ D.boundaryCircle) :
    x ∈ interior D.carrier := by
  have hxD' :
      x ∈ D.openDisk.chart.source ∩
        D.openDisk.chart ⁻¹'
          Metric.closedBall D.openDisk.center D.closedRadius := by
    simpa [D.carrier_eq] using hxD
  have hdist_le :
      dist (D.openDisk.chart x) D.openDisk.center ≤ D.closedRadius := by
    simpa [Metric.mem_closedBall] using hxD'.2
  have hdist_ne :
      dist (D.openDisk.chart x) D.openDisk.center ≠ D.closedRadius := by
    intro hdist_eq
    apply hx_not_boundary
    rw [ClosedCoordinateDisk.boundaryCircle]
    exact ⟨hxD'.1, by simpa [Metric.mem_sphere, dist_eq_norm] using hdist_eq⟩
  have hdist_lt :
      dist (D.openDisk.chart x) D.openDisk.center < D.closedRadius :=
    lt_of_le_of_ne hdist_le hdist_ne
  have hx_open : x ∈ D.expandedOpenDisk D.closedRadius := by
    rw [ClosedCoordinateDisk.expandedOpenDisk]
    exact ⟨hxD'.1, by simpa [Metric.mem_ball] using hdist_lt⟩
  have hopen : IsOpen (D.expandedOpenDisk D.closedRadius) :=
    D.expandedOpenDisk_isOpen D.closedRadius
  have hsubset : D.expandedOpenDisk D.closedRadius ⊆ D.carrier := by
    intro y hy
    rw [ClosedCoordinateDisk.expandedOpenDisk] at hy
    rw [D.carrier_eq]
    exact ⟨hy.1, Metric.ball_subset_closedBall hy.2⟩
  exact interior_maximal hsubset hopen hx_open

/--
%%handwave
name:
  Annular Perron boundary lies on the outer boundary or inner circle
statement:
  The boundary of the annulus obtained by deleting a closed coordinate disk
  from a smooth domain is contained in the union of the original outer
  boundary and the inner coordinate circle.
proof:
  The annulus is the intersection of the original domain with the complement
  of the closed disk.  The frontier of an intersection lies in the union of
  the two frontiers.  The frontier of the complement of the closed disk is the
  frontier of the disk, and that frontier lies on the boundary circle.
-/
theorem annularPerronDomain_boundary_subset_outer_or_inner
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty) :
    (annularPerronDomain Ω D hD_subset hnonempty).boundary ⊆
      Ω.boundary ∪ D.boundaryCircle := by
  intro x hx
  have hx_frontier :
      x ∈ frontier (Ω.carrier ∩ D.carrierᶜ) := by
    simpa [PerronDomain.boundary, annularPerronDomain_carrier,
      Set.diff_eq] using hx
  rcases frontier_inter_subset Ω.carrier D.carrierᶜ hx_frontier with hxΩ | hxD
  · exact Or.inl hxΩ.1
  · have hxD' : x ∈ frontier D.carrier := by
      simpa [frontier_compl] using hxD.2
    exact Or.inr (D.frontier_carrier_subset_boundaryCircle hxD')

/--
%%handwave
name:
  The outer boundary is an annular Perron boundary component
statement:
  If a closed coordinate disk is contained in a smooth domain, then the
  original boundary of the smooth domain is contained in the boundary of the
  annulus obtained by deleting the disk.
proof:
  A point of the original boundary cannot lie in the deleted disk, because the
  disk is contained in the open domain and an open set is disjoint from its
  frontier.  Near such a point the complement of the deleted disk is a
  neighborhood, so the annulus and the original domain have the same frontier
  germ there.
-/
theorem outer_boundary_subset_annularPerronDomain_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty) :
    Ω.boundary ⊆ (annularPerronDomain Ω D hD_subset hnonempty).boundary := by
  intro x hxΩ_boundary
  have hx_frontier : x ∈ frontier Ω.carrier := by
    simpa [SmoothBoundaryDomain.boundary] using hxΩ_boundary
  have hx_notD : x ∉ D.carrier := by
    intro hxD
    have hx_empty : x ∈ Ω.carrier ∩ frontier Ω.carrier :=
      ⟨hD_subset hxD, hx_frontier⟩
    simp [Ω.isOpen.inter_frontier_eq] at hx_empty
  have hlocal_eq :
      (Ω.carrier \ D.carrier) ∩ D.carrierᶜ =
        Ω.carrier ∩ D.carrierᶜ := by
    ext y
    simp [Set.diff_eq]
  have hfrontier :
      ∀ᶠ y in 𝓝 x,
        (y ∈ frontier (Ω.carrier \ D.carrier) ↔
          y ∈ frontier Ω.carrier) :=
    eventually_frontier_congr_of_inter_eq
      (ClosedCoordinateDisk.isClosed D).isOpen_compl hx_notD hlocal_eq
  have hx_annular_frontier : x ∈ frontier (Ω.carrier \ D.carrier) :=
    (Filter.Eventually.self_of_nhds hfrontier).2 hx_frontier
  simpa [PerronDomain.boundary, annularPerronDomain_carrier] using
    hx_annular_frontier

/--
%%handwave
name:
  Logarithmic annular boundary values are continuous
statement:
  The boundary value which is constant \(\log r\) on the inner coordinate
  circle and \(0\) on the outer boundary is continuous on the boundary of the
  annular domain.
proof:
  The boundary of the annulus is the disjoint union of the inner coordinate
  circle and the inherited outer boundary.  Each piece is relatively open and
  closed in the annular boundary, and the boundary value is constant on each
  piece.
-/
theorem annularLogBoundaryFunction_continuousOn_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty) :
    ContinuousOn (annularLogBoundaryFunction D)
      (annularPerronDomain Ω D hD_subset hnonempty).boundary := by
  classical
  let B : Set X := (annularPerronDomain Ω D hD_subset hnonempty).boundary
  have hboundary_subset :
      B ⊆ Ω.boundary ∪ D.boundaryCircle := by
    simpa [B] using
      annularPerronDomain_boundary_subset_outer_or_inner Ω D hD_subset hnonempty
  have hinner_local :
      ∀ x ∈ B, x ∈ D.boundaryCircle →
        ∀ᶠ y in 𝓝 x, y ∈ B → y ∈ D.boundaryCircle := by
    intro x hxB hxinner
    filter_upwards [Ω.isOpen.mem_nhds (hD_subset (D.boundaryCircle_subset_carrier hxinner))]
      with y hyΩ hyB
    rcases hboundary_subset hyB with hy_outer | hy_inner
    · have hy_notΩ : y ∉ Ω.carrier := by
        intro hyΩ'
        have hy_empty : y ∈ Ω.carrier ∩ frontier Ω.carrier :=
          ⟨hyΩ', hy_outer⟩
        simp [Ω.isOpen.inter_frontier_eq] at hy_empty
      exact False.elim (hy_notΩ hyΩ)
    · exact hy_inner
  have houter_local :
      ∀ x ∈ B, x ∉ D.boundaryCircle →
        ∀ᶠ y in 𝓝 x, y ∈ B → y ∉ D.boundaryCircle := by
    intro x hxB hxnotinner
    have hx_outer : x ∈ Ω.boundary := by
      rcases hboundary_subset hxB with hx_outer | hx_inner
      · exact hx_outer
      · exact False.elim (hxnotinner hx_inner)
    have hx_notD : x ∉ D.carrier := by
      intro hxD
      have hxΩ : x ∈ Ω.carrier := hD_subset hxD
      have hx_empty : x ∈ Ω.carrier ∩ frontier Ω.carrier :=
        ⟨hxΩ, hx_outer⟩
      simp [Ω.isOpen.inter_frontier_eq] at hx_empty
    filter_upwards [(ClosedCoordinateDisk.isClosed D).isOpen_compl.mem_nhds hx_notD]
      with y hy_notD _hyB hy_inner
    exact hy_notD (D.boundaryCircle_subset_carrier hy_inner)
  intro x hxB
  have hxB' : x ∈ B := by
    simpa [B] using hxB
  by_cases hxinner : x ∈ D.boundaryCircle
  · have hconst :
        (annularLogBoundaryFunction D)
          =ᶠ[𝓝[B] x] fun _ : X => Real.log D.closedRadius := by
      filter_upwards [(hinner_local x hxB' hxinner).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with y hy hyB
      simp [annularLogBoundaryFunction, hy hyB]
    exact continuousWithinAt_const.congr_of_eventuallyEq hconst (by
      simp [annularLogBoundaryFunction, hxinner])
  · have hconst :
        (annularLogBoundaryFunction D)
          =ᶠ[𝓝[B] x] fun _ : X => 0 := by
      filter_upwards [(houter_local x hxB' hxinner).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with y hy hyB
      simp [annularLogBoundaryFunction, hy hyB]
    exact continuousWithinAt_const.congr_of_eventuallyEq hconst (by
      simp [annularLogBoundaryFunction, hxinner])

/--
%%handwave
name:
  Logarithmic annular boundary data
statement:
  On the annular Perron domain, prescribe the constant value \(\log r\) on
  the inner coordinate circle of radius \(r\), and value \(0\) on the outer
  boundary.
proof:
  The two boundary components are disjoint closed smooth curves, so the
  piecewise constant boundary value is continuous on the boundary.
-/
noncomputable def annularLogBoundaryData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty) :
    PerronBoundaryData (annularPerronDomain Ω D hD_subset hnonempty) where
  toFun := annularLogBoundaryFunction D
  continuous_boundary := by
    exact annularLogBoundaryFunction_continuousOn_boundary
      Ω D hD_subset hnonempty

@[simp] theorem annularLogBoundaryData_eq_log_on_boundaryCircle
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    {x : X} (hx : x ∈ D.boundaryCircle) :
    annularLogBoundaryData Ω D hD_subset hnonempty x =
      Real.log D.closedRadius := by
  simp [annularLogBoundaryData, annularLogBoundaryFunction, hx]

@[simp] theorem annularLogBoundaryData_eq_zero_off_boundaryCircle
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    {x : X} (hx : x ∉ D.boundaryCircle) :
    annularLogBoundaryData Ω D hD_subset hnonempty x = 0 := by
  simp [annularLogBoundaryData, annularLogBoundaryFunction, hx]

/--
%%handwave
name:
  Annular logarithmic data vanish on the outer boundary
statement:
  For the annulus obtained by deleting a closed coordinate disk contained in a
  smooth domain, the logarithmic annular boundary value is zero on the
  original boundary of the smooth domain.
proof:
  A point on the outer boundary cannot lie on the inner coordinate circle:
  the inner circle is contained in the deleted closed disk, and the closed
  disk lies inside the smooth domain, while an open domain is disjoint from
  its frontier.  Therefore the boundary value is the outer value \(0\).
-/
@[simp] theorem annularLogBoundaryData_eq_zero_on_outer_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    {x : X} (hx : x ∈ Ω.boundary) :
    annularLogBoundaryData Ω D hD_subset hnonempty x = 0 := by
  apply annularLogBoundaryData_eq_zero_off_boundaryCircle
  intro hxinner
  have hxD : x ∈ D.carrier := D.boundaryCircle_subset_carrier hxinner
  have hxΩ : x ∈ Ω.carrier := hD_subset hxD
  have hxfrontier : x ∈ frontier Ω.carrier := by
    simpa [SmoothBoundaryDomain.boundary] using hx
  have hx_empty : x ∈ Ω.carrier ∩ frontier Ω.carrier := ⟨hxΩ, hxfrontier⟩
  simp [Ω.isOpen.inter_frontier_eq] at hx_empty

/--
%%handwave
name:
  Annular logarithmic data are bounded above by the larger boundary level
statement:
  On the annular Perron boundary, the logarithmic boundary value is bounded
  above by the larger of the outer value \(0\) and the inner value
  \(\log r\).
proof:
  Every annular boundary point lies either on the original outer boundary or
  on the inner coordinate circle.  On these two pieces the boundary value is
  respectively \(0\) and \(\log r\).
-/
theorem annularLogBoundaryData_le_boundary_max
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty) :
    ∀ x ∈ (annularPerronDomain Ω D hD_subset hnonempty).boundary,
      annularLogBoundaryData Ω D hD_subset hnonempty x ≤
        max 0 (Real.log D.closedRadius) := by
  intro x hx
  rcases annularPerronDomain_boundary_subset_outer_or_inner
      Ω D hD_subset hnonempty hx with hxouter | hxinner
  · rw [annularLogBoundaryData_eq_zero_on_outer_boundary
      Ω D hD_subset hnonempty hxouter]
    exact le_max_left 0 (Real.log D.closedRadius)
  · rw [annularLogBoundaryData_eq_log_on_boundaryCircle
      Ω D hD_subset hnonempty hxinner]
    exact le_max_right 0 (Real.log D.closedRadius)

/--
%%handwave
name:
  Annular logarithmic data are bounded below by the smaller boundary level
statement:
  On the annular Perron boundary, the logarithmic boundary value is bounded
  below by the smaller of the outer value \(0\) and the inner value
  \(\log r\).
proof:
  Every annular boundary point lies either on the original outer boundary or
  on the inner coordinate circle.  On these two pieces the boundary value is
  respectively \(0\) and \(\log r\).
-/
theorem boundary_min_le_annularLogBoundaryData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty) :
    ∀ x ∈ (annularPerronDomain Ω D hD_subset hnonempty).boundary,
      min (Real.log D.closedRadius) 0 ≤
        annularLogBoundaryData Ω D hD_subset hnonempty x := by
  intro x hx
  rcases annularPerronDomain_boundary_subset_outer_or_inner
      Ω D hD_subset hnonempty hx with hxouter | hxinner
  · rw [annularLogBoundaryData_eq_zero_on_outer_boundary
      Ω D hD_subset hnonempty hxouter]
    exact min_le_right (Real.log D.closedRadius) 0
  · rw [annularLogBoundaryData_eq_log_on_boundaryCircle
      Ω D hD_subset hnonempty hxinner]
    exact min_le_left (Real.log D.closedRadius) 0

/--
%%handwave
name:
  Small-radius annular logarithmic data are nonpositive
statement:
  If the inner coordinate radius is at most \(1\), then the logarithmic
  annular boundary value is nonpositive on the annular Perron boundary.
proof:
  The outer boundary value is \(0\), and the inner value \(\log r\) is
  nonpositive for \(0<r\le 1\).
-/
theorem annularLogBoundaryData_nonpositive_of_closedRadius_le_one
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    (hR_le_one : D.closedRadius ≤ 1) :
    ∀ x ∈ (annularPerronDomain Ω D hD_subset hnonempty).boundary,
      annularLogBoundaryData Ω D hD_subset hnonempty x ≤ 0 := by
  intro x hx
  have hlog_nonpos : Real.log D.closedRadius ≤ 0 :=
    Real.log_nonpos D.closedRadius_pos.le hR_le_one
  have hmax :
      max 0 (Real.log D.closedRadius) = 0 :=
    max_eq_left hlog_nonpos
  simpa [hmax] using
    annularLogBoundaryData_le_boundary_max Ω D hD_subset hnonempty x hx

/--
%%handwave
name:
  Annular Perron solution
statement:
  The logarithmic annular boundary value has a harmonic Perron solution on
  the corresponding annulus.
proof:
  The annulus is a smooth boundary domain, hence Perron-regular once it has
  the componentwise geometry needed for the maximum principle.  Apply the
  ordinary Perron Dirichlet theorem for smooth boundary domains.
-/
theorem annularPerron_dirichlet_solution
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty) :
    ∃ u : X → ℝ,
      SolvesHarmonicDirichletProblem
        (annularPerronDomain Ω D hD_subset hnonempty)
        (annularLogBoundaryData Ω D hD_subset hnonempty) u := by
  exact
    perron_dirichlet_solution_on_smooth_boundary_domain
      (smoothBoundaryDomainRemoveClosedCoordinateDisk Ω D hD_subset hnonempty)
      (annularPerronDomain_hasComponentwiseMaximumPrincipleGeometry
        Ω D hD_subset hnonempty)
      (annularLogBoundaryData Ω D hD_subset hnonempty)

/--
%%handwave
name:
  Annular Perron solutions vanish on the outer boundary
statement:
  A solution of the logarithmic annular Dirichlet problem is zero on the
  original boundary of the smooth domain.
proof:
  The original boundary is part of the annular Perron boundary, and the
  logarithmic boundary datum is zero on that component.
-/
theorem annularPerron_solution_eq_zero_on_outer_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    {u : X → ℝ}
    (hu :
      SolvesHarmonicDirichletProblem
        (annularPerronDomain Ω D hD_subset hnonempty)
        (annularLogBoundaryData Ω D hD_subset hnonempty) u)
    {x : X} (hx : x ∈ Ω.boundary) :
    u x = 0 := by
  have hx_annular :
      x ∈ (annularPerronDomain Ω D hD_subset hnonempty).boundary :=
    outer_boundary_subset_annularPerronDomain_boundary
      Ω D hD_subset hnonempty hx
  have hboundary :
      u x = annularLogBoundaryData Ω D hD_subset hnonempty x :=
    hu.2.2 x hx_annular
  simpa [annularLogBoundaryData_eq_zero_on_outer_boundary
    Ω D hD_subset hnonempty hx] using hboundary

/--
%%handwave
name:
  Annular Perron solutions take the inner logarithmic value
statement:
  On any point of the annular boundary lying on the deleted coordinate
  circle, a solution of the logarithmic annular Dirichlet problem has value
  equal to the logarithm of the deleted radius.
proof:
  The solution assumes the prescribed Dirichlet boundary data on the annular
  boundary, and that boundary datum is the constant logarithmic radius on the
  deleted coordinate circle.
-/
theorem annularPerron_solution_eq_log_on_inner_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    {u : X → ℝ}
    (hu :
      SolvesHarmonicDirichletProblem
        (annularPerronDomain Ω D hD_subset hnonempty)
        (annularLogBoundaryData Ω D hD_subset hnonempty) u)
    {x : X}
    (hx_boundary :
      x ∈ (annularPerronDomain Ω D hD_subset hnonempty).boundary)
    (hx_inner : x ∈ D.boundaryCircle) :
    u x = Real.log D.closedRadius := by
  have hboundary :
      u x = annularLogBoundaryData Ω D hD_subset hnonempty x :=
    hu.2.2 x hx_boundary
  simpa [annularLogBoundaryData_eq_log_on_boundaryCircle
    Ω D hD_subset hnonempty hx_inner] using hboundary

/--
%%handwave
name:
  Annular Perron solutions are bounded above by the larger boundary level
statement:
  A logarithmic annular Perron solution is bounded above throughout the
  annulus by the larger of \(0\) and the inner logarithmic boundary value.
proof:
  Apply the harmonic maximum principle for Dirichlet solutions using the
  upper boundary bound for the logarithmic annular data.
-/
theorem annularPerron_solution_le_boundary_max
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    {u : X → ℝ}
    (hu :
      SolvesHarmonicDirichletProblem
        (annularPerronDomain Ω D hD_subset hnonempty)
        (annularLogBoundaryData Ω D hD_subset hnonempty) u) :
    ∀ x ∈ (annularPerronDomain Ω D hD_subset hnonempty).carrier,
      u x ≤ max 0 (Real.log D.closedRadius) := by
  exact solvesHarmonicDirichletProblem_le_of_boundary_le hu
    (annularPerronDomain_hasComponentwiseMaximumPrincipleGeometry
      Ω D hD_subset hnonempty)
    (annularLogBoundaryData_le_boundary_max Ω D hD_subset hnonempty)

/--
%%handwave
name:
  Small-radius annular Perron solutions are nonpositive
statement:
  If the inner coordinate radius is at most \(1\), then every logarithmic
  annular Perron solution is nonpositive throughout the annulus.
proof:
  The boundary data are nonpositive, and the harmonic maximum principle
  propagates this upper bound to the interior.
-/
theorem annularPerron_solution_nonpositive_of_closedRadius_le_one
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    (hR_le_one : D.closedRadius ≤ 1)
    {u : X → ℝ}
    (hu :
      SolvesHarmonicDirichletProblem
        (annularPerronDomain Ω D hD_subset hnonempty)
        (annularLogBoundaryData Ω D hD_subset hnonempty) u) :
    ∀ x ∈ (annularPerronDomain Ω D hD_subset hnonempty).carrier,
      u x ≤ 0 := by
  exact solvesHarmonicDirichletProblem_le_of_boundary_le hu
    (annularPerronDomain_hasComponentwiseMaximumPrincipleGeometry
      Ω D hD_subset hnonempty)
    (annularLogBoundaryData_nonpositive_of_closedRadius_le_one
      Ω D hD_subset hnonempty hR_le_one)

/--
%%handwave
name:
  Annular Perron solutions are bounded below by the smaller boundary level
statement:
  A logarithmic annular Perron solution is bounded below throughout the
  annulus by the smaller of \(0\) and the inner logarithmic boundary value.
proof:
  Apply the harmonic maximum principle for Dirichlet solutions using the
  lower boundary bound for the logarithmic annular data.
-/
theorem boundary_min_le_annularPerron_solution
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    {u : X → ℝ}
    (hu :
      SolvesHarmonicDirichletProblem
        (annularPerronDomain Ω D hD_subset hnonempty)
        (annularLogBoundaryData Ω D hD_subset hnonempty) u) :
    ∀ x ∈ (annularPerronDomain Ω D hD_subset hnonempty).carrier,
      min (Real.log D.closedRadius) 0 ≤ u x := by
  exact le_solvesHarmonicDirichletProblem_of_boundary_le hu
    (annularPerronDomain_hasComponentwiseMaximumPrincipleGeometry
      Ω D hD_subset hnonempty)
    (boundary_min_le_annularLogBoundaryData Ω D hD_subset hnonempty)

/-- The harmonic measure normalized to be one on the inner coordinate circle. -/
noncomputable def annularPerronUnitHarmonicMeasure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : ClosedCoordinateDisk X) (u : X → ℝ) : X → ℝ :=
  fun x ↦ u x / Real.log D.closedRadius

/--
%%handwave
name:
  Normalized annular harmonic measure lies between zero and one
statement:
  Suppose the inner radius of an annular logarithmic Dirichlet problem is
  strictly less than one.  Dividing its solution by the logarithm of that
  radius gives a harmonic function with values in $[0,1]$ throughout the
  annulus.
proof:
  The original solution lies between the two boundary levels
  $\log r<0$ and $0$.  Division by the negative number $\log r$ reverses
  the inequalities.
-/
theorem annularPerronUnitHarmonicMeasure_mem_Icc
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    (hR_lt_one : D.closedRadius < 1)
    {u : X → ℝ}
    (hu :
      SolvesHarmonicDirichletProblem
        (annularPerronDomain Ω D hD_subset hnonempty)
        (annularLogBoundaryData Ω D hD_subset hnonempty) u) :
    ∀ x ∈ (annularPerronDomain Ω D hD_subset hnonempty).carrier,
      annularPerronUnitHarmonicMeasure D u x ∈ Set.Icc 0 1 := by
  have hlog_neg : Real.log D.closedRadius < 0 :=
    Real.log_neg D.closedRadius_pos hR_lt_one
  intro x hx
  have hu_nonpos : u x ≤ 0 :=
    annularPerron_solution_nonpositive_of_closedRadius_le_one
      Ω D hD_subset hnonempty hR_lt_one.le hu x hx
  have hlog_le_u : Real.log D.closedRadius ≤ u x := by
    have hmin :=
      boundary_min_le_annularPerron_solution
        Ω D hD_subset hnonempty hu x hx
    simpa [min_eq_left hlog_neg.le] using hmin
  constructor
  · exact div_nonneg_of_nonpos hu_nonpos hlog_neg.le
  · apply (div_le_iff_of_neg hlog_neg).2
    simpa using hlog_le_u

/--
%%handwave
name:
  Normalized harmonic measure is strictly below one on an outer coordinate circle
statement:
  Let a relatively compact smooth domain lie in a noncompact connected
  Riemann surface, and let an inner coordinate disk and its ambient coordinate
  disk lie in the domain.  If the inner radius is less than one, then the
  normalized annular harmonic measure is strictly below one on every larger
  coordinate circle still inside the ambient disk.
proof:
  Removing the inner disk from the component containing it leaves a connected
  region by coordinate-circle path surgery.  If the normalized harmonic
  measure attained one on the larger circle, the strong maximum principle
  would make it identically one on that region.  Continuity would propagate
  this value to the outer frontier of the relatively compact component, where
  the Dirichlet value is zero, a contradiction.
-/
theorem annularPerronUnitHarmonicMeasure_lt_one_on_radiusBoundaryCircle
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hnoncompact : ¬ CompactSpace X)
    (Ω : SmoothBoundaryDomain X) {p : X} (hpΩ : p ∈ Ω.carrier)
    (D : ClosedCoordinateDisk X) (hpD : p ∈ D.carrier)
    (hopenDisk_subset : D.openDisk.carrier ⊆ Ω.carrier)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    (hR_lt_one : D.closedRadius < 1)
    {u : X → ℝ}
    (hu :
      SolvesHarmonicDirichletProblem
        (annularPerronDomain Ω D hD_subset hnonempty)
        (annularLogBoundaryData Ω D hD_subset hnonempty) u)
    {ρ : ℝ} (hDρ : D.closedRadius < ρ)
    (hρ_open : ρ < D.openDisk.radius) :
    ∀ x ∈ D.radiusBoundaryCircle ρ,
      annularPerronUnitHarmonicMeasure D u x < 1 := by
  let A : PerronDomain X := annularPerronDomain Ω D hD_subset hnonempty
  let k : X → ℝ := annularPerronUnitHarmonicMeasure D u
  let S : Set X := connectedComponentIn Ω.carrier p
  let C : Set X := S \ D.carrier
  have hp_openDisk : p ∈ D.openDisk.carrier := D.subset_openDisk hpD
  have hopenDiskS : D.openDisk.carrier ⊆ S := by
    dsimp [S]
    exact D.openDisk.isPathConnected.isConnected.isPreconnected.subset_connectedComponentIn
      hp_openDisk hopenDisk_subset
  have hS_open : IsOpen S := by
    dsimp [S]
    exact Ω.isOpen.connectedComponentIn
  have hpS : p ∈ S := by
    dsimp [S]
    exact mem_connectedComponentIn hpΩ
  have hS_path : IsPathConnected S :=
    (hS_open.isConnected_iff_isPathConnected).mp
      ⟨⟨p, hpS⟩, isPreconnected_connectedComponentIn⟩
  have hC_open : IsOpen C := by
    dsimp [C]
    exact hS_open.sdiff (ClosedCoordinateDisk.isClosed D)
  have hC_preconnected : IsPreconnected C := by
    dsimp [C]
    exact isPreconnected_diff_closedCoordinateDisk_of_forall_joinedIn
      D S hopenDiskS (fun x hx y hy ↦ hS_path.joinedIn x hx y hy)
  have hS_subsetΩ : S ⊆ Ω.carrier := by
    dsimp [S]
    exact connectedComponentIn_subset Ω.carrier p
  have hC_subset_A : C ⊆ A.carrier := by
    intro y hy
    change y ∈ Ω.carrier \ D.carrier
    exact ⟨hS_subsetΩ hy.1, hy.2⟩
  have hk_harmonic : IsHarmonicOnSurface C k := by
    have hscaled :
        IsHarmonicOnSurface A.carrier
          (fun y ↦ (Real.log D.closedRadius)⁻¹ * u y) :=
      harmonicOnSurface_const_mul (Real.log D.closedRadius)⁻¹ hu.1
    apply harmonicOnSurface_mono hC_subset_A
    simpa [k, annularPerronUnitHarmonicMeasure, div_eq_mul_inv,
      mul_comm] using hscaled
  have hk_le_one : ∀ y ∈ C, k y ≤ 1 := by
    intro y hy
    exact
      (annularPerronUnitHarmonicMeasure_mem_Icc
        Ω D hD_subset hnonempty hR_lt_one hu y (hC_subset_A hy)).2
  have hS_compact : IsCompact (closure S) :=
    Ω.compact_closure.of_isClosed_subset isClosed_closure
      (closure_mono hS_subsetΩ)
  have hS_ne_univ : S ≠ Set.univ := by
    intro hS_univ
    have huniv_compact : IsCompact (Set.univ : Set X) := by
      simpa [hS_univ] using hS_compact
    exact hnoncompact (isCompact_univ_iff.mp huniv_compact)
  have hfrontierS_nonempty : (frontier S).Nonempty :=
    (nonempty_frontier_iff).2 ⟨⟨p, hpS⟩, hS_ne_univ⟩
  intro x hx_circle
  have hx_openDisk : x ∈ D.openDisk.carrier := by
    rw [D.openDisk.carrier_eq]
    refine ⟨hx_circle.1, ?_⟩
    exact Metric.sphere_subset_ball hρ_open hx_circle.2
  have hxC : x ∈ C := by
    exact ⟨hopenDiskS hx_openDisk,
      D.radiusBoundaryCircle_subset_compl_carrier hDρ hx_circle⟩
  have hkx_le : k x ≤ 1 := hk_le_one x hxC
  by_contra hnot_lt
  have hkx_eq : k x = 1 := le_antisymm hkx_le (le_of_not_gt hnot_lt)
  have hk_max : IsMaxOn k C x := by
    intro y hy
    simpa [hkx_eq] using hk_le_one y hy
  have hk_eq : Set.EqOn k (fun _ ↦ k x) C :=
    harmonicOnSurface_eqOn_of_isPreconnected_of_isMaxOn
      hC_open hC_preconnected hk_harmonic hxC hk_max
  rcases hfrontierS_nonempty with ⟨y, hy_frontierS⟩
  have hy_notS : y ∉ S := by
    intro hyS
    have hy_empty : y ∈ S ∩ frontier S := ⟨hyS, hy_frontierS⟩
    simp [hS_open.inter_frontier_eq] at hy_empty
  have hy_outer : y ∈ Ω.boundary := by
    change y ∈ frontier Ω.carrier
    have hy_closureΩ : y ∈ closure Ω.carrier :=
      closure_mono hS_subsetΩ (frontier_subset_closure hy_frontierS)
    have hy_notΩ : y ∉ Ω.carrier := by
      intro hyΩ
      have hyS : y ∈ S := by
        dsimp [S]
        exact mem_connectedComponentIn_of_mem_closure_of_mem hpΩ hyΩ
          (frontier_subset_closure hy_frontierS)
      exact hy_notS hyS
    rw [frontier, Ω.isOpen.interior_eq]
    exact ⟨hy_closureΩ, hy_notΩ⟩
  have hy_notD : y ∈ D.carrierᶜ := by
    intro hyD
    exact hy_notS (hopenDiskS (D.subset_openDisk hyD))
  have hy_closureC : y ∈ closure C := by
    rw [mem_closure_iff_nhds]
    intro N hN
    have hy_closureS : y ∈ closure S := frontier_subset_closure hy_frontierS
    rw [mem_closure_iff_nhds] at hy_closureS
    have hDcompl : D.carrierᶜ ∈ 𝓝 y :=
      (ClosedCoordinateDisk.isClosed D).isOpen_compl.mem_nhds hy_notD
    rcases hy_closureS (N ∩ D.carrierᶜ) (Filter.inter_mem hN hDcompl) with
      ⟨z, hz, hzS⟩
    exact ⟨z, hz.1, hzS, hz.2⟩
  have hk_cont_A : ContinuousOn k (closure A.carrier) := by
    simpa [k, annularPerronUnitHarmonicMeasure] using
      hu.2.1.div_const (Real.log D.closedRadius)
  have hk_cont_C : ContinuousOn k (closure C) :=
    hk_cont_A.mono (closure_mono hC_subset_A)
  have hk_eq_closure : Set.EqOn k (fun _ ↦ k x) (closure C) :=
    hk_eq.of_subset_closure hk_cont_C continuousOn_const
      subset_closure subset_rfl
  have hky_one : k y = 1 := by
    simpa [hkx_eq] using hk_eq_closure hy_closureC
  have huy_zero : u y = 0 :=
    annularPerron_solution_eq_zero_on_outer_boundary
      Ω D hD_subset hnonempty hu hy_outer
  have hky_zero : k y = 0 := by
    simp [k, annularPerronUnitHarmonicMeasure, huy_zero]
  linarith

/--
%%handwave
name:
  Uniform outer-circle bound for normalized harmonic measure
statement:
  Under the hypotheses of the strict outer-circle estimate, there is a
  number $a<1$ which bounds the normalized harmonic measure on the whole
  outer coordinate circle.
proof:
  The coordinate circle is nonempty and compact.  The normalized harmonic
  measure is continuous there, so it attains a maximum; the pointwise strict
  estimate says that this maximum is below one.
-/
theorem exists_annularPerronUnitHarmonicMeasure_outerCircle_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hnoncompact : ¬ CompactSpace X)
    (Ω : SmoothBoundaryDomain X) {p : X} (hpΩ : p ∈ Ω.carrier)
    (D : ClosedCoordinateDisk X) (hpD : p ∈ D.carrier)
    (hopenDisk_subset : D.openDisk.carrier ⊆ Ω.carrier)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    (hR_lt_one : D.closedRadius < 1)
    {u : X → ℝ}
    (hu :
      SolvesHarmonicDirichletProblem
        (annularPerronDomain Ω D hD_subset hnonempty)
        (annularLogBoundaryData Ω D hD_subset hnonempty) u)
    {ρ : ℝ} (hDρ : D.closedRadius < ρ)
    (hρ_open : ρ < D.openDisk.radius) :
    ∃ a : ℝ, a < 1 ∧
      ∀ x ∈ D.radiusBoundaryCircle ρ,
        annularPerronUnitHarmonicMeasure D u x ≤ a := by
  let A : PerronDomain X := annularPerronDomain Ω D hD_subset hnonempty
  let k : X → ℝ := annularPerronUnitHarmonicMeasure D u
  have hcircle_compact : IsCompact (D.radiusBoundaryCircle ρ) :=
    D.radiusBoundaryCircle_isCompact hρ_open
  have hcircle_nonempty : (D.radiusBoundaryCircle ρ).Nonempty :=
    D.radiusBoundaryCircle_nonempty (D.closedRadius_pos.trans hDρ).le hρ_open
  have hcircle_subset_A : D.radiusBoundaryCircle ρ ⊆ A.carrier := by
    intro x hx
    have hx_openDisk : x ∈ D.openDisk.carrier := by
      rw [D.openDisk.carrier_eq]
      exact ⟨hx.1, Metric.sphere_subset_ball hρ_open hx.2⟩
    change x ∈ Ω.carrier \ D.carrier
    exact ⟨hopenDisk_subset hx_openDisk,
      D.radiusBoundaryCircle_subset_compl_carrier hDρ hx⟩
  have hk_cont : ContinuousOn k (D.radiusBoundaryCircle ρ) := by
    have hk_cont_A : ContinuousOn k (closure A.carrier) := by
      simpa [k, annularPerronUnitHarmonicMeasure] using
        hu.2.1.div_const (Real.log D.closedRadius)
    exact hk_cont_A.mono (fun x hx ↦ subset_closure (hcircle_subset_A hx))
  rcases hcircle_compact.exists_isMaxOn hcircle_nonempty hk_cont with
    ⟨x, hx_circle, hx_max⟩
  refine ⟨k x, ?_, ?_⟩
  · exact annularPerronUnitHarmonicMeasure_lt_one_on_radiusBoundaryCircle
      hnoncompact Ω hpΩ D hpD hopenDisk_subset hD_subset hnonempty
      hR_lt_one hu hDρ hρ_open x hx_circle
  · intro y hy
    exact hx_max hy

/--
%%handwave
name:
  Hubbard barrier constants
statement:
  If $0<r<R$ and $a<1$, then there are constants $B>0$ and $A$ such that
  $aB<A-\log R$ and $A-\log r<B$.
proof:
  Choose $B$ so large that
  $(1-a)B>\log R-\log r$.  The two desired inequalities then leave a
  nonempty open interval for $A$, and its midpoint is a valid choice.
-/
theorem exists_hubbard_barrier_constants
    {r R a : ℝ} (hr : 0 < r) (hrR : r < R) (ha : a < 1) :
    ∃ A B : ℝ, 0 < B ∧ a * B < A - Real.log R ∧
      A - Real.log r < B := by
  let d : ℝ := Real.log R - Real.log r
  have hd : 0 < d := by
    dsimp [d]
    exact sub_pos.mpr (Real.log_lt_log hr hrR)
  have hden : 0 < 1 - a := sub_pos.mpr ha
  let B : ℝ := (d + 1) / (1 - a)
  have hB : 0 < B := div_pos (by linarith) hden
  have hB_identity : (1 - a) * B = d + 1 := by
    dsimp [B]
    field_simp
  let L : ℝ := a * B + Real.log R
  let U : ℝ := B + Real.log r
  have hLU : L < U := by
    have hdiff : U - L = (1 - a) * B - d := by
      dsimp [L, U, d]
      ring
    have hdiff_pos : 0 < U - L := by
      rw [hdiff, hB_identity]
      linarith
    linarith
  let A : ℝ := (L + U) / 2
  have hLA : L < A := by
    dsimp [A]
    linarith
  have hAU : A < U := by
    dsimp [A]
    linarith
  refine ⟨A, B, hB, ?_, ?_⟩
  · dsimp [L] at hLA
    linarith
  · dsimp [U] at hAU
    linarith

/-- The logarithmic branch used in Hubbard's annular barrier. -/
noncomputable def closedCoordinateDiskLogarithmicModel
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : ClosedCoordinateDisk X) (A : ℝ) : X → ℝ :=
  fun x ↦ A - Real.log ‖D.openDisk.chart x - D.openDisk.center‖

/-- The outer minimum paste in Hubbard's annular barrier. -/
noncomputable def hubbardOuterAnnularPerronBarrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : ClosedCoordinateDisk X) (ρ : ℝ) (u : X → ℝ) (A B : ℝ) : X → ℝ :=
  superharmonicInfPaste (D.expandedOpenDisk ρ)
    (fun x ↦ B * annularPerronUnitHarmonicMeasure D u x)
    (closedCoordinateDiskLogarithmicModel D A)

/--
%%handwave
name:
  Hubbard's outer minimum paste
statement:
  Let $k_1$ be the normalized harmonic measure of a fixed annular Dirichlet
  problem.  Suppose $k_1\le a<1$ on a larger coordinate circle and choose
  $B>0$ and $A$ with $aB<A-\log R$.  Then the function obtained by taking
  $\min\{Bk_1,A-\log|z|\}$ inside that circle and $Bk_1$ outside it is
  continuous and superharmonic on the fixed annular domain.
proof:
  Both entries of the minimum are harmonic on the overlap.  On the gluing
  circle the numerical inequality makes $Bk_1$ no larger than the logarithmic
  branch.  Minimum contact pasting therefore gives both continuity and
  superharmonicity.
-/
theorem hubbardOuterAnnularPerronBarrier_continuous_superharmonic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) {p : X}
    (D : ClosedCoordinateDisk X) (hpD : p ∈ D.carrier)
    (hp_interior : p ∈ interior D.carrier)
    (hcenter : D.openDisk.center = D.openDisk.chart p)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    {u : X → ℝ}
    (hu :
      SolvesHarmonicDirichletProblem
        (annularPerronDomain Ω D hD_subset hnonempty)
        (annularLogBoundaryData Ω D hD_subset hnonempty) u)
    {ρ a A B : ℝ}
    (hρ_open : ρ < D.openDisk.radius)
    (hcircle_bound :
      ∀ x ∈ D.radiusBoundaryCircle ρ,
        annularPerronUnitHarmonicMeasure D u x ≤ a)
    (hB : 0 < B) (houter : a * B < A - Real.log ρ) :
    ContinuousOn (hubbardOuterAnnularPerronBarrier D ρ u A B)
        (closure (annularPerronDomain Ω D hD_subset hnonempty).carrier) ∧
      IsSuperharmonicOnSurface
        (annularPerronDomain Ω D hD_subset hnonempty).carrier
        (hubbardOuterAnnularPerronBarrier D ρ u A B) := by
  let P : PerronDomain X := annularPerronDomain Ω D hD_subset hnonempty
  let V : Set X := D.expandedOpenDisk ρ
  let k : X → ℝ := annularPerronUnitHarmonicMeasure D u
  let L : X → ℝ := closedCoordinateDiskLogarithmicModel D A
  let w : X → ℝ := hubbardOuterAnnularPerronBarrier D ρ u A B
  have hp_source : p ∈ D.openDisk.chart.source := by
    have hp_open := D.subset_openDisk hpD
    rw [D.openDisk.carrier_eq] at hp_open
    exact hp_open.1
  have hV_open : IsOpen V := D.expandedOpenDisk_isOpen ρ
  have hV_compact_closed : IsCompact (D.expandedClosedDisk ρ) :=
    D.expandedClosedDisk_compact hρ_open
  have hclosureV_subset_closed :
      closure V ⊆ D.expandedClosedDisk ρ :=
    closure_minimal (D.expandedOpenDisk_subset_expandedClosedDisk ρ)
      hV_compact_closed.isClosed
  have hclosureV_source : closure V ⊆ D.openDisk.chart.source := by
    intro x hx
    exact (hclosureV_subset_closed hx).1
  have hP_subset_compl_interior :
      P.carrier ⊆ (interior D.carrier)ᶜ := by
    intro x hx hxint
    have hx' : x ∈ Ω.carrier \ D.carrier := by
      simpa [P, annularPerronDomain_carrier] using hx
    exact hx'.2 (interior_subset hxint)
  have hclosureP_subset_compl_interior :
      closure P.carrier ⊆ (interior D.carrier)ᶜ :=
    closure_minimal hP_subset_compl_interior isOpen_interior.isClosed_compl
  have hclosureP_punctured : closure P.carrier ⊆ {x : X | x ≠ p} := by
    intro x hx hxp
    exact hclosureP_subset_compl_interior hx (by simpa [hxp] using hp_interior)
  have hk_cont : ContinuousOn k (closure P.carrier) := by
    simpa [k, annularPerronUnitHarmonicMeasure] using
      hu.2.1.div_const (Real.log D.closedRadius)
  have hk_harm : IsHarmonicOnSurface P.carrier k := by
    have hscaled :
        IsHarmonicOnSurface P.carrier
          (fun x ↦ (Real.log D.closedRadius)⁻¹ * u x) :=
      harmonicOnSurface_const_mul (Real.log D.closedRadius)⁻¹ hu.1
    simpa [k, annularPerronUnitHarmonicMeasure, div_eq_mul_inv,
      mul_comm] using hscaled
  have hBk_cont : ContinuousOn (fun x ↦ B * k x) (closure P.carrier) :=
    continuousOn_const.mul hk_cont
  have hBk_harm : IsHarmonicOnSurface P.carrier (fun x ↦ B * k x) :=
    harmonicOnSurface_const_mul B hk_harm
  have hL_cont : ContinuousOn L (closure P.carrier ∩ closure V) := by
    have hsource : closure P.carrier ∩ closure V ⊆ D.openDisk.chart.source :=
      fun x hx ↦ hclosureV_source hx.2
    have hchart :
        ContinuousOn D.openDisk.chart (closure P.carrier ∩ closure V) :=
      D.openDisk.chart.continuousOn.mono hsource
    have hnorm :
        ContinuousOn
          (fun x : X ↦ ‖D.openDisk.chart x - D.openDisk.center‖)
          (closure P.carrier ∩ closure V) :=
      (hchart.sub continuousOn_const).norm
    have hnorm_ne :
        ∀ x ∈ closure P.carrier ∩ closure V,
          ‖D.openDisk.chart x - D.openDisk.center‖ ≠ 0 := by
      intro x hx hzero
      have hchart_eq : D.openDisk.chart x = D.openDisk.center :=
        sub_eq_zero.mp (norm_eq_zero.mp hzero)
      have hxp : x = p := by
        apply D.openDisk.chart.injOn (hsource hx) hp_source
        simpa [hcenter] using hchart_eq
      exact (hclosureP_punctured hx.1) hxp
    simpa [L, closedCoordinateDiskLogarithmicModel] using
      continuousOn_const.sub (hnorm.log hnorm_ne)
  have hL_harm : IsHarmonicOnSurface (P.carrier ∩ V) L := by
    have hsource : P.carrier ∩ V ⊆ D.openDisk.chart.source := by
      intro x hx
      exact hx.2.1
    have havoid :
        ∀ x ∈ P.carrier ∩ V,
          D.openDisk.chart x ≠ D.openDisk.center := by
      intro x hx hEq
      have hxp : x = p := by
        apply D.openDisk.chart.injOn (hsource hx) hp_source
        simpa [hcenter] using hEq
      have hxP : x ∈ Ω.carrier \ D.carrier := by
        simpa [P, annularPerronDomain_carrier] using hx.1
      exact hxP.2 (by simpa [hxp] using hpD)
    have hlog :=
      coordinateLogDistance_harmonicOnSurface D.openDisk.chart
        D.openDisk.chart_mem_atlas hsource havoid
    simpa [L, closedCoordinateDiskLogarithmicModel] using
      harmonicOnSurface_sub
        (harmonicOnSurface_const (P.carrier ∩ V) A) hlog
  have hcontact :
      ∀ x ∈ closure P.carrier ∩ frontier V, B * k x ≤ L x := by
    intro x hx
    have hx_circle : x ∈ D.radiusBoundaryCircle ρ :=
      D.frontier_expandedOpenDisk_subset_radiusBoundaryCircle
        hρ_open hx.2
    have hkxa : k x ≤ a := hcircle_bound x hx_circle
    have hscaled : B * k x ≤ B * a :=
      mul_le_mul_of_nonneg_left hkxa hB.le
    have hnorm : ‖D.openDisk.chart x - D.openDisk.center‖ = ρ := by
      simpa [ClosedCoordinateDisk.radiusBoundaryCircle, Metric.mem_sphere,
        dist_eq_norm] using
        hx_circle.2
    dsimp [L, closedCoordinateDiskLogarithmicModel]
    rw [hnorm]
    nlinarith
  have hw_cont : ContinuousOn w (closure P.carrier) := by
    have := continuousOn_superharmonicInfPaste_of_boundary_le
      hBk_cont hL_cont hcontact
    simpa [w, hubbardOuterAnnularPerronBarrier, V, k, L] using this
  have hw_super : IsSuperharmonicOnSurface P.carrier w := by
    have hBk_super :
        IsSuperharmonicOnSurface P.carrier (fun x ↦ B * k x) :=
      harmonicOnSurface_superharmonic P.isOpen hBk_harm
    have hL_super : IsSuperharmonicOnSurface (P.carrier ∩ V) L :=
      harmonicOnSurface_superharmonic (P.isOpen.inter hV_open) hL_harm
    have hcontact' :
        ∀ x ∈ P.carrier ∩ frontier V, B * k x ≤ L x :=
      fun x hx ↦ hcontact x ⟨subset_closure hx.1, hx.2⟩
    have := superharmonicOnSurface_inf_paste_of_boundary_le
      hV_open (hBk_cont.mono subset_closure)
      (hL_cont.mono (fun x hx ↦ ⟨subset_closure hx.1, hx.2⟩))
      hBk_super hL_super hcontact'
    simpa [w, hubbardOuterAnnularPerronBarrier, V, k, L] using this
  exact ⟨hw_cont, hw_super⟩

/-- Hubbard's logarithmic barrier after the inner logarithmic branch is pasted in. -/
noncomputable def hubbardAnnularPerronBarrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : ClosedCoordinateDisk X) (ρ : ℝ) (u : X → ℝ) (A B : ℝ) : X → ℝ := by
  classical
  exact fun x ↦
    if x ∈ D.carrier then closedCoordinateDiskLogarithmicModel D A x
    else hubbardOuterAnnularPerronBarrier D ρ u A B x

/--
%%handwave
name:
  Hubbard's domain-relative logarithmic barrier
statement:
  Let a fixed coordinate disk around $p$ lie compactly inside a relatively
  compact smooth domain.  Normalize the harmonic function which is one on
  the disk boundary and zero on the outer boundary.  If $A,B$ satisfy the two
  strict seam inequalities from Hubbard's construction, then the function
  which is $A-\log|z|$ inside the disk,
  $\min\{Bk_1,A-\log|z|\}$ in the intervening annulus, and $Bk_1$ outside is
  continuous on the closed punctured domain and superharmonic on the open
  punctured domain.  It has the exact logarithmic model inside and vanishes
  on the outer boundary.
proof:
  The outer seam is the minimum contact paste.  At the inner seam the
  normalized harmonic measure equals one, and
  $A-\log r<B$ makes the logarithmic branch the smaller branch.  A local
  contact-pasting argument across that circle proves superharmonicity;
  continuity follows from the same two contact equalities.
-/
theorem hubbardAnnularPerronBarrier_properties
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) {p : X}
    (D : ClosedCoordinateDisk X) (hpD : p ∈ D.carrier)
    (hp_interior : p ∈ interior D.carrier)
    (hcenter : D.openDisk.center = D.openDisk.chart p)
    (hopenDisk_subset : D.openDisk.carrier ⊆ Ω.carrier)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    (hR_lt_one : D.closedRadius < 1)
    {u : X → ℝ}
    (hu :
      SolvesHarmonicDirichletProblem
        (annularPerronDomain Ω D hD_subset hnonempty)
        (annularLogBoundaryData Ω D hD_subset hnonempty) u)
    {ρ a A B : ℝ}
    (hDρ : D.closedRadius < ρ) (hρ_open : ρ < D.openDisk.radius)
    (hcircle_bound :
      ∀ x ∈ D.radiusBoundaryCircle ρ,
        annularPerronUnitHarmonicMeasure D u x ≤ a)
    (hB : 0 < B) (houter : a * B < A - Real.log ρ)
    (hinner : A - Real.log D.closedRadius < B) :
    ContinuousOn (hubbardAnnularPerronBarrier D ρ u A B)
        (closure Ω.carrier \ {p}) ∧
      IsSuperharmonicOnSurface (Ω.carrier \ {p})
        (hubbardAnnularPerronBarrier D ρ u A B) ∧
      (∀ x ∈ D.carrier, x ≠ p →
        hubbardAnnularPerronBarrier D ρ u A B x =
          closedCoordinateDiskLogarithmicModel D A x) ∧
      (∀ x ∈ Ω.boundary,
        hubbardAnnularPerronBarrier D ρ u A B x = 0) := by
  classical
  let P : PerronDomain X := annularPerronDomain Ω D hD_subset hnonempty
  let V : Set X := D.expandedOpenDisk ρ
  let k : X → ℝ := annularPerronUnitHarmonicMeasure D u
  let L : X → ℝ := closedCoordinateDiskLogarithmicModel D A
  let w : X → ℝ := hubbardOuterAnnularPerronBarrier D ρ u A B
  let b : X → ℝ := hubbardAnnularPerronBarrier D ρ u A B
  let U : Set X := Ω.carrier \ {p}
  let Ucl : Set X := closure Ω.carrier \ {p}
  let G : X → ℝ := superharmonicInfPaste P.carrier L (fun x ↦ B * k x)
  have hlog_neg : Real.log D.closedRadius < 0 :=
    Real.log_neg D.closedRadius_pos hR_lt_one
  have hp_source : p ∈ D.openDisk.chart.source := by
    have hp_open := D.subset_openDisk hpD
    rw [D.openDisk.carrier_eq] at hp_open
    exact hp_open.1
  have hV_open : IsOpen V := D.expandedOpenDisk_isOpen ρ
  have hV_subset_openDisk : V ⊆ D.openDisk.carrier := by
    intro x hx
    change x ∈ D.expandedOpenDisk ρ at hx
    rw [ClosedCoordinateDisk.expandedOpenDisk] at hx
    rw [D.openDisk.carrier_eq]
    exact ⟨hx.1, Metric.ball_subset_ball hρ_open.le hx.2⟩
  have hV_subset_Ω : V ⊆ Ω.carrier := hV_subset_openDisk.trans hopenDisk_subset
  have hD_subset_V : D.carrier ⊆ V := by
    intro x hx
    rw [D.carrier_eq] at hx
    change x ∈ D.expandedOpenDisk ρ
    rw [ClosedCoordinateDisk.expandedOpenDisk]
    exact ⟨hx.1, Metric.closedBall_subset_ball hDρ hx.2⟩
  have hU_open : IsOpen U := Ω.isOpen.sdiff isClosed_singleton
  have hL_cont_of_subset :
      ∀ {T : Set X}, T ⊆ D.openDisk.chart.source →
        T ⊆ {x : X | x ≠ p} → ContinuousOn L T := by
    intro T hT_source hT_punctured
    have hchart : ContinuousOn D.openDisk.chart T :=
      D.openDisk.chart.continuousOn.mono hT_source
    have hnorm :
        ContinuousOn (fun x : X ↦ ‖D.openDisk.chart x - D.openDisk.center‖) T :=
      (hchart.sub continuousOn_const).norm
    have hnorm_ne :
        ∀ x ∈ T, ‖D.openDisk.chart x - D.openDisk.center‖ ≠ 0 := by
      intro x hx hzero
      have hchart_eq : D.openDisk.chart x = D.openDisk.center :=
        sub_eq_zero.mp (norm_eq_zero.mp hzero)
      have hxp : x = p := by
        apply D.openDisk.chart.injOn (hT_source hx) hp_source
        simpa [hcenter] using hchart_eq
      exact (hT_punctured hx) hxp
    simpa [L, closedCoordinateDiskLogarithmicModel] using
      continuousOn_const.sub (hnorm.log hnorm_ne)
  have hL_harm_of_subset :
      ∀ {T : Set X}, T ⊆ D.openDisk.chart.source →
        T ⊆ {x : X | x ≠ p} → IsHarmonicOnSurface T L := by
    intro T hT_source hT_punctured
    have havoid :
        ∀ x ∈ T, D.openDisk.chart x ≠ D.openDisk.center := by
      intro x hx hEq
      have hxp : x = p := by
        apply D.openDisk.chart.injOn (hT_source hx) hp_source
        simpa [hcenter] using hEq
      exact (hT_punctured hx) hxp
    have hlog :=
      coordinateLogDistance_harmonicOnSurface D.openDisk.chart
        D.openDisk.chart_mem_atlas hT_source havoid
    simpa [L, closedCoordinateDiskLogarithmicModel] using
      harmonicOnSurface_sub (harmonicOnSurface_const T A) hlog
  have hk_cont : ContinuousOn k (closure P.carrier) := by
    simpa [k, annularPerronUnitHarmonicMeasure] using
      hu.2.1.div_const (Real.log D.closedRadius)
  have hk_harm : IsHarmonicOnSurface P.carrier k := by
    have hscaled :
        IsHarmonicOnSurface P.carrier
          (fun x ↦ (Real.log D.closedRadius)⁻¹ * u x) :=
      harmonicOnSurface_const_mul (Real.log D.closedRadius)⁻¹ hu.1
    simpa [k, annularPerronUnitHarmonicMeasure, div_eq_mul_inv,
      mul_comm] using hscaled
  have hBk_cont : ContinuousOn (fun x ↦ B * k x) (closure P.carrier) :=
    continuousOn_const.mul hk_cont
  have hBk_harm : IsHarmonicOnSurface P.carrier (fun x ↦ B * k x) :=
    harmonicOnSurface_const_mul B hk_harm
  rcases hubbardOuterAnnularPerronBarrier_continuous_superharmonic
      Ω D hpD hp_interior hcenter hD_subset hnonempty hu
      hρ_open hcircle_bound hB houter with
    ⟨hw_cont, hw_super⟩
  have hinner_boundary_contact :
      ∀ x ∈ (Ucl ∩ V) ∩ frontier P.carrier, L x ≤ B * k x := by
    intro x hx
    have hx_boundary : x ∈ P.boundary := by
      simpa [P, PerronDomain.boundary] using hx.2
    rcases annularPerronDomain_boundary_subset_outer_or_inner
        Ω D hD_subset hnonempty hx_boundary with hx_outer | hx_inner
    · have hxΩ : x ∈ Ω.carrier := hV_subset_Ω hx.1.2
      have hx_empty : x ∈ Ω.carrier ∩ frontier Ω.carrier :=
        ⟨hxΩ, by simpa [SmoothBoundaryDomain.boundary] using hx_outer⟩
      simp [Ω.isOpen.inter_frontier_eq] at hx_empty
    · have hu_log : u x = Real.log D.closedRadius :=
        annularPerron_solution_eq_log_on_inner_boundary
          Ω D hD_subset hnonempty hu hx_boundary hx_inner
      have hk_one : k x = 1 := by
        dsimp [k, annularPerronUnitHarmonicMeasure]
        rw [hu_log]
        exact div_self hlog_neg.ne
      have hnorm :
          ‖D.openDisk.chart x - D.openDisk.center‖ = D.closedRadius := by
        simpa [ClosedCoordinateDisk.boundaryCircle, Metric.mem_sphere,
          dist_eq_norm] using
          hx_inner.2
      dsimp [L, closedCoordinateDiskLogarithmicModel]
      rw [hnorm, hk_one]
      nlinarith
  have hG_cont : ContinuousOn G (Ucl ∩ V) := by
    have hL_cont : ContinuousOn L (Ucl ∩ V) :=
      hL_cont_of_subset
        (fun x hx ↦ (by
          have hxV : x ∈ D.expandedOpenDisk ρ := hx.2
          rw [ClosedCoordinateDisk.expandedOpenDisk] at hxV
          exact hxV.1))
        (fun x hx ↦ hx.1.2)
    have hBk_cont' :
        ContinuousOn (fun x ↦ B * k x) ((Ucl ∩ V) ∩ closure P.carrier) :=
      hBk_cont.mono (fun x hx ↦ hx.2)
    have := continuousOn_superharmonicInfPaste_of_boundary_le
      hL_cont hBk_cont' hinner_boundary_contact
    simpa [G] using this
  have hG_super : IsSuperharmonicOnSurface (U ∩ V) G := by
    have hL_harm : IsHarmonicOnSurface (U ∩ V) L :=
      hL_harm_of_subset
        (fun x hx ↦ (by
          have hxV : x ∈ D.expandedOpenDisk ρ := hx.2
          rw [ClosedCoordinateDisk.expandedOpenDisk] at hxV
          exact hxV.1))
        (fun x hx ↦ hx.1.2)
    have hL_super : IsSuperharmonicOnSurface (U ∩ V) L :=
      harmonicOnSurface_superharmonic (hU_open.inter hV_open) hL_harm
    have hBk_super :
        IsSuperharmonicOnSurface ((U ∩ V) ∩ P.carrier) (fun x ↦ B * k x) :=
      harmonicOnSurface_superharmonic
        ((hU_open.inter hV_open).inter P.isOpen)
        (harmonicOnSurface_mono (fun x hx ↦ hx.2) hBk_harm)
    have hcontact :
        ∀ x ∈ (U ∩ V) ∩ frontier P.carrier, L x ≤ B * k x := by
      intro x hx
      apply hinner_boundary_contact x
      refine ⟨⟨?_, hx.1.2⟩, hx.2⟩
      change x ∈ closure Ω.carrier \ {p}
      exact ⟨subset_closure hx.1.1.1, hx.1.1.2⟩
    have hBk_cont' :
        ContinuousOn (fun x ↦ B * k x) ((U ∩ V) ∩ closure P.carrier) :=
      hBk_cont.mono (fun x hx ↦ hx.2)
    have := superharmonicOnSurface_inf_paste_of_boundary_le
      P.isOpen (hL_cont_of_subset
        (fun x hx ↦ (by
          have hxV : x ∈ D.expandedOpenDisk ρ := hx.2
          rw [ClosedCoordinateDisk.expandedOpenDisk] at hxV
          exact hxV.1))
        (fun x hx ↦ hx.1.2)) hBk_cont'
      hL_super hBk_super hcontact
    simpa [G] using this
  have hb_eq_G : Set.EqOn b G (Ucl ∩ V) := by
    intro x hx
    have hxΩ : x ∈ Ω.carrier := hV_subset_Ω hx.2
    by_cases hxD : x ∈ D.carrier
    · have hx_notP : x ∉ P.carrier := by
        intro hxP
        have hxP' : x ∈ Ω.carrier \ D.carrier := by
          simpa [P, annularPerronDomain_carrier] using hxP
        exact hxP'.2 hxD
      simp [b, hubbardAnnularPerronBarrier, hxD, G,
        superharmonicInfPaste, hx_notP, L]
    · have hxP : x ∈ P.carrier := by
        simpa [P, annularPerronDomain_carrier] using And.intro hxΩ hxD
      have hxV : x ∈ D.expandedOpenDisk ρ := hx.2
      simp [b, hubbardAnnularPerronBarrier, hxD,
        hubbardOuterAnnularPerronBarrier, hxV, G,
        superharmonicInfPaste, hxP, L, k, inf_comm]
  have hb_eq_w_on_compl : Set.EqOn b w (Ucl ∩ D.carrierᶜ) := by
    intro x hx
    have hxD : x ∉ D.carrier := hx.2
    dsimp [b, w]
    simp [hubbardAnnularPerronBarrier, hxD]
  have hUcl_compl_subset_closureP : Ucl ∩ closure D.carrierᶜ ⊆ closure P.carrier := by
    intro x hx
    have hx_closureΩ : x ∈ closure Ω.carrier := hx.1.1
    rw [mem_closure_iff_nhds]
    intro N hN
    by_cases hxD : x ∈ D.carrier
    · have hxΩ : x ∈ Ω.carrier := hD_subset hxD
      have hΩ_nhds : Ω.carrier ∈ 𝓝 x := Ω.isOpen.mem_nhds hxΩ
      have hx_closure_compl : x ∈ closure D.carrierᶜ := hx.2
      rw [mem_closure_iff_nhds] at hx_closure_compl
      rcases hx_closure_compl (N ∩ Ω.carrier)
          (Filter.inter_mem hN hΩ_nhds) with ⟨y, hy, hyD⟩
      exact ⟨y, hy.1, by
        change y ∈ Ω.carrier \ D.carrier
        exact ⟨hy.2, hyD⟩⟩
    · have hD_nhds : D.carrierᶜ ∈ 𝓝 x :=
        (ClosedCoordinateDisk.isClosed D).isOpen_compl.mem_nhds hxD
      rw [mem_closure_iff_nhds] at hx_closureΩ
      rcases hx_closureΩ (N ∩ D.carrierᶜ)
          (Filter.inter_mem hN hD_nhds) with ⟨y, hy, hyΩ⟩
      exact ⟨y, hy.1, by
        change y ∈ Ω.carrier \ D.carrier
        exact ⟨hyΩ, hy.2⟩⟩
  have hb_cont : ContinuousOn b Ucl := by
    apply continuousOn_of_locally_continuousOn
    intro x hx
    by_cases hxD : x ∈ D.carrier
    · refine ⟨V, hV_open, hD_subset_V hxD, ?_⟩
      exact (hG_cont.congr (fun y hy ↦ hb_eq_G ⟨hy.1, hy.2⟩)).mono
        (by intro y hy; exact hy)
    · refine ⟨D.carrierᶜ, (ClosedCoordinateDisk.isClosed D).isOpen_compl,
        hxD, ?_⟩
      have hw_cont' : ContinuousOn w (Ucl ∩ D.carrierᶜ) :=
        hw_cont.mono (fun y hy ↦
          hUcl_compl_subset_closureP ⟨hy.1, subset_closure hy.2⟩)
      exact hw_cont'.congr (fun y hy ↦ hb_eq_w_on_compl hy)
  have hb_super : IsSuperharmonicOnSurface U b := by
    apply superharmonicOnSurface_of_locally hU_open
    intro x hx
    by_cases hxD : x ∈ D.carrier
    · refine ⟨V, hV_open, hD_subset_V hxD, ?_⟩
      change IsSubharmonicOnSurface (U ∩ V) (fun y ↦ -b y)
      apply subharmonicOnSurface_congr_on hG_super
      intro y hy
      exact congrArg Neg.neg
        (hb_eq_G ⟨⟨subset_closure hy.1.1, hy.1.2⟩, hy.2⟩).symm
    · refine ⟨D.carrierᶜ, (ClosedCoordinateDisk.isClosed D).isOpen_compl,
        hxD, ?_⟩
      have hw_super' : IsSuperharmonicOnSurface (U ∩ D.carrierᶜ) w := by
        apply superharmonicOnSurface_mono
          (fun y hy ↦ (by
            change y ∈ Ω.carrier \ D.carrier
            exact ⟨hy.1.1, hy.2⟩))
        exact hw_super
      change IsSubharmonicOnSurface (U ∩ D.carrierᶜ) (fun y ↦ -b y)
      apply subharmonicOnSurface_congr_on hw_super'
      intro y hy
      exact congrArg Neg.neg (hb_eq_w_on_compl ⟨⟨subset_closure hy.1.1,
        hy.1.2⟩, hy.2⟩).symm
  have hb_model :
      ∀ x ∈ D.carrier, x ≠ p → b x = L x := by
    intro x hxD _hxp
    simp [b, hubbardAnnularPerronBarrier, hxD, L]
  have hb_outer : ∀ x ∈ Ω.boundary, b x = 0 := by
    intro x hx_outer
    have hx_notD : x ∉ D.carrier := by
      intro hxD
      have hxΩ : x ∈ Ω.carrier := hD_subset hxD
      have hx_empty : x ∈ Ω.carrier ∩ frontier Ω.carrier :=
        ⟨hxΩ, by simpa [SmoothBoundaryDomain.boundary] using hx_outer⟩
      simp [Ω.isOpen.inter_frontier_eq] at hx_empty
    have hx_notV : x ∉ V := by
      intro hxV
      have hxΩ : x ∈ Ω.carrier := hV_subset_Ω hxV
      have hx_empty : x ∈ Ω.carrier ∩ frontier Ω.carrier :=
        ⟨hxΩ, by simpa [SmoothBoundaryDomain.boundary] using hx_outer⟩
      simp [Ω.isOpen.inter_frontier_eq] at hx_empty
    have hu_zero : u x = 0 :=
      annularPerron_solution_eq_zero_on_outer_boundary
        Ω D hD_subset hnonempty hu hx_outer
    simp [b, hubbardAnnularPerronBarrier, hx_notD,
      hubbardOuterAnnularPerronBarrier, V, hx_notV,
      superharmonicInfPaste, annularPerronUnitHarmonicMeasure, hu_zero]
  exact ⟨hb_cont, hb_super, by simpa [b, L] using hb_model,
    by simpa [b] using hb_outer⟩

/--
%%handwave
name:
  Annular Perron solutions compare below harmonic barriers
statement:
  A harmonic annular Perron solution is at most any harmonic comparison
  function whose boundary values dominate the logarithmic annular boundary
  data.
proof:
  Apply the harmonic Dirichlet comparison principle on the annular Perron
  domain.  The annular domain has the required componentwise maximum-principle
  geometry.
-/
theorem annularPerron_solution_le_harmonic_of_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    {u h : X → ℝ}
    (hu :
      SolvesHarmonicDirichletProblem
        (annularPerronDomain Ω D hD_subset hnonempty)
        (annularLogBoundaryData Ω D hD_subset hnonempty) u)
    (hharm :
      IsHarmonicOnSurface
        (annularPerronDomain Ω D hD_subset hnonempty).carrier h)
    (hcont :
      ContinuousOn h
        (closure (annularPerronDomain Ω D hD_subset hnonempty).carrier))
    (hboundary :
      ∀ x ∈ (annularPerronDomain Ω D hD_subset hnonempty).boundary,
        annularLogBoundaryData Ω D hD_subset hnonempty x ≤ h x) :
    ∀ x ∈ (annularPerronDomain Ω D hD_subset hnonempty).carrier,
      u x ≤ h x := by
  exact
    solvesHarmonicDirichletProblem_le_harmonic_of_boundary_le hu
      (annularPerronDomain_hasComponentwiseMaximumPrincipleGeometry
        Ω D hD_subset hnonempty)
      hharm hcont hboundary

/--
%%handwave
name:
  Harmonic barriers compare below annular Perron solutions
statement:
  Any harmonic comparison function whose boundary values are bounded above by
  the logarithmic annular boundary data is at most the annular Perron solution
  throughout the annulus.
proof:
  Apply the harmonic Dirichlet comparison principle on the annular Perron
  domain, using the componentwise maximum-principle geometry of the annulus.
-/
theorem harmonic_le_annularPerron_solution_of_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) (D : ClosedCoordinateDisk X)
    (hD_subset : D.carrier ⊆ Ω.carrier)
    (hnonempty : (Ω.carrier \ D.carrier).Nonempty)
    {u h : X → ℝ}
    (hu :
      SolvesHarmonicDirichletProblem
        (annularPerronDomain Ω D hD_subset hnonempty)
        (annularLogBoundaryData Ω D hD_subset hnonempty) u)
    (hharm :
      IsHarmonicOnSurface
        (annularPerronDomain Ω D hD_subset hnonempty).carrier h)
    (hcont :
      ContinuousOn h
        (closure (annularPerronDomain Ω D hD_subset hnonempty).carrier))
    (hboundary :
      ∀ x ∈ (annularPerronDomain Ω D hD_subset hnonempty).boundary,
        h x ≤ annularLogBoundaryData Ω D hD_subset hnonempty x) :
    ∀ x ∈ (annularPerronDomain Ω D hD_subset hnonempty).carrier,
      h x ≤ u x := by
  exact
    harmonic_le_solvesHarmonicDirichletProblem_of_boundary_le hu
      (annularPerronDomain_hasComponentwiseMaximumPrincipleGeometry
        Ω D hD_subset hnonempty)
      hharm hcont hboundary

/--
%%handwave
name:
  Logarithmic zero within an open set
statement:
  A function has a logarithmic zero at a point within a set if, in every
  coordinate at the point, it agrees near the puncture inside that set with
  the coordinate logarithm plus a harmonic remainder on a smaller
  neighborhood contained in the set.
-/
def HasLogarithmicZeroWithin
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (U : Set X) (p : X) (u : X → ℝ) : Prop :=
  ∀ χ : PointedSurfaceCoordinate X p,
    ∃ N : Set X, ∃ h : X → ℝ,
      IsOpen N ∧ p ∈ N ∧ N ⊆ U ∧ N ⊆ χ.chart.source ∧
        IsHarmonicOnSurface N h ∧
          ∀ᶠ x in 𝓝[N ∩ {x : X | x ≠ p}] p,
            u x - Real.log ‖χ.chart x - χ.chart p‖ = h x

/--
%%handwave
name:
  Bounded-domain negative Green potential
statement:
  A bounded-domain negative Green potential on a smooth domain is harmonic
  away from its pole, has a logarithmic zero at the pole, vanishes on the
  boundary, is continuous on the closed domain away from the pole, and is
  nonpositive in the domain.
-/
structure BoundedNegativeGreenPotential
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : SmoothBoundaryDomain X) (p : X) where
  /-- The ambient real-valued potential. -/
  toFun : X → ℝ
  /-- The potential is harmonic in the punctured domain. -/
  harmonic_away_pole : IsHarmonicOnSurface (Ω.carrier \ {p}) toFun
  /-- The potential is continuous on the closed bounded domain away from the pole. -/
  continuousOn_punctured_closure : ContinuousOn toFun (closure Ω.carrier \ {p})
  /-- The potential has zero boundary value on the outer boundary. -/
  boundary_zero : ∀ x ∈ Ω.boundary, toFun x = 0
  /-- The potential is nonpositive in the bounded domain. -/
  nonpositive_on_domain : ∀ x ∈ Ω.carrier, toFun x ≤ 0
  /-- The potential tends to \(-\infty\) at the pole from inside the domain. -/
  tends_to_neg_infinity_at_pole :
    Filter.Tendsto toFun (𝓝[Ω.carrier \ {p}] p) Filter.atBot
  /-- In every coordinate at the pole, the logarithmic zero is locally removable inside the domain. -/
  logarithmic_zero : HasLogarithmicZeroWithin X Ω.carrier p toFun

namespace BoundedNegativeGreenPotential

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Ω : SmoothBoundaryDomain X} {p : X}

instance : CoeFun (BoundedNegativeGreenPotential X Ω p) (fun _ ↦ X → ℝ) where
  coe G := G.toFun

/-- The normalized potential with value zero at the base point. -/
noncomputable def centeredAt (G : BoundedNegativeGreenPotential X Ω p) (q : X) :
    X → ℝ :=
  fun x ↦ G.toFun x - G.toFun q

/-- The outer boundary height after normalizing at the base point. -/
noncomputable def boundaryHeightAt (G : BoundedNegativeGreenPotential X Ω p)
    (q : X) : ℝ :=
  -G.toFun q

/--
%%handwave
name:
  Centered bounded Green potential vanishes at the base point
statement:
  The bounded-domain Green potential normalized at a base point has value zero
  at that base point.
proof:
  This is the definition of the normalization: subtract the value at the base
  point.
-/
theorem centeredAt_base
    (G : BoundedNegativeGreenPotential X Ω p) (q : X) :
    G.centeredAt q q = 0 := by
  simp [centeredAt]

/--
%%handwave
name:
  Centered bounded Green potential has constant outer boundary value
statement:
  On the outer boundary of the bounded domain, the potential normalized at a
  base point is equal to the corresponding boundary height.
proof:
  The bounded-domain Green potential itself has boundary value zero, so
  subtracting its value at the base point gives the boundary height.
-/
theorem centeredAt_eq_boundaryHeightAt_on_boundary
    (G : BoundedNegativeGreenPotential X Ω p) (q : X)
    {x : X} (hx : x ∈ Ω.boundary) :
    G.centeredAt q x = G.boundaryHeightAt q := by
  simp [centeredAt, boundaryHeightAt, G.boundary_zero x hx]

/--
%%handwave
name:
  Bounded Green boundary heights are nonnegative
statement:
  The normalized outer boundary height of a bounded-domain negative Green
  potential is nonnegative at every base point in the domain.
proof:
  The bounded-domain Green potential is nonpositive in the domain, so the
  negative of its value at the base point is nonnegative.
-/
theorem boundaryHeightAt_nonnegative
    (G : BoundedNegativeGreenPotential X Ω p) {q : X}
    (hq : q ∈ Ω.carrier) :
    0 ≤ G.boundaryHeightAt q := by
  exact neg_nonneg.mpr (G.nonpositive_on_domain q hq)

/--
%%handwave
name:
  Centered bounded Green value as height minus positive Green value
statement:
  The normalized bounded Green value at a point is the outer boundary height
  at the base point minus the corresponding positive Green value at the point.
proof:
  Expand the two normalizations and rearrange the signs.
-/
theorem centeredAt_eq_boundaryHeightAt_sub_neg
    (G : BoundedNegativeGreenPotential X Ω p) (q x : X) :
    G.centeredAt q x = G.boundaryHeightAt q - (-G.toFun x) := by
  simp [centeredAt, boundaryHeightAt]
  ring

/--
%%handwave
name:
  Harnack upper control gives a linear centered lower bound
statement:
  If the positive bounded Green value at a point is at most \(C\) times the
  boundary height at the base point, then the centered value is bounded below
  by \((1-C)\) times that boundary height.
proof:
  Write the centered value as height minus the positive Green value and apply
  the assumed upper bound.
-/
theorem centeredAt_ge_one_sub_mul_boundaryHeightAt_of_neg_le_mul
    (G : BoundedNegativeGreenPotential X Ω p) (q x : X) {C : ℝ}
    (hupper : -G.toFun x ≤ C * G.boundaryHeightAt q) :
    (1 - C) * G.boundaryHeightAt q ≤ G.centeredAt q x := by
  rw [G.centeredAt_eq_boundaryHeightAt_sub_neg q x]
  nlinarith

/--
%%handwave
name:
  Punctured closed-domain continuity gives positive Green continuity on
  exhaustion collars
statement:
  If a bounded-domain negative Green potential is continuous on the closed
  domain away from its pole, then the positive Green function \(-G\) is
  continuous on every closed exhaustion collar whose inner domain contains the
  pole.
proof:
  The closure of such a collar lies in the closed outer domain and avoids the
  pole.  Restrict the punctured closed-domain continuity to the collar
  closure and negate.
-/
theorem neg_continuousOn_closedCollar_of_continuousOn_punctured_closure
    {E : SmoothRelativelyCompactExhaustion X} {m n : ℕ}
    (G : BoundedNegativeGreenPotential X (E.domain n) p)
    (hp_inner : p ∈ (E.domain m).carrier)
    (hcont : ContinuousOn G.toFun (closure (E.domain n).carrier \ {p})) :
    ContinuousOn (fun x : X ↦ -G.toFun x)
      (closure (E.closedCollar m n)) := by
  exact
    (hcont.mono
      (E.closure_closedCollar_subset_punctured_outer_closure_of_mem_inner
        (m := m) (n := n) hp_inner)).neg

/--
%%handwave
name:
  Punctured closed-domain continuity gives centered Green continuity on
  exhaustion collars
statement:
  If a bounded-domain negative Green potential is continuous on the closed
  domain away from its pole, then its normalization \(G-G(q)\) is continuous
  on every closed exhaustion collar whose inner domain contains the pole.
proof:
  The closure of the collar lies in the punctured closed outer domain.  On
  that set the potential is continuous, and subtracting the constant value
  \(G(q)\) preserves continuity.
-/
theorem centeredAt_continuousOn_closedCollar_of_continuousOn_punctured_closure
    {E : SmoothRelativelyCompactExhaustion X} {m n : ℕ} {q : X}
    (G : BoundedNegativeGreenPotential X (E.domain n) p)
    (hp_inner : p ∈ (E.domain m).carrier)
    (hcont : ContinuousOn G.toFun (closure (E.domain n).carrier \ {p})) :
    ContinuousOn (G.centeredAt q) (closure (E.closedCollar m n)) := by
  have hG :
      ContinuousOn G.toFun (closure (E.closedCollar m n)) :=
    hcont.mono
      (E.closure_closedCollar_subset_punctured_outer_closure_of_mem_inner
        (m := m) (n := n) hp_inner)
  simpa [centeredAt] using hG.sub continuousOn_const

/--
%%handwave
name:
  Centered bounded Green potentials remain harmonic away from the pole
statement:
  Subtracting the value at a base point from a bounded-domain Green potential
  preserves harmonicity on the punctured domain.
proof:
  The centered potential is the difference between the original harmonic
  potential and a constant function, and constants are harmonic.
-/
theorem centeredAt_harmonic_away_pole
    (G : BoundedNegativeGreenPotential X Ω p) (q : X) :
    IsHarmonicOnSurface (Ω.carrier \ {p}) (G.centeredAt q) := by
  simpa [centeredAt] using
    harmonicOnSurface_sub G.harmonic_away_pole
      (harmonicOnSurface_const (Ω.carrier \ {p}) (G.toFun q))

/--
%%handwave
name:
  Centered bounded Green potentials have the same logarithmic zero
statement:
  Normalizing a bounded-domain Green potential at a base point preserves the
  logarithmic zero at the pole, changing only the removable harmonic term by a
  constant.
proof:
  In a coordinate at the pole, subtract the base-point value from the
  removable harmonic term.  Harmonicity is preserved by subtracting a
  constant, and the eventual logarithmic identity is just algebra.
-/
theorem centeredAt_logarithmic_zero
    (G : BoundedNegativeGreenPotential X Ω p) (q : X) :
    HasLogarithmicZeroWithin X Ω.carrier p (G.centeredAt q) := by
  intro χ
  rcases G.logarithmic_zero χ with
    ⟨N, h, hN_open, hpN, hN_domain, hN_source, hharm, heq⟩
  refine ⟨N, fun x ↦ h x - G.toFun q, hN_open, hpN, hN_domain, hN_source, ?_, ?_⟩
  · exact harmonicOnSurface_sub hharm
      (harmonicOnSurface_const N (G.toFun q))
  · filter_upwards [heq] with x hx
    simp [centeredAt] at hx ⊢
    linarith

/--
%%handwave
name:
  Negated bounded Green potentials have logarithmic poles
statement:
  The negative of a bounded-domain negative Green potential has a removable
  logarithmic pole at the same point.
proof:
  In a pole coordinate the original potential differs from
  \(\log |z-z(p)|\) by a harmonic function.  Negating the identity gives the
  corresponding logarithmic-pole form, with the negative harmonic remainder.
-/
theorem neg_logarithmic_singularity
    (G : BoundedNegativeGreenPotential X Ω p) :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ N : Set X, ∃ h : X → ℝ,
        IsOpen N ∧ p ∈ N ∧ N ⊆ Ω.carrier ∧ N ⊆ χ.chart.source ∧
          IsHarmonicOnSurface N h ∧
            ∀ᶠ x in 𝓝[N ∩ {x : X | x ≠ p}] p,
              -G.toFun x + Real.log ‖χ.chart x - χ.chart p‖ = h x := by
  intro χ
  rcases G.logarithmic_zero χ with
    ⟨N, h, hN_open, hpN, hN_domain, hN_source, hharm, heq⟩
  refine ⟨N, fun x ↦ -h x, hN_open, hpN, hN_domain, hN_source,
    harmonicOnSurface_neg hharm, ?_⟩
  filter_upwards [heq] with x hx
  linarith

/--
%%handwave
name:
  Centered bounded Green potentials still tend to minus infinity at the pole
statement:
  Subtracting a constant from a bounded-domain Green potential does not change
  its divergence to \(-\infty\) at the pole.
proof:
  A function tending to \(-\infty\) remains so after adding any fixed
  constant.
-/
theorem centeredAt_tends_to_neg_infinity_at_pole
    (G : BoundedNegativeGreenPotential X Ω p) (q : X) :
    Filter.Tendsto (G.centeredAt q)
      (𝓝[Ω.carrier \ {p}] p) Filter.atBot := by
  simpa [centeredAt, sub_eq_add_neg] using
    G.tends_to_neg_infinity_at_pole.atBot_add
      (tendsto_const_nhds (x := -G.toFun q))

end BoundedNegativeGreenPotential

/--
%%handwave
name:
  Diverging boundary heights give large centered boundary values
statement:
  If the normalized outer boundary heights of bounded-domain Green potentials
  along an exhaustion tend to \(+\infty\), then for every real level, all
  sufficiently late centered potentials are at least that level on the
  boundary of their exhaustion domain.
proof:
  On each outer boundary, the centered potential is exactly its boundary
  height.  The claimed lower bound is therefore the defining eventual lower
  bound for a sequence tending to \(+\infty\).
-/
theorem centered_boundedNegativeGreen_boundary_eventually_ge_of_heights
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    (hheights :
      Filter.Tendsto
        (fun n : ℕ ↦ (B n).boundaryHeightAt q)
        Filter.atTop Filter.atTop)
    (A : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ x ∈ (E.domain n).boundary, A ≤ (B n).centeredAt q x := by
  filter_upwards [hheights.eventually_ge_atTop A] with n hn x hx
  rw [BoundedNegativeGreenPotential.centeredAt_eq_boundaryHeightAt_on_boundary
    (B n) q hx]
  exact hn

/--
%%handwave
name:
  Divergent boundary heights remain divergent along subsequences
statement:
  If the normalized outer boundary heights of bounded-domain Green potentials
  tend to \(+\infty\), then they still tend to \(+\infty\) along every
  strictly increasing subsequence.
proof:
  A strictly increasing sequence of natural numbers tends to infinity, so
  composing a divergent sequence with it preserves divergence to infinity.
-/
theorem boundedNegativeGreen_boundaryHeights_tendsto_atTop_comp_strictMono
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hheights :
      Filter.Tendsto
        (fun n : ℕ ↦ (B n).boundaryHeightAt q)
        Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun k : ℕ ↦ (B (φ k)).boundaryHeightAt q)
      Filter.atTop Filter.atTop := by
  exact hheights.comp hφ.tendsto_atTop

/--
%%handwave
name:
  Diverging boundary heights give large centered boundary values along
  subsequences
statement:
  If the normalized outer boundary heights of bounded-domain Green potentials
  tend to \(+\infty\), then along any strictly increasing subsequence, for
  every real level all sufficiently late centered potentials are at least
  that level on the corresponding outer boundary.
proof:
  The full exhaustion sequence has the eventual boundary lower bound, and a
  strictly increasing subsequence preserves eventual properties.
-/
theorem centered_boundedNegativeGreen_boundary_subsequence_eventually_ge_of_heights
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hheights :
      Filter.Tendsto
        (fun n : ℕ ↦ (B n).boundaryHeightAt q)
        Filter.atTop Filter.atTop)
    (A : ℝ) :
    ∀ᶠ k : ℕ in Filter.atTop,
      ∀ x ∈ (E.domain (φ k)).boundary, A ≤ (B (φ k)).centeredAt q x := by
  exact hφ.tendsto_atTop.eventually
    (centered_boundedNegativeGreen_boundary_eventually_ge_of_heights
      (E := E) (p := p) (q := q) B hheights A)

/--
%%handwave
name:
  Positive bounded Green functions obey collar upper bounds
statement:
  Let \(G\) be a bounded-domain negative Green potential and let \(C\) be a
  compact Perron collar contained in the punctured domain.  If the positive
  Green function \(-G\) is continuous on the closed collar and bounded above
  by \(\varepsilon\) on the collar boundary, then it is bounded above by
  \(\varepsilon\) throughout the collar.
proof:
  The positive Green function is harmonic on the collar because the collar is
  contained in the punctured domain.  Apply the harmonic maximum principle
  with the supplied closed-collar continuity and boundary upper bound.
-/
theorem neg_boundedNegativeGreen_collar_upper_bound_of_boundary_upper_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (G : BoundedNegativeGreenPotential X Ω p)
    (C : PerronDomain X)
    (hC_geometry : HasComponentwiseMaximumPrincipleGeometry C.carrier)
    (hC_subset : C.carrier ⊆ Ω.carrier \ {p})
    (hcont : ContinuousOn (fun x : X ↦ -G.toFun x) (closure C.carrier))
    {ε : ℝ}
    (hboundary : ∀ x ∈ C.boundary, -G.toFun x ≤ ε) :
    ∀ x ∈ C.carrier, -G.toFun x ≤ ε := by
  have hharm :
      IsHarmonicOnSurface C.carrier (fun x : X ↦ -G.toFun x) :=
    harmonicOnSurface_neg (harmonicOnSurface_mono hC_subset G.harmonic_away_pole)
  exact
    harmonic_le_constant_of_boundary_le C hC_geometry hcont hharm hboundary

/--
%%handwave
name:
  Centered bounded Green potentials obey collar lower bounds
statement:
  Let \(G\) be a bounded-domain negative Green potential and let \(C\) be a
  compact Perron collar contained in the punctured domain.  If the centered
  potential \(G-G(q)\) is continuous on the closed collar and bounded below
  by \(A\) on the collar boundary, then it is bounded below by \(A\)
  throughout the collar.
proof:
  The centered potential is harmonic on the collar because centering only
  subtracts a constant and the collar avoids the pole.  Apply the harmonic
  maximum principle with the supplied closed-collar continuity and boundary
  lower bound.
-/
theorem centered_boundedNegativeGreen_collar_lower_bound_of_boundary_lower_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p q : X}
    (G : BoundedNegativeGreenPotential X Ω p)
    (C : PerronDomain X)
    (hC_geometry : HasComponentwiseMaximumPrincipleGeometry C.carrier)
    (hC_subset : C.carrier ⊆ Ω.carrier \ {p})
    (hcont : ContinuousOn (G.centeredAt q) (closure C.carrier))
    {A : ℝ}
    (hboundary : ∀ x ∈ C.boundary, A ≤ G.centeredAt q x) :
    ∀ x ∈ C.carrier, A ≤ G.centeredAt q x := by
  have hharm :
      IsHarmonicOnSurface C.carrier (G.centeredAt q) :=
    harmonicOnSurface_mono hC_subset (G.centeredAt_harmonic_away_pole q)
  exact
    constant_le_harmonic_of_boundary_le C hC_geometry hcont hharm hboundary

/--
%%handwave
name:
  Positive bounded Green functions obey closed-exhaustion-collar upper bounds
statement:
  Let \(G\) be a bounded-domain negative Green potential on an exhaustion
  domain.  If the positive Green function \(-G\) is continuous on the closed
  collar between an inner and outer exhaustion domain and is bounded above on
  the collar boundary, then it is bounded above throughout the collar.
proof:
  Package the nonempty exhaustion collar as a Perron domain.  The collar lies
  in the punctured outer domain because the inner domain contains the pole, so
  the general collar maximum-principle comparison applies.
-/
theorem neg_boundedNegativeGreen_closedCollar_upper_bound_of_boundary_upper_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X} {m n : ℕ}
    (G : BoundedNegativeGreenPotential X (E.domain n) p)
    (hnonempty : (E.closedCollar m n).Nonempty)
    (hp_inner : p ∈ (E.domain m).carrier)
    (hcont : ContinuousOn (fun x : X ↦ -G.toFun x)
      (closure (E.closedCollar m n)))
    {ε : ℝ}
    (hboundary : ∀ x ∈ frontier (E.closedCollar m n), -G.toFun x ≤ ε) :
    ∀ x ∈ E.closedCollar m n, -G.toFun x ≤ ε := by
  let C : PerronDomain X := E.closedCollarPerronDomain m n hnonempty
  have hgeom : HasComponentwiseMaximumPrincipleGeometry C.carrier := by
    simpa [C] using
      E.closedCollarPerronDomain_hasComponentwiseMaximumPrincipleGeometry
        (m := m) (n := n) (p := p) hnonempty hp_inner
  have hsubset : C.carrier ⊆ (E.domain n).carrier \ {p} := by
    simpa [C] using
      E.closedCollar_subset_punctured_outer_of_mem_inner
        (m := m) (n := n) hp_inner
  have hcontC : ContinuousOn (fun x : X ↦ -G.toFun x)
      (closure C.carrier) := by
    simpa [C] using hcont
  have hboundaryC : ∀ x ∈ C.boundary, -G.toFun x ≤ ε := by
    simpa [C] using hboundary
  have hcomparison :=
    neg_boundedNegativeGreen_collar_upper_bound_of_boundary_upper_bound
      G C hgeom hsubset hcontC hboundaryC
  simpa [C] using hcomparison

/--
%%handwave
name:
  Centered bounded Green potentials obey closed-exhaustion-collar lower bounds
statement:
  Let \(G\) be a bounded-domain negative Green potential on an exhaustion
  domain.  If the centered potential \(G-G(q)\) is continuous on the closed
  collar between an inner and outer exhaustion domain and is bounded below on
  the collar boundary, then it is bounded below throughout the collar.
proof:
  Package the nonempty exhaustion collar as a Perron domain.  Since the inner
  exhaustion domain contains the pole, the collar lies in the punctured outer
  domain, where the centered potential is harmonic.  Apply the general collar
  lower-bound comparison.
-/
theorem centered_boundedNegativeGreen_closedCollar_lower_bound_of_boundary_lower_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X} {m n : ℕ}
    (G : BoundedNegativeGreenPotential X (E.domain n) p)
    (hnonempty : (E.closedCollar m n).Nonempty)
    (hp_inner : p ∈ (E.domain m).carrier)
    (hcont : ContinuousOn (G.centeredAt q) (closure (E.closedCollar m n)))
    {A : ℝ}
    (hboundary : ∀ x ∈ frontier (E.closedCollar m n), A ≤ G.centeredAt q x) :
    ∀ x ∈ E.closedCollar m n, A ≤ G.centeredAt q x := by
  let C : PerronDomain X := E.closedCollarPerronDomain m n hnonempty
  have hgeom : HasComponentwiseMaximumPrincipleGeometry C.carrier := by
    simpa [C] using
      E.closedCollarPerronDomain_hasComponentwiseMaximumPrincipleGeometry
        (m := m) (n := n) (p := p) hnonempty hp_inner
  have hsubset : C.carrier ⊆ (E.domain n).carrier \ {p} := by
    simpa [C] using
      E.closedCollar_subset_punctured_outer_of_mem_inner
        (m := m) (n := n) hp_inner
  have hcontC : ContinuousOn (G.centeredAt q) (closure C.carrier) := by
    simpa [C] using hcont
  have hboundaryC : ∀ x ∈ C.boundary, A ≤ G.centeredAt q x := by
    simpa [C] using hboundary
  have hcomparison :=
    centered_boundedNegativeGreen_collar_lower_bound_of_boundary_lower_bound
      G C hgeom hsubset hcontC hboundaryC
  simpa [C] using hcomparison

/--
%%handwave
name:
  Positive bounded Green functions obey closed-collar upper bounds from the
  two exhaustion boundaries
statement:
  If the positive Green function \(-G\) is bounded above on both boundary
  components of an exhaustion collar and is continuous on the closed collar,
  then it is bounded above throughout the collar.
proof:
  If the collar is empty, the conclusion is vacuous.  Otherwise package it as
  a Perron domain.  Every collar-boundary point lies on either the inner or
  outer exhaustion boundary, so the two supplied boundary estimates give the
  boundary estimate needed for the closed-collar maximum principle.
-/
theorem neg_boundedNegativeGreen_closedCollar_upper_bound_of_two_boundary_upper_bounds
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X} {m n : ℕ}
    (G : BoundedNegativeGreenPotential X (E.domain n) p)
    (hp_inner : p ∈ (E.domain m).carrier)
    (hcont : ContinuousOn (fun x : X ↦ -G.toFun x)
      (closure (E.closedCollar m n)))
    {ε : ℝ}
    (houter : ∀ x ∈ (E.domain n).boundary, -G.toFun x ≤ ε)
    (hinner : ∀ x ∈ (E.domain m).boundary, -G.toFun x ≤ ε) :
    ∀ x ∈ E.closedCollar m n, -G.toFun x ≤ ε := by
  by_cases hnonempty : (E.closedCollar m n).Nonempty
  · refine
      neg_boundedNegativeGreen_closedCollar_upper_bound_of_boundary_upper_bound
        G hnonempty hp_inner hcont ?_
    intro x hx
    rcases
        E.frontier_closedCollar_subset_outer_boundary_or_inner_boundary
          (m := m) (n := n) hx with
      hx_outer | hx_inner
    · exact houter x hx_outer
    · exact hinner x hx_inner
  · intro x hx
    exact False.elim (hnonempty ⟨x, hx⟩)

/--
%%handwave
name:
  Positive bounded Green functions obey closed-collar upper bounds from the
  inner boundary
statement:
  If \(\varepsilon\ge0\), the positive Green function \(-G\) is bounded above
  by \(\varepsilon\) on the outer boundary because \(G\) vanishes there.  Thus
  an upper bound by \(\varepsilon\) on the inner boundary propagates through
  the whole closed exhaustion collar.
proof:
  The outer boundary estimate is the zero boundary value of \(G\).  Apply the
  two-boundary closed-collar estimate.
-/
theorem neg_boundedNegativeGreen_closedCollar_upper_bound_of_inner_boundary_upper_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X} {m n : ℕ}
    (G : BoundedNegativeGreenPotential X (E.domain n) p)
    (hp_inner : p ∈ (E.domain m).carrier)
    (hcont : ContinuousOn (fun x : X ↦ -G.toFun x)
      (closure (E.closedCollar m n)))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hinner : ∀ x ∈ (E.domain m).boundary, -G.toFun x ≤ ε) :
    ∀ x ∈ E.closedCollar m n, -G.toFun x ≤ ε := by
  refine
    neg_boundedNegativeGreen_closedCollar_upper_bound_of_two_boundary_upper_bounds
      G hp_inner hcont ?_ hinner
  intro x hx
  rw [G.boundary_zero x hx]
  simpa using hε

/--
%%handwave
name:
  Positive Green values are bounded by inner harmonic measure
statement:
  On a closed exhaustion collar, if the positive Green function is bounded
  above by \(M\) on the inner boundary, then it is bounded above by \(M\)
  times the harmonic measure of that inner boundary.
proof:
  The positive Green function is harmonic on the collar and continuous on its
  closure because the collar avoids the pole.  Its outer-boundary value is
  \(0\).  Compare it with \(M\) times the inner harmonic measure, which has
  boundary values \(M\) on the inner boundary and \(0\) on the outer boundary.
-/
theorem neg_boundedNegativeGreen_closedCollar_upper_bound_by_inner_harmonicMeasure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X} {m n : ℕ}
    (hmn : m < n)
    (G : BoundedNegativeGreenPotential X (E.domain n) p)
    (hp_inner : p ∈ (E.domain m).carrier)
    (hnonempty : (E.closedCollar m n).Nonempty)
    {M : ℝ}
    (hinner : ∀ x ∈ (E.domain m).boundary, -G.toFun x ≤ M) :
    ∀ x ∈ E.closedCollar m n,
      -G.toFun x ≤
        M * E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x := by
  have hsubset :
      E.closedCollar m n ⊆ (E.domain n).carrier \ {p} :=
    E.closedCollar_subset_punctured_outer_of_mem_inner
      (m := m) (n := n) hp_inner
  have hharm :
      IsHarmonicOnSurface (E.closedCollar m n) (fun x : X ↦ -G.toFun x) :=
    harmonicOnSurface_neg (harmonicOnSurface_mono hsubset G.harmonic_away_pole)
  have hcont : ContinuousOn (fun x : X ↦ -G.toFun x)
      (closure (E.closedCollar m n)) :=
    G.neg_continuousOn_closedCollar_of_continuousOn_punctured_closure
      (E := E) (m := m) (n := n) hp_inner G.continuousOn_punctured_closure
  refine
    E.harmonicOn_closedCollar_le_innerBoundaryBound_mul_innerHarmonicMeasure
      hmn hnonempty hharm hcont ?_ ?_
  · intro x _hx_boundary hx_inner
    exact hinner x hx_inner
  · intro x hx_boundary hx_not_inner
    have hx_frontier : x ∈ frontier (E.closedCollar m n) := by
      simpa using hx_boundary
    rcases
        E.frontier_closedCollar_subset_outer_boundary_or_inner_boundary
          (m := m) (n := n) hx_frontier with
      hx_outer | hx_inner
    · rw [G.boundary_zero x hx_outer]
      norm_num
    · exact False.elim (hx_not_inner hx_inner)

/--
%%handwave
name:
  Harmonic-measure decay gives exterior smallness for positive Green functions
statement:
  Suppose one fixed inner exhaustion boundary carries a uniform eventual upper
  bound for the positive Green functions, and the harmonic measure of that
  inner boundary becomes uniformly small outside a compact set as the outer
  boundary recedes.  Then the positive Green functions are eventually
  uniformly small outside a compact exceptional set.
proof:
  Choose the harmonic-measure tolerance so that the inner-boundary bound times
  the tolerance is at most the prescribed error.  Outside the compact set,
  points of the outer domain are either in the distant collar or in the fixed
  inner piece.  The latter is excluded by putting the fixed inner closure into
  the compact set; on the collar the harmonic-measure comparison gives the
  desired estimate.
-/
theorem neg_boundedNegativeGreen_exhaustion_eventual_exterior_norm_small_of_inner_boundary_bound_and_harmonicMeasure_small
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {m : ℕ}
    (hp_inner : p ∈ (E.domain m).carrier)
    (hinner_bound :
      ∃ M : ℝ, 0 < M ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ y ∈ (E.domain m).boundary, -((B n).toFun y) ≤ M)
    (hmeasure_small :
      ∀ δ : ℝ, 0 < δ →
        ∃ K : Set X, IsCompact K ∧ p ∈ K ∧
          closure (E.domain m).carrier ⊆ K ∧
          ∀ᶠ n : ℕ in Filter.atTop,
            ∀ (hmn : m < n) (hnonempty : (E.closedCollar m n).Nonempty),
              ∀ x ∈ E.closedCollar m n, x ∉ K →
                E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x ≤ δ) :
    ∀ ε : ℝ, 0 < ε → ∃ K : Set X, IsCompact K ∧ p ∈ K ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x : X, x ∈ (E.domain n).carrier → x ∉ K →
          ‖-((B n).toFun x)‖ ≤ ε := by
  intro ε hε
  rcases hinner_bound with ⟨M, hM_pos, hinner_event⟩
  let δ : ℝ := ε / M
  have hδ_pos : 0 < δ := div_pos hε hM_pos
  rcases hmeasure_small δ hδ_pos with
    ⟨K, hK_compact, hpK, hinner_closure_subset, hω_event⟩
  refine ⟨K, hK_compact, hpK, ?_⟩
  have hlate : ∀ᶠ n : ℕ in Filter.atTop, m < n := by
    refine Filter.eventually_atTop.2 ⟨m + 1, ?_⟩
    intro n hn
    exact Nat.lt_of_succ_le hn
  filter_upwards [hinner_event, hω_event, hlate] with
    n hinner_n hω_n hmn x hx_domain hx_notK
  have hx_not_inner : x ∉ (E.domain m).carrier := by
    intro hx_inner
    exact hx_notK (hinner_closure_subset (subset_closure hx_inner))
  have hx_outer_sdiff :
      x ∈ (E.domain n).carrier \ (E.domain m).carrier :=
    ⟨hx_domain, hx_not_inner⟩
  have hpos_nonneg : 0 ≤ -((B n).toFun x) :=
    neg_nonneg.mpr ((B n).nonpositive_on_domain x hx_domain)
  have hpositive_le : -((B n).toFun x) ≤ ε := by
    rcases
        E.outer_sdiff_inner_subset_inner_boundary_union_closedCollar
          (m := m) (n := n) hx_outer_sdiff with
      hx_boundary | hx_collar
    · have hx_closure : x ∈ closure (E.domain m).carrier := by
        have hx_frontier : x ∈ frontier (E.domain m).carrier := by
          simpa [SmoothBoundaryDomain.boundary] using hx_boundary
        exact frontier_subset_closure hx_frontier
      exact False.elim (hx_notK (hinner_closure_subset hx_closure))
    · have hnonempty : (E.closedCollar m n).Nonempty := ⟨x, hx_collar⟩
      have hweighted :
          -((B n).toFun x) ≤
            M * E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x :=
        neg_boundedNegativeGreen_closedCollar_upper_bound_by_inner_harmonicMeasure
          (E := E) (p := p) (m := m) (n := n) hmn (B n)
          hp_inner hnonempty hinner_n x hx_collar
      have hωx :
          E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x ≤ δ :=
        hω_n hmn hnonempty x hx_collar hx_notK
      have hmul : M *
          E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x ≤ ε := by
        calc
          M * E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x
              ≤ M * δ := mul_le_mul_of_nonneg_left hωx hM_pos.le
          _ = ε := by
            dsimp [δ]
            exact mul_div_cancel₀ ε hM_pos.ne'
      exact hweighted.trans hmul
  have hnorm_eq :
      ‖-((B n).toFun x)‖ = -((B n).toFun x) := by
    simpa [Real.norm_eq_abs] using abs_of_nonneg hpos_nonneg
  simpa [hnorm_eq] using hpositive_le

/--
%%handwave
name:
  Centered bounded Green potentials obey closed-collar lower bounds from the
  two exhaustion boundaries
statement:
  If a centered bounded Green potential is bounded below on both boundary
  components of an exhaustion collar and is continuous on the closed collar,
  then it is bounded below throughout the collar.
proof:
  If the collar is empty, the conclusion is vacuous.  Otherwise package it as
  a Perron domain.  The frontier of the collar lies on the union of the two
  exhaustion boundaries, and the general closed-collar lower-bound comparison
  applies.
-/
theorem centered_boundedNegativeGreen_closedCollar_lower_bound_of_two_boundary_lower_bounds
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X} {m n : ℕ}
    (G : BoundedNegativeGreenPotential X (E.domain n) p)
    (hp_inner : p ∈ (E.domain m).carrier)
    (hcont : ContinuousOn (G.centeredAt q) (closure (E.closedCollar m n)))
    {A : ℝ}
    (houter : ∀ x ∈ (E.domain n).boundary, A ≤ G.centeredAt q x)
    (hinner : ∀ x ∈ (E.domain m).boundary, A ≤ G.centeredAt q x) :
    ∀ x ∈ E.closedCollar m n, A ≤ G.centeredAt q x := by
  by_cases hnonempty : (E.closedCollar m n).Nonempty
  · refine
      centered_boundedNegativeGreen_closedCollar_lower_bound_of_boundary_lower_bound
        G hnonempty hp_inner hcont ?_
    intro x hx
    rcases
        E.frontier_closedCollar_subset_outer_boundary_or_inner_boundary
          (m := m) (n := n) hx with
      hx_outer | hx_inner
    · exact houter x hx_outer
    · exact hinner x hx_inner
  · intro x hx
    exact False.elim (hnonempty ⟨x, hx⟩)

/--
%%handwave
name:
  Centered bounded Green potentials obey closed-collar lower bounds from the
  inner boundary and outer height
statement:
  On the outer boundary of the bounded domain, the centered potential equals
  its boundary height.  Therefore, if this height is at least \(A\) and the
  centered potential is at least \(A\) on the inner boundary, then it is at
  least \(A\) throughout the closed collar.
proof:
  Convert the outer height lower bound to an outer boundary lower bound using
  the zero boundary value of the Green potential, then apply the two-boundary
  closed-collar lower-bound estimate.
-/
theorem centered_boundedNegativeGreen_closedCollar_lower_bound_of_inner_boundary_and_outer_height
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X} {m n : ℕ}
    (G : BoundedNegativeGreenPotential X (E.domain n) p)
    (hp_inner : p ∈ (E.domain m).carrier)
    (hcont : ContinuousOn (G.centeredAt q) (closure (E.closedCollar m n)))
    {A : ℝ}
    (houter_height : A ≤ G.boundaryHeightAt q)
    (hinner : ∀ x ∈ (E.domain m).boundary, A ≤ G.centeredAt q x) :
    ∀ x ∈ E.closedCollar m n, A ≤ G.centeredAt q x := by
  refine
    centered_boundedNegativeGreen_closedCollar_lower_bound_of_two_boundary_lower_bounds
      G hp_inner hcont ?_ hinner
  intro x hx
  rw [G.centeredAt_eq_boundaryHeightAt_on_boundary q hx]
  exact houter_height

/--
%%handwave
name:
  Centered Green values are bounded below by harmonic-measure interpolation
statement:
  On a closed exhaustion collar, if a centered Green potential is bounded
  below by \(L\) on the inner boundary, then throughout the collar it is
  bounded below by the affine harmonic function with value \(L\) on the inner
  boundary and value equal to the outer boundary height on the outer boundary.
proof:
  Subtract the centered potential from the outer boundary height.  This
  harmonic function is bounded above by the height gap on the inner boundary
  and by \(0\) on the outer boundary.  The inner harmonic-measure comparison
  gives the desired affine lower bound after rearranging.
-/
theorem centered_boundedNegativeGreen_closedCollar_lower_bound_by_inner_harmonicMeasure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X} {m n : ℕ}
    (hmn : m < n)
    (G : BoundedNegativeGreenPotential X (E.domain n) p)
    (hp_inner : p ∈ (E.domain m).carrier)
    (hnonempty : (E.closedCollar m n).Nonempty)
    {L : ℝ}
    (hinner : ∀ x ∈ (E.domain m).boundary, L ≤ G.centeredAt q x) :
    ∀ x ∈ E.closedCollar m n,
      G.boundaryHeightAt q -
          (G.boundaryHeightAt q - L) *
            E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x
        ≤ G.centeredAt q x := by
  let H : ℝ := G.boundaryHeightAt q
  let u : X → ℝ := fun x ↦ H - G.centeredAt q x
  have hsubset :
      E.closedCollar m n ⊆ (E.domain n).carrier \ {p} :=
    E.closedCollar_subset_punctured_outer_of_mem_inner
      (m := m) (n := n) hp_inner
  have hcenter_harm :
      IsHarmonicOnSurface (E.closedCollar m n) (G.centeredAt q) :=
    harmonicOnSurface_mono hsubset (G.centeredAt_harmonic_away_pole q)
  have hu_harm :
      IsHarmonicOnSurface (E.closedCollar m n) u := by
    simpa [u] using
      harmonicOnSurface_sub
        (harmonicOnSurface_const (E.closedCollar m n) H)
        hcenter_harm
  have hcenter_cont : ContinuousOn (G.centeredAt q)
      (closure (E.closedCollar m n)) :=
    G.centeredAt_continuousOn_closedCollar_of_continuousOn_punctured_closure
      (E := E) (m := m) (n := n) (q := q) hp_inner
      G.continuousOn_punctured_closure
  have hu_cont : ContinuousOn u (closure (E.closedCollar m n)) := by
    simpa [u] using continuousOn_const.sub hcenter_cont
  have hupper :
      ∀ x ∈ E.closedCollar m n,
        u x ≤
          (H - L) *
            E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x := by
    refine
      E.harmonicOn_closedCollar_le_innerBoundaryBound_mul_innerHarmonicMeasure
        hmn hnonempty hu_harm hu_cont ?_ ?_
    · intro x _hx_boundary hx_inner
      have hx_lower : L ≤ G.centeredAt q x := hinner x hx_inner
      simp [u, H]
      linarith
    · intro x hx_boundary hx_not_inner
      have hx_frontier : x ∈ frontier (E.closedCollar m n) := by
        simpa using hx_boundary
      rcases
          E.frontier_closedCollar_subset_outer_boundary_or_inner_boundary
            (m := m) (n := n) hx_frontier with
        hx_outer | hx_inner
      · have hx_center :
            G.centeredAt q x = G.boundaryHeightAt q :=
          G.centeredAt_eq_boundaryHeightAt_on_boundary q hx_outer
        simp [u, H, hx_center]
      · exact False.elim (hx_not_inner hx_inner)
  intro x hx
  have hx_upper := hupper x hx
  dsimp [u, H] at hx_upper ⊢
  linarith

/--
%%handwave
name:
  Harmonic-measure decay gives exterior lower growth for centered Green
  functions
statement:
  Suppose the centered Green functions have a uniform eventual lower bound on
  one fixed inner exhaustion boundary, the outer boundary heights tend to
  \(+\infty\), and the harmonic measure of that inner boundary is uniformly
  small outside a compact set as the outer boundary recedes.  Then every
  prescribed lower bound holds eventually outside a compact exceptional set.
proof:
  On the collar, the centered potential dominates the affine harmonic
  interpolation between the large outer boundary height and the fixed inner
  lower bound.  Where the inner harmonic measure is at most \(1/2\), this
  interpolation is bounded below by half the outer height plus half the worse
  of the inner lower bound and \(0\).  Taking the outer height sufficiently
  large gives the desired lower bound.
-/
theorem centered_boundedNegativeGreen_exhaustion_eventual_exterior_large_of_inner_boundary_lower_bound_and_harmonicMeasure_small
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {m : ℕ}
    (hp_inner : p ∈ (E.domain m).carrier)
    (hq_inner : q ∈ (E.domain m).carrier)
    (hheights :
      Filter.Tendsto
        (fun n : ℕ ↦ (B n).boundaryHeightAt q)
        Filter.atTop Filter.atTop)
    (hinner_lower :
      ∃ L : ℝ,
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ y ∈ (E.domain m).boundary, L ≤ (B n).centeredAt q y)
    (hmeasure_small :
      ∀ δ : ℝ, 0 < δ →
        ∃ K : Set X, IsCompact K ∧ p ∈ K ∧ q ∈ K ∧
          closure (E.domain m).carrier ⊆ K ∧
          ∀ᶠ n : ℕ in Filter.atTop,
            ∀ (hmn : m < n) (hnonempty : (E.closedCollar m n).Nonempty),
              ∀ x ∈ E.closedCollar m n, x ∉ K →
                E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x ≤ δ) :
    ∀ A : ℝ, ∃ K : Set X, IsCompact K ∧ p ∈ K ∧ q ∈ K ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x : X, x ∈ (E.domain n).carrier → x ∉ K →
          A ≤ (B n).centeredAt q x := by
  intro A
  rcases hinner_lower with ⟨L, hinner_event⟩
  let δ : ℝ := (1 / 2 : ℝ)
  have hδ_pos : 0 < δ := by norm_num [δ]
  rcases hmeasure_small δ hδ_pos with
    ⟨K, hK_compact, hpK, hqK, hinner_closure_subset, hω_event⟩
  refine ⟨K, hK_compact, hpK, hqK, ?_⟩
  let R : ℝ := 2 * A - min L 0
  have hlate : ∀ᶠ n : ℕ in Filter.atTop, m < n := by
    refine Filter.eventually_atTop.2 ⟨m + 1, ?_⟩
    intro n hn
    exact Nat.lt_of_succ_le hn
  filter_upwards [hinner_event, hω_event, hlate,
    hheights.eventually_ge_atTop R] with
    n hinner_n hω_n hmn hheight_n x hx_domain hx_notK
  have hx_not_inner : x ∉ (E.domain m).carrier := by
    intro hx_inner
    exact hx_notK (hinner_closure_subset (subset_closure hx_inner))
  have hx_outer_sdiff :
      x ∈ (E.domain n).carrier \ (E.domain m).carrier :=
    ⟨hx_domain, hx_not_inner⟩
  rcases
      E.outer_sdiff_inner_subset_inner_boundary_union_closedCollar
        (m := m) (n := n) hx_outer_sdiff with
    hx_boundary | hx_collar
  · have hx_closure : x ∈ closure (E.domain m).carrier := by
      have hx_frontier : x ∈ frontier (E.domain m).carrier := by
        simpa [SmoothBoundaryDomain.boundary] using hx_boundary
      exact frontier_subset_closure hx_frontier
    exact False.elim (hx_notK (hinner_closure_subset hx_closure))
  · have hnonempty : (E.closedCollar m n).Nonempty := ⟨x, hx_collar⟩
    let omega : ℝ :=
      E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x
    have hω_le_half : omega ≤ (1 / 2 : ℝ) := by
      simpa [omega, δ] using hω_n hmn hnonempty x hx_collar hx_notK
    have hω_nonneg : 0 ≤ omega := by
      have hIcc :=
        E.exhaustionClosedCollarInnerHarmonicMeasure_mem_Icc
          hmn hnonempty x hx_collar
      simpa [omega] using hIcc.1
    have hH_nonneg : 0 ≤ (B n).boundaryHeightAt q := by
      exact (B n).boundaryHeightAt_nonnegative
        (E.carrier_mono hmn.le hq_inner)
    have hhalf_le_one_sub : (1 / 2 : ℝ) ≤ 1 - omega := by
      linarith
    have hH_half_le :
        (B n).boundaryHeightAt q * (1 / 2 : ℝ) ≤
          (B n).boundaryHeightAt q * (1 - omega) :=
      mul_le_mul_of_nonneg_left hhalf_le_one_sub hH_nonneg
    have hmin_le_L : min L 0 ≤ L := min_le_left L 0
    have hmin_nonpos : min L 0 ≤ 0 := min_le_right L 0
    have hmin_half_le_min_ω :
        min L 0 * (1 / 2 : ℝ) ≤ min L 0 * omega :=
      mul_le_mul_of_nonpos_left hω_le_half hmin_nonpos
    have hmin_ω_le_Lω : min L 0 * omega ≤ L * omega :=
      mul_le_mul_of_nonneg_right hmin_le_L hω_nonneg
    have hL_half_le :
        min L 0 * (1 / 2 : ℝ) ≤ L * omega :=
      hmin_half_le_min_ω.trans hmin_ω_le_Lω
    have htarget :
        A ≤
          (B n).boundaryHeightAt q * (1 / 2 : ℝ) +
            min L 0 * (1 / 2 : ℝ) := by
      dsimp [R] at hheight_n
      linarith
    have hinterp_ge :
        A ≤
          (B n).boundaryHeightAt q -
            ((B n).boundaryHeightAt q - L) * omega := by
      nlinarith
    have hweighted :
        (B n).boundaryHeightAt q -
            ((B n).boundaryHeightAt q - L) *
              E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x
          ≤ (B n).centeredAt q x :=
      centered_boundedNegativeGreen_closedCollar_lower_bound_by_inner_harmonicMeasure
        (E := E) (p := p) (q := q) (m := m) (n := n)
        hmn (B n) hp_inner hnonempty hinner_n x hx_collar
    exact hinterp_ge.trans (by simpa [omega] using hweighted)

/--
%%handwave
name:
  Weighted collar capacity estimates give exterior lower growth
statement:
  Suppose the centered Green functions have a uniform eventual lower bound on
  one fixed inner exhaustion boundary.  If the capacitary interpolation
  between this inner lower bound and the moving outer boundary height is
  eventually above any prescribed level outside one compact set, then the
  centered Green functions themselves satisfy the same exterior lower-growth
  conclusion.
proof:
  Put the fixed inner closure into the compact exceptional set.  A point of a
  late bounded domain outside that compact set lies in the closed collar
  between the fixed inner boundary and the moving outer boundary.  The
  collar comparison theorem bounds the centered Green function from below by
  the capacitary interpolation, and the assumed weighted capacity estimate
  gives the required lower bound.
-/
theorem centered_boundedNegativeGreen_exhaustion_eventual_exterior_large_of_inner_boundary_lower_bound_and_weighted_capacity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {m : ℕ}
    (hp_inner : p ∈ (E.domain m).carrier)
    (hinner_lower :
      ∃ L : ℝ,
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ y ∈ (E.domain m).boundary, L ≤ (B n).centeredAt q y)
    (hweighted_capacity :
      ∀ A L : ℝ,
        ∃ K : Set X, IsCompact K ∧ p ∈ K ∧ q ∈ K ∧
          closure (E.domain m).carrier ⊆ K ∧
          ∀ᶠ n : ℕ in Filter.atTop,
            ∀ (hmn : m < n) (hnonempty : (E.closedCollar m n).Nonempty),
              ∀ x ∈ E.closedCollar m n, x ∉ K →
                A ≤
                  (B n).boundaryHeightAt q -
                    ((B n).boundaryHeightAt q - L) *
                      E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x) :
    ∀ A : ℝ, ∃ K : Set X, IsCompact K ∧ p ∈ K ∧ q ∈ K ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x : X, x ∈ (E.domain n).carrier → x ∉ K →
          A ≤ (B n).centeredAt q x := by
  intro A
  rcases hinner_lower with ⟨L, hinner_event⟩
  rcases hweighted_capacity A L with
    ⟨K, hK_compact, hpK, hqK, hinner_closure_subset, hcapacity_event⟩
  refine ⟨K, hK_compact, hpK, hqK, ?_⟩
  have hlate : ∀ᶠ n : ℕ in Filter.atTop, m < n := by
    refine Filter.eventually_atTop.2 ⟨m + 1, ?_⟩
    intro n hn
    exact Nat.lt_of_succ_le hn
  filter_upwards [hinner_event, hcapacity_event, hlate] with
    n hinner_n hcapacity_n hmn x hx_domain hx_notK
  have hx_not_inner : x ∉ (E.domain m).carrier := by
    intro hx_inner
    exact hx_notK (hinner_closure_subset (subset_closure hx_inner))
  have hx_outer_sdiff :
      x ∈ (E.domain n).carrier \ (E.domain m).carrier :=
    ⟨hx_domain, hx_not_inner⟩
  rcases
      E.outer_sdiff_inner_subset_inner_boundary_union_closedCollar
        (m := m) (n := n) hx_outer_sdiff with
    hx_boundary | hx_collar
  · have hx_closure : x ∈ closure (E.domain m).carrier := by
      have hx_frontier : x ∈ frontier (E.domain m).carrier := by
        simpa [SmoothBoundaryDomain.boundary] using hx_boundary
      exact frontier_subset_closure hx_frontier
    exact False.elim (hx_notK (hinner_closure_subset hx_closure))
  · have hnonempty : (E.closedCollar m n).Nonempty := ⟨x, hx_collar⟩
    have hcapacity :
        A ≤
          (B n).boundaryHeightAt q -
            ((B n).boundaryHeightAt q - L) *
              E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x :=
      hcapacity_n hmn hnonempty x hx_collar hx_notK
    have hweighted :
        (B n).boundaryHeightAt q -
            ((B n).boundaryHeightAt q - L) *
              E.exhaustionClosedCollarInnerHarmonicMeasure hmn hnonempty x
          ≤ (B n).centeredAt q x :=
      centered_boundedNegativeGreen_closedCollar_lower_bound_by_inner_harmonicMeasure
        (E := E) (p := p) (q := q) (m := m) (n := n)
        hmn (B n) hp_inner hnonempty hinner_n x hx_collar
    exact hcapacity.trans hweighted

/--
%%handwave
name:
  Inner-boundary control traps positive Green superlevels inside the inner
  exhaustion domain
statement:
  Suppose \(-G\le\varepsilon\) on the boundary of an inner exhaustion domain
  and \(\varepsilon\ge0\).  Then no point outside the inner domain but inside
  the outer domain can satisfy \(\varepsilon<-G\).
proof:
  A point outside the inner domain is either on the inner boundary or in the
  closed collar.  The boundary estimate handles the first case, and the
  closed-collar maximum principle handles the second, using the continuity
  included in the bounded Green potential.
-/
theorem neg_boundedNegativeGreen_outer_superlevel_subset_inner_of_inner_boundary_upper_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X} {m n : ℕ}
    (G : BoundedNegativeGreenPotential X (E.domain n) p)
    (hp_inner : p ∈ (E.domain m).carrier)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hinner : ∀ x ∈ (E.domain m).boundary, -G.toFun x ≤ ε) :
    {x : X | x ∈ (E.domain n).carrier ∧ ε < -G.toFun x} ⊆
      (E.domain m).carrier := by
  have hcont : ContinuousOn (fun x : X ↦ -G.toFun x)
      (closure (E.closedCollar m n)) :=
    G.neg_continuousOn_closedCollar_of_continuousOn_punctured_closure
      (E := E) (m := m) (n := n) hp_inner G.continuousOn_punctured_closure
  have hcollar :
      ∀ x ∈ E.closedCollar m n, -G.toFun x ≤ ε :=
    neg_boundedNegativeGreen_closedCollar_upper_bound_of_inner_boundary_upper_bound
      G hp_inner hcont hε hinner
  intro x hx
  by_contra hx_not_inner
  have hx_outside :
      x ∈ (E.domain n).carrier \ (E.domain m).carrier :=
    ⟨hx.1, hx_not_inner⟩
  rcases
      E.outer_sdiff_inner_subset_inner_boundary_union_closedCollar
        (m := m) (n := n) hx_outside with
    hx_boundary | hx_collar
  · exact (not_lt_of_ge (hinner x hx_boundary)) hx.2
  · exact (not_lt_of_ge (hcollar x hx_collar)) hx.2

/--
%%handwave
name:
  Inner-boundary and outer-height control trap centered sublevels inside the
  inner exhaustion domain
statement:
  Suppose the centered potential is at least \(A\) on the inner boundary, its
  outer boundary height is at least \(A\).  Then no point outside the inner
  domain but inside the outer domain can have centered value below \(A\).
proof:
  A point outside the inner domain is either on the inner boundary or in the
  closed collar.  The inner boundary lower bound handles the first case.  The
  outer height and inner boundary lower bound propagate through the collar by
  the closed-collar maximum principle, using the continuity included in the
  bounded Green potential, handling the second.
-/
theorem centered_boundedNegativeGreen_outer_sublevel_subset_inner_of_inner_boundary_and_outer_height
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X} {m n : ℕ}
    (G : BoundedNegativeGreenPotential X (E.domain n) p)
    (hp_inner : p ∈ (E.domain m).carrier)
    {A : ℝ}
    (houter_height : A ≤ G.boundaryHeightAt q)
    (hinner : ∀ x ∈ (E.domain m).boundary, A ≤ G.centeredAt q x) :
    {x : X | x ∈ (E.domain n).carrier ∧ G.centeredAt q x < A} ⊆
      (E.domain m).carrier := by
  have hcont : ContinuousOn (G.centeredAt q) (closure (E.closedCollar m n)) :=
    G.centeredAt_continuousOn_closedCollar_of_continuousOn_punctured_closure
      (E := E) (m := m) (n := n) (q := q) hp_inner
      G.continuousOn_punctured_closure
  have hcollar :
      ∀ x ∈ E.closedCollar m n, A ≤ G.centeredAt q x :=
    centered_boundedNegativeGreen_closedCollar_lower_bound_of_inner_boundary_and_outer_height
      G hp_inner hcont houter_height hinner
  intro x hx
  by_contra hx_not_inner
  have hx_outside :
      x ∈ (E.domain n).carrier \ (E.domain m).carrier :=
    ⟨hx.1, hx_not_inner⟩
  rcases
      E.outer_sdiff_inner_subset_inner_boundary_union_closedCollar
        (m := m) (n := n) hx_outside with
    hx_boundary | hx_collar
  · exact (not_lt_of_ge (hinner x hx_boundary)) hx.2
  · exact (not_lt_of_ge (hcollar x hx_collar)) hx.2

/--
%%handwave
name:
  Positive Green superlevels crossing an exhaustion collar meet the inner
  boundary
statement:
  If a point in the outer bounded domain but outside an inner exhaustion
  domain has \(-G>\varepsilon\), with \(\varepsilon\ge0\), then the inner
  exhaustion boundary contains a point with \(-G>\varepsilon\).
proof:
  Otherwise the positive Green function would be at most \(\varepsilon\) on
  the inner boundary.  The closed-collar maximum principle would then trap
  the strict superlevel inside the inner domain, contradicting the chosen
  point.
-/
theorem neg_boundedNegativeGreen_outer_superlevel_inner_boundary_witness_of_not_mem_inner
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X} {m n : ℕ}
    (G : BoundedNegativeGreenPotential X (E.domain n) p)
    (hp_inner : p ∈ (E.domain m).carrier)
    {ε : ℝ} (hε : 0 ≤ ε)
    {x : X}
    (hxdomain : x ∈ (E.domain n).carrier)
    (hx_not_inner : x ∉ (E.domain m).carrier)
    (hsuper : ε < -G.toFun x) :
    ∃ y : X, y ∈ (E.domain m).boundary ∧ ε < -G.toFun y := by
  by_contra hno
  have hinner : ∀ y ∈ (E.domain m).boundary, -G.toFun y ≤ ε := by
    intro y hy
    exact le_of_not_gt (by
      intro hygt
      exact hno ⟨y, hy, hygt⟩)
  have hsubset :
      {z : X | z ∈ (E.domain n).carrier ∧ ε < -G.toFun z} ⊆
        (E.domain m).carrier :=
    neg_boundedNegativeGreen_outer_superlevel_subset_inner_of_inner_boundary_upper_bound
      (E := E) (p := p) (m := m) (n := n) G hp_inner hε hinner
  exact hx_not_inner (hsubset ⟨hxdomain, hsuper⟩)

/--
%%handwave
name:
  Centered Green sublevels crossing an exhaustion collar meet the inner boundary
statement:
  If the outer boundary height is at least \(A\) and a point in the outer
  bounded domain but outside an inner exhaustion domain has centered value
  below \(A\), then the inner exhaustion boundary also contains a point with
  centered value below \(A\).
proof:
  Otherwise the centered potential is at least \(A\) on the inner boundary.
  Together with the outer boundary height lower bound, the closed-collar
  maximum principle traps the strict sublevel inside the inner domain, which
  contradicts the chosen point.
-/
theorem centered_boundedNegativeGreen_outer_sublevel_inner_boundary_witness_of_not_mem_inner_and_outer_height
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X} {m n : ℕ}
    (G : BoundedNegativeGreenPotential X (E.domain n) p)
    (hp_inner : p ∈ (E.domain m).carrier)
    {A : ℝ}
    (houter_height : A ≤ G.boundaryHeightAt q)
    {x : X}
    (hxdomain : x ∈ (E.domain n).carrier)
    (hx_not_inner : x ∉ (E.domain m).carrier)
    (hsub : G.centeredAt q x < A) :
    ∃ y : X, y ∈ (E.domain m).boundary ∧ G.centeredAt q y < A := by
  by_contra hno
  have hinner : ∀ y ∈ (E.domain m).boundary, A ≤ G.centeredAt q y := by
    intro y hy
    exact le_of_not_gt (by
      intro hylt
      exact hno ⟨y, hy, hylt⟩)
  have hsubset :
      {z : X | z ∈ (E.domain n).carrier ∧ G.centeredAt q z < A} ⊆
        (E.domain m).carrier :=
    centered_boundedNegativeGreen_outer_sublevel_subset_inner_of_inner_boundary_and_outer_height
      (E := E) (p := p) (q := q) (m := m) (n := n)
      G hp_inner houter_height hinner
  exact hx_not_inner (hsubset ⟨hxdomain, hsub⟩)

/--
%%handwave
name:
  Escaping positive superlevel sequences have moving inner-boundary witnesses
statement:
  If positive Green superlevel points escape the corresponding exhaustion
  closures, then at every index the matching inner exhaustion boundary also
  contains a point in the same positive superlevel.
proof:
  An escaping point is outside the inner exhaustion domain because that domain
  is contained in its closure.  Apply the collar-crossing boundary-witness
  lemma at each index.
-/
theorem neg_boundedNegativeGreen_exhaustion_escaping_positive_superlevel_sequence_inner_boundary_witness
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X}
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier)
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {ε : ℝ} (hε : 0 ≤ ε)
    (ν : ℕ → ℕ) (x : ℕ → X)
    (hdomain : ∀ j : ℕ, x j ∈ (E.domain (ν j)).carrier)
    (hsuper : ∀ j : ℕ, ε < -((B (ν j)).toFun (x j)))
    (hescape : ∀ j : ℕ, x j ∉ closure (E.domain j).carrier) :
    ∀ j : ℕ,
      ∃ y : X, y ∈ (E.domain j).boundary ∧
        ε < -((B (ν j)).toFun y) := by
  intro j
  have hx_not_inner : x j ∉ (E.domain j).carrier := by
    intro hx_inner
    exact hescape j (subset_closure hx_inner)
  exact
    neg_boundedNegativeGreen_outer_superlevel_inner_boundary_witness_of_not_mem_inner
      (E := E) (p := p) (m := j) (n := ν j)
      (B (ν j)) (hp j) hε (hdomain j) hx_not_inner (hsuper j)

/--
%%handwave
name:
  Escaping centered sublevel sequences have moving inner-boundary witnesses
statement:
  If centered sublevel points escape the corresponding exhaustion closures and
  the outer boundary height is at least the sublevel, then the matching inner
  exhaustion boundary contains a point in the same centered sublevel.
proof:
  Since an escaping point is outside the inner domain, the deterministic
  collar-crossing sublevel witness applies at each index with the supplied
  outer-height lower bound.
-/
theorem centered_boundedNegativeGreen_exhaustion_escaping_sublevel_sequence_inner_boundary_witness_of_outer_height
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier)
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    (A : ℝ)
    (ν : ℕ → ℕ) (x : ℕ → X)
    (houter : ∀ j : ℕ, A ≤ (B (ν j)).boundaryHeightAt q)
    (hdomain : ∀ j : ℕ, x j ∈ (E.domain (ν j)).carrier)
    (hsub : ∀ j : ℕ, (B (ν j)).centeredAt q (x j) < A)
    (hescape : ∀ j : ℕ, x j ∉ closure (E.domain j).carrier) :
    ∀ j : ℕ,
      ∃ y : X, y ∈ (E.domain j).boundary ∧
        (B (ν j)).centeredAt q y < A := by
  intro j
  have hx_not_inner : x j ∉ (E.domain j).carrier := by
    intro hx_inner
    exact hescape j (subset_closure hx_inner)
  exact
    centered_boundedNegativeGreen_outer_sublevel_inner_boundary_witness_of_not_mem_inner_and_outer_height
      (E := E) (p := p) (q := q) (m := j) (n := ν j)
      (B (ν j)) (hp j) (houter j) (hdomain j) hx_not_inner (hsub j)

/--
%%handwave
name:
  Eventual inner-boundary control traps positive Green superlevels
statement:
  If, eventually in the exhaustion, \(-G_n\) is bounded by a positive level
  on a fixed inner boundary, then the positive superlevel
  \(\{-G_n>\varepsilon\}\) is eventually contained in the fixed inner
  exhaustion domain.
proof:
  On each sufficiently late index apply the deterministic closed-collar
  trapping lemma; the needed collar continuity is part of each bounded Green
  potential.
-/
theorem neg_boundedNegativeGreen_exhaustion_eventual_positive_superlevel_subset_inner_of_eventual_boundary_upper_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {m : ℕ} (hp_inner : p ∈ (E.domain m).carrier)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hinner :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x ∈ (E.domain m).boundary, -((B n).toFun x) ≤ ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      {x : X | x ∈ (E.domain n).carrier ∧ ε < -((B n).toFun x)} ⊆
        (E.domain m).carrier := by
  filter_upwards [hinner] with n hinner_n
  exact
    neg_boundedNegativeGreen_outer_superlevel_subset_inner_of_inner_boundary_upper_bound
      (E := E) (p := p) (m := m) (n := n)
      (B n) hp_inner hε hinner_n

/--
%%handwave
name:
  Eventual inner-boundary control and divergent outer heights trap centered
  Green sublevels
statement:
  If the outer boundary heights tend to \(+\infty\), and eventually the
  centered potentials are at least \(A\) on a fixed inner boundary, then the
  sublevel \(\{G_n-G_n(q)<A\}\) is eventually contained in the fixed inner
  exhaustion domain.
proof:
  The divergent outer heights eventually give the lower bound \(A\) on the
  outer boundary.  Together with the eventual inner-boundary estimates and
  the continuity packaged with each bounded Green potential, the deterministic
  closed-collar trapping lemma applies at each sufficiently late index.
-/
theorem centered_boundedNegativeGreen_exhaustion_eventual_sublevel_subset_inner_of_eventual_boundary_lower_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {m : ℕ} (hp_inner : p ∈ (E.domain m).carrier)
    (hheights :
      Filter.Tendsto
        (fun n : ℕ ↦ (B n).boundaryHeightAt q)
        Filter.atTop Filter.atTop)
    (A : ℝ)
    (hinner :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x ∈ (E.domain m).boundary, A ≤ (B n).centeredAt q x) :
    ∀ᶠ n : ℕ in Filter.atTop,
      {x : X | x ∈ (E.domain n).carrier ∧ (B n).centeredAt q x < A} ⊆
        (E.domain m).carrier := by
  have houter :
      ∀ᶠ n : ℕ in Filter.atTop, A ≤ (B n).boundaryHeightAt q :=
    hheights.eventually_ge_atTop A
  filter_upwards [houter, hinner] with n houter_n hinner_n
  exact
    centered_boundedNegativeGreen_outer_sublevel_subset_inner_of_inner_boundary_and_outer_height
      (E := E) (p := p) (q := q) (m := m) (n := n)
      (B n) hp_inner houter_n hinner_n

/--
%%handwave
name:
  Punctured closed-domain continuity and inner-boundary control trap positive
  Green superlevels
statement:
  If \(-G_n\le\varepsilon\) eventually on a fixed inner boundary, then the
  positive superlevel \(\{-G_n>\varepsilon\}\) is eventually contained in the
  fixed inner exhaustion domain.
proof:
  This is an immediate compatibility wrapper around the eventual trapping
  theorem, since bounded Green potentials now include punctured closed-domain
  continuity.
-/
theorem neg_boundedNegativeGreen_exhaustion_eventual_positive_superlevel_subset_inner_of_eventual_boundary_upper_bound_and_punctured_closure_continuity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {m : ℕ} (hp_inner : p ∈ (E.domain m).carrier)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hinner :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x ∈ (E.domain m).boundary, -((B n).toFun x) ≤ ε)
    (_hclosed_cont :
      ∀ᶠ n : ℕ in Filter.atTop,
        ContinuousOn (B n).toFun (closure (E.domain n).carrier \ {p})) :
    ∀ᶠ n : ℕ in Filter.atTop,
      {x : X | x ∈ (E.domain n).carrier ∧ ε < -((B n).toFun x)} ⊆
        (E.domain m).carrier := by
  exact
    neg_boundedNegativeGreen_exhaustion_eventual_positive_superlevel_subset_inner_of_eventual_boundary_upper_bound
      (E := E) (p := p) B hp_inner hε hinner

/--
%%handwave
name:
  Punctured closed-domain continuity and inner-boundary control trap centered
  Green sublevels
statement:
  If the outer heights tend to \(+\infty\), and the centered potentials are
  eventually at least \(A\) on a fixed inner boundary, then the sublevel
  \(\{G_n-G_n(q)<A\}\) is eventually contained in the fixed inner exhaustion
  domain.
proof:
  This is an immediate compatibility wrapper around the eventual centered
  trapping theorem, since bounded Green potentials now include punctured
  closed-domain continuity.
-/
theorem centered_boundedNegativeGreen_exhaustion_eventual_sublevel_subset_inner_of_eventual_boundary_lower_bound_and_punctured_closure_continuity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {m : ℕ} (hp_inner : p ∈ (E.domain m).carrier)
    (hheights :
      Filter.Tendsto
        (fun n : ℕ ↦ (B n).boundaryHeightAt q)
        Filter.atTop Filter.atTop)
    (A : ℝ)
    (hinner :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x ∈ (E.domain m).boundary, A ≤ (B n).centeredAt q x)
    (_hclosed_cont :
      ∀ᶠ n : ℕ in Filter.atTop,
        ContinuousOn (B n).toFun (closure (E.domain n).carrier \ {p})) :
    ∀ᶠ n : ℕ in Filter.atTop,
      {x : X | x ∈ (E.domain n).carrier ∧ (B n).centeredAt q x < A} ⊆
        (E.domain m).carrier := by
  exact
    centered_boundedNegativeGreen_exhaustion_eventual_sublevel_subset_inner_of_eventual_boundary_lower_bound
      (E := E) (p := p) (q := q) B hp_inner hheights A hinner

/--
%%handwave
name:
  Centered exhaustion Green potentials are eventually harmonic on compact
  punctured regions
statement:
  Let \(U\) be a surface region whose closure is compact and avoids the pole.
  Along a smooth exhaustion, all sufficiently late centered bounded-domain
  Green potentials are harmonic on \(U\).
proof:
  The compact closure of \(U\) eventually lies inside the exhaustion domains.
  Since the closure avoids the pole, \(U\) is contained in the punctured
  domain of each sufficiently late bounded-domain Green potential, where the
  centered potential is harmonic.
-/
theorem centered_boundedNegativeGreen_eventually_harmonic_on_relativelyCompact_punctured_region
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {U : Set X}
    (hU_compact_closure : IsCompact (closure U))
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p}) :
    ∀ᶠ n : ℕ in Filter.atTop,
      IsHarmonicOnSurface U ((B n).centeredAt q) := by
  filter_upwards
    [E.eventually_compact_subset_domain hU_compact_closure] with n hn
  exact harmonicOnSurface_mono
    (U := U) (V := (E.domain n).carrier \ {p})
    (by
      intro x hxU
      exact ⟨hn (subset_closure hxU), hU_punctured_closure (subset_closure hxU)⟩)
    ((B n).centeredAt_harmonic_away_pole q)

/--
%%handwave
name:
  Centered exhaustion Green subsequences are eventually harmonic on compact
  punctured regions
statement:
  The eventual harmonicity on a relatively compact punctured region persists
  after passing to any strictly increasing subsequence of the exhaustion.
proof:
  Strictly increasing subsequences tend to infinity, so they preserve every
  eventual property of the original exhaustion sequence.
-/
theorem centered_boundedNegativeGreen_eventually_harmonic_on_relativelyCompact_punctured_region_comp_strictMono
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {U : Set X}
    (hU_compact_closure : IsCompact (closure U))
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p}) :
    ∀ᶠ k : ℕ in Filter.atTop,
      IsHarmonicOnSurface U ((B (φ k)).centeredAt q) := by
  exact hφ.tendsto_atTop.eventually
    (centered_boundedNegativeGreen_eventually_harmonic_on_relativelyCompact_punctured_region
      (E := E) (p := p) (q := q) B hU_compact_closure hU_punctured_closure)

/--
%%handwave
name:
  Centered Green subsequences have compact uniform limits on compact regions
statement:
  If a centered bounded-domain Green subsequence is pointwise relatively
  compact and locally equicontinuous on a compact punctured region, then it
  has a further subsequence that converges uniformly on that compact region.
proof:
  Eventual harmonicity on the surrounding punctured region gives continuity
  after discarding finitely many terms.  The compact-restriction
  Arzelà-Ascoli extraction theorem then applies to the shifted sequence, and
  the finite shift is absorbed into the selected subsequence.
-/
theorem centered_boundedNegativeGreen_subsequence_extracts_uniformLimit_on_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {K U : Set X}
    (hU_open : IsOpen U)
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hpointwise :
      ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ k : ℕ, (B (φ k)).centeredAt q x ∈ Q)
    (heq_tail :
      ∃ N₀ : ℕ,
        EquicontinuousOn
          (fun n : ℕ ↦ fun x : X ↦ (B (φ (N₀ + n))).centeredAt q x) K) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ f : X → ℝ,
        TendstoUniformlyOn
          (fun n : ℕ ↦ fun x : X ↦ (B (φ (ψ n))).centeredAt q x)
          f Filter.atTop K := by
  classical
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  let F : ℕ → X → ℝ := fun k x ↦ (B (φ k)).centeredAt q x
  rcases Filter.eventually_atTop.mp
      (centered_boundedNegativeGreen_eventually_harmonic_on_relativelyCompact_punctured_region_comp_strictMono
        (E := E) (p := p) (q := q) B hφ hU_compact_closure hU_punctured_closure) with
    ⟨N, hN⟩
  rcases heq_tail with ⟨Neq, heq₀⟩
  let Ntail : ℕ := N + Neq
  have hcont : ∀ n : ℕ, ContinuousOn (F (Ntail + n)) K := by
    intro n
    have hharm : IsHarmonicOnSurface U (F (Ntail + n)) := by
      have hN_le : N ≤ Ntail + n := by
        simpa [Ntail, Nat.add_assoc] using Nat.le_add_right N (Neq + n)
      simpa [F] using hN (Ntail + n) hN_le
    exact (harmonicOnSurface_continuousOn hU_open hharm).mono hKU
  have hpointwise_tail :
      ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ n : ℕ, F (Ntail + n) x ∈ Q := by
    intro x hxK
    rcases hpointwise x hxK with ⟨Q, hQ_compact, hQ_mem⟩
    exact ⟨Q, hQ_compact, fun n ↦ by simpa [F] using hQ_mem (Ntail + n)⟩
  have heq : EquicontinuousOn (fun n : ℕ ↦ F (Ntail + n)) K := by
    intro x hxK V hV
    filter_upwards [heq₀ x hxK V hV] with y hy n
    have hidx : Neq + (N + n) = Ntail + n := by
      simp [Ntail, Nat.add_comm, Nat.add_left_comm]
    have h := hy (N + n)
    rw [hidx] at h
    simpa [F] using h
  rcases realFunctions_tail_subsequence_tendstoUniformlyOn_of_compact_equicontinuousOn
      hK_compact Ntail hcont hpointwise_tail heq with
    ⟨ψ, hψ, f, hf⟩
  exact ⟨ψ, hψ, f, by simpa [F] using hf⟩

/--
%%handwave
name:
  Centered Green subsequences have compact uniform limits away from the pole
statement:
  If a centered bounded-domain Green subsequence is pointwise relatively
  compact and locally equicontinuous on a compact set avoiding the pole, then
  it has a further subsequence that converges uniformly on that compact set.
proof:
  The compact set eventually lies inside the exhaustion domains and avoids
  the pole, so the centered potentials are eventually harmonic near it and
  hence continuous on it.  Apply compact Arzelà-Ascoli to a tail, then absorb
  the finite shift into the selected subsequence.
-/
theorem centered_boundedNegativeGreen_subsequence_extracts_uniformLimit_on_compact_away_pole
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {K : Set X}
    (hK_compact : IsCompact K)
    (hK_punctured : K ⊆ {x : X | x ≠ p})
    (hpointwise :
      ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ k : ℕ, (B (φ k)).centeredAt q x ∈ Q)
    (heq_tail :
      ∃ N₀ : ℕ,
        EquicontinuousOn
          (fun n : ℕ ↦ fun x : X ↦ (B (φ (N₀ + n))).centeredAt q x) K) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ f : X → ℝ,
        TendstoUniformlyOn
          (fun n : ℕ ↦ fun x : X ↦ (B (φ (ψ n))).centeredAt q x)
          f Filter.atTop K := by
  classical
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  let F : ℕ → X → ℝ := fun k x ↦ (B (φ k)).centeredAt q x
  have hdomain_event :
      ∀ᶠ k : ℕ in Filter.atTop, K ⊆ (E.domain (φ k)).carrier :=
    hφ.tendsto_atTop.eventually
      (E.eventually_compact_subset_domain hK_compact)
  rcases Filter.eventually_atTop.mp hdomain_event with ⟨N, hNdomain⟩
  rcases heq_tail with ⟨Neq, heq₀⟩
  let Ntail : ℕ := N + Neq
  have hcont : ∀ n : ℕ, ContinuousOn (F (Ntail + n)) K := by
    intro n
    have hK_subset :
        K ⊆ (E.domain (φ (Ntail + n))).carrier \ {p} := by
      intro x hxK
      have hN_le : N ≤ Ntail + n := by
        simpa [Ntail, Nat.add_assoc] using Nat.le_add_right N (Neq + n)
      refine ⟨hNdomain (Ntail + n) hN_le hxK, ?_⟩
      simpa using hK_punctured hxK
    have hopen : IsOpen ((E.domain (φ (Ntail + n))).carrier \ {p}) :=
      (E.domain (φ (Ntail + n))).isOpen.sdiff isClosed_singleton
    exact
      (harmonicOnSurface_continuousOn hopen
        ((B (φ (Ntail + n))).centeredAt_harmonic_away_pole q)).mono hK_subset
  have hpointwise_tail :
      ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ n : ℕ, F (Ntail + n) x ∈ Q := by
    intro x hxK
    rcases hpointwise x hxK with ⟨Q, hQ_compact, hQ_mem⟩
    exact ⟨Q, hQ_compact, fun n ↦ by simpa [F] using hQ_mem (Ntail + n)⟩
  have heq : EquicontinuousOn (fun n : ℕ ↦ F (Ntail + n)) K := by
    intro x hxK V hV
    filter_upwards [heq₀ x hxK V hV] with y hy n
    have hidx : Neq + (N + n) = Ntail + n := by
      simp [Ntail, Nat.add_comm, Nat.add_left_comm]
    have h := hy (N + n)
    rw [hidx] at h
    simpa [F] using h
  rcases realFunctions_tail_subsequence_tendstoUniformlyOn_of_compact_equicontinuousOn
      hK_compact Ntail hcont hpointwise_tail heq with
    ⟨ψ, hψ, f, hf⟩
  exact ⟨ψ, hψ, f, by simpa [F] using hf⟩

/--
%%handwave
name:
  Centered Green subsequences have compact-local convergent subsequences
statement:
  If centered bounded-domain Green potentials are pointwise relatively
  compact and equicontinuous on compact subsets away from the pole, then a
  further subsequence converges uniformly on every compact subset away from
  the pole.
proof:
  Apply the one-compact extraction theorem on the compact members of an
  exhaustion of the punctured surface and diagonalize.  Pointwise compactness
  passes to subsequences, and equicontinuity of the full tail passes to every
  reindexed subfamily.  The resulting punctured-surface limit is transferred
  back to the original surface by assigning an arbitrary value at the pole.
-/
theorem centered_boundedNegativeGreen_subsequence_extracts_compact_convergence_away_pole
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hpq : q ≠ p)
    (hpointwise :
      ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
        ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
          ∀ k : ℕ, (B (φ k)).centeredAt q x ∈ Q)
    (heq_tail :
      ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
        ∃ N : ℕ,
          EquicontinuousOn
            (fun n : ℕ ↦ fun x : X ↦ (B (φ (N + n))).centeredAt q x) K) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ f : X → ℝ,
        ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
          TendstoUniformlyOn
            (fun k : ℕ ↦ (B (φ (ψ k))).centeredAt q)
            f Filter.atTop K := by
  classical
  let U : TopologicalSpace.Opens X :=
    ⟨{x : X | x ≠ p}, by
      simpa using (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})⟩
  let P : Type := U
  haveI : RiemannSurface P :=
    riemannSurface_openSubset U ⟨q, hpq⟩
      (by simpa [U] using punctured_riemannSurface_preconnected X p)
  rcases riemannSurface_compactExhaustion P with ⟨Kp⟩
  let Fp : ℕ → P → ℝ := fun k z ↦ (B (φ k)).centeredAt q z.1
  have hextract :
      ∀ (θ : ℕ → ℕ), StrictMono θ → ∀ m : ℕ,
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∃ f : P → ℝ,
            TendstoUniformlyOn
              (fun n : ℕ ↦ Fp (θ (ψ n))) f Filter.atTop (Kp m) := by
    intro θ hθ m
    let KX : Set X := Subtype.val '' (Kp m)
    have hKp_compact : IsCompact (Kp m) := Kp.isCompact m
    have hKX_compact : IsCompact KX := by
      simpa [KX] using (Subtype.isCompact_iff.mp hKp_compact)
    have hKX_punctured : KX ⊆ {x : X | x ≠ p} := by
      rintro x ⟨z, _hz, rfl⟩
      exact z.2
    have hpointwiseθ :
        ∀ x ∈ KX, ∃ Q : Set ℝ, IsCompact Q ∧
          ∀ k : ℕ, (B (φ (θ k))).centeredAt q x ∈ Q := by
      intro x hxK
      rcases hpointwise KX hKX_compact hKX_punctured x hxK with
        ⟨Q, hQ_compact, hQ_mem⟩
      exact ⟨Q, hQ_compact, fun k ↦ hQ_mem (θ k)⟩
    have heqθ :
        ∃ N : ℕ,
          EquicontinuousOn
            (fun n : ℕ ↦ fun x : X ↦ (B (φ (θ (N + n)))).centeredAt q x) KX := by
      rcases heq_tail KX hKX_compact hKX_punctured with ⟨Neq, heq₀⟩
      rcases Filter.eventually_atTop.mp
          (hθ.tendsto_atTop.eventually (Filter.eventually_ge_atTop Neq)) with
        ⟨M, hM⟩
      refine ⟨M, ?_⟩
      intro x hxK V hV
      filter_upwards [heq₀ x hxK V hV] with y hy n
      have hθ_ge : Neq ≤ θ (M + n) :=
        hM (M + n) (Nat.le_add_right M n)
      let j : ℕ := θ (M + n) - Neq
      have hidx : Neq + j = θ (M + n) := Nat.add_sub_of_le hθ_ge
      have h := hy j
      rw [hidx] at h
      simpa [j] using h
    rcases
      centered_boundedNegativeGreen_subsequence_extracts_uniformLimit_on_compact_away_pole
        (E := E) (p := p) (q := q) B (hφ.comp hθ) hKX_compact
        hKX_punctured hpointwiseθ heqθ with
      ⟨ψ, hψ, fX, hconvX⟩
    refine ⟨ψ, hψ, fun z : P ↦ fX z.1, ?_⟩
    have hconvP :
        TendstoUniformlyOn
          (fun n : ℕ ↦
            ((B (φ (θ (ψ n)))).centeredAt q) ∘ (fun z : P ↦ (z : X)))
          (fX ∘ fun z : P ↦ (z : X)) Filter.atTop
          ((fun z : P ↦ (z : X)) ⁻¹' KX) :=
      hconvX.comp (fun z : P ↦ (z : X))
    refine (hconvP.mono ?_).congr ?_
    · intro z hz
      exact ⟨z, hz, rfl⟩
    · filter_upwards with n z hz
      rfl
  rcases
    realFunctions_subsequence_tendstoUniformlyOn_compactExhaustion_of_subsequence_extractions
      Kp (F := Fp) hextract with
    ⟨ψ, hψ, fP, hconvP⟩
  let f : X → ℝ := fun x ↦ if hx : x ≠ p then fP ⟨x, hx⟩ else 0
  refine ⟨ψ, hψ, f, ?_⟩
  intro K hK_compact hK_punctured
  let KP : Set P := {z : P | z.1 ∈ K}
  have hKP_compact : IsCompact KP := by
    rw [Subtype.isCompact_iff]
    have h_image : Subtype.val '' KP = K := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hxK
        exact ⟨⟨x, hK_punctured hxK⟩, hxK, rfl⟩
    simpa [h_image] using hK_compact
  rcases Kp.exists_superset_of_isCompact hKP_compact with ⟨m, hKPm⟩
  have hconvKP : TendstoUniformlyOn
      (fun n : ℕ ↦ Fp (ψ n)) fP Filter.atTop KP :=
    (hconvP m).mono hKPm
  intro V hV
  filter_upwards [hconvKP V hV] with n hn x hxK
  have hx_ne : x ≠ p := hK_punctured hxK
  have hzK : (⟨x, hx_ne⟩ : P) ∈ KP := hxK
  simpa [Fp, f, hx_ne] using hn ⟨x, hx_ne⟩ hzK

/--
%%handwave
name:
  Two punctured points have a relatively compact preconnected neighborhood
statement:
  If \(q\) and \(x\) are distinct from a pole \(p\), then there is an open
  preconnected region containing both \(q\) and \(x\), whose closure is
  compact and avoids \(p\).
proof:
  Join \(q\) to \(x\) by a path in the punctured surface.  Thicken the compact
  path image to a smooth relatively compact domain inside the punctured
  surface, and take the path component of that domain containing \(q\).
-/
theorem exists_preconnected_relativelyCompact_punctured_neighborhood_pair
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p q x : X}
    (hq : q ≠ p) (hx : x ≠ p) :
    ∃ U : Set X,
      IsOpen U ∧ IsPreconnected U ∧ IsCompact (closure U) ∧
        closure U ⊆ {y : X | y ≠ p} ∧ q ∈ U ∧ x ∈ U := by
  classical
  let γ : Path q x :=
    (punctured_riemannSurface_joinedIn X hq hx).somePath
  have hγ_punctured : ∀ t, γ t ∈ {y : X | y ≠ p} := by
    intro t
    exact (punctured_riemannSurface_joinedIn X hq hx).somePath_mem t
  let K : Set X := Set.range γ
  have hK_compact : IsCompact K := by
    simpa [K, Set.image_univ] using (isCompact_univ.image γ.continuous)
  have hK_nonempty : K.Nonempty := by
    exact ⟨q, by simpa [K] using γ.source_mem_range⟩
  have hpunctured_open : IsOpen {y : X | y ≠ p} := by
    simpa using (isOpen_ne (x := p) : IsOpen {y : X | y ≠ p})
  have hK_punctured : K ⊆ {y : X | y ≠ p} := by
    intro y hy
    rcases hy with ⟨t, rfl⟩
    exact hγ_punctured t
  rcases exists_smoothBoundaryDomain_between_compact_and_open
      (X := X) (K := K) (U := {y : X | y ≠ p})
      hK_compact hK_nonempty hpunctured_open hK_punctured with
    ⟨Ω, hKΩ, hΩ_closure_punctured⟩
  have hqΩ : q ∈ Ω.carrier := by
    exact hKΩ (by simpa [K] using γ.source_mem_range)
  have hxΩ : x ∈ Ω.carrier := by
    exact hKΩ (by simpa [K] using γ.target_mem_range)
  let U : Set X := pathComponentIn Ω.carrier q
  have hqU : q ∈ U := by
    simpa [U] using mem_pathComponentIn_self hqΩ
  have hxU : x ∈ U := by
    change JoinedIn Ω.carrier q x
    exact ⟨γ, fun t ↦ hKΩ ⟨t, rfl⟩⟩
  have hU_open : IsOpen U := by
    simpa [U] using Ω.isOpen.pathComponentIn q
  have hU_preconnected : IsPreconnected U := by
    exact (isPathConnected_pathComponentIn hqΩ).isConnected.isPreconnected
  have hU_subset : U ⊆ Ω.carrier := by
    simpa [U] using (pathComponentIn_subset : pathComponentIn Ω.carrier q ⊆ Ω.carrier)
  have hU_compact : IsCompact (closure U) :=
    Ω.compact_closure.of_isClosed_subset isClosed_closure (closure_mono hU_subset)
  have hU_punctured : closure U ⊆ {y : X | y ≠ p} :=
    (closure_mono hU_subset).trans hΩ_closure_punctured
  exact ⟨U, hU_open, hU_preconnected, hU_compact, hU_punctured, hqU, hxU⟩

/--
%%handwave
name:
  Negated bounded Green subsequences are eventually harmonic on compact
  punctured regions
statement:
  Let \(U\) be a surface region whose closure is compact and avoids the pole.
  Along any strictly increasing subsequence of a smooth exhaustion, the
  negated bounded-domain Green potentials are eventually harmonic on \(U\).
proof:
  The compact closure of \(U\) eventually lies inside the exhaustion domains.
  There the bounded-domain Green potential is harmonic away from the pole,
  and harmonicity is preserved by negation.  Passing to a strictly increasing
  subsequence preserves eventuality.
-/
theorem neg_boundedNegativeGreen_subsequence_eventually_harmonic_on_relativelyCompact_punctured_region
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {U : Set X}
    (hU_compact_closure : IsCompact (closure U))
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p}) :
    ∀ᶠ k : ℕ in Filter.atTop,
      IsHarmonicOnSurface U (fun x : X ↦ -((B (φ k)).toFun x)) := by
  have hfull :
      ∀ᶠ n : ℕ in Filter.atTop,
        IsHarmonicOnSurface U (fun x : X ↦ -((B n).toFun x)) := by
    filter_upwards
      [E.eventually_compact_subset_domain hU_compact_closure] with n hn
    have hB :
        IsHarmonicOnSurface U (B n).toFun :=
      harmonicOnSurface_mono
        (U := U) (V := (E.domain n).carrier \ {p})
        (by
          intro x hxU
          exact ⟨hn (subset_closure hxU), hU_punctured_closure (subset_closure hxU)⟩)
        (B n).harmonic_away_pole
    exact harmonicOnSurface_neg hB
  exact hφ.tendsto_atTop.eventually hfull

/--
%%handwave
name:
  Negated bounded Green subsequences are eventually nonnegative on compact
  regions
statement:
  Let \(U\) be a surface region whose closure is compact.  Along any strictly
  increasing subsequence of a smooth exhaustion, the negated bounded-domain
  Green potentials are eventually nonnegative on \(U\).
proof:
  The compact closure of \(U\) eventually lies inside the exhaustion domains.
  On each such domain the bounded-domain Green potential is nonpositive, so
  its negative is nonnegative.  Passing to a strictly increasing subsequence
  preserves eventuality.
-/
theorem neg_boundedNegativeGreen_subsequence_eventually_nonnegative_on_relativelyCompact_region
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {U : Set X}
    (hU_compact_closure : IsCompact (closure U)) :
    ∀ᶠ k : ℕ in Filter.atTop,
      ∀ x ∈ U, 0 ≤ -((B (φ k)).toFun x) := by
  have hfull :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x ∈ U, 0 ≤ -((B n).toFun x) := by
    filter_upwards
      [E.eventually_compact_subset_domain hU_compact_closure] with n hn x hxU
    exact neg_nonneg.mpr ((B n).nonpositive_on_domain x (hn (subset_closure hxU)))
  exact hφ.tendsto_atTop.eventually hfull

/--
%%handwave
name:
  Negated bounded Green subsequences satisfy local Harnack control
statement:
  On a relatively compact region avoiding the pole, every point has a
  neighborhood on which all sufficiently late negated bounded-domain Green
  potentials are controlled by their value at that point.
proof:
  The negated potentials are eventually harmonic and nonnegative on the
  region.  Apply the local Harnack inequality for nonnegative harmonic
  functions and combine it with these eventual properties.
-/
theorem neg_boundedNegativeGreen_subsequence_eventual_local_harnack_control
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {U : Set X} (hU_open : IsOpen U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    {x : X} (hxU : x ∈ U) :
    ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ y ∈ N,
            -((B (φ k)).toFun y) ≤ C * (-((B (φ k)).toFun x)) := by
  rcases local_harnack_control_for_nonnegative_harmonic_function
      (X := X) hU_open hxU with
    ⟨N, hN_nhds, hN_subset, C, hC_pos, hcontrol⟩
  refine ⟨N, hN_nhds, hN_subset, C, hC_pos, ?_⟩
  filter_upwards
    [neg_boundedNegativeGreen_subsequence_eventually_harmonic_on_relativelyCompact_punctured_region
      (E := E) (p := p) B hφ hU_compact_closure hU_punctured_closure,
     neg_boundedNegativeGreen_subsequence_eventually_nonnegative_on_relativelyCompact_region
      (E := E) (p := p) B hφ hU_compact_closure] with k hharm hnonneg y hyN
  exact hcontrol hharm (fun z hzU ↦ hnonneg z hzU) y hyN

/--
%%handwave
name:
  Negated bounded Green subsequences satisfy pairwise local Harnack control
statement:
  On a relatively compact region avoiding the pole, every point has a
  neighborhood on which all sufficiently late negated bounded-domain Green
  potentials at any two nearby points are comparable by a fixed constant.
proof:
  The negated potentials are eventually harmonic and nonnegative on the
  region.  Apply the pairwise local Harnack inequality for nonnegative
  harmonic functions and combine it with these eventual properties.
-/
theorem neg_boundedNegativeGreen_subsequence_eventual_local_pair_harnack_control
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {U : Set X} (hU_open : IsOpen U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    {x : X} (hxU : x ∈ U) :
    ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ a ∈ N, ∀ b ∈ N,
            -((B (φ k)).toFun a) ≤ C * (-((B (φ k)).toFun b)) := by
  rcases local_harnack_pair_control_for_nonnegative_harmonic_function
      (X := X) hU_open hxU with
    ⟨N, hN_nhds, hN_subset, C, hC_pos, hcontrol⟩
  refine ⟨N, hN_nhds, hN_subset, C, hC_pos, ?_⟩
  filter_upwards
    [neg_boundedNegativeGreen_subsequence_eventually_harmonic_on_relativelyCompact_punctured_region
      (E := E) (p := p) B hφ hU_compact_closure hU_punctured_closure,
     neg_boundedNegativeGreen_subsequence_eventually_nonnegative_on_relativelyCompact_region
      (E := E) (p := p) B hφ hU_compact_closure] with k hharm hnonneg a haN b hbN
  exact hcontrol hharm (fun z hzU ↦ hnonneg z hzU) a haN b hbN

/--
%%handwave
name:
  Bounded boundary heights bound the normalization point
statement:
  If the normalized boundary heights of a subsequence of bounded-domain Green
  potentials are bounded above by \(A\), then the corresponding negated
  potentials take values in \([0,A)\) at the normalization point.
proof:
  At the normalization point, the negated Green potential equals the boundary
  height by definition.  The upper bound is the given bounded-height
  hypothesis, and the lower bound follows from nonpositivity of the
  bounded-domain Green potential.
-/
theorem neg_boundedNegativeGreen_subsequence_base_mem_Ico_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    (hq : ∀ n : ℕ, q ∈ (E.domain n).carrier)
    {φ : ℕ → ℕ} {A : ℝ}
    (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A) :
    ∀ k : ℕ, 0 ≤ -((B (φ k)).toFun q) ∧ -((B (φ k)).toFun q) < A := by
  intro k
  constructor
  · exact neg_nonneg.mpr ((B (φ k)).nonpositive_on_domain q (hq (φ k)))
  · simpa [BoundedNegativeGreenPotential.boundaryHeightAt] using hbound k

/--
%%handwave
name:
  Bounded boundary heights give local bounds for negated Green subsequences
statement:
  If a bounded-height subsequence is normalized at a point \(q\), then on a
  small neighborhood of \(q\) inside any relatively compact punctured region,
  the negated Green potentials are eventually bounded above by a constant
  multiple of the boundary-height bound.
proof:
  Apply local Harnack control at \(q\).  The value at \(q\) is the boundary
  height by definition, so the assumed upper bound propagates to a local
  upper bound.
-/
theorem neg_boundedNegativeGreen_subsequence_eventual_local_bound_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {A : ℝ} (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A)
    {U : Set X} (hU_open : IsOpen U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hqU : q ∈ U) :
    ∃ N : Set X, N ∈ 𝓝 q ∧ N ⊆ U ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ y ∈ N, -((B (φ k)).toFun y) ≤ C * A := by
  rcases neg_boundedNegativeGreen_subsequence_eventual_local_harnack_control
      (E := E) (p := p) B hφ hU_open hU_compact_closure
      hU_punctured_closure hqU with
    ⟨N, hN_nhds, hN_subset, C, hC_pos, hcontrol⟩
  refine ⟨N, hN_nhds, hN_subset, C, hC_pos, ?_⟩
  filter_upwards [hcontrol] with k hk y hyN
  have hbase_le : -((B (φ k)).toFun q) ≤ A := by
    exact le_of_lt (by
      simpa [BoundedNegativeGreenPotential.boundaryHeightAt] using hbound k)
  exact (hk y hyN).trans (mul_le_mul_of_nonneg_left hbase_le hC_pos.le)

/--
%%handwave
name:
  Bounded boundary heights give pointwise bounds on preconnected regions
statement:
  If a bounded-height subsequence is normalized at a point \(q\), then on any
  preconnected relatively compact region avoiding the pole and containing
  \(q\), the negated Green potentials are eventually bounded above at every
  point.
proof:
  The boundary-height bound gives an eventual upper bound at \(q\).  Pairwise
  local Harnack control propagates this boundedness through the preconnected
  region.
-/
theorem neg_boundedNegativeGreen_subsequence_eventual_pointwise_bound_on_preconnected_region_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {A : ℝ} (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A)
    {U : Set X} (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hqU : q ∈ U) :
    ∀ x ∈ U,
      ∃ M : ℝ,
        ∀ᶠ k : ℕ in Filter.atTop, -((B (φ k)).toFun x) ≤ M := by
  refine eventual_upper_bound_propagates_of_local_pair_harnack_control
    hU_preconnected ?_ hqU ?_
  · intro x hxU
    rcases neg_boundedNegativeGreen_subsequence_eventual_local_pair_harnack_control
        (E := E) (p := p) B hφ hU_open hU_compact_closure
        hU_punctured_closure hxU with
      ⟨N, hN_nhds, hN_subset, C, hC_pos, hcontrol⟩
    exact ⟨N, hN_nhds, hN_subset, C, hC_pos.le, hcontrol⟩
  · refine ⟨A, ?_⟩
    exact Filter.Eventually.of_forall (fun k ↦
      le_of_lt (by
        simpa [BoundedNegativeGreenPotential.boundaryHeightAt] using hbound k))

/--
%%handwave
name:
  Bounded boundary heights give local uniform bounds on preconnected regions
statement:
  If a bounded-height subsequence is normalized at a point \(q\), then on any
  preconnected relatively compact region avoiding the pole and containing
  \(q\), the negated Green potentials are eventually bounded above uniformly
  near every point.
proof:
  The boundary-height bound gives an eventual upper bound at \(q\).  Pairwise
  local Harnack control first propagates boundedness through the preconnected
  region and then converts the pointwise bound at each center into a uniform
  bound on a neighborhood.
-/
theorem neg_boundedNegativeGreen_subsequence_eventual_locally_uniform_bound_on_preconnected_region_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {A : ℝ} (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A)
    {U : Set X} (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hqU : q ∈ U) :
    ∀ x ∈ U,
      ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
        ∃ M : ℝ,
          ∀ᶠ k : ℕ in Filter.atTop,
            ∀ y ∈ N, -((B (φ k)).toFun y) ≤ M := by
  refine eventual_locally_uniform_upper_bound_propagates_of_local_pair_harnack_control
    hU_preconnected ?_ hqU ?_
  · intro x hxU
    rcases neg_boundedNegativeGreen_subsequence_eventual_local_pair_harnack_control
        (E := E) (p := p) B hφ hU_open hU_compact_closure
        hU_punctured_closure hxU with
      ⟨N, hN_nhds, hN_subset, C, hC_pos, hcontrol⟩
    exact ⟨N, hN_nhds, hN_subset, C, hC_pos.le, hcontrol⟩
  · refine ⟨A, ?_⟩
    exact Filter.Eventually.of_forall (fun k ↦
      le_of_lt (by
        simpa [BoundedNegativeGreenPotential.boundaryHeightAt] using hbound k))

/--
%%handwave
name:
  Bounded boundary heights give compact bounds on preconnected regions
statement:
  If a bounded-height subsequence is normalized at a point \(q\), then on
  every compact subset of any preconnected relatively compact region avoiding
  the pole and containing \(q\), the negated Green potentials have a single
  eventual upper bound.
proof:
  The boundary-height bound gives an eventual upper bound at \(q\).  Pairwise
  local Harnack control propagates this to local uniform bounds throughout
  the preconnected region, and a finite subcover of the compact set gives one
  bound on the whole compact set.
-/
theorem neg_boundedNegativeGreen_subsequence_eventual_uniform_bound_on_compact_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {A : ℝ} (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A)
    {K U : Set X}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hqU : q ∈ U) :
    ∃ M : ℝ,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ y ∈ K, -((B (φ k)).toFun y) ≤ M := by
  refine eventual_uniform_upper_bound_on_compact_propagates_of_local_pair_harnack_control
    hU_preconnected hK_compact hKU ?_ hqU ?_
  · intro x hxU
    rcases neg_boundedNegativeGreen_subsequence_eventual_local_pair_harnack_control
        (E := E) (p := p) B hφ hU_open hU_compact_closure
        hU_punctured_closure hxU with
      ⟨N, hN_nhds, hN_subset, C, hC_pos, hcontrol⟩
    exact ⟨N, hN_nhds, hN_subset, C, hC_pos.le, hcontrol⟩
  · refine ⟨A, ?_⟩
    exact Filter.Eventually.of_forall (fun k ↦
      le_of_lt (by
        simpa [BoundedNegativeGreenPotential.boundaryHeightAt] using hbound k))

/--
%%handwave
name:
  Bounded boundary heights give compact bounds away from the pole
statement:
  If the normalized boundary heights of bounded-domain Green potentials are
  bounded above and \(K\) is a nonempty compact set avoiding the pole, then
  the corresponding positive Green functions are eventually bounded above
  uniformly on \(K\).
proof:
  Put \(K\) and the normalization point in one relatively compact
  preconnected punctured region.  The compact bound for bounded-height
  subsequences, applied to the identity subsequence, gives the desired
  full-exhaustion eventual bound.
-/
theorem neg_boundedNegativeGreen_exhaustion_eventual_uniform_bound_on_compact_away_pole_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    (hpq : q ≠ p)
    {A : ℝ} (hbound : ∀ n : ℕ, (B n).boundaryHeightAt q < A)
    {K : Set X}
    (hK_compact : IsCompact K) (hK_nonempty : K.Nonempty)
    (hK_punctured : K ⊆ {x : X | x ≠ p}) :
    ∃ M : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ y ∈ K, -((B n).toFun y) ≤ M := by
  classical
  let W : K → Set X := fun x =>
    Classical.choose
      (exists_preconnected_relativelyCompact_punctured_neighborhood_pair
        (X := X) (p := p) (q := q) (x := x.1) hpq (hK_punctured x.2))
  have hW_spec :
      ∀ x : K,
        IsOpen (W x) ∧ IsPreconnected (W x) ∧
          IsCompact (closure (W x)) ∧
            closure (W x) ⊆ {y : X | y ≠ p} ∧ q ∈ W x ∧ x.1 ∈ W x := by
    intro x
    exact
      Classical.choose_spec
        (exists_preconnected_relativelyCompact_punctured_neighborhood_pair
          (X := X) (p := p) (q := q) (x := x.1) hpq (hK_punctured x.2))
  have hcover : K ⊆ ⋃ x : K, W x := by
    intro x hxK
    exact Set.mem_iUnion.mpr
      ⟨⟨x, hxK⟩, (hW_spec ⟨x, hxK⟩).2.2.2.2.2⟩
  rcases hK_compact.elim_finite_subcover W
      (fun x ↦ (hW_spec x).1) hcover with
    ⟨t, ht⟩
  rcases hK_nonempty with ⟨x0, hx0K⟩
  let x0K : K := ⟨x0, hx0K⟩
  let t' : Finset K := insert x0K t
  let U : Set X := ⋃ x ∈ t', W x
  have hclosure_eq : closure U = ⋃ x ∈ t', closure (W x) := by
    simpa [U] using (Finset.closure_biUnion t' W)
  have hU_open : IsOpen U := by
    dsimp [U]
    exact isOpen_iUnion fun x ↦ isOpen_iUnion fun _ ↦ (hW_spec x).1
  have hU_preconnected : IsPreconnected U := by
    let C : Set (Set X) := W '' (↑t' : Set K)
    have hqC : ∀ V ∈ C, q ∈ V := by
      rintro V ⟨x, _hxt, rfl⟩
      exact (hW_spec x).2.2.2.2.1
    have hpreC : ∀ V ∈ C, IsPreconnected V := by
      rintro V ⟨x, _hxt, rfl⟩
      exact (hW_spec x).2.1
    have hpre : IsPreconnected (⋃₀ C) :=
      isPreconnected_sUnion q C hqC hpreC
    have hU_eq : U = ⋃₀ C := by
      ext z
      constructor
      · intro hz
        rcases Set.mem_iUnion₂.mp hz with ⟨x, hxt, hzW⟩
        exact ⟨W x, ⟨x, hxt, rfl⟩, hzW⟩
      · intro hz
        rcases hz with ⟨V, hVC, hzV⟩
        rcases hVC with ⟨x, hxt, rfl⟩
        exact Set.mem_iUnion₂.mpr ⟨x, hxt, hzV⟩
    simpa [hU_eq] using hpre
  have hU_compact_closure : IsCompact (closure U) := by
    have hcompact : IsCompact (⋃ x ∈ t', closure (W x)) :=
      t'.isCompact_biUnion fun x _ ↦ (hW_spec x).2.2.1
    simpa [hclosure_eq] using hcompact
  have hU_punctured_closure : closure U ⊆ {x : X | x ≠ p} := by
    intro x hx
    rw [hclosure_eq] at hx
    rcases Set.mem_iUnion₂.mp hx with ⟨y, _hyt, hxy⟩
    exact (hW_spec y).2.2.2.1 hxy
  have hKU : K ⊆ U := by
    intro x hxK
    rcases Set.mem_iUnion₂.mp (ht hxK) with ⟨y, hyt, hxy⟩
    exact Set.mem_iUnion₂.mpr
      ⟨y, Finset.mem_insert.mpr (Or.inr hyt), hxy⟩
  have hqU : q ∈ U := by
    exact Set.mem_iUnion₂.mpr
      ⟨x0K, Finset.mem_insert_self x0K t, (hW_spec x0K).2.2.2.2.1⟩
  let φ : ℕ → ℕ := id
  have hφ : StrictMono φ := strictMono_id
  have hboundφ : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A := by
    intro k
    simpa [φ] using hbound k
  rcases
    neg_boundedNegativeGreen_subsequence_eventual_uniform_bound_on_compact_of_boundaryHeight_bound
      (E := E) (p := p) (q := q) B hφ hboundφ hU_open hU_preconnected
      hK_compact hKU hU_compact_closure hU_punctured_closure hqU with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  simpa [φ] using hM

/--
%%handwave
name:
  Bounded boundary heights give compact interval control
statement:
  If a bounded-height subsequence is normalized at a point \(q\), then on
  every compact subset of a suitable preconnected punctured region, the
  negated Green potentials eventually take values in one fixed compact
  interval \([0,M]\).
proof:
  Nonnegativity of the negated bounded-domain Green potentials gives the
  lower bound.  The compact upper bound obtained from pairwise Harnack
  propagation gives the upper endpoint.
-/
theorem neg_boundedNegativeGreen_subsequence_eventual_mem_Icc_on_compact_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {A : ℝ} (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A)
    {K U : Set X}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hqU : q ∈ U) :
    ∃ M : ℝ,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ y ∈ K, -((B (φ k)).toFun y) ∈ Set.Icc (0 : ℝ) M := by
  rcases neg_boundedNegativeGreen_subsequence_eventual_uniform_bound_on_compact_of_boundaryHeight_bound
      (E := E) (p := p) (q := q) B hφ hbound hU_open hU_preconnected
      hK_compact hKU hU_compact_closure hU_punctured_closure hqU with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  filter_upwards
    [hM,
     neg_boundedNegativeGreen_subsequence_eventually_nonnegative_on_relativelyCompact_region
      (E := E) (p := p) B hφ hU_compact_closure] with k hupper hnonneg y hyK
  exact ⟨hnonneg y (hKU hyK), hupper y hyK⟩

/--
%%handwave
name:
  Bounded boundary heights give compact pointwise range on compact sets
statement:
  If a bounded-height subsequence is normalized at a point \(q\), then on
  every compact subset of a suitable preconnected punctured region, the
  values of the negated Green subsequence at each point lie in a compact
  subset of the real line.
proof:
  The compact interval control gives eventual membership in a fixed closed
  interval.  The finitely many initial values are added to that interval.
-/
theorem neg_boundedNegativeGreen_subsequence_pointwise_compactRange_on_compact_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {A : ℝ} (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A)
    {K U : Set X}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hqU : q ∈ U) :
    ∀ y ∈ K,
      ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ k : ℕ, -((B (φ k)).toFun y) ∈ Q := by
  rcases neg_boundedNegativeGreen_subsequence_eventual_mem_Icc_on_compact_of_boundaryHeight_bound
      (E := E) (p := p) (q := q) B hφ hbound hU_open hU_preconnected
      hK_compact hKU hU_compact_closure hU_punctured_closure hqU with
    ⟨M, hM⟩
  intro y hyK
  exact exists_compact_range_of_eventually_mem_Icc
    (a := fun k : ℕ ↦ -((B (φ k)).toFun y))
    (A := 0) (B := M)
    (by
      filter_upwards [hM] with k hk
      exact hk y hyK)

/--
%%handwave
name:
  Bounded boundary heights give compact pointwise range away from the pole
statement:
  If a bounded-height Green subsequence is normalized at a point \(q\ne p\),
  then at every point \(y\ne p\) the negated potentials take values in a
  compact subset of the real line.
proof:
  Choose a relatively compact preconnected punctured region containing \(q\)
  and \(y\), then apply the compact-range theorem to the singleton \(\{y\}\).
-/
theorem neg_boundedNegativeGreen_subsequence_pointwise_compactRange_away_pole_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hpq : q ≠ p)
    {A : ℝ} (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A) :
    ∀ y : X, y ≠ p →
      ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ k : ℕ, -((B (φ k)).toFun y) ∈ Q := by
  intro y hy
  rcases exists_preconnected_relativelyCompact_punctured_neighborhood_pair
      (X := X) (p := p) (q := q) (x := y) hpq hy with
    ⟨U, hU_open, hU_preconnected, hU_compact_closure,
      hU_punctured_closure, hqU, hyU⟩
  have hsingleton_subset : ({y} : Set X) ⊆ U := by
    intro z hz
    simpa [Set.mem_singleton_iff.mp hz] using hyU
  exact
    neg_boundedNegativeGreen_subsequence_pointwise_compactRange_on_compact_of_boundaryHeight_bound
      (E := E) (p := p) (q := q) B hφ hbound hU_open hU_preconnected
      (isCompact_singleton (x := y)) hsingleton_subset hU_compact_closure
      hU_punctured_closure hqU y (by simp)

/--
%%handwave
name:
  Bounded boundary heights give compact pointwise range on compact punctured sets
statement:
  If a bounded-height Green subsequence is normalized away from the pole, then
  at every point of a compact set avoiding the pole the negated potentials
  take values in a compact subset of the real line.
proof:
  Apply the pointwise away-from-the-pole compact-range theorem at each point
  of the compact set.
-/
theorem neg_boundedNegativeGreen_subsequence_pointwise_compactRange_on_compact_away_pole_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hpq : q ≠ p)
    {A : ℝ} (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A)
    {K : Set X} (hK_punctured : K ⊆ {y : X | y ≠ p}) :
    ∀ y ∈ K,
      ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ k : ℕ, -((B (φ k)).toFun y) ∈ Q := by
  intro y hyK
  exact
    neg_boundedNegativeGreen_subsequence_pointwise_compactRange_away_pole_of_boundaryHeight_bound
      (E := E) (p := p) (q := q) B hφ hpq hbound y (hK_punctured hyK)

/--
%%handwave
name:
  Bounded Green subsequences are equicontinuous on compact sets away from the pole
statement:
  If a bounded-height Green subsequence is normalized away from its pole, then
  the corresponding positive Green functions have an equicontinuous tail on
  every compact set avoiding the pole.
proof:
  Thicken the compact set to a relatively compact smooth region still
  avoiding the pole.  On this fixed region the positive Green functions are
  eventually harmonic.  At each point, Harnack propagation from the
  normalization point gives an eventual pointwise bound, and local Harnack
  control turns it into a local uniform bound.  The bounded-harmonic
  equicontinuity theorem then gives an equicontinuous tail.
-/
theorem neg_boundedNegativeGreen_subsequence_tail_equicontinuousOn_compact_away_pole_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hpq : q ≠ p)
    {A : ℝ} (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A)
    {K : Set X}
    (hK_compact : IsCompact K)
    (hK_punctured : K ⊆ {x : X | x ≠ p}) :
    ∃ N₀ : ℕ,
      EquicontinuousOn
        (fun n : ℕ ↦ fun x : X ↦ -((B (φ (N₀ + n))).toFun x)) K := by
  classical
  by_cases hK_nonempty : K.Nonempty
  · have hpunctured_open : IsOpen {x : X | x ≠ p} := by
      simpa using (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
    rcases exists_smoothBoundaryDomain_between_compact_and_open
        (X := X) (K := K) (U := {x : X | x ≠ p})
        hK_compact hK_nonempty hpunctured_open hK_punctured with
      ⟨ΩK, hKΩK, hΩK_closure_punctured⟩
    let F : ℕ → X → ℝ := fun k x ↦ -((B (φ k)).toFun x)
    refine
      harmonicOnSurface_tail_equicontinuousOn_of_eventually_harmonic_locally_eventual_abs_bound
        (U := ΩK.carrier) (K := K) (F := F) hK_compact ?_ ?_
    · simpa [F] using
        neg_boundedNegativeGreen_subsequence_eventually_harmonic_on_relativelyCompact_punctured_region
          (E := E) (p := p) B hφ ΩK.compact_closure hΩK_closure_punctured
    · intro x hxK
      have hxΩK : x ∈ ΩK.carrier := hKΩK hxK
      rcases neg_boundedNegativeGreen_subsequence_eventual_local_harnack_control
          (E := E) (p := p) B hφ ΩK.isOpen ΩK.compact_closure
          hΩK_closure_punctured hxΩK with
        ⟨N, hN_nhds, hN_subset, C, hC_pos, hcontrol⟩
      have hx_ne : x ≠ p := hK_punctured hxK
      rcases exists_preconnected_relativelyCompact_punctured_neighborhood_pair
          (X := X) (p := p) (q := q) (x := x) hpq hx_ne with
        ⟨Ux, hUx_open, hUx_preconnected, hUx_compact_closure,
          hUx_punctured_closure, hqUx, hxUx⟩
      rcases
        neg_boundedNegativeGreen_subsequence_eventual_pointwise_bound_on_preconnected_region_of_boundaryHeight_bound
          (E := E) (p := p) (q := q) B hφ hbound hUx_open hUx_preconnected
          hUx_compact_closure hUx_punctured_closure hqUx x hxUx with
        ⟨Mx, hMx⟩
      refine ⟨N, hN_nhds, hN_subset, max (C * Mx) 0, ?_⟩
      filter_upwards
        [hcontrol, hMx,
         neg_boundedNegativeGreen_subsequence_eventually_nonnegative_on_relativelyCompact_region
          (E := E) (p := p) B hφ ΩK.compact_closure] with
        k hcontrol_k hMx_k hnonneg_k y hyN
      have hctrl_y : F k y ≤ C * F k x := by
        simpa [F] using hcontrol_k y hyN
      have hMx_x : F k x ≤ Mx := by
        simpa [F] using hMx_k
      have hupper : F k y ≤ C * Mx :=
        hctrl_y.trans (mul_le_mul_of_nonneg_left hMx_x hC_pos.le)
      have hnonneg_y : 0 ≤ F k y := by
        simpa [F] using hnonneg_k y (hN_subset hyN)
      calc
        |F k y| = F k y := abs_of_nonneg hnonneg_y
        _ ≤ C * Mx := hupper
        _ ≤ max (C * Mx) 0 := le_max_left (C * Mx) 0
  · refine ⟨0, ?_⟩
    intro x hxK
    exact False.elim (hK_nonempty ⟨x, hxK⟩)

/--
%%handwave
name:
  Bounded Green subsequences are equicontinuous on compact regions
statement:
  If a subsequence of bounded-domain Green functions has bounded normalized
  boundary height, then some tail of the corresponding positive Green
  functions is equicontinuous on every compact subset of a preconnected
  relatively compact punctured region containing the normalization point.
proof:
  Harnack propagation gives eventual local upper bounds for the positive
  Green functions, while nonpositivity of the original bounded Green
  potentials gives eventual nonnegativity.  These are eventual local absolute
  bounds.  Together with eventual harmonicity on the region, the
  bounded-harmonic equicontinuity theorem gives an equicontinuous tail.
-/
theorem neg_boundedNegativeGreen_subsequence_tail_equicontinuousOn_compact_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {A : ℝ} (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A)
    {K U : Set X}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hqU : q ∈ U) :
    ∃ N₀ : ℕ,
      EquicontinuousOn
        (fun n : ℕ ↦ fun x : X ↦ -((B (φ (N₀ + n))).toFun x)) K := by
  classical
  let F : ℕ → X → ℝ := fun k x ↦ -((B (φ k)).toFun x)
  refine
    harmonicOnSurface_tail_equicontinuousOn_of_eventually_harmonic_locally_eventual_abs_bound
      (U := U) (K := K) (F := F) hK_compact
      (neg_boundedNegativeGreen_subsequence_eventually_harmonic_on_relativelyCompact_punctured_region
        (E := E) (p := p) B hφ hU_compact_closure hU_punctured_closure)
      ?_
  intro x hxK
  rcases
    neg_boundedNegativeGreen_subsequence_eventual_locally_uniform_bound_on_preconnected_region_of_boundaryHeight_bound
      (E := E) (p := p) (q := q) B hφ hbound hU_open hU_preconnected
      hU_compact_closure hU_punctured_closure hqU x (hKU hxK) with
    ⟨N, hN_nhds, hN_subset, M, hM⟩
  refine ⟨N, hN_nhds, hN_subset, max M 0, ?_⟩
  filter_upwards
    [hM,
     neg_boundedNegativeGreen_subsequence_eventually_nonnegative_on_relativelyCompact_region
      (E := E) (p := p) B hφ hU_compact_closure] with k hupper hnonneg y hyN
  have hnonneg_y : 0 ≤ F k y := hnonneg y (hN_subset hyN)
  have hupper_y : F k y ≤ M := hupper y hyN
  calc
    |F k y| = F k y := abs_of_nonneg hnonneg_y
    _ ≤ M := hupper_y
    _ ≤ max M 0 := le_max_left M 0

/--
%%handwave
name:
  Bounded Green subsequences have compact uniform limits on compact regions
statement:
  If a bounded-height Green subsequence is locally equicontinuous on a
  compact subset of a preconnected punctured region, then it has a further
  subsequence that converges uniformly on that compact subset.
proof:
  The bounded-height Harnack propagation gives pointwise compact range on the
  compact set.  Eventual harmonicity gives continuity after discarding a
  finite initial segment.  The compact-restriction Arzelà-Ascoli theorem then
  gives a uniformly convergent further subsequence.
-/
theorem neg_boundedNegativeGreen_subsequence_extracts_uniformLimit_on_compact_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {A : ℝ} (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A)
    {K U : Set X}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hqU : q ∈ U) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ f : X → ℝ,
        TendstoUniformlyOn
          (fun n : ℕ ↦ fun x : X ↦ -((B (φ (ψ n))).toFun x))
          f Filter.atTop K := by
  classical
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  let F : ℕ → X → ℝ := fun k x ↦ -((B (φ k)).toFun x)
  rcases
    neg_boundedNegativeGreen_subsequence_tail_equicontinuousOn_compact_of_boundaryHeight_bound
      (E := E) (p := p) (q := q) B hφ hbound hU_open hU_preconnected
      hK_compact hKU hU_compact_closure hU_punctured_closure hqU with
    ⟨Neq, heq₀⟩
  rcases Filter.eventually_atTop.mp
      (neg_boundedNegativeGreen_subsequence_eventually_harmonic_on_relativelyCompact_punctured_region
        (E := E) (p := p) B hφ hU_compact_closure hU_punctured_closure) with
    ⟨N, hN⟩
  let Ntail : ℕ := N + Neq
  have hcont : ∀ n : ℕ, ContinuousOn (F (Ntail + n)) K := by
    intro n
    have hN_le : N ≤ Ntail + n := by
      simpa [Ntail, Nat.add_assoc] using Nat.le_add_right N (Neq + n)
    have hharm : IsHarmonicOnSurface U (F (Ntail + n)) := by
      simpa [F] using
        hN (Ntail + n) hN_le
    exact (harmonicOnSurface_continuousOn hU_open hharm).mono hKU
  have hpointwise :
      ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ n : ℕ, F (Ntail + n) x ∈ Q := by
    intro x hxK
    rcases
      neg_boundedNegativeGreen_subsequence_pointwise_compactRange_on_compact_of_boundaryHeight_bound
        (E := E) (p := p) (q := q) B hφ hbound hU_open hU_preconnected
      hK_compact hKU hU_compact_closure hU_punctured_closure hqU
      x hxK with
      ⟨Q, hQ_compact, hQ_mem⟩
    exact ⟨Q, hQ_compact, fun n ↦ by simpa [F] using hQ_mem (Ntail + n)⟩
  have heq : EquicontinuousOn (fun n : ℕ ↦ F (Ntail + n)) K := by
    intro x hxK V hV
    filter_upwards [heq₀ x hxK V hV] with y hy n
    simpa [F, Ntail, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      hy (N + n)
  rcases realFunctions_tail_subsequence_tendstoUniformlyOn_of_compact_equicontinuousOn
      hK_compact Ntail hcont hpointwise heq with
    ⟨ψ, hψ, f, hf⟩
  exact ⟨ψ, hψ, f, by simpa [F] using hf⟩

/--
%%handwave
name:
  Bounded Green subsequences have compact uniform limits away from the pole
statement:
  If a bounded-height Green subsequence is locally equicontinuous on a compact
  set avoiding the pole, then it has a further subsequence that converges
  uniformly on that compact set.
proof:
  The compact set eventually lies in the bounded exhaustion domains and stays
  away from the pole, so the negated Green potentials are eventually harmonic
  near it and hence continuous on it.  Bounded-height Harnack propagation
  gives pointwise compact range at every point away from the pole.  Apply the
  compact Arzelà-Ascoli extraction theorem to a tail and absorb the finite
  shift into the selected subsequence.
-/
theorem neg_boundedNegativeGreen_subsequence_extracts_uniformLimit_on_compact_away_pole_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hpq : q ≠ p)
    {A : ℝ} (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A)
    {K : Set X}
    (hK_compact : IsCompact K)
    (hK_punctured : K ⊆ {x : X | x ≠ p}) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ f : X → ℝ,
        TendstoUniformlyOn
          (fun n : ℕ ↦ fun x : X ↦ -((B (φ (ψ n))).toFun x))
          f Filter.atTop K := by
  classical
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  let F : ℕ → X → ℝ := fun k x ↦ -((B (φ k)).toFun x)
  rcases
    neg_boundedNegativeGreen_subsequence_tail_equicontinuousOn_compact_away_pole_of_boundaryHeight_bound
      (E := E) (p := p) (q := q) B hφ hpq hbound hK_compact
      hK_punctured with
    ⟨Neq, heq₀⟩
  have hdomain_event :
      ∀ᶠ k : ℕ in Filter.atTop, K ⊆ (E.domain (φ k)).carrier :=
    hφ.tendsto_atTop.eventually
      (E.eventually_compact_subset_domain hK_compact)
  rcases Filter.eventually_atTop.mp hdomain_event with ⟨Ndom, hNdomain⟩
  let Ntail : ℕ := Ndom + Neq
  have hcont : ∀ n : ℕ, ContinuousOn (F (Ntail + n)) K := by
    intro n
    have hK_subset :
        K ⊆ (E.domain (φ (Ntail + n))).carrier \ {p} := by
      intro x hxK
      have hN_le : Ndom ≤ Ntail + n := by
        simpa [Ntail, Nat.add_assoc] using Nat.le_add_right Ndom (Neq + n)
      refine ⟨hNdomain (Ntail + n) hN_le hxK, ?_⟩
      simpa using hK_punctured hxK
    have hopen : IsOpen ((E.domain (φ (Ntail + n))).carrier \ {p}) :=
      (E.domain (φ (Ntail + n))).isOpen.sdiff isClosed_singleton
    exact
      (harmonicOnSurface_continuousOn hopen
        (harmonicOnSurface_neg (B (φ (Ntail + n))).harmonic_away_pole)).mono
        hK_subset
  have hpointwise :
      ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ n : ℕ, F (Ntail + n) x ∈ Q := by
    intro x hxK
    rcases
      neg_boundedNegativeGreen_subsequence_pointwise_compactRange_on_compact_away_pole_of_boundaryHeight_bound
        (E := E) (p := p) (q := q) B hφ hpq hbound hK_punctured
        x hxK with
      ⟨Q, hQ_compact, hQ_mem⟩
    exact ⟨Q, hQ_compact, fun n ↦ by simpa [F] using hQ_mem (Ntail + n)⟩
  have heq : EquicontinuousOn (fun n : ℕ ↦ F (Ntail + n)) K := by
    intro x hxK V hV
    filter_upwards [heq₀ x hxK V hV] with y hy n
    simpa [F, Ntail, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      hy (Ndom + n)
  rcases realFunctions_tail_subsequence_tendstoUniformlyOn_of_compact_equicontinuousOn
      hK_compact Ntail hcont hpointwise heq with
    ⟨ψ, hψ, f, hf⟩
  exact ⟨ψ, hψ, f, by simpa [F] using hf⟩

/--
%%handwave
name:
  Bounded Green subsequences have compact-local convergent subsequences
statement:
  If the normalized boundary heights of a subsequence of bounded-domain
  negative Green potentials are uniformly bounded, then the associated
  positive Green functions have a further subsequence converging uniformly on
  every compact subset away from the pole.
proof:
  Work on the punctured surface.  On each compact member of a compact
  exhaustion, the one-compact Arzelà-Ascoli theorem extracts a further
  uniformly convergent subsequence using the Harnack bounds and
  equicontinuity.  A diagonal argument gives one subsequence converging on
  all exhaustion members, and hence on every compact subset of the punctured
  surface.  Finally transfer the limit back to the original surface.
-/
theorem neg_boundedNegativeGreen_subsequence_extracts_compact_convergence_away_pole_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hpq : q ≠ p)
    {A : ℝ} (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ f : X → ℝ,
        ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
          TendstoUniformlyOn
            (fun k : ℕ ↦ fun x : X ↦ -((B (φ (ψ k))).toFun x))
            f Filter.atTop K := by
  classical
  let U : TopologicalSpace.Opens X :=
    ⟨{x : X | x ≠ p}, by
      simpa using (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})⟩
  let P : Type := U
  haveI : RiemannSurface P :=
    riemannSurface_openSubset U ⟨q, hpq⟩
      (by simpa [U] using punctured_riemannSurface_preconnected X p)
  rcases riemannSurface_compactExhaustion P with ⟨Kp⟩
  let Fp : ℕ → P → ℝ := fun k z ↦ -((B (φ k)).toFun z.1)
  have hextract :
      ∀ (θ : ℕ → ℕ), StrictMono θ → ∀ m : ℕ,
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∃ f : P → ℝ,
            TendstoUniformlyOn
              (fun n : ℕ ↦ Fp (θ (ψ n))) f Filter.atTop (Kp m) := by
    intro θ hθ m
    let KX : Set X := Subtype.val '' (Kp m)
    have hKp_compact : IsCompact (Kp m) := Kp.isCompact m
    have hKX_compact : IsCompact KX := by
      simpa [KX] using (Subtype.isCompact_iff.mp hKp_compact)
    have hKX_punctured : KX ⊆ {x : X | x ≠ p} := by
      rintro x ⟨z, _hz, rfl⟩
      exact z.2
    have hboundθ : ∀ k : ℕ, (B (φ (θ k))).boundaryHeightAt q < A :=
      fun k ↦ hbound (θ k)
    rcases
      neg_boundedNegativeGreen_subsequence_extracts_uniformLimit_on_compact_away_pole_of_boundaryHeight_bound
        (E := E) (p := p) (q := q) B (hφ.comp hθ) hpq hboundθ
        hKX_compact hKX_punctured with
      ⟨ψ, hψ, fX, hconvX⟩
    refine ⟨ψ, hψ, fun z : P ↦ fX z.1, ?_⟩
    have hconvP :
        TendstoUniformlyOn
          (fun n : ℕ ↦ (fun x : X ↦ -((B (φ (θ (ψ n)))).toFun x)) ∘
            (fun z : P ↦ (z : X)))
          (fX ∘ fun z : P ↦ (z : X)) Filter.atTop
          ((fun z : P ↦ (z : X)) ⁻¹' KX) :=
      hconvX.comp (fun z : P ↦ (z : X))
    refine (hconvP.mono ?_).congr ?_
    · intro z hz
      exact ⟨z, hz, rfl⟩
    · filter_upwards with n z hz
      rfl
  rcases
    realFunctions_subsequence_tendstoUniformlyOn_compactExhaustion_of_subsequence_extractions
      Kp (F := Fp) hextract with
    ⟨ψ, hψ, fP, hconvP⟩
  let f : X → ℝ := fun x ↦ if hx : x ≠ p then fP ⟨x, hx⟩ else 0
  refine ⟨ψ, hψ, f, ?_⟩
  intro K hK_compact hK_punctured
  let KP : Set P := {z : P | z.1 ∈ K}
  have hKP_compact : IsCompact KP := by
    rw [Subtype.isCompact_iff]
    have h_image : Subtype.val '' KP = K := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hxK
        exact ⟨⟨x, hK_punctured hxK⟩, hxK, rfl⟩
    simpa [h_image] using hK_compact
  rcases Kp.exists_superset_of_isCompact hKP_compact with ⟨m, hKPm⟩
  have hconvKP : TendstoUniformlyOn
      (fun n : ℕ ↦ Fp (ψ n)) fP Filter.atTop KP :=
    (hconvP m).mono hKPm
  intro U hU
  filter_upwards [hconvKP U hU] with n hn x hxK
  have hx_ne : x ≠ p := hK_punctured hxK
  have hzK : (⟨x, hx_ne⟩ : P) ∈ KP := hxK
  simpa [Fp, f, hx_ne] using hn ⟨x, hx_ne⟩ hzK

/--
%%handwave
name:
  Compact-local bounded Green limits are harmonic away from the pole
statement:
  If the positive bounded-domain Green functions in a subsequence converge
  uniformly on every compact subset away from the pole, then the limit is
  harmonic away from the pole.
proof:
  Around each point away from the pole, choose a relatively compact smooth
  coordinate neighborhood whose closure avoids the pole.  The exhaustion
  domains eventually contain this closure, so the subsequence is eventually
  harmonic on that neighborhood.  Compact-local uniform convergence then
  passes harmonicity to the limit locally, and local harmonicity patches over
  the punctured surface.
-/
theorem neg_boundedNegativeGreen_subsequence_limit_harmonic_away_pole_of_compact_convergence
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ -((B (φ k)).toFun x))
          f Filter.atTop K) :
    IsHarmonicOnSurface {x : X | x ≠ p} f := by
  classical
  let F : ℕ → X → ℝ := fun k x ↦ -((B (φ k)).toFun x)
  refine
    harmonicOnSurface_of_local_eventually_harmonic_forall_compact_tendstoUniformlyOn
      (l := Filter.atTop) (U := {x : X | x ≠ p}) (F := F) (f := f) ?_ ?_
  · intro x hx
    have hpunctured_open : IsOpen {y : X | y ≠ p} := by
      simpa using (isOpen_ne (x := p) : IsOpen {y : X | y ≠ p})
    rcases exists_smoothBoundaryDomain_between_compact_and_open
        (X := X) (K := ({x} : Set X)) (U := {y : X | y ≠ p})
        (isCompact_singleton (x := x)) ⟨x, rfl⟩ hpunctured_open
        (by intro y hy; simpa [Set.mem_singleton_iff.mp hy] using hx) with
      ⟨Ωx, hxΩx, hΩx_closure_punctured⟩
    refine ⟨Ωx.carrier, Ωx.isOpen, hxΩx (by simp), ?_, ?_⟩
    · intro y hy
      exact hΩx_closure_punctured (subset_closure hy)
    · simpa [F] using
        neg_boundedNegativeGreen_subsequence_eventually_harmonic_on_relativelyCompact_punctured_region
          (E := E) (p := p) B hφ Ωx.compact_closure hΩx_closure_punctured
  · intro K hKU hK
    exact hconv K hK hKU

/--
%%handwave
name:
  Compact-local bounded Green limits are nonnegative away from the pole
statement:
  If the positive bounded-domain Green functions in a subsequence converge
  uniformly on compact subsets away from the pole, then their limit is
  nonnegative away from the pole.
proof:
  At a fixed point away from the pole, the exhaustion domains eventually
  contain that point.  The bounded-domain Green potential is nonpositive
  there, so its negative is nonnegative.  Uniform convergence on the
  singleton passes this pointwise inequality to the limit.
-/
theorem neg_boundedNegativeGreen_subsequence_limit_nonnegative_away_pole_of_compact_convergence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ -((B (φ k)).toFun x))
          f Filter.atTop K) :
    ∀ x : X, x ≠ p → 0 ≤ f x := by
  intro x hx
  have hsingle_punctured : ({x} : Set X) ⊆ {y : X | y ≠ p} := by
    intro y hy
    simpa [Set.mem_singleton_iff.mp hy] using hx
  have hconv_single :
      TendstoUniformlyOn
        (fun k : ℕ ↦ fun y : X ↦ -((B (φ k)).toFun y))
        f Filter.atTop ({x} : Set X) :=
    hconv ({x} : Set X) (isCompact_singleton (x := x)) hsingle_punctured
  have hdomain :
      ∀ᶠ k : ℕ in Filter.atTop, x ∈ (E.domain (φ k)).carrier := by
    filter_upwards
      [hφ.tendsto_atTop.eventually
        (E.eventually_compact_subset_domain (isCompact_singleton (x := x)))] with
      k hk
    exact hk (by simp)
  exact tendstoUniformlyOn_pointwise_ge_of_eventually_ge
    (K := ({x} : Set X))
    (F := fun k : ℕ ↦ fun y : X ↦ -((B (φ k)).toFun y))
    (f := f) (x := x) (a := 0) (by simp) hconv_single
    (by
      filter_upwards [hdomain] with k hk
      exact neg_nonneg.mpr ((B (φ k)).nonpositive_on_domain x hk))

/--
%%handwave
name:
  Logarithmic bounded Green limits blow up at the pole
statement:
  If a bounded Green subsequence limit has the logarithmic-pole asymptotic at
  the pole, then it tends to \(+\infty\) along the punctured surface.
proof:
  The removable harmonic remainder is finite and continuous at the pole,
  while the coordinate logarithm tends to \(-\infty\).  Thus the positive
  Green potential, obtained by subtracting that logarithm, tends to
  \(+\infty\).
-/
theorem neg_boundedNegativeGreen_subsequence_limit_tends_to_infinity_at_pole_of_logarithmic_singularity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X} {f : X → ℝ}
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ h : X → ℝ,
          IsHarmonicOnSurface χ.chart.source h ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              f x + Real.log ‖χ.chart x - χ.chart p‖ = h x) :
    Filter.Tendsto f (𝓝[≠] p) Filter.atTop :=
  logarithmic_singularity_tendsto_atTop X p hlog

/--
%%handwave
name:
  Compact-local bounded Green limits are positive away from the pole
statement:
  If a compact-local limit of positive bounded-domain Green functions has the
  logarithmic pole asymptotic, then it is strictly positive away from the
  pole.
proof:
  Compact-local convergence passes nonnegativity and harmonicity to the
  punctured limit.  The logarithmic pole asymptotic gives blow-up at the pole.
  The strong minimum principle on the punctured surface upgrades
  nonnegativity to strict positivity.
-/
theorem neg_boundedNegativeGreen_subsequence_limit_positive_away_pole_of_compact_convergence_and_logarithmic_singularity
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ -((B (φ k)).toFun x))
          f Filter.atTop K)
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ h : X → ℝ,
          IsHarmonicOnSurface χ.chart.source h ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              f x + Real.log ‖χ.chart x - χ.chart p‖ = h x) :
    ∀ x : X, x ≠ p → 0 < f x := by
  have hnonneg :
      ∀ x : X, x ≠ p → 0 ≤ f x :=
    neg_boundedNegativeGreen_subsequence_limit_nonnegative_away_pole_of_compact_convergence
      (E := E) (p := p) B hφ hconv
  have hharm :
      IsHarmonicOnSurface {x : X | x ≠ p} f :=
    neg_boundedNegativeGreen_subsequence_limit_harmonic_away_pole_of_compact_convergence
      (E := E) (p := p) B hφ hconv
  have hblow : Filter.Tendsto f (𝓝[≠] p) Filter.atTop :=
    logarithmic_singularity_tendsto_atTop X p hlog
  exact
    nonnegative_on_punctured_harmonicOn_punctured_tendsto_atTop_positive
      X p hnonneg hharm hblow

/--
%%handwave
name:
  Compact-local bounded Green limits have compact positive superlevels
statement:
  If a compact-local limit of positive bounded-domain Green functions tends
  to zero along the ends, then its positive superlevel sets are compact after
  adjoining the pole.
proof:
  Compact-local convergence gives harmonicity on the punctured surface, hence
  punctured continuity.  Vanishing at infinity traps every positive
  superlevel in a compact set up to the adjoined pole.
-/
theorem neg_boundedNegativeGreen_subsequence_limit_compact_positive_superlevel_of_compact_convergence_and_zero_at_infinity
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ -((B (φ k)).toFun x))
          f Filter.atTop K)
    (hzero : Filter.Tendsto f (Filter.cocompact X) (𝓝 0)) :
    ∀ a : ℝ, 0 < a → IsCompact ({p} ∪ {x : X | a ≤ f x}) := by
  intro a ha
  exact
    SmoothRelativelyCompactExhaustion.compact_adjoined_superlevel_of_tendsto_zero_cocompact_of_harmonicOn_punctured
      (a := a) ha hzero
      (neg_boundedNegativeGreen_subsequence_limit_harmonic_away_pole_of_compact_convergence
        (E := E) (p := p) B hφ hconv)

/--
%%handwave
name:
  Compact-local centered Green limits are harmonic away from the pole
statement:
  If centered bounded-domain Green potentials converge uniformly on every
  compact subset away from the pole, then the limit is harmonic away from the
  pole.
proof:
  Around each point away from the pole, choose a relatively compact smooth
  neighborhood avoiding the pole.  The exhaustion eventually contains its
  closure, so the centered potentials are eventually harmonic there.  The
  compact-local harmonic-limit theorem then gives local harmonicity, which
  patches over the punctured surface.
-/
theorem centered_boundedNegativeGreen_subsequence_limit_harmonic_away_pole_of_compact_convergence
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ (B (φ k)).centeredAt q)
          f Filter.atTop K) :
    IsHarmonicOnSurface {x : X | x ≠ p} f := by
  classical
  let F : ℕ → X → ℝ := fun k x ↦ (B (φ k)).centeredAt q x
  refine
    harmonicOnSurface_of_local_eventually_harmonic_forall_compact_tendstoUniformlyOn
      (l := Filter.atTop) (U := {x : X | x ≠ p}) (F := F) (f := f) ?_ ?_
  · intro x hx
    have hpunctured_open : IsOpen {y : X | y ≠ p} := by
      simpa using (isOpen_ne (x := p) : IsOpen {y : X | y ≠ p})
    rcases exists_smoothBoundaryDomain_between_compact_and_open
        (X := X) (K := ({x} : Set X)) (U := {y : X | y ≠ p})
        (isCompact_singleton (x := x)) ⟨x, rfl⟩ hpunctured_open
        (by intro y hy; simpa [Set.mem_singleton_iff.mp hy] using hx) with
      ⟨Ωx, hxΩx, hΩx_closure_punctured⟩
    refine ⟨Ωx.carrier, Ωx.isOpen, hxΩx (by simp), ?_, ?_⟩
    · intro y hy
      exact hΩx_closure_punctured (subset_closure hy)
    · simpa [F] using
        centered_boundedNegativeGreen_eventually_harmonic_on_relativelyCompact_punctured_region_comp_strictMono
          (E := E) (p := p) (q := q) B hφ Ωx.compact_closure
          hΩx_closure_punctured
  · intro K hKU hK
    exact hconv K hK hKU

/--
%%handwave
name:
  Compact-local centered Green limits vanish at the base point
statement:
  If centered bounded-domain Green potentials converge uniformly on compact
  subsets away from the pole, then the limit has value \(0\) at the
  normalization point.
proof:
  Each centered potential is exactly zero at the base point.  Uniform
  convergence on the singleton \(\{q\}\) passes that equality to the limit.
-/
theorem centered_boundedNegativeGreen_subsequence_limit_eq_zero_at_base_of_compact_convergence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ}
    (hpq : q ≠ p)
    {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ (B (φ k)).centeredAt q)
          f Filter.atTop K) :
    f q = 0 := by
  have hsingle_punctured : ({q} : Set X) ⊆ {x : X | x ≠ p} := by
    intro y hy
    simpa [Set.mem_singleton_iff.mp hy] using hpq
  have hconv_single :
      TendstoUniformlyOn
        (fun k : ℕ ↦ (B (φ k)).centeredAt q)
        f Filter.atTop ({q} : Set X) :=
    hconv ({q} : Set X) (isCompact_singleton (x := q)) hsingle_punctured
  have htendsto :
      Filter.Tendsto
        (fun k : ℕ ↦ (B (φ k)).centeredAt q q)
        Filter.atTop (𝓝 (f q)) :=
    hconv_single.tendsto_at (by simp)
  have hzero :
      Filter.Tendsto (fun _k : ℕ ↦ (0 : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds
  exact (tendsto_nhds_unique
    (by simpa [BoundedNegativeGreenPotential.centeredAt_base] using hzero)
    htendsto).symm

/--
%%handwave
name:
  Logarithmic centered Green limits tend to negative infinity at the pole
statement:
  If a centered Green exhaustion limit has the logarithmic-zero asymptotic at
  the pole, then it tends to \(-\infty\) along the punctured surface.
proof:
  The removable harmonic remainder is finite and continuous at the pole,
  while the coordinate logarithm tends to \(-\infty\).  Thus the centered
  potential has the same \(-\infty\) limit.
-/
theorem centered_boundedNegativeGreen_subsequence_limit_tends_to_neg_infinity_at_pole_of_logarithmic_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X} {f : X → ℝ}
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ h : X → ℝ,
          IsHarmonicOnSurface χ.chart.source h ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              f x - Real.log ‖χ.chart x - χ.chart p‖ = h x) :
    Filter.Tendsto f (𝓝[≠] p) Filter.atBot :=
  logarithmic_zero_tendsto_atBot X p hlog

/--
%%handwave
name:
  Bounded logarithmic-zero remainders are removable
statement:
  If a harmonic function on a punctured surface has locally bounded
  remainders after subtracting the coordinate logarithm, then those
  remainders extend harmonically across the puncture in every coordinate.
proof:
  In a pointed coordinate, the coordinate logarithm is harmonic away from the
  puncture.  Hence the corrected remainder is punctured-harmonic.  The
  bounded removable-singularity theorem then extends the corrected remainder
  harmonically across the puncture.
-/
theorem logarithmic_zero_of_harmonicOn_punctured_and_bounded_remainder
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X} {f : X → ℝ}
    (hharm : IsHarmonicOnSurface {x : X | x ≠ p} f)
    (hbound :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ M : ℝ,
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            ‖f x - Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M) :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ h : X → ℝ,
        IsHarmonicOnSurface χ.chart.source h ∧
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            f x - Real.log ‖χ.chart x - χ.chart p‖ = h x := by
  intro χ
  let g : X → ℝ := fun x ↦ f x - Real.log ‖χ.chart x - χ.chart p‖
  have hf_harm :
      IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p}) f :=
    harmonicOnSurface_mono (fun x hx ↦ hx.2) hharm
  have hlog_harm :
      IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p})
        (fun x : X ↦ Real.log ‖χ.chart x - χ.chart p‖) := by
    exact coordinateLogDistance_harmonicOnSurface χ.chart χ.chart_mem_atlas
      (fun x hx ↦ hx.1)
      (fun x hx hEq ↦ hx.2 (χ.chart.injOn hx.1 χ.base_mem_source hEq))
  have hg_harm :
      IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p}) g := by
    simpa [g] using harmonicOnSurface_sub hf_harm hlog_harm
  rcases hbound χ with ⟨M, hM⟩
  rcases bounded_harmonicOn_punctured_pointed_coordinate_removable
      X χ g hg_harm ⟨M, by simpa [g] using hM⟩ with
    ⟨h, hh, heq⟩
  exact ⟨h, hh, by simpa [g] using heq⟩

/--
%%handwave
name:
  Local bounded punctured harmonic functions are removable inside an open set
statement:
  Let a function be harmonic on the punctured part of an open coordinate
  neighborhood inside a larger open set containing the puncture.  If it is
  bounded near the puncture, then it agrees near the puncture with a harmonic
  function on a smaller full neighborhood contained in the larger open set.
proof:
  Choose a coordinate ball about the puncture whose closed ball remains
  inside the coordinate image of the open set.  Transport the punctured
  function to this planar punctured ball, apply the classical bounded
  removable-singularity theorem, and pull the planar harmonic extension back
  to the surface.
-/
theorem bounded_harmonicOn_open_punctured_pointed_coordinate_has_local_removable_extension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X} {U : Set X}
    (hU_open : IsOpen U) (hpU : p ∈ U)
    (χ : PointedSurfaceCoordinate X p) (g : X → ℝ)
    (hharm :
      IsHarmonicOnSurface
        ((U ∩ χ.chart.source) ∩ {x : X | x ≠ p}) g)
    (hbound :
      ∃ M : ℝ,
        ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
          ‖g x‖ ≤ M) :
    ∃ N : Set X, ∃ h : X → ℝ,
      IsOpen N ∧ p ∈ N ∧ N ⊆ U ∧ N ⊆ χ.chart.source ∧
        IsHarmonicOnSurface N h ∧
          ∀ᶠ x in 𝓝[N ∩ {x : X | x ≠ p}] p,
            g x = h x := by
  let c : ℂ := χ.chart p
  have hc_target : c ∈ χ.chart.target :=
    χ.chart.map_source χ.base_mem_source
  have htarget_nhds : χ.chart.target ∈ 𝓝 c :=
    χ.chart.open_target.mem_nhds hc_target
  have hU_nhds : U ∈ 𝓝 p := hU_open.mem_nhds hpU
  have hU_map : U ∈ Filter.map χ.chart.symm (𝓝 c) :=
    χ.chart.continuousAt_symm hc_target
      (by simpa [c, χ.chart.left_inv χ.base_mem_source] using hU_nhds)
  have hU_pre : χ.chart.symm ⁻¹' U ∈ 𝓝 c := by
    simpa [Filter.mem_map] using hU_map
  rcases Metric.mem_nhds_iff.mp
      (Filter.inter_mem htarget_nhds hU_pre) with
    ⟨R₀, hR₀_pos, hball_targetU⟩
  let r : ℝ := R₀ / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hrR₀ : r < R₀ := by
    dsimp [r]
    linarith
  have hclosed_r :
      Metric.closedBall c r ⊆ χ.chart.target ∩ χ.chart.symm ⁻¹' U :=
    (Metric.closedBall_subset_ball hrR₀).trans hball_targetU
  let f : ℂ → ℝ := fun z ↦ g (χ.chart.symm z)
  have hharm_planar :
      InnerProductSpace.HarmonicOnNhd f (Metric.ball c r \ {c}) := by
    have hsurface := hharm χ.chart χ.chart_mem_atlas
    refine hsurface.mono ?_
    intro z hz
    have hzball : z ∈ Metric.ball c r := hz.1
    have hz_closed : z ∈ Metric.closedBall c r :=
      Metric.ball_subset_closedBall hzball
    have hz_target : z ∈ χ.chart.target := (hclosed_r hz_closed).1
    have hzU : χ.chart.symm z ∈ U := (hclosed_r hz_closed).2
    have hsymm_source : χ.chart.symm z ∈ χ.chart.source :=
      χ.chart.map_target hz_target
    have hsymm_ne : χ.chart.symm z ≠ p := by
      intro hsymm_eq
      have hz_eq_c : z = c := by
        calc
          z = χ.chart (χ.chart.symm z) := (χ.chart.right_inv hz_target).symm
          _ = χ.chart p := by rw [hsymm_eq]
          _ = c := rfl
      exact hz.2 (by simpa [Set.mem_singleton_iff] using hz_eq_c)
    exact ⟨hz_target, ⟨⟨hzU, hsymm_source⟩, hsymm_ne⟩⟩
  have hbound_planar :
      ∃ M : ℝ,
        ∀ᶠ z in 𝓝[Metric.ball c r \ {c}] c, ‖f z‖ ≤ M := by
    rcases hbound with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    let E : Set X :=
      {x : X | x ∈ χ.chart.source ∩ {x : X | x ≠ p} → ‖g x‖ ≤ M}
    have hE_nhds : E ∈ 𝓝 p := by
      simpa [E] using eventually_nhdsWithin_iff.mp hM
    have hpre_map :
        E ∈ Filter.map χ.chart.symm (𝓝 c) :=
      χ.chart.continuousAt_symm hc_target
        (by simpa [c, χ.chart.left_inv χ.base_mem_source] using hE_nhds)
    have hpre : χ.chart.symm ⁻¹' E ∈ 𝓝 c := by
      simpa [Filter.mem_map] using hpre_map
    filter_upwards [mem_nhdsWithin_of_mem_nhds hpre, self_mem_nhdsWithin] with
      z hzE hzpunct
    have hz_target : z ∈ χ.chart.target :=
      (hclosed_r (Metric.ball_subset_closedBall hzpunct.1)).1
    have hsymm_source : χ.chart.symm z ∈ χ.chart.source :=
      χ.chart.map_target hz_target
    have hsymm_ne : χ.chart.symm z ≠ p := by
      intro hsymm_eq
      have hz_eq_c : z = c := by
        calc
          z = χ.chart (χ.chart.symm z) := (χ.chart.right_inv hz_target).symm
          _ = χ.chart p := by rw [hsymm_eq]
          _ = c := rfl
      exact hzpunct.2 (by simpa [Set.mem_singleton_iff] using hz_eq_c)
    exact hzE ⟨hsymm_source, hsymm_ne⟩
  rcases bounded_harmonicOn_punctured_complex_ball_has_removable_extension
      hr hharm_planar hbound_planar with
    ⟨δ, F, hδ_pos, hδr, hF_harm, hF_eq⟩
  let N : Set X := χ.chart.source ∩ χ.chart ⁻¹' Metric.ball c δ
  let h : X → ℝ := fun x ↦ F (χ.chart x)
  refine ⟨N, h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact χ.chart.isOpen_inter_preimage Metric.isOpen_ball
  · exact ⟨χ.base_mem_source, by simp [Metric.mem_ball, c, hδ_pos]⟩
  · intro x hx
    have hx_closed : χ.chart x ∈ Metric.closedBall c r := by
      rw [Metric.mem_closedBall]
      have hx_ball : dist (χ.chart x) c < δ := by
        simpa [Metric.mem_ball] using hx.2
      exact le_trans (le_of_lt hx_ball) hδr
    have hsymmU : χ.chart.symm (χ.chart x) ∈ U :=
      (hclosed_r hx_closed).2
    simpa [χ.chart.left_inv hx.1] using hsymmU
  · intro x hx
    exact hx.1
  · intro e he z hz
    have hz_target : z ∈ e.target := hz.1
    have hxN : e.symm z ∈ N := hz.2
    have hxχ_source : e.symm z ∈ χ.chart.source := hxN.1
    have hF_at :
        InnerProductSpace.HarmonicAt F (χ.chart (e.symm z)) :=
      hF_harm (χ.chart (e.symm z)) hxN.2
    have htransition :
        AnalyticAt ℂ (fun w : ℂ ↦ χ.chart (e.symm w)) z :=
      chartTransition_analyticAt e he χ.chart χ.chart_mem_atlas
        hz_target hxχ_source
    simpa [h, Function.comp_def] using
      harmonicAt_comp_analyticAt hF_at htransition
  · let E : Set ℂ :=
      {z : ℂ | z ∈ Metric.ball c r \ {c} → f z = F z}
    have hE_nhds : E ∈ 𝓝 c := by
      simpa [E] using eventually_nhdsWithin_iff.mp hF_eq
    have hpre : χ.chart ⁻¹' E ∈ 𝓝 p :=
      χ.chart.continuousAt χ.base_mem_source hE_nhds
    filter_upwards
      [mem_nhdsWithin_of_mem_nhds hpre, self_mem_nhdsWithin]
      with x hxE hxpunct
    have hxN : x ∈ N := hxpunct.1
    have hxsource : x ∈ χ.chart.source := hxN.1
    have hxchart_ball_r : χ.chart x ∈ Metric.ball c r := by
      rw [Metric.mem_ball]
      have hx_ball : dist (χ.chart x) c < δ := by
        simpa [Metric.mem_ball] using hxN.2
      exact lt_of_lt_of_le hx_ball hδr
    have hxchart_ne : χ.chart x ≠ c := by
      intro hxchart
      exact hxpunct.2 (χ.chart.injOn hxsource χ.base_mem_source (by
        simpa [c] using hxchart))
    have hxchart_punct : χ.chart x ∈ Metric.ball c r \ {c} :=
      ⟨hxchart_ball_r, by simpa [Set.mem_singleton_iff] using hxchart_ne⟩
    have heq := hxE hxchart_punct
    simpa [f, h, χ.chart.left_inv hxsource] using heq

/--
%%handwave
name:
  Local bounded logarithmic-zero remainders are removable
statement:
  Let a real-valued function be harmonic on a punctured open neighborhood of
  a point.  If in every coordinate at that point the difference between the
  function and the coordinate logarithm is bounded near the puncture, then
  the logarithmic zero is removable in every coordinate.
proof:
  Since the open set contains the pole, every coordinate source has a smaller
  punctured coordinate neighborhood lying in the open set.  On that smaller
  neighborhood the corrected remainder is harmonic and bounded, so the local
  removable-singularity theorem gives a harmonic extension across the pole.
  This gives the logarithmic-zero identity on a full neighborhood of the pole
  contained in the open set.
-/
theorem logarithmic_zero_of_harmonicOn_open_punctured_and_bounded_remainder
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X} {U : Set X} {f : X → ℝ}
    (hU_open : IsOpen U) (hpU : p ∈ U)
    (hharm : IsHarmonicOnSurface (U \ {p}) f)
    (hbound :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ M : ℝ,
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            ‖f x - Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M) :
    HasLogarithmicZeroWithin X U p f := by
  intro χ
  let g : X → ℝ := fun x ↦ f x - Real.log ‖χ.chart x - χ.chart p‖
  have hf_harm :
      IsHarmonicOnSurface
        ((U ∩ χ.chart.source) ∩ {x : X | x ≠ p}) f := by
    refine harmonicOnSurface_mono ?_ hharm
    intro x hx
    exact ⟨hx.1.1, by simpa [Set.mem_singleton_iff] using hx.2⟩
  have hlog_harm_full :
      IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p})
        (fun x : X ↦ Real.log ‖χ.chart x - χ.chart p‖) := by
    exact coordinateLogDistance_harmonicOnSurface χ.chart χ.chart_mem_atlas
      (fun x hx ↦ hx.1)
      (fun x hx hEq ↦ hx.2 (χ.chart.injOn hx.1 χ.base_mem_source hEq))
  have hlog_harm :
      IsHarmonicOnSurface
        ((U ∩ χ.chart.source) ∩ {x : X | x ≠ p})
        (fun x : X ↦ Real.log ‖χ.chart x - χ.chart p‖) :=
    harmonicOnSurface_mono
      (show ((U ∩ χ.chart.source) ∩ {x : X | x ≠ p}) ⊆
          χ.chart.source ∩ {x : X | x ≠ p} from by
        intro x hx
        exact ⟨hx.1.2, hx.2⟩) hlog_harm_full
  have hg_harm :
      IsHarmonicOnSurface
        ((U ∩ χ.chart.source) ∩ {x : X | x ≠ p}) g := by
    simpa [g] using harmonicOnSurface_sub hf_harm hlog_harm
  rcases hbound χ with ⟨M, hM⟩
  rcases
    bounded_harmonicOn_open_punctured_pointed_coordinate_has_local_removable_extension
      hU_open hpU χ g hg_harm ⟨M, by simpa [g] using hM⟩ with
    ⟨N, h, hN_open, hpN, hNU, hN_source, hharmN, heq⟩
  refine ⟨N, h, hN_open, hpN, hNU, hN_source, hharmN, ?_⟩
  filter_upwards [heq] with x hx
  simpa [g] using hx

/--
%%handwave
name:
  Local logarithmic zeros imply pole decay inside the open set
statement:
  If a function has a logarithmic zero at a point within an open set
  containing that point, then it tends to \(-\infty\) as the point is
  approached through the punctured open set.
proof:
  In a smaller coordinate neighborhood inside the open set, the function is
  the coordinate logarithm plus a harmonic remainder.  The harmonic remainder
  is continuous at the pole, while the coordinate logarithm tends to
  \(-\infty\).  Since the smaller neighborhood and the open set determine the
  same punctured neighborhood filter at the pole, this gives the desired
  limit.
-/
theorem logarithmic_zero_within_tendsto_atBot
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X} {U : Set X} {f : X → ℝ}
    (hU_open : IsOpen U) (hpU : p ∈ U)
    (hlog : HasLogarithmicZeroWithin X U p f) :
    Filter.Tendsto f (𝓝[U \ {p}] p) Filter.atBot := by
  let χ : PointedSurfaceCoordinate X p :=
    { chart := chartAt ℂ p
      chart_mem_atlas := chart_mem_atlas ℂ p
      base_mem_source := mem_chart_source ℂ p }
  rcases hlog χ with
    ⟨N, h, hN_open, hpN, _hNU, hN_source, hharm, hevent⟩
  let F : Filter X := 𝓝[N ∩ {x : X | x ≠ p}] p
  have hF_eq : F = 𝓝[≠] p := by
    have hN_mem : N ∈ 𝓝[{x : X | x ≠ p}] p :=
      mem_nhdsWithin_of_mem_nhds (hN_open.mem_nhds hpN)
    simpa [F] using nhdsWithin_inter_of_mem hN_mem
  have hU_filter_eq : 𝓝[U \ {p}] p = 𝓝[≠] p := by
    have hU_mem : U ∈ 𝓝[{x : X | x ≠ p}] p :=
      mem_nhdsWithin_of_mem_nhds (hU_open.mem_nhds hpU)
    have hU_inter :
        𝓝[U ∩ {x : X | x ≠ p}] p = 𝓝[≠] p := by
      simpa using nhdsWithin_inter_of_mem hU_mem
    have hdiff : U \ {p} = U ∩ {x : X | x ≠ p} := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1, by simpa [Set.mem_singleton_iff] using hx.2⟩
      · intro hx
        exact ⟨hx.1, by simpa [Set.mem_singleton_iff] using hx.2⟩
    rw [hdiff]
    exact hU_inter
  have hh_cont :
      Filter.Tendsto h F (𝓝 (h p)) := by
    have hcont_on : ContinuousOn h N :=
      harmonicOnSurface_continuousOn hN_open hharm
    have hwithin :
        Filter.Tendsto h (𝓝[N] p) (𝓝 (h p)) :=
      hcont_on.continuousWithinAt hpN
    exact hwithin.mono_left (by
      simpa [F] using
        (nhdsWithin_mono p (Set.inter_subset_left :
          N ∩ {x : X | x ≠ p} ⊆ N)))
  have hlog_bot :
      Filter.Tendsto
        (fun x : X => Real.log ‖χ.chart x - χ.chart p‖)
        F Filter.atBot := by
    have hsubset :
        N ∩ {x : X | x ≠ p} ⊆
          χ.chart.source ∩ {x : X | x ≠ p} := by
      intro x hx
      exact ⟨hN_source hx.1, hx.2⟩
    exact (pointedCoordinate_log_norm_tendsto_atBot X χ).mono_left
      (by simpa [F] using nhdsWithin_mono p hsubset)
  have hsum_bot :
      Filter.Tendsto
        (fun x : X => h x + Real.log ‖χ.chart x - χ.chart p‖)
        F Filter.atBot :=
    hh_cont.add_atBot hlog_bot
  have hf_event :
      (fun x : X => h x + Real.log ‖χ.chart x - χ.chart p‖) =ᶠ[F] f := by
    filter_upwards [by simpa [F] using hevent] with x hx
    linarith
  have hf_punctured : Filter.Tendsto f (𝓝[≠] p) Filter.atBot := by
    simpa [hF_eq] using Filter.Tendsto.congr' hf_event hsum_bot
  simpa [hU_filter_eq] using hf_punctured

/--
%%handwave
name:
  Bounded logarithmic-pole remainders are removable
statement:
  If a harmonic function on a punctured surface has locally bounded
  remainders after adding the coordinate logarithm, then those remainders
  extend harmonically across the puncture in every coordinate.
proof:
  The coordinate logarithm is harmonic away from the puncture, so adding it to
  the punctured harmonic function gives a bounded punctured-harmonic
  remainder.  The bounded removable-singularity theorem extends it across the
  puncture.
-/
theorem logarithmic_singularity_of_harmonicOn_punctured_and_bounded_remainder
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X} {f : X → ℝ}
    (hharm : IsHarmonicOnSurface {x : X | x ≠ p} f)
    (hbound :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ M : ℝ,
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            ‖f x + Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M) :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ h : X → ℝ,
        IsHarmonicOnSurface χ.chart.source h ∧
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            f x + Real.log ‖χ.chart x - χ.chart p‖ = h x := by
  intro χ
  let g : X → ℝ := fun x ↦ f x + Real.log ‖χ.chart x - χ.chart p‖
  have hf_harm :
      IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p}) f :=
    harmonicOnSurface_mono (fun x hx ↦ hx.2) hharm
  have hlog_harm :
      IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p})
        (fun x : X ↦ Real.log ‖χ.chart x - χ.chart p‖) := by
    exact coordinateLogDistance_harmonicOnSurface χ.chart χ.chart_mem_atlas
      (fun x hx ↦ hx.1)
      (fun x hx hEq ↦ hx.2 (χ.chart.injOn hx.1 χ.base_mem_source hEq))
  have hg_harm :
      IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p}) g := by
    simpa [g] using harmonicOnSurface_add hf_harm hlog_harm
  rcases hbound χ with ⟨M, hM⟩
  rcases bounded_harmonicOn_punctured_pointed_coordinate_removable
      X χ g hg_harm ⟨M, by simpa [g] using hM⟩ with
    ⟨h, hh, heq⟩
  exact ⟨h, hh, by simpa [g] using heq⟩

/--
%%handwave
name:
  Compact-local centered Green limits have compact adjoined sublevels
statement:
  If a compact-local limit of centered bounded-domain Green potentials tends
  to \(+\infty\) along the ends, then all of its sublevel sets are compact
  after adjoining the logarithmic zero.
proof:
  Compact-local convergence of the centered potentials gives harmonicity on
  the punctured surface.  Harmonicity gives punctured continuity, and the
  end-growth traps sublevel sets in compact subsets up to the adjoined pole.
-/
theorem centered_boundedNegativeGreen_subsequence_limit_compact_sublevel_with_zero_of_compact_convergence
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ (B (φ k)).centeredAt q)
          f Filter.atTop K)
    (hinfty : Filter.Tendsto f (Filter.cocompact X) Filter.atTop) :
    ∀ a : ℝ, IsCompact ({p} ∪ {x : X | f x ≤ a}) := by
  intro a
  exact
    SmoothRelativelyCompactExhaustion.compact_adjoined_sublevel_of_tendsto_atTop_cocompact_of_harmonicOn_punctured
      (a := a) hinfty
      (centered_boundedNegativeGreen_subsequence_limit_harmonic_away_pole_of_compact_convergence
        (E := E) (p := p) (q := q) B hφ hconv)

/--
%%handwave
name:
  Annular Green approximants exist
statement:
  For every closed coordinate disk whose deletion leaves a nonempty annulus
  inside a smooth boundary domain, the logarithmic annular Perron problem has
  a harmonic solution.
proof:
  Apply the annular Perron theorem.  The componentwise maximum-principle
  geometry for the annulus is supplied by the general componentwise-geometry
  theorem for open relatively compact proper regions.
-/
theorem smoothBoundaryDomain_has_annularPerronGreenApproximants
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) :
    ∀ (D : ClosedCoordinateDisk X)
      (hD_subset : D.carrier ⊆ Ω.carrier)
      (hnonempty : (Ω.carrier \ D.carrier).Nonempty),
      ∃ u : X → ℝ,
        SolvesHarmonicDirichletProblem
          (annularPerronDomain Ω D hD_subset hnonempty)
          (annularLogBoundaryData Ω D hD_subset hnonempty) u := by
  intro D hD_subset hnonempty
  exact annularPerron_dirichlet_solution Ω D hD_subset hnonempty

/--
%%handwave
name:
  Arbitrarily small annuli around an interior pole
statement:
  Let \(p\) be an interior point of a smooth boundary domain.  Every open
  neighborhood of \(p\) contains a closed coordinate disk containing \(p\),
  lying in the smooth domain, and whose deletion leaves a nonempty annular
  region.
proof:
  Intersect the prescribed neighborhood with the smooth domain.  This open
  set contains a second point distinct from \(p\).  Choose a tiny closed
  coordinate disk around \(p\) inside the intersection and avoiding that
  second point; the avoided point witnesses that the annulus is nonempty.
-/
theorem smoothBoundaryDomain_exists_arbitrarilySmall_annularCoordinateDisk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) {p : X} (hp : p ∈ Ω.carrier) :
    ∀ ⦃N : Set X⦄, IsOpen N → p ∈ N →
      ∃ D : ClosedCoordinateDisk X,
        p ∈ D.carrier ∧
          D.closedRadius ≤ 1 ∧
            D.carrier ⊆ Ω.carrier ∧
              D.carrier ⊆ N ∧
                (Ω.carrier \ D.carrier).Nonempty := by
  intro N hN_open hpN
  have hΩN_open : IsOpen (Ω.carrier ∩ N) := Ω.isOpen.inter hN_open
  have hpΩN : p ∈ Ω.carrier ∩ N := ⟨hp, hpN⟩
  rcases exists_ne_mem_open_of_mem hΩN_open hpΩN with
    ⟨q, hqΩN, hq_ne_p⟩
  rcases exists_closedCoordinateDisk_mem_subset_open_avoids_point
      hΩN_open hpΩN hq_ne_p with
    ⟨D, hpD, hD_radius, hD_subset, hq_notD⟩
  refine ⟨D, hpD, hD_radius, ?_, ?_, ?_⟩
  · exact fun x hxD ↦ (hD_subset hxD).1
  · exact fun x hxD ↦ (hD_subset hxD).2
  · exact ⟨q, hqΩN.1, hq_notD⟩

/--
%%handwave
name:
  Annular Perron approximation system
statement:
  An annular Perron approximation system consists of closed coordinate disks
  of radius at most one, shrinking to a pole inside a smooth boundary domain,
  together with solutions of the logarithmic Dirichlet problem on the
  corresponding annuli.
-/
structure AnnularPerronApproximationSystem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (Ω : SmoothBoundaryDomain X) (p : X) where
  /-- Closed coordinate disks deleted from the smooth domain. -/
  disk : ℕ → ClosedCoordinateDisk X
  /-- Each deleted disk contains the pole. -/
  pole_mem_disk : ∀ n : ℕ, p ∈ (disk n).carrier
  /-- Each deleted disk has closed radius at most one. -/
  closedRadius_le_one : ∀ n : ℕ, (disk n).closedRadius ≤ 1
  /-- Each deleted disk is contained in the smooth domain. -/
  disk_subset_domain : ∀ n : ℕ, (disk n).carrier ⊆ Ω.carrier
  /-- Deleting each disk leaves a nonempty annular region. -/
  annulus_nonempty : ∀ n : ℕ, (Ω.carrier \ (disk n).carrier).Nonempty
  /-- The annular Perron solutions. -/
  approximant : ℕ → X → ℝ
  /-- Each approximant solves the logarithmic annular Dirichlet problem. -/
  solves_annular_problem :
    ∀ n : ℕ,
      SolvesHarmonicDirichletProblem
        (annularPerronDomain Ω (disk n)
          (disk_subset_domain n) (annulus_nonempty n))
        (annularLogBoundaryData Ω (disk n)
          (disk_subset_domain n) (annulus_nonempty n))
        (approximant n)
  /-- The deleted disks shrink to the pole. -/
  disks_shrink_to_pole :
    ∀ ⦃N : Set X⦄, IsOpen N → p ∈ N →
      ∀ᶠ n : ℕ in Filter.atTop, (disk n).carrier ⊆ N

namespace AnnularPerronApproximationSystem

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {Ω : SmoothBoundaryDomain X} {p : X}

/--
%%handwave
name:
  Logarithmically normalized annular deletions
statement:
  A zero-radius annular approximation system is logarithmically normalized if,
  in every coordinate at the pole, the prescribed logarithmic height of the
  moving inner boundary differs from the coordinate logarithm on that boundary
  by a uniformly bounded amount.
proof:
  This is the normalization condition needed to identify the limiting pole
  asymptotic.  It rules out rescaling the moving disk coordinates in a way
  that keeps the carriers shrinking but changes the logarithmic boundary
  height by an unbounded additive constant.
-/
def HasLogarithmicBoundaryNormalization
    (S : AnnularPerronApproximationSystem X Ω p) : Prop :=
  ∀ χ : PointedSurfaceCoordinate X p,
    ∃ C : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x ∈ (S.disk n).boundaryCircle,
          x ∈ χ.chart.source ∧ x ≠ p ∧
            ‖Real.log (S.disk n).closedRadius -
              Real.log ‖χ.chart x - χ.chart p‖‖ ≤ C

/--
%%handwave
name:
  Annular approximants vanish on the outer boundary
statement:
  In an annular Perron approximation system, every approximating harmonic
  function is zero on the original boundary of the smooth domain.
proof:
  This is the outer-boundary value in the logarithmic annular Dirichlet
  problem solved by each approximant.
-/
theorem approximant_eq_zero_on_outer_boundary
    (S : AnnularPerronApproximationSystem X Ω p) (n : ℕ)
    {x : X} (hx : x ∈ Ω.boundary) :
    S.approximant n x = 0 := by
  exact annularPerron_solution_eq_zero_on_outer_boundary
    Ω (S.disk n) (S.disk_subset_domain n) (S.annulus_nonempty n)
    (S.solves_annular_problem n) hx

/--
%%handwave
name:
  Annular approximants take the inner logarithmic value
statement:
  On a point of the annular boundary lying on the deleted coordinate circle,
  an annular Perron approximant has value equal to the logarithm of the
  deleted radius.
proof:
  Apply the inner-boundary trace theorem for the logarithmic annular
  Dirichlet problem solved by the approximant.
-/
theorem approximant_eq_log_on_inner_boundary
    (S : AnnularPerronApproximationSystem X Ω p) (n : ℕ)
    {x : X}
    (hx_boundary :
      x ∈
        (annularPerronDomain Ω (S.disk n)
          (S.disk_subset_domain n) (S.annulus_nonempty n)).boundary)
    (hx_inner : x ∈ (S.disk n).boundaryCircle) :
    S.approximant n x = Real.log (S.disk n).closedRadius := by
  exact annularPerron_solution_eq_log_on_inner_boundary
    Ω (S.disk n) (S.disk_subset_domain n) (S.annulus_nonempty n)
    (S.solves_annular_problem n) hx_boundary hx_inner

/--
%%handwave
name:
  Normalized annular approximants have bounded inner logarithmic remainder
statement:
  For a logarithmically normalized annular approximation system, in every
  coordinate at the pole the difference between the approximant and the
  coordinate logarithm is uniformly bounded on the moving inner boundary,
  whenever that point is part of the annular boundary.
proof:
  The approximant has the logarithmic deleted-radius value on the inner
  boundary, and the logarithmic normalization says that this radius logarithm
  differs by a bounded amount from the chosen coordinate logarithm there.
-/
theorem approximant_logarithmic_remainder_bound_on_inner_boundary
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    (χ : PointedSurfaceCoordinate X p) :
    ∃ C : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x : X,
          x ∈
            (annularPerronDomain Ω (S.disk n)
              (S.disk_subset_domain n) (S.annulus_nonempty n)).boundary →
          x ∈ (S.disk n).boundaryCircle →
          x ∈ χ.chart.source ∧ x ≠ p ∧
            ‖S.approximant n x -
              Real.log ‖χ.chart x - χ.chart p‖‖ ≤ C := by
  rcases hnormalized χ with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n hn x hx_boundary hx_inner
  rcases hn x hx_inner with ⟨hx_source, hx_ne, hbound⟩
  have happrox :
      S.approximant n x = Real.log (S.disk n).closedRadius :=
    S.approximant_eq_log_on_inner_boundary n hx_boundary hx_inner
  refine ⟨hx_source, hx_ne, ?_⟩
  simpa [happrox] using hbound

/--
%%handwave
name:
  Normalized shrinking deleted disks eventually contain the pole in their
  interior
statement:
  In a logarithmically normalized annular approximation system, the deleted
  coordinate disks eventually contain the pole as an interior point.
proof:
  The normalization says that every point on the moving boundary circle is
  distinct from the pole, for all sufficiently large indices.  Since each
  deleted disk contains the pole, the pole is then a non-boundary point of the
  closed coordinate disk and hence lies in its interior.
-/
theorem disk_eventually_pole_mem_interior_of_logarithmicBoundaryNormalization
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    (χ : PointedSurfaceCoordinate X p) :
    ∀ᶠ n : ℕ in Filter.atTop, p ∈ interior (S.disk n).carrier := by
  rcases hnormalized χ with ⟨C, hC⟩
  filter_upwards [hC] with n hn
  have hp_not_boundary : p ∉ (S.disk n).boundaryCircle := by
    intro hp_boundary
    exact (hn p hp_boundary).2.1 rfl
  exact
    (S.disk n).mem_interior_carrier_of_mem_carrier_of_not_mem_boundaryCircle
      (S.pole_mem_disk n) hp_not_boundary

/--
%%handwave
name:
  Fixed coordinate ball cut by a moving annulus has componentwise geometry
statement:
  Intersecting a fixed coordinate ball around the pole with one of the
  annular Perron domains gives an open relatively compact proper region, and
  hence has the componentwise maximum-principle geometry.
proof:
  The coordinate ball is open and has compact surface closure because its
  closed Euclidean ball lies in the chart target.  Intersecting with the
  annular domain preserves openness and compact closure.  The region is
  proper because the deleted disk contains the pole, so the pole is not in
  the annular domain.
-/
theorem coordinateBall_inter_annularDomain_hasComponentwiseMaximumPrincipleGeometry
    (S : AnnularPerronApproximationSystem X Ω p)
    (χ : PointedSurfaceCoordinate X p) {R : ℝ}
    (hclosed_target : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target)
    (n : ℕ) :
    HasComponentwiseMaximumPrincipleGeometry
      ((χ.chart.source ∩ χ.chart ⁻¹' Metric.ball (χ.chart p) R) ∩
        (annularPerronDomain Ω (S.disk n)
          (S.disk_subset_domain n) (S.annulus_nonempty n)).carrier) := by
  let U₀ : Set X :=
    χ.chart.source ∩ χ.chart ⁻¹' Metric.ball (χ.chart p) R
  let A : PerronDomain X :=
    annularPerronDomain Ω (S.disk n)
      (S.disk_subset_domain n) (S.annulus_nonempty n)
  let U : Set X := U₀ ∩ A.carrier
  change HasComponentwiseMaximumPrincipleGeometry U
  have hU₀_open : IsOpen U₀ := by
    dsimp [U₀]
    exact χ.chart.isOpen_inter_preimage Metric.isOpen_ball
  have hU_open : IsOpen U := by
    dsimp [U]
    exact hU₀_open.inter A.isOpen
  have hU_compact : IsCompact (closure U) := by
    have hU₀_compact : IsCompact (closure U₀) := by
      dsimp [U₀]
      exact
        openPartialHomeomorph_coordinateBall_compact_closure
          χ.chart hclosed_target
    exact hU₀_compact.of_isClosed_subset isClosed_closure
      (closure_mono (by
        intro x hx
        exact hx.1))
  have hU_ne_univ : U ≠ Set.univ := by
    intro hU_univ
    have hpU : p ∈ U := by
      rw [hU_univ]
      exact Set.mem_univ p
    have hp_annular : p ∈ A.carrier := hpU.2
    have hp_annular' : p ∈ Ω.carrier \ (S.disk n).carrier := by
      simpa [A, annularPerronDomain_carrier] using hp_annular
    exact hp_annular'.2 (S.pole_mem_disk n)
  exact
    hasComponentwiseMaximumPrincipleGeometry_of_open_compactClosure_ne_univ
      hU_open hU_compact hU_ne_univ

/--
%%handwave
name:
  Frontier of a fixed coordinate ball cut by a moving annulus
statement:
  A frontier point of the intersection of a fixed coordinate ball with a
  moving annular Perron domain is either on the fixed coordinate circle or on
  the boundary of the moving annular domain.
proof:
  The frontier of an intersection lies in the union of the two frontiers.  On
  the coordinate-ball side, compact containment of the closed Euclidean ball
  in the chart target shows that a coordinate-ball frontier point remains in
  the chart source and maps to the Euclidean circle.
-/
theorem frontier_coordinateBall_inter_annularDomain_subset_circle_or_annularBoundary
    (S : AnnularPerronApproximationSystem X Ω p)
    (χ : PointedSurfaceCoordinate X p) {R : ℝ}
    (hR_pos : 0 < R)
    (hclosed_target : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target)
    (n : ℕ) :
    frontier
        ((χ.chart.source ∩ χ.chart ⁻¹' Metric.ball (χ.chart p) R) ∩
          (annularPerronDomain Ω (S.disk n)
            (S.disk_subset_domain n) (S.annulus_nonempty n)).carrier) ⊆
      {x : X | x ∈ χ.chart.source ∧
        χ.chart x ∈ frontier (Metric.ball (χ.chart p) R)} ∪
        (annularPerronDomain Ω (S.disk n)
          (S.disk_subset_domain n) (S.annulus_nonempty n)).boundary := by
  let U₀ : Set X :=
    χ.chart.source ∩ χ.chart ⁻¹' Metric.ball (χ.chart p) R
  let A : PerronDomain X :=
    annularPerronDomain Ω (S.disk n)
      (S.disk_subset_domain n) (S.annulus_nonempty n)
  let K : Set X :=
    χ.chart.source ∩ χ.chart ⁻¹' Metric.closedBall (χ.chart p) R
  have hU₀_open : IsOpen U₀ := by
    dsimp [U₀]
    exact χ.chart.isOpen_inter_preimage Metric.isOpen_ball
  have hK_compact : IsCompact K := by
    dsimp [K]
    change IsCompact
      (χ.chart.source ∩ χ.chart ⁻¹'
        Metric.closedBall (χ.chart p) R)
    rw [← χ.chart.symm_image_eq_source_inter_preimage hclosed_target]
    exact (isCompact_closedBall (χ.chart p) R).image_of_continuousOn
      (χ.chart.continuousOn_symm.mono hclosed_target)
  have hU₀_subset_K : U₀ ⊆ K := by
    intro x hx
    exact ⟨hx.1, Metric.ball_subset_closedBall hx.2⟩
  have hclosure_U₀_subset_K : closure U₀ ⊆ K :=
    closure_minimal hU₀_subset_K hK_compact.isClosed
  intro x hx
  have hx_frontier_inter :
      x ∈ frontier (U₀ ∩ A.carrier) := by
    simpa [U₀, A] using hx
  rcases frontier_inter_subset U₀ A.carrier hx_frontier_inter with
    hxU₀ | hxA
  · have hx_closure_U₀ : x ∈ closure U₀ :=
      frontier_subset_closure hxU₀.1
    have hxK : x ∈ K := hclosure_U₀_subset_K hx_closure_U₀
    have hx_not_U₀ : x ∉ U₀ := by
      intro hx_mem
      have hx_empty : x ∈ U₀ ∩ frontier U₀ := ⟨hx_mem, hxU₀.1⟩
      simp [hU₀_open.inter_frontier_eq] at hx_empty
    have hx_not_ball :
        χ.chart x ∉ Metric.ball (χ.chart p) R := by
      intro hx_ball
      exact hx_not_U₀ ⟨hxK.1, hx_ball⟩
    have hdist_le :
        dist (χ.chart x) (χ.chart p) ≤ R := by
      simpa [Metric.mem_closedBall] using hxK.2
    have hnot_lt :
        ¬ dist (χ.chart x) (χ.chart p) < R := by
      intro hlt
      apply hx_not_ball
      simpa [Metric.mem_ball] using hlt
    have hdist_eq :
        dist (χ.chart x) (χ.chart p) = R :=
      le_antisymm hdist_le (le_of_not_gt hnot_lt)
    have hx_circle :
        χ.chart x ∈ frontier (Metric.ball (χ.chart p) R) := by
      rw [frontier_ball (χ.chart p) hR_pos.ne']
      simpa [Metric.mem_sphere, dist_eq_norm] using hdist_eq
    exact Or.inl ⟨hxK.1, hx_circle⟩
  · have hx_boundary : x ∈ A.boundary := by
      simpa [PerronDomain.boundary] using hxA.2
    exact Or.inr (by simpa [A] using hx_boundary)

/--
%%handwave
name:
  Boundary control for annular logarithmic remainders on a fixed coordinate
  ball
statement:
  Suppose the logarithmically corrected annular approximants are bounded on a
  fixed coordinate circle around the pole, and the closed coordinate ball lies
  inside the smooth domain.  Then the same corrected quantities are uniformly
  bounded on the frontier of the coordinate ball cut by each sufficiently
  late annular domain.
proof:
  The frontier split says that a boundary point of the cut region is either
  on the fixed coordinate circle or on the annular boundary.  The fixed-circle
  case is the assumed bound.  On the annular boundary, the outer boundary of
  the smooth domain cannot occur because the closed coordinate ball lies in
  the smooth domain; the remaining inner-boundary case is controlled by the
  logarithmic normalization and the inner Dirichlet trace.
-/
theorem approximant_logarithmic_remainder_bound_on_coordinateBall_annular_frontier
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    (χ : PointedSurfaceCoordinate X p) {R M₀ : ℝ}
    (hR_pos : 0 < R)
    (hclosed_target : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target)
    (hclosed_domain :
      Metric.closedBall (χ.chart p) R ⊆ χ.chart.symm ⁻¹' Ω.carrier)
    (hfront :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ z ∈ frontier (Metric.ball (χ.chart p) R),
          ‖S.approximant n (χ.chart.symm z) -
            Real.log ‖z - χ.chart p‖‖ ≤ M₀) :
    ∃ M : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x : X,
          x ∈
            frontier
              ((χ.chart.source ∩ χ.chart ⁻¹' Metric.ball (χ.chart p) R) ∩
                (annularPerronDomain Ω (S.disk n)
                  (S.disk_subset_domain n) (S.annulus_nonempty n)).carrier) →
          ‖S.approximant n x -
            Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M := by
  rcases
      S.approximant_logarithmic_remainder_bound_on_inner_boundary
        hnormalized χ with
    ⟨C, hinner_event⟩
  refine ⟨max M₀ C, ?_⟩
  filter_upwards [hfront, hinner_event] with n hfront_n hinner_n x hx_frontier
  let U₀ : Set X :=
    χ.chart.source ∩ χ.chart ⁻¹' Metric.ball (χ.chart p) R
  let A : PerronDomain X :=
    annularPerronDomain Ω (S.disk n)
      (S.disk_subset_domain n) (S.annulus_nonempty n)
  have hsplit :=
    S.frontier_coordinateBall_inter_annularDomain_subset_circle_or_annularBoundary
      χ hR_pos hclosed_target n hx_frontier
  rcases hsplit with hx_circle | hx_annular_boundary
  · rcases hx_circle with ⟨hx_source, hx_circle⟩
    have hsymm : χ.chart.symm (χ.chart x) = x :=
      χ.chart.left_inv hx_source
    have hbound :
        ‖S.approximant n x -
          Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M₀ := by
      simpa [hsymm] using hfront_n (χ.chart x) hx_circle
    exact hbound.trans (le_max_left M₀ C)
  · have hx_closure_region :
        x ∈ closure (U₀ ∩ A.carrier) :=
      frontier_subset_closure (by simpa [U₀, A] using hx_frontier)
    have hx_closure_ball : x ∈ closure U₀ :=
      closure_mono (by intro y hy; exact hy.1) hx_closure_region
    have hx_closed_ball :
        x ∈ χ.chart.source ∩
          χ.chart ⁻¹' Metric.closedBall (χ.chart p) R := by
      simpa [U₀] using
        openPartialHomeomorph_coordinateBall_closure_subset_source_inter_closedBall
          χ.chart hclosed_target hx_closure_ball
    have hx_boundary_A : x ∈ A.boundary := by
      simpa [A] using hx_annular_boundary
    rcases
        annularPerronDomain_boundary_subset_outer_or_inner
          Ω (S.disk n) (S.disk_subset_domain n) (S.annulus_nonempty n)
          hx_boundary_A with
      hx_outer | hx_inner
    · have hxΩ : x ∈ Ω.carrier := by
        have hxΩ_symm :
            χ.chart.symm (χ.chart x) ∈ Ω.carrier :=
          hclosed_domain hx_closed_ball.2
        simpa [χ.chart.left_inv hx_closed_ball.1] using hxΩ_symm
      have hx_frontierΩ : x ∈ frontier Ω.carrier := by
        simpa [SmoothBoundaryDomain.boundary] using hx_outer
      have hx_empty : x ∈ Ω.carrier ∩ frontier Ω.carrier :=
        ⟨hxΩ, hx_frontierΩ⟩
      simp [Ω.isOpen.inter_frontier_eq] at hx_empty
    · have hbound_inner :=
        hinner_n x (by simpa [A] using hx_boundary_A) hx_inner
      exact hbound_inner.2.2.trans (le_max_right M₀ C)

/--
%%handwave
name:
  Annular approximants are nonpositive
statement:
  In an annular Perron approximation system, every approximating harmonic
  function is nonpositive throughout its annular domain.
proof:
  The deleted coordinate disks have radius at most one, so the logarithmic
  inner boundary value is nonpositive; the maximum principle propagates this
  upper bound through the annulus.
-/
theorem approximant_nonpositive
    (S : AnnularPerronApproximationSystem X Ω p) (n : ℕ) :
    ∀ x ∈
      (annularPerronDomain Ω (S.disk n)
        (S.disk_subset_domain n) (S.annulus_nonempty n)).carrier,
        S.approximant n x ≤ 0 := by
  exact annularPerron_solution_nonpositive_of_closedRadius_le_one
    Ω (S.disk n) (S.disk_subset_domain n) (S.annulus_nonempty n)
    (S.closedRadius_le_one n) (S.solves_annular_problem n)

/--
%%handwave
name:
  Annular approximants have the logarithmic lower bound
statement:
  In an annular Perron approximation system, every approximating harmonic
  function is bounded below on its annular domain by the smaller of zero and
  the logarithm of the deleted disk radius.
proof:
  This is the lower maximum-principle estimate for the logarithmic annular
  Dirichlet problem solved by each approximant.
-/
theorem boundary_min_le_approximant
    (S : AnnularPerronApproximationSystem X Ω p) (n : ℕ) :
    ∀ x ∈
      (annularPerronDomain Ω (S.disk n)
        (S.disk_subset_domain n) (S.annulus_nonempty n)).carrier,
        min (Real.log (S.disk n).closedRadius) 0 ≤ S.approximant n x := by
  exact boundary_min_le_annularPerron_solution
    Ω (S.disk n) (S.disk_subset_domain n) (S.annulus_nonempty n)
    (S.solves_annular_problem n)

/--
%%handwave
name:
  Shrinking annular disks eventually avoid a fixed point away from the pole
statement:
  If \(q\ne p\), then the deleted coordinate disks in an annular Perron
  approximation system eventually avoid \(q\).
proof:
  Apply the shrinking condition to the open set \(X\setminus\{q\}\), which is
  a neighborhood of the pole.
-/
theorem disk_eventually_avoids_point
    (S : AnnularPerronApproximationSystem X Ω p)
    {q : X} (hq : q ≠ p) :
    ∀ᶠ n : ℕ in Filter.atTop, q ∉ (S.disk n).carrier := by
  have hp_ne_q : p ≠ q := by exact hq.symm
  have hN_open : IsOpen ({x : X | x ≠ q}) := by
    simpa using (isOpen_ne (x := q) : IsOpen {x : X | x ≠ q})
  have hpN : p ∈ {x : X | x ≠ q} := hp_ne_q
  filter_upwards [S.disks_shrink_to_pole hN_open hpN] with n hn hqD
  exact (hn hqD) rfl

/--
%%handwave
name:
  Points away from the pole eventually lie in the annular domains
statement:
  If \(q\) lies in the smooth domain and \(q\ne p\), then \(q\) eventually
  belongs to the annuli obtained by deleting the shrinking coordinate disks.
proof:
  The deleted disks eventually avoid \(q\), while \(q\) remains in the fixed
  outer smooth domain.
-/
theorem eventually_mem_annularPerronDomain_of_mem_domain_ne_p
    (S : AnnularPerronApproximationSystem X Ω p)
    {q : X} (hqΩ : q ∈ Ω.carrier) (hq : q ≠ p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      q ∈
        (annularPerronDomain Ω (S.disk n)
          (S.disk_subset_domain n) (S.annulus_nonempty n)).carrier := by
  filter_upwards [S.disk_eventually_avoids_point hq] with n hq_not_disk
  rw [annularPerronDomain_carrier]
  exact ⟨hqΩ, hq_not_disk⟩

/--
%%handwave
name:
  Annular approximants are eventually nonpositive at fixed interior points
statement:
  At every point of the smooth domain distinct from the pole, the annular
  approximants are eventually nonpositive.
proof:
  Such a point eventually lies in the annular domains, where the maximum
  principle gives nonpositivity of the approximants.
-/
theorem approximant_eventually_nonpositive_at_of_mem_domain_ne_p
    (S : AnnularPerronApproximationSystem X Ω p)
    {q : X} (hqΩ : q ∈ Ω.carrier) (hq : q ≠ p) :
    ∀ᶠ n : ℕ in Filter.atTop, S.approximant n q ≤ 0 := by
  filter_upwards
    [S.eventually_mem_annularPerronDomain_of_mem_domain_ne_p hqΩ hq] with
    n hn
  exact S.approximant_nonpositive n q hn

/--
%%handwave
name:
  Annular approximants are eventually harmonic on compact punctured regions
statement:
  Let \(U\) be a surface region whose closure is compact, contained in the
  smooth domain, and avoids the pole.  In an annular Perron approximation
  system, all sufficiently late approximants are harmonic on \(U\).
proof:
  Since the closure of \(U\) avoids the pole, the complement of that closure
  is an open neighborhood of the pole.  The deleted coordinate disks
  eventually lie in this neighborhood, so \(U\) is eventually contained in
  the corresponding annulus, where the approximant is harmonic.
-/
theorem approximant_eventually_harmonic_on_relativelyCompact_punctured_region
    (S : AnnularPerronApproximationSystem X Ω p)
    {U : Set X}
    (_hU_compact_closure : IsCompact (closure U))
    (hU_subset_domain : closure U ⊆ Ω.carrier)
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p}) :
    ∀ᶠ n : ℕ in Filter.atTop,
      IsHarmonicOnSurface U (S.approximant n) := by
  have hp_not_closure : p ∉ closure U := by
    intro hp_closure
    exact (hU_punctured_closure hp_closure) rfl
  have hdisks :
      ∀ᶠ n : ℕ in Filter.atTop, (S.disk n).carrier ⊆ (closure U)ᶜ :=
    S.disks_shrink_to_pole isClosed_closure.isOpen_compl hp_not_closure
  filter_upwards [hdisks] with n hn
  refine harmonicOnSurface_mono
    (U := U)
    (V := (annularPerronDomain Ω (S.disk n)
      (S.disk_subset_domain n) (S.annulus_nonempty n)).carrier)
    ?_ (S.solves_annular_problem n).1
  intro x hxU
  rw [annularPerronDomain_carrier]
  refine ⟨hU_subset_domain (subset_closure hxU), ?_⟩
  intro hx_disk
  exact hn hx_disk (subset_closure hxU)

/--
%%handwave
name:
  Annular approximants are eventually harmonic on boundary caps away from the
  pole
statement:
  Let \(U\) be a relatively compact region contained in the smooth domain,
  whose closure avoids the pole.  The closure is allowed to meet the outer
  boundary.  Then all sufficiently late annular approximants are harmonic on
  \(U\).
proof:
  The deleted coordinate disks eventually lie outside \(\overline U\).  Since
  \(U\) itself lies in the smooth domain, \(U\) is then contained in each
  corresponding annulus, so harmonicity restricts from the annular Dirichlet
  solution.
-/
theorem approximant_eventually_harmonic_on_relativelyCompact_punctured_subset_domain
    (S : AnnularPerronApproximationSystem X Ω p)
    {U : Set X}
    (_hU_compact_closure : IsCompact (closure U))
    (hU_subset_domain : U ⊆ Ω.carrier)
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p}) :
    ∀ᶠ n : ℕ in Filter.atTop,
      IsHarmonicOnSurface U (S.approximant n) := by
  have hp_not_closure : p ∉ closure U := by
    intro hp_closure
    exact (hU_punctured_closure hp_closure) rfl
  have hdisks :
      ∀ᶠ n : ℕ in Filter.atTop, (S.disk n).carrier ⊆ (closure U)ᶜ :=
    S.disks_shrink_to_pole isClosed_closure.isOpen_compl hp_not_closure
  filter_upwards [hdisks] with n hn
  refine harmonicOnSurface_mono
    (U := U)
    (V := (annularPerronDomain Ω (S.disk n)
      (S.disk_subset_domain n) (S.annulus_nonempty n)).carrier)
    ?_ (S.solves_annular_problem n).1
  intro x hxU
  rw [annularPerronDomain_carrier]
  refine ⟨hU_subset_domain hxU, ?_⟩
  intro hx_disk
  exact hn hx_disk (subset_closure hxU)

omit [ChartedSpace ℂ X] [RiemannSurface X] in
/--
%%handwave
name:
  Closed sets avoided by a closure may be removed before taking closure
statement:
  If the closure of a set \(U\) lies in the closure of \(\Omega\) and avoids a
  closed set \(D\), then the closure of \(U\) lies in the closure of
  \(\Omega\setminus D\).
proof:
  At a point of \(\overline U\), every neighborhood meets \(\Omega\).  Since
  the point is outside the closed set \(D\), the complement of \(D\) is also a
  neighborhood, so every neighborhood already meets \(\Omega\setminus D\).
-/
theorem closure_subset_closure_sdiff_of_closure_subset_closure_of_avoids_closed
    {U V D : Set X}
    (hU_closure_subset : closure U ⊆ closure V)
    (hD_closed : IsClosed D)
    (hU_avoids_D : closure U ⊆ Dᶜ) :
    closure U ⊆ closure (V \ D) := by
  intro x hxU
  rw [mem_closure_iff_nhds]
  intro N hN
  have hxV : x ∈ closure V := hU_closure_subset hxU
  rw [mem_closure_iff_nhds] at hxV
  have hxDcompl : Dᶜ ∈ 𝓝 x :=
    hD_closed.isOpen_compl.mem_nhds (hU_avoids_D hxU)
  rcases hxV (N ∩ Dᶜ) (Filter.inter_mem hN hxDcompl) with
    ⟨y, hyND, hyV⟩
  exact ⟨y, hyND.1, hyV, hyND.2⟩

/--
%%handwave
name:
  Annular approximants are eventually continuous on closed punctured collars
statement:
  Let \(U\) be a region whose closure is compact, lies in the closed smooth
  domain, and avoids the pole.  In an annular Perron approximation system,
  all sufficiently late approximants are continuous on \(\overline U\).
proof:
  The deleted coordinate disks eventually lie outside \(\overline U\).  Hence
  \(\overline U\) lies in the closure of the corresponding annular domain.
  Continuity follows by restricting the closed-domain continuity part of the
  annular Dirichlet solution.
-/
theorem approximant_eventually_continuousOn_closure_of_relativelyCompact_punctured_region
    (S : AnnularPerronApproximationSystem X Ω p)
    {U : Set X}
    (_hU_compact_closure : IsCompact (closure U))
    (hU_subset_closed_domain : closure U ⊆ closure Ω.carrier)
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p}) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ContinuousOn (S.approximant n) (closure U) := by
  have hp_not_closure : p ∉ closure U := by
    intro hp_closure
    exact (hU_punctured_closure hp_closure) rfl
  have hdisks :
      ∀ᶠ n : ℕ in Filter.atTop, (S.disk n).carrier ⊆ (closure U)ᶜ :=
    S.disks_shrink_to_pole isClosed_closure.isOpen_compl hp_not_closure
  filter_upwards [hdisks] with n hn
  have hclosure_subset :
      closure U ⊆
        closure
          ((annularPerronDomain Ω (S.disk n)
            (S.disk_subset_domain n) (S.annulus_nonempty n)).carrier) := by
    have havoid : closure U ⊆ (S.disk n).carrierᶜ := by
      intro x hxU hxD
      exact hn hxD hxU
    have hsubset :=
      closure_subset_closure_sdiff_of_closure_subset_closure_of_avoids_closed
        (X := X) (U := U) (V := Ω.carrier) (D := (S.disk n).carrier)
        hU_subset_closed_domain (ClosedCoordinateDisk.isClosed (S.disk n))
        havoid
    simpa [annularPerronDomain_carrier] using hsubset
  exact (S.solves_annular_problem n).2.1.mono hclosure_subset

/--
%%handwave
name:
  Annular approximants are eventually nonpositive on compact punctured regions
statement:
  Let \(U\) be a surface region whose closure is compact, contained in the
  smooth domain, and avoids the pole.  In an annular Perron approximation
  system, all sufficiently late approximants are nonpositive on \(U\).
proof:
  The deleted coordinate disks eventually lie outside the closure of \(U\),
  so \(U\) is eventually contained in the corresponding annulus.  The maximum
  principle gives nonpositivity of each annular approximant on its annulus.
-/
theorem approximant_eventually_nonpositive_on_relativelyCompact_punctured_region
    (S : AnnularPerronApproximationSystem X Ω p)
    {U : Set X}
    (_hU_compact_closure : IsCompact (closure U))
    (hU_subset_domain : closure U ⊆ Ω.carrier)
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p}) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ x ∈ U, S.approximant n x ≤ 0 := by
  have hp_not_closure : p ∉ closure U := by
    intro hp_closure
    exact (hU_punctured_closure hp_closure) rfl
  have hdisks :
      ∀ᶠ n : ℕ in Filter.atTop, (S.disk n).carrier ⊆ (closure U)ᶜ :=
    S.disks_shrink_to_pole isClosed_closure.isOpen_compl hp_not_closure
  filter_upwards [hdisks] with n hn x hxU
  apply S.approximant_nonpositive n x
  rw [annularPerronDomain_carrier]
  refine ⟨hU_subset_domain (subset_closure hxU), ?_⟩
  intro hx_disk
  exact hn hx_disk (subset_closure hxU)

/--
%%handwave
name:
  Negated annular approximants satisfy local Harnack control
statement:
  On a relatively compact region contained in the smooth domain and avoiding
  the pole, every point has a neighborhood on which all sufficiently late
  negated annular Perron approximants are controlled by their value at that
  point.
proof:
  The annular approximants are eventually harmonic and nonpositive on the
  region.  Their negatives are therefore eventually nonnegative harmonic
  functions, so the local Harnack inequality applies.
-/
theorem neg_approximant_eventual_local_harnack_control
    (S : AnnularPerronApproximationSystem X Ω p)
    {U : Set X} (hU_open : IsOpen U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_subset_domain : closure U ⊆ Ω.carrier)
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    {x : X} (hxU : x ∈ U) :
    ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ y ∈ N,
            -(S.approximant n y) ≤ C * (-(S.approximant n x)) := by
  rcases local_harnack_control_for_nonnegative_harmonic_function
      (X := X) hU_open hxU with
    ⟨N, hN_nhds, hN_subset, C, hC_pos, hcontrol⟩
  refine ⟨N, hN_nhds, hN_subset, C, hC_pos, ?_⟩
  filter_upwards
    [S.approximant_eventually_harmonic_on_relativelyCompact_punctured_region
      hU_compact_closure hU_subset_domain hU_punctured_closure,
     S.approximant_eventually_nonpositive_on_relativelyCompact_punctured_region
      hU_compact_closure hU_subset_domain hU_punctured_closure] with n hharm hnonpos y hyN
  exact hcontrol (harmonicOnSurface_neg hharm)
    (fun z hzU ↦ neg_nonneg.mpr (hnonpos z hzU)) y hyN

/--
%%handwave
name:
  Negated annular approximants satisfy pairwise local Harnack control
statement:
  On a relatively compact region contained in the smooth domain and avoiding
  the pole, every point has a neighborhood on which all sufficiently late
  negated annular Perron approximants at any two nearby points are comparable
  by a fixed constant.
proof:
  The annular approximants are eventually harmonic and nonpositive on the
  region.  Their negatives are therefore eventually nonnegative harmonic
  functions, so the pairwise local Harnack inequality applies.
-/
theorem neg_approximant_eventual_local_pair_harnack_control
    (S : AnnularPerronApproximationSystem X Ω p)
    {U : Set X} (hU_open : IsOpen U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_subset_domain : closure U ⊆ Ω.carrier)
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    {x : X} (hxU : x ∈ U) :
    ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ a ∈ N, ∀ b ∈ N,
            -(S.approximant n a) ≤ C * (-(S.approximant n b)) := by
  rcases local_harnack_pair_control_for_nonnegative_harmonic_function
      (X := X) hU_open hxU with
    ⟨N, hN_nhds, hN_subset, C, hC_pos, hcontrol⟩
  refine ⟨N, hN_nhds, hN_subset, C, hC_pos, ?_⟩
  filter_upwards
    [S.approximant_eventually_harmonic_on_relativelyCompact_punctured_region
      hU_compact_closure hU_subset_domain hU_punctured_closure,
     S.approximant_eventually_nonpositive_on_relativelyCompact_punctured_region
      hU_compact_closure hU_subset_domain hU_punctured_closure] with n hharm hnonpos a haN b hbN
  exact hcontrol (harmonicOnSurface_neg hharm)
    (fun z hzU ↦ neg_nonneg.mpr (hnonpos z hzU)) a haN b hbN

/--
%%handwave
name:
  A base bound gives pointwise annular bounds on preconnected regions
statement:
  If the negated annular approximants are eventually bounded above at one
  point of a preconnected relatively compact punctured region, then they are
  eventually bounded above at every point of that region.
proof:
  Pairwise local Harnack control propagates the base-point bound through the
  preconnected region.
-/
theorem neg_approximant_eventual_pointwise_bound_on_preconnected_region_of_base_bound
    (S : AnnularPerronApproximationSystem X Ω p)
    {q : X} {A : ℝ}
    (hbase : ∀ᶠ n : ℕ in Filter.atTop, -(S.approximant n q) ≤ A)
    {U : Set X} (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_subset_domain : closure U ⊆ Ω.carrier)
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hqU : q ∈ U) :
    ∀ x ∈ U,
      ∃ M : ℝ,
        ∀ᶠ n : ℕ in Filter.atTop, -(S.approximant n x) ≤ M := by
  refine eventual_upper_bound_propagates_of_local_pair_harnack_control
    (F := fun n x ↦ -(S.approximant n x))
    hU_preconnected ?_ hqU ⟨A, hbase⟩
  intro x hxU
  rcases S.neg_approximant_eventual_local_pair_harnack_control
      hU_open hU_compact_closure hU_subset_domain hU_punctured_closure hxU with
    ⟨N, hN_nhds, hN_subset, C, hC_pos, hcontrol⟩
  exact ⟨N, hN_nhds, hN_subset, C, hC_pos.le, hcontrol⟩

/--
%%handwave
name:
  A base bound gives compact annular bounds on preconnected regions
statement:
  If the negated annular approximants are eventually bounded above at one
  point of a preconnected relatively compact punctured region, then they have
  one eventual upper bound on every compact subset of that region.
proof:
  Pairwise local Harnack control propagates the base-point bound to local
  uniform bounds throughout the region, and compactness gives a finite
  subcover.
-/
theorem neg_approximant_eventual_uniform_bound_on_compact_of_base_bound
    (S : AnnularPerronApproximationSystem X Ω p)
    {q : X} {A : ℝ}
    (hbase : ∀ᶠ n : ℕ in Filter.atTop, -(S.approximant n q) ≤ A)
    {K U : Set X}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_subset_domain : closure U ⊆ Ω.carrier)
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hqU : q ∈ U) :
    ∃ M : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ y ∈ K, -(S.approximant n y) ≤ M := by
  refine eventual_uniform_upper_bound_on_compact_propagates_of_local_pair_harnack_control
    (F := fun n x ↦ -(S.approximant n x))
    hU_preconnected hK_compact hKU ?_ hqU ⟨A, hbase⟩
  intro x hxU
  rcases S.neg_approximant_eventual_local_pair_harnack_control
      hU_open hU_compact_closure hU_subset_domain hU_punctured_closure hxU with
    ⟨N, hN_nhds, hN_subset, C, hC_pos, hcontrol⟩
  exact ⟨N, hN_nhds, hN_subset, C, hC_pos.le, hcontrol⟩

/--
%%handwave
name:
  A base bound gives compact interval control for annular approximants
statement:
  Under a base-point bound, the annular approximants themselves eventually
  take values in one compact interval on every compact subset of a
  preconnected relatively compact punctured region.
proof:
  The base bound propagates to an upper bound for the negatives, giving a
  lower bound for the approximants.  Nonpositivity of the annular
  approximants supplies the upper endpoint \(0\).
-/
theorem approximant_eventual_mem_Icc_on_compact_of_base_bound
    (S : AnnularPerronApproximationSystem X Ω p)
    {q : X} {A : ℝ}
    (hbase : ∀ᶠ n : ℕ in Filter.atTop, -(S.approximant n q) ≤ A)
    {K U : Set X}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_subset_domain : closure U ⊆ Ω.carrier)
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hqU : q ∈ U) :
    ∃ M : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ y ∈ K, S.approximant n y ∈ Set.Icc (-M) 0 := by
  rcases S.neg_approximant_eventual_uniform_bound_on_compact_of_base_bound
      hbase hU_open hU_preconnected hK_compact hKU hU_compact_closure
      hU_subset_domain hU_punctured_closure hqU with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  filter_upwards
    [hM,
     S.approximant_eventually_nonpositive_on_relativelyCompact_punctured_region
      hU_compact_closure hU_subset_domain hU_punctured_closure] with
    n hupper hnonpos y hyK
  have hneg_upper : -(S.approximant n y) ≤ M := hupper y hyK
  have hnonpos_y : S.approximant n y ≤ 0 := hnonpos y (hKU hyK)
  constructor
  · linarith
  · exact hnonpos_y

/--
%%handwave
name:
  A base bound gives compact pointwise range for annular approximants
statement:
  Under a base-point bound, the annular approximants at each point of a
  compact subset of a preconnected relatively compact punctured region take
  values in a compact subset of the real line.
proof:
  Eventual membership in a fixed compact interval gives compact range after
  adjoining the finitely many initial values.
-/
theorem approximant_pointwise_compactRange_on_compact_of_base_bound
    (S : AnnularPerronApproximationSystem X Ω p)
    {q : X} {A : ℝ}
    (hbase : ∀ᶠ n : ℕ in Filter.atTop, -(S.approximant n q) ≤ A)
    {K U : Set X}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_subset_domain : closure U ⊆ Ω.carrier)
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hqU : q ∈ U) :
    ∀ y ∈ K,
      ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ n : ℕ, S.approximant n y ∈ Q := by
  rcases S.approximant_eventual_mem_Icc_on_compact_of_base_bound
      hbase hU_open hU_preconnected hK_compact hKU hU_compact_closure
      hU_subset_domain hU_punctured_closure hqU with
    ⟨M, hM⟩
  intro y hyK
  exact exists_compact_range_of_eventually_mem_Icc
    (a := fun n : ℕ ↦ S.approximant n y)
    (A := -M) (B := 0)
    (by
      filter_upwards [hM] with n hn
      exact hn y hyK)

/--
%%handwave
name:
  Base-bounded annular approximants are equicontinuous on compact regions
statement:
  If the negated annular Perron approximants are eventually bounded at one
  base point in a preconnected relatively compact punctured region, then a
  tail of the annular approximants is equicontinuous on every compact subset
  of that region.
proof:
  Pairwise Harnack control propagates the base-point bound to eventual local
  bounds for the negated approximants.  Since the approximants are eventually
  nonpositive, these are eventual absolute bounds for the approximants.
  Eventual harmonicity and bounded-harmonic equicontinuity then give the
  equicontinuous tail.
-/
theorem approximant_tail_equicontinuousOn_compact_of_base_bound
    (S : AnnularPerronApproximationSystem X Ω p)
    {q : X} {A : ℝ}
    (hbase : ∀ᶠ n : ℕ in Filter.atTop, -(S.approximant n q) ≤ A)
    {K U : Set X}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_subset_domain : closure U ⊆ Ω.carrier)
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hqU : q ∈ U) :
    ∃ N₀ : ℕ,
      EquicontinuousOn
        (fun n : ℕ ↦ fun x : X ↦ S.approximant (N₀ + n) x) K := by
  classical
  let F : ℕ → X → ℝ := fun n x ↦ S.approximant n x
  refine
    harmonicOnSurface_tail_equicontinuousOn_of_eventually_harmonic_locally_eventual_abs_bound
      (U := U) (K := K) (F := F) hK_compact
      (S.approximant_eventually_harmonic_on_relativelyCompact_punctured_region
        hU_compact_closure hU_subset_domain hU_punctured_closure)
      ?_
  have hloc :
      ∀ x ∈ U,
        ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
          ∃ M : ℝ,
            ∀ᶠ n : ℕ in Filter.atTop,
              ∀ y ∈ N, -(S.approximant n y) ≤ M := by
    refine eventual_locally_uniform_upper_bound_propagates_of_local_pair_harnack_control
      (F := fun n x ↦ -(S.approximant n x))
      hU_preconnected ?_ hqU ⟨A, hbase⟩
    intro x hxU
    rcases S.neg_approximant_eventual_local_pair_harnack_control
        hU_open hU_compact_closure hU_subset_domain hU_punctured_closure hxU with
      ⟨N, hN_nhds, hN_subset, C, hC_pos, hcontrol⟩
    exact ⟨N, hN_nhds, hN_subset, C, hC_pos.le, hcontrol⟩
  intro x hxK
  rcases hloc x (hKU hxK) with ⟨N, hN_nhds, hN_subset, M, hM⟩
  refine ⟨N, hN_nhds, hN_subset, max M 0, ?_⟩
  filter_upwards
    [hM,
     S.approximant_eventually_nonpositive_on_relativelyCompact_punctured_region
      hU_compact_closure hU_subset_domain hU_punctured_closure] with n hupper hnonpos y hyN
  have hnonpos_y : F n y ≤ 0 := hnonpos y (hN_subset hyN)
  have hupper_y : -F n y ≤ M := by simpa [F] using hupper y hyN
  calc
    |F n y| = -F n y := abs_of_nonpos hnonpos_y
    _ ≤ M := hupper_y
    _ ≤ max M 0 := le_max_left M 0

/--
%%handwave
name:
  A base bound gives annular compact uniform limits on compact regions
statement:
  Under a base-point bound, if the annular approximants are locally
  equicontinuous on a compact subset of a preconnected relatively compact
  punctured region, then a subsequence converges uniformly on that compact
  set.
proof:
  The base bound gives pointwise compact range on the compact set.  Eventual
  harmonicity gives continuity after discarding finitely many terms, and
  compact Arzelà-Ascoli extracts a uniformly convergent subsequence.
-/
theorem approximant_subsequence_extracts_uniformLimit_on_compact_of_base_bound
    (S : AnnularPerronApproximationSystem X Ω p)
    {q : X} {A : ℝ}
    (hbase : ∀ᶠ n : ℕ in Filter.atTop, -(S.approximant n q) ≤ A)
    {K U : Set X}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_subset_domain : closure U ⊆ Ω.carrier)
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hqU : q ∈ U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : X → ℝ,
        TendstoUniformlyOn
          (fun n : ℕ ↦ fun x : X ↦ S.approximant (φ n) x)
          f Filter.atTop K := by
  classical
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  let F : ℕ → X → ℝ := fun n x ↦ S.approximant n x
  rcases S.approximant_tail_equicontinuousOn_compact_of_base_bound
      hbase hU_open hU_preconnected hK_compact hKU hU_compact_closure
      hU_subset_domain hU_punctured_closure hqU with
    ⟨Neq, heq₀⟩
  rcases Filter.eventually_atTop.mp
      (S.approximant_eventually_harmonic_on_relativelyCompact_punctured_region
        hU_compact_closure hU_subset_domain hU_punctured_closure) with
    ⟨N, hN⟩
  let Ntail : ℕ := N + Neq
  have hcont : ∀ n : ℕ, ContinuousOn (F (Ntail + n)) K := by
    intro n
    have hN_le : N ≤ Ntail + n := by
      simpa [Ntail, Nat.add_assoc] using Nat.le_add_right N (Neq + n)
    have hharm : IsHarmonicOnSurface U (F (Ntail + n)) := by
      simpa [F] using hN (Ntail + n) hN_le
    exact (harmonicOnSurface_continuousOn hU_open hharm).mono hKU
  have hpointwise_tail :
      ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ n : ℕ, F (Ntail + n) x ∈ Q := by
    intro x hxK
    rcases
      S.approximant_pointwise_compactRange_on_compact_of_base_bound
        hbase hU_open hU_preconnected hK_compact hKU hU_compact_closure
        hU_subset_domain hU_punctured_closure hqU x hxK with
      ⟨Q, hQ_compact, hQ_mem⟩
    exact ⟨Q, hQ_compact, fun n ↦ by simpa [F] using hQ_mem (Ntail + n)⟩
  have heq : EquicontinuousOn (fun n : ℕ ↦ F (Ntail + n)) K := by
    intro x hxK V hV
    filter_upwards [heq₀ x hxK V hV] with y hy n
    simpa [F, Ntail, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      hy (N + n)
  rcases realFunctions_tail_subsequence_tendstoUniformlyOn_of_compact_equicontinuousOn
      hK_compact Ntail hcont hpointwise_tail heq with
    ⟨φ, hφ, f, hf⟩
  exact ⟨φ, hφ, f, by simpa [F] using hf⟩

/--
%%handwave
name:
  Annular Perron approximants have compact uniform limits on compact regions
statement:
  If annular Perron approximants are pointwise relatively compact and locally
  equicontinuous on a compact punctured region, then they have a subsequence
  that converges uniformly on that compact region.
proof:
  Away from the shrinking deleted disks, the approximants are eventually
  harmonic, hence continuous.  The compact-restriction Arzelà-Ascoli theorem
  applied to the eventual tail gives a uniformly convergent subsequence.
-/
theorem approximant_subsequence_extracts_uniformLimit_on_compact
    (S : AnnularPerronApproximationSystem X Ω p)
    {K U : Set X}
    (hU_open : IsOpen U)
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_subset_domain : closure U ⊆ Ω.carrier)
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    (hpointwise :
      ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ n : ℕ, S.approximant n x ∈ Q)
    (heq_tail :
      ∃ N₀ : ℕ,
        EquicontinuousOn
          (fun n : ℕ ↦ fun x : X ↦ S.approximant (N₀ + n) x) K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : X → ℝ,
        TendstoUniformlyOn
          (fun n : ℕ ↦ fun x : X ↦ S.approximant (φ n) x)
          f Filter.atTop K := by
  classical
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  let F : ℕ → X → ℝ := fun n x ↦ S.approximant n x
  rcases Filter.eventually_atTop.mp
      (S.approximant_eventually_harmonic_on_relativelyCompact_punctured_region
        hU_compact_closure hU_subset_domain hU_punctured_closure) with
    ⟨N, hN⟩
  rcases heq_tail with ⟨Neq, heq₀⟩
  let Ntail : ℕ := N + Neq
  have hcont : ∀ n : ℕ, ContinuousOn (F (Ntail + n)) K := by
    intro n
    have hharm : IsHarmonicOnSurface U (F (Ntail + n)) := by
      have hN_le : N ≤ Ntail + n := by
        simpa [Ntail, Nat.add_assoc] using Nat.le_add_right N (Neq + n)
      simpa [F] using hN (Ntail + n) hN_le
    exact (harmonicOnSurface_continuousOn hU_open hharm).mono hKU
  have hpointwise_tail :
      ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ n : ℕ, F (Ntail + n) x ∈ Q := by
    intro x hxK
    rcases hpointwise x hxK with ⟨Q, hQ_compact, hQ_mem⟩
    exact ⟨Q, hQ_compact, fun n ↦ by simpa [F] using hQ_mem (Ntail + n)⟩
  have heq : EquicontinuousOn (fun n : ℕ ↦ F (Ntail + n)) K := by
    intro x hxK V hV
    filter_upwards [heq₀ x hxK V hV] with y hy n
    have hidx : Neq + (N + n) = Ntail + n := by
      simp [Ntail, Nat.add_comm, Nat.add_left_comm]
    have h := hy (N + n)
    rw [hidx] at h
    simpa [F] using h
  rcases realFunctions_tail_subsequence_tendstoUniformlyOn_of_compact_equicontinuousOn
      hK_compact Ntail hcont hpointwise_tail heq with
    ⟨φ, hφ, f, hf⟩
  exact ⟨φ, hφ, f, by simpa [F] using hf⟩

/--
%%handwave
name:
  Annular Perron approximants have compact uniform limits away from the pole
statement:
  If annular Perron approximants are pointwise relatively compact and locally
  equicontinuous on a compact subset of the punctured smooth domain, then
  they have a subsequence that converges uniformly on that compact set.
proof:
  The compact set avoids the pole, so the deleted coordinate disks eventually
  lie in its complement.  Thus the compact set is eventually contained in the
  corresponding annuli, where the approximants are harmonic and hence
  continuous.  Apply compact Arzelà-Ascoli to a tail and absorb the finite
  shift into the selected subsequence.
-/
theorem approximant_subsequence_extracts_uniformLimit_on_compact_away_pole
    (S : AnnularPerronApproximationSystem X Ω p)
    {K : Set X}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ Ω.carrier \ {p})
    (hpointwise :
      ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ n : ℕ, S.approximant n x ∈ Q)
    (heq_tail :
      ∃ N₀ : ℕ,
        EquicontinuousOn
          (fun n : ℕ ↦ fun x : X ↦ S.approximant (N₀ + n) x) K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : X → ℝ,
        TendstoUniformlyOn
          (fun n : ℕ ↦ fun x : X ↦ S.approximant (φ n) x)
          f Filter.atTop K := by
  classical
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  let F : ℕ → X → ℝ := fun n x ↦ S.approximant n x
  have hp_not_mem : p ∉ K := by
    intro hpK
    exact (hK_subset hpK).2 rfl
  have hdisk_event :
      ∀ᶠ n : ℕ in Filter.atTop, (S.disk n).carrier ⊆ Kᶜ :=
    S.disks_shrink_to_pole hK_compact.isClosed.isOpen_compl hp_not_mem
  rcases Filter.eventually_atTop.mp hdisk_event with ⟨N, hNdisk⟩
  rcases heq_tail with ⟨Neq, heq₀⟩
  let Ntail : ℕ := N + Neq
  have hcont : ∀ n : ℕ, ContinuousOn (F (Ntail + n)) K := by
    intro n
    have hK_annular :
        K ⊆
          (annularPerronDomain Ω (S.disk (Ntail + n))
            (S.disk_subset_domain (Ntail + n))
            (S.annulus_nonempty (Ntail + n))).carrier := by
      intro x hxK
      rw [annularPerronDomain_carrier]
      refine ⟨(hK_subset hxK).1, ?_⟩
      intro hx_disk
      have hN_le : N ≤ Ntail + n := by
        simpa [Ntail, Nat.add_assoc] using Nat.le_add_right N (Neq + n)
      exact hNdisk (Ntail + n) hN_le hx_disk hxK
    exact
      (harmonicOnSurface_continuousOn
        (annularPerronDomain Ω (S.disk (Ntail + n))
          (S.disk_subset_domain (Ntail + n))
          (S.annulus_nonempty (Ntail + n))).isOpen
        (S.solves_annular_problem (Ntail + n)).1).mono hK_annular
  have hpointwise_tail :
      ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ n : ℕ, F (Ntail + n) x ∈ Q := by
    intro x hxK
    rcases hpointwise x hxK with ⟨Q, hQ_compact, hQ_mem⟩
    exact ⟨Q, hQ_compact, fun n ↦ by simpa [F] using hQ_mem (Ntail + n)⟩
  have heq : EquicontinuousOn (fun n : ℕ ↦ F (Ntail + n)) K := by
    intro x hxK V hV
    filter_upwards [heq₀ x hxK V hV] with y hy n
    simpa [F, Ntail, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      hy (N + n)
  rcases realFunctions_tail_subsequence_tendstoUniformlyOn_of_compact_equicontinuousOn
      hK_compact Ntail hcont hpointwise_tail heq with
    ⟨φ, hφ, f, hf⟩
  exact ⟨φ, hφ, f, by simpa [F] using hf⟩

/--
%%handwave
name:
  Compact-local annular Perron limits are harmonic away from the pole
statement:
  If an annular Perron subsequence converges uniformly on every compact
  subset of the punctured smooth domain, then the limit is harmonic on that
  punctured domain.
proof:
  Around each point of the punctured smooth domain, choose a relatively
  compact smooth neighborhood whose closure stays inside the punctured
  domain.  The deleted coordinate disks eventually avoid this closure, so
  the annular approximants are eventually harmonic there.  Compact-local
  convergence passes harmonicity to the limit locally, and local harmonicity
  patches the result.
-/
theorem approximant_subsequence_limit_harmonic_away_pole_of_compact_convergence
    (S : AnnularPerronApproximationSystem X Ω p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier \ {p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ S.approximant (φ k) x)
          f Filter.atTop K) :
    IsHarmonicOnSurface (Ω.carrier \ {p}) f := by
  classical
  let F : ℕ → X → ℝ := fun k x ↦ S.approximant (φ k) x
  refine
    harmonicOnSurface_of_local_eventually_harmonic_forall_compact_tendstoUniformlyOn
      (l := Filter.atTop) (U := Ω.carrier \ {p}) (F := F) (f := f) ?_ ?_
  · intro x hx
    have hpunctured_domain_open : IsOpen (Ω.carrier \ {p}) :=
      Ω.isOpen.sdiff isClosed_singleton
    rcases exists_smoothBoundaryDomain_between_compact_and_open
        (X := X) (K := ({x} : Set X)) (U := Ω.carrier \ {p})
        (isCompact_singleton (x := x)) ⟨x, rfl⟩ hpunctured_domain_open
        (by intro y hy; simpa [Set.mem_singleton_iff.mp hy] using hx) with
      ⟨Ωx, hxΩx, hΩx_closure_subset⟩
    have hΩx_closure_domain : closure Ωx.carrier ⊆ Ω.carrier := fun y hy ↦
      (hΩx_closure_subset hy).1
    have hΩx_closure_punctured : closure Ωx.carrier ⊆ {y : X | y ≠ p} := fun y hy ↦
      (hΩx_closure_subset hy).2
    refine ⟨Ωx.carrier, Ωx.isOpen, hxΩx (by simp), ?_, ?_⟩
    · intro y hy
      exact hΩx_closure_subset (subset_closure hy)
    · simpa [F] using
        hφ.tendsto_atTop.eventually
          (S.approximant_eventually_harmonic_on_relativelyCompact_punctured_region
            Ωx.compact_closure hΩx_closure_domain hΩx_closure_punctured)
  · intro K hKU hK
    exact hconv K hK hKU

/--
%%handwave
name:
  Compact-local annular Perron limits are nonpositive away from the pole
statement:
  If an annular Perron subsequence converges uniformly on every compact
  subset of the punctured smooth domain, then its limit is nonpositive on the
  punctured smooth domain.
proof:
  At a fixed point of the punctured domain, the shrinking deleted disks
  eventually avoid that point, so the annular approximants are eventually
  nonpositive there by the maximum principle.  Uniform convergence on the
  singleton passes the inequality to the limit.
-/
theorem approximant_subsequence_limit_nonpositive_on_punctured_domain_of_compact_convergence
    (S : AnnularPerronApproximationSystem X Ω p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier \ {p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ S.approximant (φ k) x)
          f Filter.atTop K) :
    ∀ x ∈ Ω.carrier \ {p}, f x ≤ 0 := by
  intro x hx
  have hconv_single :
      TendstoUniformlyOn
        (fun k : ℕ ↦ fun y : X ↦ S.approximant (φ k) y)
        f Filter.atTop ({x} : Set X) :=
    hconv ({x} : Set X) (isCompact_singleton (x := x))
      (by
        intro y hy
        simpa [Set.mem_singleton_iff.mp hy] using hx)
  have hnonpos :
      ∀ᶠ k : ℕ in Filter.atTop, S.approximant (φ k) x ≤ 0 :=
    hφ.tendsto_atTop.eventually
      (S.approximant_eventually_nonpositive_at_of_mem_domain_ne_p hx.1 hx.2)
  exact tendstoUniformlyOn_pointwise_le_of_eventually_le
    (K := ({x} : Set X))
    (F := fun k : ℕ ↦ fun y : X ↦ S.approximant (φ k) y)
    (f := f) (x := x) (a := 0) (by simp) hconv_single hnonpos

end AnnularPerronApproximationSystem

/--
%%handwave
name:
  Compact convergence is unchanged by redefining the omitted point
statement:
  Uniform convergence on a set avoiding a point is unchanged if the limiting
  function is redefined at that point.
proof:
  On the set of convergence the original and modified limiting functions
  agree.
-/
theorem tendstoUniformlyOn_update_real_of_subset_ne
    {ι X : Type} [DecidableEq X] {l : Filter ι} {F : ι → X → ℝ}
    {f : X → ℝ} {K : Set X} {p : X} {a : ℝ}
    (hconv : TendstoUniformlyOn F f l K)
    (hK : K ⊆ {x : X | x ≠ p}) :
    TendstoUniformlyOn F (Function.update f p a) l K := by
  exact hconv.congr_right (by
    intro x hxK
    have hxp : x ≠ p := hK hxK
    show f x = Function.update f p a x
    simp [Function.update, hxp])

/--
%%handwave
name:
  Continuity is unchanged by redefining an omitted point
statement:
  If a function is continuous on a set that avoids a point, then redefining
  the function at that point does not change continuity on the set.
proof:
  The original function and the redefined function agree at every point of the
  set.
-/
theorem continuousOn_update_real_of_subset_ne
    {X : Type} [DecidableEq X] [TopologicalSpace X]
    {f : X → ℝ} {K : Set X} {p : X} {a : ℝ}
    (hcont : ContinuousOn f K)
    (hK : K ⊆ {x : X | x ≠ p}) :
    ContinuousOn (Function.update f p a) K := by
  refine hcont.congr ?_
  intro x hxK
  have hxp : x ≠ p := hK hxK
  simp [Function.update, hxp]

/--
%%handwave
name:
  Logarithmic-zero asymptotics ignore the value at the pole
statement:
  If a function has a logarithmic-zero asymptotic at a pole, then redefining
  the function at the pole preserves that asymptotic.
proof:
  The punctured neighborhood used in the asymptotic contains only points
  distinct from the pole, so the two functions agree there.
-/
theorem logarithmic_zero_update_at_pole
    {X : Type} [DecidableEq X] [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {p : X} {f : X → ℝ} {a : ℝ}
    (hlog : HasLogarithmicZeroWithin X U p f) :
    HasLogarithmicZeroWithin X U p (Function.update f p a) := by
  intro χ
  rcases hlog χ with ⟨N, h, hN_open, hpN, hNU, hN_source, hharm, hnear⟩
  refine ⟨N, h, hN_open, hpN, hNU, hN_source, hharm, ?_⟩
  have hne :
      ∀ᶠ x in 𝓝[N ∩ {x : X | x ≠ p}] p, x ≠ p := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hx.2
  filter_upwards [hnear, hne] with x hx hxp
  simpa [Function.update, hxp] using hx

/--
%%handwave
name:
  Logarithmic-pole asymptotics ignore the value at the pole
statement:
  If a function has a logarithmic-pole asymptotic at a pole, then redefining
  the function at the pole preserves that asymptotic.
proof:
  The punctured neighborhood used in the asymptotic contains only points
  distinct from the pole, so the two functions agree there.
-/
theorem logarithmic_singularity_update_at_pole
    {X : Type} [DecidableEq X] [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {f : X → ℝ} {a : ℝ}
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ h : X → ℝ,
          IsHarmonicOnSurface χ.chart.source h ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              f x + Real.log ‖χ.chart x - χ.chart p‖ = h x) :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ h : X → ℝ,
        IsHarmonicOnSurface χ.chart.source h ∧
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            Function.update f p a x + Real.log ‖χ.chart x - χ.chart p‖ = h x := by
  intro χ
  rcases hlog χ with ⟨h, hharm, hnear⟩
  refine ⟨h, hharm, ?_⟩
  have hne :
      ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p, x ≠ p := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hx.2
  filter_upwards [hnear, hne] with x hx hxp
  simpa [Function.update, hxp] using hx

/--
%%handwave
name:
  Boundary values are unchanged by redefining an interior point
statement:
  If a point lies in an open smooth domain, then redefining a function at that
  point does not change its values on the boundary of the domain.
proof:
  The boundary of an open set is disjoint from the set itself.
-/
theorem boundary_zero_update_at_interior
    {X : Type} [DecidableEq X] [TopologicalSpace X] [ChartedSpace ℂ X]
    {Ω : SmoothBoundaryDomain X} {p : X} {f : X → ℝ} {a : ℝ}
    (hpΩ : p ∈ Ω.carrier)
    (hboundary : ∀ x ∈ Ω.boundary, f x = 0) :
    ∀ x ∈ Ω.boundary, Function.update f p a x = 0 := by
  intro x hx
  have hxp : x ≠ p := by
    intro hxp
    have hxΩ : x ∈ Ω.carrier := by simpa [hxp] using hpΩ
    have hx_frontier : x ∈ frontier Ω.carrier := by
      simpa [SmoothBoundaryDomain.boundary] using hx
    have hx_empty : x ∈ (∅ : Set X) := by
      simpa [Ω.isOpen.inter_frontier_eq] using
        (show x ∈ Ω.carrier ∩ frontier Ω.carrier from ⟨hxΩ, hx_frontier⟩)
    exact hx_empty.elim
  simpa [Function.update, hxp] using hboundary x hx

/--
%%handwave
name:
  Punctured nonpositivity survives redefining the pole
statement:
  If a function is nonpositive throughout a domain away from one point, then
  redefining it at that point to a nonpositive value makes it nonpositive on
  the whole domain.
proof:
  At the marked point this is the chosen value.  At every other point the
  original punctured estimate applies.
-/
theorem nonpositive_on_domain_update_at_pole_of_punctured
    {X : Type} [DecidableEq X] [TopologicalSpace X] [ChartedSpace ℂ X]
    {Ω : SmoothBoundaryDomain X} {p : X} {f : X → ℝ} {a : ℝ}
    (ha : a ≤ 0)
    (hnonpos : ∀ x ∈ Ω.carrier \ {p}, f x ≤ 0) :
    ∀ x ∈ Ω.carrier, Function.update f p a x ≤ 0 := by
  intro x hxΩ
  by_cases hxp : x = p
  · simpa [Function.update, hxp] using ha
  · simpa [Function.update, hxp] using hnonpos x ⟨hxΩ, hxp⟩

/--
%%handwave
name:
  Annular Perron approximation systems exist
statement:
  If arbitrarily small closed coordinate disks can be deleted around a pole
  with radius at most one, and the logarithmic annular Dirichlet problem is
  solvable for each such deletion, then one can choose a sequence of deleted
  disks shrinking to the pole together with the corresponding annular Perron
  solutions.
proof:
  Choose a decreasing countable neighborhood basis at the pole.  For each
  basis neighborhood, choose a closed coordinate disk of radius at most one
  contained in that neighborhood and solve the logarithmic annular Dirichlet
  problem.  Since the basis is decreasing and cofinal among neighborhoods of
  the pole, the chosen disks shrink to the pole.
-/
theorem arbitrarilySmall_annularPerron_approximationSystem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) (p : X) (_hp : p ∈ Ω.carrier)
    (hsmallAnnuli :
      ∀ ⦃N : Set X⦄, IsOpen N → p ∈ N →
        ∃ D : ClosedCoordinateDisk X,
          p ∈ D.carrier ∧
            D.closedRadius ≤ 1 ∧
              D.carrier ⊆ Ω.carrier ∧
                D.carrier ⊆ N ∧
                  (Ω.carrier \ D.carrier).Nonempty)
    (happroximants :
      ∀ (D : ClosedCoordinateDisk X)
        (_hpD : p ∈ D.carrier)
        (hD_subset : D.carrier ⊆ Ω.carrier)
        (hnonempty : (Ω.carrier \ D.carrier).Nonempty),
        ∃ u : X → ℝ,
          SolvesHarmonicDirichletProblem
            (annularPerronDomain Ω D hD_subset hnonempty)
            (annularLogBoundaryData Ω D hD_subset hnonempty) u) :
    Nonempty (AnnularPerronApproximationSystem X Ω p) := by
  classical
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  haveI : (𝓝 p).IsCountablyGenerated := inferInstance
  rcases (nhds_basis_opens p).exists_antitone_subbasis with
    ⟨N, hN_prop, hN_basis⟩
  have hchoose_disk :
      ∀ n : ℕ,
        ∃ D : ClosedCoordinateDisk X,
          p ∈ D.carrier ∧
            D.closedRadius ≤ 1 ∧
              D.carrier ⊆ Ω.carrier ∧
                D.carrier ⊆ N n ∧
                  (Ω.carrier \ D.carrier).Nonempty := by
    intro n
    exact hsmallAnnuli (hN_prop n).2 (hN_prop n).1
  choose D hD using hchoose_disk
  have hchoose_solution :
      ∀ n : ℕ,
        ∃ u : X → ℝ,
          SolvesHarmonicDirichletProblem
            (annularPerronDomain Ω (D n)
              ((hD n).2.2.1) ((hD n).2.2.2.2))
            (annularLogBoundaryData Ω (D n)
              ((hD n).2.2.1) ((hD n).2.2.2.2)) u := by
    intro n
    exact happroximants (D n) (hD n).1 (hD n).2.2.1 (hD n).2.2.2.2
  choose u hu using hchoose_solution
  refine ⟨{
    disk := D
    pole_mem_disk := fun n ↦ (hD n).1
    closedRadius_le_one := fun n ↦ (hD n).2.1
    disk_subset_domain := fun n ↦ (hD n).2.2.1
    annulus_nonempty := fun n ↦ (hD n).2.2.2.2
    approximant := u
    solves_annular_problem := hu
    disks_shrink_to_pole := ?_
  }⟩
  intro U hU_open hpU
  have hU_mem : U ∈ 𝓝 p := hU_open.mem_nhds hpU
  rcases hN_basis.mem_iff.mp hU_mem with ⟨i, hi_subset⟩
  filter_upwards [Filter.eventually_atTop.2 ⟨i, fun n hn ↦ hn⟩] with n hn
  exact ((hD n).2.2.2.1).trans ((hN_basis.2 hn).trans hi_subset)

/--
%%handwave
name:
  Annular Perron zero-radius Green limit
statement:
  An annular Perron zero-radius Green limit consists of logarithmic annular
  Perron solutions on closed coordinate disks shrinking to a pole, together
  with a subsequence that converges locally uniformly on compact subsets away
  from the pole.  The limit is a bounded-domain negative Green potential: it
  is harmonic away from the pole, has zero outer boundary value, is
  nonpositive in the domain, and has the logarithmic zero at the pole.
-/
structure AnnularPerronBoundedNegativeGreenLimit
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (Ω : SmoothBoundaryDomain X) (p : X) where
  /-- Closed coordinate disks deleted from the smooth domain. -/
  disk : ℕ → ClosedCoordinateDisk X
  /-- Each deleted disk contains the pole. -/
  pole_mem_disk : ∀ n : ℕ, p ∈ (disk n).carrier
  /-- Each deleted disk is contained in the smooth domain. -/
  disk_subset_domain : ∀ n : ℕ, (disk n).carrier ⊆ Ω.carrier
  /-- Deleting each disk leaves a nonempty annular region. -/
  annulus_nonempty : ∀ n : ℕ, (Ω.carrier \ (disk n).carrier).Nonempty
  /-- The annular Perron solutions. -/
  approximant : ℕ → X → ℝ
  /-- Each approximant solves the logarithmic annular Dirichlet problem. -/
  solves_annular_problem :
    ∀ n : ℕ,
      SolvesHarmonicDirichletProblem
        (annularPerronDomain Ω (disk n)
          (disk_subset_domain n) (annulus_nonempty n))
        (annularLogBoundaryData Ω (disk n)
          (disk_subset_domain n) (annulus_nonempty n))
        (approximant n)
  /-- The deleted disks shrink to the pole. -/
  disks_shrink_to_pole :
    ∀ ⦃N : Set X⦄, IsOpen N → p ∈ N →
      ∀ᶠ n : ℕ in Filter.atTop, (disk n).carrier ⊆ N
  /-- The selected zero-radius subsequence. -/
  subseq : ℕ → ℕ
  /-- The selected subsequence is strictly increasing. -/
  subseq_strictMono : StrictMono subseq
  /-- The limiting bounded-domain Green potential. -/
  toFun : X → ℝ
  /-- The limit is harmonic away from the pole in the smooth domain. -/
  harmonic_away_pole : IsHarmonicOnSurface (Ω.carrier \ {p}) toFun
  /-- The limit is continuous on the closed smooth domain away from the pole. -/
  continuousOn_punctured_closure : ContinuousOn toFun (closure Ω.carrier \ {p})
  /-- The limit has zero value on the outer boundary. -/
  boundary_zero : ∀ x ∈ Ω.boundary, toFun x = 0
  /-- The limit is nonpositive in the smooth domain. -/
  nonpositive_on_domain : ∀ x ∈ Ω.carrier, toFun x ≤ 0
  /-- The limit tends to \(-\infty\) at the pole from inside the domain. -/
  tends_to_neg_infinity_at_pole :
    Filter.Tendsto toFun (𝓝[Ω.carrier \ {p}] p) Filter.atBot
  /-- The logarithmic zero at the pole is locally removable inside the bounded domain. -/
  logarithmic_zero : HasLogarithmicZeroWithin X Ω.carrier p toFun
  /-- The annular Perron solutions converge locally uniformly away from the pole. -/
  locally_uniform_on_compacts_away_pole :
    ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier \ {p} →
      TendstoUniformlyOn (fun k : ℕ ↦ approximant (subseq k)) toFun Filter.atTop K

namespace AnnularPerronBoundedNegativeGreenLimit

/--
%%handwave
name:
  Annular Perron zero-radius limits are bounded Green potentials
statement:
  Every zero-radius annular Perron Green limit determines a bounded-domain
  negative Green potential with the same pole.
proof:
  The defining fields of the limit are exactly the harmonicity, boundary
  value, sign, pole divergence, and logarithmic-zero conditions required of a
  bounded-domain negative Green potential.
-/
def toBoundedNegativeGreenPotential
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (L : AnnularPerronBoundedNegativeGreenLimit X Ω p) :
    BoundedNegativeGreenPotential X Ω p where
  toFun := L.toFun
  harmonic_away_pole := L.harmonic_away_pole
  continuousOn_punctured_closure := L.continuousOn_punctured_closure
  boundary_zero := L.boundary_zero
  nonpositive_on_domain := L.nonpositive_on_domain
  tends_to_neg_infinity_at_pole := L.tends_to_neg_infinity_at_pole
  logarithmic_zero := L.logarithmic_zero

end AnnularPerronBoundedNegativeGreenLimit

/--
%%handwave
name:
  Assembling an annular Perron zero-radius Green limit
statement:
  A compact-local subsequential limit of annular Perron approximants, together
  with the outer boundary value, sign condition, and logarithmic-zero
  asymptotic, determines a zero-radius bounded-domain Green limit.
proof:
  The compact-local convergence gives harmonicity on the punctured domain.
  The supplied boundary, sign, and logarithmic-zero data fill the remaining
  fields.  The logarithmic-zero asymptotic implies decay to \(-\infty\) at
  the pole, and restricting the punctured-surface limit to the punctured
  domain gives the required pole limit.
-/
def annularPerronBoundedNegativeGreenLimit_of_compact_convergence_and_asymptotics
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (S : AnnularPerronApproximationSystem X Ω p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier \ {p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ S.approximant (φ k) x)
          f Filter.atTop K)
    (hcont : ContinuousOn f (closure Ω.carrier \ {p}))
    (hboundary : ∀ x ∈ Ω.boundary, f x = 0)
    (hnonpos : ∀ x ∈ Ω.carrier, f x ≤ 0)
    (hlog : HasLogarithmicZeroWithin X Ω.carrier p f) :
    AnnularPerronBoundedNegativeGreenLimit X Ω p where
  disk := S.disk
  pole_mem_disk := S.pole_mem_disk
  disk_subset_domain := S.disk_subset_domain
  annulus_nonempty := S.annulus_nonempty
  approximant := S.approximant
  solves_annular_problem := S.solves_annular_problem
  disks_shrink_to_pole := S.disks_shrink_to_pole
  subseq := φ
  subseq_strictMono := hφ
  toFun := f
  harmonic_away_pole :=
    S.approximant_subsequence_limit_harmonic_away_pole_of_compact_convergence
      hφ hconv
  continuousOn_punctured_closure := hcont
  boundary_zero := hboundary
  nonpositive_on_domain := hnonpos
  tends_to_neg_infinity_at_pole :=
    logarithmic_zero_within_tendsto_atBot Ω.isOpen
      (S.disk_subset_domain 0 (S.pole_mem_disk 0)) hlog
  logarithmic_zero := hlog
  locally_uniform_on_compacts_away_pole := hconv

/--
%%handwave
name:
  Normalized annular approximants admit bounded exterior majorants, core
statement:
  For a logarithmically normalized annular Perron approximation system and a
  fixed point \(q\ne p\) in the smooth domain, the positive functions
  \(-u_n\) admit, for all sufficiently small deleted disks, superharmonic
  majorants on the annular domains whose values at \(q\) are bounded by one
  constant independent of \(n\).
proof:
  Solve one fixed annular Dirichlet problem with values one and zero on its
  two boundary parts.  Its normalized harmonic measure is strictly less than
  one on a larger coordinate circle.  Hubbard's minimum construction pastes
  a multiple of this harmonic measure to a logarithmic pole model, producing
  one superharmonic barrier for every sufficiently small moving annulus.  A
  constant shift absorbs the uniform logarithmic normalization error.
-/
theorem annularPerron_normalized_approximationSystem_eventual_negative_majorant_at_point_core
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p q : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    (_hq : q ∈ Ω.carrier \ {p}) :
    ∃ A : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ b : X → ℝ,
          ContinuousOn b
            (closure
              (annularPerronDomain Ω (S.disk n)
                (S.disk_subset_domain n) (S.annulus_nonempty n)).carrier) ∧
          IsSuperharmonicOnSurface
            (annularPerronDomain Ω (S.disk n)
              (S.disk_subset_domain n) (S.annulus_nonempty n)).carrier b ∧
          (∀ x ∈
              (annularPerronDomain Ω (S.disk n)
                (S.disk_subset_domain n) (S.annulus_nonempty n)).boundary,
            -(S.approximant n x) ≤ b x) ∧
          b q ≤ A := by
  classical
  let χ : PointedSurfaceCoordinate X p :=
    { chart := chartAt ℂ p
      chart_mem_atlas := chart_mem_atlas ℂ p
      base_mem_source := mem_chart_source ℂ p }
  have hpΩ : p ∈ Ω.carrier :=
    S.disk_subset_domain 0 (S.pole_mem_disk 0)
  rcases S.approximant_logarithmic_remainder_bound_on_inner_boundary
      hnormalized χ with
    ⟨C, hC_event⟩
  rcases
      exists_centered_closedCoordinateDisk_openDisk_subset_open_avoids_point
        Ω.isOpen hpΩ _hq.2 with
    ⟨D, hp_interior, hD_radius_one, hD_chart, hD_center,
      hopenDisk_subset, hD_subset, hq_notD⟩
  have hpD : p ∈ D.carrier := interior_subset hp_interior
  have hnonempty : (Ω.carrier \ D.carrier).Nonempty :=
    ⟨q, _hq.1, hq_notD⟩
  have hcenter : D.openDisk.center = D.openDisk.chart p := by
    rw [hD_center, hD_chart]
  let ρ : ℝ := (D.closedRadius + D.openDisk.radius) / 2
  have hDρ : D.closedRadius < ρ := by
    dsimp [ρ]
    linarith [D.closedRadius_lt_openRadius]
  have hρ_open : ρ < D.openDisk.radius := by
    dsimp [ρ]
    linarith [D.closedRadius_lt_openRadius]
  rcases annularPerron_dirichlet_solution Ω D hD_subset hnonempty with
    ⟨u, hu⟩
  rcases exists_annularPerronUnitHarmonicMeasure_outerCircle_bound
      hnoncompact Ω hpΩ D hpD hopenDisk_subset hD_subset hnonempty
      hD_radius_one hu hDρ hρ_open with
    ⟨a, ha_one, hcircle_bound⟩
  rcases exists_hubbard_barrier_constants
      D.closedRadius_pos hDρ ha_one with
    ⟨A, B, hB, houter, hinner⟩
  rcases hubbardAnnularPerronBarrier_properties
      Ω D hpD hp_interior hcenter hopenDisk_subset hD_subset hnonempty
      hD_radius_one hu hDρ hρ_open hcircle_bound hB houter hinner with
    ⟨hb₀_cont, hb₀_super, hb₀_model, hb₀_outer⟩
  let K : ℝ := max 0 (C - A)
  let b : X → ℝ := fun x ↦ hubbardAnnularPerronBarrier D ρ u A B x + K
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact le_max_left 0 (C - A)
  have hC_le_AK : C ≤ A + K := by
    have hCA : C - A ≤ K := by
      dsimp [K]
      exact le_max_right 0 (C - A)
    linarith
  have hb_cont : ContinuousOn b (closure Ω.carrier \ {p}) := by
    simpa [b] using hb₀_cont.add continuousOn_const
  have hb_super : IsSuperharmonicOnSurface (Ω.carrier \ {p}) b := by
    simpa [b] using superharmonicOnSurface_add_const K hb₀_super
  refine ⟨b q, ?_⟩
  have hdisks_event :
      ∀ᶠ n : ℕ in Filter.atTop,
        (S.disk n).carrier ⊆ interior D.carrier :=
    S.disks_shrink_to_pole isOpen_interior hp_interior
  have hp_interior_event :
      ∀ᶠ n : ℕ in Filter.atTop, p ∈ interior (S.disk n).carrier :=
    S.disk_eventually_pole_mem_interior_of_logarithmicBoundaryNormalization
      hnormalized χ
  filter_upwards [hC_event, hdisks_event, hp_interior_event] with
    n hC_n hdisk_subset_fixed hp_moving_interior
  let Ωn : PerronDomain X :=
    annularPerronDomain Ω (S.disk n)
      (S.disk_subset_domain n) (S.annulus_nonempty n)
  refine ⟨b, ?_, ?_, ?_, le_rfl⟩
  · have hclosure_punctured : closure Ωn.carrier ⊆ {x : X | x ≠ p} := by
      have hcarrier_subset_compl_interior :
          Ωn.carrier ⊆ (interior (S.disk n).carrier)ᶜ := by
        intro y hy hy_interior
        have hy_annular : y ∈ Ω.carrier \ (S.disk n).carrier := by
          simpa [Ωn, annularPerronDomain_carrier] using hy
        exact hy_annular.2 (interior_subset hy_interior)
      have hclosure_subset_compl_interior :
          closure Ωn.carrier ⊆ (interior (S.disk n).carrier)ᶜ :=
        closure_minimal hcarrier_subset_compl_interior
          (isOpen_interior.isClosed_compl)
      intro y hy hy_eq_p
      exact hclosure_subset_compl_interior hy
        (by simpa [hy_eq_p] using hp_moving_interior)
    have hclosure_domain : closure Ωn.carrier ⊆ closure Ω.carrier := by
      apply closure_mono
      intro y hy
      have hy_annular : y ∈ Ω.carrier \ (S.disk n).carrier := by
        simpa [Ωn, annularPerronDomain_carrier] using hy
      exact hy_annular.1
    exact hb_cont.mono (fun y hy ↦
      ⟨hclosure_domain hy, hclosure_punctured hy⟩)
  · have hcarrier_punctured_domain : Ωn.carrier ⊆ Ω.carrier \ {p} := by
      intro y hy
      have hy_annular : y ∈ Ω.carrier \ (S.disk n).carrier := by
        simpa [Ωn, annularPerronDomain_carrier] using hy
      refine ⟨hy_annular.1, ?_⟩
      intro hy_eq_p
      subst y
      exact hy_annular.2 (S.pole_mem_disk n)
    exact superharmonicOnSurface_mono hcarrier_punctured_domain hb_super
  · intro x hx_boundary
    have hx_boundary' : x ∈ Ωn.boundary := by
      simpa [Ωn] using hx_boundary
    rcases
        annularPerronDomain_boundary_subset_outer_or_inner
          Ω (S.disk n) (S.disk_subset_domain n) (S.annulus_nonempty n)
          hx_boundary' with
      hx_outer | hx_inner
    · have happrox_zero : S.approximant n x = 0 :=
        S.approximant_eq_zero_on_outer_boundary n hx_outer
      rw [happrox_zero]
      have hb₀_zero : hubbardAnnularPerronBarrier D ρ u A B x = 0 :=
        hb₀_outer x hx_outer
      simp [b, hb₀_zero, hK_nonneg]
    · rcases hC_n x (by simpa [Ωn] using hx_boundary') hx_inner with
        ⟨hx_source, hx_ne_p, hlog_bound⟩
      have hxD : x ∈ D.carrier :=
        interior_subset
          (hdisk_subset_fixed
            ((S.disk n).boundaryCircle_subset_carrier hx_inner))
      have hb₀_eq :
          hubbardAnnularPerronBarrier D ρ u A B x =
            A - Real.log ‖χ.chart x - χ.chart p‖ := by
        rw [hb₀_model x hxD hx_ne_p]
        simp [closedCoordinateDiskLogarithmicModel, hD_chart, hD_center, χ]
      have hb_eq :
          b x = -Real.log ‖χ.chart x - χ.chart p‖ + (A + K) := by
        rw [show b x = hubbardAnnularPerronBarrier D ρ u A B x + K by rfl,
          hb₀_eq]
        ring
      rw [hb_eq]
      have hlower :
          -C ≤ S.approximant n x -
              Real.log ‖χ.chart x - χ.chart p‖ := by
        exact (abs_le.mp (by
          simpa [Real.norm_eq_abs] using hlog_bound)).1
      have hneg_le_C :
          -(S.approximant n x) ≤
            -Real.log ‖χ.chart x - χ.chart p‖ + C := by
        linarith
      exact hneg_le_C.trans (by linarith)

/--
%%handwave
name:
  Normalized annular approximants are bounded at fixed interior points, core
statement:
  For a logarithmically normalized zero-radius annular Perron approximation
  system, at every fixed point of the punctured smooth domain the negatives
  of the annular solutions are eventually bounded above.
proof:
  Use the bounded exterior majorants for the positive functions \(-u_n\).
  The maximum principle compares \(-u_n\) with such a superharmonic majorant
  on each annular domain, and the majorant values at the fixed point are
  uniformly bounded.
-/
theorem annularPerron_normalized_approximationSystem_eventual_base_bound_core
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p q : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    (hq : q ∈ Ω.carrier \ {p}) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in Filter.atTop, -(S.approximant n q) ≤ A := by
  rcases
    annularPerron_normalized_approximationSystem_eventual_negative_majorant_at_point_core
      hnoncompact S hnormalized hq with
    ⟨A, hA⟩
  refine ⟨A, ?_⟩
  filter_upwards
    [hA, S.eventually_mem_annularPerronDomain_of_mem_domain_ne_p hq.1 hq.2]
    with n hmajorant hq_domain
  rcases hmajorant with ⟨b, hb_cont, hb_super, hb_boundary, hbq⟩
  let Ωn : PerronDomain X :=
    annularPerronDomain Ω (S.disk n)
      (S.disk_subset_domain n) (S.annulus_nonempty n)
  have hΩn_geometry : HasComponentwiseMaximumPrincipleGeometry Ωn.carrier := by
    simpa [Ωn] using
      annularPerronDomain_hasComponentwiseMaximumPrincipleGeometry
        Ω (S.disk n) (S.disk_subset_domain n) (S.annulus_nonempty n)
  have hneg_cont :
      ContinuousOn (fun x : X ↦ -(S.approximant n x)) (closure Ωn.carrier) := by
    simpa [Ωn] using (S.solves_annular_problem n).2.1.neg
  have hneg_harm :
      IsHarmonicOnSurface Ωn.carrier
        (fun x : X ↦ -(S.approximant n x)) := by
    simpa [Ωn] using harmonicOnSurface_neg (S.solves_annular_problem n).1
  have hneg_sub :
      IsSubharmonicOnSurface Ωn.carrier
        (fun x : X ↦ -(S.approximant n x)) :=
    harmonicOnSurface_subharmonic Ωn.isOpen hneg_harm
  have hb_cont' : ContinuousOn b (closure Ωn.carrier) := by
    simpa [Ωn] using hb_cont
  have hb_super' : IsSuperharmonicOnSurface Ωn.carrier b := by
    simpa [Ωn] using hb_super
  have hboundary :
      ∀ x ∈ Ωn.boundary, -(S.approximant n x) ≤ b x := by
    intro x hx
    exact hb_boundary x (by simpa [Ωn] using hx)
  have hle_all :
      ∀ x ∈ Ωn.carrier, -(S.approximant n x) ≤ b x :=
    subharmonic_le_superharmonic_of_boundary_le Ωn hΩn_geometry
      hneg_cont hneg_sub hb_cont' hb_super' hboundary
  exact (hle_all q (by simpa [Ωn] using hq_domain)).trans hbq

/--
%%handwave
name:
  Annular approximants are bounded at fixed interior points
statement:
  For a logarithmically normalized zero-radius annular Perron approximation
  system and every fixed point of the punctured smooth domain, the negatives
  of the annular approximants are eventually bounded above.
proof:
  Compare the negative approximants with the fixed Hubbard superharmonic
  barrier and apply the maximum principle.
-/
theorem annularPerron_approximationSystem_eventual_base_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p q : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    (hq : q ∈ Ω.carrier \ {p}) :
    ∃ A : ℝ, ∀ᶠ n : ℕ in Filter.atTop, -(S.approximant n q) ≤ A := by
  exact
    annularPerron_normalized_approximationSystem_eventual_base_bound_core
      hnoncompact S hnormalized hq

/--
%%handwave
name:
  Annular approximants have compact lower bounds in punctured regions
statement:
  On every compact subset of a preconnected relatively compact region whose
  closure lies in the punctured smooth domain, the annular Perron
  approximants are eventually bounded below by one finite constant.
proof:
  Choose a base point in the preconnected region.  The annular base-point
  estimate bounds the negative approximants there, and Harnack comparison
  propagates that bound uniformly to the compact subset.
-/
theorem approximant_eventual_uniform_lower_bound_on_compact_in_preconnected_punctured_region
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    {K U : Set X}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_subset_domain : closure U ⊆ Ω.carrier)
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    {q : X} (hqU : q ∈ U) :
    ∃ M : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ y ∈ K, -M ≤ S.approximant n y := by
  have hq_closure : q ∈ closure U := subset_closure hqU
  have hq_domain : q ∈ Ω.carrier \ {p} :=
    ⟨hU_subset_domain hq_closure, hU_punctured_closure hq_closure⟩
  rcases annularPerron_approximationSystem_eventual_base_bound
      hnoncompact S hnormalized hq_domain with
    ⟨A, hbase⟩
  rcases S.neg_approximant_eventual_uniform_bound_on_compact_of_base_bound
      hbase hU_open hU_preconnected hK_compact hKU hU_compact_closure
      hU_subset_domain hU_punctured_closure hqU with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  filter_upwards [hM] with n hn y hyK
  have hneg : -(S.approximant n y) ≤ M := hn y hyK
  linarith

/--
%%handwave
name:
  Annular approximants have compact lower bounds away from the pole
statement:
  On every compact subset of the smooth domain that avoids the pole, the
  annular Perron approximants are eventually bounded below by one finite
  constant.
proof:
  Around each compact-set point, choose a small relatively compact punctured
  coordinate neighborhood.  The fixed-point annular lower bound and local
  Harnack control give a uniform lower bound on a neighborhood of that point.
  Compactness gives a finite subcover and hence one eventual bound on the
  whole compact set.
-/
theorem approximant_eventual_uniform_lower_bound_on_compact_punctured_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    {K : Set X}
    (hK_compact : IsCompact K)
    (hK_subset_domain : K ⊆ Ω.carrier)
    (hK_punctured : K ⊆ {x : X | x ≠ p}) :
    ∃ M : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ y ∈ K, -M ≤ S.approximant n y := by
  classical
  have hpunctured_open : IsOpen (Ω.carrier \ ({p} : Set X)) :=
    Ω.isOpen.sdiff isClosed_singleton
  have hloc :
      ∀ x ∈ K,
        ∃ O : Set X, IsOpen O ∧ x ∈ O ∧
          ∃ M : ℝ,
            ∀ᶠ n : ℕ in Filter.atTop,
              ∀ y ∈ O, -(S.approximant n y) ≤ M := by
    intro x hxK
    have hxU : x ∈ Ω.carrier \ ({p} : Set X) :=
      ⟨hK_subset_domain hxK, by simpa using hK_punctured hxK⟩
    rcases exists_surface_open_nhds_isCompact_closure_subset
        (X := X) hpunctured_open hxU with
      ⟨U, hU_open, hxU_mem, hU_closure_subset, hU_compact_closure⟩
    rcases annularPerron_approximationSystem_eventual_base_bound
        hnoncompact S hnormalized hxU with
      ⟨A, hA⟩
    rcases S.neg_approximant_eventual_local_harnack_control
        hU_open hU_compact_closure
        (fun y hy ↦ (hU_closure_subset hy).1)
        (fun y hy ↦ (hU_closure_subset hy).2)
        hxU_mem with
      ⟨N, hN_nhds, _hN_subset, C, hC_pos, hcontrol⟩
    rcases mem_nhds_iff.mp hN_nhds with
      ⟨O, hON, hO_open, hxO⟩
    refine ⟨O, hO_open, hxO, max (C * A) 0, ?_⟩
    filter_upwards [hcontrol, hA] with n hcontrol_n hA_n y hyO
    have hyN : y ∈ N := hON hyO
    have hctrl : -(S.approximant n y) ≤ C * (-(S.approximant n x)) :=
      hcontrol_n y hyN
    have hupper : -(S.approximant n y) ≤ C * A :=
      hctrl.trans (mul_le_mul_of_nonneg_left hA_n hC_pos.le)
    exact hupper.trans (le_max_left (C * A) 0)
  choose O hO_open hxO M hM using hloc
  rcases
    eventual_uniform_upper_bound_on_compact_of_open_local_uniform_upper_bound
      (K := K) (U := K) (F := fun n y ↦ -(S.approximant n y))
      (O := fun x ↦ if hx : x ∈ K then O x hx else ∅)
      (M := fun x ↦ if hx : x ∈ K then M x hx else 0)
      hK_compact (fun _ hx ↦ hx)
      (fun x hx ↦ by simpa [hx] using hO_open x hx)
      (fun x hx ↦ by simpa [hx] using hxO x hx)
      (fun x hx ↦ by
        simpa [hx] using hM x hx) with
    ⟨A, hA⟩
  refine ⟨A, ?_⟩
  filter_upwards [hA] with n hn y hyK
  have hneg : -(S.approximant n y) ≤ A := hn y hyK
  linarith

/--
%%handwave
name:
  A cap barrier converts artificial-boundary lower bounds into boundary
  neighborhood lower bounds
statement:
  Let \(C\) be a Perron cap touching a boundary point \(x\).  Suppose \(B\)
  is a nonnegative superharmonic barrier on the cap tending to zero at \(x\),
  and suppose the cap boundary is split between the true outer boundary and a
  compact artificial boundary \(K\), where \(B\) has a positive floor.  If a
  sequence of harmonic functions is zero on the true boundary and eventually
  bounded below on \(K\), then it is eventually greater than
  \(-\varepsilon\) on a fixed neighborhood of \(x\) inside the ambient
  domain.
proof:
  Calibrate \(A-CB\), with \(A=-\varepsilon/2\), so that it lies below the
  functions on both boundary pieces.  The affine negative barrier is
  subharmonic and the functions are harmonic, so the comparison principle
  propagates the inequality through the cap.  Since \(B\to0\) at \(x\), the
  affine barrier is greater than \(-\varepsilon\) near \(x\).
-/
theorem cap_barrier_eventually_gt_boundary_sub_of_artificial_boundary_lower_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X}
    (Cdom : PerronDomain X)
    (hC_geometry : HasComponentwiseMaximumPrincipleGeometry Cdom.carrier)
    {x : X} {K : Set X} {B : X → ℝ} {F : ℕ → X → ℝ}
    {ε M δ : ℝ}
    (hε : 0 < ε)
    (hδ : 0 < δ)
    (hcap_nhds : Cdom.carrier ∈ 𝓝[Ω.carrier] x)
    (hB_tendsto : Filter.Tendsto B (𝓝[Ω.carrier] x) (𝓝 0))
    (hB_cont : ContinuousOn B (closure Cdom.carrier))
    (hB_super : IsSuperharmonicOnSurface Cdom.carrier B)
    (hB_nonneg_boundary : ∀ y ∈ Cdom.boundary, 0 ≤ B y)
    (hB_floor_K : ∀ y ∈ K, δ ≤ B y)
    (hboundary_split :
      ∀ y ∈ Cdom.boundary, y ∈ Ω.boundary ∨ y ∈ K)
    (hF_cont :
      ∀ᶠ n : ℕ in Filter.atTop,
        ContinuousOn (F n) (closure Cdom.carrier))
    (hF_harmonic :
      ∀ᶠ n : ℕ in Filter.atTop,
        IsHarmonicOnSurface Cdom.carrier (F n))
    (hF_outer_zero :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ y ∈ Ω.boundary, F n y = 0)
    (hF_lower_K :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ y ∈ K, -M ≤ F n y) :
    ∀ᶠ y in 𝓝[Ω.carrier] x,
      ∀ᶠ n : ℕ in Filter.atTop, -ε < F n y := by
  let A : ℝ := -ε / 2
  let Cc : ℝ := max 0 ((M - ε / 2) / δ)
  have hCc_nonneg : 0 ≤ Cc := le_max_left 0 ((M - ε / 2) / δ)
  have hgap_le_Cδ : M - ε / 2 ≤ Cc * δ := by
    have hdiv_le_C : (M - ε / 2) / δ ≤ Cc :=
      le_max_right 0 ((M - ε / 2) / δ)
    calc
      M - ε / 2 = ((M - ε / 2) / δ) * δ := by
        exact (div_mul_cancel₀ (M - ε / 2) hδ.ne').symm
      _ ≤ Cc * δ := mul_le_mul_of_nonneg_right hdiv_le_C hδ.le
  have hCB_tendsto :
      Filter.Tendsto (fun y : X ↦ Cc * B y) (𝓝[Ω.carrier] x) (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul Cc hB_tendsto)
  have hsmall :
      ∀ᶠ y in 𝓝[Ω.carrier] x, Cc * B y < ε / 2 := by
    exact (tendsto_order.mp hCB_tendsto).2 (ε / 2) (by linarith)
  filter_upwards [hcap_nhds, hsmall] with y hyC hsmall_y
  filter_upwards [hF_cont, hF_harmonic, hF_outer_zero, hF_lower_K] with
    n hcont_n hharm_n houter_n hlowerK_n
  have hboundary :
      ∀ z ∈ Cdom.boundary, A - Cc * B z ≤ F n z := by
    intro z hz_boundary
    rcases hboundary_split z hz_boundary with hz_outer | hzK
    · have hz_zero : F n z = 0 := houter_n z hz_outer
      have hB_nonneg : 0 ≤ B z := hB_nonneg_boundary z hz_boundary
      have hscaled_nonneg : 0 ≤ Cc * B z :=
        mul_nonneg hCc_nonneg hB_nonneg
      dsimp [A]
      rw [hz_zero]
      linarith
    · have hB_floor : δ ≤ B z := hB_floor_K z hzK
      have hscaled_floor : Cc * δ ≤ Cc * B z :=
        mul_le_mul_of_nonneg_left hB_floor hCc_nonneg
      have hgap_le_CB : M - ε / 2 ≤ Cc * B z :=
        hgap_le_Cδ.trans hscaled_floor
      have hlower_z : -M ≤ F n z := hlowerK_n z hzK
      dsimp [A]
      linarith
  have hcomp :
      A - Cc * B y ≤ F n y :=
    affine_neg_superharmonic_le_harmonic_of_boundary_le
      Cdom hC_geometry hCc_nonneg hB_cont hB_super hcont_n hharm_n
      hboundary y hyC
  have hbarrier_gt : -ε < A - Cc * B y := by
    dsimp [A] at hsmall_y ⊢
    linarith
  exact hbarrier_gt.trans_le hcomp

/--
%%handwave
name:
  Smooth boundary points admit punctured interior barrier caps
statement:
  Let \(x\) be a smooth boundary point different from the pole.  There is a
  relatively compact Perron cap approaching \(x\) from inside the domain, a
  nonnegative superharmonic barrier on the cap tending to zero at \(x\), and a
  compact artificial edge lying in a connected punctured interior region.
  The cap boundary is contained in the union of the true outer boundary and
  this artificial edge, and the barrier has a positive floor on the artificial
  edge.
proof:
  Choose a small closed coordinate disk around the pole with the pole in its
  interior and the disk compactly contained in the smooth domain.  Removing
  this disk gives an annular collar of the outer boundary; its artificial
  boundary is the compact frontier of the deleted disk and its closure avoids
  the pole.  A global Perron barrier at \(x\) tends to zero along the outer
  boundary approach and has a positive floor on the compact artificial edge.
-/
theorem smoothBoundaryDomain_exists_punctured_interior_barrier_cap_data
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p x : X}
    (hp : p ∈ Ω.carrier) (hx_boundary : x ∈ Ω.boundary) (_hxp : x ≠ p) :
    ∃ Cdom : PerronDomain X, ∃ K : Set X,
      ∃ B : X → ℝ, ∃ δ : ℝ,
        0 < δ ∧
          HasComponentwiseMaximumPrincipleGeometry Cdom.carrier ∧
            Cdom.carrier ∈ 𝓝[Ω.carrier] x ∧
              Cdom.carrier ⊆ Ω.carrier ∧
                closure Cdom.carrier ⊆ closure Ω.carrier ∧
                  closure Cdom.carrier ⊆ {z : X | z ≠ p} ∧
                    Filter.Tendsto B (𝓝[Ω.carrier] x) (𝓝 0) ∧
                      ContinuousOn B (closure Cdom.carrier) ∧
                        IsSuperharmonicOnSurface Cdom.carrier B ∧
                          (∀ y ∈ Cdom.boundary, 0 ≤ B y) ∧
                            (∀ y ∈ K, δ ≤ B y) ∧
                              (∀ y ∈ Cdom.boundary,
                                y ∈ Ω.boundary ∨ y ∈ K) ∧
                                IsCompact K ∧
                                  K ⊆ Ω.carrier ∧
                                    K ⊆ {z : X | z ≠ p} := by
  classical
  have hx_perron :
      x ∈ (PerronDomain.ofSmoothBoundaryDomain Ω).boundary := by
    simpa using hx_boundary
  rcases smoothBoundaryDomain_boundary_points_have_barriers Ω x hx_perron with
    ⟨_hx_boundary, B, hB_contΩ, hB_superΩ, hB_zero, hB_posΩ⟩
  rcases exists_ne_mem_open_of_mem Ω.isOpen hp with
    ⟨q, hqΩ, hq_ne_p⟩
  rcases exists_closedCoordinateDisk_mem_interior_subset_open_avoids_point
      Ω.isOpen hp hq_ne_p with
    ⟨D, hpD_int, _hD_radius, hD_subset, hq_notD⟩
  have hnonempty : (Ω.carrier \ D.carrier).Nonempty :=
    ⟨q, hqΩ, hq_notD⟩
  let Cdom : PerronDomain X := annularPerronDomain Ω D hD_subset hnonempty
  let K : Set X := frontier D.carrier
  have hx_frontier : x ∈ frontier Ω.carrier := by
    simpa [SmoothBoundaryDomain.boundary] using hx_boundary
  have hx_closureΩ : x ∈ closure Ω.carrier :=
    frontier_subset_closure hx_frontier
  have hx_notD : x ∉ D.carrier := by
    intro hxD
    have hx_empty : x ∈ Ω.carrier ∩ frontier Ω.carrier :=
      ⟨hD_subset hxD, hx_frontier⟩
    simp [Ω.isOpen.inter_frontier_eq] at hx_empty
  have hC_geometry :
      HasComponentwiseMaximumPrincipleGeometry Cdom.carrier := by
    simpa [Cdom] using
      annularPerronDomain_hasComponentwiseMaximumPrincipleGeometry
        Ω D hD_subset hnonempty
  have hDcompl_mem : D.carrierᶜ ∈ 𝓝 x :=
    (ClosedCoordinateDisk.isClosed D).isOpen_compl.mem_nhds hx_notD
  have hcap_nhds : Cdom.carrier ∈ 𝓝[Ω.carrier] x := by
    change (annularPerronDomain Ω D hD_subset hnonempty).carrier ∈
      𝓝[Ω.carrier] x
    rw [annularPerronDomain_carrier, Set.diff_eq]
    exact Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds hDcompl_mem)
  have hC_subset_domain : Cdom.carrier ⊆ Ω.carrier := by
    change (annularPerronDomain Ω D hD_subset hnonempty).carrier ⊆ Ω.carrier
    rw [annularPerronDomain_carrier]
    exact Set.diff_subset
  have hC_closure_subset_closed_domain :
      closure Cdom.carrier ⊆ closure Ω.carrier :=
    closure_mono hC_subset_domain
  have hp_not_closure_C : p ∉ closure Cdom.carrier := by
    intro hp_closure
    have hD_mem : D.carrier ∈ 𝓝 p := by
      exact mem_nhds_iff.mpr
        ⟨interior D.carrier, interior_subset, isOpen_interior, hpD_int⟩
    rcases mem_closure_iff_nhds.mp hp_closure D.carrier hD_mem with
      ⟨y, hyD, hyC⟩
    change y ∈ (annularPerronDomain Ω D hD_subset hnonempty).carrier at hyC
    rw [annularPerronDomain_carrier] at hyC
    exact hyC.2 hyD
  have hC_punctured_closure :
      closure Cdom.carrier ⊆ {z : X | z ≠ p} := by
    intro y hy hyeq
    exact hp_not_closure_C (by simpa [hyeq] using hy)
  have hB_tendsto_closure :
      Filter.Tendsto B (𝓝[closure Ω.carrier] x) (𝓝 (B x)) :=
    hB_contΩ x hx_closureΩ
  have hB_tendsto :
      Filter.Tendsto B (𝓝[Ω.carrier] x) (𝓝 0) := by
    simpa [hB_zero] using
      (tendsto_nhdsWithin_mono_left subset_closure hB_tendsto_closure)
  have hB_cont_C : ContinuousOn B (closure Cdom.carrier) :=
    hB_contΩ.mono hC_closure_subset_closed_domain
  have hB_super_C : IsSuperharmonicOnSurface Cdom.carrier B :=
    superharmonicOnSurface_mono hC_subset_domain hB_superΩ
  have hB_nonneg_boundary : ∀ y ∈ Cdom.boundary, 0 ≤ B y := by
    intro y hy
    have hy_frontier : y ∈ frontier Cdom.carrier := by
      simpa [PerronDomain.boundary] using hy
    have hy_closureC : y ∈ closure Cdom.carrier :=
      frontier_subset_closure hy_frontier
    have hy_closureΩ : y ∈ closure Ω.carrier :=
      hC_closure_subset_closed_domain hy_closureC
    by_cases hyx : y = x
    · simp [hyx, hB_zero]
    · exact le_of_lt (hB_posΩ y hy_closureΩ hyx)
  have hK_compact : IsCompact K := by
    exact D.compact.of_isClosed_subset isClosed_frontier (by
      intro y hy
      exact (ClosedCoordinateDisk.isClosed D).frontier_subset hy)
  have hK_subset_domain : K ⊆ Ω.carrier := by
    intro y hyK
    exact hD_subset ((ClosedCoordinateDisk.isClosed D).frontier_subset hyK)
  have hK_punctured : K ⊆ {z : X | z ≠ p} := by
    intro y hyK hyp
    have hpD : p ∈ D.carrier := interior_subset hpD_int
    have hp_not_frontier : p ∉ frontier D.carrier :=
      (mem_interior_iff_notMem_frontier hpD).mp hpD_int
    exact hp_not_frontier (by simpa [hyp] using hyK)
  have hx_notK : x ∉ K := by
    intro hxK
    exact hx_notD ((ClosedCoordinateDisk.isClosed D).frontier_subset hxK)
  rcases
      localPerronBarrier_positive_floor_on_compact
        (PerronDomain.ofSmoothBoundaryDomain Ω)
        (p := x) (N := Set.univ) (K := K) (b := B)
        (by simpa using hB_contΩ)
        (by
          intro y hy hyx
          exact hB_posΩ y (by simpa using hy.1) hyx)
        hK_compact
        (by
          intro y hyK
          exact ⟨subset_closure (hK_subset_domain hyK), trivial⟩)
        hx_notK with
    ⟨δ, hδ, hB_floor_K⟩
  have hboundary_split :
      ∀ y ∈ Cdom.boundary, y ∈ Ω.boundary ∨ y ∈ K := by
    intro y hy
    have hy_frontier :
        y ∈ frontier (Ω.carrier ∩ D.carrierᶜ) := by
      simpa [Cdom, PerronDomain.boundary, annularPerronDomain_carrier,
        Set.diff_eq] using hy
    rcases frontier_inter_subset Ω.carrier D.carrierᶜ hy_frontier with
      hΩpart | hDpart
    · exact Or.inl (by
        simpa [SmoothBoundaryDomain.boundary] using hΩpart.1)
    · exact Or.inr (by
        have hyD_frontier : y ∈ frontier D.carrier := by
          simpa [frontier_compl] using hDpart.2
        simpa [K] using hyD_frontier)
  exact
    ⟨Cdom, K, B, δ, hδ, hC_geometry, hcap_nhds, hC_subset_domain,
      hC_closure_subset_closed_domain, hC_punctured_closure, hB_tendsto,
      hB_cont_C, hB_super_C, hB_nonneg_boundary, hB_floor_K,
      hboundary_split, hK_compact, hK_subset_domain, hK_punctured⟩

/--
%%handwave
name:
  Annular approximants have compactness data
statement:
  In a zero-radius annular Perron approximation system, the approximating
  potentials have pointwise compact range and equicontinuous tails on every
  compact subset of the punctured smooth domain.
proof:
  Choose a base point away from the shrinking disks.  The annular Harnack
  estimates propagate a base-point lower bound for the potentials through
  relatively compact punctured regions, while the maximum principle gives the
  upper bound.  Bounded-harmonic equicontinuity then gives equicontinuous
  tails on compact subsets.
-/
theorem annularPerron_approximationSystem_compactness_data
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S) :
    (∀ K : Set X, IsCompact K → K ⊆ Ω.carrier \ {p} →
      ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ n : ℕ, S.approximant n x ∈ Q) ∧
    (∀ K : Set X, IsCompact K → K ⊆ Ω.carrier \ {p} →
      ∃ N : ℕ,
        EquicontinuousOn
          (fun n : ℕ ↦ fun x : X ↦ S.approximant (N + n) x) K) := by
  classical
  constructor
  · intro K _hK_compact hK_subset x hxK
    have hxU : x ∈ Ω.carrier \ {p} := hK_subset hxK
    rcases annularPerron_approximationSystem_eventual_base_bound
        hnoncompact S hnormalized hxU with
      ⟨A, hA⟩
    have hnonpos :
        ∀ᶠ n : ℕ in Filter.atTop, S.approximant n x ≤ 0 :=
      S.approximant_eventually_nonpositive_at_of_mem_domain_ne_p hxU.1 hxU.2
    exact exists_compact_range_of_eventually_mem_Icc
      (a := fun n : ℕ ↦ S.approximant n x)
      (A := -A) (B := 0)
      (by
        filter_upwards [hA, hnonpos] with n hA_n hnonpos_n
        constructor
        · linarith
        · exact hnonpos_n)
  · intro K hK_compact hK_subset
    by_cases hK_nonempty : K.Nonempty
    · have hpunctured_domain_open : IsOpen (Ω.carrier \ {p}) :=
        Ω.isOpen.sdiff isClosed_singleton
      rcases exists_smoothBoundaryDomain_between_compact_and_open
          (X := X) (K := K) (U := Ω.carrier \ {p})
          hK_compact hK_nonempty hpunctured_domain_open hK_subset with
        ⟨ΩK, hKΩK, hΩK_closure_subset⟩
      let F : ℕ → X → ℝ := fun n x ↦ S.approximant n x
      refine
        harmonicOnSurface_tail_equicontinuousOn_of_eventually_harmonic_locally_eventual_abs_bound
          (U := ΩK.carrier) (K := K) (F := F) hK_compact ?_ ?_
      · exact
          S.approximant_eventually_harmonic_on_relativelyCompact_punctured_region
            ΩK.compact_closure
            (fun x hx ↦ (hΩK_closure_subset hx).1)
            (fun x hx ↦ (hΩK_closure_subset hx).2)
      · intro x hxK
        have hxΩK : x ∈ ΩK.carrier := hKΩK hxK
        rcases S.neg_approximant_eventual_local_harnack_control
            ΩK.isOpen ΩK.compact_closure
            (fun y hy ↦ (hΩK_closure_subset hy).1)
            (fun y hy ↦ (hΩK_closure_subset hy).2)
            hxΩK with
          ⟨N, hN_nhds, hN_subset, C, hC_pos, hcontrol⟩
        have hxU : x ∈ Ω.carrier \ {p} := hK_subset hxK
        rcases annularPerron_approximationSystem_eventual_base_bound
            hnoncompact S hnormalized hxU with
          ⟨A, hA⟩
        refine ⟨N, hN_nhds, hN_subset, max (C * A) 0, ?_⟩
        filter_upwards
          [hcontrol, hA,
           S.approximant_eventually_nonpositive_on_relativelyCompact_punctured_region
            ΩK.compact_closure
            (fun y hy ↦ (hΩK_closure_subset hy).1)
            (fun y hy ↦ (hΩK_closure_subset hy).2)] with
          n hcontrol_n hA_n hnonpos_n y hyN
        have hctrl_y : -F n y ≤ C * (-F n x) := by
          simpa [F] using hcontrol_n y hyN
        have hupper : -F n y ≤ C * A :=
          hctrl_y.trans (mul_le_mul_of_nonneg_left hA_n hC_pos.le)
        have hnonpos_y : F n y ≤ 0 := hnonpos_n y (hN_subset hyN)
        calc
          |F n y| = -F n y := abs_of_nonpos hnonpos_y
          _ ≤ C * A := hupper
          _ ≤ max (C * A) 0 := le_max_left (C * A) 0
    · refine ⟨0, ?_⟩
      intro x hxK
      exact False.elim (hK_nonempty ⟨x, hxK⟩)

/--
%%handwave
name:
  Annular approximants have compact-local convergent subsequences
statement:
  If an annular Perron approximation system has pointwise compact range and
  equicontinuous tails on compact subsets of the punctured smooth domain, then
  a subsequence converges uniformly on every such compact set.  The selected
  limit is defined to vanish on the outer boundary.
proof:
  Work on the open subtype given by the punctured smooth domain.  A compact
  exhaustion and the one-compact Arzelà-Ascoli extraction theorem give a
  diagonal subsequence converging on every exhaustion member.  Transfer the
  limit back to the ambient surface, assigning value zero off the punctured
  domain.
-/
theorem annularPerron_approximationSystem_extracts_compact_convergence_away_pole
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (S : AnnularPerronApproximationSystem X Ω p)
    (hpointwise :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier \ {p} →
        ∀ x ∈ K, ∃ Q : Set ℝ, IsCompact Q ∧
          ∀ n : ℕ, S.approximant n x ∈ Q)
    (heq_tail :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier \ {p} →
        ∃ N : ℕ,
          EquicontinuousOn
            (fun n : ℕ ↦ fun x : X ↦ S.approximant (N + n) x) K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : X → ℝ,
        (∀ K : Set X, IsCompact K → K ⊆ Ω.carrier \ {p} →
          TendstoUniformlyOn
            (fun k : ℕ ↦ fun x : X ↦ S.approximant (φ k) x)
            f Filter.atTop K) ∧
        (∀ x ∈ Ω.boundary, f x = 0) := by
  classical
  let U : Set X := Ω.carrier \ {p}
  let P : Type := U
  have hU_open : IsOpen U := Ω.isOpen.sdiff isClosed_singleton
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  letI : LocallyCompactSpace P := hU_open.locallyCompactSpace
  haveI : SecondCountableTopology P := inferInstance
  haveI : WeaklyLocallyCompactSpace P := inferInstance
  haveI : SigmaCompactSpace P := inferInstance
  let Kp : CompactExhaustion P := CompactExhaustion.choice P
  let Fp : ℕ → P → ℝ := fun n z ↦ S.approximant n z.1
  have hextract :
      ∀ (θ : ℕ → ℕ), StrictMono θ → ∀ m : ℕ,
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∃ f : P → ℝ,
            TendstoUniformlyOn
              (fun n : ℕ ↦ Fp (θ (ψ n))) f Filter.atTop (Kp m) := by
    intro θ hθ m
    let KX : Set X := Subtype.val '' (Kp m)
    have hKp_compact : IsCompact (Kp m) := Kp.isCompact m
    have hKX_compact : IsCompact KX := by
      simpa [KX] using (Subtype.isCompact_iff.mp hKp_compact)
    have hKX_subset : KX ⊆ Ω.carrier \ {p} := by
      rintro x ⟨z, _hz, rfl⟩
      exact z.2
    let Sθ : AnnularPerronApproximationSystem X Ω p := {
      disk := fun n ↦ S.disk (θ n)
      pole_mem_disk := fun n ↦ S.pole_mem_disk (θ n)
      closedRadius_le_one := fun n ↦ S.closedRadius_le_one (θ n)
      disk_subset_domain := fun n ↦ S.disk_subset_domain (θ n)
      annulus_nonempty := fun n ↦ S.annulus_nonempty (θ n)
      approximant := fun n ↦ S.approximant (θ n)
      solves_annular_problem := fun n ↦ S.solves_annular_problem (θ n)
      disks_shrink_to_pole := by
        intro N hN_open hpN
        exact hθ.tendsto_atTop.eventually
          (S.disks_shrink_to_pole hN_open hpN) }
    have hpointwiseθ :
        ∀ x ∈ KX, ∃ Q : Set ℝ, IsCompact Q ∧
          ∀ k : ℕ, Sθ.approximant k x ∈ Q := by
      intro x hxK
      rcases hpointwise KX hKX_compact hKX_subset x hxK with
        ⟨Q, hQ_compact, hQ_mem⟩
      exact ⟨Q, hQ_compact, fun k ↦ by simpa [Sθ] using hQ_mem (θ k)⟩
    have heqθ :
        ∃ N : ℕ,
          EquicontinuousOn
            (fun n : ℕ ↦ fun x : X ↦ Sθ.approximant (N + n) x) KX := by
      rcases heq_tail KX hKX_compact hKX_subset with ⟨Neq, heq₀⟩
      rcases Filter.eventually_atTop.mp
          (hθ.tendsto_atTop.eventually (Filter.eventually_ge_atTop Neq)) with
        ⟨M, hM⟩
      refine ⟨M, ?_⟩
      intro x hxK V hV
      filter_upwards [heq₀ x hxK V hV] with y hy n
      have hθ_ge : Neq ≤ θ (M + n) :=
        hM (M + n) (Nat.le_add_right M n)
      let j : ℕ := θ (M + n) - Neq
      have hidx : Neq + j = θ (M + n) := Nat.add_sub_of_le hθ_ge
      simpa [Sθ, j, hidx] using hy j
    rcases
      Sθ.approximant_subsequence_extracts_uniformLimit_on_compact_away_pole
        hKX_compact hKX_subset hpointwiseθ heqθ with
      ⟨ψ, hψ, fX, hconvX⟩
    refine ⟨ψ, hψ, fun z : P ↦ fX z.1, ?_⟩
    have hconvP :
        TendstoUniformlyOn
          (fun n : ℕ ↦
            (fun x : X ↦ S.approximant (θ (ψ n)) x) ∘
              (fun z : P ↦ (z : X)))
          (fX ∘ fun z : P ↦ (z : X)) Filter.atTop
          ((fun z : P ↦ (z : X)) ⁻¹' KX) :=
      by
        simpa [Sθ] using hconvX.comp (fun z : P ↦ (z : X))
    refine (hconvP.mono ?_).congr ?_
    · intro z hz
      exact ⟨z, hz, rfl⟩
    · filter_upwards with n z hz
      rfl
  rcases
    realFunctions_subsequence_tendstoUniformlyOn_compactExhaustion_of_subsequence_extractions
      Kp (F := Fp) hextract with
    ⟨φ, hφ, fP, hconvP⟩
  let f : X → ℝ := fun x ↦ if hx : x ∈ Ω.carrier \ {p} then fP ⟨x, hx⟩ else 0
  refine ⟨φ, hφ, f, ?_, ?_⟩
  · intro K hK_compact hK_subset
    let KP : Set P := {z : P | z.1 ∈ K}
    have hKP_compact : IsCompact KP := by
      rw [Subtype.isCompact_iff]
      have h_image : Subtype.val '' KP = K := by
        ext x
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact hz
        · intro hxK
          exact ⟨⟨x, hK_subset hxK⟩, hxK, rfl⟩
      simpa [h_image] using hK_compact
    rcases Kp.exists_superset_of_isCompact hKP_compact with ⟨m, hKPm⟩
    have hconvKP : TendstoUniformlyOn
        (fun n : ℕ ↦ Fp (φ n)) fP Filter.atTop KP :=
      (hconvP m).mono hKPm
    intro V hV
    filter_upwards [hconvKP V hV] with n hn x hxK
    have hxU : x ∈ Ω.carrier \ {p} := hK_subset hxK
    have hxU' : x ∈ Ω.carrier ∧ ¬x = p := by
      simpa using hxU
    have hzK : (⟨x, hxU⟩ : P) ∈ KP := hxK
    simpa [Fp, f, hxU'] using hn ⟨x, hxU⟩ hzK
  · intro x hx_boundary
    have hx_frontier : x ∈ frontier Ω.carrier := by
      simpa [SmoothBoundaryDomain.boundary] using hx_boundary
    have hx_not_carrier : x ∉ Ω.carrier := by
      intro hxΩ
      have hx_empty : x ∈ Ω.carrier ∩ frontier Ω.carrier :=
        ⟨hxΩ, hx_frontier⟩
      simp [Ω.isOpen.inter_frontier_eq] at hx_empty
    have hx_not_U : ¬ x ∈ Ω.carrier \ {p} := fun hxU ↦ hx_not_carrier hxU.1
    have hx_not_U' : ¬(x ∈ Ω.carrier ∧ ¬x = p) := by
      intro hxU
      exact hx_not_carrier hxU.1
    simp [f, hx_not_U']

/--
%%handwave
name:
  Compact lower bounds imply uniform outer-boundary lower estimates
statement:
  Suppose annular Perron approximants have eventual uniform lower bounds on
  every compact artificial boundary lying in a preconnected relatively
  compact punctured region.  Then at an outer smooth boundary point different
  from the pole, the annular Perron solutions are eventually greater than
  \(-\varepsilon\) on one fixed interior neighborhood of that boundary point.
proof:
  Choose a local smooth Perron barrier at the outer boundary point and a
  compactly contained cap inside the barrier neighborhood whose artificial
  boundary is away from the pole.  The assumed compact lower bound controls
  the annular solutions on the artificial boundary.  The outer boundary value
  is zero.  Comparing with a calibrated multiple of the local barrier on the
  cap gives the desired lower estimate, uniformly for all sufficiently small
  deleted disks.
-/
theorem annularPerron_approximationSystem_approximants_eventually_gt_outer_boundary_sub_of_compact_lower_bounds
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (S : AnnularPerronApproximationSystem X Ω p)
    {x : X} (hx_boundary : x ∈ Ω.boundary) (hxp : x ≠ p)
    {ε : ℝ} (hε : 0 < ε)
    (hcompactLower :
      ∀ {K : Set X},
        IsCompact K →
          K ⊆ Ω.carrier →
            K ⊆ {z : X | z ≠ p} →
              ∃ M : ℝ,
                ∀ᶠ n : ℕ in Filter.atTop,
                  ∀ y ∈ K, -M ≤ S.approximant n y) :
    ∀ᶠ y in 𝓝[Ω.carrier] x,
      ∀ᶠ n : ℕ in Filter.atTop, -ε < S.approximant n y := by
  have hp_domain : p ∈ Ω.carrier :=
    S.disk_subset_domain 0 (S.pole_mem_disk 0)
  rcases
    smoothBoundaryDomain_exists_punctured_interior_barrier_cap_data
      (Ω := Ω) (p := p) hp_domain hx_boundary hxp with
    ⟨Cdom, K, B, δ, hδ, hC_geometry, hcap_nhds,
      hC_subset_domain, hC_closure_subset_closed_domain,
      hC_punctured_closure, hB_tendsto, hB_cont, hB_super,
      hB_nonneg_boundary, hB_floor_K, hboundary_split, hK_compact,
      hK_subset_domain, hK_punctured⟩
  rcases hcompactLower hK_compact hK_subset_domain hK_punctured with
    ⟨M, hM⟩
  have hF_cont :
      ∀ᶠ n : ℕ in Filter.atTop,
        ContinuousOn (S.approximant n) (closure Cdom.carrier) :=
    S.approximant_eventually_continuousOn_closure_of_relativelyCompact_punctured_region
      Cdom.compact_closure hC_closure_subset_closed_domain
      hC_punctured_closure
  have hF_harmonic :
      ∀ᶠ n : ℕ in Filter.atTop,
        IsHarmonicOnSurface Cdom.carrier (S.approximant n) :=
    S.approximant_eventually_harmonic_on_relativelyCompact_punctured_subset_domain
      Cdom.compact_closure hC_subset_domain hC_punctured_closure
  have hF_outer_zero :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ y ∈ Ω.boundary, S.approximant n y = 0 :=
    Filter.Eventually.of_forall fun n y hy ↦
      S.approximant_eq_zero_on_outer_boundary n hy
  exact
    cap_barrier_eventually_gt_boundary_sub_of_artificial_boundary_lower_bound
      (Ω := Ω) (Cdom := Cdom) (x := x) (K := K) (B := B)
      (F := S.approximant) (ε := ε) (M := M) (δ := δ)
      hC_geometry hε hδ hcap_nhds hB_tendsto hB_cont hB_super
      hB_nonneg_boundary hB_floor_K hboundary_split hF_cont hF_harmonic
      hF_outer_zero hM

/--
%%handwave
name:
  Annular approximants have uniform lower estimates at the outer boundary
statement:
  In a zero-radius annular Perron approximation system, fix a point of the
  outer smooth boundary different from the pole.  For every positive
  \(\varepsilon\), all sufficiently small deleted disks have annular Perron
  solutions greater than \(-\varepsilon\) throughout a single neighborhood of
  that boundary point inside the smooth domain.
proof:
  Choose a local smooth Perron barrier at the outer boundary point and shrink
  its neighborhood so that the deleted disks eventually lie outside it.  On
  the artificial inner boundary of this local cap, compact Harnack estimates
  give a uniform finite lower bound for the annular solutions.  The outer
  boundary value is zero.  A local barrier comparison on the cap then gives
  the uniform lower estimate near the boundary point.
-/
theorem annularPerron_approximationSystem_approximants_eventually_gt_outer_boundary_sub
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    {x : X} (hx_boundary : x ∈ Ω.boundary) (hxp : x ≠ p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝[Ω.carrier] x,
      ∀ᶠ n : ℕ in Filter.atTop, -ε < S.approximant n y := by
  exact
    annularPerron_approximationSystem_approximants_eventually_gt_outer_boundary_sub_of_compact_lower_bounds
      S hx_boundary hxp hε
      (fun {K} hK_compact hK_subset_domain hK_punctured ↦
        approximant_eventual_uniform_lower_bound_on_compact_punctured_domain
          hnoncompact S hnormalized hK_compact hK_subset_domain hK_punctured)

/--
%%handwave
name:
  Annular compact-local limits have lower boundary estimates
statement:
  Let zero-radius annular Perron solutions converge locally uniformly away
  from the pole to a function \(f\).  At any smooth outer boundary point
  different from the pole, \(f\) is eventually greater than
  \(-\varepsilon\) when approached from inside the domain.
proof:
  Use the uniform approximant lower estimate with \(\varepsilon/2\).  For
  each point in the resulting punctured neighborhood, compact convergence on
  the singleton passes the eventual lower bound to the limit, giving
  \(f\ge-\varepsilon/2>-\varepsilon\).
-/
theorem annularPerron_approximationSystem_limit_eventually_gt_outer_boundary_sub_of_compact_convergence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier \ {p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ S.approximant (φ k) x)
          f Filter.atTop K)
    {x : X} (hx_boundary : x ∈ Ω.boundary) (hxp : x ≠ p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝[Ω.carrier] x, -ε < f y := by
  have hε_half : 0 < ε / 2 := by linarith
  have happ :
      ∀ᶠ y in 𝓝[Ω.carrier] x,
        ∀ᶠ n : ℕ in Filter.atTop, -(ε / 2) < S.approximant n y :=
    annularPerron_approximationSystem_approximants_eventually_gt_outer_boundary_sub
      hnoncompact S hnormalized hx_boundary hxp hε_half
  have hnotp_open : IsOpen ({y : X | y ≠ p}) := by
    simpa using (isOpen_ne (x := p) : IsOpen {y : X | y ≠ p})
  have hnotp_nhds : {y : X | y ≠ p} ∈ 𝓝 x :=
    hnotp_open.mem_nhds hxp
  filter_upwards
    [happ, mem_nhdsWithin_of_mem_nhds hnotp_nhds, self_mem_nhdsWithin] with
    y hy_lower hy_ne hyΩ
  have hyU : y ∈ Ω.carrier \ {p} := ⟨hyΩ, by simpa using hy_ne⟩
  have hconv_single :
      TendstoUniformlyOn
        (fun k : ℕ ↦ fun z : X ↦ S.approximant (φ k) z)
        f Filter.atTop ({y} : Set X) :=
    hconv ({y} : Set X) (isCompact_singleton (x := y))
      (by
        intro z hz
        simpa [Set.mem_singleton_iff.mp hz] using hyU)
  have hge_subseq :
      ∀ᶠ k : ℕ in Filter.atTop, -(ε / 2) ≤ S.approximant (φ k) y :=
    hφ.tendsto_atTop.eventually
      (hy_lower.mono fun n hn ↦ le_of_lt hn)
  have hge_limit : -(ε / 2) ≤ f y :=
    tendstoUniformlyOn_pointwise_ge_of_eventually_ge
      (K := ({y} : Set X))
      (F := fun k : ℕ ↦ fun z : X ↦ S.approximant (φ k) z)
      (f := f) (x := y) (a := -(ε / 2))
      (by simp) hconv_single hge_subseq
  linarith

/--
%%handwave
name:
  Annular compact-local limits are continuous at the outer boundary
statement:
  Let zero-radius annular Perron solutions converge locally uniformly away
  from the pole to a function \(f\), and suppose \(f\) takes the zero outer
  boundary value.  At any smooth outer boundary point different from the
  pole, \(f\) is continuous when approached through the punctured closed
  domain.
proof:
  The lower boundary-barrier estimate gives \(f>-\varepsilon\) from inside
  the domain.  Nonpositivity gives the matching upper estimate \(f\le0\), and
  the function is identically zero on the outer boundary.  Since the closed
  domain is the union of the open domain and its boundary, these two
  one-sided estimates give continuity at the boundary point.
-/
theorem annularPerron_approximationSystem_limit_continuousWithinAt_punctured_closure_at_boundary_of_compact_convergence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier \ {p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ S.approximant (φ k) x)
          f Filter.atTop K)
    (hboundary : ∀ x ∈ Ω.boundary, f x = 0)
    {x : X} (hx_boundary : x ∈ Ω.boundary) (hxp : x ≠ p) :
    ContinuousWithinAt f (closure Ω.carrier \ {p}) x := by
  have hnonpos :
      ∀ y ∈ Ω.carrier \ {p}, f y ≤ 0 :=
    S.approximant_subsequence_limit_nonpositive_on_punctured_domain_of_compact_convergence
      hφ hconv
  have hinside :
      Filter.Tendsto f (𝓝[Ω.carrier \ {p}] x) (𝓝 0) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      have hε : 0 < -a := by linarith
      have hlower :
          ∀ᶠ y in 𝓝[Ω.carrier] x, -(-a) < f y :=
        annularPerron_approximationSystem_limit_eventually_gt_outer_boundary_sub_of_compact_convergence
          hnoncompact S hnormalized hφ hconv hx_boundary hxp hε
      have hlower' :
          ∀ᶠ y in 𝓝[Ω.carrier \ {p}] x, -(-a) < f y :=
        (nhdsWithin_mono x (Set.diff_subset : Ω.carrier \ {p} ⊆ Ω.carrier))
          hlower
      filter_upwards [hlower'] with y hy
      linarith
    · intro a ha
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact lt_of_le_of_lt (hnonpos y hy) ha
  have hboundary_side :
      Filter.Tendsto f (𝓝[Ω.boundary \ {p}] x) (𝓝 0) := by
    have heq : f =ᶠ[𝓝[Ω.boundary \ {p}] x] fun _ : X ↦ (0 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hboundary y hy.1
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  have hclosed_union :
      closure Ω.carrier \ {p} =
        (Ω.carrier \ {p}) ∪ (Ω.boundary \ {p}) := by
    calc
      closure Ω.carrier \ {p}
          = (Ω.carrier ∪ frontier Ω.carrier) \ {p} := by
              rw [closure_eq_self_union_frontier]
      _ = (Ω.carrier \ {p}) ∪ (frontier Ω.carrier \ {p}) := by
              ext y
              constructor
              · rintro ⟨hy, hyp⟩
                rcases hy with hyΩ | hy_frontier
                · exact Or.inl ⟨hyΩ, hyp⟩
                · exact Or.inr ⟨hy_frontier, hyp⟩
              · rintro (⟨hyΩ, hyp⟩ | ⟨hy_frontier, hyp⟩)
                · exact ⟨Or.inl hyΩ, hyp⟩
                · exact ⟨Or.inr hy_frontier, hyp⟩
      _ = (Ω.carrier \ {p}) ∪ (Ω.boundary \ {p}) := by
              simp [SmoothBoundaryDomain.boundary]
  change Filter.Tendsto f (𝓝[closure Ω.carrier \ {p}] x) (𝓝 (f x))
  rw [hboundary x hx_boundary]
  rw [hclosed_union, nhdsWithin_union]
  exact hinside.sup hboundary_side

/--
%%handwave
name:
  Annular compact-local limits are continuous on the punctured closed domain
statement:
  Let zero-radius annular Perron solutions converge locally uniformly away
  from the pole to a function \(f\), and suppose \(f\) takes the zero outer
  boundary value.  Then \(f\) is continuous on the closure of the smooth
  domain after removing the pole.
proof:
  On the punctured interior, the compact-local limit is harmonic and hence
  continuous.  At outer boundary points, apply the boundary-continuity
  theorem obtained from smooth Perron barriers.
-/
theorem annularPerron_approximationSystem_limit_continuousOn_punctured_closure_of_compact_convergence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier \ {p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ S.approximant (φ k) x)
          f Filter.atTop K)
    (hboundary : ∀ x ∈ Ω.boundary, f x = 0) :
    ContinuousOn f (closure Ω.carrier \ {p}) := by
  have hpunctured_open : IsOpen (Ω.carrier \ {p}) :=
    Ω.isOpen.sdiff isClosed_singleton
  have hharm :
      IsHarmonicOnSurface (Ω.carrier \ {p}) f :=
    S.approximant_subsequence_limit_harmonic_away_pole_of_compact_convergence
      hφ hconv
  have hcont_punctured : ContinuousOn f (Ω.carrier \ {p}) :=
    harmonicOnSurface_continuousOn hpunctured_open hharm
  intro x hx
  by_cases hxΩ : x ∈ Ω.carrier
  · have hxU : x ∈ Ω.carrier \ {p} := ⟨hxΩ, hx.2⟩
    have hxU_nhds : Ω.carrier \ {p} ∈ 𝓝 x :=
      hpunctured_open.mem_nhds hxU
    exact (hcont_punctured.continuousAt hxU_nhds).continuousWithinAt
  · have hx_frontier : x ∈ frontier Ω.carrier := by
      rw [Ω.isOpen.frontier_eq]
      exact ⟨hx.1, hxΩ⟩
    have hx_boundary : x ∈ Ω.boundary := by
      simpa [SmoothBoundaryDomain.boundary] using hx_frontier
    exact
      annularPerron_approximationSystem_limit_continuousWithinAt_punctured_closure_at_boundary_of_compact_convergence
        hnoncompact S hnormalized hφ hconv hboundary hx_boundary hx.2

/--
%%handwave
name:
  Outer circle bounds control annular logarithmic remainders, core
statement:
  Fix a coordinate circle around the pole whose closed disk lies in the
  surface coordinate and in the smooth domain.  If the logarithmically
  corrected annular Perron solutions are eventually bounded on this outer
  circle, then, after perhaps enlarging the bound, they are eventually bounded
  throughout the part of the punctured coordinate disk lying in the moving
  annular domains.
proof:
  Compare the annular Perron solution with the coordinate logarithm on the
  region between the moving deleted disk and the fixed coordinate circle.  On
  the fixed outer circle the bound is assumed.  On the inner boundary, the
  prescribed logarithmic value differs from the chosen coordinate logarithm by
  a bounded coordinate-transition term for all sufficiently small deleted
  disks.  The componentwise maximum principle then propagates the two-sided
  estimate across the annular region.
-/
theorem annularPerron_approximationSystem_logarithmic_remainder_from_frontier_bound_core
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    (χ : PointedSurfaceCoordinate X p) {R M₀ : ℝ}
    (hR_pos : 0 < R)
    (hclosed_target : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target)
    (hclosed_domain :
      Metric.closedBall (χ.chart p) R ⊆ χ.chart.symm ⁻¹' Ω.carrier)
    (hfront :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ z ∈ frontier (Metric.ball (χ.chart p) R),
          ‖S.approximant n (χ.chart.symm z) -
            Real.log ‖z - χ.chart p‖‖ ≤ M₀) :
    ∃ M : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x : X, x ∈ χ.chart.source → x ≠ p →
          ‖χ.chart x - χ.chart p‖ < R →
          x ∈
            (annularPerronDomain Ω (S.disk n)
              (S.disk_subset_domain n) (S.annulus_nonempty n)).carrier →
            ‖S.approximant n x -
              Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M := by
  rcases
      S.approximant_logarithmic_remainder_bound_on_coordinateBall_annular_frontier
        hnormalized χ hR_pos hclosed_target hclosed_domain hfront with
    ⟨M, hMfront⟩
  refine ⟨M, ?_⟩
  filter_upwards
    [hMfront,
      S.disk_eventually_pole_mem_interior_of_logarithmicBoundaryNormalization
        hnormalized χ] with n hfront_n hp_interior x hx_source hx_ne_p hx_norm_lt hx_annular
  let U₀ : Set X :=
    χ.chart.source ∩ χ.chart ⁻¹' Metric.ball (χ.chart p) R
  let A : PerronDomain X :=
    annularPerronDomain Ω (S.disk n)
      (S.disk_subset_domain n) (S.annulus_nonempty n)
  let U : Set X := U₀ ∩ A.carrier
  let g : X → ℝ :=
    fun y : X ↦ S.approximant n y -
      Real.log ‖χ.chart y - χ.chart p‖
  have hxU : x ∈ U := by
    refine ⟨?_, ?_⟩
    · exact ⟨hx_source, by simpa [Metric.mem_ball, dist_eq_norm] using hx_norm_lt⟩
    · simpa [A] using hx_annular
  have hU_geometry : HasComponentwiseMaximumPrincipleGeometry U := by
    simpa [U, U₀, A] using
      S.coordinateBall_inter_annularDomain_hasComponentwiseMaximumPrincipleGeometry
        χ hclosed_target n
  have hU_source : U ⊆ χ.chart.source := by
    intro y hy
    exact hy.1.1
  have hU_avoid : ∀ y ∈ U, χ.chart y ≠ χ.chart p := by
    intro y hy hchart
    have hy_eq_p : y = p :=
      χ.chart.injOn hy.1.1 χ.base_mem_source hchart
    have hyA : y ∈ A.carrier := hy.2
    have hy_annular' : y ∈ Ω.carrier \ (S.disk n).carrier := by
      simpa [A, annularPerronDomain_carrier] using hyA
    exact hy_annular'.2 (by simpa [hy_eq_p] using S.pole_mem_disk n)
  have happ_harm :
      IsHarmonicOnSurface U (S.approximant n) := by
    refine harmonicOnSurface_mono ?_ (S.solves_annular_problem n).1
    intro y hy
    simpa [A] using hy.2
  have hlog_harm :
      IsHarmonicOnSurface U
        (fun y : X ↦ Real.log ‖χ.chart y - χ.chart p‖) :=
    coordinateLogDistance_harmonicOnSurface χ.chart χ.chart_mem_atlas
      hU_source hU_avoid
  have hg_harm :
      IsHarmonicOnSurface U g := by
    simpa [g] using harmonicOnSurface_sub happ_harm hlog_harm
  have happ_cont : ContinuousOn (S.approximant n) (closure U) := by
    have hclosure_subset_A :
        closure U ⊆ closure A.carrier :=
      closure_mono (by
        intro y hy
        exact hy.2)
    exact (S.solves_annular_problem n).2.1.mono (by
      simpa [A] using hclosure_subset_A)
  have hclosure_U_subset_U₀ : closure U ⊆ closure U₀ :=
    closure_mono (by
      intro y hy
      exact hy.1)
  have hclosure_source_closed :
      closure U ⊆
        χ.chart.source ∩ χ.chart ⁻¹'
          Metric.closedBall (χ.chart p) R := by
    intro y hy
    exact
      openPartialHomeomorph_coordinateBall_closure_subset_source_inter_closedBall
        χ.chart hclosed_target (hclosure_U_subset_U₀ hy)
  have hU_subset_compl_disk : U ⊆ (S.disk n).carrierᶜ := by
    intro y hy hy_disk
    have hy_annular' : y ∈ Ω.carrier \ (S.disk n).carrier := by
      simpa [A, annularPerronDomain_carrier] using hy.2
    exact hy_annular'.2 hy_disk
  have hclosure_U_ne_p : closure U ⊆ {y : X | y ≠ p} := by
    have hU_subset_compl_interior :
        U ⊆ (interior (S.disk n).carrier)ᶜ := by
      intro y hy hy_interior
      exact hU_subset_compl_disk hy (interior_subset hy_interior)
    have hclosure_subset_compl_interior :
        closure U ⊆ (interior (S.disk n).carrier)ᶜ :=
      closure_minimal hU_subset_compl_interior
        (isOpen_interior.isClosed_compl)
    intro y hy hy_eq_p
    exact hclosure_subset_compl_interior hy (by simpa [hy_eq_p] using hp_interior)
  have hchart_cont : ContinuousOn χ.chart (closure U) :=
    χ.chart.continuousOn.mono (fun y hy ↦ (hclosure_source_closed hy).1)
  have hdist_cont :
      ContinuousOn
        (fun y : X ↦ ‖χ.chart y - χ.chart p‖) (closure U) :=
    (hchart_cont.sub continuousOn_const).norm
  have hdist_ne :
      ∀ y ∈ closure U, ‖χ.chart y - χ.chart p‖ ≠ 0 := by
    intro y hy hzero
    have hsub_zero : χ.chart y - χ.chart p = 0 := norm_eq_zero.mp hzero
    have hchart_eq : χ.chart y = χ.chart p := sub_eq_zero.mp hsub_zero
    exact hclosure_U_ne_p hy
      (χ.chart.injOn (hclosure_source_closed hy).1 χ.base_mem_source hchart_eq)
  have hlog_cont :
      ContinuousOn
        (fun y : X ↦ Real.log ‖χ.chart y - χ.chart p‖) (closure U) :=
    hdist_cont.log hdist_ne
  have hg_cont : ContinuousOn g (closure U) := by
    simpa [g] using happ_cont.sub hlog_cont
  have hfrontier_bound : ∀ y ∈ frontier U, ‖g y‖ ≤ M := by
    intro y hy
    simpa [g, U, U₀, A] using hfront_n y (by simpa [U, U₀, A] using hy)
  have hbound :
      ∀ y ∈ U, ‖g y‖ ≤ M :=
    harmonicOnSurface_norm_le_of_frontier_norm_le_componentwise
      hU_geometry hg_harm hg_cont hfrontier_bound
  simpa [g] using hbound x hxU

/--
%%handwave
name:
  Annular logarithmic remainders are bounded on a fixed coordinate ball
statement:
  For an annular Perron approximation system and a coordinate at the pole,
  there is a smaller coordinate ball around the pole, compactly contained in
  the chart, and a constant \(M\) such that all sufficiently small deleted
  disks have annular solutions whose difference from the coordinate logarithm
  has absolute value at most \(M\) throughout the part of the punctured ball
  lying in the annular domain.
proof:
  Choose a compact coordinate ball around the pole lying in the smooth domain.
  For all sufficiently small deleted disks, compare the annular Perron
  solution with the coordinate logarithm on the annulus between the deleted
  disk and the fixed coordinate circle.  The inner boundary values agree up
  to the coordinate-radius normalization, while the outer circle is controlled
  by compact Harnack bounds and the maximum principle propagates the two-sided
  estimate through the annular part of the punctured ball.
-/
theorem annularPerron_approximationSystem_logarithmic_remainder_eventual_bound_on_pointed_coordinate_ball
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    (χ : PointedSurfaceCoordinate X p) :
    ∃ R M : ℝ, 0 < R ∧
      Metric.closedBall (χ.chart p) R ⊆ χ.chart.target ∧
      (∀ x : X, x ∈ χ.chart.source →
        ‖χ.chart x - χ.chart p‖ < R → x ∈ Ω.carrier) ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x : X, x ∈ χ.chart.source → x ≠ p →
          ‖χ.chart x - χ.chart p‖ < R →
          x ∈
            (annularPerronDomain Ω (S.disk n)
              (S.disk_subset_domain n) (S.annulus_nonempty n)).carrier →
            ‖S.approximant n x -
              Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M := by
  classical
  let c : ℂ := χ.chart p
  have hpΩ : p ∈ Ω.carrier :=
    S.disk_subset_domain 0 (S.pole_mem_disk 0)
  have hc_target : c ∈ χ.chart.target := by
    dsimp [c]
    exact χ.chart.map_source χ.base_mem_source
  have htarget_nhds : χ.chart.target ∈ 𝓝 c :=
    χ.chart.open_target.mem_nhds hc_target
  have hdomain_nhds : Ω.carrier ∈ 𝓝 p :=
    Ω.isOpen.mem_nhds hpΩ
  have hsymm_c : χ.chart.symm c = p := by
    simpa [c] using χ.chart.left_inv χ.base_mem_source
  have hdomain_at_symm : Ω.carrier ∈ 𝓝 (χ.chart.symm c) := by
    simpa [hsymm_c] using hdomain_nhds
  have hdomain_map :
      Ω.carrier ∈ Filter.map χ.chart.symm (𝓝 c) :=
    χ.chart.continuousAt_symm hc_target hdomain_at_symm
  have hdomain_pre :
      χ.chart.symm ⁻¹' Ω.carrier ∈ 𝓝 c := by
    simpa [Filter.mem_map] using hdomain_map
  rcases Metric.mem_nhds_iff.mp
      (Filter.inter_mem htarget_nhds hdomain_pre) with
    ⟨R₀, hR₀_pos, hball_target_domain⟩
  let R : ℝ := R₀ / 2
  have hR_pos : 0 < R := by
    dsimp [R]
    linarith
  have hR_lt_R₀ : R < R₀ := by
    dsimp [R]
    linarith
  have hclosed_target_domain :
      Metric.closedBall c R ⊆
        χ.chart.target ∩ χ.chart.symm ⁻¹' Ω.carrier :=
    (Metric.closedBall_subset_ball hR_lt_R₀).trans hball_target_domain
  have hclosed_target :
      Metric.closedBall (χ.chart p) R ⊆ χ.chart.target := by
    intro z hz
    exact (hclosed_target_domain (by simpa [c] using hz)).1
  have hclosed_domain :
      Metric.closedBall (χ.chart p) R ⊆
        χ.chart.symm ⁻¹' Ω.carrier := by
    intro z hz
    exact (hclosed_target_domain (by simpa [c] using hz)).2
  have hball_domain :
      ∀ x : X, x ∈ χ.chart.source →
        ‖χ.chart x - χ.chart p‖ < R → x ∈ Ω.carrier := by
    intro x hxsource hxR
    have hx_closed : χ.chart x ∈ Metric.closedBall (χ.chart p) R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_lt hxR
    have hsymm_domain : χ.chart.symm (χ.chart x) ∈ Ω.carrier :=
      hclosed_domain hx_closed
    simpa [χ.chart.left_inv hxsource] using hsymm_domain
  let K : Set X := χ.chart.symm '' Metric.sphere c R
  have hsphere_target : Metric.sphere c R ⊆ χ.chart.target := by
    intro z hz
    have hz_closed : z ∈ Metric.closedBall c R :=
      Metric.sphere_subset_closedBall hz
    exact (hclosed_target_domain hz_closed).1
  have hK_compact : IsCompact K :=
    (isCompact_sphere c R).image_of_continuousOn
      (χ.chart.continuousOn_symm.mono hsphere_target)
  have hK_subset_domain : K ⊆ Ω.carrier := by
    intro x hxK
    rcases hxK with ⟨z, hz_sphere, rfl⟩
    have hz_closed : z ∈ Metric.closedBall c R :=
      Metric.sphere_subset_closedBall hz_sphere
    exact (hclosed_target_domain hz_closed).2
  have hK_punctured : K ⊆ {x : X | x ≠ p} := by
    intro x hxK
    rcases hxK with ⟨z, hz_sphere, rfl⟩
    have hz_target : z ∈ χ.chart.target := hsphere_target hz_sphere
    have hzc : z ≠ c := Metric.ne_of_mem_sphere hz_sphere hR_pos.ne'
    intro hsymm_eq
    have hz_eq_c : z = c := by
      calc
        z = χ.chart (χ.chart.symm z) := (χ.chart.right_inv hz_target).symm
        _ = χ.chart p := by rw [hsymm_eq]
        _ = c := rfl
    exact hzc hz_eq_c
  rcases approximant_eventual_uniform_lower_bound_on_compact_punctured_domain
      hnoncompact S hnormalized hK_compact hK_subset_domain hK_punctured with
    ⟨M₁, hM₁⟩
  have hp_not_K : p ∉ K := by
    intro hpK
    exact (hK_punctured hpK) rfl
  have hdisks_avoid_K :
      ∀ᶠ n : ℕ in Filter.atTop, (S.disk n).carrier ⊆ Kᶜ :=
    S.disks_shrink_to_pole hK_compact.isClosed.isOpen_compl hp_not_K
  let Mfront : ℝ := max M₁ 0 + ‖Real.log R‖
  have hfront :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ z ∈ frontier (Metric.ball (χ.chart p) R),
          ‖S.approximant n (χ.chart.symm z) -
            Real.log ‖z - χ.chart p‖‖ ≤ Mfront := by
    filter_upwards [hM₁, hdisks_avoid_K] with n hlower havoid z hz
    have hz_sphere : z ∈ Metric.sphere c R := by
      simpa [c, frontier_ball c hR_pos.ne'] using hz
    have hxK : χ.chart.symm z ∈ K := ⟨z, hz_sphere, rfl⟩
    have hlower_y : -M₁ ≤ S.approximant n (χ.chart.symm z) :=
      hlower (χ.chart.symm z) hxK
    have hdomain_y :
        χ.chart.symm z ∈
          (annularPerronDomain Ω (S.disk n)
            (S.disk_subset_domain n) (S.annulus_nonempty n)).carrier := by
      rw [annularPerronDomain_carrier]
      refine ⟨hK_subset_domain hxK, ?_⟩
      intro hz_disk
      exact havoid hz_disk hxK
    have hupper_y : S.approximant n (χ.chart.symm z) ≤ 0 :=
      S.approximant_nonpositive n (χ.chart.symm z) hdomain_y
    have hnorm_y :
        ‖S.approximant n (χ.chart.symm z)‖ ≤ max M₁ 0 := by
      have hleft : -max M₁ 0 ≤ S.approximant n (χ.chart.symm z) := by
        have hM_le : M₁ ≤ max M₁ 0 := le_max_left M₁ 0
        exact (neg_le_neg hM_le).trans hlower_y
      have hright : S.approximant n (χ.chart.symm z) ≤ max M₁ 0 :=
        hupper_y.trans (le_max_right M₁ 0)
      simpa [Real.norm_eq_abs] using abs_le.mpr ⟨hleft, hright⟩
    have hnorm_eq : ‖z - χ.chart p‖ = R := by
      simpa [c] using hz_sphere
    calc
      ‖S.approximant n (χ.chart.symm z) -
          Real.log ‖z - χ.chart p‖‖
          = ‖S.approximant n (χ.chart.symm z) - Real.log R‖ := by
              rw [hnorm_eq]
      _ ≤ ‖S.approximant n (χ.chart.symm z)‖ + ‖Real.log R‖ :=
          norm_sub_le _ _
      _ ≤ Mfront := by
          simpa [Mfront, add_comm, add_left_comm, add_assoc] using
            add_le_add_right hnorm_y ‖Real.log R‖
  rcases
    annularPerron_approximationSystem_logarithmic_remainder_from_frontier_bound_core
      S hnormalized χ hR_pos hclosed_target hclosed_domain hfront with
    ⟨M, hM⟩
  exact ⟨R, M, hR_pos, hclosed_target, hball_domain, hM⟩

/--
%%handwave
name:
  Annular logarithmic remainders are uniformly bounded before taking
  subsequences
statement:
  For an annular Perron approximation system, in every coordinate at the
  pole the difference between each annular solution and the coordinate
  logarithm is bounded by one constant near the pole, uniformly for all
  sufficiently late approximants.
proof:
  On the shrinking coordinate annuli, the inner boundary data is the
  logarithm of the deleted radius.  Comparing with the coordinate logarithm
  and applying annular maximum-principle barriers gives a two-sided bound for
  the corrected remainders on a fixed punctured coordinate neighborhood.
-/
theorem annularPerron_approximationSystem_logarithmic_remainder_eventual_local_bound_full
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S) :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ M : ℝ,
        ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
          ∀ᶠ n : ℕ in Filter.atTop,
            ‖S.approximant n x -
              Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M := by
  intro χ
  rcases
    annularPerron_approximationSystem_logarithmic_remainder_eventual_bound_on_pointed_coordinate_ball
      hnoncompact S hnormalized χ with
    ⟨R, M, hR_pos, _hclosed, _hball_domain, hbound⟩
  refine ⟨M, ?_⟩
  filter_upwards
    [pointedCoordinate_eventually_mem_inner_ball X χ χ hR_pos,
      self_mem_nhdsWithin] with x hxsmall hxpunct
  have hxΩ : x ∈ Ω.carrier := _hball_domain x hxsmall.1 hxsmall.2
  have hxdomain :
      ∀ᶠ n : ℕ in Filter.atTop,
        x ∈
          (annularPerronDomain Ω (S.disk n)
            (S.disk_subset_domain n) (S.annulus_nonempty n)).carrier := by
    filter_upwards [S.disk_eventually_avoids_point hxpunct.2] with n hx_not_disk
    rw [annularPerronDomain_carrier]
    exact ⟨hxΩ, hx_not_disk⟩
  filter_upwards [hbound, hxdomain] with n hn hxn
  exact hn x hxsmall.1 hxpunct.2 hxsmall.2 hxn

/--
%%handwave
name:
  Annular logarithmic remainders are uniformly bounded before taking limits
statement:
  For an annular Perron approximation system, in every coordinate at the
  pole the difference between each annular solution and the coordinate
  logarithm is bounded by one constant near the pole, uniformly for all
  sufficiently late members of any selected subsequence.
proof:
  Apply the full-sequence annular remainder estimate, then compose its
  eventual tail with the selected strictly increasing subsequence.
-/
theorem annularPerron_approximationSystem_logarithmic_remainder_eventual_local_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ M : ℝ,
        ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
          ∀ᶠ k : ℕ in Filter.atTop,
            ‖S.approximant (φ k) x -
              Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M := by
  intro χ
  rcases annularPerron_approximationSystem_logarithmic_remainder_eventual_local_bound_full
      hnoncompact S hnormalized χ with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  filter_upwards [hM] with x hxM
  exact hφ.tendsto_atTop.eventually hxM

/--
%%handwave
name:
  Annular logarithmic remainders stay bounded after compact convergence
statement:
  A compact-local limit of annular Perron approximants has locally bounded
  logarithmically corrected remainders near the pole in every coordinate.
proof:
  The annular remainder bound holds uniformly for all late approximants.  At
  each nearby punctured point, compact-local convergence on the singleton
  passes that absolute bound to the limiting value.
-/
theorem annularPerron_approximationSystem_limit_logarithmic_remainder_locally_bounded_of_compact_convergence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier \ {p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ S.approximant (φ k) x)
          f Filter.atTop K) :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ M : ℝ,
        ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
          ‖f x - Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M := by
  intro χ
  rcases
    annularPerron_approximationSystem_logarithmic_remainder_eventual_local_bound
      hnoncompact S hnormalized hφ χ with
    ⟨M, hM⟩
  have hpΩ : p ∈ Ω.carrier :=
    S.disk_subset_domain 0 (S.pole_mem_disk 0)
  have hΩ_mem : Ω.carrier ∈ 𝓝 p :=
    Ω.isOpen.mem_nhds hpΩ
  refine ⟨M, ?_⟩
  filter_upwards
    [hM, mem_nhdsWithin_of_mem_nhds hΩ_mem, self_mem_nhdsWithin] with
    x hxM hxΩ hx
  have hx_ne : x ≠ p := hx.2
  have hconv_single :
      TendstoUniformlyOn
        (fun k : ℕ ↦ fun y : X ↦ S.approximant (φ k) y)
        f Filter.atTop ({x} : Set X) :=
    hconv ({x} : Set X) (isCompact_singleton (x := x))
      (by
        intro y hy
        exact ⟨by simpa [Set.mem_singleton_iff.mp hy] using hxΩ,
          by simpa [Set.mem_singleton_iff.mp hy] using hx_ne⟩)
  simpa [sub_eq_add_neg] using
    tendstoUniformlyOn_pointwise_norm_add_const_le_of_eventually
      (K := ({x} : Set X))
      (F := fun k : ℕ ↦ fun y : X ↦ S.approximant (φ k) y)
      (f := f) (x := x)
      (c := -Real.log ‖χ.chart x - χ.chart p‖) (M := M)
      (by simp) hconv_single (by
        filter_upwards [hxM] with k hk
        simpa [sub_eq_add_neg] using hk)

/--
%%handwave
name:
  Annular compact-local limits retain the logarithmic zero
statement:
  A compact-local limit of zero-radius annular Perron approximants has the
  removable logarithmic zero prescribed by the shrinking inner boundary
  circles.
proof:
  In a coordinate at the pole, subtract the coordinate logarithm from each
  annular solution.  The inner boundary value makes the remainders uniformly
  controlled on shrinking annuli, and removable compactness produces a
  harmonic limit across the pole.
-/
theorem annularPerron_approximationSystem_limit_logarithmic_zero_of_compact_convergence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier \ {p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ S.approximant (φ k) x)
          f Filter.atTop K) :
    HasLogarithmicZeroWithin X Ω.carrier p f := by
  have hpΩ : p ∈ Ω.carrier :=
    S.disk_subset_domain 0 (S.pole_mem_disk 0)
  have hharm :
      IsHarmonicOnSurface (Ω.carrier \ {p}) f :=
    S.approximant_subsequence_limit_harmonic_away_pole_of_compact_convergence
      hφ hconv
  exact
    logarithmic_zero_of_harmonicOn_open_punctured_and_bounded_remainder
      Ω.isOpen hpΩ hharm
      (annularPerron_approximationSystem_limit_logarithmic_remainder_locally_bounded_of_compact_convergence
        hnoncompact S hnormalized hφ hconv)

/--
%%handwave
name:
  Annular approximations have a compact-local logarithmic limit
statement:
  An annular zero-radius approximation system has a subsequence converging
  uniformly on compact subsets away from the pole to a function with zero
  outer boundary value, nonpositive values away from the pole, and the
  logarithmic-zero asymptotic at the pole.
proof:
  Prove a uniform base-point barrier estimate for the annular Perron
  solutions, use Harnack compactness and a diagonal argument on compact
  subsets away from the pole, pass the maximum-principle sign and outer
  boundary values to the limit, and identify the pole asymptotic from the
  logarithmic inner boundary data.
-/
theorem annularPerron_approximationSystem_extracts_compact_convergence_asymptotics
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : X → ℝ,
        (∀ K : Set X, IsCompact K → K ⊆ Ω.carrier \ {p} →
          TendstoUniformlyOn
            (fun k : ℕ ↦ fun x : X ↦ S.approximant (φ k) x)
            f Filter.atTop K) ∧
        ContinuousOn f (closure Ω.carrier \ {p}) ∧
        (∀ x ∈ Ω.boundary, f x = 0) ∧
        (∀ x ∈ Ω.carrier \ {p}, f x ≤ 0) ∧
        HasLogarithmicZeroWithin X Ω.carrier p f := by
  rcases annularPerron_approximationSystem_compactness_data
      hnoncompact S hnormalized with
    ⟨hpointwise, heq_tail⟩
  rcases
    annularPerron_approximationSystem_extracts_compact_convergence_away_pole
      S hpointwise heq_tail with
    ⟨φ, hφ, f, hconv, hboundary⟩
  have hcont :
      ContinuousOn f (closure Ω.carrier \ {p}) :=
    annularPerron_approximationSystem_limit_continuousOn_punctured_closure_of_compact_convergence
      hnoncompact S hnormalized hφ hconv hboundary
  refine ⟨φ, hφ, f, hconv, hcont, hboundary, ?_, ?_⟩
  · exact
      S.approximant_subsequence_limit_nonpositive_on_punctured_domain_of_compact_convergence
        hφ hconv
  · exact
      annularPerron_approximationSystem_limit_logarithmic_zero_of_compact_convergence
        hnoncompact S hnormalized hφ hconv

/--
%%handwave
name:
  Logarithmically normalized annular Perron systems have zero-radius Green limits
statement:
  Every logarithmically normalized annular Perron approximation system has a
  subsequential zero-radius Green limit.
proof:
  The maximum principle supplies uniform sign and boundary control.  Harnack
  compactness gives a locally uniform subsequential limit on compact subsets
  away from the pole.  The logarithmic normalization of the moving inner
  boundary identifies the logarithmic zero at the pole, and the outer boundary
  values pass to zero.
-/
theorem annularPerron_approximationSystem_extracts_boundedNegativeGreenLimit
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    (hnoncompact : ¬ CompactSpace X)
    (S : AnnularPerronApproximationSystem X Ω p)
    (hnormalized :
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S) :
    Nonempty (AnnularPerronBoundedNegativeGreenLimit X Ω p) := by
  classical
  rcases annularPerron_approximationSystem_extracts_compact_convergence_asymptotics
      hnoncompact S hnormalized with
    ⟨φ, hφ, f, hconv, hcont, hboundary, hnonpos_punctured, hlog⟩
  have hpΩ : p ∈ Ω.carrier := (S.disk_subset_domain 0) (S.pole_mem_disk 0)
  refine ⟨
    annularPerronBoundedNegativeGreenLimit_of_compact_convergence_and_asymptotics
      S hφ
      (f := Function.update f p 0)
      ?_ ?_ ?_ ?_ ?_⟩
  · intro K hK_compact hK_subset
    exact tendstoUniformlyOn_update_real_of_subset_ne
      (hconv K hK_compact hK_subset)
      (fun x hxK ↦ (hK_subset hxK).2)
  · exact continuousOn_update_real_of_subset_ne hcont
      (fun x hx ↦ hx.2)
  · exact boundary_zero_update_at_interior (Ω := Ω) (p := p) (a := 0)
      hpΩ hboundary
  · exact nonpositive_on_domain_update_at_pole_of_punctured
      (Ω := Ω) (p := p) (a := 0) le_rfl hnonpos_punctured
  · exact logarithmic_zero_update_at_pole (p := p) (a := 0) hlog

/--
%%handwave
name:
  Fixed-chart shrinking closed coordinate disks
statement:
  A fixed coordinate chart and an initial radius \(\rho<R\) determine closed
  coordinate disks of radii \(\rho/(n+1)\) inside the same ambient coordinate
  ball.
-/
noncomputable def fixedChartShrinkingClosedCoordinateDisk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (c : ℂ)
    {ρ R : ℝ} (hρ_pos : 0 < ρ) (hρR : ρ < R)
    (hball_target : Metric.ball c R ⊆ e.target) (n : ℕ) :
    ClosedCoordinateDisk X := by
  let r : ℝ := ρ / ((n : ℝ) + 1)
  have hr_pos : 0 < r := by
    dsimp [r]
    exact div_pos hρ_pos (Nat.cast_add_one_pos n)
  have hr_le_ρ : r ≤ ρ := by
    have hden_pos : 0 < (n : ℝ) + 1 := Nat.cast_add_one_pos n
    have hden_ge : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [div_le_iff₀ hden_pos]
    nlinarith [mul_le_mul_of_nonneg_left hden_ge hρ_pos.le]
  have hrR : r < R := hr_le_ρ.trans_lt hρR
  exact closedCoordinateDiskOfChartBall e he c hr_pos hrR hball_target

@[simp] theorem fixedChartShrinkingClosedCoordinateDisk_closedRadius
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (c : ℂ)
    {ρ R : ℝ} (hρ_pos : 0 < ρ) (hρR : ρ < R)
    (hball_target : Metric.ball c R ⊆ e.target) (n : ℕ) :
    (fixedChartShrinkingClosedCoordinateDisk e he c hρ_pos hρR hball_target n).closedRadius =
      ρ / ((n : ℝ) + 1) := by
  rfl

/--
%%handwave
name:
  Logarithms of comparable positive quantities differ by a bounded amount
statement:
  If \(a,b>0\) and \(ma\le b\le Ma\) for positive constants \(m,M\),
  then \(|\log a-\log b|\) is bounded by a constant depending only on
  \(m\) and \(M\).
-/
lemma real_log_sub_norm_le_of_mul_le_le_mul
    {a b m M : ℝ} (ha : 0 < a) (hm : 0 < m) (hM : 0 < M)
    (hlo : m * a ≤ b) (hhi : b ≤ M * a) :
    ‖Real.log a - Real.log b‖ ≤
      max ‖Real.log m‖ ‖Real.log M‖ := by
  have hma_pos : 0 < m * a := mul_pos hm ha
  have hb : 0 < b := lt_of_lt_of_le hma_pos hlo
  have hlow_log : Real.log (m * a) ≤ Real.log b :=
    Real.log_le_log hma_pos hlo
  have hlow_log' : Real.log m + Real.log a ≤ Real.log b := by
    simpa [Real.log_mul hm.ne' ha.ne'] using hlow_log
  have hupper_log : Real.log b ≤ Real.log (M * a) :=
    Real.log_le_log hb hhi
  have hupper_log' : Real.log b ≤ Real.log M + Real.log a := by
    simpa [Real.log_mul hM.ne' ha.ne'] using hupper_log
  have hleft : -(max ‖Real.log m‖ ‖Real.log M‖) ≤
      Real.log a - Real.log b := by
    have hM_bound : -‖Real.log M‖ ≤ Real.log a - Real.log b := by
      have hneg : -‖Real.log M‖ ≤ -Real.log M :=
        neg_le_neg (Real.le_norm_self (Real.log M))
      have hlog : -Real.log M ≤ Real.log a - Real.log b := by
        linarith
      exact hneg.trans hlog
    have hmax : ‖Real.log M‖ ≤ max ‖Real.log m‖ ‖Real.log M‖ :=
      le_max_right _ _
    linarith
  have hright : Real.log a - Real.log b ≤
      max ‖Real.log m‖ ‖Real.log M‖ := by
    have hm_bound : Real.log a - Real.log b ≤ ‖Real.log m‖ := by
      exact (by linarith : Real.log a - Real.log b ≤ -Real.log m).trans
        (by simpa using (Real.le_norm_self (-Real.log m)))
    have hmax : ‖Real.log m‖ ≤ max ‖Real.log m‖ ‖Real.log M‖ :=
      le_max_left _ _
    linarith
  simpa [Real.norm_eq_abs] using abs_le.mpr ⟨hleft, hright⟩

/--
%%handwave
name:
  Noncritical holomorphic germs have bounded logarithmic distance distortion
statement:
  If a holomorphic germ of one complex variable has nonzero derivative at a
  point, then near that point the logarithm of the distance to the point and
  the logarithm of the distance to its image differ by a bounded amount.
proof:
  The derivative is nonzero, so the germ is locally bi-Lipschitz.  The two
  distances are comparable by positive multiplicative constants, and taking
  logarithms turns this comparison into a uniform additive bound.
-/
theorem analyticAt_nonzero_deriv_log_norm_sub_comparable_core
    {F : ℂ → ℂ} {z₀ : ℂ}
    (hF : AnalyticAt ℂ F z₀) (hderiv : deriv F z₀ ≠ 0) :
    ∃ r C : ℝ, 0 < r ∧
      ∀ z : ℂ, z ≠ z₀ → ‖z - z₀‖ < r →
        ‖Real.log ‖z - z₀‖ -
          Real.log ‖F z - F z₀‖‖ ≤ C := by
  let d : ℂ := deriv F z₀
  have hd_pos : 0 < ‖d‖ := norm_pos_iff.mpr (by simpa [d] using hderiv)
  have hderivAt : HasDerivAt F d z₀ := by
    simpa [d] using hF.differentiableAt.hasDerivAt
  have hslope_tendsto :
      Filter.Tendsto (slope F z₀) (𝓝[≠] z₀) (𝓝 d) :=
    hderivAt.tendsto_slope
  have hslope_event :
      {z : ℂ | slope F z₀ z ∈ Metric.ball d (‖d‖ / 2)} ∈
        𝓝[≠] z₀ :=
    hslope_tendsto (Metric.ball_mem_nhds d (half_pos hd_pos))
  rcases Metric.mem_nhdsWithin_iff.mp hslope_event with
    ⟨r, hr_pos, hball_slope⟩
  let m : ℝ := ‖d‖ / 2
  let M : ℝ := (3 / 2 : ℝ) * ‖d‖
  refine ⟨r, max ‖Real.log m‖ ‖Real.log M‖, hr_pos, ?_⟩
  intro z hz_ne hz_small
  have hz_ball : z ∈ Metric.ball z₀ r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz_small
  have hz_compl : z ∈ ({z₀}ᶜ : Set ℂ) := by
    simpa using hz_ne
  have hclose_mem :
      slope F z₀ z ∈ Metric.ball d (‖d‖ / 2) :=
    hball_slope ⟨hz_ball, hz_compl⟩
  have hclose : ‖slope F z₀ z - d‖ < ‖d‖ / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hclose_mem
  have hclose_rev : ‖d - slope F z₀ z‖ < ‖d‖ / 2 := by
    simpa [norm_sub_rev] using hclose
  have hslope_lower : m ≤ ‖slope F z₀ z‖ := by
    have hd_le :
        ‖d‖ ≤ ‖d - slope F z₀ z‖ + ‖slope F z₀ z‖ := by
      calc
        ‖d‖ = ‖(d - slope F z₀ z) + slope F z₀ z‖ := by
          ring_nf
        _ ≤ ‖d - slope F z₀ z‖ + ‖slope F z₀ z‖ :=
          norm_add_le _ _
    dsimp [m]
    linarith
  have hslope_upper : ‖slope F z₀ z‖ ≤ M := by
    have hs_le :
        ‖slope F z₀ z‖ ≤ ‖slope F z₀ z - d‖ + ‖d‖ := by
      calc
        ‖slope F z₀ z‖ = ‖(slope F z₀ z - d) + d‖ := by
          ring_nf
        _ ≤ ‖slope F z₀ z - d‖ + ‖d‖ :=
          norm_add_le _ _
    dsimp [M]
    linarith
  have hzsub_ne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz_ne
  have hnorm_z_pos : 0 < ‖z - z₀‖ := norm_pos_iff.mpr hzsub_ne
  have hnorm_z_ne : ‖z - z₀‖ ≠ 0 := ne_of_gt hnorm_z_pos
  have hnorm_slope_mul :
      ‖slope F z₀ z‖ * ‖z - z₀‖ = ‖F z - F z₀‖ := by
    rw [slope_def_module, norm_smul, norm_inv]
    field_simp [hnorm_z_ne]
  have hm_pos : 0 < m := by
    dsimp [m]
    exact half_pos hd_pos
  have hM_pos : 0 < M := by
    dsimp [M]
    exact mul_pos (by norm_num) hd_pos
  have hlo : m * ‖z - z₀‖ ≤ ‖F z - F z₀‖ := by
    calc
      m * ‖z - z₀‖ ≤ ‖slope F z₀ z‖ * ‖z - z₀‖ :=
        mul_le_mul_of_nonneg_right hslope_lower hnorm_z_pos.le
      _ = ‖F z - F z₀‖ := hnorm_slope_mul
  have hhi : ‖F z - F z₀‖ ≤ M * ‖z - z₀‖ := by
    calc
      ‖F z - F z₀‖ = ‖slope F z₀ z‖ * ‖z - z₀‖ :=
        hnorm_slope_mul.symm
      _ ≤ M * ‖z - z₀‖ :=
        mul_le_mul_of_nonneg_right hslope_upper hnorm_z_pos.le
  exact
    real_log_sub_norm_le_of_mul_le_le_mul
      (a := ‖z - z₀‖) (b := ‖F z - F z₀‖)
      (m := m) (M := M) hnorm_z_pos hm_pos hM_pos hlo hhi

/--
%%handwave
name:
  Pole coordinates have bounded logarithmic distance distortion, core
statement:
  For two coordinates centered at the same surface point, the difference
  between the logarithms of the two coordinate distances to the point is
  bounded on a sufficiently small punctured neighborhood.
proof:
  The transition map between the coordinates is holomorphic, maps the pole to
  the pole, and has nonzero derivative there.  Hence it is bi-Lipschitz near
  the pole.  The coordinate distances are therefore comparable up to positive
  multiplicative constants, and taking logarithms gives a bounded additive
  difference.
-/
theorem poleCoordinate_logDistance_difference_bounded_near_pole_core
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (p : X)
    (hp_source : p ∈ e.source) (χ : PointedSurfaceCoordinate X p) :
    ∃ r C : ℝ, 0 < r ∧
      ∀ x : X, x ∈ e.source → x ≠ p →
        ‖e x - e p‖ < r →
          x ∈ χ.chart.source ∧
            ‖Real.log ‖e x - e p‖ -
              Real.log ‖χ.chart x - χ.chart p‖‖ ≤ C := by
  let ψ : PointedSurfaceCoordinate X p :=
    { chart := e, chart_mem_atlas := he, base_mem_source := hp_source }
  let F : ℂ → ℂ := fun z : ℂ ↦ χ.chart (ψ.chart.symm z)
  let z₀ : ℂ := ψ.chart p
  have hz₀_target : z₀ ∈ ψ.chart.target := by
    dsimp [z₀]
    exact ψ.chart.map_source ψ.base_mem_source
  have hsymm_z₀ : ψ.chart.symm z₀ = p := by
    dsimp [z₀]
    exact ψ.chart.left_inv ψ.base_mem_source
  have hz₀_sourceχ : ψ.chart.symm z₀ ∈ χ.chart.source := by
    simpa [hsymm_z₀] using χ.base_mem_source
  have hF_an : AnalyticAt ℂ F z₀ := by
    dsimp [F, z₀]
    exact chartTransition_analyticAt ψ.chart ψ.chart_mem_atlas
      χ.chart χ.chart_mem_atlas hz₀_target hz₀_sourceχ
  have hF_deriv_ne : deriv F z₀ ≠ 0 := by
    simpa [F, z₀] using
      (pointedCoordinate_transition_deriv_ne_zero X χ ψ)
  rcases
    analyticAt_nonzero_deriv_log_norm_sub_comparable_core hF_an hF_deriv_ne with
    ⟨r_log, C, hr_log_pos, hlog⟩
  have hpre_sourceχ : ψ.chart.symm ⁻¹' χ.chart.source ∈ 𝓝 z₀ := by
    have hsource_nhds : χ.chart.source ∈ 𝓝 (ψ.chart.symm z₀) := by
      simpa [hsymm_z₀] using
        χ.chart.open_source.mem_nhds χ.base_mem_source
    exact ψ.chart.continuousAt_symm hz₀_target hsource_nhds
  rcases Metric.mem_nhds_iff.mp hpre_sourceχ with
    ⟨r_source, hr_source_pos, hball_source⟩
  let r : ℝ := min r_log r_source / 2
  have hr_pos : 0 < r := by
    dsimp [r]
    exact half_pos (lt_min hr_log_pos hr_source_pos)
  refine ⟨r, C, hr_pos, ?_⟩
  intro x hx_source hx_ne hx_r
  have hr_le_log : r ≤ r_log := by
    dsimp [r]
    have hmin_le : min r_log r_source ≤ r_log := min_le_left _ _
    linarith
  have hr_le_source : r ≤ r_source := by
    dsimp [r]
    have hmin_le : min r_log r_source ≤ r_source := min_le_right _ _
    linarith
  have hz_ne : e x ≠ z₀ := by
    intro hz
    apply hx_ne
    exact e.injOn hx_source hp_source (by simpa [ψ, z₀] using hz)
  have hz_source_small : ‖e x - z₀‖ < r_source := by
    have hlt : ‖e x - e p‖ < r_source := lt_of_lt_of_le hx_r hr_le_source
    simpa [ψ, z₀] using hlt
  have hx_sourceχ : x ∈ χ.chart.source := by
    have hz_ball : e x ∈ Metric.ball z₀ r_source := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz_source_small
    have hsymm_sourceχ : ψ.chart.symm (e x) ∈ χ.chart.source :=
      hball_source hz_ball
    simpa [ψ, e.left_inv hx_source] using hsymm_sourceχ
  have hz_log_small : ‖e x - z₀‖ < r_log := by
    have hlt : ‖e x - e p‖ < r_log := lt_of_lt_of_le hx_r hr_le_log
    simpa [ψ, z₀] using hlt
  have hx_log := hlog (e x) hz_ne hz_log_small
  have hF_ex : F (e x) = χ.chart x := by
    dsimp [F, ψ]
    rw [e.left_inv hx_source]
  have hF_z₀ : F z₀ = χ.chart p := by
    dsimp [F, z₀, ψ]
    rw [e.left_inv hp_source]
  refine ⟨hx_sourceχ, ?_⟩
  simpa [F, z₀, ψ, hF_ex, hF_z₀] using hx_log

/--
%%handwave
name:
  Fixed-chart shrinking disks have bounded logarithmic coordinate distortion,
  core
statement:
  Let the deleted disks be concentric disks in one fixed pole coordinate with
  radii \(\rho/(n+1)\).  In every other coordinate at the pole, the logarithm
  of this radius differs from the logarithmic distance to the pole on the
  moving boundary circle by one uniform additive constant.
proof:
  The transition between the fixed pole coordinate and any other pole
  coordinate is holomorphic with nonzero derivative at the pole.  Hence it is
  bi-Lipschitz on a sufficiently small neighborhood of the pole.  On the
  circle \(|z-c|=\rho/(n+1)\), this gives two-sided multiplicative bounds for
  the other coordinate distance; taking logarithms gives the stated uniform
  additive bound.
-/
theorem fixedChartShrinkingClosedCoordinateDisk_logarithmicBoundaryNormalization_core
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (p : X)
    (hp_source : p ∈ e.source)
    {ρ R : ℝ} (hρ_pos : 0 < ρ) (hρR : ρ < R)
    (hball_target : Metric.ball (e p) R ⊆ e.target) :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ C : ℝ,
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ x ∈
            (fixedChartShrinkingClosedCoordinateDisk e he (e p)
              hρ_pos hρR hball_target n).boundaryCircle,
            x ∈ χ.chart.source ∧ x ≠ p ∧
              ‖Real.log
                  (fixedChartShrinkingClosedCoordinateDisk e he (e p)
                    hρ_pos hρR hball_target n).closedRadius -
                Real.log ‖χ.chart x - χ.chart p‖‖ ≤ C := by
  intro χ
  rcases
    poleCoordinate_logDistance_difference_bounded_near_pole_core
      e he p hp_source χ with
    ⟨r₀, C, hr₀_pos, hdist⟩
  refine ⟨C, ?_⟩
  have htendsto_one :
      Filter.Tendsto
        (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have htendsto_r :
      Filter.Tendsto
        (fun n : ℕ ↦ ρ * ((1 : ℝ) / ((n : ℝ) + 1)))
        Filter.atTop (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul ρ htendsto_one)
  have hevent_small :
      ∀ᶠ n : ℕ in Filter.atTop, ρ / ((n : ℝ) + 1) < r₀ := by
    have hsmall :=
      htendsto_r.eventually (Iio_mem_nhds hr₀_pos)
    filter_upwards [hsmall] with n hn
    simpa [div_eq_mul_inv] using hn
  filter_upwards [hevent_small] with n hn_small x hx_boundary
  change x ∈
    e.source ∩ e ⁻¹' Metric.sphere (e p) (ρ / ((n : ℝ) + 1)) at hx_boundary
  have hx_source : x ∈ e.source := hx_boundary.1
  have hnorm_eq : ‖e x - e p‖ = ρ / ((n : ℝ) + 1) := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hx_boundary.2
  have hx_ne : x ≠ p := by
    intro hxp
    have hzero : ‖e x - e p‖ = 0 := by simp [hxp]
    have hr_pos : 0 < ρ / ((n : ℝ) + 1) :=
      div_pos hρ_pos (Nat.cast_add_one_pos n)
    linarith
  have hdist_small : ‖e x - e p‖ < r₀ := by
    simpa [hnorm_eq] using hn_small
  rcases hdist x hx_source hx_ne hdist_small with
    ⟨hxχ_source, hlog⟩
  refine ⟨hxχ_source, hx_ne, ?_⟩
  simpa [hnorm_eq] using hlog

/--
%%handwave
name:
  Smooth domains admit normalized annular disk sequences, core
statement:
  Around an interior point of a smooth boundary domain there is a sequence of
  closed coordinate disks, all cut from one pole coordinate chart, whose
  carriers shrink to the pole, whose complements in the domain are nonempty,
  and whose logarithmic boundary radii are uniformly comparable with the
  logarithmic distance in every other pole coordinate.
proof:
  Choose a coordinate ball compactly contained in the smooth domain and
  avoiding a second interior point.  Delete concentric closed disks with
  radii tending to zero.  These disks shrink to the pole and leave the second
  point in the annulus.  For any other pole coordinate, the transition map has
  nonzero derivative at the pole, so the ratio between the two coordinate
  distances is bounded above and below on sufficiently small punctured
  neighborhoods; taking logarithms gives the stated uniform additive bound.
-/
theorem smoothBoundaryDomain_has_logarithmically_normalized_annularCoordinateDiskSequence_core
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) (p : X) (hp : p ∈ Ω.carrier) :
    ∃ disk : ℕ → ClosedCoordinateDisk X,
      (∀ n : ℕ, p ∈ (disk n).carrier) ∧
        (∀ n : ℕ, (disk n).closedRadius ≤ 1) ∧
          (∀ n : ℕ, (disk n).carrier ⊆ Ω.carrier) ∧
            (∀ n : ℕ, (Ω.carrier \ (disk n).carrier).Nonempty) ∧
              (∀ ⦃N : Set X⦄, IsOpen N → p ∈ N →
                ∀ᶠ n : ℕ in Filter.atTop, (disk n).carrier ⊆ N) ∧
                (∀ χ : PointedSurfaceCoordinate X p,
                  ∃ C : ℝ,
                    ∀ᶠ n : ℕ in Filter.atTop,
                      ∀ x ∈ (disk n).boundaryCircle,
                        x ∈ χ.chart.source ∧ x ≠ p ∧
                          ‖Real.log (disk n).closedRadius -
                            Real.log ‖χ.chart x - χ.chart p‖‖ ≤ C) := by
  classical
  rcases exists_ne_mem_open_of_mem Ω.isOpen hp with
    ⟨q, hqΩ, hq_ne_p⟩
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let c : ℂ := e p
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ p
  have hp_ne_q : p ≠ q := hq_ne_p.symm
  let U : Set X := (Ω.carrier ∩ {x : X | x ≠ q}) ∩ e.source
  have hU_nhds : U ∈ 𝓝 p := by
    have hΩ_ne_nhds :
        Ω.carrier ∩ {x : X | x ≠ q} ∈ 𝓝 p :=
      (Ω.isOpen.inter (isOpen_ne (x := q))).mem_nhds
        ⟨hp, hp_ne_q⟩
    exact Filter.inter_mem hΩ_ne_nhds
      (e.open_source.mem_nhds hp_source)
  have himage : e '' U ∈ 𝓝 c := by
    simpa [c, U] using e.image_mem_nhds hp_source hU_nhds
  rcases Metric.mem_nhds_iff.mp himage with
    ⟨R, hR_pos, hball_image⟩
  have hball_target : Metric.ball c R ⊆ e.target := by
    intro z hz
    rcases hball_image hz with ⟨y, hy, hyz⟩
    rw [← hyz]
    exact e.map_source hy.2
  let ρ : ℝ := min R 1 / 2
  have hmin_pos : 0 < min R 1 := lt_min hR_pos zero_lt_one
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    linarith
  have hρR : ρ < R := by
    have hmin_le : min R 1 ≤ R := min_le_left R 1
    dsimp [ρ]
    linarith
  have hρ_le_one : ρ ≤ 1 := by
    have hmin_le : min R 1 ≤ 1 := min_le_right R 1
    dsimp [ρ]
    linarith
  let disk : ℕ → ClosedCoordinateDisk X :=
    fun n ↦ fixedChartShrinkingClosedCoordinateDisk e he c hρ_pos hρR hball_target n
  have hr_le_ρ :
      ∀ n : ℕ, ρ / ((n : ℝ) + 1) ≤ ρ := by
    intro n
    have hden_pos : 0 < (n : ℝ) + 1 := Nat.cast_add_one_pos n
    have hden_ge : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [div_le_iff₀ hden_pos]
    nlinarith [mul_le_mul_of_nonneg_left hden_ge hρ_pos.le]
  have hr_lt_R :
      ∀ n : ℕ, ρ / ((n : ℝ) + 1) < R := fun n ↦
    (hr_le_ρ n).trans_lt hρR
  have hp_disk : ∀ n : ℕ, p ∈ (disk n).carrier := by
    intro n
    change p ∈ e.source ∩ e ⁻¹' Metric.closedBall c (ρ / ((n : ℝ) + 1))
    refine ⟨hp_source, ?_⟩
    have hr_nonneg : 0 ≤ ρ / ((n : ℝ) + 1) :=
      (div_pos hρ_pos (Nat.cast_add_one_pos n)).le
    simpa [c, Metric.mem_closedBall] using hr_nonneg
  have hr_le_one : ∀ n : ℕ, (disk n).closedRadius ≤ 1 := by
    intro n
    change ρ / ((n : ℝ) + 1) ≤ 1
    exact (hr_le_ρ n).trans hρ_le_one
  have hsubset : ∀ n : ℕ, (disk n).carrier ⊆ Ω.carrier := by
    intro n y hyD
    change y ∈ e.source ∩ e ⁻¹' Metric.closedBall c (ρ / ((n : ℝ) + 1)) at hyD
    have hy_ball : e y ∈ Metric.ball c R := by
      rw [Metric.mem_ball]
      have hydist : dist (e y) c ≤ ρ / ((n : ℝ) + 1) := by
        simpa [Metric.mem_closedBall] using hyD.2
      exact lt_of_le_of_lt hydist (hr_lt_R n)
    rcases hball_image hy_ball with ⟨x, hx, hxy⟩
    have hxy_eq : x = y := e.injOn hx.2 hyD.1 hxy
    simpa [← hxy_eq] using hx.1.1
  have hq_not_disk : ∀ n : ℕ, q ∉ (disk n).carrier := by
    intro n hqD
    change q ∈ e.source ∩ e ⁻¹' Metric.closedBall c (ρ / ((n : ℝ) + 1)) at hqD
    have hq_ball : e q ∈ Metric.ball c R := by
      rw [Metric.mem_ball]
      have hqdist : dist (e q) c ≤ ρ / ((n : ℝ) + 1) := by
        simpa [Metric.mem_closedBall] using hqD.2
      exact lt_of_le_of_lt hqdist (hr_lt_R n)
    rcases hball_image hq_ball with ⟨x, hx, hxq⟩
    have hx_eq_q : x = q := e.injOn hx.2 hqD.1 hxq
    exact hx.1.2 hx_eq_q
  have hnonempty :
      ∀ n : ℕ, (Ω.carrier \ (disk n).carrier).Nonempty := by
    intro n
    exact ⟨q, hqΩ, hq_not_disk n⟩
  have hshrink :
      ∀ ⦃N : Set X⦄, IsOpen N → p ∈ N →
        ∀ᶠ n : ℕ in Filter.atTop, (disk n).carrier ⊆ N := by
    intro N hN_open hpN
    have hN_nhds : N ∩ e.source ∈ 𝓝 p :=
      Filter.inter_mem (hN_open.mem_nhds hpN)
        (e.open_source.mem_nhds hp_source)
    have hN_image : e '' (N ∩ e.source) ∈ 𝓝 c := by
      simpa [c] using e.image_mem_nhds hp_source hN_nhds
    rcases Metric.mem_nhds_iff.mp hN_image with
      ⟨δ, hδ_pos, hball_N⟩
    have htendsto_one :
        Filter.Tendsto
          (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1))
          Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have htendsto_r :
        Filter.Tendsto
          (fun n : ℕ ↦ ρ * ((1 : ℝ) / ((n : ℝ) + 1)))
          Filter.atTop (𝓝 0) := by
      simpa using (Filter.Tendsto.const_mul ρ htendsto_one)
    have hevent_small :
        ∀ᶠ n : ℕ in Filter.atTop, ρ / ((n : ℝ) + 1) < δ := by
      have hsmall :=
        htendsto_r.eventually (Iio_mem_nhds hδ_pos)
      filter_upwards [hsmall] with n hn
      simpa [div_eq_mul_inv] using hn
    filter_upwards [hevent_small] with n hn_small y hyD
    change y ∈ e.source ∩ e ⁻¹' Metric.closedBall c (ρ / ((n : ℝ) + 1)) at hyD
    have hy_ball : e y ∈ Metric.ball c δ := by
      rw [Metric.mem_ball]
      have hydist : dist (e y) c ≤ ρ / ((n : ℝ) + 1) := by
        simpa [Metric.mem_closedBall] using hyD.2
      exact lt_of_le_of_lt hydist hn_small
    rcases hball_N hy_ball with ⟨x, hx, hxy⟩
    have hxy_eq : x = y := e.injOn hx.2 hyD.1 hxy
    simpa [← hxy_eq] using hx.1
  have hnormalized :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ C : ℝ,
          ∀ᶠ n : ℕ in Filter.atTop,
            ∀ x ∈ (disk n).boundaryCircle,
              x ∈ χ.chart.source ∧ x ≠ p ∧
                ‖Real.log (disk n).closedRadius -
                  Real.log ‖χ.chart x - χ.chart p‖‖ ≤ C := by
    simpa [disk, c] using
      fixedChartShrinkingClosedCoordinateDisk_logarithmicBoundaryNormalization_core
        e he p hp_source hρ_pos hρR (by simpa [c] using hball_target)
  exact
    ⟨disk, hp_disk, hr_le_one, hsubset, hnonempty, hshrink, hnormalized⟩

/--
%%handwave
name:
  Smooth domains admit normalized annular Perron approximation systems, core
statement:
  Around an interior point of a smooth boundary domain, choose deleted disks
  from one fixed coordinate chart with radii tending to zero, solve the
  logarithmic annular Perron problem on each resulting annulus, and obtain a
  logarithmically normalized annular approximation system.
proof:
  Pick a coordinate ball compactly contained in the smooth domain and choose a
  decreasing positive radius sequence.  The corresponding closed coordinate
  disks all contain the pole, lie in the domain, and shrink to the pole.  The
  assumed annular Perron solvability supplies the harmonic solutions.  For any
  other pole coordinate, the transition map has nonzero derivative at the
  pole, so on sufficiently small boundary circles the two logarithmic
  distances differ by a bounded amount.
-/
theorem smoothBoundaryDomain_has_normalized_annularPerron_approximationSystem_core
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) (p : X) (hp : p ∈ Ω.carrier)
    (happroximants :
      ∀ (D : ClosedCoordinateDisk X)
        (_hpD : p ∈ D.carrier)
        (hD_subset : D.carrier ⊆ Ω.carrier)
        (hnonempty : (Ω.carrier \ D.carrier).Nonempty),
        ∃ u : X → ℝ,
          SolvesHarmonicDirichletProblem
            (annularPerronDomain Ω D hD_subset hnonempty)
            (annularLogBoundaryData Ω D hD_subset hnonempty) u) :
    ∃ S : AnnularPerronApproximationSystem X Ω p,
      AnnularPerronApproximationSystem.HasLogarithmicBoundaryNormalization S := by
  rcases
    smoothBoundaryDomain_has_logarithmically_normalized_annularCoordinateDiskSequence_core
      Ω p hp with
    ⟨disk, hp_disk, hr_le_one, hsubset, hnonempty, hshrink,
      hnormalized_disk⟩
  have hchoose_solution :
      ∀ n : ℕ,
        ∃ u : X → ℝ,
          SolvesHarmonicDirichletProblem
            (annularPerronDomain Ω (disk n)
              (hsubset n) (hnonempty n))
            (annularLogBoundaryData Ω (disk n)
              (hsubset n) (hnonempty n)) u := by
    intro n
    exact happroximants (disk n) (hp_disk n) (hsubset n) (hnonempty n)
  choose u hu using hchoose_solution
  refine ⟨{
    disk := disk
    pole_mem_disk := hp_disk
    closedRadius_le_one := hr_le_one
    disk_subset_domain := hsubset
    annulus_nonempty := hnonempty
    approximant := u
    solves_annular_problem := hu
    disks_shrink_to_pole := ?_
  }, ?_⟩
  · intro N hN_open hpN
    exact hshrink hN_open hpN
  · exact hnormalized_disk

/--
%%handwave
name:
  Annular Perron problems have a zero-radius Green limit
statement:
  If arbitrarily small closed coordinate disks about a pole can be deleted
  from a smooth boundary domain and the associated logarithmic annular Perron
  problems are solvable, then a sequence of such solutions has a zero-radius
  Green limit.
proof:
  Choose disks shrinking to the pole and solve the annular Perron problem on
  each punctured domain.  The maximum principle supplies uniform sign and
  boundary control, and Harnack compactness gives a locally uniform
  subsequential limit on compact subsets away from the pole.  The logarithmic
  inner boundary values identify the logarithmic zero at the pole.
-/
theorem arbitrarilySmall_annularPerron_extracts_boundedNegativeGreenLimit
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hnoncompact : ¬ CompactSpace X)
    (Ω : SmoothBoundaryDomain X) (p : X) (hp : p ∈ Ω.carrier)
    (_hsmallAnnuli :
      ∀ ⦃N : Set X⦄, IsOpen N → p ∈ N →
        ∃ D : ClosedCoordinateDisk X,
          p ∈ D.carrier ∧
            D.closedRadius ≤ 1 ∧
              D.carrier ⊆ Ω.carrier ∧
                D.carrier ⊆ N ∧
                  (Ω.carrier \ D.carrier).Nonempty)
    (happroximants :
      ∀ (D : ClosedCoordinateDisk X)
        (_hpD : p ∈ D.carrier)
        (hD_subset : D.carrier ⊆ Ω.carrier)
        (hnonempty : (Ω.carrier \ D.carrier).Nonempty),
        ∃ u : X → ℝ,
          SolvesHarmonicDirichletProblem
            (annularPerronDomain Ω D hD_subset hnonempty)
        (annularLogBoundaryData Ω D hD_subset hnonempty) u) :
    Nonempty (AnnularPerronBoundedNegativeGreenLimit X Ω p) := by
  rcases smoothBoundaryDomain_has_normalized_annularPerron_approximationSystem_core
      Ω p hp happroximants with
    ⟨S, hnormalized⟩
  exact annularPerron_approximationSystem_extracts_boundedNegativeGreenLimit
    hnoncompact S hnormalized

/--
%%handwave
name:
  Bounded Green potential from arbitrarily small annular Perron problems
statement:
  If arbitrarily small closed coordinate disks about a pole can be deleted
  from a smooth boundary domain and the associated logarithmic annular Perron
  problems are solvable, then their zero-inner-radius limit is a
  bounded-domain negative Green potential with that pole.
proof:
  Choose a nested sequence of such disks whose radii tend to zero.  Solve the
  annular Perron problem on each punctured domain.  Harnack compactness gives
  a locally uniform subsequential limit away from the pole; the maximum
  principle preserves the sign and outer boundary value, and the logarithmic
  inner boundary data gives the logarithmic zero at the pole.
-/
theorem arbitrarilySmall_annularPerron_limit_boundedNegativeGreenPotential
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hnoncompact : ¬ CompactSpace X)
    (Ω : SmoothBoundaryDomain X) (p : X) (hp : p ∈ Ω.carrier)
    (hsmallAnnuli :
      ∀ ⦃N : Set X⦄, IsOpen N → p ∈ N →
        ∃ D : ClosedCoordinateDisk X,
          p ∈ D.carrier ∧
            D.closedRadius ≤ 1 ∧
              D.carrier ⊆ Ω.carrier ∧
                D.carrier ⊆ N ∧
                  (Ω.carrier \ D.carrier).Nonempty)
    (happroximants :
      ∀ (D : ClosedCoordinateDisk X)
        (_hpD : p ∈ D.carrier)
        (hD_subset : D.carrier ⊆ Ω.carrier)
        (hnonempty : (Ω.carrier \ D.carrier).Nonempty),
        ∃ u : X → ℝ,
          SolvesHarmonicDirichletProblem
            (annularPerronDomain Ω D hD_subset hnonempty)
            (annularLogBoundaryData Ω D hD_subset hnonempty) u) :
    Nonempty (BoundedNegativeGreenPotential X Ω p) := by
  rcases arbitrarilySmall_annularPerron_extracts_boundedNegativeGreenLimit
      hnoncompact Ω p hp hsmallAnnuli happroximants with
    ⟨L⟩
  exact ⟨L.toBoundedNegativeGreenPotential⟩

/--
%%handwave
name:
  Bounded Green potential as a zero-inner-radius limit
statement:
  If all logarithmic annular Perron approximants around a pole in a smooth
  boundary domain exist, then their zero-inner-radius limit is a bounded-domain
  negative Green potential with that pole.
proof:
  Choose a decreasing sequence of closed coordinate disks around the pole.
  Harnack compactness gives a locally uniform subsequential limit on compact
  subsets away from the pole.  The maximum principle preserves the boundary
  value and sign, while the logarithmic inner boundary values give the local
  logarithmic zero at the pole.
-/
theorem annularPerron_zeroInnerRadiusLimit_boundedNegativeGreenPotential
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hnoncompact : ¬ CompactSpace X)
    (Ω : SmoothBoundaryDomain X) (p : X) (hp : p ∈ Ω.carrier)
    (happroximants :
      ∀ (D : ClosedCoordinateDisk X)
        (hD_subset : D.carrier ⊆ Ω.carrier)
        (hnonempty : (Ω.carrier \ D.carrier).Nonempty),
        ∃ u : X → ℝ,
          SolvesHarmonicDirichletProblem
            (annularPerronDomain Ω D hD_subset hnonempty)
            (annularLogBoundaryData Ω D hD_subset hnonempty) u) :
    Nonempty (BoundedNegativeGreenPotential X Ω p) := by
  exact arbitrarilySmall_annularPerron_limit_boundedNegativeGreenPotential
    hnoncompact Ω p hp
    (smoothBoundaryDomain_exists_arbitrarilySmall_annularCoordinateDisk Ω hp)
    (fun D hpD hD_subset hnonempty ↦ happroximants D hD_subset hnonempty)

/--
%%handwave
name:
  Bounded Green potential from annular Perron problems
statement:
  Every point of a smooth boundary domain is the pole of a bounded-domain
  negative Green potential obtained as the zero-inner-radius limit of
  logarithmic annular Perron solutions.
proof:
  Delete a decreasing sequence of closed coordinate disks around the pole.
  On each resulting annulus solve the ordinary Perron problem with value
  \(\log r\) on the inner circle and value \(0\) on the outer boundary.  The
  maximum principle and Harnack compactness give a locally uniform limit on
  the punctured domain, and the explicit inner boundary values give the
  logarithmic zero at the pole.
-/
theorem smoothBoundaryDomain_has_boundedNegativeGreenPotential_via_annularPerron
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hnoncompact : ¬ CompactSpace X)
    (Ω : SmoothBoundaryDomain X) (p : X) (hp : p ∈ Ω.carrier) :
    Nonempty (BoundedNegativeGreenPotential X Ω p) := by
  exact annularPerron_zeroInnerRadiusLimit_boundedNegativeGreenPotential
    hnoncompact Ω p hp
      (smoothBoundaryDomain_has_annularPerronGreenApproximants Ω)

/--
%%handwave
name:
  Bounded Green potentials along a smooth exhaustion
statement:
  If a pole belongs to every member of a smooth exhaustion, then one can
  choose bounded-domain negative Green potentials on all exhaustion domains.
proof:
  Each member of the smooth exhaustion is a smooth relatively compact domain.
  The hypothesis \(p\in E_n\) for every \(n\) is exactly what is needed to
  apply the bounded-domain annular Perron construction with pole \(p\) on
  each \(E_n\).  Choose one bounded-domain negative Green potential for each
  member of the exhaustion.
-/
theorem smoothRelativelyCompactExhaustion_has_boundedNegativeGreenPotentials
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (hnoncompact : ¬ CompactSpace X)
    (E : SmoothRelativelyCompactExhaustion X) (p : X)
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier) :
    Nonempty ((n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p) := by
  exact ⟨fun n ↦
    Classical.choice
      (smoothBoundaryDomain_has_boundedNegativeGreenPotential_via_annularPerron
        hnoncompact (E.domain n) p (hp n))⟩

/--
%%handwave
name:
  Failure of divergence gives a bounded subsequence
statement:
  If a real sequence does not tend to \(+\infty\), then there are a real
  number \(A\) and a strictly increasing subsequence whose values are all
  strictly below \(A\).
proof:
  Negate the order-filter characterization of convergence to \(+\infty\).
  This gives, beyond every index, a later value below one fixed level.  The
  standard subsequence selection lemma turns those arbitrarily late choices
  into a strictly increasing subsequence.
-/
theorem exists_strictMono_bounded_subsequence_of_not_tendsto_atTop
    {f : ℕ → ℝ}
    (hnot : ¬ Filter.Tendsto f Filter.atTop Filter.atTop) :
    ∃ A : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : ℕ, f (φ k) < A := by
  rw [Filter.tendsto_atTop_atTop] at hnot
  push Not at hnot
  rcases hnot with ⟨A, hA⟩
  have hlate : ∀ N : ℕ, ∃ n > N, f n < A := by
    intro N
    rcases hA (N + 1) with ⟨n, hn, hnA⟩
    exact ⟨n, Nat.lt_of_succ_le hn, hnA⟩
  rcases Nat.exists_strictMono_subsequence hlate with ⟨φ, hφ, hφ_bound⟩
  exact ⟨A, φ, hφ, hφ_bound⟩

/--
%%handwave
name:
  Divergence is preserved by late reindexing
statement:
  If a real sequence tends to \(+\infty\), then every reindexing whose chosen
  index is always at least the input index also tends to \(+\infty\).
proof:
  For a prescribed lower bound, take a tail on which the original sequence is
  above that bound.  A late reindexing sends every sufficiently large input
  into the same tail.
-/
theorem tendsto_atTop_atTop_comp_of_ge
    {f : ℕ → ℝ} {ν : ℕ → ℕ}
    (hf : Filter.Tendsto f Filter.atTop Filter.atTop)
    (hν_late : ∀ j : ℕ, j ≤ ν j) :
    Filter.Tendsto (fun j : ℕ ↦ f (ν j)) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop] at hf ⊢
  intro A
  rcases hf A with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro j hj
  exact hN (ν j) (hj.trans (hν_late j))

/--
%%handwave
name:
  Divergent natural-number selectors have strictly increasing selected values
statement:
  If \(\beta_j\to+\infty\), then there is a strictly increasing subsequence
  \(\sigma_k\) such that the selected values \(\beta_{\sigma_k}\) are also
  strictly increasing.
proof:
  Recursively choose the next index past the previous selected index and far
  enough that its \(\beta\)-value is larger than the previous selected
  \(\beta\)-value.  The divergence of \(\beta\) supplies such choices at every
  step.
-/
theorem exists_strictMono_subsequence_strictMono_comp_of_tendsto_atTop
    {β : ℕ → ℕ}
    (hβ : Filter.Tendsto β Filter.atTop Filter.atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ StrictMono (fun k : ℕ ↦ β (σ k)) := by
  classical
  have hβ_atTop :
      ∀ b : ℕ, ∃ a : ℕ, ∀ n : ℕ, a ≤ n → b ≤ β n := by
    simpa [Filter.tendsto_atTop_atTop] using hβ
  have hchoose :
      ∀ s t : ℕ, ∃ n : ℕ, s < n ∧ t < β n := by
    intro s t
    rcases hβ_atTop (t + 1) with ⟨N, hN⟩
    let n : ℕ := max (s + 1) N
    refine ⟨n, ?_, ?_⟩
    · exact Nat.lt_of_succ_le (le_max_left (s + 1) N)
    · exact Nat.lt_of_succ_le (hN n (le_max_right (s + 1) N))
  let σ : ℕ → ℕ := Nat.rec (Classical.choose (hchoose 0 0))
    (fun _k prev ↦ Classical.choose (hchoose prev (β prev)))
  have hstep :
      ∀ k : ℕ,
        σ (k + 1) =
          Classical.choose (hchoose (σ k) (β (σ k))) := by
    intro k
    simp [σ]
  have hσ_succ : ∀ k : ℕ, σ k < σ (k + 1) := by
    intro k
    rw [hstep k]
    exact (Classical.choose_spec (hchoose (σ k) (β (σ k)))).1
  have hβ_succ : ∀ k : ℕ, β (σ k) < β (σ (k + 1)) := by
    intro k
    rw [hstep k]
    exact (Classical.choose_spec (hchoose (σ k) (β (σ k)))).2
  exact ⟨σ, strictMono_nat_of_lt_succ hσ_succ,
    strictMono_nat_of_lt_succ hβ_succ⟩

/--
Strictifies a sequence of late outer indices by recursively jumping beyond
both the previous selected index and the previous outer index.
-/
def lateSelectorStrictSubsequence (ν : ℕ → ℕ) : ℕ → ℕ :=
  Nat.rec 0 (fun _k prev ↦ max (prev + 1) (ν prev + 1))

/--
%%handwave
name:
  Strictifying a late selector gives a strictly increasing index sequence
statement:
  The recursive selector that jumps beyond the previous selected index is
  strictly increasing.
proof:
  At each successor step the new index is at least one more than the previous
  selected index.
-/
theorem lateSelectorStrictSubsequence_strictMono (ν : ℕ → ℕ) :
    StrictMono (lateSelectorStrictSubsequence ν) := by
  refine strictMono_nat_of_lt_succ ?_
  intro k
  have hstep :
      lateSelectorStrictSubsequence ν (k + 1) =
        max (lateSelectorStrictSubsequence ν k + 1)
          (ν (lateSelectorStrictSubsequence ν k) + 1) := by
    simp [lateSelectorStrictSubsequence]
  have hle :
      lateSelectorStrictSubsequence ν k + 1 ≤
        lateSelectorStrictSubsequence ν (k + 1) := by
    rw [hstep]
    exact Nat.le_max_left _ _
  exact Nat.lt_of_succ_le hle

/--
%%handwave
name:
  Strictifying a late selector gives strictly increasing outer indices
statement:
  If each outer index is at least its selected index, then after strictifying
  the selector, the corresponding outer indices are strictly increasing.
proof:
  The next selected index is chosen beyond the previous outer index, and the
  late-selector hypothesis puts the next outer index beyond that next selected
  index.
-/
theorem lateSelectorStrictSubsequence_comp_strictMono
    {ν : ℕ → ℕ} (hν_late : ∀ j : ℕ, j ≤ ν j) :
    StrictMono (fun k : ℕ ↦ ν (lateSelectorStrictSubsequence ν k)) := by
  refine strictMono_nat_of_lt_succ ?_
  intro k
  have hstep :
      lateSelectorStrictSubsequence ν (k + 1) =
        max (lateSelectorStrictSubsequence ν k + 1)
          (ν (lateSelectorStrictSubsequence ν k) + 1) := by
    simp [lateSelectorStrictSubsequence]
  have hlt_step :
      ν (lateSelectorStrictSubsequence ν k) <
        lateSelectorStrictSubsequence ν (k + 1) := by
    have hle :
        ν (lateSelectorStrictSubsequence ν k) + 1 ≤
          lateSelectorStrictSubsequence ν (k + 1) := by
      rw [hstep]
      exact Nat.le_max_right _ _
    exact Nat.lt_of_succ_le hle
  exact lt_of_lt_of_le hlt_step
    (hν_late (lateSelectorStrictSubsequence ν (k + 1)))

/--
%%handwave
name:
  Bounded Green compact-local subsequence limit
statement:
  A bounded Green compact-local subsequence limit is the locally uniform
  limit, on compact subsets away from the pole, of the positive bounded-domain
  Green functions obtained by negating a bounded-height subsequence.  It is
  positive and harmonic off the pole and has the standard logarithmic pole,
  but no behavior at infinity is built into the object.
-/
structure BoundedNegativeGreenSubsequenceCompactLimit
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    (φ : ℕ → ℕ) where
  /-- The selected further subsequence of the bounded-height subsequence. -/
  subseq : ℕ → ℕ
  /-- The selected further subsequence is strictly increasing. -/
  subseq_strictMono : StrictMono subseq
  /-- The compact-local limiting positive Green function. -/
  toFun : X → ℝ
  /-- The limit is positive away from the pole. -/
  positive_away_pole : ∀ x : X, x ≠ p → 0 < toFun x
  /-- The limit is harmonic on the punctured surface. -/
  harmonic_away_pole : IsHarmonicOnSurface {x : X | x ≠ p} toFun
  /-- The limit diverges to \(+\infty\) at the pole. -/
  tends_to_infinity_at_pole :
    Filter.Tendsto toFun (𝓝[≠] p) Filter.atTop
  /-- The logarithmic pole is removable after adding the local logarithm. -/
  logarithmic_singularity :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ h : X → ℝ,
        IsHarmonicOnSurface χ.chart.source h ∧
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            toFun x + Real.log ‖χ.chart x - χ.chart p‖ = h x
  /-- The negated bounded-domain potentials converge on compact sets away from the pole. -/
  locally_uniform_on_compacts_away_pole :
    ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
      TendstoUniformlyOn
        (fun k : ℕ ↦ fun x : X ↦ -((B (φ (subseq k))).toFun x))
        toFun Filter.atTop K

/--
%%handwave
name:
  Bounded Green subsequence limit
statement:
  A bounded Green subsequence limit is the locally uniform limit, on compact
  subsets away from the pole, of the positive bounded-domain Green functions
  obtained by negating a bounded-height subsequence.  The limit is a global
  Green function: it is positive and harmonic off the pole, has the
  logarithmic pole, vanishes at infinity, and has compact positive superlevel
  sets after adjoining the pole.
-/
structure BoundedNegativeGreenSubsequenceGreenLimit
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    (φ : ℕ → ℕ) where
  /-- The selected further subsequence of the bounded-height subsequence. -/
  subseq : ℕ → ℕ
  /-- The selected further subsequence is strictly increasing. -/
  subseq_strictMono : StrictMono subseq
  /-- The limiting Green function. -/
  toFun : X → ℝ
  /-- The limit is positive away from the pole. -/
  positive_away_pole : ∀ x : X, x ≠ p → 0 < toFun x
  /-- The limit is harmonic on the punctured surface. -/
  harmonic_away_pole : IsHarmonicOnSurface {x : X | x ≠ p} toFun
  /-- The limit diverges to \(+\infty\) at the pole. -/
  tends_to_infinity_at_pole :
    Filter.Tendsto toFun (𝓝[≠] p) Filter.atTop
  /-- The logarithmic pole is removable after adding the local logarithm. -/
  logarithmic_singularity :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ h : X → ℝ,
        IsHarmonicOnSurface χ.chart.source h ∧
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            toFun x + Real.log ‖χ.chart x - χ.chart p‖ = h x
  /-- The limit vanishes along the ends of the surface. -/
  tends_to_zero_at_infinity :
    Filter.Tendsto toFun (Filter.cocompact X) (𝓝 0)
  /-- Positive superlevel sets are compact after adjoining the pole. -/
  compact_positive_superlevel :
    ∀ a : ℝ, 0 < a → IsCompact ({p} ∪ {x : X | a ≤ toFun x})
  /-- The negated bounded-domain potentials converge on compact sets away from the pole. -/
  locally_uniform_on_compacts_away_pole :
    ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
      TendstoUniformlyOn
        (fun k : ℕ ↦ fun x : X ↦ -((B (φ (subseq k))).toFun x))
        toFun Filter.atTop K

namespace BoundedNegativeGreenSubsequenceGreenLimit

/--
%%handwave
name:
  Bounded Green subsequence limits are Green functions
statement:
  Every bounded Green subsequence limit determines a Green function with the
  same pole.
proof:
  The fields of the subsequence limit are exactly the positivity,
  harmonicity, logarithmic pole, vanishing at infinity, and compact-superlevel
  requirements in the definition of a Green function.
-/
def toGreenFunctionWithPole
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    {B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p}
    {φ : ℕ → ℕ}
    (L : BoundedNegativeGreenSubsequenceGreenLimit (p := p) (q := q) E B φ) :
    GreenFunctionWithPole X p where
  toFun := L.toFun
  positive_away_pole := L.positive_away_pole
  harmonic_away_pole := L.harmonic_away_pole
  tends_to_infinity_at_pole := L.tends_to_infinity_at_pole
  logarithmic_singularity := L.logarithmic_singularity
  tends_to_zero_at_infinity := L.tends_to_zero_at_infinity
  compact_positive_superlevel := L.compact_positive_superlevel

end BoundedNegativeGreenSubsequenceGreenLimit

/--
%%handwave
name:
  Assembling a bounded Green subsequence limit
statement:
  A compact-local subsequential limit of positive bounded-domain Green
  functions, together with logarithmic-pole asymptotics and vanishing at
  infinity, determines a global Green subsequence limit.
proof:
  Compact-local convergence gives harmonicity and nonnegativity away from the
  pole.  The logarithmic-pole asymptotic gives blow-up at the pole, and the
  strong minimum principle upgrades nonnegativity to strict positivity.
  Vanishing at infinity, together with punctured continuity, gives compact
  positive superlevel sets.
-/
def boundedNegativeGreenSubsequenceGreenLimit_of_compact_convergence_and_asymptotics
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ ψ : ℕ → ℕ} (hφ : StrictMono φ) (hψ : StrictMono ψ) {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ -((B (φ (ψ k))).toFun x))
          f Filter.atTop K)
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ h : X → ℝ,
          IsHarmonicOnSurface χ.chart.source h ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              f x + Real.log ‖χ.chart x - χ.chart p‖ = h x)
    (hzero : Filter.Tendsto f (Filter.cocompact X) (𝓝 0)) :
    BoundedNegativeGreenSubsequenceGreenLimit (p := p) (q := q) E B φ where
  subseq := ψ
  subseq_strictMono := hψ
  toFun := f
  positive_away_pole :=
    neg_boundedNegativeGreen_subsequence_limit_positive_away_pole_of_compact_convergence_and_logarithmic_singularity
      (E := E) (p := p) B (hφ.comp hψ) hconv hlog
  harmonic_away_pole :=
    neg_boundedNegativeGreen_subsequence_limit_harmonic_away_pole_of_compact_convergence
      (E := E) (p := p) B (hφ.comp hψ) hconv
  tends_to_infinity_at_pole :=
    neg_boundedNegativeGreen_subsequence_limit_tends_to_infinity_at_pole_of_logarithmic_singularity
      (X := X) (p := p) hlog
  logarithmic_singularity := hlog
  tends_to_zero_at_infinity := hzero
  compact_positive_superlevel :=
    neg_boundedNegativeGreen_subsequence_limit_compact_positive_superlevel_of_compact_convergence_and_zero_at_infinity
      (E := E) (p := p) B (hφ.comp hψ) hconv hzero
  locally_uniform_on_compacts_away_pole := hconv

/--
%%handwave
name:
  Assembling a bounded Green compact-local subsequence limit
statement:
  A compact-local subsequential limit of positive bounded-domain Green
  functions, together with logarithmic-pole asymptotics, determines a bounded
  Green compact-local subsequence limit.
proof:
  Compact-local convergence gives harmonicity and nonnegativity away from the
  pole.  The logarithmic-pole asymptotic gives blow-up at the pole, and the
  strong minimum principle upgrades nonnegativity to strict positivity.
-/
def boundedNegativeGreenSubsequenceCompactLimit_of_compact_convergence_and_logarithmic_singularity
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ ψ : ℕ → ℕ} (hφ : StrictMono φ) (hψ : StrictMono ψ) {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ -((B (φ (ψ k))).toFun x))
          f Filter.atTop K)
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ h : X → ℝ,
          IsHarmonicOnSurface χ.chart.source h ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              f x + Real.log ‖χ.chart x - χ.chart p‖ = h x) :
    BoundedNegativeGreenSubsequenceCompactLimit (p := p) (q := q) E B φ where
  subseq := ψ
  subseq_strictMono := hψ
  toFun := f
  positive_away_pole :=
    neg_boundedNegativeGreen_subsequence_limit_positive_away_pole_of_compact_convergence_and_logarithmic_singularity
      (E := E) (p := p) B (hφ.comp hψ) hconv hlog
  harmonic_away_pole :=
    neg_boundedNegativeGreen_subsequence_limit_harmonic_away_pole_of_compact_convergence
      (E := E) (p := p) B (hφ.comp hψ) hconv
  tends_to_infinity_at_pole :=
    neg_boundedNegativeGreen_subsequence_limit_tends_to_infinity_at_pole_of_logarithmic_singularity
      (X := X) (p := p) hlog
  logarithmic_singularity := hlog
  locally_uniform_on_compacts_away_pole := hconv

namespace BoundedNegativeGreenSubsequenceCompactLimit

/--
%%handwave
name:
  A compact-local bounded Green limit that vanishes at infinity is a Green
  limit
statement:
  If a bounded Green compact-local subsequence limit also tends to \(0\) at
  infinity, then it determines a bounded Green subsequence limit, hence a
  Green function with the same pole.
proof:
  Add the vanishing-at-infinity field.  Compactness of positive superlevel
  sets follows from compact-local convergence and vanishing at infinity.
-/
def toGreenLimitOfTendsToZero
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    {B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p}
    {φ : ℕ → ℕ}
    (L : BoundedNegativeGreenSubsequenceCompactLimit (p := p) (q := q) E B φ)
    (hφ : StrictMono φ)
    (hzero : Filter.Tendsto L.toFun (Filter.cocompact X) (𝓝 0)) :
    BoundedNegativeGreenSubsequenceGreenLimit (p := p) (q := q) E B φ :=
  boundedNegativeGreenSubsequenceGreenLimit_of_compact_convergence_and_asymptotics
    (E := E) (p := p) (q := q) B hφ L.subseq_strictMono
    L.locally_uniform_on_compacts_away_pole L.logarithmic_singularity hzero

end BoundedNegativeGreenSubsequenceCompactLimit

/--
%%handwave
name:
  Boundary bounds control logarithmic-zero remainders in a coordinate disk
statement:
  Let a harmonic function on a punctured surface region have a logarithmic
  zero at \(p\).  If a closed coordinate disk around \(p\) lies in the region
  and the logarithmically corrected function is bounded on the boundary
  circle, then the same bound holds throughout the punctured coordinate disk.
proof:
  In the coordinate, subtract the Euclidean logarithm.  The logarithmic-zero
  hypothesis gives a finite removable limit at the center, while harmonicity
  and continuity transfer to the punctured closed disk.  The punctured-disk
  maximum principle then propagates the boundary bound to the interior.
-/
theorem logarithmicZeroWithin_remainder_bound_on_pointed_coordinate_ball_of_frontier_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {U : Set X} {p : X} {u : X → ℝ}
    (hharm : IsHarmonicOnSurface (U \ {p}) u)
    (hcont : ContinuousOn u (closure U \ {p}))
    (hlog : HasLogarithmicZeroWithin X U p u)
    (χ : PointedSurfaceCoordinate X p) {R M : ℝ} (hR_pos : 0 < R)
    (hclosed_target : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target)
    (hclosed_U : Metric.closedBall (χ.chart p) R ⊆ χ.chart.symm ⁻¹' U)
    (hfront :
      ∀ z ∈ frontier (Metric.ball (χ.chart p) R),
        ‖u (χ.chart.symm z) -
          Real.log ‖z - χ.chart p‖‖ ≤ M) :
    ∀ x : X, x ∈ χ.chart.source → x ≠ p →
      ‖χ.chart x - χ.chart p‖ < R →
        ‖u x - Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M := by
  classical
  let c : ℂ := χ.chart p
  let f : ℂ → ℝ := fun z ↦ u (χ.chart.symm z) - Real.log ‖z - c‖
  have hc_target : c ∈ χ.chart.target := by
    dsimp [c]
    exact χ.chart.map_source χ.base_mem_source
  have hball_target : Metric.ball c R ⊆ χ.chart.target := by
    intro z hz
    exact hclosed_target (by simpa [c] using Metric.ball_subset_closedBall hz)
  have hsymm_ne_of_ne_c :
      ∀ {z : ℂ}, z ∈ χ.chart.target → z ≠ c → χ.chart.symm z ≠ p := by
    intro z hz_target hzc hsymm_eq
    have hz_eq_c : z = c := by
      calc
        z = χ.chart (χ.chart.symm z) := (χ.chart.right_inv hz_target).symm
        _ = χ.chart p := by rw [hsymm_eq]
        _ = c := rfl
    exact hzc hz_eq_c
  have hu_planar :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦ u (χ.chart.symm z)) (Metric.ball c R \ {c}) := by
    have hsurface := hharm χ.chart χ.chart_mem_atlas
    refine hsurface.mono ?_
    intro z hz
    have hz_ball : z ∈ Metric.ball c R := hz.1
    have hz_closed : z ∈ Metric.closedBall c R :=
      Metric.ball_subset_closedBall hz_ball
    have hz_target : z ∈ χ.chart.target := hclosed_target (by simpa [c] using hz_closed)
    have hzc : z ≠ c := by
      simpa [Set.mem_singleton_iff] using hz.2
    have hsymm_U : χ.chart.symm z ∈ U :=
      hclosed_U (by simpa [c] using hz_closed)
    have hsymm_ne : χ.chart.symm z ≠ p :=
      hsymm_ne_of_ne_c hz_target hzc
    exact ⟨hz_target, ⟨hsymm_U, by simpa [Set.mem_singleton_iff] using hsymm_ne⟩⟩
  have hf_harm :
      InnerProductSpace.HarmonicOnNhd f (Metric.ball c R \ {c}) := by
    simpa [f] using
      hu_planar.sub
        (complex_log_norm_sub_harmonicOn_punctured_ball (c := c) (r := R))
  rcases hlog χ with
    ⟨N, h, hN_open, hpN, _hNU, _hN_source, hharmN, heq⟩
  have hh_contAt : ContinuousAt h p :=
    (harmonicOnSurface_continuousOn hN_open hharmN).continuousAt
      (hN_open.mem_nhds hpN)
  have hh_tendsto : Filter.Tendsto h (𝓝 p) (𝓝 (h p)) := hh_contAt
  have hsymm_c : χ.chart.symm c = p := by
    simpa [c] using χ.chart.left_inv χ.base_mem_source
  have hsymm_tendsto_raw :
      Filter.Tendsto χ.chart.symm (𝓝 c) (𝓝 (χ.chart.symm c)) :=
    (χ.chart.continuousAt_symm hc_target)
  have hsymm_tendsto_nhds :
      Filter.Tendsto χ.chart.symm (𝓝 c) (𝓝 p) := by
    simpa [hsymm_c] using hsymm_tendsto_raw
  have hsymm_tendsto :
      Filter.Tendsto χ.chart.symm (𝓝[Metric.ball c R \ {c}] c) (𝓝 p) :=
    hsymm_tendsto_nhds.mono_left nhdsWithin_le_nhds
  have hh_comp_tendsto :
      Filter.Tendsto (fun z : ℂ ↦ h (χ.chart.symm z))
        (𝓝[Metric.ball c R \ {c}] c) (𝓝 (h p)) :=
    hh_tendsto.comp hsymm_tendsto
  let EqSet : Set X :=
    {x : X | x ∈ N ∩ {x : X | x ≠ p} →
      u x - Real.log ‖χ.chart x - χ.chart p‖ = h x}
  have hEqSet_nhds : EqSet ∈ 𝓝 p := by
    simpa [EqSet] using eventually_nhdsWithin_iff.mp heq
  have hpre_eq : χ.chart.symm ⁻¹' EqSet ∈ 𝓝 c :=
    hsymm_tendsto_nhds hEqSet_nhds
  have hpre_N : χ.chart.symm ⁻¹' N ∈ 𝓝 c :=
    hsymm_tendsto_nhds (hN_open.mem_nhds hpN)
  have hf_eq_h :
      f =ᶠ[𝓝[Metric.ball c R \ {c}] c]
        fun z : ℂ ↦ h (χ.chart.symm z) := by
    filter_upwards
      [mem_nhdsWithin_of_mem_nhds hpre_eq,
        mem_nhdsWithin_of_mem_nhds hpre_N,
        (self_mem_nhdsWithin :
          Metric.ball c R \ {c} ∈ 𝓝[Metric.ball c R \ {c}] c)] with
        z hzEq hzN hzpunct
    have hz_target : z ∈ χ.chart.target := hball_target hzpunct.1
    have hzc : z ≠ c := by
      simpa [Set.mem_singleton_iff] using hzpunct.2
    have hsymm_ne : χ.chart.symm z ≠ p :=
      hsymm_ne_of_ne_c hz_target hzc
    have hEq := hzEq ⟨hzN, hsymm_ne⟩
    simpa [f, c, χ.chart.right_inv hz_target] using hEq
  have hf_tendsto :
      Filter.Tendsto f (𝓝[Metric.ball c R \ {c}] c) (𝓝 (h p)) :=
    hh_comp_tendsto.congr' hf_eq_h.symm
  have hsymm_cont :
      ContinuousOn χ.chart.symm (Metric.closedBall c R \ {c}) := by
    exact χ.chart.continuousOn_symm.mono (by
      intro z hz
      exact hclosed_target (by simpa [c] using hz.1))
  have hmaps :
      Set.MapsTo χ.chart.symm (Metric.closedBall c R \ {c})
        (closure U \ {p}) := by
    intro z hz
    have hz_target : z ∈ χ.chart.target :=
      hclosed_target (by simpa [c] using hz.1)
    have hzc : z ≠ c := by
      simpa [Set.mem_singleton_iff] using hz.2
    have hsymm_ne : χ.chart.symm z ≠ p :=
      hsymm_ne_of_ne_c hz_target hzc
    exact ⟨subset_closure (hclosed_U (by simpa [c] using hz.1)),
      by simpa [Set.mem_singleton_iff] using hsymm_ne⟩
  have hu_cont_planar :
      ContinuousOn (fun z : ℂ ↦ u (χ.chart.symm z))
        (Metric.closedBall c R \ {c}) :=
    hcont.comp' hsymm_cont hmaps
  have hlog_cont :
      ContinuousOn (fun z : ℂ ↦ Real.log ‖z - c‖)
        (Metric.closedBall c R \ {c}) := by
    have hnorm_cont :
        ContinuousOn (fun z : ℂ ↦ ‖z - c‖)
          (Metric.closedBall c R \ {c}) :=
      (continuousOn_id.sub continuousOn_const).norm
    refine hnorm_cont.log ?_
    intro z hz
    have hzc : z ≠ c := by
      simpa [Set.mem_singleton_iff] using hz.2
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzc)
  have hf_cont :
      ContinuousOn f (Metric.closedBall c R \ {c}) := by
    simpa [f] using hu_cont_planar.sub hlog_cont
  have hfront_f :
      ∀ z ∈ frontier (Metric.ball c R), ‖f z‖ ≤ M := by
    intro z hz
    simpa [f, c] using hfront z (by simpa [c] using hz)
  have hpunct_bound :
      ∀ z ∈ Metric.ball c R \ {c}, ‖f z‖ ≤ M :=
    punctured_harmonicOn_complex_ball_norm_le_of_frontier_norm_le_of_tendsto
      hR_pos hf_harm hf_tendsto hf_cont hfront_f
  intro x hxsource hxne hxR
  have hx_ball : χ.chart x ∈ Metric.ball c R := by
    simpa [Metric.mem_ball, dist_eq_norm, c] using hxR
  have hx_chart_ne : χ.chart x ≠ c := by
    intro hx_chart
    exact hxne (χ.chart.injOn hxsource χ.base_mem_source (by simpa [c] using hx_chart))
  have hx_punct : χ.chart x ∈ Metric.ball c R \ {c} :=
    ⟨hx_ball, by simpa [Set.mem_singleton_iff] using hx_chart_ne⟩
  have hx_bound := hpunct_bound (χ.chart x) hx_punct
  simpa [f, c, χ.chart.left_inv hxsource] using hx_bound

/--
%%handwave
name:
  Bounded-height Green remainders are bounded on a fixed coordinate ball
statement:
  For bounded-domain negative Green potentials whose normalized outer heights
  stay below a fixed level, and for a coordinate at the pole, there is a
  smaller coordinate ball around the pole and a constant \(M\) such that all
  sufficiently late positive Green functions differ from the negative
  coordinate logarithm by at most \(M\) throughout the punctured ball.
proof:
  Choose a coordinate ball compactly contained in the first exhaustion
  domain.  The bounded normalization gives Harnack control for the positive
  Green functions on the outer coordinate circle.  On the annulus between
  the pole and that circle, compare with the coordinate logarithm and use the
  maximum principle to propagate the two-sided bound uniformly in the
  exhaustion parameter.
-/
theorem neg_boundedNegativeGreen_exhaustion_logarithmic_remainder_eventual_bound_on_pointed_coordinate_ball_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (hpq : q ≠ p)
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier)
    (_hq : ∀ n : ℕ, q ∈ (E.domain n).carrier)
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {A : ℝ}
    (hbound : ∀ n : ℕ, (B n).boundaryHeightAt q < A)
    (χ : PointedSurfaceCoordinate X p) :
    ∃ R M : ℝ, 0 < R ∧
      Metric.closedBall (χ.chart p) R ⊆ χ.chart.target ∧
      (∀ x : X, x ∈ χ.chart.source →
        ‖χ.chart x - χ.chart p‖ < R → x ∈ (E.domain 0).carrier) ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x : X, x ∈ χ.chart.source → x ≠ p →
          ‖χ.chart x - χ.chart p‖ < R →
            ‖-((B n).toFun x) +
              Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M := by
  classical
  let c : ℂ := χ.chart p
  have hc_target : c ∈ χ.chart.target := by
    dsimp [c]
    exact χ.chart.map_source χ.base_mem_source
  have htarget_nhds : χ.chart.target ∈ 𝓝 c :=
    χ.chart.open_target.mem_nhds hc_target
  have hdomain0_nhds : (E.domain 0).carrier ∈ 𝓝 p :=
    (E.domain 0).isOpen.mem_nhds (hp 0)
  have hsymm_c : χ.chart.symm c = p := by
    simpa [c] using χ.chart.left_inv χ.base_mem_source
  have hdomain0_at_symm : (E.domain 0).carrier ∈ 𝓝 (χ.chart.symm c) := by
    simpa [hsymm_c] using hdomain0_nhds
  have hdomain0_map :
      (E.domain 0).carrier ∈ Filter.map χ.chart.symm (𝓝 c) :=
    χ.chart.continuousAt_symm hc_target hdomain0_at_symm
  have hdomain0_pre :
      χ.chart.symm ⁻¹' (E.domain 0).carrier ∈ 𝓝 c := by
    simpa [Filter.mem_map] using hdomain0_map
  rcases Metric.mem_nhds_iff.mp
      (Filter.inter_mem htarget_nhds hdomain0_pre) with
    ⟨R₀, hR₀_pos, hball_target_domain0⟩
  let R : ℝ := R₀ / 2
  have hR_pos : 0 < R := by
    dsimp [R]
    linarith
  have hR_lt_R₀ : R < R₀ := by
    dsimp [R]
    linarith
  have hclosed_target_domain0 :
      Metric.closedBall c R ⊆
        χ.chart.target ∩ χ.chart.symm ⁻¹' (E.domain 0).carrier :=
    (Metric.closedBall_subset_ball hR_lt_R₀).trans hball_target_domain0
  have hclosed_target :
      Metric.closedBall (χ.chart p) R ⊆ χ.chart.target := by
    intro z hz
    exact (hclosed_target_domain0 (by simpa [c] using hz)).1
  have hclosed_domain0 :
      Metric.closedBall (χ.chart p) R ⊆
        χ.chart.symm ⁻¹' (E.domain 0).carrier := by
    intro z hz
    exact (hclosed_target_domain0 (by simpa [c] using hz)).2
  have hball_domain :
      ∀ x : X, x ∈ χ.chart.source →
        ‖χ.chart x - χ.chart p‖ < R → x ∈ (E.domain 0).carrier := by
    intro x hxsource hxR
    have hx_closed : χ.chart x ∈ Metric.closedBall (χ.chart p) R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_lt hxR
    have hsymm_domain : χ.chart.symm (χ.chart x) ∈ (E.domain 0).carrier :=
      hclosed_domain0 hx_closed
    simpa [χ.chart.left_inv hxsource] using hsymm_domain
  let K : Set X := χ.chart.symm '' Metric.sphere c R
  have hsphere_target : Metric.sphere c R ⊆ χ.chart.target := by
    intro z hz
    have hz_closed : z ∈ Metric.closedBall c R :=
      Metric.sphere_subset_closedBall hz
    exact (hclosed_target_domain0 hz_closed).1
  have hK_compact : IsCompact K :=
    (isCompact_sphere c R).image_of_continuousOn
      (χ.chart.continuousOn_symm.mono hsphere_target)
  have hK_nonempty : K.Nonempty := by
    rcases (NormedSpace.sphere_nonempty (x := c) (r := R)).mpr hR_pos.le with
      ⟨z, hz⟩
    exact ⟨χ.chart.symm z, ⟨z, hz, rfl⟩⟩
  have hK_punctured : K ⊆ {x : X | x ≠ p} := by
    intro x hxK
    rcases hxK with ⟨z, hz_sphere, rfl⟩
    have hz_target : z ∈ χ.chart.target := hsphere_target hz_sphere
    have hzc : z ≠ c := Metric.ne_of_mem_sphere hz_sphere hR_pos.ne'
    intro hsymm_eq
    have hz_eq_c : z = c := by
      calc
        z = χ.chart (χ.chart.symm z) := (χ.chart.right_inv hz_target).symm
        _ = χ.chart p := by rw [hsymm_eq]
        _ = c := rfl
    exact hzc hz_eq_c
  rcases
    neg_boundedNegativeGreen_exhaustion_eventual_uniform_bound_on_compact_away_pole_of_boundaryHeight_bound
      (E := E) (p := p) (q := q) B hpq hbound
      hK_compact hK_nonempty hK_punctured with
    ⟨M₀, hM₀⟩
  let M : ℝ := M₀ + ‖Real.log R‖
  refine ⟨R, M, hR_pos, hclosed_target, hball_domain, ?_⟩
  filter_upwards [hM₀] with n hn
  have hclosed_domain_n :
      Metric.closedBall (χ.chart p) R ⊆
        χ.chart.symm ⁻¹' (E.domain n).carrier := by
    intro z hz
    exact E.carrier_mono (Nat.zero_le n) (hclosed_domain0 hz)
  have hfront :
      ∀ z ∈ frontier (Metric.ball (χ.chart p) R),
        ‖(B n).toFun (χ.chart.symm z) -
          Real.log ‖z - χ.chart p‖‖ ≤ M := by
    intro z hz
    have hz_sphere : z ∈ Metric.sphere c R := by
      simpa [c, frontier_ball c hR_pos.ne'] using hz
    have hxK : χ.chart.symm z ∈ K := ⟨z, hz_sphere, rfl⟩
    have hupper_neg : -((B n).toFun (χ.chart.symm z)) ≤ M₀ :=
      hn (χ.chart.symm z) hxK
    have hz_closed : z ∈ Metric.closedBall (χ.chart p) R := by
      exact Metric.sphere_subset_closedBall (by simpa [c] using hz_sphere)
    have hx_domain : χ.chart.symm z ∈ (E.domain n).carrier :=
      hclosed_domain_n hz_closed
    have hnonpos :
        (B n).toFun (χ.chart.symm z) ≤ 0 :=
      (B n).nonpositive_on_domain (χ.chart.symm z) hx_domain
    have hnorm_toFun :
        ‖(B n).toFun (χ.chart.symm z)‖ ≤ M₀ := by
      have hnorm_eq :
          ‖(B n).toFun (χ.chart.symm z)‖ =
            -((B n).toFun (χ.chart.symm z)) := by
        simpa [Real.norm_eq_abs] using
          (abs_of_nonpos hnonpos :
            |(B n).toFun (χ.chart.symm z)| =
              -((B n).toFun (χ.chart.symm z)))
      rw [hnorm_eq]
      exact hupper_neg
    have hnorm_eq : ‖z - χ.chart p‖ = R := by
      simpa [c] using hz_sphere
    calc
      ‖(B n).toFun (χ.chart.symm z) -
          Real.log ‖z - χ.chart p‖‖
          = ‖(B n).toFun (χ.chart.symm z) - Real.log R‖ := by
              rw [hnorm_eq]
      _ ≤ ‖(B n).toFun (χ.chart.symm z)‖ + ‖Real.log R‖ :=
          norm_sub_le _ _
      _ ≤ M := by
          simpa [M, add_comm, add_left_comm, add_assoc] using
            add_le_add_right hnorm_toFun ‖Real.log R‖
  intro x hxsource hxne hxR
  have hzero_bound :
      ‖(B n).toFun x -
        Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M :=
    logarithmicZeroWithin_remainder_bound_on_pointed_coordinate_ball_of_frontier_bound
      (U := (E.domain n).carrier) (p := p)
      (u := (B n).toFun)
      (B n).harmonic_away_pole
      (B n).continuousOn_punctured_closure (B n).logarithmic_zero
      χ hR_pos hclosed_target hclosed_domain_n hfront
      x hxsource hxne hxR
  have hnorm_flip :
      ‖-((B n).toFun x) +
          Real.log ‖χ.chart x - χ.chart p‖‖ =
        ‖(B n).toFun x -
          Real.log ‖χ.chart x - χ.chart p‖‖ := by
    have hneg :
        -((B n).toFun x) + Real.log ‖χ.chart x - χ.chart p‖ =
          -((B n).toFun x -
            Real.log ‖χ.chart x - χ.chart p‖) := by
      ring
    rw [hneg, norm_neg]
  simpa [hnorm_flip] using hzero_bound

/--
%%handwave
name:
  Bounded-height Green remainders are uniformly bounded
statement:
  For a bounded-height sequence of positive bounded-domain Green functions, in
  every coordinate at the pole the logarithmically corrected remainders are
  bounded by one constant near the pole, uniformly for all sufficiently late
  functions.
proof:
  The bounded normalization gives Harnack control for the positive Green
  functions on punctured coordinate annuli.  Comparing with the coordinate
  logarithm gives a uniform two-sided bound for the corrected remainders on a
  sufficiently small punctured coordinate neighborhood.
-/
theorem neg_boundedNegativeGreen_exhaustion_logarithmic_remainder_eventual_local_bound_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (hpq : q ≠ p)
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier)
    (hq : ∀ n : ℕ, q ∈ (E.domain n).carrier)
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {A : ℝ}
    (hbound : ∀ n : ℕ, (B n).boundaryHeightAt q < A) :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ M : ℝ,
        ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
          ∀ᶠ n : ℕ in Filter.atTop,
            ‖-((B n).toFun x) +
              Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M := by
  intro χ
  rcases
    neg_boundedNegativeGreen_exhaustion_logarithmic_remainder_eventual_bound_on_pointed_coordinate_ball_of_boundaryHeight_bound
      (E := E) (p := p) (q := q) hpq hp hq B hbound χ with
    ⟨R, M, hR_pos, _hclosed, _hball_domain, hbound_ball⟩
  refine ⟨M, ?_⟩
  filter_upwards
    [pointedCoordinate_eventually_mem_inner_ball X χ χ hR_pos,
      self_mem_nhdsWithin] with x hxsmall hxpunct
  filter_upwards [hbound_ball] with n hn
  exact hn x hxsmall.1 hxpunct.2 hxsmall.2

/--
%%handwave
name:
  Bounded-height Green remainders are uniformly bounded along one subsequence
statement:
  For a bounded-height subsequence of positive bounded-domain Green
  functions, in every coordinate at the pole the logarithmically corrected
  remainders are bounded by one constant near the pole, uniformly for all
  sufficiently late members of that subsequence.
proof:
  The bounded normalization gives Harnack control for the positive Green
  functions on punctured coordinate annuli.  Comparing with the coordinate
  logarithm gives a uniform two-sided bound for the corrected remainders on a
  sufficiently small punctured coordinate neighborhood.
-/
theorem neg_boundedNegativeGreen_subsequence_logarithmic_remainder_eventual_local_bound_of_boundaryHeight_bound_base
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (hpq : q ≠ p)
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier)
    (hq : ∀ n : ℕ, q ∈ (E.domain n).carrier)
      (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
      {A : ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
      (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A) :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ M : ℝ,
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            ∀ᶠ k : ℕ in Filter.atTop,
              ‖-((B (φ k)).toFun x) +
                Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M := by
    intro χ
    let Eφ : SmoothRelativelyCompactExhaustion X := E.compStrictMono φ hφ
    let Bφ : (n : ℕ) → BoundedNegativeGreenPotential X (Eφ.domain n) p :=
      fun n ↦ B (φ n)
    have hpφ : ∀ n : ℕ, p ∈ (Eφ.domain n).carrier := by
      intro n
      simpa [Eφ] using hp (φ n)
    have hqφ : ∀ n : ℕ, q ∈ (Eφ.domain n).carrier := by
      intro n
      simpa [Eφ] using hq (φ n)
    have hboundφ : ∀ n : ℕ, (Bφ n).boundaryHeightAt q < A := by
      intro n
      simpa [Bφ] using hbound n
    rcases
      neg_boundedNegativeGreen_exhaustion_logarithmic_remainder_eventual_local_bound_of_boundaryHeight_bound
        (E := Eφ) (p := p) (q := q) hpq hpφ hqφ Bφ hboundφ χ with
      ⟨M, hM⟩
    exact ⟨M, by simpa [Bφ] using hM⟩

/--
%%handwave
name:
  Bounded-height Green remainders are uniformly bounded before taking limits
statement:
  For a bounded-height subsequence of positive bounded-domain Green functions,
  in every coordinate at the pole the logarithmically corrected remainders are
  bounded by one constant near the pole, uniformly for all sufficiently late
  members of any further subsequence.
proof:
  Apply the one-subsequence estimate to the composed subsequence.  The
  bounded-height hypothesis is inherited by composition.
-/
theorem neg_boundedNegativeGreen_subsequence_logarithmic_remainder_eventual_local_bound_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (hpq : q ≠ p)
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier)
    (hq : ∀ n : ℕ, q ∈ (E.domain n).carrier)
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {A : ℝ} {φ ψ : ℕ → ℕ} (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A) :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ M : ℝ,
        ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
          ∀ᶠ k : ℕ in Filter.atTop,
            ‖-((B (φ (ψ k))).toFun x) +
              Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M := by
  intro χ
  have hbound_comp :
      ∀ k : ℕ, (B ((φ ∘ ψ) k)).boundaryHeightAt q < A := fun k ↦ hbound (ψ k)
  rcases
    neg_boundedNegativeGreen_subsequence_logarithmic_remainder_eventual_local_bound_of_boundaryHeight_bound_base
      (E := E) (p := p) (q := q) hpq hp hq B (hφ.comp hψ) hbound_comp χ with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  filter_upwards [hM] with x hxM
  filter_upwards [hxM] with k hk
  simpa [Function.comp] using hk

/--
%%handwave
name:
  Bounded-height logarithmic remainders are locally bounded
statement:
  For a bounded-height subsequential limit of positive bounded-domain Green
  functions, adding the coordinate logarithm gives a locally bounded
  punctured-harmonic remainder near the pole.
proof:
  The bounded normalization gives uniform Harnack control for the harmonic
  remainders obtained by adding the coordinate logarithm to the positive
  Green functions.  Compact-local convergence passes this local bound to the
  limiting remainder.
-/
theorem neg_boundedNegativeGreen_subsequence_limit_logarithmic_remainder_locally_bounded_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (hpq : q ≠ p)
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier)
    (hq : ∀ n : ℕ, q ∈ (E.domain n).carrier)
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {A : ℝ} {φ ψ : ℕ → ℕ} (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A)
    {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ -((B (φ (ψ k))).toFun x))
          f Filter.atTop K) :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ M : ℝ,
        ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
          ‖f x + Real.log ‖χ.chart x - χ.chart p‖‖ ≤ M := by
  intro χ
  rcases
    neg_boundedNegativeGreen_subsequence_logarithmic_remainder_eventual_local_bound_of_boundaryHeight_bound
      (E := E) (p := p) (q := q) hpq hp hq B hφ hψ hbound χ with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  filter_upwards [hM, self_mem_nhdsWithin] with x hxM hx
  have hx_ne : x ≠ p := hx.2
  have hconv_single :
      TendstoUniformlyOn
        (fun k : ℕ ↦ fun y : X ↦ -((B (φ (ψ k))).toFun y))
        f Filter.atTop ({x} : Set X) :=
    hconv ({x} : Set X) (isCompact_singleton (x := x))
      (by
        intro y hy
        simpa [Set.mem_singleton_iff.mp hy] using hx_ne)
  exact
    tendstoUniformlyOn_pointwise_norm_add_const_le_of_eventually
      (K := ({x} : Set X))
      (F := fun k : ℕ ↦ fun y : X ↦ -((B (φ (ψ k))).toFun y))
      (f := f) (x := x)
      (c := Real.log ‖χ.chart x - χ.chart p‖) (M := M)
      (by simp) hconv_single hxM

/--
%%handwave
name:
  Bounded-height limits retain the logarithmic pole
statement:
  Let positive bounded-domain Green functions on an exhaustion have bounded
  normalized heights along a subsequence and converge locally uniformly away
  from the pole.  Then the limit has the same removable logarithmic pole at
  the pole.
proof:
  In a coordinate disk around the pole, subtract the explicit logarithmic
  singularity from each approximating Green function.  The height bound gives
  uniform Harnack control for these harmonic remainders on smaller disks, so
  a harmonic limit extends across the pole and gives the stated removable
  logarithmic model.
-/
theorem neg_boundedNegativeGreen_subsequence_limit_logarithmic_singularity_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (hpq : q ≠ p)
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier)
    (hq : ∀ n : ℕ, q ∈ (E.domain n).carrier)
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {A : ℝ} {φ ψ : ℕ → ℕ} (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A)
    {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ fun x : X ↦ -((B (φ (ψ k))).toFun x))
          f Filter.atTop K) :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ h : X → ℝ,
        IsHarmonicOnSurface χ.chart.source h ∧
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            f x + Real.log ‖χ.chart x - χ.chart p‖ = h x := by
    have hharm :
        IsHarmonicOnSurface {x : X | x ≠ p} f :=
      neg_boundedNegativeGreen_subsequence_limit_harmonic_away_pole_of_compact_convergence
        (E := E) (p := p) B (hφ.comp hψ) hconv
    exact logarithmic_singularity_of_harmonicOn_punctured_and_bounded_remainder
      hharm
      (neg_boundedNegativeGreen_subsequence_limit_logarithmic_remainder_locally_bounded_of_boundaryHeight_bound
        (E := E) (p := p) (q := q) hpq hp hq B hφ hψ hbound hconv)

/--
%%handwave
name:
  Positive moving-boundary values occur only in genuine collars
statement:
  If a later positive bounded Green function is strictly positive on the
  \(j\)-th exhaustion boundary, then its outer index is strictly larger than
  \(j\).
proof:
  If the outer index were \(j\), the point would lie on the outer boundary of
  that bounded Green problem, where the Green potential has boundary value
  zero.  This contradicts strict positivity.
-/
theorem neg_boundedNegativeGreen_exhaustion_selected_boundary_superlevel_strict_outer
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (_hpq : q ≠ p)
    (_hp : ∀ n : ℕ, p ∈ (E.domain n).carrier)
    (_hq : ∀ n : ℕ, q ∈ (E.domain n).carrier)
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {ε : ℝ}
    (hε : 0 < ε)
    (μ : ℕ → ℕ) (hμ_late : ∀ j : ℕ, j ≤ μ j)
    (y : ℕ → X)
    (hboundary : ∀ j : ℕ, y j ∈ (E.domain j).boundary)
    (hsuper : ∀ j : ℕ, ε < -((B (μ j)).toFun (y j))) :
    ∀ j : ℕ, j < μ j := by
  intro j
  refine lt_of_le_of_ne (hμ_late j) ?_
  intro h_eq
  have hzero : (B (μ j)).toFun (y j) = 0 := by
    rw [← h_eq]
    exact (B j).boundary_zero (y j) (hboundary j)
  have hlt_zero : ε < 0 := by
    simpa [hzero] using hsuper j
  exact (not_lt_of_ge hε.le) hlt_zero

/--
%%handwave
name:
  Bounded selected positive Green functions have uniform compact Harnack bounds
statement:
  Let \(E=(\Omega_n)\) be a smooth relatively compact exhaustion of a
  Riemann surface, and let \(p\ne q\), with both points lying in
  every \(\Omega_n\).  Let \(\beta_k\to+\infty\), and for each \(k\) let
  \(G_k\) be a bounded-domain negative Green potential on
  \(\Omega_{\beta_k}\) with pole \(p\).  If the normalized heights
  \(H_k=-G_k(q)\) satisfy \(H_k<A\) for all \(k\), then for every nonempty
  compact set \(K\subset X\setminus\{p\}\) there is a constant \(M\) such that
  for all sufficiently large \(k\),
  \[
    -G_k(x)\le M\qquad\text{for every }x\in K .
  \]
proof:
  Choose a relatively compact preconnected open set \(U\subset X\setminus\{p\}\)
  containing \(K\) and \(q\).  Since \(\beta_k\to+\infty\), the closures of
  \(U\) eventually lie in the domains \(\Omega_{\beta_k}\), so the functions
  \(u_k=-G_k\) are eventually nonnegative and harmonic on \(U\).  The height
  bound says \(u_k(q)=H_k<A\).  Local pairwise Harnack inequalities propagate
  this one-point bound from \(q\) through the preconnected region \(U\); a
  finite subcover of \(K\) gives a single upper bound on \(K\).

  Equivalently, if no such \(M\) existed, choose a further sequence
  \(k_j\to\infty\) with \(\beta_{k_j}\) strictly increasing and with values on
  \(K\) tending to \(+\infty\).  After reindexing the exhaustion by the
  strictly increasing outer indices \(\beta_{k_j}\), this contradicts [bounded normalized heights give uniform bounds on compact subsets of a preconnected punctured region](lean:JJMath.Uniformization.neg_boundedNegativeGreen_subsequence_eventual_uniform_bound_on_compact_of_boundaryHeight_bound).
-/
theorem neg_boundedNegativeGreen_selected_eventual_uniform_bound_on_compact_away_pole_of_boundaryHeight_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (hpq : q ≠ p)
    (_hp : ∀ n : ℕ, p ∈ (E.domain n).carrier)
    (_hq : ∀ n : ℕ, q ∈ (E.domain n).carrier)
    {A : ℝ} {β : ℕ → ℕ}
    (hβ : Filter.Tendsto β Filter.atTop Filter.atTop)
    (G : (k : ℕ) → BoundedNegativeGreenPotential X (E.domain (β k)) p)
    (hheight : ∀ k : ℕ, (G k).boundaryHeightAt q < A)
    {K : Set X}
    (hK_compact : IsCompact K)
    (hK_nonempty : K.Nonempty)
    (hK_punctured : K ⊆ {x : X | x ≠ p}) :
    ∃ M : ℝ,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x ∈ K, -((G k).toFun x) ≤ M := by
  classical
  let W : K → Set X := fun x =>
    Classical.choose
      (exists_preconnected_relativelyCompact_punctured_neighborhood_pair
        (X := X) (p := p) (q := q) (x := x.1) hpq (hK_punctured x.2))
  have hW_spec :
      ∀ x : K,
        IsOpen (W x) ∧ IsPreconnected (W x) ∧
          IsCompact (closure (W x)) ∧
            closure (W x) ⊆ {y : X | y ≠ p} ∧ q ∈ W x ∧ x.1 ∈ W x := by
    intro x
    exact
      Classical.choose_spec
        (exists_preconnected_relativelyCompact_punctured_neighborhood_pair
          (X := X) (p := p) (q := q) (x := x.1) hpq (hK_punctured x.2))
  have hcover : K ⊆ ⋃ x : K, W x := by
    intro x hxK
    exact Set.mem_iUnion.mpr
      ⟨⟨x, hxK⟩, (hW_spec ⟨x, hxK⟩).2.2.2.2.2⟩
  rcases hK_compact.elim_finite_subcover W
      (fun x ↦ (hW_spec x).1) hcover with
    ⟨t, ht⟩
  rcases hK_nonempty with ⟨x0, hx0K⟩
  let x0K : K := ⟨x0, hx0K⟩
  let t' : Finset K := insert x0K t
  let U : Set X := ⋃ x ∈ t', W x
  have hclosure_eq : closure U = ⋃ x ∈ t', closure (W x) := by
    simpa [U] using (Finset.closure_biUnion t' W)
  have hU_open : IsOpen U := by
    dsimp [U]
    exact isOpen_iUnion fun x ↦ isOpen_iUnion fun _ ↦ (hW_spec x).1
  have hU_preconnected : IsPreconnected U := by
    let C : Set (Set X) := W '' (↑t' : Set K)
    have hqC : ∀ V ∈ C, q ∈ V := by
      rintro V ⟨x, _hxt, rfl⟩
      exact (hW_spec x).2.2.2.2.1
    have hpreC : ∀ V ∈ C, IsPreconnected V := by
      rintro V ⟨x, _hxt, rfl⟩
      exact (hW_spec x).2.1
    have hpre : IsPreconnected (⋃₀ C) :=
      isPreconnected_sUnion q C hqC hpreC
    have hU_eq : U = ⋃₀ C := by
      ext z
      constructor
      · intro hz
        rcases Set.mem_iUnion₂.mp hz with ⟨x, hxt, hzW⟩
        exact ⟨W x, ⟨x, hxt, rfl⟩, hzW⟩
      · intro hz
        rcases hz with ⟨V, hVC, hzV⟩
        rcases hVC with ⟨x, hxt, rfl⟩
        exact Set.mem_iUnion₂.mpr ⟨x, hxt, hzV⟩
    simpa [hU_eq] using hpre
  have hU_compact_closure : IsCompact (closure U) := by
    have hcompact : IsCompact (⋃ x ∈ t', closure (W x)) :=
      t'.isCompact_biUnion fun x _ ↦ (hW_spec x).2.2.1
    simpa [hclosure_eq] using hcompact
  have hU_punctured_closure : closure U ⊆ {x : X | x ≠ p} := by
    intro x hx
    rw [hclosure_eq] at hx
    rcases Set.mem_iUnion₂.mp hx with ⟨y, _hyt, hxy⟩
    exact (hW_spec y).2.2.2.1 hxy
  have hKU : K ⊆ U := by
    intro x hxK
    rcases Set.mem_iUnion₂.mp (ht hxK) with ⟨y, hyt, hxy⟩
    exact Set.mem_iUnion₂.mpr
      ⟨y, Finset.mem_insert.mpr (Or.inr hyt), hxy⟩
  have hqU : q ∈ U := by
    exact Set.mem_iUnion₂.mpr
      ⟨x0K, Finset.mem_insert_self x0K t, (hW_spec x0K).2.2.2.2.1⟩
  have hU_event :
      ∀ᶠ k : ℕ in Filter.atTop, closure U ⊆ (E.domain (β k)).carrier := by
    exact hβ.eventually (E.eventually_compact_subset_domain hU_compact_closure)
  refine
    eventual_uniform_upper_bound_on_compact_propagates_of_local_pair_harnack_control
      hU_preconnected hK_compact hKU ?_ hqU ?_
  · intro x hxU
    rcases local_harnack_pair_control_for_nonnegative_harmonic_function
        (X := X) hU_open hxU with
      ⟨N, hN_nhds, hN_subset, C, hC_pos, hcontrol⟩
    refine ⟨N, hN_nhds, hN_subset, C, hC_pos.le, ?_⟩
    filter_upwards [hU_event] with k hU_domain y hyN z hzN
    let u : X → ℝ := fun w ↦ -((G k).toFun w)
    have hu_harm : IsHarmonicOnSurface U u := by
      have hG_harm : IsHarmonicOnSurface U (G k).toFun :=
        harmonicOnSurface_mono
          (U := U) (V := (E.domain (β k)).carrier \ {p})
          (by
            intro w hwU
            exact ⟨hU_domain (subset_closure hwU),
              hU_punctured_closure (subset_closure hwU)⟩)
          (G k).harmonic_away_pole
      exact harmonicOnSurface_neg hG_harm
    have hu_nonneg : ∀ w ∈ U, 0 ≤ u w := by
      intro w hwU
      exact neg_nonneg.mpr
        ((G k).nonpositive_on_domain w (hU_domain (subset_closure hwU)))
    exact hcontrol hu_harm hu_nonneg y hyN z hzN
  · refine ⟨A, ?_⟩
    exact Filter.Eventually.of_forall fun k ↦
      le_of_lt (by
        simpa [BoundedNegativeGreenPotential.boundaryHeightAt] using hheight k)

/--
%%handwave
name:
  Exterior smallness forbids escaping positive selected superlevels
statement:
  Let \(E=(\Omega_n)\) be a smooth relatively compact exhaustion, let
  \(\beta_j\) be selected outer indices, and let \(G_j\) be bounded-domain
  negative Green potentials on \(\Omega_{\beta_j}\) with pole \(p\).  Suppose
  that for the positive level \(\varepsilon\) there is a compact set
  \(K\subset X\), containing \(p\), such that for all sufficiently large \(j\),
  \[
    z\in\Omega_{\beta_j},\quad z\notin K
    \quad\Longrightarrow\quad
    -G_j(z)<\varepsilon .
  \]
  Then no sequence \(x_j\in\Omega_{\beta_j}\) escaping every compact set
  containing \(p\) can satisfy
  \[
    \varepsilon<-G_j(x_j)
  \]
  for every \(j\).
proof:
  The points \(x_j\) eventually lie in their selected domains and eventually
  leave the compact exceptional set \(K\).  On that same tail the exterior
  smallness estimate gives \(-G_j(x_j)<\varepsilon\), contradicting the
  assumed strict lower bound \(\varepsilon<-G_j(x_j)\).
-/
theorem neg_boundedNegativeGreen_selected_no_escaping_positive_superlevel_of_eventual_exterior_small
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p : X}
    {β : ℕ → ℕ}
    (G : (j : ℕ) → BoundedNegativeGreenPotential X (E.domain (β j)) p)
    {ε : ℝ}
    (_hε : 0 < ε)
    (hsmall :
      ∃ K : Set X, IsCompact K ∧ p ∈ K ∧
        ∀ᶠ j : ℕ in Filter.atTop,
          ∀ z : X, z ∈ (E.domain (β j)).carrier →
            z ∉ K → -((G j).toFun z) < ε)
    (x : ℕ → X)
    (_hdomain :
      ∀ᶠ j : ℕ in Filter.atTop, x j ∈ (E.domain (β j)).carrier)
    (_hescape :
      ∀ K : Set X, IsCompact K → p ∈ K →
        ∀ᶠ j : ℕ in Filter.atTop, x j ∉ K)
    (_hsuper : ∀ j : ℕ, ε < -((G j).toFun (x j))) :
    False := by
  rcases hsmall with ⟨K, hK_compact, hpK, hsmall_event⟩
  have hfalse : ∀ᶠ j : ℕ in Filter.atTop, False := by
    filter_upwards [_hdomain, _hescape K hK_compact hpK, hsmall_event] with
      j hx_domain hx_escape hsmall_j
    exact (not_lt_of_ge (le_of_lt (_hsuper j)))
      (hsmall_j (x j) hx_domain hx_escape)
  rcases Filter.eventually_atTop.mp hfalse with ⟨N, hN⟩
  exact hN N le_rfl



















































/--
%%handwave
name:
  Bounded Green subsequences have compact-local logarithmic limits
statement:
  If bounded-domain negative Green potentials along an exhaustion have
  uniformly bounded normalized outer heights along a subsequence, then the
  associated positive Green functions have a compact-local subsequential
  limit away from the pole, with the logarithmic-pole asymptotic.  No
  behavior at infinity is asserted here.
proof:
  Harnack compactness gives the compact-local limit on compact subsets away
  from the pole.  The local logarithmic models pass through this convergence
  near the pole.
-/
theorem boundedNegativeGreen_bounded_subsequence_extracts_compactLimit
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (hpq : q ≠ p)
    (hp : ∀ n : ℕ, p ∈ (E.domain n).carrier)
    (hq : ∀ n : ℕ, q ∈ (E.domain n).carrier)
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    (A : ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hbound : ∀ k : ℕ, (B (φ k)).boundaryHeightAt q < A) :
    Nonempty
      (BoundedNegativeGreenSubsequenceCompactLimit (p := p) (q := q) E B φ) := by
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  rcases
    neg_boundedNegativeGreen_subsequence_extracts_compact_convergence_away_pole_of_boundaryHeight_bound
      (E := E) (p := p) (q := q) B hφ hpq hbound with
    ⟨ψ, hψ, f, hconv⟩
  have hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ h : X → ℝ,
          IsHarmonicOnSurface χ.chart.source h ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              f x + Real.log ‖χ.chart x - χ.chart p‖ = h x :=
    neg_boundedNegativeGreen_subsequence_limit_logarithmic_singularity_of_boundaryHeight_bound
      (E := E) (p := p) (q := q) hpq hp hq B hφ hψ hbound hconv
  exact ⟨
    boundedNegativeGreenSubsequenceCompactLimit_of_compact_convergence_and_logarithmic_singularity
      (E := E) (p := p) (q := q) B hφ hψ hconv hlog⟩




/--
%%handwave
name:
  Centered Green exhaustion Evans limit
statement:
  A centered Green exhaustion Evans limit is a subsequential locally uniform
  limit, on compact subsets away from the pole, of centered bounded-domain
  negative Green potentials whose boundary heights diverge.  The limit is
  harmonic off the pole, has the logarithmic zero at the pole, tends to
  \(+\infty\) at infinity, and has compact sublevel sets after adjoining the
  pole.
-/
structure CenteredBoundedNegativeGreenEvansLimit
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p) where
  /-- The selected exhaustion subsequence. -/
  subseq : ℕ → ℕ
  /-- The selected subsequence is strictly increasing. -/
  subseq_strictMono : StrictMono subseq
  /-- The limiting Evans potential. -/
  toFun : X → ℝ
  /-- The limit is harmonic on the punctured surface. -/
  harmonic_away_pole : IsHarmonicOnSurface {x : X | x ≠ p} toFun
  /-- The limit tends to \(-\infty\) at its logarithmic zero. -/
  tends_to_neg_infinity_at_pole :
    Filter.Tendsto toFun (𝓝[≠] p) Filter.atBot
  /-- The logarithmic singularity at the pole is removable in every coordinate. -/
  logarithmic_zero :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ h : X → ℝ,
        IsHarmonicOnSurface χ.chart.source h ∧
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            toFun x - Real.log ‖χ.chart x - χ.chart p‖ = h x
  /-- The limit tends to \(+\infty\) along the ends of the surface. -/
  tends_to_infinity_at_infinity :
    Filter.Tendsto toFun (Filter.cocompact X) Filter.atTop
  /-- The sublevel sets are compact after adjoining the logarithmic zero. -/
  compact_sublevel_with_zero :
    ∀ a : ℝ, IsCompact ({p} ∪ {x : X | toFun x ≤ a})
  /-- The centered bounded-domain Green potentials converge on compact sets away from the pole. -/
  locally_uniform_on_compacts_away_pole :
    ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
      TendstoUniformlyOn
        (fun k : ℕ ↦ (B (subseq k)).centeredAt q) toFun Filter.atTop K

namespace CenteredBoundedNegativeGreenEvansLimit

/--
%%handwave
name:
  Centered Green exhaustion limits are Evans potentials
statement:
  Every centered Green exhaustion Evans limit determines an Evans potential
  with the same logarithmic zero.
proof:
  The fields of the exhaustion limit are exactly the harmonicity, logarithmic
  zero, growth at infinity, and compact-sublevel requirements in the
  definition of an Evans potential.
-/
def toEvansPotentialAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    {B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p}
    (L : CenteredBoundedNegativeGreenEvansLimit (p := p) (q := q) E B) :
    EvansPotentialAt X p where
  toFun := L.toFun
  harmonic_away_pole := L.harmonic_away_pole
  tends_to_neg_infinity_at_pole := L.tends_to_neg_infinity_at_pole
  logarithmic_zero := L.logarithmic_zero
  tends_to_infinity_at_infinity := L.tends_to_infinity_at_infinity
  compact_sublevel_with_zero := L.compact_sublevel_with_zero

end CenteredBoundedNegativeGreenEvansLimit

/--
%%handwave
name:
  Assembling a centered Green exhaustion Evans limit
statement:
  A compact-local subsequential limit of centered bounded-domain Green
  potentials, together with logarithmic-zero asymptotics and growth at
  infinity, determines an Evans exhaustion limit.
proof:
  Compact-local convergence gives harmonicity on the punctured surface.  The
  logarithmic-zero asymptotic gives decay to \(-\infty\) at the pole, and
  growth at infinity gives compact sublevel sets after adjoining the pole.
-/
def centeredBoundedNegativeGreenEvansLimit_of_compact_convergence_and_asymptotics
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {f : X → ℝ}
    (hconv :
      ∀ K : Set X, IsCompact K → K ⊆ {x : X | x ≠ p} →
        TendstoUniformlyOn
          (fun k : ℕ ↦ (B (φ k)).centeredAt q)
          f Filter.atTop K)
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ h : X → ℝ,
          IsHarmonicOnSurface χ.chart.source h ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              f x - Real.log ‖χ.chart x - χ.chart p‖ = h x)
    (hinfty : Filter.Tendsto f (Filter.cocompact X) Filter.atTop) :
    CenteredBoundedNegativeGreenEvansLimit (p := p) (q := q) E B where
  subseq := φ
  subseq_strictMono := hφ
  toFun := f
  harmonic_away_pole :=
    centered_boundedNegativeGreen_subsequence_limit_harmonic_away_pole_of_compact_convergence
      (E := E) (p := p) (q := q) B hφ hconv
  tends_to_neg_infinity_at_pole :=
    centered_boundedNegativeGreen_subsequence_limit_tends_to_neg_infinity_at_pole_of_logarithmic_zero
      (X := X) (p := p) hlog
  logarithmic_zero := hlog
  tends_to_infinity_at_infinity := hinfty
  compact_sublevel_with_zero :=
    centered_boundedNegativeGreen_subsequence_limit_compact_sublevel_with_zero_of_compact_convergence
      (E := E) (p := p) (q := q) B hφ hconv hinfty
  locally_uniform_on_compacts_away_pole := hconv

/--
%%handwave
name:
  Compact punctured sets and a base point have a preconnected relatively compact
  punctured neighborhood
statement:
  If a compact set and a base point avoid a pole, then they are contained in a
  common open preconnected region whose closure is compact and still avoids the
  pole.
proof:
  Join the base point to each point of the compact set inside the punctured
  surface.  Compactness gives finitely many path thickenings covering the set;
  their finite union is preconnected because all of them contain the base point.
  A smooth relatively compact thickening inside the punctured surface gives the
  desired region.
-/
theorem exists_preconnected_relativelyCompact_punctured_neighborhood_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {K : Set X} {p q : X}
    (hq : q ≠ p)
    (hK_compact : IsCompact K) (hK_nonempty : K.Nonempty)
    (hK_punctured : K ⊆ {x : X | x ≠ p}) :
    ∃ U : Set X,
      IsOpen U ∧ IsPreconnected U ∧ IsCompact (closure U) ∧
        closure U ⊆ {x : X | x ≠ p} ∧ K ⊆ U ∧ q ∈ U := by
  classical
  let W : K → Set X := fun x =>
    Classical.choose
      (exists_preconnected_relativelyCompact_punctured_neighborhood_pair
        (X := X) (p := p) (q := q) (x := x.1) hq (hK_punctured x.2))
  have hW_spec :
      ∀ x : K,
        IsOpen (W x) ∧ IsPreconnected (W x) ∧
          IsCompact (closure (W x)) ∧
            closure (W x) ⊆ {y : X | y ≠ p} ∧ q ∈ W x ∧ x.1 ∈ W x := by
    intro x
    exact
      Classical.choose_spec
        (exists_preconnected_relativelyCompact_punctured_neighborhood_pair
          (X := X) (p := p) (q := q) (x := x.1) hq (hK_punctured x.2))
  have hcover : K ⊆ ⋃ x : K, W x := by
    intro x hxK
    exact Set.mem_iUnion.mpr
      ⟨⟨x, hxK⟩, (hW_spec ⟨x, hxK⟩).2.2.2.2.2⟩
  rcases hK_compact.elim_finite_subcover W
      (fun x ↦ (hW_spec x).1) hcover with
    ⟨t, ht⟩
  rcases hK_nonempty with ⟨x0, hx0K⟩
  let x0K : K := ⟨x0, hx0K⟩
  let t' : Finset K := insert x0K t
  let U : Set X := ⋃ x ∈ t', W x
  have hclosure_eq : closure U = ⋃ x ∈ t', closure (W x) := by
    simpa [U] using (Finset.closure_biUnion t' W)
  refine ⟨U, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [U]
    exact isOpen_iUnion fun x ↦ isOpen_iUnion fun _ ↦ (hW_spec x).1
  · let C : Set (Set X) := W '' (↑t' : Set K)
    have hqC : ∀ V ∈ C, q ∈ V := by
      rintro V ⟨x, _hxt, rfl⟩
      exact (hW_spec x).2.2.2.2.1
    have hpreC : ∀ V ∈ C, IsPreconnected V := by
      rintro V ⟨x, _hxt, rfl⟩
      exact (hW_spec x).2.1
    have hpre : IsPreconnected (⋃₀ C) :=
      isPreconnected_sUnion q C hqC hpreC
    have hU_eq : U = ⋃₀ C := by
      ext z
      constructor
      · intro hz
        rcases Set.mem_iUnion₂.mp hz with ⟨x, hxt, hzW⟩
        exact ⟨W x, ⟨x, hxt, rfl⟩, hzW⟩
      · intro hz
        rcases hz with ⟨V, hVC, hzV⟩
        rcases hVC with ⟨x, hxt, rfl⟩
        exact Set.mem_iUnion₂.mpr ⟨x, hxt, hzV⟩
    simpa [hU_eq]
  · have hcompact : IsCompact (⋃ x ∈ t', closure (W x)) :=
      t'.isCompact_biUnion fun x _ ↦ (hW_spec x).2.2.1
    simpa [hclosure_eq] using hcompact
  · intro x hx
    rw [hclosure_eq] at hx
    rcases Set.mem_iUnion₂.mp hx with ⟨y, _hyt, hxy⟩
    exact (hW_spec y).2.2.2.1 hxy
  · intro x hxK
    rcases Set.mem_iUnion₂.mp (ht hxK) with ⟨y, hyt, hxy⟩
    exact Set.mem_iUnion₂.mpr
      ⟨y, Finset.mem_insert.mpr (Or.inr hyt), hxy⟩
  · exact Set.mem_iUnion₂.mpr
      ⟨x0K, Finset.mem_insert_self x0K t, (hW_spec x0K).2.2.2.2.1⟩

/--
%%handwave
name:
  A one-sided Harnack bound gives compact absolute bounds
statement:
  Let a family of functions on a preconnected region be eventually bounded
  below by a fixed constant, and suppose the shifted nonnegative family has
  local pairwise Harnack control.  If the original family is normalized to
  vanish at one point, then it is eventually bounded in absolute value on
  every compact subset of the region.
proof:
  Apply Harnack propagation to the shifted nonnegative functions.  This gives
  an eventual upper bound for the shift on the compact set.  The assumed
  lower bound supplies the other side, and the two endpoint bounds give one
  absolute-value bound.
-/
theorem eventual_uniform_abs_bound_on_compact_of_eventual_lower_bound_and_local_pair_harnack_control
    {X : Type} [TopologicalSpace X]
    {K U : Set X} {F : ℕ → X → ℝ} {a : ℝ} {x₀ : X}
    (hU_preconnected : IsPreconnected U)
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hlower : ∀ᶠ n : ℕ in Filter.atTop, ∀ x ∈ U, a ≤ F n x)
    (hlocal :
      ∀ x ∈ U,
        ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ᶠ n : ℕ in Filter.atTop,
              ∀ y ∈ N, ∀ z ∈ N,
                F n y - a ≤ C * (F n z - a))
    (hx₀ : x₀ ∈ U)
    (hbase : ∀ᶠ n : ℕ in Filter.atTop, F n x₀ = 0) :
    ∃ M : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x ∈ K, ‖F n x‖ ≤ M := by
  have hbase_shift :
      ∃ A : ℝ,
        ∀ᶠ n : ℕ in Filter.atTop, F n x₀ - a ≤ A := by
    refine ⟨-a, ?_⟩
    filter_upwards [hbase] with n hn
    rw [hn]
    simp
  rcases
    eventual_uniform_upper_bound_on_compact_propagates_of_local_pair_harnack_control
      (K := K) (U := U) (F := fun n x ↦ F n x - a)
      hU_preconnected hK_compact hKU hlocal hx₀ hbase_shift with
    ⟨A, hA⟩
  refine ⟨max |a| |A + a|, ?_⟩
  filter_upwards [hlower, hA] with n hn_lower hn_upper x hxK
  have hxU : x ∈ U := hKU hxK
  have hFx_lower : a ≤ F n x := hn_lower x hxU
  have hshift_upper : F n x - a ≤ A := hn_upper x hxK
  have hFx_upper : F n x ≤ A + a := by linarith
  have hlower_abs : -max |a| |A + a| ≤ a := by
    have hmax : |a| ≤ max |a| |A + a| := le_max_left |a| |A + a|
    have hneg : -max |a| |A + a| ≤ -|a| := neg_le_neg hmax
    exact hneg.trans (neg_abs_le a)
  have hupper_abs : A + a ≤ max |a| |A + a| := by
    exact (le_abs_self (A + a)).trans (le_max_right |a| |A + a|)
  have habs : |F n x| ≤ max |a| |A + a| :=
    abs_le.mpr ⟨hlower_abs.trans hFx_lower, hFx_upper.trans hupper_abs⟩
  simpa [Real.norm_eq_abs] using habs

/--
%%handwave
name:
  Shifted centered Green potentials satisfy local Harnack control
statement:
  If centered bounded-domain Green potentials are eventually bounded below on
  a relatively compact punctured region, then after subtracting that lower
  bound they form a nonnegative harmonic family there, so local pairwise
  Harnack inequalities apply.
proof:
  The centered potentials are eventually harmonic on the region because its
  compact closure avoids the pole and is eventually contained in the
  exhaustion domains.  Subtracting the lower bound preserves harmonicity, and
  the assumed lower bound gives nonnegativity.  Apply the local Harnack
  theorem for nonnegative harmonic functions.
-/
theorem centered_boundedNegativeGreen_exhaustion_eventual_local_pair_harnack_control_of_eventual_lower_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {E : SmoothRelativelyCompactExhaustion X} {p q : X}
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    {U : Set X}
    (hU_open : IsOpen U)
    (hU_compact_closure : IsCompact (closure U))
    (hU_punctured_closure : closure U ⊆ {x : X | x ≠ p})
    {a : ℝ}
    (hlower :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ y ∈ U, a ≤ (B n).centeredAt q y)
    {x : X} (hxU : x ∈ U) :
    ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ y ∈ N, ∀ z ∈ N,
            (B n).centeredAt q y - a ≤
              C * ((B n).centeredAt q z - a) := by
  rcases local_harnack_pair_control_for_nonnegative_harmonic_function
      (X := X) hU_open hxU with
    ⟨N, hN_nhds, hN_subset, C, hC_pos, hcontrol⟩
  refine ⟨N, hN_nhds, hN_subset, C, hC_pos, ?_⟩
  filter_upwards
    [centered_boundedNegativeGreen_eventually_harmonic_on_relativelyCompact_punctured_region
      (E := E) (p := p) (q := q) B hU_compact_closure hU_punctured_closure,
     hlower] with n hharm hlower_n y hyN z hzN
  let u : X → ℝ := fun w ↦ (B n).centeredAt q w - a
  have hu_harm : IsHarmonicOnSurface U u :=
    harmonicOnSurface_sub hharm (harmonicOnSurface_const U a)
  have hu_nonneg : ∀ w ∈ U, 0 ≤ u w := by
    intro w hwU
    exact sub_nonneg.mpr (hlower_n w hwU)
  exact hcontrol hu_harm hu_nonneg y hyN z hzN

/--
%%handwave
name:
  Local eventual lower bounds give compact eventual lower bounds
statement:
  If every point of a region has an open neighborhood on which a sequence is
  eventually bounded below, then every compact subset of the region has a
  single eventual lower bound.
proof:
  Apply the corresponding compact upper-bound assertion to the negatives of
  the functions.  The resulting upper bound for the negatives is exactly a
  lower bound for the original functions.
-/
theorem eventual_uniform_lower_bound_on_compact_of_open_local_uniform_lower_bound
    {X : Type} [TopologicalSpace X]
    {K U : Set X} {F : ℕ → X → ℝ}
    {O : X → Set X} {L : X → ℝ}
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hO_open : ∀ x ∈ U, IsOpen (O x))
    (hxO : ∀ x ∈ U, x ∈ O x)
    (hbound :
      ∀ x ∈ U,
        ∀ᶠ n : ℕ in Filter.atTop, ∀ y ∈ O x, L x ≤ F n y) :
    ∃ a : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop, ∀ y ∈ K, a ≤ F n y := by
  rcases
    eventual_uniform_upper_bound_on_compact_of_open_local_uniform_upper_bound
      (K := K) (U := U) (F := fun n x ↦ -(F n x))
      (O := O) (M := fun x ↦ -(L x))
      hK_compact hKU hO_open hxO
      (fun x hxU ↦ by
        filter_upwards [hbound x hxU] with n hn y hyO
        have hy_lower : L x ≤ F n y := hn y hyO
        linarith) with
    ⟨A, hA⟩
  refine ⟨-A, ?_⟩
  filter_upwards [hA] with n hn y hyK
  have hy_upper : -(F n y) ≤ A := hn y hyK
  linarith

















/--
%%handwave
name:
  Escaping divergent centered sublevel sequences yield moving boundary
  witnesses
statement:
  If centered bounded-domain Green potentials with divergent normalized outer
  heights have a sublevel sequence escaping every compact set, then after
  passing to later terms one obtains, for every exhaustion boundary, a point
  on that boundary lying in the same fixed centered sublevel for a still later
  bounded Green potential.
proof:
  For a fixed inner exhaustion boundary, compact escape puts sufficiently late
  sublevel points outside the inner closure, while the outer height is already
  above the prescribed level.  The deterministic collar-crossing lemma then
  produces a sublevel point on that inner boundary.  Choose one sufficiently
  late index for each inner boundary.
-/
theorem centered_boundedNegativeGreen_exhaustion_escaping_sublevel_sequence_inner_boundary_witnesses_of_boundaryHeights_tendsto_atTop
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (_hp : ∀ n : ℕ, p ∈ (E.domain n).carrier)
    (_hq : ∀ n : ℕ, q ∈ (E.domain n).carrier)
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    (hheights :
      Filter.Tendsto
        (fun n : ℕ ↦ (B n).boundaryHeightAt q)
        Filter.atTop Filter.atTop)
    (A : ℝ)
    (ν : ℕ → ℕ) (hν_late : ∀ j : ℕ, j ≤ ν j)
    (x : ℕ → X)
    (hdomain :
      ∀ᶠ j : ℕ in Filter.atTop, x j ∈ (E.domain (ν j)).carrier)
    (hescape :
      ∀ K : Set X, IsCompact K → p ∈ K → q ∈ K →
        ∀ᶠ j : ℕ in Filter.atTop, x j ∉ K)
    (hsub :
      ∀ᶠ j : ℕ in Filter.atTop, (B (ν j)).centeredAt q (x j) < A) :
    ∃ μ : ℕ → ℕ, (∀ j : ℕ, j ≤ μ j) ∧
      ∀ j : ℕ, ∃ y : X, y ∈ (E.domain j).boundary ∧
        (B (μ j)).centeredAt q y < A := by
  classical
  have hheightν :
      ∀ᶠ k : ℕ in Filter.atTop, A ≤ (B (ν k)).boundaryHeightAt q := by
    rcases Filter.eventually_atTop.mp (hheights.eventually_ge_atTop A) with
      ⟨N, hN⟩
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    exact hN (ν k) (hk.trans (hν_late k))
  have hselect :
      ∀ j : ℕ,
        ∃ k : ℕ, j ≤ k ∧
          x k ∈ (E.domain (ν k)).carrier ∧
            x k ∉ closure (E.domain j).carrier ∧
              (B (ν k)).centeredAt q (x k) < A ∧
                A ≤ (B (ν k)).boundaryHeightAt q := by
    intro j
    let K : Set X := closure (E.domain j).carrier
    have hK_compact : IsCompact K := (E.domain j).compact_closure
    have hpK : p ∈ K := subset_closure (_hp j)
    have hqK : q ∈ K := subset_closure (_hq j)
    have hprops :
        ∀ᶠ k : ℕ in Filter.atTop,
          j ≤ k ∧
            x k ∈ (E.domain (ν k)).carrier ∧
              x k ∉ K ∧
                (B (ν k)).centeredAt q (x k) < A ∧
                  A ≤ (B (ν k)).boundaryHeightAt q := by
      filter_upwards
        [Filter.eventually_ge_atTop j, hdomain,
          hescape K hK_compact hpK hqK, hsub, hheightν] with
        k hjk hdomain_k hescape_k hsub_k hheight_k
      exact ⟨hjk, hdomain_k, hescape_k, hsub_k, hheight_k⟩
    rcases Filter.eventually_atTop.mp hprops with ⟨N, hN⟩
    let k : ℕ := max j N
    have hkN : N ≤ k := le_max_right j N
    exact ⟨k, by simpa [K, k] using hN k hkN⟩
  choose k hk using hselect
  let μ : ℕ → ℕ := fun j ↦ ν (k j)
  refine ⟨μ, ?_, ?_⟩
  · intro j
    exact (hk j).1.trans (hν_late (k j))
  · intro j
    rcases hk j with
      ⟨hjk, hdomain_k, hescape_k, hsub_k, hheight_k⟩
    have hx_not_inner : x (k j) ∉ (E.domain j).carrier := by
      intro hx_inner
      exact hescape_k (subset_closure hx_inner)
    simpa [μ] using
      centered_boundedNegativeGreen_outer_sublevel_inner_boundary_witness_of_not_mem_inner_and_outer_height
        (E := E) (p := p) (q := q) (m := j) (n := ν (k j))
        (B (ν (k j))) (_hp j) hheight_k hdomain_k hx_not_inner hsub_k

/--
%%handwave
name:
  Moving centered sublevels eventually occur only in genuine collars
statement:
  If the selected normalized heights tend to \(+\infty\), then a fixed
  centered sublevel on the \(j\)-th moving boundary can occur only when the
  selected outer index is strictly larger than \(j\), for all sufficiently
  large \(j\).
proof:
  On the boundary of the selected outer domain, the centered value equals the
  selected normalized height.  Once that height is at least the fixed level,
  equality of the two indices would contradict the strict sublevel.
-/
theorem centered_boundedNegativeGreen_exhaustion_selected_boundary_sublevel_eventually_strict_outer_of_selected_boundaryHeights_tendsto_atTop
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X) {p q : X}
    (_hpq : q ≠ p)
    (_hp : ∀ n : ℕ, p ∈ (E.domain n).carrier)
    (_hq : ∀ n : ℕ, q ∈ (E.domain n).carrier)
    (B : (n : ℕ) → BoundedNegativeGreenPotential X (E.domain n) p)
    (A : ℝ)
    (μ : ℕ → ℕ) (hμ_late : ∀ j : ℕ, j ≤ μ j)
    (hheightμ :
      Filter.Tendsto
        (fun j : ℕ ↦ (B (μ j)).boundaryHeightAt q)
        Filter.atTop Filter.atTop)
    (y : ℕ → X)
    (hboundary : ∀ j : ℕ, y j ∈ (E.domain j).boundary)
    (hsub : ∀ j : ℕ, (B (μ j)).centeredAt q (y j) < A) :
    ∀ᶠ j : ℕ in Filter.atTop, j < μ j := by
  filter_upwards [hheightμ.eventually_ge_atTop A] with j hheight_j
  refine lt_of_le_of_ne (hμ_late j) ?_
  intro h_eq
  have hcenter :
      (B (μ j)).centeredAt q (y j) =
        (B (μ j)).boundaryHeightAt q := by
    rw [← h_eq]
    exact (B j).centeredAt_eq_boundaryHeightAt_on_boundary q (hboundary j)
  have hlt : (B (μ j)).boundaryHeightAt q < A := by
    simpa [hcenter] using hsub j
  exact (not_lt_of_ge hheight_j) hlt


































end Uniformization

end JJMath
