import JJMath.RiemannianGeometry.SurfaceMetric
import JJMath.RiemannianGeometry.Volume

/-!
# Riemannian volume measures on surfaces

Local coordinate densities and gluing for Riemannian volume measures on real
surfaces.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff

namespace Uniformization
/--
%%handwave
name:
  Smooth positive area measure on a surface
statement:
  A smooth positive area measure on a Riemann surface is a Borel measure whose
  local coordinate densities are smooth and strictly positive, and which is
  finite on compact sets.
-/
structure SmoothPositiveAreaMeasureOnSurface (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (μ : Measure X) where
  /-- Compact sets have finite measure. -/
  finite_on_compact : ∀ K : Set X, IsCompact K → μ K ≠ (∞ : ℝ≥0∞)
  /-- In each complex coordinate the measure has a smooth positive density. -/
  chart_density :
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
      ∃ ρ : ℂ → ℝ,
        ContDiffOn ℝ ∞ ρ e.target ∧
          (∀ z ∈ e.target, 0 < ρ z) ∧
          Measure.map e (μ.restrict e.source) =
            (MeasureTheory.volume.restrict e.target).withDensity
              (fun z : ℂ ↦ ENNReal.ofReal (ρ z))

/--
%%handwave
name:
  Metric determinant in tangent coordinates
statement:
  In the preferred tangent coordinates at a point, the local determinant of a
  smooth Riemannian metric is the determinant of its Gram matrix on the two
  standard tangent directions.
-/
noncomputable def surfaceMetricGramDetAt {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) (x : X) : ℝ :=
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let b := g.toContMDiffRiemannianMetric.inner x
  b (1 : ℂ) (1 : ℂ) * b Complex.I Complex.I -
    b (1 : ℂ) Complex.I * b Complex.I (1 : ℂ)

/--
%%handwave
name:
  Metric volume density in tangent coordinates
statement:
  In the preferred tangent coordinates at a point, the metric volume density
  is the square root of the determinant of the metric Gram matrix.
-/
noncomputable def surfaceMetricVolumeDensityAt {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) (x : X) : ℝ :=
  Real.sqrt (surfaceMetricGramDetAt g x)

/--
%%handwave
name:
  Tangent map of a surface coordinate chart
statement:
  The tangent map of a coordinate chart sends the standard tangent directions
  in the coordinate plane to the preferred tangent coordinates at the
  corresponding point of the surface.
-/
noncomputable def surfaceChartTangentMap {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  fderivWithin ℝ
    (fun w : ℂ ↦ chartAt ℂ (e.symm z) (e.symm w)) e.target z

/--
%%handwave
name:
  Continuous preferred tangent coordinates
statement:
  Preferred tangent coordinates are continuous along coordinate charts if,
  for every chart and every fixed coordinate tangent vector, the tangent
  vector obtained by pushing that vector through the inverse chart and then
  expressing it in the preferred tangent coordinates depends continuously on
  the coordinate point.
-/
def ContinuousPreferredTangentCoordinatesOnSurface (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ), e ∈ atlas ℂ X → ∀ v : ℂ,
    ContinuousOn (fun z : ℂ ↦ surfaceChartTangentMap e z v) e.target

/--
%%handwave
name:
  Metric determinant in a coordinate chart
statement:
  In a coordinate chart, the local metric determinant is the determinant of
  the Gram matrix of the two coordinate tangent vectors.
-/
noncomputable def surfaceMetricGramDetInChart {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ) : ℝ :=
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let A := surfaceChartTangentMap e z
  let b := g.toContMDiffRiemannianMetric.inner (e.symm z)
  let v₁ : TangentSpace SurfaceRealModel (e.symm z) := A (1 : ℂ)
  let v₂ : TangentSpace SurfaceRealModel (e.symm z) := A Complex.I
  b v₁ v₁ * b v₂ v₂ - b v₁ v₂ * b v₂ v₁

/--
%%handwave
name:
  Metric volume density in a coordinate chart
statement:
  In a coordinate chart, the Riemannian volume density is the square root of
  the determinant of the Gram matrix of the coordinate tangent frame.
-/
noncomputable def surfaceMetricVolumeDensityInChart {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ) : ℝ :=
  Real.sqrt (surfaceMetricGramDetInChart g e z)

/--
%%handwave
name:
  Riemannian volume in one coordinate chart
statement:
  In a coordinate chart, the local Riemannian volume measure is Lebesgue
  measure restricted to the chart image, weighted by the square root of the
  metric determinant.
-/
noncomputable def riemannianVolumeChartMeasure {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) : Measure ℂ :=
  (MeasureTheory.volume.restrict e.target).withDensity
    (fun z : ℂ ↦ ENNReal.ofReal
      (surfaceMetricVolumeDensityInChart g e z))

/--
%%handwave
name:
  Coordinate volume is supported on the chart image
statement:
  The coordinate Riemannian volume measure associated to a chart is supported
  on that chart image.
proof:
  By definition it is a smooth positive density with respect to Lebesgue
  measure restricted to the chart image.
-/
theorem riemannianVolumeChartMeasure_restrict_target {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) :
    (riemannianVolumeChartMeasure g e).restrict e.target =
      riemannianVolumeChartMeasure g e := by
  rw [riemannianVolumeChartMeasure, restrict_withDensity e.open_target.measurableSet]
  rw [Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume)
    (s := e.target) (t := e.target) (by intro z hz; exact hz)]

/--
%%handwave
name:
  Transition map between surface coordinates
statement:
  The transition map from one surface coordinate chart to another sends the
  coordinate of a point in the second chart to its coordinate in the first.
-/
noncomputable def surfaceChartTransition {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e e' : OpenPartialHomeomorph X ℂ) : ℂ → ℂ :=
  fun z : ℂ ↦ e (e'.symm z)

/--
%%handwave
name:
  Domain of a chart overlap in coordinates
statement:
  The coordinate domain of an overlap consists of the points in the second
  chart whose corresponding surface point also lies in the first chart.
-/
def surfaceChartOverlapDomain {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e e' : OpenPartialHomeomorph X ℂ) : Set ℂ :=
  e'.target ∩ e'.symm ⁻¹' e.source

/--
%%handwave
name:
  Range of a chart overlap in coordinates
statement:
  The coordinate range of an overlap consists of the points in the first
  chart whose corresponding surface point also lies in the second chart.
-/
def surfaceChartOverlapRange {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e e' : OpenPartialHomeomorph X ℂ) : Set ℂ :=
  e.target ∩ e.symm ⁻¹' e'.source

/--
%%handwave
name:
  Surface-chart overlap domains are open
statement:
  For complex surface charts \(e,e'\), the set of \(e'\)-coordinates whose
  inverse image lies in \(e.source\) is open in \(\mathbb C\).
proof:
  Intersect the open target of \(e'\) with the preimage of the open source of
  \(e\) under the continuous inverse chart.
-/
theorem surfaceChartOverlapDomain_isOpen {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e e' : OpenPartialHomeomorph X ℂ) :
    IsOpen (surfaceChartOverlapDomain e e') := by
  simpa [surfaceChartOverlapDomain] using
    (e'.isOpen_inter_preimage_symm e.open_source)

/--
%%handwave
name:
  Surface-chart overlap ranges are open
statement:
  For complex surface charts \(e,e'\), the image of their common source in
  \(e\)-coordinates is open in \(\mathbb C\).
proof:
  Intersect the target of \(e\) with the inverse-chart preimage of \(e'.source\).
-/
theorem surfaceChartOverlapRange_isOpen {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e e' : OpenPartialHomeomorph X ℂ) :
    IsOpen (surfaceChartOverlapRange e e') := by
  simpa [surfaceChartOverlapRange] using
    (e.isOpen_inter_preimage_symm e'.open_source)

/--
%%handwave
name:
  A surface-chart transition maps overlap domain onto overlap range
statement:
  The transition \(e\circ(e')^{-1}\) carries its \(e'\)-coordinate overlap
  domain exactly onto the corresponding \(e\)-coordinate overlap range.
proof:
  Use the left- and right-inverse identities for the two partial homeomorphisms
  to prove the two set inclusions.
-/
theorem surfaceChartTransition_image_overlapDomain {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e e' : OpenPartialHomeomorph X ℂ) :
    surfaceChartTransition e e' '' surfaceChartOverlapDomain e e' =
      surfaceChartOverlapRange e e' := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with ⟨hz_target, hz_source⟩
    have hx_source : e'.symm z ∈ e'.source := e'.symm.mapsTo hz_target
    have hT_target : e (e'.symm z) ∈ e.target := e.mapsTo hz_source
    have hsymm_eq : e.symm (e (e'.symm z)) = e'.symm z :=
      e.left_inv hz_source
    exact ⟨hT_target, by simpa [surfaceChartTransition, hsymm_eq] using hx_source⟩
  · intro hy
    rcases hy with ⟨hy_target, hy_source'⟩
    refine ⟨e' (e.symm y), ?_, ?_⟩
    · have hx_source : e.symm y ∈ e.source := e.symm.mapsTo hy_target
      have hz_target : e' (e.symm y) ∈ e'.target := e'.mapsTo hy_source'
      exact ⟨hz_target, by simpa [e'.left_inv hy_source'] using hx_source⟩
    · simp [surfaceChartTransition, e'.left_inv hy_source', e.right_inv hy_target]

/--
%%handwave
name:
  Surface-chart transitions are injective on overlaps
statement:
  The transition \(e\circ(e')^{-1}\) is injective on its coordinate overlap domain.
proof:
  Injectivity of \(e\) gives equality of the inverse-chart points, and applying
  \(e'\) recovers equality of the original coordinates.
-/
theorem surfaceChartTransition_injOn_overlapDomain {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e e' : OpenPartialHomeomorph X ℂ) :
    Set.InjOn (surfaceChartTransition e e')
      (surfaceChartOverlapDomain e e') := by
  intro z₁ hz₁ z₂ hz₂ h
  rcases hz₁ with ⟨hz₁_target, hz₁_source⟩
  rcases hz₂ with ⟨hz₂_target, hz₂_source⟩
  have hsymm : e'.symm z₁ = e'.symm z₂ := by
    apply e.injOn hz₁_source hz₂_source
    simpa [surfaceChartTransition] using h
  calc
    z₁ = e' (e'.symm z₁) := (e'.right_inv hz₁_target).symm
    _ = e' (e'.symm z₂) := by rw [hsymm]
    _ = z₂ := e'.right_inv hz₂_target

/--
%%handwave
name:
  Continuity of a surface-coordinate transition
statement:
  For surface charts \(e,e'\), the transition
  \(T_{e,e'}=e\circ(e')^{-1}\) is continuous on
  \[
    \Omega_{e,e'}=e'(U_{e'})\cap(e')^{-1}(U_e).
  \]
proof:
  On \(\Omega_{e,e'}\), the inverse of \(e'\) is continuous and takes values
  in \(U_e\), where \(e\) is continuous. Their composition is therefore
  continuous on the overlap.
-/
theorem surfaceChartTransition_continuousOn_overlap {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e e' : OpenPartialHomeomorph X ℂ) :
    ContinuousOn (surfaceChartTransition e e')
      (surfaceChartOverlapDomain e e') := by
  exact e.continuousOn.comp'
    (e'.continuousOn_symm.mono
      (by
        intro z hz
        exact hz.1))
    (by
      intro z hz
      exact hz.2)

/--
%%handwave
name:
  Almost-everywhere measurability of a surface-coordinate transition
statement:
  For any Borel measure \(\mu\) on \(\mathbb C\), the transition
  \(T_{e,e'}\) is measurable almost everywhere with respect to
  \(\mu|_{\Omega_{e,e'}}\).
proof:
  [The transition \(T_{e,e'}\) is continuous on the open overlap \(\Omega_{e,e'}\).](lean:JJMath.Uniformization.surfaceChartTransition_continuousOn_overlap) Continuity on this Borel set implies almost-everywhere measurability for the restricted measure.
-/
theorem surfaceChartTransition_aemeasurable_restrict_overlapDomain {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (e e' : OpenPartialHomeomorph X ℂ) (μ : Measure ℂ) :
    AEMeasurable (surfaceChartTransition e e')
      (μ.restrict (surfaceChartOverlapDomain e e')) := by
  exact (surfaceChartTransition_continuousOn_overlap e e').aemeasurable
    (surfaceChartOverlapDomain_isOpen e e').measurableSet

/--
%%handwave
name:
  Differentiability of coordinate transition maps on overlaps
statement:
  The transition map between two surface charts is differentiable on their
  coordinate overlap.
proof:
  The real smooth manifold structure makes chart transitions smooth.  Since
  the real model of the surface is the identity model on the complex plane,
  this gives differentiability of the coordinate transition map on the
  overlap.
-/
theorem surfaceChartTransition_hasFDerivWithinAt_on_overlap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    (g : SmoothRiemannianMetricOnSurface X) :
    ∀ z ∈ surfaceChartOverlapDomain e e',
      HasFDerivWithinAt (surfaceChartTransition e e')
        (fderivWithin ℝ (surfaceChartTransition e e')
          (surfaceChartOverlapDomain e e') z)
        (surfaceChartOverlapDomain e e') z := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  have hcontDiff :
      ContDiffOn ℝ ∞ (surfaceChartTransition e e')
        (surfaceChartOverlapDomain e e') := by
    have h := SurfaceRealModel.contDiffOn_extendCoordChange
      (IsManifold.subset_maximalAtlas (I := SurfaceRealModel) (n := ∞) _he')
      (IsManifold.subset_maximalAtlas (I := SurfaceRealModel) (n := ∞) _he)
    simpa [SurfaceRealModel, surfaceChartTransition, surfaceChartOverlapDomain,
      ModelWithCorners.extendCoordChange, PartialEquiv.trans_source] using h
  intro z hz
  exact (hcontDiff.differentiableOn (by simp) z hz).hasFDerivWithinAt

/--
%%handwave
name:
  Tangent frames transform by the derivative of the transition map
statement:
  On a chart overlap, the coordinate tangent frame from one chart is obtained
  from the coordinate tangent frame of the other chart by applying the
  derivative of the transition map.
proof:
  This is the chain rule applied to the identity
  \(e'^{-1}=e^{-1}\circ(e\circ e'^{-1})\) on the overlap, followed by the
  definition of the tangent trivialization in coordinates.
-/
theorem surfaceChartTangentMap_comp_transition_on_overlap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    (g : SmoothRiemannianMetricOnSurface X) :
    ∀ z ∈ surfaceChartOverlapDomain e e',
      surfaceChartTangentMap e' z =
        (surfaceChartTangentMap e (surfaceChartTransition e e' z)).comp
          (fderivWithin ℝ (surfaceChartTransition e e')
            (surfaceChartOverlapDomain e e') z) := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  intro z hz
  let s : Set ℂ := surfaceChartOverlapDomain e e'
  let T : ℂ → ℂ := surfaceChartTransition e e'
  let x : X := e'.symm z
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  rcases hz with ⟨hz_target, hz_source⟩
  have hz_s : z ∈ s := ⟨hz_target, hz_source⟩
  have hTz_target : T z ∈ e.target := by
    exact e.mapsTo hz_source
  have hbase_z : e.symm (T z) = e'.symm z := by
    simpa [T, surfaceChartTransition, x] using e.left_inv hz_source
  have hx_c_source : x ∈ c.source := by
    exact mem_chart_source ℂ x
  let u : Set ℂ := e.target ∩ e.symm ⁻¹' c.source
  let F : ℂ → ℂ := fun w ↦ c (e.symm w)
  have hcontDiff_F_u : ContDiffOn ℝ ∞ F u := by
    have h := SurfaceRealModel.contDiffOn_extendCoordChange
      (IsManifold.subset_maximalAtlas (I := SurfaceRealModel) (n := ∞) _he)
      (IsManifold.chart_mem_maximalAtlas (I := SurfaceRealModel) (n := ∞) x)
    simpa [SurfaceRealModel, F, u, c, ModelWithCorners.extendCoordChange,
      PartialEquiv.trans_source] using h
  have hTz_u : T z ∈ u := by
    exact ⟨hTz_target, by simp [hbase_z, c, x, hx_c_source]⟩
  have hu_mem : u ∈ 𝓝[e.target] (T z) := by
    have hpre : e.symm ⁻¹' c.source ∈ 𝓝 (T z) := by
      exact (e.symm.continuousAt hTz_target).preimage_mem_nhds
        (c.open_source.mem_nhds (by simp [hbase_z, c, x, hx_c_source]))
    exact Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hpre)
  have hFdiff_u : DifferentiableWithinAt ℝ F u (T z) :=
    hcontDiff_F_u.differentiableOn (by simp) (T z) hTz_u
  have hFdiff : DifferentiableWithinAt ℝ F e.target (T z) :=
    hFdiff_u.mono_of_mem_nhdsWithin hu_mem
  have hFderiv :
      HasFDerivWithinAt F (fderivWithin ℝ F e.target (T z)) e.target (T z) :=
    hFdiff.hasFDerivWithinAt
  have hTderiv :
      HasFDerivWithinAt T
        (fderivWithin ℝ T s z) s z := by
    simpa [T, s] using
      surfaceChartTransition_hasFDerivWithinAt_on_overlap X e e' _he _he' g z hz_s
  have hmaps : Set.MapsTo T s e.target := by
    intro w hw
    exact e.mapsTo hw.2
  have hcomp :
      HasFDerivWithinAt (F ∘ T)
        ((fderivWithin ℝ F e.target (T z)).comp
          (fderivWithin ℝ T s z)) s z :=
    hFderiv.comp z hTderiv hmaps
  let F' : ℂ → ℂ := fun w ↦ chartAt ℂ (e'.symm z) (e'.symm w)
  have hEq : Set.EqOn F' (F ∘ T) s := by
    intro w hw
    have hw_source : e'.symm w ∈ e.source := hw.2
    have hbase_w : e.symm (T w) = e'.symm w := by
      simpa [T, surfaceChartTransition] using e.left_inv hw_source
    simp [F', F, T, c, x, hbase_w]
  have hderiv_s :
      HasFDerivWithinAt F'
        ((fderivWithin ℝ F e.target (T z)).comp
          (fderivWithin ℝ T s z)) s z :=
    hcomp.congr hEq (hEq hz_s)
  have hs_nhds : s ∈ 𝓝[e'.target] z := by
    have hs_open : IsOpen s := by
      simpa [s] using surfaceChartOverlapDomain_isOpen e e'
    exact mem_nhdsWithin_of_mem_nhds (hs_open.mem_nhds hz_s)
  have hderiv_target :
      HasFDerivWithinAt F'
        ((fderivWithin ℝ F e.target (T z)).comp
          (fderivWithin ℝ T s z)) e'.target z :=
    hderiv_s.mono_of_mem_nhdsWithin hs_nhds
  have huniq : UniqueDiffWithinAt ℝ e'.target z :=
    e'.open_target.uniqueDiffWithinAt hz_target
  have hfinal := hderiv_target.fderivWithin huniq
  simpa [surfaceChartTangentMap, F', F, T, s, c, x, hbase_z] using hfinal

/--
%%handwave
name:
  Two-dimensional Gram determinants transform by squared determinant
statement:
  For a real bilinear form \(b\) on \(\mathbb C\) and real-linear maps \(A,J\),
  the Gram determinant of \(b\) on \(A(J1),A(Ji)\) is
  \(\det(J)^2\) times its Gram determinant on \(A1,Ai\).
proof:
  Write the real matrix of \(J\) in the basis \(1,i\), expand both sides using
  bilinearity, and collect the resulting polynomial identity.
-/
private theorem complex_gramDet_comp
    (b : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (A J : ℂ →L[ℝ] ℂ) :
    (let A' := A.comp J;
      b (A' (1 : ℂ)) (A' (1 : ℂ)) * b (A' Complex.I) (A' Complex.I) -
        b (A' (1 : ℂ)) (A' Complex.I) * b (A' Complex.I) (A' (1 : ℂ))) =
      J.det ^ 2 *
        (b (A (1 : ℂ)) (A (1 : ℂ)) * b (A Complex.I) (A Complex.I) -
          b (A (1 : ℂ)) (A Complex.I) * b (A Complex.I) (A (1 : ℂ))) := by
  let u := A (1 : ℂ)
  let v := A Complex.I
  let a := (J (1 : ℂ)).re
  let c := (J (1 : ℂ)).im
  let b₁ := (J Complex.I).re
  let d := (J Complex.I).im
  let g11 := b u u
  let g12 := b u v
  let g21 := b v u
  let g22 := b v v
  have hJ1 : J (1 : ℂ) = (a : ℝ) • (1 : ℂ) + (c : ℝ) • Complex.I := by
    apply Complex.ext <;> simp [a, c]
  have hJI : J Complex.I = (b₁ : ℝ) • (1 : ℂ) + (d : ℝ) • Complex.I := by
    apply Complex.ext <;> simp [b₁, d]
  have hA1 :
      A (J (1 : ℂ)) = (a : ℝ) • u + (c : ℝ) • v := by
    rw [hJ1, map_add, map_smul, map_smul]
  have hAI :
      A (J Complex.I) = (b₁ : ℝ) • u + (d : ℝ) • v := by
    rw [hJI, map_add, map_smul, map_smul]
  have hb11 :
      b (A (J (1 : ℂ))) (A (J (1 : ℂ))) =
        a * a * g11 + a * c * g12 + c * a * g21 + c * c * g22 := by
    rw [hA1]
    simp only [map_add, map_smul]
    simp [g11, g12, g21, g22, smul_eq_mul]
    ring_nf
  have hb22 :
      b (A (J Complex.I)) (A (J Complex.I)) =
        b₁ * b₁ * g11 + b₁ * d * g12 + d * b₁ * g21 + d * d * g22 := by
    rw [hAI]
    simp only [map_add, map_smul]
    simp [g11, g12, g21, g22, smul_eq_mul]
    ring_nf
  have hb12 :
      b (A (J (1 : ℂ))) (A (J Complex.I)) =
        a * b₁ * g11 + a * d * g12 + c * b₁ * g21 + c * d * g22 := by
    rw [hA1, hAI]
    simp only [map_add, map_smul]
    simp [g11, g12, g21, g22, smul_eq_mul]
    ring_nf
  have hb21 :
      b (A (J Complex.I)) (A (J (1 : ℂ))) =
        b₁ * a * g11 + b₁ * c * g12 + d * a * g21 + d * c * g22 := by
    rw [hAI, hA1]
    simp only [map_add, map_smul]
    simp [g11, g12, g21, g22, smul_eq_mul]
    ring_nf
  have hJdet : J.det = a * d - b₁ * c := by
    change LinearMap.det (J : ℂ →ₗ[ℝ] ℂ) = a * d - b₁ * c
    calc
      LinearMap.det (J : ℂ →ₗ[ℝ] ℂ)
          = Matrix.det (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
              (J : ℂ →ₗ[ℝ] ℂ)) :=
        (LinearMap.det_toMatrix Complex.basisOneI (J : ℂ →ₗ[ℝ] ℂ)).symm
      _ = a * d - b₁ * c := by
        rw [Matrix.det_fin_two]
        simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
          a, b₁, c, d]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hb11, hb22, hb12, hb21, hJdet]
  ring

/--
%%handwave
name:
  A positive-definite form on \(\mathbb C\) has positive Gram determinant
statement:
  If \(b\) is symmetric and positive definite on the real plane \(\mathbb C\), then
  \[
    b(1,1)b(i,i)-b(1,i)b(i,1)>0.
  \]
proof:
  Set \(r=b(1,i)/b(1,1)\) and apply positivity to \(i-r1\ne0\).
  Expanding \(b(i-r1,i-r1)>0\) and multiplying by \(b(1,1)>0\) gives the claim.
-/
private theorem complex_gramDet_pos_of_posDef
    (b : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (hsymm : ∀ v w : ℂ, b v w = b w v)
    (hpos : ∀ v : ℂ, v ≠ 0 → 0 < b v v) :
    0 < b (1 : ℂ) (1 : ℂ) * b Complex.I Complex.I -
      b (1 : ℂ) Complex.I * b Complex.I (1 : ℂ) := by
  let a : ℝ := b (1 : ℂ) (1 : ℂ)
  let c : ℝ := b (1 : ℂ) Complex.I
  let d : ℝ := b Complex.I Complex.I
  have ha : 0 < a := hpos 1 (by norm_num)
  let r : ℝ := c / a
  let v : ℂ := Complex.I - (r : ℝ) • (1 : ℂ)
  have hv_ne : v ≠ 0 := by
    intro hv
    have him := congr_arg Complex.im hv
    simp [v, r] at him
  have hv_pos : 0 < b v v := hpos v hv_ne
  have hv_expand : b v v = d - r * c - r * c + r * r * a := by
    change b (Complex.I - (r : ℝ) • (1 : ℂ))
        (Complex.I - (r : ℝ) • (1 : ℂ)) =
      d - r * c - r * c + r * r * a
    rw [map_sub]
    simp only [ContinuousLinearMap.sub_apply, map_sub, map_smul, smul_eq_mul]
    rw [hsymm Complex.I 1]
    simp [a, c, d]
    ring
  have hv_eval : b v v = d - c * c / a := by
    rw [hv_expand]
    simp [r]
    field_simp [ha.ne']
    ring
  rw [hv_eval] at hv_pos
  have hmul : 0 < a * (d - c * c / a) := mul_pos ha hv_pos
  have hdet : a * (d - c * c / a) = a * d - c * c := by
    field_simp [ha.ne']
  rw [hdet] at hmul
  simpa [a, c, d, hsymm Complex.I 1] using hmul

/--
%%handwave
name:
  An invertible real-linear endomorphism of \(\mathbb C\) has nonzero determinant
statement:
  If \(A:\mathbb C\to_{\mathbb R}\mathbb C\) is invertible, then \(\det A\ne0\).
proof:
  Represent \(A\) by a real-linear equivalence; the determinant of an
  equivalence is a unit and hence is nonzero.
-/
private theorem complex_det_ne_zero_of_isInvertible
    (A : ℂ →L[ℝ] ℂ) (hA : A.IsInvertible) : A.det ≠ 0 := by
  rcases hA with ⟨e, rfl⟩
  change LinearMap.det (e : ℂ →ₗ[ℝ] ℂ) ≠ 0
  exact (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero

/--
%%handwave
name:
  The intrinsic surface volume density is positive
statement:
  For every smooth Riemannian metric \(g\) on a surface and every \(x\in X\),
  the preferred-coordinate density \(\rho_g(x)\) is strictly positive.
proof:
  The metric is symmetric positive definite, so its Gram determinant in the
  basis \(1,i\) is positive.  The density is the positive square root of this determinant.
-/
theorem surfaceMetricVolumeDensityAt_pos {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) (x : X) :
    0 < surfaceMetricVolumeDensityAt g x := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let b := g.toContMDiffRiemannianMetric.inner x
  have hdet :
      0 < b (1 : ℂ) (1 : ℂ) * b Complex.I Complex.I -
        b (1 : ℂ) Complex.I * b Complex.I (1 : ℂ) :=
    complex_gramDet_pos_of_posDef b
      (g.toContMDiffRiemannianMetric.symm x)
      (g.toContMDiffRiemannianMetric.pos x)
  simpa [surfaceMetricVolumeDensityAt, surfaceMetricGramDetAt, b] using
    (Real.sqrt_pos.mpr hdet)

/--
%%handwave
name:
  Transformation law for surface volume density
statement:
  For a surface chart \(e\) and \(z\in e.target\),
  \[
    \rho_{g,e}(z)=\lvert\det J_e(z)\rvert\,\rho_g(e^{-1}z),
  \]
  where \(J_e(z)\) is the tangent-coordinate transition map.
proof:
  The coordinate Gram determinant is \(\det(J_e)^2\) times the intrinsic Gram
  determinant.  Taking square roots gives the absolute determinant factor,
  using nonnegativity of both determinants.
-/
theorem surfaceMetricVolumeDensityInChart_eq_abs_det_mul_at {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (z : ℂ) (_hz : z ∈ e.target) :
    surfaceMetricVolumeDensityInChart g e z =
      |(surfaceChartTangentMap e z).det| *
        surfaceMetricVolumeDensityAt g (e.symm z) := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let J : ℂ →L[ℝ] ℂ := surfaceChartTangentMap e z
  let b := g.toContMDiffRiemannianMetric.inner (e.symm z)
  have hgram :
      surfaceMetricGramDetInChart g e z =
        J.det ^ 2 * surfaceMetricGramDetAt g (e.symm z) := by
    have hlin := complex_gramDet_comp b (ContinuousLinearMap.id ℝ ℂ) J
    simpa [surfaceMetricGramDetInChart, surfaceMetricGramDetAt, J, b] using hlin
  rw [surfaceMetricVolumeDensityInChart, surfaceMetricVolumeDensityAt, hgram]
  rw [Real.sqrt_mul (sq_nonneg J.det), Real.sqrt_sq_eq_abs]

/--
%%handwave
name:
  Linear algebra of transformed volume density
statement:
  If the two coordinate tangent frames on an overlap are related by the
  derivative of the transition map, then the corresponding Riemannian volume
  densities differ by the absolute Jacobian determinant.
proof:
  The Gram matrix of the transformed frame is \(J^T GJ\).  Its determinant is
  \((\det J)^2\det G\), and taking the positive square root gives the factor
  \(|\det J|\).
-/
theorem surfaceMetricVolumeDensityInChart_transform_of_tangentMap_comp
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    (_hframe :
      ∀ z ∈ surfaceChartOverlapDomain e e',
        surfaceChartTangentMap e' z =
          (surfaceChartTangentMap e (surfaceChartTransition e e' z)).comp
            (fderivWithin ℝ (surfaceChartTransition e e')
              (surfaceChartOverlapDomain e e') z)) :
    ∀ z ∈ surfaceChartOverlapDomain e e',
      ENNReal.ofReal (surfaceMetricVolumeDensityInChart g e' z) =
        ENNReal.ofReal
          |(fderivWithin ℝ (surfaceChartTransition e e')
            (surfaceChartOverlapDomain e e') z).det| *
          ENNReal.ofReal
            (surfaceMetricVolumeDensityInChart g e
              (surfaceChartTransition e e' z)) := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  intro z hz
  let T : ℂ → ℂ := surfaceChartTransition e e'
  let J : ℂ →L[ℝ] ℂ :=
    fderivWithin ℝ T (surfaceChartOverlapDomain e e') z
  let A : ℂ →L[ℝ] ℂ := surfaceChartTangentMap e (T z)
  let b := g.toContMDiffRiemannianMetric.inner (e'.symm z)
  rcases hz with ⟨hz_target, hz_source⟩
  have hbase : e.symm (T z) = e'.symm z := by
    simpa [T, surfaceChartTransition] using e.left_inv hz_source
  have hframe_z :
      surfaceChartTangentMap e' z = A.comp J := by
    simpa [A, J, T] using _hframe z ⟨hz_target, hz_source⟩
  have hgram :
      surfaceMetricGramDetInChart g e' z =
        J.det ^ 2 * surfaceMetricGramDetInChart g e (T z) := by
    have hlin := complex_gramDet_comp b A J
    rw [surfaceMetricGramDetInChart, surfaceMetricGramDetInChart, hframe_z]
    rw [hbase]
    simpa [A, J, T, b] using hlin
  have hsqrt :
      surfaceMetricVolumeDensityInChart g e' z =
        |J.det| * surfaceMetricVolumeDensityInChart g e (T z) := by
    rw [surfaceMetricVolumeDensityInChart, surfaceMetricVolumeDensityInChart,
      hgram]
    rw [Real.sqrt_mul (sq_nonneg J.det)]
    rw [Real.sqrt_sq_eq_abs]
  rw [show fderivWithin ℝ (surfaceChartTransition e e')
        (surfaceChartOverlapDomain e e') z = J by rfl]
  rw [show surfaceChartTransition e e' z = T z by rfl]
  rw [← ENNReal.ofReal_mul (abs_nonneg J.det)]
  exact congrArg ENNReal.ofReal hsqrt

/--
%%handwave
name:
  Weighted change of variables on a coordinate overlap
statement:
  For an injective differentiable transition map between coordinate overlap
  domains, a source density equal to the target density times the absolute
  Jacobian determinant pushes forward to the target weighted measure.
proof:
  This is Mathlib's differentiable change-of-variables theorem for Lebesgue
  measure, combined with the elementary rule for pushing forward a density
  pulled back along a measurable map.
-/
theorem weighted_changeOfVariablesOn_overlap
    {s t : Set ℂ} (F : ℂ → ℂ)
    (ρs ρt : ℂ → ℝ≥0∞)
    (hs : MeasurableSet s)
    (_ht : MeasurableSet t)
    (himage : F '' s = t)
    (hF :
      ∀ z ∈ s, HasFDerivWithinAt F (fderivWithin ℝ F s z) s z)
    (hinj : Set.InjOn F s)
    (hdensity :
      ∀ z ∈ s,
        ρs z = ENNReal.ofReal |(fderivWithin ℝ F s z).det| * ρt (F z)) :
    Measure.map F ((MeasureTheory.volume.restrict s).withDensity ρs) =
      (MeasureTheory.volume.restrict t).withDensity ρt := by
  apply Measure.ext
  intro A hA
  have hF_cont : ContinuousOn F s := by
    intro z hz
    exact (hF z hz).continuousWithinAt
  have hF_aemeas_s : AEMeasurable F (MeasureTheory.volume.restrict s) := by
    exact hF_cont.aemeasurable₀ hs.nullMeasurableSet
  have hF_aemeas_source :
      AEMeasurable F ((MeasureTheory.volume.restrict s).withDensity ρs) :=
    hF_aemeas_s.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [Measure.map_apply_of_aemeasurable hF_aemeas_source hA]
  have hpre : NullMeasurableSet (F ⁻¹' A) (MeasureTheory.volume.restrict s) :=
    hF_aemeas_s.nullMeasurableSet_preimage hA
  rw [withDensity_apply₀ _ hpre]
  rw [withDensity_apply _ hA]
  change (∫⁻ x, ρs x ∂((MeasureTheory.volume.restrict s).restrict (F ⁻¹' A))) =
    (∫⁻ x, ρt x ∂((MeasureTheory.volume.restrict t).restrict A))
  rw [Measure.restrict_restrict₀ hpre]
  rw [Measure.restrict_restrict hA]
  let J : ℂ → ℝ≥0∞ :=
    fun x ↦ ENNReal.ofReal |(fderivWithin ℝ F s x).det|
  have hρ :
      (∫⁻ x in F ⁻¹' A ∩ s, ρs x ∂MeasureTheory.volume)
        =
      (∫⁻ x in F ⁻¹' A ∩ s, J x * ρt (F x) ∂MeasureTheory.volume) := by
    apply lintegral_congr_ae
    have hpre_inter :
        NullMeasurableSet (F ⁻¹' A ∩ s) MeasureTheory.volume :=
      (nullMeasurableSet_restrict hs.nullMeasurableSet).1 hpre
    filter_upwards [ae_restrict_mem₀ hpre_inter] with x hx
    have hx_s : x ∈ s := hx.2
    simpa [J] using hdensity x hx_s
  rw [hρ]
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := MeasureTheory.volume) hs hF hinj (fun y : ℂ ↦ A.indicator ρt y)
  rw [himage] at hcov
  have hsource_indicator :
      (∫⁻ x in s, J x * A.indicator ρt (F x) ∂MeasureTheory.volume)
        =
      (∫⁻ x in F ⁻¹' A ∩ s, J x * ρt (F x) ∂MeasureTheory.volume) := by
    rw [← setLIntegral_indicator₀
      (μ := MeasureTheory.volume)
      (f := fun x : ℂ ↦ J x * ρt (F x))
      (s := F ⁻¹' A) (t := s) hpre]
    apply setLIntegral_congr_fun hs
    intro x _hx
    by_cases hxA : F x ∈ A
    · have hxpre : x ∈ F ⁻¹' A := hxA
      rw [Set.indicator_of_mem hxpre]
      change J x * A.indicator ρt (F x) = J x * ρt (F x)
      rw [Set.indicator_of_mem hxA]
    · have hxpre : x ∉ F ⁻¹' A := hxA
      rw [Set.indicator_of_notMem hxpre]
      change J x * A.indicator ρt (F x) = 0
      rw [Set.indicator_of_notMem hxA, mul_zero]
  calc
    (∫⁻ x in F ⁻¹' A ∩ s, J x * ρt (F x) ∂MeasureTheory.volume)
        = ∫⁻ x in s, J x * A.indicator ρt (F x) ∂MeasureTheory.volume :=
      hsource_indicator.symm
    _ = ∫⁻ y in t, A.indicator ρt y ∂MeasureTheory.volume := by
      simpa [J] using hcov.symm
    _ = ∫⁻ y in A ∩ t, ρt y ∂MeasureTheory.volume :=
      setLIntegral_indicator hA ρt

/--
%%handwave
name:
  Compatibility of coordinate volume measures
statement:
  The local Riemannian volume measures are compatible when, on every overlap
  of two coordinate charts, the transition map carries the measure written in
  one coordinate to the measure written in the other.
-/
def RiemannianVolumeChartMeasuresCompatible {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) : Prop :=
  ∀ (e e' : OpenPartialHomeomorph X ℂ)
      (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X),
    Measure.map (surfaceChartTransition e e')
      ((riemannianVolumeChartMeasure g e').restrict
        (surfaceChartOverlapDomain e e')) =
      (riemannianVolumeChartMeasure g e).restrict
        (surfaceChartOverlapRange e e')

/--
%%handwave
name:
  Riemannian volume measure for a surface metric
statement:
  A measure is the Riemannian volume measure of a smooth metric when it is a
  smooth positive area measure and, in every coordinate chart, its pushforward
  is Lebesgue measure with density given by the square root of the metric
  determinant.
-/
def IsRiemannianVolumeMeasureOnSurface {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : SmoothRiemannianMetricOnSurface X) (μ : Measure X) : Prop :=
  SmoothPositiveAreaMeasureOnSurface X μ ∧
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
      Measure.map e (μ.restrict e.source) =
        riemannianVolumeChartMeasure g e

/--
%%handwave
name:
  Transformation law for coordinate volume densities
statement:
  On a chart overlap, the Riemannian volume density in one coordinate system
  is the density in the other coordinate system multiplied by the absolute
  Jacobian determinant of the transition map.
proof:
  The coordinate tangent frames are related by the derivative of the
  transition map.  The Gram determinant of a pulled-back bilinear form is
  multiplied by the square of the determinant of this derivative, so the
  square-root density is multiplied by the absolute determinant.
-/
theorem surfaceMetricVolumeDensityInChart_transform_on_overlap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X) :
    ∀ z ∈ surfaceChartOverlapDomain e e',
      ENNReal.ofReal (surfaceMetricVolumeDensityInChart g e' z) =
        ENNReal.ofReal
          |(fderivWithin ℝ (surfaceChartTransition e e')
            (surfaceChartOverlapDomain e e') z).det| *
          ENNReal.ofReal
            (surfaceMetricVolumeDensityInChart g e
              (surfaceChartTransition e e' z)) := by
  exact surfaceMetricVolumeDensityInChart_transform_of_tangentMap_comp
    X g e e' _he _he'
    (surfaceChartTangentMap_comp_transition_on_overlap X e e' _he _he' g)

/--
%%handwave
name:
  Weighted change of variables on a chart overlap
statement:
  If the coordinate Riemannian densities on an overlap satisfy the Jacobian
  transformation law, then the transition map carries the local Riemannian
  measure in one coordinate chart to the local Riemannian measure in the
  other.
proof:
  Apply the smooth change-of-variables theorem to the transition map.  The
  assumed density transformation law identifies the Jacobian-weighted density
  on the source overlap with the target chart density.
-/
theorem riemannianVolumeChartMeasure_map_overlap_eq_of_density_transform
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    (_hdensity :
      ∀ z ∈ surfaceChartOverlapDomain e e',
        ENNReal.ofReal (surfaceMetricVolumeDensityInChart g e' z) =
          ENNReal.ofReal
            |(fderivWithin ℝ (surfaceChartTransition e e')
              (surfaceChartOverlapDomain e e') z).det| *
            ENNReal.ofReal
              (surfaceMetricVolumeDensityInChart g e
                (surfaceChartTransition e e' z))) :
    Measure.map (surfaceChartTransition e e')
      ((riemannianVolumeChartMeasure g e').restrict
        (surfaceChartOverlapDomain e e')) =
      (riemannianVolumeChartMeasure g e).restrict
        (surfaceChartOverlapRange e e') := by
  let s : Set ℂ := surfaceChartOverlapDomain e e'
  let t : Set ℂ := surfaceChartOverlapRange e e'
  let F : ℂ → ℂ := surfaceChartTransition e e'
  let ρs : ℂ → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal (surfaceMetricVolumeDensityInChart g e' z)
  let ρt : ℂ → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal (surfaceMetricVolumeDensityInChart g e z)
  have hs_open : IsOpen s := by
    simpa [s] using surfaceChartOverlapDomain_isOpen e e'
  have ht_open : IsOpen t := by
    simpa [t] using surfaceChartOverlapRange_isOpen e e'
  have hs : MeasurableSet s := hs_open.measurableSet
  have ht : MeasurableSet t := ht_open.measurableSet
  have hs_subset : s ⊆ e'.target := by
    intro z hz
    exact hz.1
  have ht_subset : t ⊆ e.target := by
    intro z hz
    exact hz.1
  have hleft :
      (riemannianVolumeChartMeasure g e').restrict s =
        (MeasureTheory.volume.restrict s).withDensity ρs := by
    rw [riemannianVolumeChartMeasure, restrict_withDensity hs]
    rw [Measure.restrict_restrict_of_subset hs_subset]
  have hright :
      (riemannianVolumeChartMeasure g e).restrict t =
        (MeasureTheory.volume.restrict t).withDensity ρt := by
    rw [riemannianVolumeChartMeasure, restrict_withDensity ht]
    rw [Measure.restrict_restrict_of_subset ht_subset]
  rw [show surfaceChartOverlapDomain e e' = s by rfl,
    show surfaceChartOverlapRange e e' = t by rfl, hleft, hright]
  exact weighted_changeOfVariablesOn_overlap F ρs ρt hs ht
    (by simpa [F, s, t] using surfaceChartTransition_image_overlapDomain e e')
    (by
      intro z hz
      simpa [F, s] using
        surfaceChartTransition_hasFDerivWithinAt_on_overlap X e e' _he _he' g z hz)
    (by simpa [F, s] using surfaceChartTransition_injOn_overlapDomain e e')
    (by
      intro z hz
      simpa [F, s, ρs, ρt] using _hdensity z hz)

/--
%%handwave
name:
  Smooth metrics give compatible coordinate volume measures
statement:
  The coordinate volume measures determined by a smooth Riemannian metric are
  compatible on chart overlaps.
proof:
  On an overlap, the two Gram matrices are related by the Jacobian of the
  transition map.  Taking determinants gives the usual Jacobian
  transformation law for the volume density, and the smooth
  change-of-variables theorem identifies the two pushed-forward measures.
-/
theorem riemannianVolumeChartMeasuresCompatible_of_smoothMetric
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) :
    RiemannianVolumeChartMeasuresCompatible g := by
  intro e e' he he'
  exact riemannianVolumeChartMeasure_map_overlap_eq_of_density_transform
    X g e e' he he'
    (surfaceMetricVolumeDensityInChart_transform_on_overlap X g e e' he he')

/--
%%handwave
name:
  Coordinate tangent vector fields are smooth
statement:
  For a coordinate chart, pushing a fixed coordinate tangent vector through
  the chart inverse gives a smooth tangent-vector field over the chart image.
proof:
  The constant tangent vector field on the coordinate plane is smooth.  The
  chart inverse is smooth on the chart image, and Mathlib’s tangent-map
  smoothness theorem shows that composing the constant field with the tangent
  map of the chart inverse is smooth.  Unfolding the tangent map identifies
  this field with the coordinate tangent map used in the Gram matrix.
-/
theorem surfaceChartCoordinateVector_contDiffOn
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (u : ℂ) :
    ContMDiffOn SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun z : ℂ ↦ (Bundle.TotalSpace.mk' ℂ (e.symm z)
        (surfaceChartTangentMap e z u) : TangentBundle SurfaceRealModel X)) e.target := by
  have hsymm : ContMDiffOn SurfaceRealModel SurfaceRealModel ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := SurfaceRealModel) (n := ∞) _he)
  have hbaseVec : ContMDiffOn SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun z : ℂ ↦ (⟨z, u⟩ : TangentBundle SurfaceRealModel ℂ)) e.target := by
    change ContMDiffOn SurfaceRealModel SurfaceRealModel.tangent ∞
        ((tangentBundleModelSpaceHomeomorph SurfaceRealModel).symm ∘
          fun z : ℂ ↦ ((z, u) : ModelProd ℂ ℂ)) e.target
    refine (contMDiff_tangentBundleModelSpaceHomeomorph_symm
      (I := SurfaceRealModel)).contMDiffOn.comp (t := Set.univ) ?_ ?_
    · rw [← modelWithCornersSelf_prod]
      apply ContDiffOn.contMDiffOn
      fun_prop
    · intro z hz
      simp
  have htangent : ContMDiffOn SurfaceRealModel.tangent SurfaceRealModel.tangent ∞
      (tangentMapWithin SurfaceRealModel SurfaceRealModel e.symm e.target)
      (Bundle.TotalSpace.proj ⁻¹' e.target) := by
    exact hsymm.contMDiffOn_tangentMapWithin (m := ∞) (by simp) e.open_target.uniqueMDiffOn
  have hcomp : ContMDiffOn SurfaceRealModel SurfaceRealModel.tangent ∞
      ((tangentMapWithin SurfaceRealModel SurfaceRealModel e.symm e.target) ∘
        (fun z : ℂ ↦ (⟨z, u⟩ : TangentBundle SurfaceRealModel ℂ))) e.target := by
    exact htangent.comp hbaseVec (fun z hz => by simpa using hz)
  refine hcomp.congr ?_
  intro z hz
  have hmd : MDifferentiableWithinAt SurfaceRealModel SurfaceRealModel e.symm e.target z :=
    mdifferentiableOn_atlas_symm (I := SurfaceRealModel) _he z hz
  simp [tangentMapWithin, surfaceChartTangentMap, mfderivWithin, writtenInExtChartAt,
    SurfaceRealModel, hmd]
  rfl

/--
%%handwave
name:
  Metric Gram entries are smooth in a coordinate chart
statement:
  In a coordinate chart, evaluating a smooth Riemannian metric on two fixed
  coordinate tangent directions gives a smooth real-valued function.
proof:
  The metric is a smooth section of the bundle of tangent bilinear forms, and
  the two coordinate tangent vector fields are smooth by
  [smoothness of coordinate tangent vector fields](lean:JJMath.Uniformization.surfaceChartCoordinateVector_contDiffOn).
  Smooth bundle-bilinear evaluation gives a smooth trivial real-bundle
  section; reading off its fiber coordinate gives the required smooth
  function.
-/
theorem surfaceMetricGramEntryInChart_contDiffOn
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (g : ContMDiffRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (u v : ℂ) :
    ContDiffOn ℝ ∞ (fun z : ℂ ↦
      g.inner (e.symm z) (surfaceChartTangentMap e z u)
        (surfaceChartTangentMap e z v)) e.target := by
  have hsymm : ContMDiffOn SurfaceRealModel SurfaceRealModel ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := SurfaceRealModel) (n := ∞) _he)
  have hmetric : ContMDiffOn SurfaceRealModel
      (SurfaceRealModel.prod 𝓘(ℝ, TangentBilinearFormModel)) ∞
      (fun z : ℂ ↦ Bundle.TotalSpace.mk' TangentBilinearFormModel
        (E := fun x : X ↦ TangentBilinearFormAt X x) (e.symm z)
        (g.inner (e.symm z))) e.target := by
    exact g.contMDiff.contMDiffOn.comp (t := Set.univ) hsymm (fun z hz => by simp)
  have hu := surfaceChartCoordinateVector_contDiffOn X e _he u
  have hv := surfaceChartCoordinateVector_contDiffOn X e _he v
  have htot : ContMDiffOn SurfaceRealModel (SurfaceRealModel.prod 𝓘(ℝ, ℝ)) ∞
      (fun z : ℂ ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial X ℝ) (e.symm z)
        (g.inner (e.symm z) (surfaceChartTangentMap e z u)
          (surfaceChartTangentMap e z v))) e.target := by
    exact ContMDiffOn.clm_bundle_apply₂ hmetric hu hv
  intro z hz
  have hz' := htot z hz
  rw [Bundle.contMDiffWithinAt_totalSpace] at hz'
  rcases hz' with ⟨_, hf⟩
  simpa [Bundle.Trivial.trivialization] using hf.contDiffWithinAt

/--
%%handwave
name:
  Coordinate Gram determinant is smooth
statement:
  In a coordinate chart, the Gram determinant of a smooth Riemannian metric is
  a smooth function on the chart image.
proof:
  The two coordinate tangent vector fields obtained from the chart inverse are
  [smooth sections of the tangent bundle](lean:JJMath.Uniformization.surfaceChartCoordinateVector_contDiffOn).
  Smoothness of the Riemannian metric makes
  [all four Gram matrix entries smooth](lean:JJMath.Uniformization.surfaceMetricGramEntryInChart_contDiffOn),
  and the determinant is a polynomial expression in those entries.
-/
theorem surfaceMetricGramDetInChart_contDiffOn
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) :
    ContDiffOn ℝ ∞ (surfaceMetricGramDetInChart g e) e.target := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  have h11 := surfaceMetricGramEntryInChart_contDiffOn X
    g.toContMDiffRiemannianMetric e _he (1 : ℂ) (1 : ℂ)
  have h22 := surfaceMetricGramEntryInChart_contDiffOn X
    g.toContMDiffRiemannianMetric e _he Complex.I Complex.I
  have h12 := surfaceMetricGramEntryInChart_contDiffOn X
    g.toContMDiffRiemannianMetric e _he (1 : ℂ) Complex.I
  have h21 := surfaceMetricGramEntryInChart_contDiffOn X
    g.toContMDiffRiemannianMetric e _he Complex.I (1 : ℂ)
  simpa [surfaceMetricGramDetInChart] using (h11.mul h22).sub (h12.mul h21)

/--
%%handwave
name:
  Chart tangent map is invertible
statement:
  In a genuine coordinate chart, the tangent map from coordinate tangent
  vectors to the surface tangent plane is a linear isomorphism at every point
  of the chart image.
proof:
  The inverse of a coordinate chart is a local diffeomorphism.  Mathlib’s
  manifold derivative of a differentiable open partial homeomorphism is a
  continuous linear equivalence; identifying this manifold derivative with the
  coordinate tangent map gives the result.
-/
theorem surfaceChartTangentMap_isInvertible_of_isManifold
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) :
    ∀ z ∈ e.target, (surfaceChartTangentMap e z).IsInvertible := by
  intro z hz
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ (e.symm z)
  have hx_c : e.symm z ∈ c.source := by
    simp [c]
  have hz_source : z ∈ (SurfaceRealModel.extendCoordChange e c).source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter]
    refine ⟨e.symm z, ⟨?_, hx_c⟩, ?_⟩
    · exact e.symm.mapsTo hz
    · simp [SurfaceRealModel]
      exact e.right_inv hz
  have hinv_src :
      (fderivWithin ℝ (SurfaceRealModel.extendCoordChange e c)
        (SurfaceRealModel.extendCoordChange e c).source z).IsInvertible :=
    ModelWithCorners.isInvertible_fderivWithin_extendCoordChange
      (I := SurfaceRealModel) (n := ∞) (e := e) (e' := c)
      (by simp)
      (IsManifold.subset_maximalAtlas (I := SurfaceRealModel) (n := ∞) _he)
      (IsManifold.chart_mem_maximalAtlas (I := SurfaceRealModel) (n := ∞) (e.symm z))
      hz_source
  have hpre_nhds : e.symm ⁻¹' c.source ∈ 𝓝 z :=
    (e.symm.continuousAt hz).preimage_mem_nhds (c.open_source.mem_nhds hx_c)
  have hsource_eq :
      (SurfaceRealModel.extendCoordChange e c).source =
        e.target ∩ e.symm ⁻¹' c.source := by
    simp [SurfaceRealModel, ModelWithCorners.extendCoordChange,
      PartialEquiv.trans_source, c]
  have hderiv_set :
      fderivWithin ℝ (SurfaceRealModel.extendCoordChange e c)
        (SurfaceRealModel.extendCoordChange e c).source z =
      fderivWithin ℝ (SurfaceRealModel.extendCoordChange e c) e.target z := by
    rw [hsource_eq]
    exact fderivWithin_inter hpre_nhds
  have hderiv_fun :
      fderivWithin ℝ (SurfaceRealModel.extendCoordChange e c) e.target z =
        surfaceChartTangentMap e z := by
    simp [surfaceChartTangentMap, c, SurfaceRealModel, ModelWithCorners.extendCoordChange]
    rfl
  rw [hderiv_set, hderiv_fun] at hinv_src
  exact hinv_src
/--
%%handwave
name:
  Invertibility of the tangent map of a surface chart
statement:
  Let \(g\) be a smooth Riemannian metric on a surface \(X\), let \(e\) be a
  surface chart, and let \(z\in e(U_e)\). The derivative
  \[
    d(e^{-1})_z:\mathbb R^2\longrightarrow T_{e^{-1}(z)}X
  \]
  is an invertible real-linear map.
proof:
  The metric supplies the smooth real-surface structure, and [on any smooth surface the derivative of the inverse of a coordinate chart is a linear isomorphism at every point of its image.](lean:JJMath.Uniformization.surfaceChartTangentMap_isInvertible_of_isManifold)
-/
theorem surfaceChartTangentMap_isInvertible
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) :
    ∀ z ∈ e.target, (surfaceChartTangentMap e z).IsInvertible := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  exact surfaceChartTangentMap_isInvertible_of_isManifold X e _he

/--
%%handwave
name:
  Chart tangent map has nonzero determinant
statement:
  In a genuine coordinate chart, the tangent map from coordinate tangent
  vectors to the surface tangent plane has nonzero determinant at every point
  of the chart image.
proof:
  Since [the chart tangent map is invertible](lean:JJMath.Uniformization.surfaceChartTangentMap_isInvertible),
  its determinant is nonzero.
-/
theorem surfaceChartTangentMap_det_ne_zero
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) :
    ∀ z ∈ e.target, (surfaceChartTangentMap e z).det ≠ 0 := by
  intro z hz
  exact complex_det_ne_zero_of_isInvertible (surfaceChartTangentMap e z)
    (surfaceChartTangentMap_isInvertible X g e _he z hz)

/--
%%handwave
name:
  Coordinate Gram determinant is positive
statement:
  In a coordinate chart, the Gram determinant of a positive definite
  Riemannian metric is strictly positive at every point of the chart image.
proof:
  The derivative of a coordinate chart inverse is a linear isomorphism, so the
  two coordinate tangent vectors form a basis of the tangent plane.  The Gram
  matrix of a positive definite bilinear form on a basis is positive
  definite, hence its determinant is strictly positive.
-/
theorem surfaceMetricGramDetInChart_pos
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) :
    ∀ z ∈ e.target, 0 < surfaceMetricGramDetInChart g e z := by
  intro z hz
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let A := surfaceChartTangentMap e z
  let b := g.toContMDiffRiemannianMetric.inner (e.symm z)
  have hbase :
      0 < b (1 : ℂ) (1 : ℂ) * b Complex.I Complex.I -
        b (1 : ℂ) Complex.I * b Complex.I (1 : ℂ) :=
    complex_gramDet_pos_of_posDef b
      (g.toContMDiffRiemannianMetric.symm (e.symm z))
      (g.toContMDiffRiemannianMetric.pos (e.symm z))
  have hdetA : A.det ≠ 0 := surfaceChartTangentMap_det_ne_zero X g e _he z hz
  have hdetA_sq : 0 < A.det ^ 2 := sq_pos_iff.mpr hdetA
  have hcomp := complex_gramDet_comp b (ContinuousLinearMap.id ℝ ℂ) A
  have hgram :
      surfaceMetricGramDetInChart g e z =
        A.det ^ 2 *
          (b (1 : ℂ) (1 : ℂ) * b Complex.I Complex.I -
            b (1 : ℂ) Complex.I * b Complex.I (1 : ℂ)) := by
    simpa [surfaceMetricGramDetInChart, A, b] using hcomp
  rw [hgram]
  exact mul_pos hdetA_sq hbase

/--
%%handwave
name:
  Coordinate Riemannian volume density is smooth and positive
statement:
  In a coordinate chart, the Riemannian volume density of a smooth positive
  definite metric is a smooth strictly positive function on the chart image.
proof:
  Smoothness follows from smoothness of the metric coefficients and the chart
  tangent map.  Positivity follows because the coordinate tangent frame is a
  basis and the metric is positive definite, so the Gram determinant is
  strictly positive.
-/
theorem surfaceMetricVolumeDensityInChart_smooth_positive
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) :
    ContDiffOn ℝ ∞ (surfaceMetricVolumeDensityInChart g e) e.target ∧
      ∀ z ∈ e.target, 0 < surfaceMetricVolumeDensityInChart g e z := by
  constructor
  · have hdet : ContDiffOn ℝ ∞ (surfaceMetricGramDetInChart g e) e.target :=
      surfaceMetricGramDetInChart_contDiffOn X g e _he
    have hpos : ∀ z ∈ e.target, surfaceMetricGramDetInChart g e z ≠ 0 := by
      intro z hz
      exact ne_of_gt (surfaceMetricGramDetInChart_pos X g e _he z hz)
    simpa [surfaceMetricVolumeDensityInChart] using hdet.sqrt hpos
  · intro z hz
    rw [surfaceMetricVolumeDensityInChart]
    exact Real.sqrt_pos.mpr (surfaceMetricGramDetInChart_pos X g e _he z hz)

/--
%%handwave
name:
  Coordinate changes are nonsingular for area-null sets
statement:
  On a chart overlap, the holomorphic coordinate transition sends area-null
  sets to area-null sets in the inverse-image sense.
proof:
  The Riemannian coordinate measures are smooth positive densities times
  planar area measure.  The weighted change-of-variables theorem gives
  equality of the pushed-forward weighted measures on overlaps.  Since the
  weights are positive almost everywhere, ordinary planar area measure is
  mutually absolutely continuous with the weighted coordinate measures, and
  nonsingularity follows.
-/
theorem surfaceChartTransition_volume_map_absolutelyContinuous_overlap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X) :
    Measure.map (surfaceChartTransition e e')
        (MeasureTheory.volume.restrict (surfaceChartOverlapDomain e e')) ≪
      MeasureTheory.volume.restrict (surfaceChartOverlapRange e e') := by
  let s : Set ℂ := surfaceChartOverlapDomain e e'
  let t : Set ℂ := surfaceChartOverlapRange e e'
  let F : ℂ → ℂ := surfaceChartTransition e e'
  let μ : Measure ℂ := MeasureTheory.volume.restrict s
  let ν : Measure ℂ := MeasureTheory.volume.restrict t
  let ρs : ℂ → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal (surfaceMetricVolumeDensityInChart g e' z)
  let ρt : ℂ → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal (surfaceMetricVolumeDensityInChart g e z)
  have hs_open : IsOpen s := by
    simpa [s] using surfaceChartOverlapDomain_isOpen e e'
  have ht_open : IsOpen t := by
    simpa [t] using surfaceChartOverlapRange_isOpen e e'
  have hs : MeasurableSet s := hs_open.measurableSet
  have ht : MeasurableSet t := ht_open.measurableSet
  have hs_subset : s ⊆ e'.target := by
    intro z hz
    exact hz.1
  have hρs_aemeas :
      AEMeasurable ρs μ := by
    have hρ_smooth :
        ContDiffOn ℝ ∞ (surfaceMetricVolumeDensityInChart g e') e'.target :=
      (surfaceMetricVolumeDensityInChart_smooth_positive X g e' _he').1
    have hρ_cont : ContinuousOn
        (surfaceMetricVolumeDensityInChart g e') s :=
      hρ_smooth.continuousOn.mono hs_subset
    have hρ_aemeas :
        AEMeasurable (surfaceMetricVolumeDensityInChart g e') μ :=
      hρ_cont.aemeasurable₀ hs.nullMeasurableSet
    exact hρ_aemeas.ennreal_ofReal
  have hρs_ne_zero :
      ∀ᵐ z ∂μ, ρs z ≠ 0 := by
    have hmem : ∀ᵐ z ∂μ, z ∈ s := by
      simpa [μ] using ae_restrict_mem hs
    filter_upwards [hmem] with z hz
    exact ne_of_gt
      (ENNReal.ofReal_pos.mpr
        ((surfaceMetricVolumeDensityInChart_smooth_positive X g e' _he').2
          z (hs_subset hz)))
  have hμ_ac_weighted : μ ≪ μ.withDensity ρs :=
    withDensity_absolutelyContinuous' hρs_aemeas hρs_ne_zero
  have hF_aemeas_μ : AEMeasurable F μ := by
    simpa [F, μ, s] using
      surfaceChartTransition_aemeasurable_restrict_overlapDomain e e'
        (MeasureTheory.volume : Measure ℂ)
  have hF_aemeas_weighted : AEMeasurable F (μ.withDensity ρs) :=
    hF_aemeas_μ.mono_ac (withDensity_absolutelyContinuous μ ρs)
  have hweighted_map :
      Measure.map F (μ.withDensity ρs) = ν.withDensity ρt := by
    simpa [F, μ, ν, ρs, ρt, s, t] using
      weighted_changeOfVariablesOn_overlap F ρs ρt hs ht
        (by simpa [F, s, t] using
          surfaceChartTransition_image_overlapDomain e e')
        (by
          intro z hz
          simpa [F, s] using
            surfaceChartTransition_hasFDerivWithinAt_on_overlap
              X e e' _he _he' g z hz)
        (by simpa [F, s] using
          surfaceChartTransition_injOn_overlapDomain e e')
        (by
          intro z hz
          simpa [F, s, ρs, ρt] using
            surfaceMetricVolumeDensityInChart_transform_on_overlap
              X g e e' _he _he' z hz)
  refine Measure.AbsolutelyContinuous.mk ?_
  intro A hA hνA
  rw [Measure.map_apply_of_aemeasurable hF_aemeas_μ hA]
  apply hμ_ac_weighted
  have hν_weighted_A : (ν.withDensity ρt) A = 0 :=
    withDensity_absolutelyContinuous ν ρt hνA
  have hmap_weighted_A : Measure.map F (μ.withDensity ρs) A = 0 := by
    rw [hweighted_map]
    exact hν_weighted_A
  simpa only [Measure.map_apply_of_aemeasurable hF_aemeas_weighted hA] using
    hmap_weighted_A

/--
%%handwave
name:
  Almost-everywhere pullback along coordinate changes
statement:
  An almost-everywhere statement on the range side of a chart overlap pulls
  back to an almost-everywhere statement on the domain side of the overlap
  under the coordinate transition.
proof:
  This is the filter form of nonsingularity of coordinate changes for
  planar area measure on chart overlaps.
-/
theorem surfaceChartTransition_ae_restrict_overlapDomain_of_ae_restrict_overlapRange
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    {P : ℂ → Prop}
    (hP :
      ∀ᵐ y ∂MeasureTheory.volume.restrict
          (surfaceChartOverlapRange e e'), P y) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict
        (surfaceChartOverlapDomain e e'),
      P (surfaceChartTransition e e' z) := by
  let μ : Measure ℂ :=
    MeasureTheory.volume.restrict (surfaceChartOverlapDomain e e')
  let ν : Measure ℂ :=
    MeasureTheory.volume.restrict (surfaceChartOverlapRange e e')
  let F : ℂ → ℂ := surfaceChartTransition e e'
  have hF_aemeas : AEMeasurable F μ := by
    simpa [F, μ] using
      surfaceChartTransition_aemeasurable_restrict_overlapDomain e e'
        (MeasureTheory.volume : Measure ℂ)
  have hmap_ac : Measure.map F μ ≪ ν := by
    simpa [F, μ, ν] using
      surfaceChartTransition_volume_map_absolutelyContinuous_overlap
        X g e e' _he _he'
  exact ae_of_ae_map hF_aemeas (hmap_ac.ae_le hP)

/--
%%handwave
name:
  Coordinate volume integral is density-weighted Lebesgue integral
statement:
  Integrating a real-valued function against the coordinate Riemannian volume
  measure is the same as integrating it over the chart image against Lebesgue
  measure weighted by the Riemannian volume density.
proof:
  The coordinate volume measure is, by definition, Lebesgue measure restricted
  to the chart image with density \(\rho\).  The density is smooth and
  positive on the chart image, so the standard with-density integral formula
  identifies the integral with the density-weighted set integral.
-/
theorem riemannianVolumeChartMeasure_integral_eq_setIntegral_density {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (ψ : ℂ → ℝ) :
    ∫ z, ψ z ∂riemannianVolumeChartMeasure g e =
      ∫ z in e.target,
        ψ z * surfaceMetricVolumeDensityInChart g e z ∂MeasureTheory.volume := by
  let ρ : ℂ → ℝ := surfaceMetricVolumeDensityInChart g e
  let δ : ℂ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  have hρ_cont : ContinuousOn ρ e.target :=
    (surfaceMetricVolumeDensityInChart_smooth_positive X g e _he).1.continuousOn
  have hρ_aemeas :
      AEMeasurable ρ (MeasureTheory.volume.restrict e.target) :=
    hρ_cont.aemeasurable₀ e.open_target.measurableSet.nullMeasurableSet
  have hδ_aemeas :
      AEMeasurable δ (MeasureTheory.volume.restrict e.target) :=
    hρ_aemeas.ennreal_ofReal
  have hδ_lt_top :
      ∀ᵐ z ∂MeasureTheory.volume.restrict e.target, δ z < (∞ : ℝ≥0∞) :=
    Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)
  rw [riemannianVolumeChartMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul₀ hδ_aemeas hδ_lt_top]
  change
    ∫ z in e.target, (δ z).toReal • ψ z ∂MeasureTheory.volume =
      ∫ z in e.target, ψ z * ρ z ∂MeasureTheory.volume
  refine setIntegral_congr_fun e.open_target.measurableSet ?_
  intro z hz
  have hρ_nonneg : 0 ≤ ρ z :=
    le_of_lt ((surfaceMetricVolumeDensityInChart_smooth_positive X g e _he).2 z hz)
  simp [δ, ρ, ENNReal.toReal_ofReal hρ_nonneg, mul_comm]

/--
%%handwave
name:
  Local compact finiteness of coordinate Riemannian volume
statement:
  In a coordinate chart, the Riemannian volume measure determined by a smooth
  metric is finite on compact subsets of the chart image.
proof:
  The metric determinant density is continuous and finite in the chart.  On a
  compact subset of the coordinate domain it is bounded above.  Since compact
  subsets of the complex plane have finite Lebesgue measure, the weighted
  coordinate volume is finite there.
-/
theorem riemannianVolumeChartMeasure_finite_on_compact
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ e.target →
      riemannianVolumeChartMeasure g e K ≠ (∞ : ℝ≥0∞) := by
  intro K hK hK_subset
  let ρ : ℂ → ℝ := surfaceMetricVolumeDensityInChart g e
  have hK_meas : MeasurableSet K := hK.measurableSet
  have hρ_smooth : ContDiffOn ℝ ∞ ρ e.target :=
    (surfaceMetricVolumeDensityInChart_smooth_positive X g e _he).1
  have hρ_cont_K : ContinuousOn ρ K :=
    hρ_smooth.continuousOn.mono hK_subset
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hρ_cont_K
  have hρ_le_C : ∀ z ∈ K, ENNReal.ofReal (ρ z) ≤ ENNReal.ofReal C := by
    intro z hz
    exact ENNReal.ofReal_le_ofReal ((le_abs_self (ρ z)).trans (hC z hz))
  have hbase_finite :
      (MeasureTheory.volume.restrict e.target) K < (∞ : ℝ≥0∞) :=
    hK.measure_lt_top (μ := MeasureTheory.volume.restrict e.target)
  have hconst_finite :
      (∫⁻ _ in K, ENNReal.ofReal C ∂(MeasureTheory.volume.restrict e.target)) <
        (∞ : ℝ≥0∞) := by
    have hmul :
        ENNReal.ofReal C *
          (MeasureTheory.volume.restrict e.target).restrict K Set.univ <
            (∞ : ℝ≥0∞) := by
      simpa [hK_meas] using ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbase_finite
    simpa [lintegral_const] using hmul
  have hweighted_finite :
      (∫⁻ z in K, ENNReal.ofReal (ρ z) ∂(MeasureTheory.volume.restrict e.target)) <
        (∞ : ℝ≥0∞) :=
    lt_of_le_of_lt
      (setLIntegral_mono' hK_meas hρ_le_C)
      hconst_finite
  rw [riemannianVolumeChartMeasure, withDensity_apply _ hK_meas]
  exact hweighted_finite.ne

/--
%%handwave
name:
  Countable chart source cover
statement:
  On a second-countable charted surface, the preferred coordinate charts at a
  countable set of points cover the surface.
proof:
  The source of the preferred chart at a point is an open neighbourhood of
  that point.  Second countability gives a countable subcover of this
  neighbourhood cover.
-/
theorem exists_countable_chartAt_source_cover
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [SecondCountableTopology X] :
    ∃ S : Set X, S.Countable ∧
      (⋃ x ∈ S, (chartAt ℂ x).source) = Set.univ := by
  exact countable_cover_nhds (fun x : X ↦ chart_source_mem_nhds ℂ x)

/--
%%handwave
name:
  Countable chart source cover as a sequence
statement:
  On a nonempty second-countable charted surface, the preferred coordinate
  charts at a sequence of points cover the surface.
proof:
  Enumerate the countable set of chart centers supplied by second
  countability.
-/
theorem exists_nat_chartAt_source_cover
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [SecondCountableTopology X] [Nonempty X] :
    ∃ c : ℕ → X, (⋃ n, (chartAt ℂ (c n)).source) = Set.univ := by
  rcases exists_countable_chartAt_source_cover X with
    ⟨S, hS_countable, hS_cover⟩
  let c : ℕ → X := Set.enumerateCountable hS_countable Classical.ofNonempty
  refine ⟨c, ?_⟩
  rw [Set.eq_univ_iff_forall]
  intro y
  have hy : y ∈ ⋃ x ∈ S, (chartAt ℂ x).source := by
    simp [hS_cover]
  rcases Set.mem_iUnion.mp hy with ⟨x, hyx⟩
  rcases Set.mem_iUnion.mp hyx with ⟨hxS, hyU⟩
  obtain ⟨n, hn⟩ := Set.subset_range_enumerate hS_countable
    Classical.ofNonempty hxS
  exact Set.mem_iUnion.mpr ⟨n, by simpa [c, hn] using hyU⟩

/--
%%handwave
name:
  Disjoint source piece of a chart cover
statement:
  Given a sequence of charts, the \(n\)-th source piece is the part of the
  \(n\)-th chart source not already covered by earlier chart sources.
-/
def chartMeasureGluingSourcePiece {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (c : ℕ → X) (n : ℕ) : Set X :=
  disjointed (fun m : ℕ ↦ (chartAt ℂ (c m)).source) n

/--
%%handwave
name:
  A disjointized chart piece lies in its chart source
statement:
  For chart sources \(U_n\), define
  \(P_n=U_n\setminus\bigcup_{m<n}U_m\). Then \(P_n\subseteq U_n\).
proof:
  Removing the points covered by earlier sets can only shrink \(U_n\).
-/
theorem chartMeasureGluingSourcePiece_subset {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (c : ℕ → X) (n : ℕ) :
    chartMeasureGluingSourcePiece c n ⊆ (chartAt ℂ (c n)).source := by
  exact disjointed_subset _ _

/--
%%handwave
name:
  Pairwise disjointness of disjointized chart pieces
statement:
  The sets \(P_n=U_n\setminus\bigcup_{m<n}U_m\) are pairwise disjoint:
  \(i\ne j\) implies \(P_i\cap P_j=\varnothing\).
proof:
  If \(i<j\), every point of \(P_i\) lies in an earlier source removed when
  forming \(P_j\); the case \(j<i\) is symmetric.
-/
theorem pairwise_disjoint_chartMeasureGluingSourcePiece {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (c : ℕ → X) :
    Pairwise (fun i j ↦
      Disjoint (chartMeasureGluingSourcePiece c i)
        (chartMeasureGluingSourcePiece c j)) := by
  simpa [chartMeasureGluingSourcePiece] using
    disjoint_disjointed (fun n : ℕ ↦ (chartAt ℂ (c n)).source)

/--
%%handwave
name:
  Disjointization preserves the union of chart sources
statement:
  For \(P_n=U_n\setminus\bigcup_{m<n}U_m\),
  \[
    \bigcup_{n\ge0}P_n=\bigcup_{n\ge0}U_n.
  \]
proof:
  A point in the right-hand union belongs to its least-indexed chart source
  \(U_n\), hence belongs to \(P_n\); the reverse inclusion follows from
  \(P_n\subseteq U_n\).
-/
theorem iUnion_chartMeasureGluingSourcePiece {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (c : ℕ → X) :
    (⋃ n, chartMeasureGluingSourcePiece c n) =
      ⋃ n, (chartAt ℂ (c n)).source := by
  simpa [chartMeasureGluingSourcePiece] using
    (iUnion_disjointed (f := fun n : ℕ ↦ (chartAt ℂ (c n)).source))

/--
%%handwave
name:
  Disjointized chart pieces cover the surface
statement:
  If \(\bigcup_n U_n=X\), then the disjointized pieces
  \(P_n=U_n\setminus\bigcup_{m<n}U_m\) satisfy \(\bigcup_nP_n=X\).
proof:
  [Disjointization does not change the union of the chart sources.](lean:JJMath.Uniformization.iUnion_chartMeasureGluingSourcePiece) Substitute the assumed covering equality.
-/
theorem iUnion_chartMeasureGluingSourcePiece_eq_univ {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (c : ℕ → X) (hc_cover : (⋃ n, (chartAt ℂ (c n)).source) = Set.univ) :
    (⋃ n, chartMeasureGluingSourcePiece c n) = Set.univ := by
  rw [iUnion_chartMeasureGluingSourcePiece c, hc_cover]

/--
%%handwave
name:
  Measurability of disjointized chart pieces
statement:
  If the chart sources \(U_n\) are open in a Borel space, then every
  \(P_n=U_n\setminus\bigcup_{m<n}U_m\) is Borel measurable.
proof:
  Open sets are Borel, and finite unions and set differences preserve Borel
  measurability.
-/
theorem measurableSet_chartMeasureGluingSourcePiece {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (c : ℕ → X) (n : ℕ) :
    MeasurableSet (chartMeasureGluingSourcePiece c n) := by
  exact MeasurableSet.disjointed
    (fun m : ℕ ↦ (chartAt ℂ (c m)).open_source.measurableSet) n

/--
%%handwave
name:
  Disjoint target piece of a chart cover
statement:
  The target piece corresponding to a source piece is its image in the
  coordinate plane of that chart.
-/
def chartMeasureGluingTargetPiece {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (c : ℕ → X) (n : ℕ) : Set ℂ :=
  (chartAt ℂ (c n)) '' chartMeasureGluingSourcePiece c n

/--
%%handwave
name:
  A chart-image piece lies in the chart target
statement:
  If \(e_n:U_n\to V_n\) is the \(n\)-th chart and \(T_n=e_n(P_n)\), then
  \(T_n\subseteq V_n\).
proof:
  Since \(P_n\subseteq U_n\), the chart sends every point of \(P_n\) into its
  target \(V_n\).
-/
theorem chartMeasureGluingTargetPiece_subset {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (c : ℕ → X) (n : ℕ) :
    chartMeasureGluingTargetPiece c n ⊆ (chartAt ℂ (c n)).target := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  exact (chartAt ℂ (c n)).map_source
    (chartMeasureGluingSourcePiece_subset c n hx)

/--
%%handwave
name:
  Measurability of chart-image pieces
statement:
  For a Borel chart \(e_n:U_n\to V_n\), the image
  \(T_n=e_n(P_n)\) of the Borel set \(P_n\subseteq U_n\) is Borel measurable
  in \(\mathbb C\).
proof:
  Regard \(P_n\) as a Borel subset of \(U_n\). The chart homeomorphism maps it
  to a Borel subset of \(V_n\), and the open inclusion
  \(V_n\hookrightarrow\mathbb C\) preserves Borel measurability.
-/
theorem measurableSet_chartMeasureGluingTargetPiece {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (c : ℕ → X) (n : ℕ) :
    MeasurableSet (chartMeasureGluingTargetPiece c n) := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ (c n)
  let P : Set X := chartMeasureGluingSourcePiece c n
  let Psub : Set e.source := {x : e.source | (x : X) ∈ P}
  have hP : MeasurableSet P :=
    measurableSet_chartMeasureGluingSourcePiece c n
  have hPsub : MeasurableSet Psub := by
    exact hP.preimage measurable_subtype_coe
  have htarget_sub :
      MeasurableSet (e.toHomeomorphSourceTarget '' Psub) :=
    e.toHomeomorphSourceTarget.measurableEmbedding.measurableSet_image' hPsub
  have htarget :
      MeasurableSet (((↑) : e.target → ℂ) ''
        (e.toHomeomorphSourceTarget '' Psub)) :=
    e.open_target.measurableSet.subtype_image htarget_sub
  convert htarget using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨e x, e.map_source (chartMeasureGluingSourcePiece_subset c n hx)⟩,
      ⟨⟨x, chartMeasureGluingSourcePiece_subset c n hx⟩, hx, rfl⟩, rfl⟩
  · rintro ⟨z', ⟨x, hx, hz'⟩, hz⟩
    rcases x with ⟨x, hx_source⟩
    subst z
    subst z'
    exact ⟨x, hx, rfl⟩

/--
%%handwave
name:
  Source piece viewed in a fixed target chart
statement:
  Given a target chart, the \(n\)-th source piece determines the subset of the
  target coordinate plane obtained by applying the target chart to the part of
  that source piece lying in the target chart source.
-/
def chartMeasureGluingOverlapTargetPiece {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (c : ℕ → X) (n : ℕ) : Set ℂ :=
  e '' (chartMeasureGluingSourcePiece c n ∩ e.source)

/--
%%handwave
name:
  An overlap piece lies in the fixed chart target
statement:
  For a chart \(e:U_e\to V_e\), define
  \(Q_n^e=e(P_n\cap U_e)\). Then \(Q_n^e\subseteq V_e\).
proof:
  Every point of \(P_n\cap U_e\) lies in the source of \(e\), so its image
  lies in \(V_e\).
-/
theorem chartMeasureGluingOverlapTargetPiece_subset {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (c : ℕ → X) (n : ℕ) :
    chartMeasureGluingOverlapTargetPiece e c n ⊆ e.target := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  exact e.map_source hx.2

/--
%%handwave
name:
  Measurability of overlap pieces in a fixed chart
statement:
  For a Borel chart \(e:U_e\to V_e\), each set
  \(Q_n^e=e(P_n\cap U_e)\) is Borel measurable in \(\mathbb C\).
proof:
  The intersection \(P_n\cap U_e\) is Borel. Regard it as a subset of
  \(U_e\), apply the measurable chart homeomorphism, and then include the
  resulting Borel subset of the open set \(V_e\) into \(\mathbb C\).
-/
theorem measurableSet_chartMeasureGluingOverlapTargetPiece {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (e : OpenPartialHomeomorph X ℂ) (c : ℕ → X) (n : ℕ) :
    MeasurableSet (chartMeasureGluingOverlapTargetPiece e c n) := by
  let P : Set X := chartMeasureGluingSourcePiece c n ∩ e.source
  let Psub : Set e.source := {x : e.source | (x : X) ∈ P}
  have hP : MeasurableSet P :=
    (measurableSet_chartMeasureGluingSourcePiece c n).inter
      e.open_source.measurableSet
  have hPsub : MeasurableSet Psub :=
    hP.preimage measurable_subtype_coe
  have htarget_sub :
      MeasurableSet (e.toHomeomorphSourceTarget '' Psub) :=
    e.toHomeomorphSourceTarget.measurableEmbedding.measurableSet_image' hPsub
  have htarget :
      MeasurableSet (((↑) : e.target → ℂ) ''
        (e.toHomeomorphSourceTarget '' Psub)) :=
    e.open_target.measurableSet.subtype_image htarget_sub
  convert htarget using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨e x, e.map_source hx.2⟩, ⟨⟨x, hx.2⟩, hx, rfl⟩, rfl⟩
  · rintro ⟨z', ⟨x, hx, hz'⟩, hz⟩
    rcases x with ⟨x, hx_source⟩
    subst z
    subst z'
    exact ⟨x, hx, rfl⟩

/--
%%handwave
name:
  Pairwise disjointness of overlap pieces in a fixed chart
statement:
  For a fixed chart \(e\), the sets \(Q_n^e=e(P_n\cap U_e)\) are pairwise
  disjoint.
proof:
  If a point lay in both \(Q_i^e\) and \(Q_j^e\), injectivity of \(e\) on
  \(U_e\) would give a point in \(P_i\cap P_j\), contradicting pairwise
  disjointness of the source pieces.
-/
theorem pairwise_disjoint_chartMeasureGluingOverlapTargetPiece {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (c : ℕ → X) :
    Pairwise (fun i j ↦
      Disjoint (chartMeasureGluingOverlapTargetPiece e c i)
        (chartMeasureGluingOverlapTargetPiece e c j)) := by
  intro i j hij
  rw [Set.disjoint_iff_inter_eq_empty]
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  rcases hz with ⟨hzi, hzj⟩
  rcases hzi with ⟨x, hx, rfl⟩
  rcases hzj with ⟨y, hy, hyz⟩
  have hyx : y = x := by
    have := congrArg e.symm hyz
    simpa [e.left_inv hy.2, e.left_inv hx.2] using this
  have hdisj :
      Disjoint (chartMeasureGluingSourcePiece c i)
        (chartMeasureGluingSourcePiece c j) :=
    pairwise_disjoint_chartMeasureGluingSourcePiece c hij
  exact Set.disjoint_left.mp hdisj hx.1 (by simpa [hyx] using hy.1)

/--
%%handwave
name:
  Overlap pieces partition a fixed chart target
statement:
  If \(\bigcup_nU_n=X\), then for every chart \(e:U_e\to V_e\),
  \[
    \bigcup_{n\ge0}Q_n^e=V_e,
    \qquad Q_n^e=e(P_n\cap U_e).
  \]
proof:
  The source pieces \(P_n\) cover \(X\), so every \(x\in U_e\) lies in some
  \(P_n\). Applying \(e\) gives the reverse inclusion; the forward inclusion
  follows from \(Q_n^e\subseteq V_e\).
-/
theorem iUnion_chartMeasureGluingOverlapTargetPiece_eq_target {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (c : ℕ → X)
    (hc_cover : (⋃ n, (chartAt ℂ (c n)).source) = Set.univ) :
    (⋃ n, chartMeasureGluingOverlapTargetPiece e c n) = e.target := by
  rw [Set.eq_univ_iff_forall] at hc_cover
  ext z
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨n, hzn⟩
    exact chartMeasureGluingOverlapTargetPiece_subset e c n hzn
  · intro hz
    let x : X := e.symm z
    have hx_source : x ∈ e.source := e.map_target hz
    have hx_piece :
        x ∈ ⋃ n, chartMeasureGluingSourcePiece c n := by
      rw [iUnion_chartMeasureGluingSourcePiece_eq_univ c]
      · exact Set.mem_univ x
      · exact Set.eq_univ_iff_forall.mpr hc_cover
    rcases Set.mem_iUnion.mp hx_piece with ⟨n, hxn⟩
    exact Set.mem_iUnion.mpr
      ⟨n, ⟨x, ⟨hxn, hx_source⟩, e.right_inv hz⟩⟩

/--
%%handwave
name:
  A partition piece lies in the corresponding coordinate overlap
statement:
  Let \(e_n:U_n\to V_n\) be the \(n\)-th chart. For any chart \(e\),
  \[
    Q_n^e=e(P_n\cap U_e)\subseteq e(U_e\cap U_n),
  \]
  the range of the transition from \(e_n\)-coordinates to \(e\)-coordinates.
proof:
  A representative \(x\in P_n\cap U_e\) lies in \(U_n\) because
  \(P_n\subseteq U_n\); hence \(e(x)\) lies in the stated overlap range.
-/
theorem chartMeasureGluingOverlapTargetPiece_subset_overlapRange {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (c : ℕ → X) (n : ℕ) :
    chartMeasureGluingOverlapTargetPiece e c n ⊆
      surfaceChartOverlapRange e (chartAt ℂ (c n)) := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  refine ⟨e.map_source hx.2, ?_⟩
  simpa [e.left_inv hx.2] using
    chartMeasureGluingSourcePiece_subset c n hx.1

/--
%%handwave
name:
  Transition preimage of an overlap partition piece
statement:
  Let \(e_n:U_n\to V_n\), let \(T_n=e_n(P_n)\), and let
  \(Q_n^e=e(P_n\cap U_e)\). On the transition domain
  \(\Omega_{e,e_n}=e_n(U_n\cap U_e)\),
  \[
    T_{e,e_n}^{-1}(Q_n^e)\cap\Omega_{e,e_n}
      =T_n\cap\Omega_{e,e_n}.
  \]
proof:
  Write a point in either side as \(e_n(x)\). The chart inverse identities
  reduce membership on both sides to \(x\in P_n\cap U_e\); injectivity of
  \(e\) and \(e_n\) gives the two implications.
-/
theorem surfaceChartTransition_preimage_overlapTargetPiece_inter_overlapDomain {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (c : ℕ → X) (n : ℕ) :
    (surfaceChartTransition e (chartAt ℂ (c n))) ⁻¹'
        chartMeasureGluingOverlapTargetPiece e c n ∩
      surfaceChartOverlapDomain e (chartAt ℂ (c n)) =
        chartMeasureGluingTargetPiece c n ∩
          surfaceChartOverlapDomain e (chartAt ℂ (c n)) := by
  let e' : OpenPartialHomeomorph X ℂ := chartAt ℂ (c n)
  let P : Set X := chartMeasureGluingSourcePiece c n
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hz_pre, hz_overlap⟩
    rcases hz_overlap with ⟨hz_target, hz_source⟩
    rcases hz_pre with ⟨x, hx, hx_eq⟩
    have hx_eq' : e x = e (e'.symm z) := by
      simpa [surfaceChartTransition, e'] using hx_eq
    have hx_source : x ∈ e.source := hx.2
    have hx_base : x = e'.symm z := by
      exact e.injOn hx_source hz_source hx_eq'
    refine ⟨?_, ⟨hz_target, hz_source⟩⟩
    refine ⟨x, hx.1, ?_⟩
    calc
      e' x = e' (e'.symm z) := by rw [hx_base]
      _ = z := e'.right_inv hz_target
  · intro hz
    rcases hz with ⟨hz_targetPiece, hz_overlap⟩
    rcases hz_overlap with ⟨hz_target, hz_source⟩
    rcases hz_targetPiece with ⟨x, hxP, hz_eq⟩
    have hx_source' : x ∈ e'.source :=
      chartMeasureGluingSourcePiece_subset c n hxP
    have hx_source : x ∈ e.source := by
      have hsymm : e'.symm z = x := by
        calc
          e'.symm z = e'.symm (e' x) := by rw [← hz_eq]
          _ = x := e'.left_inv hx_source'
      rw [← hsymm]
      exact hz_source
    refine ⟨?_, ⟨hz_target, hz_source⟩⟩
    refine ⟨x, ⟨hxP, hx_source⟩, ?_⟩
    have hsymm : e'.symm z = x := by
      calc
        e'.symm z = e'.symm (e' x) := by rw [← hz_eq]
        _ = x := e'.left_inv hx_source'
    calc
      e x = e (e'.symm z) := by rw [hsymm]
      _ = surfaceChartTransition e e' z := by
        rfl

/--
%%handwave
name:
  A partial homeomorphism is almost everywhere measurable on its source
statement:
  For an open partial homeomorphism \(e:X\to Y\) and any measure \(\mu\) on
  \(X\), the map \(e\) is almost everywhere measurable for \(\mu|_{e.source}\).
proof:
  The map is continuous on its open source, hence measurable there and almost
  everywhere measurable for the restricted measure.
-/
theorem openPartialHomeomorph_aemeasurable_restrict_source {X Y : Type}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : OpenPartialHomeomorph X Y) (μ : Measure X) :
    AEMeasurable e (μ.restrict e.source) := by
  exact e.continuousOn.aemeasurable e.open_source.measurableSet

/--
%%handwave
name:
  The inverse partial homeomorphism is almost everywhere measurable on its target
statement:
  For an open partial homeomorphism \(e:X\to Y\) and any measure \(\nu\) on
  \(Y\), the inverse \(e^{-1}\) is almost everywhere measurable for \(\nu|_{e.target}\).
proof:
  The inverse is continuous on the open target, hence measurable there and
  almost everywhere measurable for the restricted measure.
-/
theorem openPartialHomeomorph_symm_aemeasurable_restrict_target {X Y : Type}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : OpenPartialHomeomorph X Y) (μ : Measure Y) :
    AEMeasurable e.symm (μ.restrict e.target) := by
  exact e.continuousOn_symm.aemeasurable e.open_target.measurableSet

/--
%%handwave
name:
  Local measure pulled back from one chart piece
statement:
  The \(n\)-th contribution to the glued measure is obtained by restricting
  the \(n\)-th coordinate measure to its target piece and pulling it back by
  the inverse chart.
-/
noncomputable def chartMeasureGluingLocalMeasure {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (ν : ∀ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X → Measure ℂ)
    (c : ℕ → X) (n : ℕ) : Measure X :=
  Measure.map ((chartAt ℂ (c n)).symm)
    ((ν (chartAt ℂ (c n)) (chart_mem_atlas ℂ (c n))).restrict
      (chartMeasureGluingTargetPiece c n))

/--
%%handwave
name:
  A pulled-back chart measure is supported on its source piece
statement:
  Let \(e_n:U_n\to V_n\), \(P_n\subseteq U_n\),
  \(T_n=e_n(P_n)\), and
  \[
    \mu_n=(e_n^{-1})_*(\nu_{e_n}|_{T_n}).
  \]
  Then \(\mu_n|_{P_n}=\mu_n\).
proof:
  Every point of \(T_n\) is \(e_n(x)\) for some \(x\in P_n\), and
  \(e_n^{-1}(e_n(x))=x\). Thus the measure being pushed forward is supported
  on the preimage of \(P_n\), so restricting its pushforward to \(P_n\)
  changes nothing.
-/
theorem chartMeasureGluingLocalMeasure_restrict_sourcePiece {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (ν : ∀ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X → Measure ℂ)
    (c : ℕ → X) (n : ℕ) :
    (chartMeasureGluingLocalMeasure ν c n).restrict
        (chartMeasureGluingSourcePiece c n) =
      chartMeasureGluingLocalMeasure ν c n := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ (c n)
  let P : Set X := chartMeasureGluingSourcePiece c n
  let T : Set ℂ := chartMeasureGluingTargetPiece c n
  let νe : Measure ℂ := ν e (chart_mem_atlas ℂ (c n))
  have hP : MeasurableSet P := measurableSet_chartMeasureGluingSourcePiece c n
  have hT : MeasurableSet T := measurableSet_chartMeasureGluingTargetPiece c n
  have hT_subset_preimage : T ⊆ e.symm ⁻¹' P := by
    intro z hz
    rcases hz with ⟨x, hxP, rfl⟩
    change e.symm (e x) ∈ P
    simpa [e.left_inv (chartMeasureGluingSourcePiece_subset c n hxP)] using hxP
  have hsymm :
      AEMeasurable e.symm (νe.restrict T) := by
    exact (e.continuousOn_symm.mono
      (by
        intro z hz
        exact chartMeasureGluingTargetPiece_subset c n hz)).aemeasurable hT
  calc
    (chartMeasureGluingLocalMeasure ν c n).restrict P
        = (Measure.map e.symm (νe.restrict T)).restrict P := by
            rfl
    _ = Measure.map e.symm ((νe.restrict T).restrict (e.symm ⁻¹' P)) := by
            rw [Measure.restrict_map_of_aemeasurable hsymm hP]
    _ = Measure.map e.symm (νe.restrict T) := by
            congr 1
            rw [Measure.restrict_restrict' hT]
            congr 1
            exact Set.inter_eq_right.mpr hT_subset_preimage
    _ = chartMeasureGluingLocalMeasure ν c n := by
            rfl

/--
%%handwave
name:
  A pulled-back chart measure vanishes on every other source piece
statement:
  For \(i\ne j\), the measure
  \(\mu_i=(e_i^{-1})_*(\nu_{e_i}|_{T_i})\) satisfies
  \(\mu_i|_{P_j}=0\).
proof:
  The measure \(\mu_i\) is supported on \(P_i\), while
  \(P_i\cap P_j=\varnothing\). Restrict first to \(P_i\) and then to \(P_j\);
  the resulting restriction is the measure of the empty intersection.
-/
theorem chartMeasureGluingLocalMeasure_restrict_sourcePiece_of_ne {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (ν : ∀ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X → Measure ℂ)
    (c : ℕ → X) {i j : ℕ} (hij : i ≠ j) :
    (chartMeasureGluingLocalMeasure ν c i).restrict
        (chartMeasureGluingSourcePiece c j) = 0 := by
  let Pi : Set X := chartMeasureGluingSourcePiece c i
  let Pj : Set X := chartMeasureGluingSourcePiece c j
  have hPj : MeasurableSet Pj := measurableSet_chartMeasureGluingSourcePiece c j
  have hdisj : Disjoint Pi Pj :=
    pairwise_disjoint_chartMeasureGluingSourcePiece c hij
  have h_inter : Pj ∩ Pi = ∅ := by
    rw [Set.inter_comm]
    exact Set.disjoint_iff_inter_eq_empty.mp hdisj
  calc
    (chartMeasureGluingLocalMeasure ν c i).restrict Pj
        = ((chartMeasureGluingLocalMeasure ν c i).restrict Pi).restrict Pj := by
            rw [chartMeasureGluingLocalMeasure_restrict_sourcePiece ν c i]
    _ = (chartMeasureGluingLocalMeasure ν c i).restrict (Pj ∩ Pi) := by
            rw [Measure.restrict_restrict hPj]
    _ = 0 := by
            rw [h_inter, Measure.restrict_empty]

/--
%%handwave
name:
  A chart recovers its restricted coordinate measure
statement:
  With
  \(\mu_n=(e_n^{-1})_*(\nu_{e_n}|_{T_n})\), pushing \(\mu_n\) forward by
  \(e_n\) gives
  \[
    (e_n)_*\mu_n=\nu_{e_n}|_{T_n}.
  \]
proof:
  The measure \(\mu_n\) is supported on \(P_n\subseteq U_n\), so the two
  successive pushforwards compose. On \(T_n\subseteq V_n\),
  \(e_n\circ e_n^{-1}\) is the identity, and pushing forward by the identity
  leaves the restricted coordinate measure unchanged.
-/
theorem chartMeasureGluingLocalMeasure_own_chart_pushforward {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (ν : ∀ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X → Measure ℂ)
    (c : ℕ → X) (n : ℕ) :
    Measure.map (chartAt ℂ (c n))
        (chartMeasureGluingLocalMeasure ν c n) =
      (ν (chartAt ℂ (c n)) (chart_mem_atlas ℂ (c n))).restrict
        (chartMeasureGluingTargetPiece c n) := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ (c n)
  let P : Set X := chartMeasureGluingSourcePiece c n
  let T : Set ℂ := chartMeasureGluingTargetPiece c n
  let νe : Measure ℂ := ν e (chart_mem_atlas ℂ (c n))
  have hT : MeasurableSet T := measurableSet_chartMeasureGluingTargetPiece c n
  have hP_subset_source : P ⊆ e.source :=
    chartMeasureGluingSourcePiece_subset c n
  have hT_subset_target : T ⊆ e.target :=
    chartMeasureGluingTargetPiece_subset c n
  have hsymm :
      AEMeasurable e.symm (νe.restrict T) := by
    exact (e.continuousOn_symm.mono hT_subset_target).aemeasurable hT
  have he :
      AEMeasurable e (Measure.map e.symm (νe.restrict T)) := by
    change AEMeasurable e (chartMeasureGluingLocalMeasure ν c n)
    rw [← chartMeasureGluingLocalMeasure_restrict_sourcePiece ν c n]
    exact (e.continuousOn.mono hP_subset_source).aemeasurable
      (measurableSet_chartMeasureGluingSourcePiece c n)
  have hmap :
      Measure.map e (Measure.map e.symm (νe.restrict T)) =
        Measure.map (fun z : ℂ ↦ e (e.symm z)) (νe.restrict T) := by
    simpa [Function.comp_def] using
      (AEMeasurable.map_map_of_aemeasurable he hsymm)
  have hright :
      (fun z : ℂ ↦ e (e.symm z)) =ᵐ[νe.restrict T] fun z ↦ z := by
    exact ae_restrict_of_forall_mem hT fun z hzT ↦
      e.right_inv (hT_subset_target hzT)
  calc
    Measure.map (chartAt ℂ (c n))
        (chartMeasureGluingLocalMeasure ν c n)
        = Measure.map e (Measure.map e.symm (νe.restrict T)) := by
            rfl
    _ = Measure.map (fun z : ℂ ↦ e (e.symm z)) (νe.restrict T) := hmap
    _ = Measure.map (fun z : ℂ ↦ z) (νe.restrict T) :=
            Measure.map_congr hright
    _ = (ν (chartAt ℂ (c n)) (chart_mem_atlas ℂ (c n))).restrict
        (chartMeasureGluingTargetPiece c n) := by
            rw [Measure.map_id']

/--
%%handwave
name:
  Measure obtained by summing chart pieces
statement:
  The glued measure associated to a countable chart cover is the sum of the
  measures pulled back from the disjoint coordinate pieces.
-/
noncomputable def chartMeasureGluingMeasure {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (ν : ∀ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X → Measure ℂ)
    (c : ℕ → X) : Measure X :=
  Measure.sum (fun n : ℕ ↦ chartMeasureGluingLocalMeasure ν c n)

/--
%%handwave
name:
  Restricting the glued measure recovers one local contribution
statement:
  Let \(\mu=\sum_{i\ge0}\mu_i\), where \(\mu_i\) is supported on the pairwise
  disjoint set \(P_i\). Then
  \[
    \mu|_{P_n}=\mu_n.
  \]
proof:
  Restriction commutes with the countable sum. The \(n\)-th summand remains
  \(\mu_n\), while every summand with \(i\ne n\) restricts to zero on \(P_n\);
  hence the sum has only one nonzero term.
-/
theorem chartMeasureGluingMeasure_restrict_sourcePiece {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (ν : ∀ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X → Measure ℂ)
    (c : ℕ → X) (n : ℕ) :
    (chartMeasureGluingMeasure ν c).restrict
        (chartMeasureGluingSourcePiece c n) =
      chartMeasureGluingLocalMeasure ν c n := by
  rw [chartMeasureGluingMeasure, Measure.restrict_sum_of_countable]
  ext s hs
  rw [Measure.sum_apply _ hs]
  rw [tsum_eq_single n]
  · rw [chartMeasureGluingLocalMeasure_restrict_sourcePiece ν c n]
  · intro i hi
    rw [chartMeasureGluingLocalMeasure_restrict_sourcePiece_of_ne ν c hi]
    simp

/--
%%handwave
name:
  Summing over overlap pieces recovers a coordinate measure
statement:
  Suppose the chart sources cover \(X\), and a coordinate measure \(\nu_e\)
  is supported on the target \(V_e\). For the measurable pairwise disjoint
  partition \(Q_n^e=e(P_n\cap U_e)\) of \(V_e\),
  \[
    \sum_{n\ge0}\nu_e|_{Q_n^e}=\nu_e.
  \]
proof:
  The restriction of a measure to a countable disjoint measurable union is
  the sum of its restrictions. The union of the \(Q_n^e\) is \(V_e\), and the
  support hypothesis identifies \(\nu_e|_{V_e}\) with \(\nu_e\).
-/
theorem chartMeasureGluingOverlapTargetPiece_sum_restrict {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : ∀ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X → Measure ℂ)
    (hsupport :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X),
        (ν e he).restrict e.target = ν e he)
    (c : ℕ → X) (hc_cover : (⋃ n, (chartAt ℂ (c n)).source) = Set.univ)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) :
    Measure.sum (fun n : ℕ ↦
      (ν e he).restrict (chartMeasureGluingOverlapTargetPiece e c n)) =
        ν e he := by
  have hpartition :
      (ν e he).restrict (⋃ n, chartMeasureGluingOverlapTargetPiece e c n) =
        Measure.sum (fun n : ℕ ↦
          (ν e he).restrict (chartMeasureGluingOverlapTargetPiece e c n)) :=
    Measure.restrict_iUnion
      (pairwise_disjoint_chartMeasureGluingOverlapTargetPiece e c)
      (fun n ↦ measurableSet_chartMeasureGluingOverlapTargetPiece e c n)
  calc
    Measure.sum (fun n : ℕ ↦
      (ν e he).restrict (chartMeasureGluingOverlapTargetPiece e c n))
        = (ν e he).restrict
            (⋃ n, chartMeasureGluingOverlapTargetPiece e c n) := hpartition.symm
    _ = (ν e he).restrict e.target := by
            rw [iUnion_chartMeasureGluingOverlapTargetPiece_eq_target e c hc_cover]
    _ = ν e he := hsupport e he

/--
%%handwave
name:
  One chart piece transforms to the corresponding overlap piece
statement:
  If a local measure piece is restricted to an arbitrary chart source and
  pushed forward by that chart, compatibility of the coordinate measures
  identifies it with the target chart measure restricted to the corresponding
  overlap target piece.
proof:
  Unfold the local piece as the pullback through its own inverse chart.  On
  the intersection of the two chart sources, the resulting map is the
  transition map between coordinates.  The compatibility hypothesis gives the
  required equality on the full overlap, and restricting both sides to the
  image of the disjoint source piece gives the stated piecewise equality.
-/
theorem chartMeasureGluingLocalMeasure_chart_pushforward_piece
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : ∀ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X → Measure ℂ)
    (hcompat :
      ∀ (e e' : OpenPartialHomeomorph X ℂ)
          (he : e ∈ atlas ℂ X) (he' : e' ∈ atlas ℂ X),
        Measure.map (surfaceChartTransition e e')
          ((ν e' he').restrict (surfaceChartOverlapDomain e e')) =
          (ν e he).restrict (surfaceChartOverlapRange e e'))
    (c : ℕ → X) (n : ℕ)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) :
    Measure.map e
        ((chartMeasureGluingLocalMeasure ν c n).restrict e.source) =
      (ν e he).restrict (chartMeasureGluingOverlapTargetPiece e c n) := by
  let e' : OpenPartialHomeomorph X ℂ := chartAt ℂ (c n)
  let T : Set ℂ := chartMeasureGluingTargetPiece c n
  let O : Set ℂ := surfaceChartOverlapDomain e e'
  let B : Set ℂ := chartMeasureGluingOverlapTargetPiece e c n
  let R : Set ℂ := surfaceChartOverlapRange e e'
  let νe' : Measure ℂ := ν e' (chart_mem_atlas ℂ (c n))
  let νe : Measure ℂ := ν e he
  have he' : e' ∈ atlas ℂ X := chart_mem_atlas ℂ (c n)
  have hT : MeasurableSet T := measurableSet_chartMeasureGluingTargetPiece c n
  have hO : MeasurableSet O := (surfaceChartOverlapDomain_isOpen e e').measurableSet
  have hB : MeasurableSet B := measurableSet_chartMeasureGluingOverlapTargetPiece e c n
  have hB_subset_R : B ⊆ R := by
    simpa [B, R, e'] using
      chartMeasureGluingOverlapTargetPiece_subset_overlapRange e c n
  have hT_subset_target : T ⊆ e'.target := by
    simpa [T, e'] using chartMeasureGluingTargetPiece_subset c n
  have hsymm_T : AEMeasurable e'.symm (νe'.restrict T) := by
    exact (e'.continuousOn_symm.mono hT_subset_target).aemeasurable hT
  have hrestrict_source :
      (Measure.map e'.symm (νe'.restrict T)).restrict e.source =
        Measure.map e'.symm
          ((νe'.restrict T).restrict (e'.symm ⁻¹' e.source)) := by
    rw [Measure.restrict_map_of_aemeasurable hsymm_T e.open_source.measurableSet]
  have hpre_source_ae :
      e'.symm ⁻¹' e.source =ᵐ[νe'.restrict T] O := by
    filter_upwards [ae_restrict_mem hT] with z hzT
    apply propext
    constructor
    · intro hz_source
      exact ⟨hT_subset_target hzT, hz_source⟩
    · intro hzO
      exact hzO.2
  have hsource_restrict :
      (νe'.restrict T).restrict (e'.symm ⁻¹' e.source) =
        νe'.restrict (T ∩ O) := by
    calc
      (νe'.restrict T).restrict (e'.symm ⁻¹' e.source)
          = (νe'.restrict T).restrict O := by
              exact Measure.restrict_congr_set hpre_source_ae
      _ = νe'.restrict (O ∩ T) := by
              rw [Measure.restrict_restrict hO]
      _ = νe'.restrict (T ∩ O) := by
              rw [Set.inter_comm]
  have hsymm_piece :
      AEMeasurable e'.symm
        ((νe'.restrict T).restrict (e'.symm ⁻¹' e.source)) :=
    hsymm_T.mono_measure Measure.restrict_le_self
  have he_piece :
      AEMeasurable e
        (Measure.map e'.symm
          ((νe'.restrict T).restrict (e'.symm ⁻¹' e.source))) := by
    rw [← hrestrict_source]
    exact e.continuousOn.aemeasurable e.open_source.measurableSet
  have hlhs :
      Measure.map e
          ((chartMeasureGluingLocalMeasure ν c n).restrict e.source) =
        Measure.map (surfaceChartTransition e e')
          (νe'.restrict (T ∩ O)) := by
    calc
      Measure.map e
          ((chartMeasureGluingLocalMeasure ν c n).restrict e.source)
          = Measure.map e
              ((Measure.map e'.symm (νe'.restrict T)).restrict e.source) := by
                rfl
      _ = Measure.map e
              (Measure.map e'.symm
                ((νe'.restrict T).restrict (e'.symm ⁻¹' e.source))) := by
                rw [hrestrict_source]
      _ = Measure.map (surfaceChartTransition e e')
              ((νe'.restrict T).restrict (e'.symm ⁻¹' e.source)) := by
                simpa [surfaceChartTransition, Function.comp_def] using
                  (AEMeasurable.map_map_of_aemeasurable he_piece hsymm_piece)
      _ = Measure.map (surfaceChartTransition e e')
              (νe'.restrict (T ∩ O)) := by
                rw [hsource_restrict]
  have htrans :
      AEMeasurable (surfaceChartTransition e e') (νe'.restrict O) := by
    exact surfaceChartTransition_aemeasurable_restrict_overlapDomain e e' νe'
  have hpre_piece_ae :
      (surfaceChartTransition e e') ⁻¹' B =ᵐ[νe'.restrict O] T := by
    filter_upwards [ae_restrict_mem hO] with z hzO
    have hset :=
      congrFun
        (show (surfaceChartTransition e e') ⁻¹' B ∩ O =
            T ∩ O from by
          simpa [B, T, O, e'] using
            surfaceChartTransition_preimage_overlapTargetPiece_inter_overlapDomain e c n)
        z
    apply propext
    constructor
    · intro hzpre
      exact (hset.mp ⟨hzpre, hzO⟩).1
    · intro hzT
      exact (hset.mpr ⟨hzT, hzO⟩).1
  have hcompat_piece :
      Measure.map (surfaceChartTransition e e')
          (νe'.restrict (T ∩ O)) =
        νe.restrict B := by
    have hcomp :=
      congrArg (fun μ : Measure ℂ ↦ μ.restrict B)
        (hcompat e e' he he')
    change (Measure.map (surfaceChartTransition e e') (νe'.restrict O)).restrict B =
      (νe.restrict R).restrict B at hcomp
    rw [Measure.restrict_map_of_aemeasurable htrans hB] at hcomp
    rw [Measure.restrict_congr_set hpre_piece_ae] at hcomp
    rw [Measure.restrict_restrict hT] at hcomp
    rw [Measure.restrict_restrict hB] at hcomp
    rw [show B ∩ R = B from Set.inter_eq_left.mpr hB_subset_R] at hcomp
    simpa [νe, νe', T, O, B, R] using hcomp
  calc
    Measure.map e
        ((chartMeasureGluingLocalMeasure ν c n).restrict e.source)
        = Measure.map (surfaceChartTransition e e')
            (νe'.restrict (T ∩ O)) := hlhs
    _ = (ν e he).restrict (chartMeasureGluingOverlapTargetPiece e c n) := by
        simpa [νe, B] using hcompat_piece

/--
%%handwave
name:
  The chart-piece construction has the prescribed chart pushforwards
statement:
  On every chart, the pushforward of the glued measure restricted to the
  chart source is the prescribed coordinate measure.
proof:
  The disjoint source pieces partition the chart source.  For a piece coming
  from another chart, compatibility on the overlap identifies the pushforward
  through the target chart with the restriction of the target coordinate
  measure to the corresponding image of that piece.  Summing the disjoint
  restrictions recovers the whole target coordinate measure, and the support
  hypothesis removes mass outside the chart image.
-/
theorem chartMeasureGluingMeasure_chart_pushforward
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    (ν : ∀ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X → Measure ℂ)
    (hsupport :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X),
        (ν e he).restrict e.target = ν e he)
    (hcompat :
      ∀ (e e' : OpenPartialHomeomorph X ℂ)
          (he : e ∈ atlas ℂ X) (he' : e' ∈ atlas ℂ X),
        Measure.map (surfaceChartTransition e e')
          ((ν e' he').restrict (surfaceChartOverlapDomain e e')) =
          (ν e he).restrict (surfaceChartOverlapRange e e'))
    (c : ℕ → X) (hc_cover : (⋃ n, (chartAt ℂ (c n)).source) = Set.univ) :
    ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X),
      Measure.map e ((chartMeasureGluingMeasure ν c).restrict e.source) =
        ν e he := by
  intro e he
  rw [chartMeasureGluingMeasure, Measure.restrict_sum_of_countable]
  have he_sum :
      AEMeasurable e
        (Measure.sum (fun n : ℕ ↦
          (chartMeasureGluingLocalMeasure ν c n).restrict e.source)) := by
    rw [aemeasurable_sum_measure_iff]
    intro n
    exact e.continuousOn.aemeasurable e.open_source.measurableSet
  rw [Measure.map_sum he_sum]
  simp_rw [chartMeasureGluingLocalMeasure_chart_pushforward_piece
    X ν hcompat c _ e he]
  exact chartMeasureGluingOverlapTargetPiece_sum_restrict
    ν hsupport c hc_cover e he

/--
%%handwave
name:
  Finiteness of the glued measure on a compact set inside one chart
statement:
  Let \(\mu=\sum_n(e_n^{-1})_*(\nu_{e_n}|_{T_n})\), where the coordinate
  measures are supported on chart targets, compatible under coordinate
  changes, and finite on compact subsets of those targets. If
  \(K\subseteq U_e\) is compact, then \(\mu(K)<\infty\).
proof:
  The image \(L=e(K)\) is compact and lies in \(V_e\). The chart-pushforward
  identity gives \(e_*(\mu|_{U_e})=\nu_e\), whence
  \(\mu(K)\le\nu_e(L)\). The assumed compact finiteness of \(\nu_e\) makes the
  right-hand side finite.
-/
theorem chartMeasureGluingMeasure_compact_subset_chart_source_ne_top
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X]
    (ν : ∀ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X → Measure ℂ)
    (hsupport :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X),
        (ν e he).restrict e.target = ν e he)
    (hcompat :
      ∀ (e e' : OpenPartialHomeomorph X ℂ)
          (he : e ∈ atlas ℂ X) (he' : e' ∈ atlas ℂ X),
        Measure.map (surfaceChartTransition e e')
          ((ν e' he').restrict (surfaceChartOverlapDomain e e')) =
          (ν e he).restrict (surfaceChartOverlapRange e e'))
    (hfinite :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
        (K : Set ℂ), IsCompact K → K ⊆ e.target → ν e he K ≠ (∞ : ℝ≥0∞))
    (c : ℕ → X) (hc_cover : (⋃ n, (chartAt ℂ (c n)).source) = Set.univ)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (K : Set X) (hK : IsCompact K) (hK_subset : K ⊆ e.source) :
    chartMeasureGluingMeasure ν c K ≠ (∞ : ℝ≥0∞) := by
  let μ : Measure X := chartMeasureGluingMeasure ν c
  let L : Set ℂ := e '' K
  have hL_compact : IsCompact L :=
    hK.image_of_continuousOn (e.continuousOn.mono hK_subset)
  have hL_subset : L ⊆ e.target := by
    intro z hz
    rcases hz with ⟨x, hxK, rfl⟩
    exact e.map_source (hK_subset hxK)
  have hL_finite : ν e he L ≠ (∞ : ℝ≥0∞) :=
    hfinite e he L hL_compact hL_subset
  have hL_meas : MeasurableSet L := hL_compact.measurableSet
  have he_aem : AEMeasurable e (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hpush :
      Measure.map e (μ.restrict e.source) = ν e he := by
    simpa [μ] using
      chartMeasureGluingMeasure_chart_pushforward
        X ν hsupport hcompat c hc_cover e he
  have hle : μ K ≤ ν e he L := by
    calc
      μ K = μ.restrict e.source K := by
        exact (Measure.restrict_eq_self μ hK_subset).symm
      _ ≤ μ.restrict e.source (e ⁻¹' L) := by
        exact measure_mono fun x hxK ↦ ⟨x, hxK, rfl⟩
      _ = Measure.map e (μ.restrict e.source) L := by
        exact (Measure.map_apply_of_aemeasurable he_aem hL_meas).symm
      _ = ν e he L := by
        rw [hpush]
  exact ne_top_of_le_ne_top hL_finite hle

/--
%%handwave
name:
  The chart-piece construction is compact-finite
statement:
  If the local chart measures are finite on compact subsets of chart images,
  supported on chart images, and compatible on overlaps, then the measure
  obtained by summing the pulled-back disjoint chart pieces is finite on
  compact subsets of the surface.
proof:
  First prove local finiteness.  Around each point, local compactness gives a
  compact neighbourhood contained in a chart source.  The chart-pushforward
  calculation bounds the measure of this compact neighbourhood by the
  prescribed finite coordinate measure of its compact image.  Compact
  finiteness then follows from local finiteness.
-/
theorem chartMeasureGluingMeasure_finite_on_compact
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X]
    (ν : ∀ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X → Measure ℂ)
    (hsupport :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X),
        (ν e he).restrict e.target = ν e he)
    (hcompat :
      ∀ (e e' : OpenPartialHomeomorph X ℂ)
          (he : e ∈ atlas ℂ X) (he' : e' ∈ atlas ℂ X),
        Measure.map (surfaceChartTransition e e')
          ((ν e' he').restrict (surfaceChartOverlapDomain e e')) =
          (ν e he).restrict (surfaceChartOverlapRange e e'))
    (hfinite :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
        (K : Set ℂ), IsCompact K → K ⊆ e.target → ν e he K ≠ (∞ : ℝ≥0∞))
    (c : ℕ → X) (hc_cover : (⋃ n, (chartAt ℂ (c n)).source) = Set.univ) :
    ∀ K : Set X, IsCompact K →
      chartMeasureGluingMeasure ν c K ≠ (∞ : ℝ≥0∞) := by
  let μ : Measure X := chartMeasureGluingMeasure ν c
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  have hloc : IsLocallyFiniteMeasure μ := by
    refine ⟨fun x ↦ ?_⟩
    let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
    have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
    have hx_source : x ∈ e.source := by
      simp [e]
    rcases LocallyCompactSpace.local_compact_nhds x e.source
        (e.open_source.mem_nhds hx_source) with
      ⟨C, hC_nhds, hC_subset, hC_compact⟩
    refine ⟨C, hC_nhds, ?_⟩
    have hC_finite :
        μ C ≠ (∞ : ℝ≥0∞) := by
      simpa [μ] using
        chartMeasureGluingMeasure_compact_subset_chart_source_ne_top
          X ν hsupport hcompat hfinite c hc_cover e he C hC_compact hC_subset
    exact lt_top_iff_ne_top.mpr hC_finite
  haveI : IsLocallyFiniteMeasure μ := hloc
  intro K hK
  exact (hK.measure_lt_top (μ := μ)).ne

/--
%%handwave
name:
  Gluing compatible chart measures from a sequential cover
statement:
  A compatible family of locally finite coordinate measures, supported on
  chart images, glues to a global measure once a sequence of chart sources
  covering the surface has been fixed.
proof:
  Use the measure obtained by summing the pulled-back disjoint chart pieces.
  The preceding compact-finiteness and chart-pushforward lemmas verify the
  two required properties.
-/
theorem exists_measure_with_compatible_nat_chart_pushforwards
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X]
    (ν : ∀ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X → Measure ℂ)
    (hsupport :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X),
        (ν e he).restrict e.target = ν e he)
    (hcompat :
      ∀ (e e' : OpenPartialHomeomorph X ℂ)
          (he : e ∈ atlas ℂ X) (he' : e' ∈ atlas ℂ X),
        Measure.map (surfaceChartTransition e e')
          ((ν e' he').restrict (surfaceChartOverlapDomain e e')) =
          (ν e he).restrict (surfaceChartOverlapRange e e'))
    (hfinite :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
        (K : Set ℂ), IsCompact K → K ⊆ e.target → ν e he K ≠ (∞ : ℝ≥0∞))
    (c : ℕ → X) (hc_cover : (⋃ n, (chartAt ℂ (c n)).source) = Set.univ) :
    ∃ μ : Measure X,
      (∀ K : Set X, IsCompact K → μ K ≠ (∞ : ℝ≥0∞)) ∧
        ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X),
          Measure.map e (μ.restrict e.source) = ν e he := by
  refine ⟨chartMeasureGluingMeasure ν c, ?_, ?_⟩
  · exact chartMeasureGluingMeasure_finite_on_compact
      X ν hsupport hcompat hfinite c hc_cover
  · exact chartMeasureGluingMeasure_chart_pushforward X ν hsupport hcompat c hc_cover

/--
%%handwave
name:
  Gluing compatible chart measures from a countable cover
statement:
  A compatible family of locally finite Borel measures in coordinate charts,
  supported on their chart images, glues to a global Borel measure once a
  countable chart-source cover has been fixed.
proof:
  Replace the countable cover by the disjoint Borel pieces obtained by
  subtracting the earlier chart sources.  Pull the coordinate measure on each
  chart image back to its corresponding piece and sum these measures.  The
  compatibility hypothesis rewrites every piece inside any target chart as a
  restriction of that target chart measure, and the pieces partition the chart
  source.  Compact finiteness follows from compactness and a finite chart
  subcover.
-/
theorem exists_measure_with_compatible_countable_chart_pushforwards
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X] [Nonempty X]
    (ν : ∀ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X → Measure ℂ)
    (hsupport :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X),
        (ν e he).restrict e.target = ν e he)
    (hcompat :
      ∀ (e e' : OpenPartialHomeomorph X ℂ)
          (he : e ∈ atlas ℂ X) (he' : e' ∈ atlas ℂ X),
        Measure.map (surfaceChartTransition e e')
          ((ν e' he').restrict (surfaceChartOverlapDomain e e')) =
          (ν e he).restrict (surfaceChartOverlapRange e e'))
    (hfinite :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
        (K : Set ℂ), IsCompact K → K ⊆ e.target → ν e he K ≠ (∞ : ℝ≥0∞))
    (S : Set X) (_hS_countable : S.Countable)
    (_hS_cover : (⋃ x ∈ S, (chartAt ℂ x).source) = Set.univ) :
    ∃ μ : Measure X,
      (∀ K : Set X, IsCompact K → μ K ≠ (∞ : ℝ≥0∞)) ∧
        ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X),
          Measure.map e (μ.restrict e.source) = ν e he := by
  let c : ℕ → X := Set.enumerateCountable _hS_countable Classical.ofNonempty
  have hc_cover : (⋃ n, (chartAt ℂ (c n)).source) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    have hy : y ∈ ⋃ x ∈ S, (chartAt ℂ x).source := by
      simp [_hS_cover]
    rcases Set.mem_iUnion.mp hy with ⟨x, hyx⟩
    rcases Set.mem_iUnion.mp hyx with ⟨hxS, hyU⟩
    obtain ⟨n, hn⟩ := Set.subset_range_enumerate _hS_countable
      Classical.ofNonempty hxS
    exact Set.mem_iUnion.mpr ⟨n, by simpa [c, hn] using hyU⟩
  exact exists_measure_with_compatible_nat_chart_pushforwards
    X ν hsupport hcompat hfinite c hc_cover

/--
%%handwave
name:
  Gluing compatible chart measures
statement:
  A compatible family of locally finite Borel measures in coordinate charts
  which are supported on their chart images glues to a global Borel measure
  whose restriction to every chart has the prescribed coordinate pushforward.
proof:
  First choose a countable chart-source cover.  Then apply the countable
  gluing construction, using support on chart images to rule out invisible
  mass outside the coordinate domains.
-/
theorem exists_measure_with_compatible_chart_pushforwards
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [T2Space X] [Nonempty X]
    (ν : ∀ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X → Measure ℂ)
    (hsupport :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X),
        (ν e he).restrict e.target = ν e he)
    (hcompat :
      ∀ (e e' : OpenPartialHomeomorph X ℂ)
          (he : e ∈ atlas ℂ X) (he' : e' ∈ atlas ℂ X),
        Measure.map (surfaceChartTransition e e')
          ((ν e' he').restrict (surfaceChartOverlapDomain e e')) =
          (ν e he).restrict (surfaceChartOverlapRange e e'))
    (hfinite :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
        (K : Set ℂ), IsCompact K → K ⊆ e.target → ν e he K ≠ (∞ : ℝ≥0∞)) :
      ∃ μ : Measure X,
      (∀ K : Set X, IsCompact K → μ K ≠ (∞ : ℝ≥0∞)) ∧
        ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X),
          Measure.map e (μ.restrict e.source) = ν e he := by
  rcases exists_countable_chartAt_source_cover X with
    ⟨S, hS_countable, hS_cover⟩
  exact exists_measure_with_compatible_countable_chart_pushforwards
    X ν hsupport hcompat hfinite S hS_countable hS_cover

/--
%%handwave
name:
  Gluing compatible coordinate volume measures
statement:
  A compatible family of smooth positive coordinate volume measures on the
  Borel charts of a surface glues to a global Borel measure whose local
  coordinate expressions are exactly the prescribed ones.
proof:
  Define the measure of a Borel set by computing it locally in charts and
  gluing along a chart cover.  Compatibility on overlaps proves independence
  of the chosen chart.  The Borel measurable structure ensures that chart
  restrictions and smooth transition maps are measurable, so the glued
  premeasure extends to a measure on the surface.
-/
theorem exists_measure_with_riemannian_chart_pushforwards
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [T2Space X] [Nonempty X]
    (g : SmoothRiemannianMetricOnSurface X)
    (_hcompat : RiemannianVolumeChartMeasuresCompatible g) :
    ∃ μ : Measure X, IsRiemannianVolumeMeasureOnSurface g μ := by
  rcases exists_measure_with_compatible_chart_pushforwards X
      (fun e _he ↦ riemannianVolumeChartMeasure g e)
      (by
        intro e _he
        exact riemannianVolumeChartMeasure_restrict_target g e)
      (by
        intro e e' he he'
        exact _hcompat e e' he he')
      (by
        intro e he K hK hK_subset
        exact riemannianVolumeChartMeasure_finite_on_compact X g e he K hK hK_subset)
    with ⟨μ, hμ_finite, hμ_charts⟩
  refine ⟨μ, ⟨?_, hμ_charts⟩⟩
  exact
    { finite_on_compact := hμ_finite
      chart_density := by
        intro e he
        refine ⟨surfaceMetricVolumeDensityInChart g e, ?_, ?_, ?_⟩
        · exact (surfaceMetricVolumeDensityInChart_smooth_positive X g e he).1
        · exact (surfaceMetricVolumeDensityInChart_smooth_positive X g e he).2
        · simpa [riemannianVolumeChartMeasure] using hμ_charts e he }

/--
%%handwave
name:
  Existence of the Riemannian volume measure
statement:
  On a smooth surface equipped with the Borel measurable structure, a smooth
  Riemannian metric admits a Riemannian volume measure whose local coordinate
  densities are the square root of the metric determinant.
proof:
  Construct the local measures in coordinate charts from Lebesgue measure
  with the metric determinant density.  The transformation law for Gram
  determinants and the smooth change-of-variables theorem show that these
  local measures agree on chart overlaps, so they glue to a global Borel
  measure.
-/
theorem exists_riemannianVolumeMeasureOnSurface
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [T2Space X] [Nonempty X]
    (g : SmoothRiemannianMetricOnSurface X) :
    ∃ μ : Measure X, IsRiemannianVolumeMeasureOnSurface g μ := by
  exact exists_measure_with_riemannian_chart_pushforwards X g
    (riemannianVolumeChartMeasuresCompatible_of_smoothMetric X g)

/--
%%handwave
name:
  Surface Riemannian volume from the manifold construction
statement:
  A smooth Riemannian metric on a surface, regarded as a metric on its
  underlying real manifold, has the general finite-dimensional Riemannian
  volume measure.
proof:
  Apply the manifold Riemannian-volume construction to the underlying real
  smooth manifold metric.
-/
theorem exists_riemannianVolumeMeasureOnSurface_as_manifold
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [T2Space X]
    (g : SmoothRiemannianMetricOnSurface X) :
    ∃ μ : Measure X,
      IsRiemannianVolumeMeasureOnManifold g.toManifoldMetric μ := by
  exact exists_riemannianVolumeMeasureOnManifold g.toManifoldMetric

namespace SmoothRiemannianMetricOnSurface

/--
%%handwave
name:
  Manifold Riemannian volume of a surface metric
statement:
  The general manifold construction assigns a Riemannian volume measure to a
  surface metric after forgetting to the underlying real smooth manifold.
-/
noncomputable def manifoldVolume {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [T2Space X]
    (g : SmoothRiemannianMetricOnSurface X) : Measure X :=
  SmoothRiemannianMetricOnManifold.volume g.toManifoldMetric

/--
%%handwave
name:
  The manifold volume of a surface metric is Riemannian
statement:
  The volume measure obtained from the general manifold construction has the
  metric chart densities for the surface viewed as a real smooth manifold.
proof:
  Specialize the general metric-volume construction to the surface model; its chart density is the square root of the metric Gram determinant.
-/
theorem manifoldVolume_isRiemannian {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [T2Space X]
    (g : SmoothRiemannianMetricOnSurface X) :
    IsRiemannianVolumeMeasureOnManifold g.toManifoldMetric
      (manifoldVolume g) :=
  SmoothRiemannianMetricOnManifold.volume_isRiemannian g.toManifoldMetric

end SmoothRiemannianMetricOnSurface


end Uniformization

end JJMath
