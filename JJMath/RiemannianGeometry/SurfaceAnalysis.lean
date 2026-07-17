import JJMath.RiemannianGeometry.SurfaceVolume

/-!
# Surface Riemannian analysis infrastructure

Compact support, integration, gradients, Laplacians, and conformal background
metrics built from smooth surface Riemannian metrics.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff

namespace Uniformization
/--
%%handwave
name:
  Compact support on a surface
statement:
  A function has compact support on a surface if the closure of the set where
  it is nonzero is compact.
-/
def HasCompactSupportOnSurface {X : Type} [TopologicalSpace X]
    (f : X → ℝ) : Prop :=
  IsCompact (closure {x : X | f x ≠ 0})

/--
%%handwave
name:
  Compactly supported functions vanish at infinity
statement:
  A compactly supported real-valued function tends to zero along the
  cocompact filter.
proof:
  Outside the compact closed support the function is identically zero.
-/
theorem hasCompactSupportOnSurface_tendsto_zero_at_cocompact
    {X : Type} [TopologicalSpace X] {f : X → ℝ}
    (hf : HasCompactSupportOnSurface f) :
    Filter.Tendsto f (Filter.cocompact X) (𝓝 0) := by
  have hevent : f =ᶠ[Filter.cocompact X] fun _ : X ↦ (0 : ℝ) := by
    filter_upwards [hf.compl_mem_cocompact] with x hx
    by_contra hfx
    exact hx (subset_closure hfx)
  exact hevent.tendsto

/--
%%handwave
name:
  Support localizes integrals
statement:
  If the closed support of an integrand is contained in a set, then integrating
  over the whole space is the same as integrating over that set.
proof:
  Outside the set the function is zero, because every nonzero point belongs to
  the support and hence to the closed support.  The usual set-integral
  localization lemma then applies.
-/
theorem integral_eq_setIntegral_of_tsupport_subset {X : Type}
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X}
    {s : Set X} {φ : X → ℝ} (hφ_support : tsupport φ ⊆ s) :
    ∫ x, φ x ∂μ = ∫ x in s, φ x ∂μ := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := μ) (s := s) (f := φ) ?_).symm
  intro x hx
  by_contra hxφ
  exact hx (hφ_support (subset_tsupport φ hxφ))

/--
%%handwave
name:
  Continuous functions with compact support inside an open set are integrable
statement:
  If a function is continuous on an open set containing its compact
  topological support, then it is integrable over the ambient locally finite
  measure space.
proof:
  The support condition extends the local continuity to global continuity by
  zero outside the support.  A globally continuous compactly supported
  function is integrable for any measure finite on compact sets.
-/
theorem integrable_of_continuousOn_of_tsupport_subset_isCompact
    {X E : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {s : Set X} {φ : X → E}
    (hφ_cont : ContinuousOn φ s) (hs_open : IsOpen s)
    (hφ_support : tsupport φ ⊆ s)
    (hφ_compact : IsCompact (tsupport φ)) :
    Integrable φ μ := by
  exact
    (hφ_cont.continuous_of_tsupport_subset hs_open hφ_support).integrable_of_hasCompactSupport
      hφ_compact

/--
%%handwave
name:
  Continuous compactly supported functions are integrable for finite support measure
statement:
  If a function is continuous on its compact topological support and that
  support has finite measure, then the function is integrable.
proof:
  Integrability over the topological support follows from continuity on the
  compact set and finiteness of its measure.  Since the ordinary support is
  contained in the topological support, this is equivalent to global
  integrability.
-/
theorem integrable_of_continuousOn_tsupport_of_isCompact_of_measure_ne_top
    {X E : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E]
    {μ : Measure X} {φ : X → E}
    (hφ_cont : ContinuousOn φ (tsupport φ))
    (hφ_compact : IsCompact (tsupport φ))
    (hφ_measure : μ (tsupport φ) ≠ (∞ : ℝ≥0∞)) :
    Integrable φ μ := by
  have hφ_int_on : IntegrableOn φ (tsupport φ) μ :=
    hφ_cont.integrableOn_of_subset_isCompact hφ_compact
      (isClosed_tsupport φ).measurableSet (fun _ hx ↦ hx) hφ_measure
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport φ)).mp
    hφ_int_on

/--
%%handwave
name:
  Continuous compactly supported functions are integrable inside an open set
statement:
  If a function is continuous on an open set containing its compact
  topological support, and that support has finite measure, then the function
  is integrable.
proof:
  Restrict the continuity statement to the compact topological support and
  apply compact-support integrability for finite support measure.
-/
theorem integrable_of_continuousOn_of_tsupport_subset_isCompact_of_measure_ne_top
    {X E : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E]
    {μ : Measure X} {s : Set X} {φ : X → E}
    (hφ_cont : ContinuousOn φ s)
    (hφ_support : tsupport φ ⊆ s)
    (hφ_compact : IsCompact (tsupport φ))
    (hφ_measure : μ (tsupport φ) ≠ (∞ : ℝ≥0∞)) :
    Integrable φ μ :=
  integrable_of_continuousOn_tsupport_of_isCompact_of_measure_ne_top
    (hφ_cont.mono hφ_support) hφ_compact hφ_measure

/--
%%handwave
name:
  Restricted integrability plus vanishing off the set gives global integrability
statement:
  If a function is integrable on a set and vanishes outside that set, then it
  is integrable globally.
proof:
  This is the standard equivalence between integrability on a set and
  integrability of an integrand whose support is contained in that set.
-/
theorem integrable_of_restrict_integrable_of_forall_notMem_eq_zero
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {s : Set X} {φ : X → E}
    (hφ : Integrable φ (μ.restrict s))
    (hzero : ∀ x, x ∉ s → φ x = 0) :
    Integrable φ μ := by
  change IntegrableOn φ s μ at hφ
  exact hφ.integrable_of_forall_notMem_eq_zero hzero

/--
%%handwave
name:
  Products of smooth surface functions are smooth
statement:
  The pointwise product of two smooth real-valued functions on a surface
  region is smooth on that region.
proof:
  In every coordinate chart this is the ordinary product rule for smooth
  functions on the plane.
-/
theorem isSmoothOnSurface_mul {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u v : X → ℝ}
    (hu : IsSmoothOnSurface U u) (hv : IsSmoothOnSurface U v) :
    IsSmoothOnSurface U (fun x ↦ u x * v x) := by
  intro e he
  simpa using (hu e he).mul (hv e he)

/--
%%handwave
name:
  Finite sums of smooth surface functions are smooth
statement:
  A finite sum of smooth real-valued functions on a surface region is smooth
  on that region.
proof:
  In coordinates this is the ordinary finite-sum rule for smooth functions.
-/
theorem isSmoothOnSurface_finset_sum {X ι : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} (s : Finset ι) {u : ι → X → ℝ}
    (hu : ∀ i ∈ s, IsSmoothOnSurface U (u i)) :
    IsSmoothOnSurface U (fun x ↦ ∑ i ∈ s, u i x) := by
  intro e he
  simpa using
    (ContDiffOn.sum
      (s := s) (f := fun (i : ι) (z : ℂ) ↦ u i (e.symm z))
      (fun i hi ↦ hu i hi e he))

/--
%%handwave
name:
  Manifold-smooth real functions are smooth in surface coordinates
statement:
  A smooth real-valued function on the underlying real smooth surface is
  smooth when written in every complex coordinate chart.
proof:
  Compose the smooth function with the inverse of a surface chart.  Since the
  surface chart is a smooth real chart and the target is the real line, the
  resulting coordinate expression is an ordinary smooth function on the chart
  image.
-/
theorem isSmoothOnSurface_of_contMDiffMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (u : C^∞⟮SurfaceRealModel, X; 𝓘(ℝ, ℝ), ℝ⟯) :
    IsSmoothOnSurface (Set.univ : Set X) (fun x ↦ u x) := by
  intro e he
  have hsymm : ContMDiffOn SurfaceRealModel SurfaceRealModel ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := SurfaceRealModel) (n := ∞) he)
  have hcomp : ContMDiffOn SurfaceRealModel 𝓘(ℝ, ℝ) ∞
      (fun z : ℂ ↦ u (e.symm z)) e.target := by
    exact u.contMDiff.contMDiffOn.comp (t := Set.univ) hsymm
      (fun _ _ ↦ by simp)
  have hcd : ContDiffOn ℝ ∞ (fun z : ℂ ↦ u (e.symm z)) e.target := by
    simpa [SurfaceRealModel] using (contMDiffOn_iff_contDiffOn.mp hcomp)
  simpa using hcd

/--
%%handwave
name:
  Compact support is preserved by multiplication on the right
statement:
  Multiplying any function by a compactly supported function gives a
  compactly supported function.
proof:
  The support of the product is contained in the support of the compactly
  supported factor.
-/
theorem hasCompactSupportOnSurface_mul_left {X : Type} [TopologicalSpace X]
    {u v : X → ℝ} (hv : HasCompactSupportOnSurface v) :
    HasCompactSupportOnSurface (fun x ↦ u x * v x) := by
  exact hv.of_isClosed_subset (isClosed_tsupport _)
    tsupport_mul_subset_right

/--
%%handwave
name:
  Compact support is preserved by multiplication on the left
statement:
  Multiplying a compactly supported function by any function gives a
  compactly supported function.
proof:
  The support of the product is contained in the support of the compactly
  supported factor.
-/
theorem hasCompactSupportOnSurface_mul_right {X : Type} [TopologicalSpace X]
    {u v : X → ℝ} (hu : HasCompactSupportOnSurface u) :
    HasCompactSupportOnSurface (fun x ↦ u x * v x) := by
  exact hu.of_isClosed_subset (isClosed_tsupport _)
    tsupport_mul_subset_left

/--
%%handwave
name:
  Finite sums of compactly supported surface functions have compact support
statement:
  A finite sum of compactly supported real-valued functions on a surface is
  compactly supported.
proof:
  Compact support is closed under addition, and induction over the finite set
  gives the result.
-/
theorem hasCompactSupportOnSurface_finset_sum {X ι : Type}
    [TopologicalSpace X] (s : Finset ι) {u : ι → X → ℝ}
    (hu : ∀ i ∈ s, HasCompactSupportOnSurface (u i)) :
    HasCompactSupportOnSurface (fun x ↦ ∑ i ∈ s, u i x) := by
  classical
  have hcompact : HasCompactSupport (fun x : X ↦ ∑ i ∈ s, u i x) := by
    induction s using Finset.induction_on with
    | empty =>
        simp [HasCompactSupport]
    | insert i s hi ih =>
        have hi_compact : HasCompactSupport (u i) := by
          simpa [HasCompactSupportOnSurface, HasCompactSupport] using
            hu i (Finset.mem_insert_self i s)
        have hs_compact :
            HasCompactSupport (fun x : X ↦ ∑ j ∈ s, u j x) :=
          ih fun j hj ↦ hu j (Finset.mem_insert_of_mem hj)
        have hadd :
            HasCompactSupport (u i + fun x : X ↦ ∑ j ∈ s, u j x) :=
          HasCompactSupport.add hi_compact hs_compact
        simpa [Finset.sum_insert hi, Pi.add_apply] using hadd
  simpa [HasCompactSupportOnSurface, HasCompactSupport] using hcompact

/--
%%handwave
name:
  Measure geometry of a surface metric
statement:
  The measure part of the background geometry is the Riemannian area measure
  attached to the smooth metric.
-/
structure SurfaceMetricMeasureGeometry (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X) where
  /-- The measurable structure contains the Borel sets. -/
  opensMeasurable : OpensMeasurableSpace X
  /-- The Riemannian area measure. -/
  volume : Measure X
  /-- The measure is the Riemannian volume measure of the metric. -/
  volume_isRiemannian : IsRiemannianVolumeMeasureOnSurface metric volume

namespace SurfaceMetricMeasureGeometry

/-- The Riemannian volume measure is smooth and positive in coordinates. -/
theorem smoothPositive {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {metric : SmoothRiemannianMetricOnSurface X}
    (μg : SurfaceMetricMeasureGeometry X metric) :
    SmoothPositiveAreaMeasureOnSurface X μg.volume :=
  μg.volume_isRiemannian.1

/--
%%handwave
name:
  Riemannian area measure is finite on compact sets
statement:
  The Riemannian area measure attached to a smooth surface metric is finite
  on compact sets.
proof:
  This is one of the defining properties of the smooth positive area measure
  used to package the Riemannian volume measure.
-/
theorem isFiniteMeasureOnCompacts {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {metric : SmoothRiemannianMetricOnSurface X}
    (μg : SurfaceMetricMeasureGeometry X metric) :
    IsFiniteMeasureOnCompacts μg.volume := by
  constructor
  intro K hK
  exact lt_top_iff_ne_top.mpr (μg.volume_isRiemannian.1.finite_on_compact K hK)


end SurfaceMetricMeasureGeometry

/--
%%handwave
name:
  Surface differential
statement:
  A stored differential represents the exterior derivative of a real-valued
  function when it is the manifold derivative from the real smooth surface to
  the real line.
-/
def IsSurfaceDifferential {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (f : X → ℝ) (df : X → ℂ →L[ℝ] ℝ) : Prop :=
  ∀ x : X, HasMFDerivAt SurfaceRealModel 𝓘(ℝ, ℝ) f x (df x)

/--
%%handwave
name:
  Smooth surface functions are manifold differentiable
statement:
  A function that is smooth in all surface coordinates is manifold
  differentiable as a map from the real smooth surface to the real line.
proof:
  Unfold the definition of coordinate smoothness.  In the source chart at a
  point and the standard chart on the real line, the written-in-coordinates
  representative is one of the smooth coordinate representatives, hence it is
  differentiable.
-/
theorem isSmoothOnSurface_univ_mdifferentiableAt {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    {f : X → ℝ} (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (x : X) :
    MDifferentiableAt SurfaceRealModel 𝓘(ℝ, ℝ) f x := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have he : e ∈ atlas ℂ X := by
    simp [e]
  have hx_source : x ∈ e.source := by
    simp [e]
  have hchart :
      ContDiffOn ℝ ∞ (fun z : ℂ ↦ f (e.symm z)) e.target := by
    have h := hf e he
    simpa [e] using h
  have hmaps : Set.MapsTo f e.source (chartAt ℝ (f x)).source := by
    intro y _hy
    simp
  have hcontMDiffOn :
      ContMDiffOn SurfaceRealModel 𝓘(ℝ, ℝ) ∞ f e.source := by
    rw [contMDiffOn_iff_of_mem_maximalAtlas'
      (I := SurfaceRealModel) (I' := 𝓘(ℝ, ℝ))
      (e := e) (e' := chartAt ℝ (f x))
      (IsManifold.chart_mem_maximalAtlas (I := SurfaceRealModel) x)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, ℝ)) (f x))
      (by intro y hy; exact hy) hmaps]
    rw [← e.image_source_eq_target] at hchart
    simpa [SurfaceRealModel, e, Function.comp_def] using hchart
  have hcontMDiffAt :
      ContMDiffAt SurfaceRealModel 𝓘(ℝ, ℝ) ∞ f x :=
    hcontMDiffOn.contMDiffAt (e.open_source.mem_nhds hx_source)
  exact hcontMDiffAt.mdifferentiableAt (by simp)

/--
%%handwave
name:
  Locally smooth surface functions are manifold smooth at points
statement:
  If a real-valued surface function is smooth on an open surface region, then
  it is smooth as a manifold map at every point of that region.
proof:
  Use a surface chart centered at the point.  In that chart, the hypothesis is
  precisely smoothness of the coordinate representative on the chart image
  over the region.  The local chart criterion for manifold smoothness gives
  manifold smoothness at the point.
-/
theorem isSmoothOnSurface_contMDiffAt_of_mem {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    {U : Set X} (hU_open : IsOpen U)
    {f : X → ℝ} (hf : IsSmoothOnSurface U f)
    {x : X} (hxU : x ∈ U) :
    ContMDiffAt SurfaceRealModel 𝓘(ℝ, ℝ) ∞ f x := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have he : e ∈ atlas ℂ X := by
    simp [e]
  have hx_source : x ∈ e.source := by
    simp [e]
  have hchart :
      ContDiffOn ℝ ∞
        (fun z : ℂ ↦ f (e.symm z)) (e.target ∩ e.symm ⁻¹' U) := by
    have h := hf e he
    simpa [e] using h
  have himage :
      (fun a ↦ e a) '' (e.source ∩ U) = e.target ∩ e.symm ⁻¹' U := by
    ext z
    constructor
    · rintro ⟨y, ⟨hy_source, hyU⟩, rfl⟩
      exact ⟨e.map_source hy_source, by simpa [e.left_inv hy_source] using hyU⟩
    · intro hz
      refine ⟨e.symm z, ⟨e.map_target hz.1, hz.2⟩, ?_⟩
      exact e.right_inv hz.1
  have hmaps : Set.MapsTo f (e.source ∩ U) (chartAt ℝ (f x)).source := by
    intro y _hy
    simp
  have hs : e.source ∩ U ⊆ e.source := Set.inter_subset_left
  have hcontMDiffOn :
      ContMDiffOn SurfaceRealModel 𝓘(ℝ, ℝ) ∞ f (e.source ∩ U) := by
    rw [contMDiffOn_iff_of_mem_maximalAtlas'
      (I := SurfaceRealModel) (I' := 𝓘(ℝ, ℝ))
      (e := e) (e' := chartAt ℝ (f x))
      (IsManifold.chart_mem_maximalAtlas (I := SurfaceRealModel) x)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, ℝ)) (f x))
      hs hmaps]
    simpa [SurfaceRealModel, e, Function.comp_def, himage] using hchart
  have hnhds : e.source ∩ U ∈ 𝓝 x :=
    (e.open_source.inter hU_open).mem_nhds ⟨hx_source, hxU⟩
  have hcontMDiffAt :
      ContMDiffAt SurfaceRealModel 𝓘(ℝ, ℝ) ∞ f x :=
    hcontMDiffOn.contMDiffAt hnhds
  exact hcontMDiffAt

/--
%%handwave
name:
  Locally smooth surface functions are manifold differentiable
statement:
  If a real-valued surface function is smooth on an open surface region, then
  it is manifold differentiable at every point of that region.
proof:
  Local manifold smoothness implies manifold differentiability.
-/
theorem isSmoothOnSurface_mdifferentiableAt_of_mem {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    {U : Set X} (hU_open : IsOpen U)
    {f : X → ℝ} (hf : IsSmoothOnSurface U f)
    {x : X} (hxU : x ∈ U) :
    MDifferentiableAt SurfaceRealModel 𝓘(ℝ, ℝ) f x :=
  (isSmoothOnSurface_contMDiffAt_of_mem hU_open hf hxU).mdifferentiableAt
    (by simp)

/--
%%handwave
name:
  Coordinate-smooth surface functions are manifold smooth
statement:
  A real-valued function that is smooth in every surface coordinate chart is
  smooth as a map from the underlying real smooth surface to the real line.
proof:
  Around each point, use the surface chart centered at that point and the
  standard chart on the real line.  The coordinate representative is smooth by
  hypothesis, so the local chart criterion gives manifold smoothness at the
  point.  Pointwise smoothness gives global smoothness.
-/
theorem isSmoothOnSurface_univ_contMDiff {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    {f : X → ℝ} (hf : IsSmoothOnSurface (Set.univ : Set X) f) :
    ContMDiff SurfaceRealModel 𝓘(ℝ, ℝ) ∞ f := by
  intro x
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have he : e ∈ atlas ℂ X := by
    simp [e]
  have hx_source : x ∈ e.source := by
    simp [e]
  have hchart :
      ContDiffOn ℝ ∞ (fun z : ℂ ↦ f (e.symm z)) e.target := by
    have h := hf e he
    simpa [e] using h
  have hmaps : Set.MapsTo f e.source (chartAt ℝ (f x)).source := by
    intro y _hy
    simp
  have hcontMDiffOn :
      ContMDiffOn SurfaceRealModel 𝓘(ℝ, ℝ) ∞ f e.source := by
    rw [contMDiffOn_iff_of_mem_maximalAtlas'
      (I := SurfaceRealModel) (I' := 𝓘(ℝ, ℝ))
      (e := e) (e' := chartAt ℝ (f x))
      (IsManifold.chart_mem_maximalAtlas (I := SurfaceRealModel) x)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, ℝ)) (f x))
      (by intro y hy; exact hy) hmaps]
    rw [← e.image_source_eq_target] at hchart
    simpa [SurfaceRealModel, e, Function.comp_def] using hchart
  exact hcontMDiffOn.contMDiffAt (e.open_source.mem_nhds hx_source)

/--
%%handwave
name:
  Exterior derivative of a surface function
statement:
  The exterior derivative of a real-valued function on a smooth surface is
  its manifold derivative, viewed as a covector on the tangent plane.
-/
noncomputable def surfaceExteriorDerivative {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (f : X → ℝ) : X → ℂ →L[ℝ] ℝ :=
  fun x ↦ mfderiv SurfaceRealModel 𝓘(ℝ, ℝ) f x

/--
%%handwave
name:
  Exterior derivative represents the surface differential
statement:
  For a smooth surface function, the exterior derivative is the surface
  differential.
proof:
  Smoothness in surface coordinates gives manifold differentiability at every
  point.  The exterior derivative is defined to be this manifold derivative.
-/
theorem surfaceExteriorDerivative_isSurfaceDifferential {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    {f : X → ℝ} (hf : IsSmoothOnSurface (Set.univ : Set X) f) :
    IsSurfaceDifferential f (surfaceExteriorDerivative f) := by
  intro x
  simpa [surfaceExteriorDerivative] using
    (isSmoothOnSurface_univ_mdifferentiableAt hf x).hasMFDerivAt

/--
%%handwave
name:
  Exterior derivative in local coordinates
statement:
  If a surface function is smooth on an open region, then on that region its
  exterior derivative applied to coordinate tangent vectors is the ordinary
  derivative of its coordinate representative.
proof:
  Local surface smoothness gives manifold differentiability at the point.
  The chain rule for the inverse chart identifies the manifold derivative of
  the coordinate representative with the exterior derivative composed with
  the chart tangent map.
-/
theorem surfaceExteriorDerivative_apply_chartTangentMap_of_isSmoothOnSurface_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    {U : Set X} (hU_open : IsOpen U)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (f : X → ℝ) (hf : IsSmoothOnSurface U f) :
    ∀ z ∈ e.target ∩ e.symm ⁻¹' U, ∀ v : ℂ,
      surfaceExteriorDerivative f (e.symm z)
          (surfaceChartTangentMap e z v) =
        fderiv ℝ (fun w : ℂ ↦ f (e.symm w)) z v := by
  intro z hz v
  have hz_target : z ∈ e.target := hz.1
  have hxU : e.symm z ∈ U := hz.2
  have hdf :
      HasMFDerivAt SurfaceRealModel 𝓘(ℝ, ℝ) f (e.symm z)
        (surfaceExteriorDerivative f (e.symm z)) := by
    simpa [surfaceExteriorDerivative] using
      (isSmoothOnSurface_mdifferentiableAt_of_mem hU_open hf hxU).hasMFDerivAt
  have hgrad :
      mfderiv SurfaceRealModel 𝓘(ℝ, ℝ) f (e.symm z) =
        surfaceExteriorDerivative f (e.symm z) :=
    hdf.mfderiv
  have hsymm :
      MDifferentiableWithinAt SurfaceRealModel SurfaceRealModel e.symm e.target z :=
    mdifferentiableOn_atlas_symm (I := SurfaceRealModel) he z hz_target
  have huniq : UniqueMDiffWithinAt SurfaceRealModel e.target z := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact e.open_target.uniqueDiffWithinAt hz_target
  have hchain :
      mfderivWithin SurfaceRealModel 𝓘(ℝ, ℝ)
          (fun w : ℂ ↦ f (e.symm w)) e.target z =
        (mfderiv SurfaceRealModel 𝓘(ℝ, ℝ) f (e.symm z)).comp
          (mfderivWithin SurfaceRealModel SurfaceRealModel e.symm e.target z) := by
    simpa [Function.comp_def] using
      (mfderiv_comp_mfderivWithin
        (I := SurfaceRealModel) (I' := SurfaceRealModel) (I'' := 𝓘(ℝ, ℝ))
        (f := e.symm) (g := f) (s := e.target) (x := z)
        hdf.mdifferentiableAt hsymm huniq)
  have htan :
      mfderivWithin SurfaceRealModel SurfaceRealModel e.symm e.target z =
        surfaceChartTangentMap e z := by
    simp [surfaceChartTangentMap, mfderivWithin, writtenInExtChartAt,
      SurfaceRealModel, hsymm]
    rfl
  have hwithin :
      fderivWithin ℝ (fun w : ℂ ↦ f (e.symm w)) e.target z =
        fderiv ℝ (fun w : ℂ ↦ f (e.symm w)) z :=
    fderivWithin_of_isOpen e.open_target hz_target
  rw [← hgrad, ← hwithin, ← htan]
  change
    ((mfderiv SurfaceRealModel 𝓘(ℝ, ℝ) f (e.symm z)).comp
        (mfderivWithin SurfaceRealModel SurfaceRealModel e.symm e.target z)) v =
      (fderivWithin ℝ (fun w : ℂ ↦ f (e.symm w)) e.target z) v
  rw [← hchain]
  simp [SurfaceRealModel]
  rfl

/--
%%handwave
name:
  Differential vanishes off the closed support
statement:
  The differential of a smooth function vanishes at every point outside its
  closed support.
proof:
  Outside the closed support the function agrees with zero in a neighbourhood
  of the point.  The derivative is therefore the derivative of the constant
  zero function, and uniqueness of the manifold derivative gives the claim.
-/
theorem surfaceDifferential_eq_zero_of_notMem_tsupport {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    {f : X → ℝ} {df : X → ℂ →L[ℝ] ℝ}
    (hdf : IsSurfaceDifferential f df) {x : X}
    (hx : x ∉ tsupport f) :
    df x = 0 := by
  have h_event :
      f =ᶠ[𝓝 x] (fun _ : X ↦ (0 : ℝ)) := by
    simpa using (notMem_tsupport_iff_eventuallyEq.mp hx)
  have hzero :
      HasMFDerivAt SurfaceRealModel 𝓘(ℝ, ℝ) f x 0 :=
    (hasMFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq h_event
  exact hasMFDerivAt_unique (hdf x) hzero

/--
%%handwave
name:
  Surface differentials commute with finite sums
statement:
  If each function in a finite family has a represented surface differential,
  then the finite sum has the finite sum of those represented differentials.
proof:
  This is the finite-sum rule for manifold derivatives.
-/
theorem surfaceDifferential_finset_sum {X ι : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (s : Finset ι) (φ : ι → X → ℝ)
    (dφ : ι → X → ℂ →L[ℝ] ℝ)
    (hφ : ∀ i ∈ s, IsSurfaceDifferential (φ i) (dφ i)) :
    IsSurfaceDifferential
      (fun x : X ↦ ∑ i ∈ s, φ i x)
      (fun x : X ↦ ∑ i ∈ s, dφ i x) := by
  intro x
  have hsum :
      HasMFDerivAt SurfaceRealModel 𝓘(ℝ, ℝ)
        (∑ i ∈ s, φ i) x (∑ i ∈ s, dφ i x) :=
    HasMFDerivAt.sum
      (I := SurfaceRealModel)
      (t := s) (f := φ) (f' := fun i ↦ dφ i x)
      (z := x) (fun i hi ↦ hφ i hi x)
  convert hsum using 1
  ext y
  simp

/--
%%handwave
name:
  Surface differentials respect finite decompositions
statement:
  If a function is a finite sum of functions and all the represented surface
  differentials are fixed, then the represented differential of the sum is the
  finite sum of the represented differentials.
proof:
  The previous finite-sum rule gives a derivative for the sum.  Since the
  original function agrees everywhere with that finite sum, it has the same
  derivative, and uniqueness of manifold derivatives identifies the stored
  covectors.
-/
theorem surfaceDifferential_eq_finset_sum_of_pointwise_sum {X ι : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (s : Finset ι) {η : X → ℝ} {dη : X → ℂ →L[ℝ] ℝ}
    (θ : ι → X → ℝ) (dθ : ι → X → ℂ →L[ℝ] ℝ)
    (hη : IsSurfaceDifferential η dη)
    (hθ : ∀ i ∈ s, IsSurfaceDifferential (θ i) (dθ i))
    (hη_sum : ∀ x : X, η x = ∑ i ∈ s, θ i x)
    (x : X) :
    dη x = ∑ i ∈ s, dθ i x := by
  have hsum :
      IsSurfaceDifferential
        (fun y : X ↦ ∑ i ∈ s, θ i y)
        (fun y : X ↦ ∑ i ∈ s, dθ i y) :=
    surfaceDifferential_finset_sum s θ dθ hθ
  have h_event :
      η =ᶠ[𝓝 x] (fun y : X ↦ ∑ i ∈ s, θ i y) :=
    Filter.Eventually.of_forall hη_sum
  have hsum_at :
      HasMFDerivAt SurfaceRealModel 𝓘(ℝ, ℝ) η x
        (∑ i ∈ s, dθ i x) :=
    (hsum x).congr_of_eventuallyEq h_event
  exact hasMFDerivAt_unique (hη x) hsum_at

/--
%%handwave
name:
  Cotangent metric duality
statement:
  A cotangent inner product is dual to a Riemannian metric when every
  covector has a unique metric-dual tangent vector and the cotangent pairing
  is evaluation against that dual vector.
-/
def IsCotangentInnerForSurfaceMetric {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (cotangentInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ) : Prop :=
  ∀ x ξ, letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
    ∃! v : ℂ,
    (∀ w : TangentSpace SurfaceRealModel x,
      ξ w = g.toContMDiffRiemannianMetric.inner x v w) ∧
      ∀ η : ℂ →L[ℝ] ℝ, cotangentInner x ξ η = η v

/--
%%handwave
name:
  Metric-dual cotangent pairing vanishes on zero
statement:
  A metric-dual cotangent pairing is zero when its second covector is zero.
proof:
  The definition represents the first covector by a metric-dual tangent
  vector, and the pairing with the second covector is evaluation of that
  second covector on this vector.
-/
theorem cotangentInner_zero_right_of_isMetricDual {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (cotangentInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (hinner : IsCotangentInnerForSurfaceMetric g cotangentInner)
    (x : X) (ξ : ℂ →L[ℝ] ℝ) :
    cotangentInner x ξ 0 = 0 := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  rcases hinner x ξ with ⟨v, hv, _hv_unique⟩
  simpa using hv.2 (0 : ℂ →L[ℝ] ℝ)

/--
%%handwave
name:
  Metric-dual cotangent pairing is linear in the second covector
statement:
  A metric-dual cotangent pairing sends a finite sum in its second covector
  argument to the corresponding finite sum of pairings.
proof:
  Represent the first covector by its metric-dual tangent vector.  Pairing
  with the second covector is evaluation on this vector, and evaluation is
  linear.
-/
theorem cotangentInner_finset_sum_right_of_isMetricDual {X ι : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (cotangentInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (hinner : IsCotangentInnerForSurfaceMetric g cotangentInner)
    (s : Finset ι) (x : X) (ξ : ℂ →L[ℝ] ℝ)
    (η : ι → ℂ →L[ℝ] ℝ) :
    cotangentInner x ξ (∑ i ∈ s, η i) =
      ∑ i ∈ s, cotangentInner x ξ (η i) := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  rcases hinner x ξ with ⟨v, hv, _hv_unique⟩
  calc
    cotangentInner x ξ (∑ i ∈ s, η i)
        = (∑ i ∈ s, η i) v := hv.2 (∑ i ∈ s, η i)
    _ = ∑ i ∈ s, η i v := by simp
    _ = ∑ i ∈ s, cotangentInner x ξ (η i) := by
      exact Finset.sum_congr rfl fun i _hi ↦ (hv.2 (η i)).symm

/--
%%handwave
name:
  Metric inner products are positive definite
statement:
  At each point, the bilinear form of a smooth Riemannian metric is symmetric
  and positive definite on the tangent plane.
-/
theorem smoothRiemannianMetric_inner_positiveDefinite
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) (x : X) :
    letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
    IsPositiveDefiniteSymmetricTangentForm x
      (g.toContMDiffRiemannianMetric.inner x) := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  exact ⟨
    g.toContMDiffRiemannianMetric.symm x,
    g.toContMDiffRiemannianMetric.pos x⟩

/--
%%handwave
name:
  Metric inner products are coercive
statement:
  At each point, the metric bilinear form dominates a positive multiple of
  the squared Euclidean norm in tangent coordinates.
proof:
  This is the finite-dimensional coercivity of positive definite symmetric
  forms on the model tangent plane.
-/
theorem smoothRiemannianMetric_inner_isCoercive
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) (x : X) :
    letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
    let B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
      g.toContMDiffRiemannianMetric.inner x
    IsCoercive B := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    g.toContMDiffRiemannianMetric.inner x
  change IsCoercive B
  exact positiveDefiniteSymmetricBilinearForm_complex_isCoercive
    B
    (smoothRiemannianMetric_inner_positiveDefinite g x)

/--
%%handwave
name:
  Metric dual of a covector
statement:
  The metric dual of a covector is the tangent vector whose metric pairing
  against every tangent vector recovers the covector.
-/
noncomputable def surfaceMetricDualCovector
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) (x : X)
    (ξ : ℂ →L[ℝ] ℝ) : ℂ :=
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    g.toContMDiffRiemannianMetric.inner x
  let hB : IsCoercive B := smoothRiemannianMetric_inner_isCoercive g x
  hB.continuousLinearEquivOfBilin.symm
    ((InnerProductSpace.toDual ℝ ℂ).symm ξ)

/--
%%handwave
name:
  Metric dual represents a covector
statement:
  The metric dual of a covector represents it by metric pairing with tangent
  vectors.
proof:
  Use Fréchet-Riesz to represent the covector in the Euclidean Hilbert
  structure, then use Lax-Milgram for the coercive metric bilinear form.
-/
theorem surfaceMetricDualCovector_spec
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) (x : X)
    (ξ : ℂ →L[ℝ] ℝ) :
    letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
    ∀ w : TangentSpace SurfaceRealModel x,
      ξ w =
        g.toContMDiffRiemannianMetric.inner x
          (surfaceMetricDualCovector g x ξ) w := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  intro w
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    g.toContMDiffRiemannianMetric.inner x
  let hB : IsCoercive B := smoothRiemannianMetric_inner_isCoercive g x
  let y : ℂ := (InnerProductSpace.toDual ℝ ℂ).symm ξ
  change ξ w = B (hB.continuousLinearEquivOfBilin.symm y) w
  calc
    ξ w = inner ℝ y w := by
      simp [y]
    _ =
        inner ℝ
          (hB.continuousLinearEquivOfBilin
            (hB.continuousLinearEquivOfBilin.symm y)) w := by
      simp
    _ = B (hB.continuousLinearEquivOfBilin.symm y) w := by
      rw [hB.continuousLinearEquivOfBilin_apply]

/--
%%handwave
name:
  Uniqueness of the metric dual covector
statement:
  A tangent vector representing a covector by metric pairing is the metric
  dual of that covector.
proof:
  Lax-Milgram identifies the coercive metric bilinear form with an invertible
  map, so the representing tangent vector is unique.
-/
theorem surfaceMetricDualCovector_unique
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) (x : X)
    (ξ : ℂ →L[ℝ] ℝ) :
    letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
    ∀ {v : ℂ},
      (∀ w : TangentSpace SurfaceRealModel x,
        ξ w = g.toContMDiffRiemannianMetric.inner x v w) →
        v = surfaceMetricDualCovector g x ξ := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  intro v hv
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    g.toContMDiffRiemannianMetric.inner x
  let hB : IsCoercive B := smoothRiemannianMetric_inner_isCoercive g x
  let y : ℂ := (InnerProductSpace.toDual ℝ ℂ).symm ξ
  change v = hB.continuousLinearEquivOfBilin.symm y
  have hy : y = hB.continuousLinearEquivOfBilin v := by
    apply hB.unique_continuousLinearEquivOfBilin
    intro w
    calc
      inner ℝ y w = ξ w := by
        simp [y]
      _ = B v w := hv w
  calc
    v = hB.continuousLinearEquivOfBilin.symm
        (hB.continuousLinearEquivOfBilin v) := by
      simp
    _ = hB.continuousLinearEquivOfBilin.symm y := by
      rw [← hy]

/--
%%handwave
name:
  Laplace-Beltrami weak characterization
statement:
  The Laplace-Beltrami operator associated to a metric, its volume measure,
  and its cotangent pairing is characterized by the integration-by-parts
  identity against compactly supported smooth test functions.
-/
def IsLaplaceBeltramiForSurfaceMetric {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (laplaceBeltrami : (X → ℝ) → X → ℝ) : Prop :=
  ∀ f η : X → ℝ,
    IsSmoothOnSurface (Set.univ : Set X) f →
    IsSmoothOnSurface (Set.univ : Set X) η →
    HasCompactSupportOnSurface η →
    Integrable (fun x ↦ laplaceBeltrami f x * η x) measureGeometry.volume →
    Integrable (fun x ↦ gradientInner x (gradient f x) (gradient η x))
      measureGeometry.volume →
    ∫ x, laplaceBeltrami f x * η x ∂measureGeometry.volume =
      - ∫ x, gradientInner x (gradient f x) (gradient η x) ∂measureGeometry.volume

/--
%%handwave
name:
  Coordinate tangent directions
statement:
  The two coordinate tangent directions of the complex plane, regarded as a
  real plane, are \(1\) and \(i\).
-/
def complexCoordinateVector : Fin 2 → ℂ
  | 0 => 1
  | 1 => Complex.I

@[simp]
theorem complexCoordinateVector_zero :
    complexCoordinateVector 0 = (1 : ℂ) := by
  rfl

@[simp]
theorem complexCoordinateVector_one :
    complexCoordinateVector 1 = Complex.I := by
  rfl

/--
%%handwave
name:
  Inverse metric coefficient in a chart
statement:
  The inverse metric coefficients in a coordinate chart are the entries of
  the inverse of the local Gram matrix of the coordinate tangent frame.
-/
noncomputable def surfaceMetricInverseGramCoeffInChart {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ) (i j : Fin 2) : ℝ :=
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let A := surfaceChartTangentMap e z
  let b := g.toContMDiffRiemannianMetric.inner (e.symm z)
  let v₁ : TangentSpace SurfaceRealModel (e.symm z) := A (1 : ℂ)
  let v₂ : TangentSpace SurfaceRealModel (e.symm z) := A Complex.I
  let a : ℝ := b v₁ v₁
  let c : ℝ := b v₁ v₂
  let d : ℝ := b v₂ v₁
  let e₂ : ℝ := b v₂ v₂
  let det : ℝ := surfaceMetricGramDetInChart g e z
  match i, j with
  | 0, 0 => det⁻¹ * e₂
  | 0, 1 => - det⁻¹ * c
  | 1, 0 => - det⁻¹ * d
  | 1, 1 => det⁻¹ * a

@[simp]
theorem surfaceMetricInverseGramCoeffInChart_zero_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ) :
    surfaceMetricInverseGramCoeffInChart g e z 0 0 =
      letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
      let A := surfaceChartTangentMap e z
      let b := g.toContMDiffRiemannianMetric.inner (e.symm z)
      let v₂ : TangentSpace SurfaceRealModel (e.symm z) := A Complex.I
      (surfaceMetricGramDetInChart g e z)⁻¹ * b v₂ v₂ := by
  simp [surfaceMetricInverseGramCoeffInChart]

@[simp]
theorem surfaceMetricInverseGramCoeffInChart_zero_one
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ) :
    surfaceMetricInverseGramCoeffInChart g e z 0 1 =
      letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
      let A := surfaceChartTangentMap e z
      let b := g.toContMDiffRiemannianMetric.inner (e.symm z)
      let v₁ : TangentSpace SurfaceRealModel (e.symm z) := A (1 : ℂ)
      let v₂ : TangentSpace SurfaceRealModel (e.symm z) := A Complex.I
      (-(surfaceMetricGramDetInChart g e z)⁻¹ * b v₁ v₂) := by
  simp [surfaceMetricInverseGramCoeffInChart]

@[simp]
theorem surfaceMetricInverseGramCoeffInChart_one_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ) :
    surfaceMetricInverseGramCoeffInChart g e z 1 0 =
      letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
      let A := surfaceChartTangentMap e z
      let b := g.toContMDiffRiemannianMetric.inner (e.symm z)
      let v₁ : TangentSpace SurfaceRealModel (e.symm z) := A (1 : ℂ)
      let v₂ : TangentSpace SurfaceRealModel (e.symm z) := A Complex.I
      (-(surfaceMetricGramDetInChart g e z)⁻¹ * b v₂ v₁) := by
  simp [surfaceMetricInverseGramCoeffInChart]

@[simp]
theorem surfaceMetricInverseGramCoeffInChart_one_one
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ) :
    surfaceMetricInverseGramCoeffInChart g e z 1 1 =
      letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
      let A := surfaceChartTangentMap e z
      let b := g.toContMDiffRiemannianMetric.inner (e.symm z)
      let v₁ : TangentSpace SurfaceRealModel (e.symm z) := A (1 : ℂ)
      (surfaceMetricGramDetInChart g e z)⁻¹ * b v₁ v₁ := by
  simp [surfaceMetricInverseGramCoeffInChart]

/--
%%handwave
name:
  Chart derivative of a surface function
statement:
  In a coordinate chart, the directional derivative of a surface function is
  the Fréchet derivative of the coordinate representative in the chosen
  coordinate direction.
-/
noncomputable def surfaceFunctionChartDirectionalDerivative {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (f : X → ℝ) (z v : ℂ) : ℝ :=
  fderiv ℝ (fun w : ℂ ↦ f (e.symm w)) z v

/--
%%handwave
name:
  Coordinate derivative component
statement:
  The coordinate derivative component \(\partial_i f\) is the derivative of
  the coordinate representative in the \(i\)-th coordinate tangent direction.
-/
noncomputable def surfaceFunctionChartDerivativeComponent {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (f : X → ℝ) (z : ℂ) (i : Fin 2) : ℝ :=
  surfaceFunctionChartDirectionalDerivative e f z (complexCoordinateVector i)

@[simp]
theorem surfaceFunctionChartDerivativeComponent_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (f : X → ℝ) (z : ℂ) :
    surfaceFunctionChartDerivativeComponent e f z 0 =
      surfaceFunctionChartDirectionalDerivative e f z (1 : ℂ) := by
  rfl

@[simp]
theorem surfaceFunctionChartDerivativeComponent_one
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (f : X → ℝ) (z : ℂ) :
    surfaceFunctionChartDerivativeComponent e f z 1 =
      surfaceFunctionChartDirectionalDerivative e f z Complex.I := by
  rfl

/--
%%handwave
name:
  Coordinate derivative components are measurable
statement:
  Each coordinate derivative component of a real surface function is a
  measurable function of the coordinate point.
proof:
  This is the Mathlib measurability theorem for the Fréchet derivative,
  evaluated on a fixed coordinate tangent vector.
-/
theorem surfaceFunctionChartDerivativeComponent_measurable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (f : X → ℝ) (i : Fin 2) :
    Measurable (fun z : ℂ ↦ surfaceFunctionChartDerivativeComponent e f z i) := by
  simpa [surfaceFunctionChartDerivativeComponent,
    surfaceFunctionChartDirectionalDerivative] using
      measurable_fderiv_apply_const ℝ
        (fun w : ℂ ↦ f (e.symm w)) (complexCoordinateVector i)

theorem surfaceFunctionChartDerivativeComponent_aestronglyMeasurable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {μ : Measure ℂ} (e : OpenPartialHomeomorph X ℂ) (f : X → ℝ)
    (i : Fin 2) :
    AEStronglyMeasurable
      (fun z : ℂ ↦ surfaceFunctionChartDerivativeComponent e f z i) μ :=
  (surfaceFunctionChartDerivativeComponent_measurable e f i).aestronglyMeasurable

/--
%%handwave
name:
  Coordinate derivative components of smooth functions are smooth
statement:
  If a surface function is smooth, then each of its coordinate derivative
  components is smooth on every chart image.
proof:
  The coordinate representative is smooth on the chart image.  Since the
  chart image is open, Mathlib's smoothness theorem for the Fréchet
  derivative gives a smooth derivative map there; evaluating this derivative
  on a fixed coordinate tangent vector is smooth.
-/
theorem surfaceFunctionChartDerivativeComponent_contDiffOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f : X → ℝ) (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (i : Fin 2) :
    ContDiffOn ℝ ∞
      (fun z : ℂ ↦ surfaceFunctionChartDerivativeComponent e f z i)
      e.target := by
  have hchart : ContDiffOn ℝ ∞
      (fun w : ℂ ↦ f (e.symm w)) e.target := by
    simpa using hf e _he
  have hfderiv : ContDiffOn ℝ ∞
      (fderiv ℝ (fun w : ℂ ↦ f (e.symm w))) e.target :=
    hchart.fderiv_of_isOpen e.open_target (by simp)
  have hvec : ContDiffOn ℝ ∞
      (fun _z : ℂ ↦ complexCoordinateVector i) e.target :=
    contDiffOn_const
  simpa [surfaceFunctionChartDerivativeComponent,
    surfaceFunctionChartDirectionalDerivative] using hfderiv.clm_apply hvec

/--
%%handwave
name:
  Local smoothness of coordinate derivative components
statement:
  If a coordinate representative of a function is smooth on an open subset of
  a chart image, then its coordinate derivative components are smooth on that
  subset.
proof:
  The derivative map of the smooth coordinate representative is smooth on the
  open set, and evaluation on a fixed coordinate vector preserves smoothness.
-/
theorem surfaceFunctionChartDerivativeComponent_contDiffOn_of_local_contDiffOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (f : X → ℝ)
    {S : Set ℂ} (hS_open : IsOpen S)
    (hf : ContDiffOn ℝ ∞ (fun w : ℂ ↦ f (e.symm w)) S)
    (i : Fin 2) :
    ContDiffOn ℝ ∞
      (fun z : ℂ ↦ surfaceFunctionChartDerivativeComponent e f z i) S := by
  have hfderiv :
      ContDiffOn ℝ ∞
        (fderiv ℝ (fun w : ℂ ↦ f (e.symm w))) S :=
    hf.fderiv_of_isOpen hS_open (by simp)
  have hvec : ContDiffOn ℝ ∞
      (fun _z : ℂ ↦ complexCoordinateVector i) S :=
    contDiffOn_const
  simpa [surfaceFunctionChartDerivativeComponent,
    surfaceFunctionChartDirectionalDerivative] using hfderiv.clm_apply hvec

/--
%%handwave
name:
  Coordinate inverse-metric pairing of covectors
statement:
  In a coordinate chart, the coordinate inverse-metric pairing of two
  covectors is the contraction of their components on the coordinate tangent
  frame with the inverse Gram matrix.
-/
noncomputable def surfaceMetricCoordinateCotangentPairingInChart {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ)
    (ξ η : ℂ →L[ℝ] ℝ) : ℝ :=
  let A := surfaceChartTangentMap e z
  ∑ i : Fin 2, ∑ j : Fin 2,
    surfaceMetricInverseGramCoeffInChart g e z i j *
      ξ (A (complexCoordinateVector i)) *
        η (A (complexCoordinateVector j))

/--
%%handwave
name:
  Coordinate inverse-metric pairing
statement:
  In a coordinate chart, the inverse-metric pairing of two differentials is
  the sum \(g^{ij}\partial_i f\,\partial_j h\).
-/
noncomputable def surfaceMetricCoordinateGradientPairingInChart {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (f h : X → ℝ) (z : ℂ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    surfaceMetricInverseGramCoeffInChart g e z i j *
      surfaceFunctionChartDerivativeComponent e f z i *
        surfaceFunctionChartDerivativeComponent e h z j

/--
%%handwave
name:
  Coordinate inverse-metric pairing expansion
statement:
  The coordinate inverse-metric pairing is the four-term expansion of
  \(g^{ij}\partial_i f\,\partial_j h\) in the coordinate directions \(1,i\).
-/
theorem surfaceMetricCoordinateGradientPairingInChart_eq_four_terms
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (f h : X → ℝ) (z : ℂ) :
    surfaceMetricCoordinateGradientPairingInChart g e f h z =
      surfaceMetricInverseGramCoeffInChart g e z 0 0 *
          surfaceFunctionChartDerivativeComponent e f z 0 *
            surfaceFunctionChartDerivativeComponent e h z 0 +
        surfaceMetricInverseGramCoeffInChart g e z 0 1 *
          surfaceFunctionChartDerivativeComponent e f z 0 *
            surfaceFunctionChartDerivativeComponent e h z 1 +
        surfaceMetricInverseGramCoeffInChart g e z 1 0 *
          surfaceFunctionChartDerivativeComponent e f z 1 *
            surfaceFunctionChartDerivativeComponent e h z 0 +
        surfaceMetricInverseGramCoeffInChart g e z 1 1 *
          surfaceFunctionChartDerivativeComponent e f z 1 *
            surfaceFunctionChartDerivativeComponent e h z 1 := by
  simp [surfaceMetricCoordinateGradientPairingInChart, Fin.sum_univ_two]
  ring

/--
%%handwave
name:
  Metric gradient flux in a chart
statement:
  The coordinate flux vector for a function is
  \(\rho g^{ij}\partial_j f\), where \(\rho\) is the Riemannian volume
  density and \(g^{ij}\) are the inverse metric coefficients.
-/
noncomputable def surfaceMetricGradientFluxInChart {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (f : X → ℝ) (z : ℂ) (i : Fin 2) : ℝ :=
  let ρ := surfaceMetricVolumeDensityInChart g e z
  ρ * ∑ j : Fin 2,
    surfaceMetricInverseGramCoeffInChart g e z i j *
      surfaceFunctionChartDerivativeComponent e f z j

theorem surfaceMetricGradientFluxInChart_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (f : X → ℝ) (z : ℂ) :
    surfaceMetricGradientFluxInChart g e f z 0 =
      surfaceMetricVolumeDensityInChart g e z *
        (surfaceMetricInverseGramCoeffInChart g e z 0 0 *
            surfaceFunctionChartDerivativeComponent e f z 0 +
          surfaceMetricInverseGramCoeffInChart g e z 0 1 *
            surfaceFunctionChartDerivativeComponent e f z 1) := by
  simp [surfaceMetricGradientFluxInChart, Fin.sum_univ_two]

theorem surfaceMetricGradientFluxInChart_one
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (f : X → ℝ) (z : ℂ) :
    surfaceMetricGradientFluxInChart g e f z 1 =
      surfaceMetricVolumeDensityInChart g e z *
        (surfaceMetricInverseGramCoeffInChart g e z 1 0 *
            surfaceFunctionChartDerivativeComponent e f z 0 +
          surfaceMetricInverseGramCoeffInChart g e z 1 1 *
            surfaceFunctionChartDerivativeComponent e f z 1) := by
  simp [surfaceMetricGradientFluxInChart, Fin.sum_univ_two]

/--
%%handwave
name:
  Euclidean coordinate divergence
statement:
  The Euclidean divergence of a two-component coordinate vector field is
  \(\partial_1 F^1+\partial_2 F^2\), with the complex plane regarded as the
  real plane with coordinate directions \(1\) and \(i\).
-/
noncomputable def surfaceCoordinateDivergence
    (F : ℂ → Fin 2 → ℝ) (z : ℂ) : ℝ :=
  ∑ i : Fin 2, fderiv ℝ (fun w : ℂ ↦ F w i) z (complexCoordinateVector i)

theorem surfaceCoordinateDivergence_eq_two_terms
    (F : ℂ → Fin 2 → ℝ) (z : ℂ) :
    surfaceCoordinateDivergence F z =
      fderiv ℝ (fun w : ℂ ↦ F w 0) z (1 : ℂ) +
        fderiv ℝ (fun w : ℂ ↦ F w 1) z Complex.I := by
  simp [surfaceCoordinateDivergence, Fin.sum_univ_two]

/--
%%handwave
name:
  Coordinate vector from two real components
statement:
  A pair of real coordinate components determines the corresponding vector in
  the complex plane regarded as a real two-dimensional vector space.
-/
noncomputable def complexVectorFromComponents (a : Fin 2 → ℝ) : ℂ :=
  (a 0 : ℝ) • (1 : ℂ) + (a 1 : ℝ) • Complex.I

/--
%%handwave
name:
  Coordinate component of a complex vector
statement:
  The two real coordinate components of a complex vector are its real and
  imaginary parts.
-/
def complexVectorComponent (v : ℂ) : Fin 2 → ℝ
  | 0 => v.re
  | 1 => v.im

@[simp]
theorem complexVectorComponent_fromComponents
    (a : Fin 2 → ℝ) :
    complexVectorComponent (complexVectorFromComponents a) = a := by
  funext i
  fin_cases i <;> simp [complexVectorComponent, complexVectorFromComponents]

@[simp]
theorem complexVectorFromComponents_component
    (v : ℂ) :
    complexVectorFromComponents (complexVectorComponent v) = v := by
  simp [complexVectorComponent, complexVectorFromComponents]

/--
%%handwave
name:
  Vector-density pullback relation
statement:
  A coordinate vector density \(F\) is the pullback of \(F'\) by a coordinate
  change \(T\) when
  \[
    F(z)=|\det dT_z|\,(dT_z)^{-1}F'(Tz).
  \]
  The components are read in the real coordinate frame \(1,i\).
-/
def IsVectorDensityPullbackBy
    (T : ℂ → ℂ) (Ω : Set ℂ)
    (F F' : ℂ → Fin 2 → ℝ) : Prop :=
  ∀ z ∈ Ω,
    let J : ℂ →L[ℝ] ℂ := fderivWithin ℝ T Ω z
    J.IsInvertible ∧
      complexVectorFromComponents (F z) =
        (|J.det| : ℝ) • J.inverse (complexVectorFromComponents (F' (T z)))

/--
%%handwave
name:
  Canonical coordinate vector-density pullback
statement:
  The canonical pullback of a coordinate vector density \(F'\) by a coordinate
  change \(T\) has components
  \[
    |\det dT_z|\,(dT_z)^{-1}F'(Tz).
  \]
-/
noncomputable def coordinateVectorDensityPullback
    (T : ℂ → ℂ) (Ω : Set ℂ)
    (F' : ℂ → Fin 2 → ℝ) (z : ℂ) : Fin 2 → ℝ :=
  let J : ℂ →L[ℝ] ℂ := fderivWithin ℝ T Ω z
  complexVectorComponent
    ((|J.det| : ℝ) • J.inverse (complexVectorFromComponents (F' (T z))))

/--
%%handwave
name:
  Local coordinate vector-density pullback
statement:
  The local form of the coordinate vector-density pullback uses the ordinary
  derivative:
  \[
    |\det dT_z|\,(dT_z)^{-1}F'(Tz).
  \]
-/
noncomputable def coordinateVectorDensityPullbackAt
    (T : ℂ → ℂ) (F' : ℂ → Fin 2 → ℝ) (z : ℂ) : Fin 2 → ℝ :=
  let J : ℂ →L[ℝ] ℂ := fderiv ℝ T z
  complexVectorComponent
    ((|J.det| : ℝ) • J.inverse (complexVectorFromComponents (F' (T z))))

/--
%%handwave
name:
  Local Jacobian orientation sign
statement:
  At a point where the derivative of a coordinate change is invertible, its
  Jacobian determinant has a sign.  This sign is \(+1\) at orientation
  preserving points and \(-1\) at orientation reversing points.
-/
noncomputable def coordinateJacobianSignAt
    (T : ℂ → ℂ) (z : ℂ) : ℝ :=
  if 0 < (fderiv ℝ T z).det then 1 else -1

private theorem coordinateComplexDet_ne_zero_of_isInvertible
    (A : ℂ →L[ℝ] ℂ) (hA : A.IsInvertible) : A.det ≠ 0 := by
  rcases hA with ⟨e, rfl⟩
  change LinearMap.det (e : ℂ →ₗ[ℝ] ℂ) ≠ 0
  exact (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero

/--
%%handwave
name:
  Orientation sign recovers the absolute Jacobian
statement:
  If the coordinate derivative at a point is invertible, then multiplying its
  Jacobian determinant by the local orientation sign gives the absolute
  Jacobian.
proof:
  If the determinant is positive this is \(\det dT=|\det dT|\).  If it is
  negative this is \(-\det dT=|\det dT|\).
-/
theorem coordinateJacobianSignAt_mul_det_eq_abs
    {T : ℂ → ℂ} {z : ℂ}
    (hdet : (fderiv ℝ T z).det ≠ 0) :
    coordinateJacobianSignAt T z * (fderiv ℝ T z).det =
      |(fderiv ℝ T z).det| := by
  unfold coordinateJacobianSignAt
  by_cases hpos : 0 < (fderiv ℝ T z).det
  · simp [hpos, abs_of_pos hpos]
  · have hle : (fderiv ℝ T z).det ≤ 0 := le_of_not_gt hpos
    have hneg : (fderiv ℝ T z).det < 0 := lt_of_le_of_ne hle hdet
    simp [hpos, abs_of_neg hneg]

/--
%%handwave
name:
  Absolute Jacobian has locally constant sign
statement:
  Near an invertible smooth point of a coordinate change, the absolute
  Jacobian is the fixed orientation sign at that point times the ordinary
  Jacobian.
proof:
  The derivative, hence its determinant, is continuous.  Since the determinant
  is nonzero at the base point, it remains positive or negative on a small
  neighborhood according to its value at the base point.
-/
theorem eventually_abs_jacobianDet_eq_coordinateJacobianSignAt_mul
    {T : ℂ → ℂ} {z : ℂ}
    (hT : ContDiffAt ℝ ∞ T z)
    (hdet : (fderiv ℝ T z).det ≠ 0) :
    ∀ᶠ w in 𝓝 z,
      |(fderiv ℝ T w).det| =
        coordinateJacobianSignAt T z * (fderiv ℝ T w).det := by
  have hdet_cont :
      ContinuousAt (fun w : ℂ ↦ (fderiv ℝ T w).det) z :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      (hT.continuousAt_fderiv (by simp))
  unfold coordinateJacobianSignAt
  by_cases hpos : 0 < (fderiv ℝ T z).det
  · have hpos_event :
        ∀ᶠ w in 𝓝 z, 0 < (fderiv ℝ T w).det :=
      hdet_cont.eventually (Ioi_mem_nhds hpos)
    filter_upwards [hpos_event] with w hw
    simp [hpos, abs_of_pos hw]
  · have hle : (fderiv ℝ T z).det ≤ 0 := le_of_not_gt hpos
    have hneg : (fderiv ℝ T z).det < 0 := lt_of_le_of_ne hle hdet
    have hneg_event :
        ∀ᶠ w in 𝓝 z, (fderiv ℝ T w).det < 0 :=
      hdet_cont.eventually (Iio_mem_nhds hneg)
    filter_upwards [hneg_event] with w hw
    simp [hpos, abs_of_neg hw]

/--
%%handwave
name:
  Signed local coordinate vector-density pullback
statement:
  Once the orientation sign has been fixed locally, the vector-density
  pullback can be written without an absolute value as
  \[
    \sigma\,\det dT_z\,(dT_z)^{-1}F'(Tz).
  \]
-/
noncomputable def coordinateVectorDensitySignedPullbackAt
    (σ : ℝ) (T : ℂ → ℂ) (F' : ℂ → Fin 2 → ℝ) (z : ℂ) :
    Fin 2 → ℝ :=
  let J : ℂ →L[ℝ] ℂ := fderiv ℝ T z
  complexVectorComponent
    ((σ * J.det : ℝ) • J.inverse (complexVectorFromComponents (F' (T z))))

/--
%%handwave
name:
  Local pullback agrees with the signed pullback near a fixed sign point
statement:
  If the absolute Jacobian agrees near a point with a fixed sign times the
  Jacobian, then the absolute-value vector-density pullback agrees near that
  point with the corresponding signed pullback.
proof:
  This is just substitution in the defining formula for the pullback.
-/
theorem coordinateVectorDensityPullbackAt_eventuallyEq_signed
    {σ : ℝ} {T : ℂ → ℂ} {F' : ℂ → Fin 2 → ℝ} {z : ℂ}
    (hdet :
      ∀ᶠ w in 𝓝 z,
        |(fderiv ℝ T w).det| = σ * (fderiv ℝ T w).det) :
    coordinateVectorDensityPullbackAt T F' =ᶠ[𝓝 z]
      coordinateVectorDensitySignedPullbackAt σ T F' := by
  filter_upwards [hdet] with w hw
  funext i
  simp [coordinateVectorDensityPullbackAt,
    coordinateVectorDensitySignedPullbackAt, hw]

/--
%%handwave
name:
  Cofactor action on coordinate vector densities
statement:
  For a real-linear map \(J:\mathbb C\to\mathbb C\), written in the coordinate
  frame \(1,i\) as
  \[
    J=\begin{pmatrix} a&b\\ c&d\end{pmatrix},
  \]
  the cofactor action on a vector density \((P,Q)\) is
  \[
    (dP-bQ,\,-cP+aQ).
  \]
-/
noncomputable def complexVectorDensityCofactorAction
    (J : ℂ →L[ℝ] ℂ) (V : Fin 2 → ℝ) : ℂ :=
  complexVectorFromComponents
    (fun
      | 0 => (J Complex.I).im * V 0 - (J Complex.I).re * V 1
      | 1 => - (J (1 : ℂ)).im * V 0 + (J (1 : ℂ)).re * V 1)

/--
%%handwave
name:
  Coordinate Jacobian entries
statement:
  The coordinate entry \(J_{ij}\) of the derivative \(dT_z\) is the \(i\)-th
  coordinate component of \(dT_z(e_j)\), where \(e_0=1\) and \(e_1=i\).
-/
noncomputable def coordinateJacobianEntry
    (T : ℂ → ℂ) (z : ℂ) (i j : Fin 2) : ℝ :=
  complexVectorComponent
    ((fderiv ℝ T z) (complexCoordinateVector j)) i

/--
%%handwave
name:
  Generic signed cofactor scalar field
statement:
  Given scalar functions \(a,b,c,d,P,Q\), the signed cofactor field is
  \[
    \bigl(\sigma(dP-bQ),\sigma(-cP+aQ)\bigr).
  \]
-/
noncomputable def signedCofactorScalarField
    (σ : ℝ) (a b c d P Q : ℂ → ℝ) (z : ℂ) : Fin 2 → ℝ
  | 0 => σ * (d z * P z - b z * Q z)
  | 1 => σ * (-(c z * P z) + a z * Q z)

private theorem coordinateComplex_det_eq_components
    (J : ℂ →L[ℝ] ℂ) :
    J.det =
      (J (1 : ℂ)).re * (J Complex.I).im -
        (J Complex.I).re * (J (1 : ℂ)).im := by
  let a := (J (1 : ℂ)).re
  let c := (J (1 : ℂ)).im
  let b := (J Complex.I).re
  let d := (J Complex.I).im
  change LinearMap.det (J : ℂ →ₗ[ℝ] ℂ) = a * d - b * c
  calc
    LinearMap.det (J : ℂ →ₗ[ℝ] ℂ)
        = Matrix.det (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
            (J : ℂ →ₗ[ℝ] ℂ)) :=
      (LinearMap.det_toMatrix Complex.basisOneI (J : ℂ →ₗ[ℝ] ℂ)).symm
    _ = a * d - b * c := by
      rw [Matrix.det_fin_two]
      simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
        a, b, c, d]

/--
%%handwave
name:
  Cofactor formula for the signed inverse pullback
statement:
  If \(J\) is invertible, then
  \[
    \sigma\det(J)J^{-1}(P,Q)=
      \sigma(dP-bQ,\,-cP+aQ).
  \]
proof:
  Apply \(J\) to both sides.  The left side becomes
  \(\sigma\det(J)(P,Q)\), while the right side becomes the same vector by the
  elementary \(2\times2\) determinant calculation.  Since \(J\) is injective,
  the two sides are equal.
-/
theorem complexVectorDensity_signedInverse_eq_signedCofactorAction
    (σ : ℝ) (J : ℂ →L[ℝ] ℂ) (V : Fin 2 → ℝ)
    (hJ : J.IsInvertible) :
    complexVectorComponent
        ((σ * J.det : ℝ) • J.inverse (complexVectorFromComponents V)) =
      complexVectorComponent
        (σ • complexVectorDensityCofactorAction J V) := by
  let cof : ℂ := complexVectorDensityCofactorAction J V
  have hdet :
      J.det =
        (J (1 : ℂ)).re * (J Complex.I).im -
          (J Complex.I).re * (J (1 : ℂ)).im :=
    coordinateComplex_det_eq_components J
  have hcof_expand :
      J cof =
        (((J Complex.I).im * V 0 - (J Complex.I).re * V 1) : ℝ) •
            J (1 : ℂ) +
          ((- (J (1 : ℂ)).im * V 0 + (J (1 : ℂ)).re * V 1) : ℝ) •
            J Complex.I := by
    let x : ℝ := (J Complex.I).im * V 0 - (J Complex.I).re * V 1
    let y : ℝ := - (J (1 : ℂ)).im * V 0 + (J (1 : ℂ)).re * V 1
    have hcof_def : cof = (x : ℝ) • (1 : ℂ) + (y : ℝ) • Complex.I := by
      simp [cof, complexVectorDensityCofactorAction,
        complexVectorFromComponents, x, y]
    calc
      J cof = J ((x : ℝ) • (1 : ℂ) + (y : ℝ) • Complex.I) := by
        rw [hcof_def]
      _ = (x : ℝ) • J (1 : ℂ) + (y : ℝ) • J Complex.I := by
        rw [map_add, map_smul, map_smul]
      _ = (((J Complex.I).im * V 0 - (J Complex.I).re * V 1) : ℝ) •
            J (1 : ℂ) +
          ((- (J (1 : ℂ)).im * V 0 + (J (1 : ℂ)).re * V 1) : ℝ) •
            J Complex.I := by
        simp [x, y]
  have hcof :
      J cof = J.det • complexVectorFromComponents V := by
    apply Complex.ext
    · rw [hcof_expand]
      simp [complexVectorFromComponents, hdet]
      ring
    · rw [hcof_expand]
      simp [complexVectorFromComponents, hdet]
      ring
  have hbase :
      (J.det : ℝ) • J.inverse (complexVectorFromComponents V) = cof := by
    apply hJ.injective
    calc
      J ((J.det : ℝ) • J.inverse (complexVectorFromComponents V)) =
          J.det • J (J.inverse (complexVectorFromComponents V)) := by
        rw [map_smul]
      _ = J.det • complexVectorFromComponents V := by
        rw [hJ.self_apply_inverse]
      _ = J cof := hcof.symm
  have hvec :
      ((σ * J.det : ℝ) • J.inverse (complexVectorFromComponents V)) =
        σ • cof := by
    calc
      ((σ * J.det : ℝ) • J.inverse (complexVectorFromComponents V)) =
          σ • ((J.det : ℝ) • J.inverse (complexVectorFromComponents V)) :=
        (smul_smul σ J.det (J.inverse (complexVectorFromComponents V))).symm
      _ = σ • cof := by
        rw [hbase]
  exact congr_arg complexVectorComponent hvec

/--
%%handwave
name:
  Signed local cofactor vector-density pullback
statement:
  The signed local cofactor form of a vector-density pullback is
  \[
    \sigma(dP-bQ,\,-cP+aQ),
  \]
  where \(a,b,c,d\) are the coordinate entries of \(dT\) and
  \((P,Q)=F'(Tz)\).
-/
noncomputable def coordinateVectorDensitySignedCofactorPullbackAt
    (σ : ℝ) (T : ℂ → ℂ) (F' : ℂ → Fin 2 → ℝ) (z : ℂ) :
    Fin 2 → ℝ :=
  let J : ℂ →L[ℝ] ℂ := fderiv ℝ T z
  complexVectorComponent
    (σ • complexVectorDensityCofactorAction J (F' (T z)))

/--
%%handwave
name:
  Component form of the signed cofactor pullback
statement:
  The signed cofactor pullback written componentwise is
  \[
    \bigl(\sigma(dP-bQ),\sigma(-cP+aQ)\bigr),
  \]
  where \(a,b,c,d\) are the coordinate entries of \(dT\) and
  \(P,Q\) are the components of \(F'\circ T\).
-/
noncomputable def coordinateVectorDensitySignedCofactorComponentsAt
    (σ : ℝ) (T : ℂ → ℂ) (F' : ℂ → Fin 2 → ℝ) (z : ℂ) :
    Fin 2 → ℝ
  | 0 =>
      σ * (coordinateJacobianEntry T z 1 1 * F' (T z) 0 -
        coordinateJacobianEntry T z 0 1 * F' (T z) 1)
  | 1 =>
      σ * (-(coordinateJacobianEntry T z 1 0 * F' (T z) 0) +
        coordinateJacobianEntry T z 0 0 * F' (T z) 1)

/--
%%handwave
name:
  Cofactor pullback equals its component formula
statement:
  The complex-vector definition of the signed cofactor pullback agrees
  identically with its component formula.
proof:
  Expand the coordinate frame \(1,i\) and read off real and imaginary parts.
-/
theorem coordinateVectorDensitySignedCofactorPullbackAt_eq_components
    (σ : ℝ) (T : ℂ → ℂ) (F' : ℂ → Fin 2 → ℝ) :
    coordinateVectorDensitySignedCofactorPullbackAt σ T F' =
      coordinateVectorDensitySignedCofactorComponentsAt σ T F' := by
  funext z i
  fin_cases i <;>
    simp [coordinateVectorDensitySignedCofactorPullbackAt,
      coordinateVectorDensitySignedCofactorComponentsAt,
      coordinateJacobianEntry, complexVectorDensityCofactorAction,
      complexVectorFromComponents, complexVectorComponent,
      complexCoordinateVector]

/--
%%handwave
name:
  Component cofactor pullback is the generic scalar field
statement:
  The componentwise cofactor pullback is the generic scalar cofactor field
  obtained by taking \(a,b,c,d\) to be the entries of \(dT\) and
  \(P,Q\) to be the components of \(F'\circ T\).
proof:
  This is just expansion of the definitions.
-/
theorem coordinateVectorDensitySignedCofactorComponentsAt_eq_scalarField
    (σ : ℝ) (T : ℂ → ℂ) (F' : ℂ → Fin 2 → ℝ) :
    coordinateVectorDensitySignedCofactorComponentsAt σ T F' =
      signedCofactorScalarField σ
        (fun w ↦ coordinateJacobianEntry T w 0 0)
        (fun w ↦ coordinateJacobianEntry T w 0 1)
        (fun w ↦ coordinateJacobianEntry T w 1 0)
        (fun w ↦ coordinateJacobianEntry T w 1 1)
        (fun w ↦ F' (T w) 0)
        (fun w ↦ F' (T w) 1) := by
  funext z i
  fin_cases i <;>
    simp [coordinateVectorDensitySignedCofactorComponentsAt,
      signedCofactorScalarField]

/--
%%handwave
name:
  Signed inverse pullback equals the signed cofactor pullback near an invertible point
statement:
  Near a point where the derivative of \(T\) is invertible, the signed
  inverse formula for the vector-density pullback agrees with the signed
  cofactor formula.
proof:
  This is the pointwise cofactor formula for
  \(\det(dT)(dT)^{-1}\), applied throughout the neighborhood where \(dT\) is
  invertible.
-/
theorem coordinateVectorDensitySignedPullbackAt_eventuallyEq_signedCofactor
    {σ : ℝ} {T : ℂ → ℂ} {F' : ℂ → Fin 2 → ℝ} {z : ℂ}
    (hinv : ∀ᶠ w in 𝓝 z, (fderiv ℝ T w).IsInvertible) :
    coordinateVectorDensitySignedPullbackAt σ T F' =ᶠ[𝓝 z]
      coordinateVectorDensitySignedCofactorPullbackAt σ T F' := by
  filter_upwards [hinv] with w hw
  simpa [coordinateVectorDensitySignedPullbackAt,
    coordinateVectorDensitySignedCofactorPullbackAt] using
      complexVectorDensity_signedInverse_eq_signedCofactorAction
        σ (fderiv ℝ T w) (F' (T w)) hw

/--
%%handwave
name:
  Open-set pullbacks agree with local pullbacks
statement:
  On an open set, the pullback written with the derivative within the set
  agrees near every point with the purely local pullback written with the
  ordinary derivative.
proof:
  The derivative within an open set equals the ordinary derivative at every
  point of the set.
-/
theorem coordinateVectorDensityPullback_eventuallyEq_at
    {T : ℂ → ℂ} {Ω : Set ℂ} {F' : ℂ → Fin 2 → ℝ}
    (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω) :
    coordinateVectorDensityPullback T Ω F' =ᶠ[𝓝 z]
      coordinateVectorDensityPullbackAt T F' := by
  filter_upwards [hΩ.mem_nhds hz] with y hy
  funext i
  rw [coordinateVectorDensityPullback, coordinateVectorDensityPullbackAt,
    fderivWithin_of_isOpen hΩ hy]

/--
%%handwave
name:
  Vector-density pullback gives local equality with the canonical pullback
statement:
  If \(F\) is the pullback of \(F'\) by \(T\) on an open set, then near every
  point of that open set \(F\) agrees with the canonical coordinate
  vector-density pullback.
proof:
  The pullback relation is pointwise on the open set.  Since the open set is a
  neighborhood of each of its points, the pointwise equality is an eventual
  equality there.
-/
theorem IsVectorDensityPullbackBy.eventuallyEq_coordinateVectorDensityPullback
    {T : ℂ → ℂ} {Ω : Set ℂ} {F F' : ℂ → Fin 2 → ℝ}
    (hpull : IsVectorDensityPullbackBy T Ω F F')
    (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω) :
    F =ᶠ[𝓝 z] coordinateVectorDensityPullback T Ω F' := by
  filter_upwards [hΩ.mem_nhds hz] with y hy
  funext i
  have hvec :=
    (hpull y hy).2
  have hcomp := congr_fun (congr_arg complexVectorComponent hvec) i
  simpa [coordinateVectorDensityPullback] using hcomp

/--
%%handwave
name:
  Coordinate divergence respects local equality
statement:
  If two coordinate vector fields agree near a point, then their Euclidean
  coordinate divergences at that point agree.
proof:
  The derivative of each component only depends on the germ of that component
  at the point.
-/
theorem surfaceCoordinateDivergence_congr_eventuallyEq
    {F G : ℂ → Fin 2 → ℝ} {z : ℂ}
    (hFG : F =ᶠ[𝓝 z] G) :
    surfaceCoordinateDivergence F z =
      surfaceCoordinateDivergence G z := by
  unfold surfaceCoordinateDivergence
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hcomp :
      (fun w : ℂ ↦ F w i) =ᶠ[𝓝 z] (fun w : ℂ ↦ G w i) :=
    hFG.mono fun w hw ↦ by simpa using congr_fun hw i
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hcomp]

/--
%%handwave
name:
  Derivative of the first scalar cofactor component
statement:
  The directional derivative of \(\sigma(dP-bQ)\) is given by the ordinary
  product rule.
proof:
  This is the product rule and the constant-multiple rule for Fréchet
  derivatives.
-/
theorem signedCofactorScalarField_fderiv_zero
    {σ : ℝ} {a b c d P Q : ℂ → ℝ} {z v : ℂ}
    (hd : DifferentiableAt ℝ d z) (hP : DifferentiableAt ℝ P z)
    (hb : DifferentiableAt ℝ b z) (hQ : DifferentiableAt ℝ Q z) :
    fderiv ℝ (fun w ↦ signedCofactorScalarField σ a b c d P Q w 0) z v =
      σ * ((fderiv ℝ d z v * P z + d z * fderiv ℝ P z v) -
        (fderiv ℝ b z v * Q z + b z * fderiv ℝ Q z v)) := by
  have hdP : DifferentiableAt ℝ (fun w : ℂ ↦ d w * P w) z := hd.mul hP
  have hbQ : DifferentiableAt ℝ (fun w : ℂ ↦ b w * Q w) z := hb.mul hQ
  change fderiv ℝ (fun w : ℂ ↦ σ * (d w * P w - b w * Q w)) z v = _
  have hconst :
      fderiv ℝ (fun w : ℂ ↦ σ * (d w * P w - b w * Q w)) z =
        σ • fderiv ℝ (fun w : ℂ ↦ d w * P w - b w * Q w) z := by
    simpa [Pi.sub_apply] using fderiv_const_mul (hdP.sub hbQ) σ
  rw [hconst]
  rw [ContinuousLinearMap.smul_apply]
  have hsub :
      fderiv ℝ (fun w : ℂ ↦ d w * P w - b w * Q w) z =
        fderiv ℝ (fun w : ℂ ↦ d w * P w) z -
          fderiv ℝ (fun w : ℂ ↦ b w * Q w) z := by
    simpa [Pi.sub_apply] using fderiv_fun_sub hdP hbQ
  rw [hsub]
  rw [ContinuousLinearMap.sub_apply]
  rw [fderiv_fun_mul hd hP, fderiv_fun_mul hb hQ]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

/--
%%handwave
name:
  Derivative of the second scalar cofactor component
statement:
  The directional derivative of \(\sigma(-cP+aQ)\) is given by the ordinary
  product rule.
proof:
  This is the product rule and the constant-multiple rule for Fréchet
  derivatives.
-/
theorem signedCofactorScalarField_fderiv_one
    {σ : ℝ} {a b c d P Q : ℂ → ℝ} {z v : ℂ}
    (hc : DifferentiableAt ℝ c z) (hP : DifferentiableAt ℝ P z)
    (ha : DifferentiableAt ℝ a z) (hQ : DifferentiableAt ℝ Q z) :
    fderiv ℝ (fun w ↦ signedCofactorScalarField σ a b c d P Q w 1) z v =
      σ * (-(fderiv ℝ c z v * P z + c z * fderiv ℝ P z v) +
        (fderiv ℝ a z v * Q z + a z * fderiv ℝ Q z v)) := by
  let R : ℂ → ℝ := fun w ↦ c w * P w
  let S : ℂ → ℝ := fun w ↦ a w * Q w
  have hR : DifferentiableAt ℝ R z := hc.mul hP
  have hS : DifferentiableAt ℝ S z := ha.mul hQ
  change fderiv ℝ (fun w : ℂ ↦ σ * ((-R) w + S w)) z v = _
  have hconst :
      fderiv ℝ (fun w : ℂ ↦ σ * ((-R) w + S w)) z =
        σ • fderiv ℝ (fun w : ℂ ↦ (-R) w + S w) z := by
    simpa [Pi.add_apply] using fderiv_const_mul (hR.neg.add hS) σ
  rw [hconst]
  rw [ContinuousLinearMap.smul_apply]
  rw [fderiv_fun_add hR.neg hS]
  rw [ContinuousLinearMap.add_apply]
  rw [fderiv_neg]
  rw [ContinuousLinearMap.neg_apply]
  dsimp only [R, S]
  rw [fderiv_fun_mul hc hP, fderiv_fun_mul ha hQ]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

/--
%%handwave
name:
  Scalar cofactor divergence from derivative identities
statement:
  Suppose \(P,Q\) satisfy the chain-rule identities expected for
  \(F'\circ T\), and \(a,b,c,d\) satisfy the mixed-partial identities expected
  for the entries of \(dT\).  Then the divergence of
  \((\sigma(dP-bQ),\sigma(-cP+aQ))\) is
  \(\sigma(ad-bc)(P_x+Q_y)\).
proof:
  Substitute the product-rule expansions, the chain-rule identities, and the
  mixed-partial identities.  The remaining statement is polynomial algebra.
-/
theorem surfaceCoordinateDivergence_signedCofactorScalarField_of_derivative_identities
    {σ : ℝ} {a b c d P Q : ℂ → ℝ} {z : ℂ}
    {Px Py Qx Qy : ℝ}
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z)
    (hc : DifferentiableAt ℝ c z) (hd : DifferentiableAt ℝ d z)
    (hP : DifferentiableAt ℝ P z) (hQ : DifferentiableAt ℝ Q z)
    (hP₁ : fderiv ℝ P z (1 : ℂ) = a z * Px + c z * Py)
    (hPI : fderiv ℝ P z Complex.I = b z * Px + d z * Py)
    (hQ₁ : fderiv ℝ Q z (1 : ℂ) = a z * Qx + c z * Qy)
    (hQI : fderiv ℝ Q z Complex.I = b z * Qx + d z * Qy)
    (hmix₁ : fderiv ℝ d z (1 : ℂ) = fderiv ℝ c z Complex.I)
    (hmix₀ : fderiv ℝ b z (1 : ℂ) = fderiv ℝ a z Complex.I) :
    surfaceCoordinateDivergence (signedCofactorScalarField σ a b c d P Q) z =
      σ * (a z * d z - b z * c z) * (Px + Qy) := by
  rw [surfaceCoordinateDivergence_eq_two_terms]
  rw [signedCofactorScalarField_fderiv_zero hd hP hb hQ]
  rw [signedCofactorScalarField_fderiv_one hc hP ha hQ]
  rw [hP₁, hPI, hQ₁, hQI, hmix₁, hmix₀]
  ring

/--
%%handwave
name:
  Coordinate Jacobian entries are differentiable
statement:
  If \(T\) is smooth at \(z\), then each coordinate entry of \(dT\) is
  differentiable at \(z\).
proof:
  The derivative \(dT\) depends smoothly on the base point, and evaluation on
  a fixed coordinate vector followed by a coordinate projection is smooth.
-/
theorem coordinateJacobianEntry_differentiableAt
    {T : ℂ → ℂ} {z : ℂ} (hT : ContDiffAt ℝ ∞ T z)
  (i j : Fin 2) :
    DifferentiableAt ℝ (fun w : ℂ ↦ coordinateJacobianEntry T w i j) z := by
  have hF : DifferentiableAt ℝ (fderiv ℝ T) z :=
    (hT.fderiv_right (m := 1) (by
      exact WithTop.coe_le_coe.2 le_top)).differentiableAt (by norm_num)
  have hEval :
      DifferentiableAt ℝ
        (fun w : ℂ ↦ fderiv ℝ T w (complexCoordinateVector j)) z :=
    hF.clm_apply (differentiableAt_const (complexCoordinateVector j))
  fin_cases i
  · simpa [coordinateJacobianEntry, complexVectorComponent] using
      ((Complex.reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp z
        hEval.hasFDerivAt).differentiableAt
  · simpa [coordinateJacobianEntry, complexVectorComponent] using
      ((Complex.imCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp z
        hEval.hasFDerivAt).differentiableAt

/--
%%handwave
name:
  Pullbacks of smooth coordinate components are differentiable
statement:
  If \(T\) is smooth at \(z\) and a component of \(F'\) is smooth at \(Tz\),
  then that component pulled back by \(T\) is differentiable at \(z\).
proof:
  This is differentiability of a composition of smooth functions.
-/
theorem pulledBackCoordinateComponent_differentiableAt
    {T : ℂ → ℂ} {F' : ℂ → Fin 2 → ℝ} {z : ℂ}
    (hT : ContDiffAt ℝ ∞ T z)
    (i : Fin 2)
    (hF' : ContDiffAt ℝ ∞ (fun w : ℂ ↦ F' w i) (T z)) :
    DifferentiableAt ℝ (fun w : ℂ ↦ F' (T w) i) z := by
  simpa [Function.comp_def] using
    (hF'.differentiableAt (by simp)).comp z
      (hT.differentiableAt (by simp))

private theorem realLinearMap_apply_complex_eq_components
    (L : ℂ →L[ℝ] ℝ) (v : ℂ) :
    L v = v.re * L (1 : ℂ) + v.im * L Complex.I := by
  have hv :
      ((v.re : ℝ) • (1 : ℂ)) + ((v.im : ℝ) • Complex.I) = v := by
    simp [Complex.re_add_im]
  calc
    L v =
        L (((v.re : ℝ) • (1 : ℂ)) + ((v.im : ℝ) • Complex.I)) := by
      exact congr_arg L hv.symm
    _ = v.re * L (1 : ℂ) + v.im * L Complex.I := by
      rw [map_add, map_smul, map_smul]
      simp [smul_eq_mul]

/--
%%handwave
name:
  Chain rule for pulled-back coordinate components along \(1\)
statement:
  The derivative of the \(i\)-th component of \(F'\circ T\) in the \(1\)
  direction is the dot product of \(dF'_i\) with the first column of \(dT\).
proof:
  Apply the Fréchet chain rule and decompose \(dT_z(1)\) in the coordinate
  basis \(1,i\).
-/
theorem pulledBackCoordinateComponent_fderiv_one
    {T : ℂ → ℂ} {F' : ℂ → Fin 2 → ℝ} {z : ℂ}
    (hT : ContDiffAt ℝ ∞ T z)
    (i : Fin 2)
    (hF' : ContDiffAt ℝ ∞ (fun w : ℂ ↦ F' w i) (T z)) :
    fderiv ℝ (fun w : ℂ ↦ F' (T w) i) z (1 : ℂ) =
      coordinateJacobianEntry T z 0 0 *
          fderiv ℝ (fun w : ℂ ↦ F' w i) (T z) (1 : ℂ) +
        coordinateJacobianEntry T z 1 0 *
          fderiv ℝ (fun w : ℂ ↦ F' w i) (T z) Complex.I := by
  let L : ℂ →L[ℝ] ℝ := fderiv ℝ (fun w : ℂ ↦ F' w i) (T z)
  have hchain :
      fderiv ℝ (fun w : ℂ ↦ F' (T w) i) z =
        L.comp (fderiv ℝ T z) := by
    simpa [L, Function.comp_def] using
      fderiv_comp z (hF'.differentiableAt (by simp))
        (hT.differentiableAt (by simp))
  rw [hchain, ContinuousLinearMap.comp_apply]
  simpa [L, coordinateJacobianEntry, complexVectorComponent,
    complexCoordinateVector] using
      realLinearMap_apply_complex_eq_components L
        ((fderiv ℝ T z) (1 : ℂ))

/--
%%handwave
name:
  Chain rule for pulled-back coordinate components along \(i\)
statement:
  The derivative of the \(i\)-th component of \(F'\circ T\) in the \(i\)
  direction is the dot product of \(dF'_i\) with the second column of \(dT\).
proof:
  Apply the Fréchet chain rule and decompose \(dT_z(i)\) in the coordinate
  basis \(1,i\).
-/
theorem pulledBackCoordinateComponent_fderiv_I
    {T : ℂ → ℂ} {F' : ℂ → Fin 2 → ℝ} {z : ℂ}
    (hT : ContDiffAt ℝ ∞ T z)
    (i : Fin 2)
    (hF' : ContDiffAt ℝ ∞ (fun w : ℂ ↦ F' w i) (T z)) :
    fderiv ℝ (fun w : ℂ ↦ F' (T w) i) z Complex.I =
      coordinateJacobianEntry T z 0 1 *
          fderiv ℝ (fun w : ℂ ↦ F' w i) (T z) (1 : ℂ) +
        coordinateJacobianEntry T z 1 1 *
          fderiv ℝ (fun w : ℂ ↦ F' w i) (T z) Complex.I := by
  let L : ℂ →L[ℝ] ℝ := fderiv ℝ (fun w : ℂ ↦ F' w i) (T z)
  have hchain :
      fderiv ℝ (fun w : ℂ ↦ F' (T w) i) z =
        L.comp (fderiv ℝ T z) := by
    simpa [L, Function.comp_def] using
      fderiv_comp z (hF'.differentiableAt (by simp))
        (hT.differentiableAt (by simp))
  rw [hchain, ContinuousLinearMap.comp_apply]
  simpa [L, coordinateJacobianEntry, complexVectorComponent,
    complexCoordinateVector] using
      realLinearMap_apply_complex_eq_components L
        ((fderiv ℝ T z) Complex.I)

private theorem coordinateJacobianEntry_fderiv
    {T : ℂ → ℂ} {z v : ℂ} (hT : ContDiffAt ℝ ∞ T z)
    (i j : Fin 2) :
    fderiv ℝ (fun w : ℂ ↦ coordinateJacobianEntry T w i j) z v =
      complexVectorComponent
        ((fderiv ℝ (fderiv ℝ T) z) v (complexCoordinateVector j)) i := by
  have hF : DifferentiableAt ℝ (fderiv ℝ T) z :=
    (hT.fderiv_right (m := 1) (by
      exact WithTop.coe_le_coe.2 le_top)).differentiableAt (by norm_num)
  let e : ℂ := complexCoordinateVector j
  have hEval :
      DifferentiableAt ℝ (fun w : ℂ ↦ fderiv ℝ T w e) z :=
    hF.clm_apply (differentiableAt_const e)
  have hEval_fderiv :
      fderiv ℝ (fun w : ℂ ↦ fderiv ℝ T w e) z =
        (fderiv ℝ (fderiv ℝ T) z).flip e := by
    rw [fderiv_clm_apply hF (differentiableAt_const e)]
    ext u
    simp [ContinuousLinearMap.flip_apply]
  fin_cases i
  · have hProj :
        HasFDerivAt
          (fun w : ℂ ↦ (fderiv ℝ T w e).re)
          ((Complex.reCLM : ℂ →L[ℝ] ℝ).comp
            (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ T w e) z)) z := by
      simpa [Function.comp_def] using
        (Complex.reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp z
          hEval.hasFDerivAt
    calc
      fderiv ℝ (fun w : ℂ ↦ coordinateJacobianEntry T w 0 j) z v =
          fderiv ℝ (fun w : ℂ ↦ (fderiv ℝ T w e).re) z v := by
        simp [coordinateJacobianEntry, complexVectorComponent, e]
      _ = ((Complex.reCLM : ℂ →L[ℝ] ℝ).comp
            (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ T w e) z)) v := by
        rw [hProj.fderiv]
      _ = complexVectorComponent
            ((fderiv ℝ (fderiv ℝ T) z) v (complexCoordinateVector j)) 0 := by
        rw [hEval_fderiv]
        simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, e,
          complexVectorComponent]
  · have hProj :
        HasFDerivAt
          (fun w : ℂ ↦ (fderiv ℝ T w e).im)
          ((Complex.imCLM : ℂ →L[ℝ] ℝ).comp
            (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ T w e) z)) z := by
      simpa [Function.comp_def] using
        (Complex.imCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp z
          hEval.hasFDerivAt
    calc
      fderiv ℝ (fun w : ℂ ↦ coordinateJacobianEntry T w 1 j) z v =
          fderiv ℝ (fun w : ℂ ↦ (fderiv ℝ T w e).im) z v := by
        simp [coordinateJacobianEntry, complexVectorComponent, e]
      _ = ((Complex.imCLM : ℂ →L[ℝ] ℝ).comp
            (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ T w e) z)) v := by
        rw [hProj.fderiv]
      _ = complexVectorComponent
            ((fderiv ℝ (fderiv ℝ T) z) v (complexCoordinateVector j)) 1 := by
        rw [hEval_fderiv]
        simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, e,
          complexVectorComponent]

/--
%%handwave
name:
  Mixed partials for coordinate Jacobian entries
statement:
  For each coordinate component of a smooth map \(T\), differentiating the
  second column of \(dT\) in the \(1\) direction agrees with differentiating
  the first column in the \(i\) direction.
proof:
  This is equality of mixed second partial derivatives for the coordinate
  component of \(T\).
-/
theorem coordinateJacobianEntry_mixed_partial
    {T : ℂ → ℂ} {z : ℂ} (hT : ContDiffAt ℝ ∞ T z)
    (i : Fin 2) :
    fderiv ℝ (fun w : ℂ ↦ coordinateJacobianEntry T w i 1) z (1 : ℂ) =
      fderiv ℝ (fun w : ℂ ↦ coordinateJacobianEntry T w i 0) z Complex.I := by
  rw [coordinateJacobianEntry_fderiv hT i 1]
  rw [coordinateJacobianEntry_fderiv hT i 0]
  have hsymm : IsSymmSndFDerivAt ℝ T z :=
    hT.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField (𝕜 := ℝ)]
      exact WithTop.coe_le_coe.2 le_top)
  simpa [complexCoordinateVector] using
    congr_arg (fun u : ℂ ↦ complexVectorComponent u i)
      (hsymm.eq (1 : ℂ) Complex.I)

/--
%%handwave
name:
  Jacobian determinant in coordinate entries
statement:
  The determinant of \(dT_z\) is \(ad-bc\) in the coordinate frame \(1,i\).
proof:
  This is the usual \(2\times2\) determinant formula in the basis \(1,i\).
-/
theorem coordinateJacobian_det_eq_entries
    (T : ℂ → ℂ) (z : ℂ) :
    (fderiv ℝ T z).det =
      coordinateJacobianEntry T z 0 0 * coordinateJacobianEntry T z 1 1 -
        coordinateJacobianEntry T z 0 1 * coordinateJacobianEntry T z 1 0 := by
  simpa [coordinateJacobianEntry, complexCoordinateVector, complexVectorComponent]
    using coordinateComplex_det_eq_components (fderiv ℝ T z)

/--
%%handwave
name:
  Componentwise cofactor Piola identity
statement:
  For a smooth coordinate change \(T\), the Euclidean divergence of the
  componentwise cofactor expression
  \[
    \bigl(\sigma(dP-bQ),\sigma(-cP+aQ)\bigr)
  \]
  is
  \[
    \sigma\det(dT)\,(\operatorname{div}F')(Tz).
  \]
proof:
  This is the scalar coordinate computation.  Apply the product rule to the
  two components, the chain rule to \(P=F'_0\circ T\) and \(Q=F'_1\circ T\),
  and use equality of mixed partial derivatives for the coordinate functions
  of \(T\).
-/
theorem surfaceCoordinateDivergence_coordinateVectorDensitySignedCofactorComponentsAt
    (σ : ℝ) (T : ℂ → ℂ) (F' : ℂ → Fin 2 → ℝ) (z : ℂ)
    (_hT : ContDiffAt ℝ ∞ T z)
    (_hF' : ∀ i : Fin 2, ContDiffAt ℝ ∞ (fun w : ℂ ↦ F' w i) (T z)) :
    surfaceCoordinateDivergence
        (coordinateVectorDensitySignedCofactorComponentsAt σ T F') z =
      σ * (fderiv ℝ T z).det *
        surfaceCoordinateDivergence F' (T z) := by
  let a : ℂ → ℝ := fun w ↦ coordinateJacobianEntry T w 0 0
  let b : ℂ → ℝ := fun w ↦ coordinateJacobianEntry T w 0 1
  let c : ℂ → ℝ := fun w ↦ coordinateJacobianEntry T w 1 0
  let d : ℂ → ℝ := fun w ↦ coordinateJacobianEntry T w 1 1
  let P : ℂ → ℝ := fun w ↦ F' (T w) 0
  let Q : ℂ → ℝ := fun w ↦ F' (T w) 1
  let Px : ℝ := fderiv ℝ (fun w : ℂ ↦ F' w 0) (T z) (1 : ℂ)
  let Py : ℝ := fderiv ℝ (fun w : ℂ ↦ F' w 0) (T z) Complex.I
  let Qx : ℝ := fderiv ℝ (fun w : ℂ ↦ F' w 1) (T z) (1 : ℂ)
  let Qy : ℝ := fderiv ℝ (fun w : ℂ ↦ F' w 1) (T z) Complex.I
  have ha : DifferentiableAt ℝ a z := by
    simpa [a] using coordinateJacobianEntry_differentiableAt _hT 0 0
  have hb : DifferentiableAt ℝ b z := by
    simpa [b] using coordinateJacobianEntry_differentiableAt _hT 0 1
  have hc : DifferentiableAt ℝ c z := by
    simpa [c] using coordinateJacobianEntry_differentiableAt _hT 1 0
  have hd : DifferentiableAt ℝ d z := by
    simpa [d] using coordinateJacobianEntry_differentiableAt _hT 1 1
  have hP : DifferentiableAt ℝ P z := by
    simpa [P] using
      pulledBackCoordinateComponent_differentiableAt _hT 0 (_hF' 0)
  have hQ : DifferentiableAt ℝ Q z := by
    simpa [Q] using
      pulledBackCoordinateComponent_differentiableAt _hT 1 (_hF' 1)
  have hP₁ : fderiv ℝ P z (1 : ℂ) = a z * Px + c z * Py := by
    simpa [a, c, P, Px, Py] using
      pulledBackCoordinateComponent_fderiv_one _hT 0 (_hF' 0)
  have hPI : fderiv ℝ P z Complex.I = b z * Px + d z * Py := by
    simpa [b, d, P, Px, Py] using
      pulledBackCoordinateComponent_fderiv_I _hT 0 (_hF' 0)
  have hQ₁ : fderiv ℝ Q z (1 : ℂ) = a z * Qx + c z * Qy := by
    simpa [a, c, Q, Qx, Qy] using
      pulledBackCoordinateComponent_fderiv_one _hT 1 (_hF' 1)
  have hQI : fderiv ℝ Q z Complex.I = b z * Qx + d z * Qy := by
    simpa [b, d, Q, Qx, Qy] using
      pulledBackCoordinateComponent_fderiv_I _hT 1 (_hF' 1)
  have hmix₁ : fderiv ℝ d z (1 : ℂ) = fderiv ℝ c z Complex.I := by
    simpa [c, d] using coordinateJacobianEntry_mixed_partial _hT 1
  have hmix₀ : fderiv ℝ b z (1 : ℂ) = fderiv ℝ a z Complex.I := by
    simpa [a, b] using coordinateJacobianEntry_mixed_partial _hT 0
  have hscalar :
      surfaceCoordinateDivergence (signedCofactorScalarField σ a b c d P Q) z =
        σ * (a z * d z - b z * c z) * (Px + Qy) :=
    surfaceCoordinateDivergence_signedCofactorScalarField_of_derivative_identities
      ha hb hc hd hP hQ hP₁ hPI hQ₁ hQI hmix₁ hmix₀
  calc
    surfaceCoordinateDivergence
        (coordinateVectorDensitySignedCofactorComponentsAt σ T F') z =
      surfaceCoordinateDivergence
        (signedCofactorScalarField σ a b c d P Q) z := by
      rw [coordinateVectorDensitySignedCofactorComponentsAt_eq_scalarField]
    _ = σ * (a z * d z - b z * c z) * (Px + Qy) :=
      hscalar
    _ = σ * (fderiv ℝ T z).det *
          surfaceCoordinateDivergence F' (T z) := by
      rw [coordinateJacobian_det_eq_entries T z,
        surfaceCoordinateDivergence_eq_two_terms]

/--
%%handwave
name:
  Cofactor Piola identity in coordinates
statement:
  For a smooth coordinate change \(T\), the Euclidean divergence of
  \[
    \sigma(dP-bQ,\,-cP+aQ),\qquad (P,Q)=F'(Tz),
  \]
  is
  \[
    \sigma\det(dT)\,(\operatorname{div}F')(Tz).
  \]
proof:
  Differentiate the two displayed components.  The derivatives of \(P\) and
  \(Q\) combine by the chain rule to give
  \(\det(dT)(\partial_1P+\partial_2Q)\circ T\).  The remaining terms are
  \((\partial_1 d-\partial_2 c)P+(-\partial_1 b+\partial_2 a)Q\), and these
  vanish because \(a,b,c,d\) are first derivatives of the two coordinate
  functions of \(T\), so the mixed second derivatives agree.
-/
theorem surfaceCoordinateDivergence_coordinateVectorDensitySignedCofactorPullbackAt
    (σ : ℝ) (T : ℂ → ℂ) (F' : ℂ → Fin 2 → ℝ) (z : ℂ)
    (_hT : ContDiffAt ℝ ∞ T z)
    (_hF' : ∀ i : Fin 2, ContDiffAt ℝ ∞ (fun w : ℂ ↦ F' w i) (T z)) :
    surfaceCoordinateDivergence
        (coordinateVectorDensitySignedCofactorPullbackAt σ T F') z =
      σ * (fderiv ℝ T z).det *
        surfaceCoordinateDivergence F' (T z) := by
  rw [coordinateVectorDensitySignedCofactorPullbackAt_eq_components]
  exact
    surfaceCoordinateDivergence_coordinateVectorDensitySignedCofactorComponentsAt
      σ T F' z _hT _hF'

/--
%%handwave
name:
  Signed local Piola identity
statement:
  For a smooth coordinate change with invertible derivative near a point, the
  Euclidean divergence of the signed local vector-density pullback
  \[
    \sigma\,\det dT\,(dT)^{-1}F'\circ T
  \]
  is
  \[
    \sigma\,\det dT\,(\operatorname{div}F')\circ T .
  \]
proof:
  Expand the inverse by the two-dimensional cofactor formula.  The divergence
  of the cofactor columns cancels by equality of mixed partial derivatives of
  the two coordinate functions of \(T\).  The remaining terms are the chain
  rule for \(\operatorname{div}F'\circ T\).  The constant sign \(\sigma\)
  factors out of the computation.
-/
theorem surfaceCoordinateDivergence_coordinateVectorDensitySignedPullbackAt
    (σ : ℝ) (T : ℂ → ℂ) (F' : ℂ → Fin 2 → ℝ) (z : ℂ)
    (_hT : ContDiffAt ℝ ∞ T z)
    (_hF' : ∀ i : Fin 2, ContDiffAt ℝ ∞ (fun w : ℂ ↦ F' w i) (T z))
    (_hinv : ∀ᶠ w in 𝓝 z, (fderiv ℝ T w).IsInvertible) :
    surfaceCoordinateDivergence
        (coordinateVectorDensitySignedPullbackAt σ T F') z =
      σ * (fderiv ℝ T z).det *
        surfaceCoordinateDivergence F' (T z) := by
  have hpull :
      coordinateVectorDensitySignedPullbackAt σ T F' =ᶠ[𝓝 z]
        coordinateVectorDensitySignedCofactorPullbackAt σ T F' :=
    coordinateVectorDensitySignedPullbackAt_eventuallyEq_signedCofactor
      _hinv
  calc
    surfaceCoordinateDivergence
        (coordinateVectorDensitySignedPullbackAt σ T F') z =
      surfaceCoordinateDivergence
        (coordinateVectorDensitySignedCofactorPullbackAt σ T F') z :=
      surfaceCoordinateDivergence_congr_eventuallyEq hpull
    _ = σ * (fderiv ℝ T z).det *
          surfaceCoordinateDivergence F' (T z) :=
      surfaceCoordinateDivergence_coordinateVectorDensitySignedCofactorPullbackAt
        σ T F' z _hT _hF'

/--
%%handwave
name:
  Local Piola identity for coordinate vector densities
statement:
  If \(T\) is smooth near a point, \(dT\) is invertible near that point, and
  \(F'\) is smooth near the image point, then the Euclidean divergence of the
  local vector-density pullback
  \[
    |\det dT|\,(dT)^{-1}F'\circ T
  \]
  is
  \[
    |\det dT|\,(\operatorname{div}F')\circ T .
  \]
proof:
  Choose a small neighborhood where the Jacobian determinant has constant
  sign.  There the absolute value is a fixed sign times the determinant.
  Expanding the inverse by the two-dimensional cofactor formula, the
  divergence of the cofactor columns cancels by equality of mixed partial
  derivatives of the two coordinate functions of \(T\).  The remaining terms
  are exactly the chain rule for \(\operatorname{div}F'\circ T\).
-/
theorem surfaceCoordinateDivergence_coordinateVectorDensityPullbackAt
    (T : ℂ → ℂ) (F' : ℂ → Fin 2 → ℝ) (z : ℂ)
    (_hT : ContDiffAt ℝ ∞ T z)
    (_hF' : ∀ i : Fin 2, ContDiffAt ℝ ∞ (fun w : ℂ ↦ F' w i) (T z))
    (_hinv : ∀ᶠ w in 𝓝 z, (fderiv ℝ T w).IsInvertible) :
    surfaceCoordinateDivergence
        (coordinateVectorDensityPullbackAt T F') z =
      |(fderiv ℝ T z).det| *
        surfaceCoordinateDivergence F' (T z) := by
  let σ : ℝ := coordinateJacobianSignAt T z
  have hinv_z : (fderiv ℝ T z).IsInvertible := _hinv.self_of_nhds
  have hdet_ne : (fderiv ℝ T z).det ≠ 0 :=
    coordinateComplexDet_ne_zero_of_isInvertible (fderiv ℝ T z) hinv_z
  have hdet_event :
      ∀ᶠ w in 𝓝 z,
        |(fderiv ℝ T w).det| = σ * (fderiv ℝ T w).det := by
    simpa [σ] using
      eventually_abs_jacobianDet_eq_coordinateJacobianSignAt_mul
        (T := T) (z := z) _hT hdet_ne
  have hpull :
      coordinateVectorDensityPullbackAt T F' =ᶠ[𝓝 z]
        coordinateVectorDensitySignedPullbackAt σ T F' :=
    coordinateVectorDensityPullbackAt_eventuallyEq_signed hdet_event
  have hpiola :
      surfaceCoordinateDivergence
          (coordinateVectorDensitySignedPullbackAt σ T F') z =
        σ * (fderiv ℝ T z).det *
          surfaceCoordinateDivergence F' (T z) :=
    surfaceCoordinateDivergence_coordinateVectorDensitySignedPullbackAt
      σ T F' z _hT _hF' _hinv
  calc
    surfaceCoordinateDivergence
        (coordinateVectorDensityPullbackAt T F') z =
      surfaceCoordinateDivergence
        (coordinateVectorDensitySignedPullbackAt σ T F') z :=
      surfaceCoordinateDivergence_congr_eventuallyEq hpull
    _ = σ * (fderiv ℝ T z).det *
          surfaceCoordinateDivergence F' (T z) :=
      hpiola
    _ = |(fderiv ℝ T z).det| *
          surfaceCoordinateDivergence F' (T z) := by
      rw [show σ * (fderiv ℝ T z).det =
          |(fderiv ℝ T z).det| by
        simpa [σ] using coordinateJacobianSignAt_mul_det_eq_abs
          (T := T) (z := z) hdet_ne]

/--
%%handwave
name:
  Piola identity for the canonical coordinate vector-density pullback
statement:
  The Euclidean divergence of the canonical pullback
  \[
    |\det dT|\,(dT)^{-1}F'\circ T
  \]
  is
  \[
    |\det dT|\,(\operatorname{div}F')\circ T .
  \]
proof:
  This is the local two-dimensional Piola identity.  On a small neighborhood
  the Jacobian determinant has constant sign, so the absolute value is a
  constant sign times the determinant.  Writing the inverse through the
  cofactor matrix, the mixed second derivatives of the two coordinate
  functions of \(T\) cancel, and the remaining first-derivative terms are the
  chain rule for \(\operatorname{div}F'\circ T\).
-/
theorem surfaceCoordinateDivergence_coordinateVectorDensityPullback
    (T : ℂ → ℂ) (Ω Ω' : Set ℂ)
    (F' : ℂ → Fin 2 → ℝ)
    (_hΩ : IsOpen Ω) (_hΩ' : IsOpen Ω')
    (_hT_maps : Set.MapsTo T Ω Ω')
    (_hT : ContDiffOn ℝ ∞ T Ω)
    (_hF' : ∀ i : Fin 2, ContDiffOn ℝ ∞ (fun z : ℂ ↦ F' z i) Ω')
    (_hinv : ∀ z ∈ Ω, (fderivWithin ℝ T Ω z).IsInvertible) :
    ∀ z ∈ Ω,
      surfaceCoordinateDivergence
          (coordinateVectorDensityPullback T Ω F') z =
        |(fderivWithin ℝ T Ω z).det| *
          surfaceCoordinateDivergence F' (T z) := by
  intro z hz
  have hz' : T z ∈ Ω' := _hT_maps hz
  have hlocal :
      coordinateVectorDensityPullback T Ω F' =ᶠ[𝓝 z]
        coordinateVectorDensityPullbackAt T F' :=
    coordinateVectorDensityPullback_eventuallyEq_at _hΩ hz
  have hT_at : ContDiffAt ℝ ∞ T z :=
    (_hT z hz).contDiffAt (_hΩ.mem_nhds hz)
  have hF'_at : ∀ i : Fin 2,
      ContDiffAt ℝ ∞ (fun w : ℂ ↦ F' w i) (T z) := by
    intro i
    exact (_hF' i (T z) hz').contDiffAt (_hΩ'.mem_nhds hz')
  have hinv_at : ∀ᶠ w in 𝓝 z, (fderiv ℝ T w).IsInvertible := by
    filter_upwards [_hΩ.mem_nhds hz] with w hw
    have hw_inv : (fderivWithin ℝ T Ω w).IsInvertible := _hinv w hw
    rwa [fderivWithin_of_isOpen _hΩ hw] at hw_inv
  have hpiola :=
    surfaceCoordinateDivergence_coordinateVectorDensityPullbackAt
      T F' z hT_at hF'_at hinv_at
  have hJ :
      fderivWithin ℝ T Ω z = fderiv ℝ T z :=
    fderivWithin_of_isOpen _hΩ hz
  calc
    surfaceCoordinateDivergence
        (coordinateVectorDensityPullback T Ω F') z =
      surfaceCoordinateDivergence
        (coordinateVectorDensityPullbackAt T F') z :=
      surfaceCoordinateDivergence_congr_eventuallyEq hlocal
    _ = |(fderiv ℝ T z).det| *
          surfaceCoordinateDivergence F' (T z) :=
      hpiola
    _ = |(fderivWithin ℝ T Ω z).det| *
          surfaceCoordinateDivergence F' (T z) := by
      rw [hJ]

/--
%%handwave
name:
  Piola identity for coordinate vector densities
statement:
  If a coordinate vector density is pulled back by a smooth coordinate change,
  then its Euclidean divergence transforms as a scalar density:
  \[
    \operatorname{div} F
      = |\det dT|\,(\operatorname{div}F')\circ T.
  \]
proof:
  This is the two-dimensional Piola identity.  In coordinates it follows by
  differentiating
  \(F=|\det dT|(dT)^{-1}F'\circ T\); the derivatives of the cofactor matrix of
  \(dT\) cancel by equality of mixed partial derivatives.
-/
theorem surfaceCoordinateDivergence_transform_of_vectorDensityPullback
    (T : ℂ → ℂ) (Ω Ω' : Set ℂ)
    (F F' : ℂ → Fin 2 → ℝ)
    (_hΩ : IsOpen Ω) (_hΩ' : IsOpen Ω')
    (_hT_maps : Set.MapsTo T Ω Ω')
    (_hT : ContDiffOn ℝ ∞ T Ω)
    (_hF : ∀ i : Fin 2, ContDiffOn ℝ ∞ (fun z : ℂ ↦ F z i) Ω)
    (_hF' : ∀ i : Fin 2, ContDiffOn ℝ ∞ (fun z : ℂ ↦ F' z i) Ω')
    (_hpull : IsVectorDensityPullbackBy T Ω F F') :
    ∀ z ∈ Ω,
      surfaceCoordinateDivergence F z =
        |(fderivWithin ℝ T Ω z).det| *
          surfaceCoordinateDivergence F' (T z) := by
  intro z hz
  have hinv : ∀ z ∈ Ω, (fderivWithin ℝ T Ω z).IsInvertible := by
    intro y hy
    exact (_hpull y hy).1
  have hlocal :
      F =ᶠ[𝓝 z] coordinateVectorDensityPullback T Ω F' :=
    _hpull.eventuallyEq_coordinateVectorDensityPullback _hΩ hz
  calc
    surfaceCoordinateDivergence F z =
        surfaceCoordinateDivergence
          (coordinateVectorDensityPullback T Ω F') z :=
      surfaceCoordinateDivergence_congr_eventuallyEq hlocal
    _ = |(fderivWithin ℝ T Ω z).det| *
          surfaceCoordinateDivergence F' (T z) :=
      surfaceCoordinateDivergence_coordinateVectorDensityPullback
        T Ω Ω' F' _hΩ _hΩ' _hT_maps _hT _hF' hinv z hz

/--
%%handwave
name:
  Inverse Gram coefficients are symmetric
statement:
  The inverse Gram matrix of the metric in a coordinate chart is symmetric.
proof:
  The metric Gram matrix is symmetric, and the explicit \(2\times2\) inverse
  formula preserves symmetry.
-/
theorem surfaceMetricInverseGramCoeffInChart_symm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ) :
    ∀ i j : Fin 2,
      surfaceMetricInverseGramCoeffInChart g e z i j =
        surfaceMetricInverseGramCoeffInChart g e z j i := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  intro i j
  fin_cases i <;> fin_cases j
  · simp
  · simp [surfaceMetricInverseGramCoeffInChart,
      g.toContMDiffRiemannianMetric.symm (e.symm z)]
  · simp [surfaceMetricInverseGramCoeffInChart,
      g.toContMDiffRiemannianMetric.symm (e.symm z)]
  · simp

/--
%%handwave
name:
  Inverse metric coefficients are smooth in coordinates
statement:
  The entries of the inverse Gram matrix of a smooth positive metric are
  smooth functions of the coordinate point.
proof:
  In dimension two the inverse matrix entries are explicit rational
  expressions in the Gram entries.  The Gram entries and determinant are
  smooth in coordinates, and the determinant is positive in a genuine chart,
  so inverting it preserves smoothness.
-/
theorem surfaceMetricInverseGramCoeffInChart_contDiffOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (i j : Fin 2) :
    ContDiffOn ℝ ∞
      (fun z : ℂ ↦ surfaceMetricInverseGramCoeffInChart g e z i j)
      e.target := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  have hdet : ContDiffOn ℝ ∞ (surfaceMetricGramDetInChart g e) e.target :=
    surfaceMetricGramDetInChart_contDiffOn X g e _he
  have hdet_inv :
      ContDiffOn ℝ ∞ (fun z : ℂ ↦ (surfaceMetricGramDetInChart g e z)⁻¹)
        e.target :=
    hdet.inv fun z hz ↦
      ne_of_gt (surfaceMetricGramDetInChart_pos X g e _he z hz)
  have h11 : ContDiffOn ℝ ∞
      (fun z : ℂ ↦
        g.toContMDiffRiemannianMetric.inner (e.symm z)
          (surfaceChartTangentMap e z (1 : ℂ))
          (surfaceChartTangentMap e z (1 : ℂ))) e.target :=
    surfaceMetricGramEntryInChart_contDiffOn X
      g.toContMDiffRiemannianMetric e _he (1 : ℂ) (1 : ℂ)
  have h12 : ContDiffOn ℝ ∞
      (fun z : ℂ ↦
        g.toContMDiffRiemannianMetric.inner (e.symm z)
          (surfaceChartTangentMap e z (1 : ℂ))
          (surfaceChartTangentMap e z Complex.I)) e.target :=
    surfaceMetricGramEntryInChart_contDiffOn X
      g.toContMDiffRiemannianMetric e _he (1 : ℂ) Complex.I
  have h21 : ContDiffOn ℝ ∞
      (fun z : ℂ ↦
        g.toContMDiffRiemannianMetric.inner (e.symm z)
          (surfaceChartTangentMap e z Complex.I)
          (surfaceChartTangentMap e z (1 : ℂ))) e.target :=
    surfaceMetricGramEntryInChart_contDiffOn X
      g.toContMDiffRiemannianMetric e _he Complex.I (1 : ℂ)
  have h22 : ContDiffOn ℝ ∞
      (fun z : ℂ ↦
        g.toContMDiffRiemannianMetric.inner (e.symm z)
          (surfaceChartTangentMap e z Complex.I)
          (surfaceChartTangentMap e z Complex.I)) e.target :=
    surfaceMetricGramEntryInChart_contDiffOn X
      g.toContMDiffRiemannianMetric e _he Complex.I Complex.I
  fin_cases i <;> fin_cases j
  · simpa [surfaceMetricInverseGramCoeffInChart] using hdet_inv.mul h22
  · simpa [surfaceMetricInverseGramCoeffInChart] using hdet_inv.neg.mul h12
  · simpa [surfaceMetricInverseGramCoeffInChart] using hdet_inv.neg.mul h21
  · simpa [surfaceMetricInverseGramCoeffInChart] using hdet_inv.mul h11

/--
%%handwave
name:
  Inverse metric coefficients are measurable for coordinate volume
statement:
  Each inverse metric coefficient is almost everywhere strongly measurable
  with respect to the coordinate Riemannian volume measure.
-/
theorem surfaceMetricInverseGramCoeffInChart_aestronglyMeasurable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (i j : Fin 2) :
    AEStronglyMeasurable
      (fun z : ℂ ↦ surfaceMetricInverseGramCoeffInChart g e z i j)
      (riemannianVolumeChartMeasure g e) := by
  have hcont : ContinuousOn
      (fun z : ℂ ↦ surfaceMetricInverseGramCoeffInChart g e z i j)
      e.target :=
    (surfaceMetricInverseGramCoeffInChart_contDiffOn g e _he i j).continuousOn
  have hvol : AEStronglyMeasurable
      (fun z : ℂ ↦ surfaceMetricInverseGramCoeffInChart g e z i j)
      (MeasureTheory.volume.restrict e.target) :=
    hcont.aestronglyMeasurable e.open_target.measurableSet
  have hac :
      riemannianVolumeChartMeasure g e ≪
        MeasureTheory.volume.restrict e.target := by
    rw [riemannianVolumeChartMeasure]
    exact withDensity_absolutelyContinuous _ _
  exact AEStronglyMeasurable.mono_ac hac hvol

/--
%%handwave
name:
  Divergence-form Laplacian in a chart
statement:
  In a coordinate chart, the Laplace-Beltrami operator is the volume-density
  inverse times the Euclidean divergence of the metric gradient flux.
-/
noncomputable def surfaceDivergenceFormLaplaceBeltramiInChart {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (f : X → ℝ) (z : ℂ) : ℝ :=
  let ρ := surfaceMetricVolumeDensityInChart g e z
  ρ⁻¹ *
    (fderiv ℝ (fun w : ℂ ↦ surfaceMetricGradientFluxInChart g e f w 0) z (1 : ℂ) +
      fderiv ℝ (fun w : ℂ ↦ surfaceMetricGradientFluxInChart g e f w 1) z Complex.I)

/--
%%handwave
name:
  Divergence-form Laplace-Beltrami operator
statement:
  The global divergence-form Laplace-Beltrami operator is computed in the
  preferred chart at each point by the local coordinate expression
  \[
    \Delta_g f=\rho^{-1}\partial_i(\rho g^{ij}\partial_j f).
  \]
-/
noncomputable def surfaceDivergenceFormLaplaceBeltrami {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) : (X → ℝ) → X → ℝ :=
  fun f x ↦
    let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
    surfaceDivergenceFormLaplaceBeltramiInChart g e f (e x)

/--
%%handwave
name:
  Density cancels in the divergence-form Laplacian
statement:
  Let \(e:U\to V\) be a surface chart, let
  \(\rho=\sqrt{\det(g_{ij})}\), and write
  \[
    D=\partial_1(\rho g^{1j}\partial_jf)
      +\partial_2(\rho g^{2j}\partial_jf).
  \]
  For \(z\in V\) and any function \(\eta\),
  \[
    (\Delta_gf)(z)\,\eta(e^{-1}z)\,\rho(z)
      =D(z)\,\eta(e^{-1}z).
  \]
proof:
  Positivity of the metric volume density on \(V\) gives \(\rho(z)\ne0\).
  Substitute \(\Delta_gf=\rho^{-1}D\) and cancel
  \(\rho(z)^{-1}\rho(z)\).
-/
theorem surfaceDivergenceFormLaplaceBeltramiInChart_mul_volumeDensity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ) :
    ∀ z ∈ e.target,
      surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
          η (e.symm z) * surfaceMetricVolumeDensityInChart metric e z =
        (fderiv ℝ (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
            z (1 : ℂ) +
          fderiv ℝ (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
            z Complex.I) * η (e.symm z) := by
  intro z hz
  let ρ := surfaceMetricVolumeDensityInChart metric e z
  let D₁ :=
    fderiv ℝ (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
      z (1 : ℂ)
  let D₂ :=
    fderiv ℝ (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
      z Complex.I
  have hρ_pos :
      0 < ρ :=
    (surfaceMetricVolumeDensityInChart_smooth_positive X metric e _he).2 z hz
  have hρ_ne : ρ ≠ 0 :=
    ne_of_gt hρ_pos
  change (ρ⁻¹ * (D₁ + D₂)) * η (e.symm z) * ρ =
    (D₁ + D₂) * η (e.symm z)
  field_simp [hρ_ne]

/--
%%handwave
name:
  Coordinate pairing times density is flux contraction
statement:
  The coordinate inverse-metric pairing multiplied by the volume density is
  the contraction of the metric gradient flux with the coordinate derivative
  of the second function.
proof:
  Expand both sides in the two coordinate directions.  The identity follows
  from symmetry of the inverse Gram coefficients.
-/
theorem surfaceMetricCoordinateGradientPairingInChart_mul_volumeDensity_eq_flux
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (f η : X → ℝ) (z : ℂ) :
    surfaceMetricCoordinateGradientPairingInChart metric e f η z *
        surfaceMetricVolumeDensityInChart metric e z =
      ∑ i : Fin 2,
        surfaceMetricGradientFluxInChart metric e f z i *
          surfaceFunctionChartDerivativeComponent e η z i := by
  rw [surfaceMetricCoordinateGradientPairingInChart_eq_four_terms]
  rw [Fin.sum_univ_two]
  rw [surfaceMetricGradientFluxInChart_zero, surfaceMetricGradientFluxInChart_one]
  rw [surfaceMetricInverseGramCoeffInChart_symm metric e z 0 1]
  ring

/--
%%handwave
name:
  Smooth chart representatives are differentiable
statement:
  A smooth surface function has a differentiable coordinate representative in
  every surface chart.
proof:
  Smoothness on the surface says that the coordinate representative is smooth
  in each chart.  Smooth real maps between finite-dimensional normed spaces
  are differentiable.
-/
theorem surfaceFunctionChartRepresentative_differentiableAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f : X → ℝ) (hf : IsSmoothOnSurface (Set.univ : Set X) f) :
    ∀ z ∈ e.target,
      DifferentiableAt ℝ (fun w : ℂ ↦ f (e.symm w)) z := by
  intro z hz
  have hchart :
      ContDiffOn ℝ ∞ (fun w : ℂ ↦ f (e.symm w)) e.target := by
    simpa using hf e _he
  have hchart_at :
      ContDiffAt ℝ ∞ (fun w : ℂ ↦ f (e.symm w)) z :=
    hchart.contDiffAt (e.open_target.mem_nhds hz)
  exact hchart_at.differentiableAt (by simp)

/--
%%handwave
name:
  Metric flux is smooth in coordinates
statement:
  For a smooth function, each coordinate component of the metric gradient
  flux is smooth inside the chart.
proof:
  The flux is the product of the smooth volume density, the smooth inverse
  metric coefficients, and the coordinate derivatives of the smooth function.
-/
theorem surfaceMetricGradientFluxInChart_contDiffOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f : X → ℝ) (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (i : Fin 2) :
    ContDiffOn ℝ ∞
      (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w i)
      e.target := by
  have hρ : ContDiffOn ℝ ∞
      (surfaceMetricVolumeDensityInChart metric e) e.target :=
    (surfaceMetricVolumeDensityInChart_smooth_positive X metric e _he).1
  have hsum : ContDiffOn ℝ ∞
      (fun w : ℂ ↦
        ∑ j : Fin 2,
          surfaceMetricInverseGramCoeffInChart metric e w i j *
            surfaceFunctionChartDerivativeComponent e f w j)
      e.target := by
    simpa using
      (ContDiffOn.sum (s := Finset.univ)
        (fun j _ ↦
          (surfaceMetricInverseGramCoeffInChart_contDiffOn
              metric e _he i j).mul
          (surfaceFunctionChartDerivativeComponent_contDiffOn
              e _he f hf j)))
  simpa [surfaceMetricGradientFluxInChart] using hρ.mul hsum

/--
%%handwave
name:
  Local smoothness of the metric flux
statement:
  In a fixed chart, if a coordinate representative is smooth on an open subset
  of the chart image, then each component of the metric gradient flux is smooth
  on that subset.
proof:
  The flux is built from the smooth volume density, the smooth inverse metric
  coefficients, and the smooth first coordinate derivatives of the function.
-/
theorem surfaceMetricGradientFluxInChart_contDiffOn_of_local_contDiffOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f : X → ℝ) {S : Set ℂ} (hS_open : IsOpen S) (hS_subset : S ⊆ e.target)
    (hf : ContDiffOn ℝ ∞ (fun w : ℂ ↦ f (e.symm w)) S)
    (i : Fin 2) :
    ContDiffOn ℝ ∞
      (fun z : ℂ ↦ surfaceMetricGradientFluxInChart metric e f z i) S := by
  have hρ : ContDiffOn ℝ ∞
      (surfaceMetricVolumeDensityInChart metric e) S :=
    (surfaceMetricVolumeDensityInChart_smooth_positive X metric e _he).1.mono
      hS_subset
  have hsum : ContDiffOn ℝ ∞
      (fun z : ℂ ↦
        ∑ j : Fin 2,
          surfaceMetricInverseGramCoeffInChart metric e z i j *
            surfaceFunctionChartDerivativeComponent e f z j) S := by
    simpa using
      (ContDiffOn.sum (s := Finset.univ)
        (fun j _ ↦
          ((surfaceMetricInverseGramCoeffInChart_contDiffOn
                metric e _he i j).mono hS_subset).mul
            (surfaceFunctionChartDerivativeComponent_contDiffOn_of_local_contDiffOn
              e f hS_open hf j)))
  simpa [surfaceMetricGradientFluxInChart] using hρ.mul hsum

/--
%%handwave
name:
  Coordinate derivatives of metric flux are continuous
statement:
  The coordinate directional derivatives of a metric flux component are
  continuous on the chart.
proof:
  Differentiate the smooth chart expression for the flux and evaluate the
  resulting derivative on a fixed coordinate vector.
-/
theorem surfaceMetricGradientFluxInChart_fderiv_apply_continuousOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f : X → ℝ) (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (i : Fin 2) (v : ℂ) :
    ContinuousOn
      (fun z : ℂ ↦
        fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w i)
          z v)
      e.target := by
  have hflux :
      ContDiffOn ℝ ∞
        (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w i)
        e.target :=
    surfaceMetricGradientFluxInChart_contDiffOn metric e _he f hf i
  have hderiv :
      ContDiffOn ℝ ∞
        (fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w i))
        e.target :=
    hflux.fderiv_of_isOpen e.open_target (by simp)
  simpa using (hderiv.clm_apply (contDiffOn_const (c := v))).continuousOn

/--
%%handwave
name:
  Metric flux is differentiable in coordinates
statement:
  For a smooth function, each coordinate component of the metric gradient
  flux is differentiable inside the chart.
proof:
  The flux is the product of the smooth volume density, the smooth inverse
  metric coefficients, and the coordinate derivatives of the smooth function.
-/
theorem surfaceMetricGradientFluxInChart_differentiableAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f : X → ℝ) (hf : IsSmoothOnSurface (Set.univ : Set X) f) :
    ∀ i : Fin 2, ∀ z ∈ e.target,
      DifferentiableAt ℝ
        (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w i) z := by
  intro i z hz
  have hflux : ContDiffOn ℝ ∞
      (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w i)
      e.target :=
    surfaceMetricGradientFluxInChart_contDiffOn metric e _he f hf i
  exact (hflux.contDiffAt (e.open_target.mem_nhds hz)).differentiableAt (by simp)

/--
%%handwave
name:
  Euclidean divergence integration by parts on the plane
statement:
  On the coordinate plane, if the two flux components and the corresponding
  differentiated products are integrable, then the integral of the Euclidean
  divergence against a test function is minus the integral of the flux
  contracted with the derivative of the test function.
proof:
  Apply Mathlib's one-direction integration-by-parts theorem separately in the
  two coordinate directions \(1\) and \(i\), then add the two identities.
-/
theorem euclidean_divergence_integral_by_parts_on_plane
    (F : Fin 2 → ℂ → ℝ) (ψ : ℂ → ℝ)
    (hF_diff : ∀ i : Fin 2, ∀ z ∈ tsupport ψ, DifferentiableAt ℝ (F i) z)
    (hψ_diff :
      ∀ i : Fin 2, ∀ z ∈ tsupport (F i), DifferentiableAt ℝ ψ z)
    (hDψ :
      ∀ i : Fin 2,
        Integrable
          (fun z : ℂ ↦
            fderiv ℝ (F i) z (complexCoordinateVector i) * ψ z))
    (hFdψ :
      ∀ i : Fin 2,
        Integrable
          (fun z : ℂ ↦
            F i z * fderiv ℝ ψ z (complexCoordinateVector i)))
    (hFψ :
      ∀ i : Fin 2, Integrable (fun z : ℂ ↦ F i z * ψ z)) :
    ∫ z : ℂ,
        (fderiv ℝ (F 0) z (1 : ℂ) +
          fderiv ℝ (F 1) z Complex.I) * ψ z =
      - ∫ z : ℂ,
        ∑ i : Fin 2, F i z * fderiv ℝ ψ z (complexCoordinateVector i) := by
  have hD0 :
      Integrable (fun z : ℂ ↦ fderiv ℝ (F 0) z (1 : ℂ) * ψ z) := by
    simpa using hDψ 0
  have hD1 :
      Integrable (fun z : ℂ ↦ fderiv ℝ (F 1) z Complex.I * ψ z) := by
    simpa using hDψ 1
  have hFd0 :
      Integrable (fun z : ℂ ↦ F 0 z * fderiv ℝ ψ z (1 : ℂ)) := by
    simpa using hFdψ 0
  have hFd1 :
      Integrable (fun z : ℂ ↦ F 1 z * fderiv ℝ ψ z Complex.I) := by
    simpa using hFdψ 1
  have h0_raw :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := MeasureTheory.volume) (f := F 0) (g := ψ)
      (v := complexCoordinateVector 0)
      (hDψ 0) (hFdψ 0) (hFψ 0) (hF_diff 0) (hψ_diff 0)
  have h0 :
      ∫ z : ℂ, fderiv ℝ (F 0) z (1 : ℂ) * ψ z =
        - ∫ z : ℂ, F 0 z * fderiv ℝ ψ z (1 : ℂ) := by
    have h0_raw' :
        (∫ z : ℂ, F 0 z * fderiv ℝ ψ z (1 : ℂ)) =
          - (∫ z : ℂ, fderiv ℝ (F 0) z (1 : ℂ) * ψ z) := by
      simpa using h0_raw
    calc
      (∫ z : ℂ, fderiv ℝ (F 0) z (1 : ℂ) * ψ z)
          = - (-(∫ z : ℂ, fderiv ℝ (F 0) z (1 : ℂ) * ψ z)) := by
            ring
      _ = - (∫ z : ℂ, F 0 z * fderiv ℝ ψ z (1 : ℂ)) := by
            rw [← h0_raw']
  have h1_raw :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := MeasureTheory.volume) (f := F 1) (g := ψ)
      (v := complexCoordinateVector 1)
      (hDψ 1) (hFdψ 1) (hFψ 1) (hF_diff 1) (hψ_diff 1)
  have h1 :
      ∫ z : ℂ, fderiv ℝ (F 1) z Complex.I * ψ z =
        - ∫ z : ℂ, F 1 z * fderiv ℝ ψ z Complex.I := by
    have h1_raw' :
        (∫ z : ℂ, F 1 z * fderiv ℝ ψ z Complex.I) =
          - (∫ z : ℂ, fderiv ℝ (F 1) z Complex.I * ψ z) := by
      simpa using h1_raw
    calc
      (∫ z : ℂ, fderiv ℝ (F 1) z Complex.I * ψ z)
          = - (-(∫ z : ℂ, fderiv ℝ (F 1) z Complex.I * ψ z)) := by
            ring
      _ = - (∫ z : ℂ, F 1 z * fderiv ℝ ψ z Complex.I) := by
            rw [← h1_raw']
  have hleft_split :
      ∫ z : ℂ,
          (fderiv ℝ (F 0) z (1 : ℂ) +
            fderiv ℝ (F 1) z Complex.I) * ψ z =
        (∫ z : ℂ, fderiv ℝ (F 0) z (1 : ℂ) * ψ z) +
          (∫ z : ℂ, fderiv ℝ (F 1) z Complex.I * ψ z) := by
    have hfun :
        (fun z : ℂ ↦
          (fderiv ℝ (F 0) z (1 : ℂ) +
            fderiv ℝ (F 1) z Complex.I) * ψ z) =
          (fun z : ℂ ↦
            fderiv ℝ (F 0) z (1 : ℂ) * ψ z +
              fderiv ℝ (F 1) z Complex.I * ψ z) := by
      funext z
      ring
    rw [hfun]
    exact integral_add hD0 hD1
  have hright_split :
      ∫ z : ℂ,
          ∑ i : Fin 2, F i z * fderiv ℝ ψ z (complexCoordinateVector i) =
        (∫ z : ℂ, F 0 z * fderiv ℝ ψ z (1 : ℂ)) +
          (∫ z : ℂ, F 1 z * fderiv ℝ ψ z Complex.I) := by
    have hfun :
        (fun z : ℂ ↦
          ∑ i : Fin 2, F i z * fderiv ℝ ψ z (complexCoordinateVector i)) =
          (fun z : ℂ ↦
            F 0 z * fderiv ℝ ψ z (1 : ℂ) +
              F 1 z * fderiv ℝ ψ z Complex.I) := by
      funext z
      simp [Fin.sum_univ_two]
    rw [hfun]
    exact integral_add hFd0 hFd1
  rw [hleft_split, hright_split, h0, h1]
  ring

/--
%%handwave
name:
  Euclidean divergence integration by parts with compact support in an open set
statement:
  On an open subset of the coordinate plane, the Euclidean divergence
  integration-by-parts identity follows from the whole-plane identity when
  the test function has topological support contained in the open set and the
  componentwise products required by integration by parts are integrable.
proof:
  The support condition makes the left integrand vanish outside the open set.
  The derivative of the test function also vanishes off its topological
  support, so the right integrand vanishes outside the open set as well.
  After localizing both whole-plane integrals to the open set, apply the
  whole-plane integration-by-parts lemma.
-/
theorem euclidean_divergence_integral_by_parts_on_open_of_component_integrable
    (Ω : Set ℂ) (_hΩ : IsOpen Ω)
    (F : Fin 2 → ℂ → ℝ) (ψ : ℂ → ℝ)
    (hψ_support : tsupport ψ ⊆ Ω)
    (hF_diff : ∀ i : Fin 2, ∀ z ∈ Ω, DifferentiableAt ℝ (F i) z)
    (hψ_diff : ∀ z ∈ Ω, DifferentiableAt ℝ ψ z)
    (hDψ :
      ∀ i : Fin 2,
        Integrable
          (fun z : ℂ ↦
            fderiv ℝ (F i) z (complexCoordinateVector i) * ψ z))
    (hFdψ :
      ∀ i : Fin 2,
        Integrable
          (fun z : ℂ ↦
            F i z * fderiv ℝ ψ z (complexCoordinateVector i)))
    (hFψ :
      ∀ i : Fin 2, Integrable (fun z : ℂ ↦ F i z * ψ z)) :
    ∫ z in Ω,
        (fderiv ℝ (F 0) z (1 : ℂ) +
          fderiv ℝ (F 1) z Complex.I) * ψ z =
      - ∫ z in Ω,
        ∑ i : Fin 2, F i z * fderiv ℝ ψ z (complexCoordinateVector i) := by
  let left : ℂ → ℝ :=
    fun z ↦
      (fderiv ℝ (F 0) z (1 : ℂ) +
        fderiv ℝ (F 1) z Complex.I) * ψ z
  let right : ℂ → ℝ :=
    fun z ↦
      ∑ i : Fin 2, F i z * fderiv ℝ ψ z (complexCoordinateVector i)
  have hF_diff_support :
      ∀ i : Fin 2, ∀ z ∈ tsupport ψ, DifferentiableAt ℝ (F i) z := by
    intro i z hz
    exact hF_diff i z (hψ_support hz)
  have hψ_diff_support :
      ∀ i : Fin 2, ∀ z ∈ tsupport (F i), DifferentiableAt ℝ ψ z := by
    intro _i z _hz
    by_cases hzΩ : z ∈ Ω
    · exact hψ_diff z hzΩ
    · have hzψ : z ∉ tsupport ψ := fun hz ↦ hzΩ (hψ_support hz)
      exact (HasFDerivAt.of_notMem_tsupport (𝕜 := ℝ) (f := ψ) hzψ).differentiableAt
  have hplane :=
    euclidean_divergence_integral_by_parts_on_plane
      F ψ hF_diff_support hψ_diff_support hDψ hFdψ hFψ
  have hleft_set :
      ∫ z : ℂ, left z = ∫ z in Ω, left z := by
    exact integral_eq_setIntegral_of_tsupport_subset
      ((tsupport_mul_subset_right).trans hψ_support)
  have hright_set :
      ∫ z : ℂ, right z = ∫ z in Ω, right z := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := MeasureTheory.volume) (s := Ω) (f := right) ?_).symm
    intro z hzΩ
    have hzψ : z ∉ tsupport ψ := fun hz ↦ hzΩ (hψ_support hz)
    have hdψ : fderiv ℝ ψ z = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := ψ) hzψ
    simp [right, hdψ]
  change ∫ z in Ω, left z = - ∫ z in Ω, right z
  rw [← hleft_set, ← hright_set]
  exact hplane

/--
%%handwave
name:
  Compactly supported chart products are componentwise integrable
statement:
  If a test function has compact support inside an open coordinate set, and
  the flux components and their first coordinate derivatives are continuous
  there, then all componentwise products needed for Euclidean
  integration by parts are integrable on the plane.
proof:
  Each product is continuous on the open set and its topological support lies
  in the compact support of the test function.  The derivative of the test
  function has support contained in the support of the test function, so the
  same compact support controls the terms involving \(d\psi\).
-/
theorem euclidean_component_products_integrable_of_tsupport_subset_isCompact
    (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (F : Fin 2 → ℂ → ℝ) (ψ : ℂ → ℝ)
    (hψ_support : tsupport ψ ⊆ Ω)
    (hψ_compact : IsCompact (tsupport ψ))
    (hF_cont : ∀ i : Fin 2, ContinuousOn (F i) Ω)
    (hDF_cont :
      ∀ i : Fin 2,
        ContinuousOn
          (fun z : ℂ ↦ fderiv ℝ (F i) z (complexCoordinateVector i)) Ω)
    (hψ_cont : ContinuousOn ψ Ω)
    (hDψ_cont :
      ∀ i : Fin 2,
        ContinuousOn
          (fun z : ℂ ↦ fderiv ℝ ψ z (complexCoordinateVector i)) Ω) :
    (∀ i : Fin 2,
        Integrable
          (fun z : ℂ ↦
            fderiv ℝ (F i) z (complexCoordinateVector i) * ψ z)) ∧
      (∀ i : Fin 2,
        Integrable
          (fun z : ℂ ↦
            F i z * fderiv ℝ ψ z (complexCoordinateVector i))) ∧
      (∀ i : Fin 2, Integrable (fun z : ℂ ↦ F i z * ψ z)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine integrable_of_continuousOn_of_tsupport_subset_isCompact
      ((hDF_cont i).mul hψ_cont) hΩ ?_ ?_
    · exact (tsupport_mul_subset_right).trans hψ_support
    · exact hψ_compact.of_isClosed_subset (isClosed_tsupport _)
        tsupport_mul_subset_right
  · intro i
    refine integrable_of_continuousOn_of_tsupport_subset_isCompact
      ((hF_cont i).mul (hDψ_cont i)) hΩ ?_ ?_
    · exact (tsupport_mul_subset_right.trans
        (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := ψ)
          (complexCoordinateVector i))).trans hψ_support
    · exact hψ_compact.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_mul_subset_right.trans
          (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := ψ)
            (complexCoordinateVector i)))
  · intro i
    refine integrable_of_continuousOn_of_tsupport_subset_isCompact
      ((hF_cont i).mul hψ_cont) hΩ ?_ ?_
    · exact (tsupport_mul_subset_right).trans hψ_support
    · exact hψ_compact.of_isClosed_subset (isClosed_tsupport _)
        tsupport_mul_subset_right

/--
%%handwave
name:
  Euclidean divergence integration by parts from compact support and continuity
statement:
  On an open subset of the coordinate plane, a compactly supported test
  function and locally continuous flux data give the Euclidean
  integration-by-parts identity.
proof:
  The compact support and local continuity hypotheses give the componentwise
  integrability hypotheses.  The preceding open-set integration-by-parts
  theorem then applies.
-/
theorem euclidean_divergence_integral_by_parts_on_open_of_tsupport_subset_isCompact
    (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (F : Fin 2 → ℂ → ℝ) (ψ : ℂ → ℝ)
    (hψ_support : tsupport ψ ⊆ Ω)
    (hψ_compact : IsCompact (tsupport ψ))
    (hF_diff : ∀ i : Fin 2, ∀ z ∈ Ω, DifferentiableAt ℝ (F i) z)
    (hψ_diff : ∀ z ∈ Ω, DifferentiableAt ℝ ψ z)
    (hF_cont : ∀ i : Fin 2, ContinuousOn (F i) Ω)
    (hDF_cont :
      ∀ i : Fin 2,
        ContinuousOn
          (fun z : ℂ ↦ fderiv ℝ (F i) z (complexCoordinateVector i)) Ω)
    (hψ_cont : ContinuousOn ψ Ω)
    (hDψ_cont :
      ∀ i : Fin 2,
        ContinuousOn
          (fun z : ℂ ↦ fderiv ℝ ψ z (complexCoordinateVector i)) Ω) :
    ∫ z in Ω,
        (fderiv ℝ (F 0) z (1 : ℂ) +
          fderiv ℝ (F 1) z Complex.I) * ψ z =
      - ∫ z in Ω,
        ∑ i : Fin 2, F i z * fderiv ℝ ψ z (complexCoordinateVector i) := by
  rcases euclidean_component_products_integrable_of_tsupport_subset_isCompact
      Ω hΩ F ψ hψ_support hψ_compact
      hF_cont hDF_cont hψ_cont hDψ_cont with
    ⟨hDψ, hFdψ, hFψ⟩
  exact euclidean_divergence_integral_by_parts_on_open_of_component_integrable
    Ω hΩ F ψ hψ_support hF_diff hψ_diff hDψ hFdψ hFψ

/--
%%handwave
name:
  Euclidean divergence integration by parts on an open set
statement:
  On an open subset of the coordinate plane, the integral of the Euclidean
  divergence of a differentiable vector field against a compactly supported
  differentiable test function is minus the integral of the vector field
  contracted with the derivative of the test function.
proof:
  Extend the integrals to the whole coordinate plane using the compact support
  of the test function, apply the one-dimensional line-derivative
  integration-by-parts theorem to the two coordinate directions \(1\) and
  \(i\), and restrict the resulting identity back to the open set.
-/
theorem euclidean_divergence_integral_by_parts_on_open
    (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (F : Fin 2 → ℂ → ℝ) (ψ : ℂ → ℝ)
    (hψ_support : tsupport ψ ⊆ Ω)
    (hψ_compact : IsCompact (tsupport ψ))
    (hF_diff : ∀ i : Fin 2, ∀ z ∈ Ω, DifferentiableAt ℝ (F i) z)
    (hψ_diff : ∀ z ∈ Ω, DifferentiableAt ℝ ψ z)
    (hF_cont : ∀ i : Fin 2, ContinuousOn (F i) Ω)
    (hDF_cont :
      ∀ i : Fin 2,
        ContinuousOn
          (fun z : ℂ ↦ fderiv ℝ (F i) z (complexCoordinateVector i)) Ω)
    (hψ_cont : ContinuousOn ψ Ω)
    (hDψ_cont :
      ∀ i : Fin 2,
        ContinuousOn
          (fun z : ℂ ↦ fderiv ℝ ψ z (complexCoordinateVector i)) Ω) :
    ∫ z in Ω,
        (fderiv ℝ (F 0) z (1 : ℂ) +
          fderiv ℝ (F 1) z Complex.I) * ψ z =
      - ∫ z in Ω,
        ∑ i : Fin 2, F i z * fderiv ℝ ψ z (complexCoordinateVector i) := by
  exact euclidean_divergence_integral_by_parts_on_open_of_tsupport_subset_isCompact
    Ω hΩ F ψ hψ_support hψ_compact hF_diff hψ_diff
    hF_cont hDF_cont hψ_cont hDψ_cont

/--
%%handwave
name:
  Zero-extended coordinate representative
statement:
  The coordinate representative of a surface function in a chart is the
  pullback by the inverse chart on the chart image, extended by zero outside
  that image.
-/
noncomputable def surfaceChartRepresentative {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (η : X → ℝ) : ℂ → ℝ :=
  e.target.indicator (fun z : ℂ ↦ η (e.symm z))

theorem surfaceChartRepresentative_apply_of_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (η : X → ℝ) {z : ℂ}
    (hz : z ∈ e.target) :
    surfaceChartRepresentative e η z = η (e.symm z) := by
  simp [surfaceChartRepresentative, hz]

theorem surfaceChartRepresentative_apply_of_notMem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (η : X → ℝ) {z : ℂ}
    (hz : z ∉ e.target) :
    surfaceChartRepresentative e η z = 0 := by
  simp [surfaceChartRepresentative, hz]

/--
%%handwave
name:
  Zero extension agrees locally inside the chart image
statement:
  At every point of the chart image, the zero-extended coordinate
  representative agrees in a neighbourhood with the ordinary inverse-chart
  pullback.
-/
theorem surfaceChartRepresentative_eventuallyEq_raw_of_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (η : X → ℝ) {z : ℂ}
    (hz : z ∈ e.target) :
    surfaceChartRepresentative e η =ᶠ[𝓝 z]
      (fun w : ℂ ↦ η (e.symm w)) := by
  filter_upwards [e.open_target.mem_nhds hz] with w hw
  exact surfaceChartRepresentative_apply_of_mem e η hw

theorem surfaceChartRepresentative_fderiv_eq_raw_of_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (η : X → ℝ) {z : ℂ}
    (hz : z ∈ e.target) :
    fderiv ℝ (surfaceChartRepresentative e η) z =
      fderiv ℝ (fun w : ℂ ↦ η (e.symm w)) z := by
  exact Filter.EventuallyEq.fderiv_eq
    (surfaceChartRepresentative_eventuallyEq_raw_of_mem e η hz)

theorem surfaceChartRepresentative_directionalDerivative_eq_of_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (η : X → ℝ) {z : ℂ}
    (hz : z ∈ e.target) (v : ℂ) :
    fderiv ℝ (surfaceChartRepresentative e η) z v =
      surfaceFunctionChartDirectionalDerivative e η z v := by
  rw [surfaceChartRepresentative_fderiv_eq_raw_of_mem e η hz]
  rfl

theorem surfaceChartRepresentative_derivativeComponent_eq_of_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (η : X → ℝ) {z : ℂ}
    (hz : z ∈ e.target) (i : Fin 2) :
    fderiv ℝ (surfaceChartRepresentative e η) z (complexCoordinateVector i) =
      surfaceFunctionChartDerivativeComponent e η z i := by
  exact surfaceChartRepresentative_directionalDerivative_eq_of_mem e η hz _

/--
%%handwave
name:
  Zero-extended chart support lies in the coordinate image
statement:
  If the topological support of a surface function lies in a chart source,
  then the zero-extended coordinate representative has topological support in
  the chart image of that surface support.
proof:
  A nonzero point of the zero-extended representative lies in the chart image.
  Applying the inverse chart gives a point where the surface function is
  nonzero, hence a point of the surface topological support.  Taking closure
  preserves the inclusion because the image of the compact surface support is
  closed in the coordinate plane.
-/
theorem surfaceChartRepresentative_tsupport_subset_image_tsupport
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) {η : X → ℝ}
    (hη_compact : HasCompactSupportOnSurface η)
    (hη_surface_support : tsupport η ⊆ e.source) :
    tsupport (surfaceChartRepresentative e η) ⊆ e '' tsupport η := by
  have hη_ts_compact : IsCompact (tsupport η) := by
    simpa [HasCompactSupportOnSurface] using hη_compact
  have himage_compact : IsCompact (e '' tsupport η) :=
    hη_ts_compact.image_of_continuousOn
      (e.continuousOn.mono hη_surface_support)
  have himage_closed : IsClosed (e '' tsupport η) := himage_compact.isClosed
  have hsupport :
      Function.support (surfaceChartRepresentative e η) ⊆ e '' tsupport η := by
    intro z hz
    have hz_target : z ∈ e.target := by
      by_contra hz_not
      exact hz (surfaceChartRepresentative_apply_of_notMem e η hz_not)
    refine ⟨e.symm z, subset_tsupport η ?_, e.right_inv hz_target⟩
    intro hη_zero
    exact hz (by
      rw [surfaceChartRepresentative_apply_of_mem e η hz_target, hη_zero])
  rw [tsupport]
  exact closure_minimal hsupport himage_closed

/--
%%handwave
name:
  Zero-extended chart support is contained in the chart target
statement:
  If the topological support of a surface function lies in a chart source,
  then the zero-extended coordinate representative has topological support in
  the chart target.
-/
theorem surfaceChartRepresentative_tsupport_subset_target
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) {η : X → ℝ}
    (hη_compact : HasCompactSupportOnSurface η)
    (hη_surface_support : tsupport η ⊆ e.source) :
    tsupport (surfaceChartRepresentative e η) ⊆ e.target := by
  intro z hz
  rcases surfaceChartRepresentative_tsupport_subset_image_tsupport
      e hη_compact hη_surface_support hz with
    ⟨x, hx, rfl⟩
  exact e.map_source (hη_surface_support hx)

/--
%%handwave
name:
  Compact surface support gives compact zero-extended coordinate support
statement:
  If a compactly supported surface function has topological support contained
  in a chart source, then its zero-extended coordinate representative has
  compact topological support contained in the chart image.
proof:
  The coordinate support is a closed subset of the image of the compact
  surface support under the chart.  That image is compact because the chart is
  continuous on the surface support.
-/
theorem surfaceChartRepresentative_tsupport_isCompact_of_surface_tsupport_subset
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) {η : X → ℝ}
    (hη_compact : HasCompactSupportOnSurface η)
    (hη_surface_support : tsupport η ⊆ e.source) :
    IsCompact (tsupport (surfaceChartRepresentative e η)) := by
  have hη_ts_compact : IsCompact (tsupport η) := by
    simpa [HasCompactSupportOnSurface] using hη_compact
  have himage_compact : IsCompact (e '' tsupport η) :=
    hη_ts_compact.image_of_continuousOn
      (e.continuousOn.mono hη_surface_support)
  exact himage_compact.of_isClosed_subset (isClosed_tsupport _)
    (surfaceChartRepresentative_tsupport_subset_image_tsupport
      e hη_compact hη_surface_support)

/--
%%handwave
name:
  Coordinate flux integration by parts
statement:
  In one coordinate chart, the Euclidean divergence of the metric gradient
  flux integrates against a compactly supported test function as minus the
  flux contracted with the coordinate derivative of that test function.
proof:
  Apply Mathlib's Euclidean divergence theorem, equivalently the
  finite-dimensional line-derivative integration-by-parts theorem, to the two
  coordinate components of the flux.  The compact support assumption removes
  boundary terms.
-/
theorem surfaceMetricGradientFluxInChart_integral_by_parts
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_support : tsupport (fun z : ℂ ↦ η (e.symm z)) ⊆ e.target)
    (hη_compact : IsCompact (tsupport (fun z : ℂ ↦ η (e.symm z)))) :
    ∫ z in e.target,
        (fderiv ℝ (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
            z (1 : ℂ) +
          fderiv ℝ (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
            z Complex.I) * η (e.symm z) =
      - ∫ z in e.target,
        ∑ i : Fin 2,
          surfaceMetricGradientFluxInChart metric e f z i *
            surfaceFunctionChartDerivativeComponent e η z i := by
  let F : Fin 2 → ℂ → ℝ :=
    fun i z ↦ surfaceMetricGradientFluxInChart metric e f z i
  let ψ : ℂ → ℝ := fun z ↦ η (e.symm z)
  have hF_diff :
      ∀ i : Fin 2, ∀ z ∈ e.target, DifferentiableAt ℝ (F i) z := by
    intro i z hz
    exact surfaceMetricGradientFluxInChart_differentiableAt
      metric e _he f hf i z hz
  have hψ_diff : ∀ z ∈ e.target, DifferentiableAt ℝ ψ z := by
    intro z hz
    exact surfaceFunctionChartRepresentative_differentiableAt
      e _he η hη z hz
  have hF_cont : ∀ i : Fin 2, ContinuousOn (F i) e.target := by
    intro i
    simpa [F] using
      (surfaceMetricGradientFluxInChart_contDiffOn
        metric e _he f hf i).continuousOn
  have hDF_cont :
      ∀ i : Fin 2,
        ContinuousOn
          (fun z : ℂ ↦ fderiv ℝ (F i) z (complexCoordinateVector i))
          e.target := by
    intro i
    simpa [F] using
      surfaceMetricGradientFluxInChart_fderiv_apply_continuousOn
        metric e _he f hf i (complexCoordinateVector i)
  have hψ_cont : ContinuousOn ψ e.target := by
    have hη_chart : ContDiffOn ℝ ∞ ψ e.target := by
      simpa [ψ] using hη e _he
    exact hη_chart.continuousOn
  have hDψ_cont :
      ∀ i : Fin 2,
        ContinuousOn
          (fun z : ℂ ↦ fderiv ℝ ψ z (complexCoordinateVector i))
          e.target := by
    intro i
    simpa [ψ, surfaceFunctionChartDerivativeComponent,
      surfaceFunctionChartDirectionalDerivative] using
      (surfaceFunctionChartDerivativeComponent_contDiffOn
        e _he η hη i).continuousOn
  have hparts :=
    euclidean_divergence_integral_by_parts_on_open
      e.target e.open_target F ψ hη_support hη_compact hF_diff hψ_diff
      hF_cont hDF_cont hψ_cont hDψ_cont
  simpa [F, ψ, surfaceFunctionChartDerivativeComponent,
    surfaceFunctionChartDirectionalDerivative] using hparts

/--
%%handwave
name:
  Local coordinate flux integration by parts
statement:
  In one surface coordinate chart, if the coordinate representative of \(f\)
  is smooth on an open coordinate set and a scalar test is compactly
  supported in that set, then the metric gradient flux satisfies the
  Euclidean divergence integration-by-parts identity on that set.
proof:
  Local smoothness of the coordinate representative gives local smoothness,
  differentiability, and continuity of the metric flux and its coordinate
  derivatives.  The compact support and smoothness hypotheses for the test
  give the remaining assumptions of the Euclidean divergence
  integration-by-parts theorem on open subsets of the coordinate plane.
-/
theorem surfaceMetricGradientFluxInChart_integral_by_parts_of_local_contDiffOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f : X → ℝ) {S : Set ℂ} (hS_open : IsOpen S) (hS_subset : S ⊆ e.target)
    (hf : ContDiffOn ℝ ∞ (fun w : ℂ ↦ f (e.symm w)) S)
    (ψ : ℂ → ℝ)
    (hψ_support : tsupport ψ ⊆ S)
    (hψ_compact : IsCompact (tsupport ψ))
    (hψ_diff : ∀ z ∈ S, DifferentiableAt ℝ ψ z)
    (hψ_cont : ContinuousOn ψ S)
    (hDψ_cont :
      ∀ i : Fin 2,
        ContinuousOn
          (fun z : ℂ ↦ fderiv ℝ ψ z (complexCoordinateVector i)) S) :
    ∫ z in S,
        (fderiv ℝ (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
            z (1 : ℂ) +
          fderiv ℝ (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
            z Complex.I) * ψ z =
      - ∫ z in S,
        ∑ i : Fin 2,
          surfaceMetricGradientFluxInChart metric e f z i *
            fderiv ℝ ψ z (complexCoordinateVector i) := by
  let F : Fin 2 → ℂ → ℝ :=
    fun i z ↦ surfaceMetricGradientFluxInChart metric e f z i
  have hflux :
      ∀ i : Fin 2,
        ContDiffOn ℝ ∞
          (fun z : ℂ ↦ surfaceMetricGradientFluxInChart metric e f z i) S := by
    intro i
    exact
      surfaceMetricGradientFluxInChart_contDiffOn_of_local_contDiffOn
        metric e _he f hS_open hS_subset hf i
  have hF_diff :
      ∀ i : Fin 2, ∀ z ∈ S, DifferentiableAt ℝ (F i) z := by
    intro i z hz
    exact ((hflux i).contDiffAt (hS_open.mem_nhds hz)).differentiableAt
      (by simp)
  have hF_cont : ∀ i : Fin 2, ContinuousOn (F i) S := by
    intro i
    simpa [F] using (hflux i).continuousOn
  have hDF_cont :
      ∀ i : Fin 2,
        ContinuousOn
          (fun z : ℂ ↦ fderiv ℝ (F i) z (complexCoordinateVector i)) S := by
    intro i
    have hderiv :
        ContDiffOn ℝ ∞
          (fderiv ℝ
            (fun z : ℂ ↦ surfaceMetricGradientFluxInChart metric e f z i))
          S :=
      (hflux i).fderiv_of_isOpen hS_open (by simp)
    simpa [F] using
      (hderiv.clm_apply (contDiffOn_const (c := complexCoordinateVector i))).continuousOn
  have hparts :=
    euclidean_divergence_integral_by_parts_on_open
      S hS_open F ψ hψ_support hψ_compact hF_diff hψ_diff
      hF_cont hDF_cont hψ_cont hDψ_cont
  simpa [F] using hparts

/--
%%handwave
name:
  Coordinate flux integration by parts from surface support
statement:
  If a smooth compactly supported test function has surface support contained
  in a chart source, then the coordinate flux integration-by-parts identity
  holds in that chart.
proof:
  Apply the Euclidean compact-support theorem to the zero-extended coordinate
  representative.  Inside the chart image this representative agrees locally
  with the ordinary inverse-chart pullback, so its coordinate derivatives are
  the usual derivative components of the surface test function.
-/
theorem surfaceMetricGradientFluxInChart_integral_by_parts_of_surface_tsupport_subset
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_compact : HasCompactSupportOnSurface η)
    (hη_surface_support : tsupport η ⊆ e.source) :
    ∫ z in e.target,
        (fderiv ℝ (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
            z (1 : ℂ) +
          fderiv ℝ (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
            z Complex.I) * η (e.symm z) =
      - ∫ z in e.target,
        ∑ i : Fin 2,
          surfaceMetricGradientFluxInChart metric e f z i *
            surfaceFunctionChartDerivativeComponent e η z i := by
  let F : Fin 2 → ℂ → ℝ :=
    fun i z ↦ surfaceMetricGradientFluxInChart metric e f z i
  let ψ : ℂ → ℝ := surfaceChartRepresentative e η
  have hψ_support : tsupport ψ ⊆ e.target := by
    simpa [ψ] using
      surfaceChartRepresentative_tsupport_subset_target
        e hη_compact hη_surface_support
  have hψ_compact : IsCompact (tsupport ψ) := by
    simpa [ψ] using
      surfaceChartRepresentative_tsupport_isCompact_of_surface_tsupport_subset
        e hη_compact hη_surface_support
  have hF_diff :
      ∀ i : Fin 2, ∀ z ∈ e.target, DifferentiableAt ℝ (F i) z := by
    intro i z hz
    exact surfaceMetricGradientFluxInChart_differentiableAt
      metric e _he f hf i z hz
  have hψ_diff : ∀ z ∈ e.target, DifferentiableAt ℝ ψ z := by
    intro z hz
    have hraw :
        DifferentiableAt ℝ (fun w : ℂ ↦ η (e.symm w)) z :=
      surfaceFunctionChartRepresentative_differentiableAt
        e _he η hη z hz
    exact hraw.congr_of_eventuallyEq
      (surfaceChartRepresentative_eventuallyEq_raw_of_mem e η hz)
  have hF_cont : ∀ i : Fin 2, ContinuousOn (F i) e.target := by
    intro i
    simpa [F] using
      (surfaceMetricGradientFluxInChart_contDiffOn
        metric e _he f hf i).continuousOn
  have hDF_cont :
      ∀ i : Fin 2,
        ContinuousOn
          (fun z : ℂ ↦ fderiv ℝ (F i) z (complexCoordinateVector i))
          e.target := by
    intro i
    simpa [F] using
      surfaceMetricGradientFluxInChart_fderiv_apply_continuousOn
        metric e _he f hf i (complexCoordinateVector i)
  have hψ_cont : ContinuousOn ψ e.target := by
    have hraw : ContinuousOn (fun z : ℂ ↦ η (e.symm z)) e.target := by
      have hη_chart : ContDiffOn ℝ ∞ (fun z : ℂ ↦ η (e.symm z)) e.target := by
        simpa using hη e _he
      exact hη_chart.continuousOn
    exact hraw.congr fun z hz ↦
      surfaceChartRepresentative_apply_of_mem e η hz
  have hDψ_cont :
      ∀ i : Fin 2,
        ContinuousOn
          (fun z : ℂ ↦ fderiv ℝ ψ z (complexCoordinateVector i))
          e.target := by
    intro i
    have hraw :
        ContinuousOn
          (fun z : ℂ ↦
            fderiv ℝ (fun w : ℂ ↦ η (e.symm w)) z
              (complexCoordinateVector i)) e.target := by
      simpa [surfaceFunctionChartDerivativeComponent,
        surfaceFunctionChartDirectionalDerivative] using
        (surfaceFunctionChartDerivativeComponent_contDiffOn
          e _he η hη i).continuousOn
    exact hraw.congr fun z hz ↦ by
      rw [surfaceChartRepresentative_fderiv_eq_raw_of_mem e η hz]
  have hparts :=
    euclidean_divergence_integral_by_parts_on_open
      e.target e.open_target F ψ hψ_support hψ_compact hF_diff hψ_diff
      hF_cont hDF_cont hψ_cont hDψ_cont
  have hleft_eq :
      ∫ z in e.target,
          (fderiv ℝ (F 0) z (1 : ℂ) +
            fderiv ℝ (F 1) z Complex.I) * ψ z =
        ∫ z in e.target,
          (fderiv ℝ (F 0) z (1 : ℂ) +
            fderiv ℝ (F 1) z Complex.I) * η (e.symm z) := by
    refine setIntegral_congr_fun e.open_target.measurableSet ?_
    intro z hz
    change
      ((fderiv ℝ (F 0) z (1 : ℂ) +
          fderiv ℝ (F 1) z Complex.I) * ψ z) =
        ((fderiv ℝ (F 0) z (1 : ℂ) +
          fderiv ℝ (F 1) z Complex.I) * η (e.symm z))
    rw [show ψ z = η (e.symm z) from
      surfaceChartRepresentative_apply_of_mem e η hz]
  have hright_eq :
      ∫ z in e.target,
          ∑ i : Fin 2, F i z * fderiv ℝ ψ z (complexCoordinateVector i) =
        ∫ z in e.target,
          ∑ i : Fin 2,
            F i z * surfaceFunctionChartDerivativeComponent e η z i := by
    refine setIntegral_congr_fun e.open_target.measurableSet ?_
    intro z hz
    change
      (∑ i : Fin 2, F i z * fderiv ℝ ψ z (complexCoordinateVector i)) =
        ∑ i : Fin 2,
          F i z * surfaceFunctionChartDerivativeComponent e η z i
    apply Finset.sum_congr rfl
    intro i _hi
    rw [show fderiv ℝ ψ z (complexCoordinateVector i) =
        surfaceFunctionChartDerivativeComponent e η z i from
      surfaceChartRepresentative_derivativeComponent_eq_of_mem e η hz i]
  change
    ∫ z in e.target,
        (fderiv ℝ (F 0) z (1 : ℂ) +
          fderiv ℝ (F 1) z Complex.I) * η (e.symm z) =
      - ∫ z in e.target,
        ∑ i : Fin 2,
          F i z * surfaceFunctionChartDerivativeComponent e η z i
  rw [← hleft_eq, ← hright_eq]
  exact hparts

/--
%%handwave
name:
  Differential components in coordinates
statement:
  The surface differential applied to a coordinate tangent vector is the
  corresponding directional derivative of the coordinate representative.
proof:
  This is the chain rule for the coordinate representative
  \(f\circ e^{-1}\), using that the stored differential is the manifold
  derivative of \(f\).
-/
theorem surfaceDifferential_apply_chartTangentMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ f : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) f →
        IsSurfaceDifferential f (gradient f))
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f : X → ℝ) (hf : IsSmoothOnSurface (Set.univ : Set X) f) :
    ∀ z ∈ e.target, ∀ v : ℂ,
      gradient f (e.symm z) (surfaceChartTangentMap e z v) =
        surfaceFunctionChartDirectionalDerivative e f z v := by
  intro z hz v
  letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
  have hdf :
      HasMFDerivAt SurfaceRealModel 𝓘(ℝ, ℝ) f (e.symm z)
        (gradient f (e.symm z)) :=
    gradient_is_differential f hf (e.symm z)
  have hgrad :
      mfderiv SurfaceRealModel 𝓘(ℝ, ℝ) f (e.symm z) =
        gradient f (e.symm z) :=
    hdf.mfderiv
  have hsymm :
      MDifferentiableWithinAt SurfaceRealModel SurfaceRealModel e.symm e.target z :=
    mdifferentiableOn_atlas_symm (I := SurfaceRealModel) _he z hz
  have huniq : UniqueMDiffWithinAt SurfaceRealModel e.target z := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact e.open_target.uniqueDiffWithinAt hz
  have hchain :
      mfderivWithin SurfaceRealModel 𝓘(ℝ, ℝ) (fun w : ℂ ↦ f (e.symm w)) e.target z =
        (mfderiv SurfaceRealModel 𝓘(ℝ, ℝ) f (e.symm z)).comp
          (mfderivWithin SurfaceRealModel SurfaceRealModel e.symm e.target z) := by
    simpa [Function.comp_def] using
      (mfderiv_comp_mfderivWithin
        (I := SurfaceRealModel) (I' := SurfaceRealModel) (I'' := 𝓘(ℝ, ℝ))
        (f := e.symm) (g := f) (s := e.target) (x := z)
        hdf.mdifferentiableAt hsymm huniq)
  have htan :
      mfderivWithin SurfaceRealModel SurfaceRealModel e.symm e.target z =
        surfaceChartTangentMap e z := by
    simp [surfaceChartTangentMap, mfderivWithin, writtenInExtChartAt, SurfaceRealModel,
      hsymm]
    rfl
  have hwithin :
      fderivWithin ℝ (fun w : ℂ ↦ f (e.symm w)) e.target z =
        fderiv ℝ (fun w : ℂ ↦ f (e.symm w)) z :=
    fderivWithin_of_isOpen e.open_target hz
  rw [← hgrad, surfaceFunctionChartDirectionalDerivative, ← hwithin, ← htan]
  change
    ((mfderiv SurfaceRealModel 𝓘(ℝ, ℝ) f (e.symm z)).comp
        (mfderivWithin SurfaceRealModel SurfaceRealModel e.symm e.target z)) v =
      (fderivWithin ℝ (fun w : ℂ ↦ f (e.symm w)) e.target z) v
  rw [← hchain]
  simp [SurfaceRealModel]
  rfl

private theorem inverseGram_two_by_two_pairing
    {g₁₁ g₁₂ g₂₁ g₂₂ p q r s α β : ℝ}
    (hp : p = α * g₁₁ + β * g₂₁)
    (hq : q = α * g₁₂ + β * g₂₂)
    (hdet : g₁₁ * g₂₂ - g₁₂ * g₂₁ ≠ 0) :
    α * r + β * s =
      (g₁₁ * g₂₂ - g₁₂ * g₂₁)⁻¹ * g₂₂ * p * r +
        (-(g₁₁ * g₂₂ - g₁₂ * g₂₁)⁻¹ * g₁₂) * p * s +
        (-(g₁₁ * g₂₂ - g₁₂ * g₂₁)⁻¹ * g₂₁) * q * r +
        (g₁₁ * g₂₂ - g₁₂ * g₂₁)⁻¹ * g₁₁ * q * s := by
  subst p
  subst q
  field_simp [hdet]
  ring

/--
%%handwave
name:
  Metric-dual covector pairing in coordinates
statement:
  The metric-dual pairing of two covectors is the inverse-Gram contraction
  of their components on the coordinate tangent frame.
proof:
  The metric-dual vector of the first covector solves the \(2\times2\) Gram
  system in the coordinate tangent basis.  Since the coordinate tangent map
  is invertible, this basis spans the tangent plane; solving the system gives
  the inverse Gram coefficients.
-/
theorem surfaceMetricCotangentPairingInChart_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (ξ η : ℂ →L[ℝ] ℝ) :
    ∀ z ∈ e.target,
      gradientInner (e.symm z) ξ η =
        surfaceMetricCoordinateCotangentPairingInChart metric e z ξ η := by
  intro z hz
  letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
  let x : X := e.symm z
  let A : ℂ →L[ℝ] ℂ := surfaceChartTangentMap e z
  let b : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    metric.toContMDiffRiemannianMetric.inner x
  let v₁ : ℂ := A (1 : ℂ)
  let v₂ : ℂ := A Complex.I
  let g₁₁ : ℝ := b v₁ v₁
  let g₁₂ : ℝ := b v₁ v₂
  let g₂₁ : ℝ := b v₂ v₁
  let g₂₂ : ℝ := b v₂ v₂
  let D : ℝ := g₁₁ * g₂₂ - g₁₂ * g₂₁
  rcases gradientInner_isMetricDual x ξ with ⟨vξ, hvξ, _hvξ_unique⟩
  have hpair : gradientInner x ξ η = η vξ := hvξ.2 η
  have hAinv : A.IsInvertible :=
    surfaceChartTangentMap_isInvertible X metric e _he z hz
  let u : ℂ := A.inverse vξ
  have hu_decomp : u = u.re • (1 : ℂ) + u.im • Complex.I := by
    rw [← Complex.re_add_im u]
    simp [Complex.real_smul]
  have hA_decomp :
      A u = u.re • A (1 : ℂ) + u.im • A Complex.I := by
    calc
      A u = A (u.re • (1 : ℂ) + u.im • Complex.I) := congr_arg A hu_decomp
      _ = u.re • A (1 : ℂ) + u.im • A Complex.I := by
        rw [A.map_add, map_smulₛₗ, map_smulₛₗ]
        simp only [RingHom.id_apply]
  have hvξ_eq : vξ = u.re • v₁ + u.im • v₂ := by
    rw [← hAinv.self_apply_inverse vξ]
    change A u = u.re • v₁ + u.im • v₂
    simpa [v₁, v₂] using hA_decomp
  have hηv :
      η vξ = u.re * η v₁ + u.im * η v₂ := by
    calc
      η vξ = η (u.re • v₁ + u.im • v₂) := by
        rw [hvξ_eq]
      _ = u.re * η v₁ + u.im * η v₂ := by
        rw [η.map_add, map_smulₛₗ, map_smulₛₗ]
        simp [smul_eq_mul]
  have hξ₁ :
      ξ v₁ = u.re * g₁₁ + u.im * g₂₁ := by
    calc
      ξ v₁ = b vξ v₁ := hvξ.1 v₁
      _ = b (u.re • v₁ + u.im • v₂) v₁ := by
        rw [hvξ_eq]
      _ = u.re * g₁₁ + u.im * g₂₁ := by
        rw [b.map_add, map_smulₛₗ, map_smulₛₗ]
        simp [g₁₁, g₂₁, smul_eq_mul]
  have hξ₂ :
      ξ v₂ = u.re * g₁₂ + u.im * g₂₂ := by
    calc
      ξ v₂ = b vξ v₂ := hvξ.1 v₂
      _ = b (u.re • v₁ + u.im • v₂) v₂ := by
        rw [hvξ_eq]
      _ = u.re * g₁₂ + u.im * g₂₂ := by
        rw [b.map_add, map_smulₛₗ, map_smulₛₗ]
        simp [g₁₂, g₂₂, smul_eq_mul]
  have hdet :
      surfaceMetricGramDetInChart metric e z ≠ 0 :=
    ne_of_gt (surfaceMetricGramDetInChart_pos X metric e _he z hz)
  have hgram : surfaceMetricGramDetInChart metric e z = D := by
    simp [surfaceMetricGramDetInChart, D, A, b, x, v₁, v₂, g₁₁, g₁₂,
      g₂₁, g₂₂]
    rfl
  have hD : D ≠ 0 := by
    simpa [hgram] using hdet
  calc
    gradientInner (e.symm z) ξ η = η vξ := by
      simpa [x] using hpair
    _ = u.re * η v₁ + u.im * η v₂ := hηv
    _ =
        D⁻¹ * g₂₂ * ξ v₁ * η v₁ +
          (-D⁻¹ * g₁₂) * ξ v₁ * η v₂ +
          (-D⁻¹ * g₂₁) * ξ v₂ * η v₁ +
          D⁻¹ * g₁₁ * ξ v₂ * η v₂ := by
      simpa [D] using
        (inverseGram_two_by_two_pairing
          (g₁₁ := g₁₁) (g₁₂ := g₁₂) (g₂₁ := g₂₁) (g₂₂ := g₂₂)
          (p := ξ v₁) (q := ξ v₂) (r := η v₁) (s := η v₂)
          (α := u.re) (β := u.im) hξ₁ hξ₂ hD)
    _ = surfaceMetricCoordinateCotangentPairingInChart metric e z ξ η := by
      simp [surfaceMetricCoordinateCotangentPairingInChart,
        surfaceMetricInverseGramCoeffInChart,
        complexCoordinateVector, Fin.sum_univ_two, A, b, x, v₁, v₂, g₁₁,
        g₁₂, g₂₁, g₂₂]
      rw [hgram]
      abel

/--
%%handwave
name:
  Metric-dual pairing has the coordinate inverse-metric formula
statement:
  In a surface coordinate chart, the metric-dual cotangent pairing of the
  differentials of two smooth functions is
  \[
    \sum_{i,j} g^{ij}\partial_i f\,\partial_j h .
  \]
proof:
  Use that [the surface differential applied to a coordinate tangent vector
  is the corresponding directional derivative of the coordinate
  representative](lean:JJMath.Uniformization.surfaceDifferential_apply_chartTangentMap).
  Then apply the pointwise fact that [the metric-dual pairing of two
  covectors is the inverse-Gram contraction of their coordinate
  components](lean:JJMath.Uniformization.surfaceMetricCotangentPairingInChart_eq).
-/
theorem surfaceMetricGradientPairingInChart_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ f : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) f →
        IsSurfaceDifferential f (gradient f))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f h : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hh : IsSmoothOnSurface (Set.univ : Set X) h) :
    ∀ z ∈ e.target,
      gradientInner (e.symm z) (gradient f (e.symm z)) (gradient h (e.symm z)) =
        surfaceMetricCoordinateGradientPairingInChart metric e f h z := by
  intro z hz
  have hpair :=
    surfaceMetricCotangentPairingInChart_eq metric gradientInner
      gradientInner_isMetricDual e _he
      (gradient f (e.symm z)) (gradient h (e.symm z)) z hz
  have hf_comp :=
    surfaceDifferential_apply_chartTangentMap metric gradient
      gradient_is_differential e _he f hf z hz
  have hh_comp :=
    surfaceDifferential_apply_chartTangentMap metric gradient
      gradient_is_differential e _he h hh z hz
  calc
    gradientInner (e.symm z) (gradient f (e.symm z)) (gradient h (e.symm z))
        = surfaceMetricCoordinateCotangentPairingInChart metric e z
            (gradient f (e.symm z)) (gradient h (e.symm z)) := hpair
    _ = surfaceMetricCoordinateGradientPairingInChart metric e f h z := by
      simp [surfaceMetricCoordinateCotangentPairingInChart,
        surfaceMetricCoordinateGradientPairingInChart,
        surfaceFunctionChartDerivativeComponent, hf_comp, hh_comp]

/--
%%handwave
name:
  Coordinate divergence-form integration by parts
statement:
  On one surface coordinate chart, for a test function compactly supported in
  the chart, the divergence-form expression satisfies
  \[
    \int \Delta_g f\,\eta\,\rho\,dz
      =
    -\int g^{ij}\partial_i f\,\partial_j\eta\,\rho\,dz .
  \]
proof:
  First [multiplying the divergence-form Laplacian by the Riemannian volume
  density cancels the prefactor
  \(\rho^{-1}\)](lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltramiInChart_mul_volumeDensity).
  The right-hand side becomes the
  [flux contraction with the coordinate derivative of the test
  function](lean:JJMath.Uniformization.surfaceMetricCoordinateGradientPairingInChart_mul_volumeDensity_eq_flux).
  The remaining step is [the Euclidean flux integration-by-parts
  identity](lean:JJMath.Uniformization.surfaceMetricGradientFluxInChart_integral_by_parts).
-/
theorem surfaceDivergenceFormLaplaceBeltramiInChart_integral_by_parts
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_support : tsupport (fun z : ℂ ↦ η (e.symm z)) ⊆ e.target)
    (hη_compact : IsCompact (tsupport (fun z : ℂ ↦ η (e.symm z)))) :
    ∫ z in e.target,
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
          η (e.symm z) * surfaceMetricVolumeDensityInChart metric e z =
      - ∫ z in e.target,
        surfaceMetricCoordinateGradientPairingInChart metric e f η z *
          surfaceMetricVolumeDensityInChart metric e z := by
  have hleft_eq :
      ∫ z in e.target,
          surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
            η (e.symm z) * surfaceMetricVolumeDensityInChart metric e z =
        ∫ z in e.target,
          (fderiv ℝ
              (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
              z (1 : ℂ) +
            fderiv ℝ
              (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
              z Complex.I) * η (e.symm z) := by
    refine setIntegral_congr_fun e.open_target.measurableSet ?_
    intro z hz
    exact surfaceDivergenceFormLaplaceBeltramiInChart_mul_volumeDensity
      metric e _he f η z hz
  have hright_eq :
      ∫ z in e.target,
          surfaceMetricCoordinateGradientPairingInChart metric e f η z *
            surfaceMetricVolumeDensityInChart metric e z =
        ∫ z in e.target,
          ∑ i : Fin 2,
            surfaceMetricGradientFluxInChart metric e f z i *
              surfaceFunctionChartDerivativeComponent e η z i := by
    refine setIntegral_congr_fun e.open_target.measurableSet ?_
    intro z _hz
    exact surfaceMetricCoordinateGradientPairingInChart_mul_volumeDensity_eq_flux
      metric e f η z
  rw [hleft_eq, hright_eq]
  exact surfaceMetricGradientFluxInChart_integral_by_parts
    metric e _he f η hf hη hη_support hη_compact

/--
%%handwave
name:
  Coordinate divergence-form integration by parts for compactly supported tests
statement:
  On one surface coordinate chart, if the coordinate test function has compact
  support inside the chart target, then the divergence-form
  Laplace-Beltrami expression satisfies the chart weak identity.
proof:
  The density cancellation and flux-contraction identities reduce the claim
  to the compactly supported coordinate flux integration-by-parts theorem.
-/
theorem surfaceDivergenceFormLaplaceBeltramiInChart_integral_by_parts_of_chart_tsupport_isCompact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_support : tsupport (fun z : ℂ ↦ η (e.symm z)) ⊆ e.target)
    (hη_compact : IsCompact (tsupport (fun z : ℂ ↦ η (e.symm z)))) :
    ∫ z in e.target,
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
          η (e.symm z) * surfaceMetricVolumeDensityInChart metric e z =
      - ∫ z in e.target,
        surfaceMetricCoordinateGradientPairingInChart metric e f η z *
          surfaceMetricVolumeDensityInChart metric e z := by
  exact surfaceDivergenceFormLaplaceBeltramiInChart_integral_by_parts
    metric e _he f η hf hη hη_support hη_compact

/--
%%handwave
name:
  Coordinate divergence-form integration by parts from surface support
statement:
  On one surface coordinate chart, if a smooth compactly supported test
  function has surface support contained in the chart source, then the
  divergence-form Laplace-Beltrami expression satisfies the chart weak
  identity.
proof:
  The density cancellation and flux-contraction identities reduce the claim
  to the
  [coordinate flux integration-by-parts identity obtained from surface
  support]
  (lean:JJMath.Uniformization.surfaceMetricGradientFluxInChart_integral_by_parts_of_surface_tsupport_subset).
-/
theorem surfaceDivergenceFormLaplaceBeltramiInChart_integral_by_parts_of_surface_tsupport_subset
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_compact : HasCompactSupportOnSurface η)
    (hη_surface_support : tsupport η ⊆ e.source) :
    ∫ z in e.target,
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
          η (e.symm z) * surfaceMetricVolumeDensityInChart metric e z =
      - ∫ z in e.target,
        surfaceMetricCoordinateGradientPairingInChart metric e f η z *
          surfaceMetricVolumeDensityInChart metric e z := by
  have hleft_eq :
      ∫ z in e.target,
          surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
            η (e.symm z) * surfaceMetricVolumeDensityInChart metric e z =
        ∫ z in e.target,
          (fderiv ℝ
              (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
              z (1 : ℂ) +
            fderiv ℝ
              (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
              z Complex.I) * η (e.symm z) := by
    refine setIntegral_congr_fun e.open_target.measurableSet ?_
    intro z hz
    exact surfaceDivergenceFormLaplaceBeltramiInChart_mul_volumeDensity
      metric e _he f η z hz
  have hright_eq :
      ∫ z in e.target,
          surfaceMetricCoordinateGradientPairingInChart metric e f η z *
            surfaceMetricVolumeDensityInChart metric e z =
        ∫ z in e.target,
          ∑ i : Fin 2,
            surfaceMetricGradientFluxInChart metric e f z i *
              surfaceFunctionChartDerivativeComponent e η z i := by
    refine setIntegral_congr_fun e.open_target.measurableSet ?_
    intro z _hz
    exact surfaceMetricCoordinateGradientPairingInChart_mul_volumeDensity_eq_flux
      metric e f η z
  rw [hleft_eq, hright_eq]
  exact surfaceMetricGradientFluxInChart_integral_by_parts_of_surface_tsupport_subset
    metric e _he f η hf hη hη_compact hη_surface_support

/--
%%handwave
name:
  Source integrability changes variables to coordinate volume
statement:
  If a source integrand agrees pointwise with the pullback of a coordinate
  integrand, then global source integrability transfers to integrability
  against the coordinate Riemannian volume measure.
proof:
  The restricted surface volume pushes forward under the chart to the
  coordinate Riemannian volume measure.  The pointwise equality identifies the
  pullback of the coordinate integrand with the source integrand on the chart
  source, so the standard integrability theorem for map measures applies.
-/
theorem riemannianVolume_source_integrable_chartMeasure_of_pointwise
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    {φ : X → ℝ} {ψ : ℂ → ℝ}
    (hsource_null :
      NullMeasurableSet e.source measureGeometry.volume)
    (he_aemeas :
      AEMeasurable e (measureGeometry.volume.restrict e.source))
    (hψ_aemeas :
      AEStronglyMeasurable ψ (riemannianVolumeChartMeasure metric e))
    (hpoint : ∀ x ∈ e.source, φ x = ψ (e x))
    (hφ_int : Integrable φ (measureGeometry.volume.restrict e.source)) :
    Integrable ψ (riemannianVolumeChartMeasure metric e) := by
  have hmap :
      Measure.map e (measureGeometry.volume.restrict e.source) =
        riemannianVolumeChartMeasure metric e :=
    measureGeometry.volume_isRiemannian.2 e _he
  have hψ_map :
      AEStronglyMeasurable ψ
        (Measure.map e (measureGeometry.volume.restrict e.source)) := by
    simpa [hmap] using hψ_aemeas
  have hpull_eq :
      (fun x ↦ ψ (e x)) =ᵐ[measureGeometry.volume.restrict e.source] φ := by
    filter_upwards [ae_restrict_mem₀ hsource_null] with x hx
    exact (hpoint x hx).symm
  have hpull_int :
      Integrable (fun x ↦ ψ (e x))
        (measureGeometry.volume.restrict e.source) :=
    hφ_int.congr hpull_eq.symm
  have hψ_map_int :
      Integrable ψ (Measure.map e (measureGeometry.volume.restrict e.source)) :=
    (integrable_map_measure hψ_map he_aemeas).2 hpull_int
  simpa [hmap] using hψ_map_int

/--
%%handwave
name:
  Coordinate volume integrability changes variables to a chart source
statement:
  If a coordinate integrand is integrable against the coordinate Riemannian
  volume measure, then its pullback is integrable over the corresponding
  chart source.
proof:
  The coordinate Riemannian volume measure is the pushforward of the
  restricted surface volume measure.  The map-measure integrability theorem
  transfers integrability to the pullback, and the pointwise identity replaces
  the pullback by the surface integrand on the chart source.
-/
theorem riemannianVolume_source_integrable_of_chartMeasure_pointwise
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    {φ : X → ℝ} {ψ : ℂ → ℝ}
    (hsource_null :
      NullMeasurableSet e.source measureGeometry.volume)
    (he_aemeas :
      AEMeasurable e (measureGeometry.volume.restrict e.source))
    (hψ_aemeas :
      AEStronglyMeasurable ψ (riemannianVolumeChartMeasure metric e))
    (hpoint : ∀ x ∈ e.source, φ x = ψ (e x))
    (hψ_int : Integrable ψ (riemannianVolumeChartMeasure metric e)) :
    Integrable φ (measureGeometry.volume.restrict e.source) := by
  have hmap :
      Measure.map e (measureGeometry.volume.restrict e.source) =
        riemannianVolumeChartMeasure metric e :=
    measureGeometry.volume_isRiemannian.2 e _he
  have hψ_map :
      AEStronglyMeasurable ψ
        (Measure.map e (measureGeometry.volume.restrict e.source)) := by
    simpa [hmap] using hψ_aemeas
  have hψ_map_int :
      Integrable ψ (Measure.map e (measureGeometry.volume.restrict e.source)) := by
    simpa [hmap] using hψ_int
  have hpull_int :
      Integrable (fun x ↦ ψ (e x))
        (measureGeometry.volume.restrict e.source) :=
    (integrable_map_measure hψ_map he_aemeas).1 hψ_map_int
  have hpull_eq :
      (fun x ↦ ψ (e x)) =ᵐ[measureGeometry.volume.restrict e.source] φ := by
    filter_upwards [ae_restrict_mem₀ hsource_null] with x hx
    exact (hpoint x hx).symm
  exact hpull_int.congr hpull_eq

/--
%%handwave
name:
  Coordinate volume integrability is density-weighted integrability
statement:
  Integrability against the coordinate Riemannian volume measure implies
  integrability of the density-weighted function over the chart image with
  respect to Lebesgue measure.
proof:
  The coordinate volume measure is Lebesgue measure restricted to the chart
  image with density \(\rho\).  The usual with-density integrability theorem
  converts integrability against this measure into integrability of
  \(\rho\psi\) against the restricted Lebesgue measure.
-/
theorem riemannianVolumeChartMeasure_integrableOn_density {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (ψ : ℂ → ℝ)
    (hψ : Integrable ψ (riemannianVolumeChartMeasure g e)) :
    IntegrableOn
      (fun z : ℂ ↦ ψ z * surfaceMetricVolumeDensityInChart g e z)
      e.target := by
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
  have hψ_density :
      Integrable (fun z : ℂ ↦ (δ z).toReal • ψ z)
        (MeasureTheory.volume.restrict e.target) := by
    rw [riemannianVolumeChartMeasure] at hψ
    exact (integrable_withDensity_iff_integrable_smul₀'
      hδ_aemeas hδ_lt_top).1 hψ
  refine hψ_density.congr ?_
  filter_upwards [ae_restrict_mem e.open_target.measurableSet] with z hz
  have hρ_nonneg : 0 ≤ ρ z :=
    le_of_lt ((surfaceMetricVolumeDensityInChart_smooth_positive X g e _he).2 z hz)
  simp [δ, ρ, ENNReal.toReal_ofReal hρ_nonneg, smul_eq_mul, mul_comm]

/--
%%handwave
name:
  Left weak integral localizes to the chart source
statement:
  If the test function is supported in a coordinate source, then the global
  integral of \(\Delta_g f\,\eta\) is already the integral over that source.
proof:
  The support of the product is contained in the support of \(\eta\), and the
  topological support of \(\eta\) is contained in the chart source.  Thus
  [support localizes integrals]
  (lean:JJMath.Uniformization.integral_eq_setIntegral_of_tsupport_subset).
-/
theorem surfaceDivergenceFormLaplaceBeltrami_left_integral_eq_source
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (e : OpenPartialHomeomorph X ℂ)
    (f η : X → ℝ)
    (hη_surface_support : tsupport η ⊆ e.source) :
    ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * η x
        ∂measureGeometry.volume =
      ∫ x in e.source,
        surfaceDivergenceFormLaplaceBeltrami metric f x * η x
        ∂measureGeometry.volume := by
  exact integral_eq_setIntegral_of_tsupport_subset
    ((tsupport_mul_subset_right).trans hη_surface_support)

/--
%%handwave
name:
  Source integral changes variables to coordinate volume
statement:
  If a source integrand agrees pointwise with the pullback of a coordinate
  integrand, then its integral over the chart source is the coordinate
  integral against the coordinate Riemannian volume measure.
proof:
  Use the Riemannian-volume compatibility to identify the pushforward of the
  restricted surface volume measure with the coordinate volume measure.  Then
  apply the standard integral formula for a measurable pushforward.
-/
theorem riemannianVolume_source_integral_eq_chartMeasure_of_pointwise
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    {φ : X → ℝ} {ψ : ℂ → ℝ}
    (hsource_null :
      NullMeasurableSet e.source measureGeometry.volume)
    (he_aemeas :
      AEMeasurable e (measureGeometry.volume.restrict e.source))
    (hψ_aemeas :
      AEStronglyMeasurable ψ (riemannianVolumeChartMeasure metric e))
    (hpoint : ∀ x ∈ e.source, φ x = ψ (e x)) :
    ∫ x in e.source, φ x ∂measureGeometry.volume =
      ∫ z, ψ z ∂riemannianVolumeChartMeasure metric e := by
  have hmap :
      Measure.map e (measureGeometry.volume.restrict e.source) =
        riemannianVolumeChartMeasure metric e :=
    measureGeometry.volume_isRiemannian.2 e _he
  have hψ_map :
      AEStronglyMeasurable ψ
        (Measure.map e (measureGeometry.volume.restrict e.source)) := by
    simpa [hmap] using hψ_aemeas
  have hpull_eq :
      (fun x ↦ ψ (e x)) =ᵐ[measureGeometry.volume.restrict e.source] φ := by
    filter_upwards [ae_restrict_mem₀ hsource_null] with x hx
    exact (hpoint x hx).symm
  calc
    ∫ x in e.source, φ x ∂measureGeometry.volume =
        ∫ x, φ x ∂measureGeometry.volume.restrict e.source := rfl
    _ = ∫ x, ψ (e x) ∂measureGeometry.volume.restrict e.source :=
        (integral_congr_ae hpull_eq.symm)
    _ = ∫ z, ψ z
          ∂Measure.map e (measureGeometry.volume.restrict e.source) := by
        exact (integral_map he_aemeas hψ_map).symm
    _ = ∫ z, ψ z ∂riemannianVolumeChartMeasure metric e := by
        rw [hmap]

/--
%%handwave
name:
  Chart sources are null-measurable for surface volume
statement:
  The source of a coordinate chart is null-measurable for the surface volume
  measure.
proof:
  The volume measure is a Borel surface measure and chart sources are open.
-/
theorem surfaceChart_source_nullMeasurable_volume
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) :
    NullMeasurableSet e.source measureGeometry.volume := by
  letI : OpensMeasurableSpace X := measureGeometry.opensMeasurable
  exact e.open_source.measurableSet.nullMeasurableSet

/--
%%handwave
name:
  Surface charts are measurable for the restricted volume
statement:
  A coordinate chart is almost everywhere measurable with respect to the
  surface volume measure restricted to its source.
proof:
  The surface measure is Borel in coordinates and the chart is continuous on
  its open source.
-/
theorem surfaceChart_aemeasurable_restrict_volume
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) :
    AEMeasurable e (measureGeometry.volume.restrict e.source) := by
  letI : OpensMeasurableSpace X := measureGeometry.opensMeasurable
  exact e.continuousOn.aemeasurable e.open_source.measurableSet

/--
%%handwave
name:
  Left weak integral changes variables to coordinate volume
statement:
  The source-localized integral of \(\Delta_g f\,\eta\) changes variables
  through the chart to the coordinate divergence-form Laplacian integrated
  against the coordinate Riemannian volume measure.
proof:
  Push forward the restricted Riemannian volume measure by the chart.  The
  volume compatibility says that this pushforward is the coordinate
  Riemannian volume measure, and the global divergence-form expression agrees
  with the coordinate one at corresponding points.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_left_chartMeasure_aestronglyMeasurable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (_hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η) :
    AEStronglyMeasurable
      (fun z : ℂ ↦
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
          η (e.symm z))
      (riemannianVolumeChartMeasure metric e) := by
  have hac :
      riemannianVolumeChartMeasure metric e ≪
        MeasureTheory.volume.restrict e.target := by
    rw [riemannianVolumeChartMeasure]
    exact withDensity_absolutelyContinuous _ _
  have hρ_inv_cont : ContinuousOn
      (fun z : ℂ ↦ (surfaceMetricVolumeDensityInChart metric e z)⁻¹)
      e.target := by
    have hρ_smooth : ContDiffOn ℝ ∞
        (surfaceMetricVolumeDensityInChart metric e) e.target :=
      (surfaceMetricVolumeDensityInChart_smooth_positive X metric e _he).1
    have hρ_ne :
        ∀ z ∈ e.target, surfaceMetricVolumeDensityInChart metric e z ≠ 0 := by
      intro z hz
      exact ne_of_gt
        ((surfaceMetricVolumeDensityInChart_smooth_positive X metric e _he).2 z hz)
    exact (hρ_smooth.inv hρ_ne).continuousOn
  have hρ_inv_vol : AEStronglyMeasurable
      (fun z : ℂ ↦ (surfaceMetricVolumeDensityInChart metric e z)⁻¹)
      (MeasureTheory.volume.restrict e.target) :=
    hρ_inv_cont.aestronglyMeasurable e.open_target.measurableSet
  have hρ_inv : AEStronglyMeasurable
      (fun z : ℂ ↦ (surfaceMetricVolumeDensityInChart metric e z)⁻¹)
      (riemannianVolumeChartMeasure metric e) :=
    AEStronglyMeasurable.mono_ac hac hρ_inv_vol
  have hD₀ : AEStronglyMeasurable
      (fun z : ℂ ↦
        fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
          z (1 : ℂ))
      (riemannianVolumeChartMeasure metric e) :=
    (measurable_fderiv_apply_const ℝ
      (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
      (1 : ℂ)).aestronglyMeasurable
  have hD₁ : AEStronglyMeasurable
      (fun z : ℂ ↦
        fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
          z Complex.I)
      (riemannianVolumeChartMeasure metric e) :=
    (measurable_fderiv_apply_const ℝ
      (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
      Complex.I).aestronglyMeasurable
  have hη_chart : ContDiffOn ℝ ∞
      (fun z : ℂ ↦ η (e.symm z)) e.target := by
    simpa using hη e _he
  have hη_vol : AEStronglyMeasurable
      (fun z : ℂ ↦ η (e.symm z))
      (MeasureTheory.volume.restrict e.target) :=
    hη_chart.continuousOn.aestronglyMeasurable e.open_target.measurableSet
  have hη_ae : AEStronglyMeasurable
      (fun z : ℂ ↦ η (e.symm z))
      (riemannianVolumeChartMeasure metric e) :=
    AEStronglyMeasurable.mono_ac hac hη_vol
  simpa [surfaceDivergenceFormLaplaceBeltramiInChart] using
    (hρ_inv.mul (hD₀.add hD₁)).mul hη_ae

/--
%%handwave
name:
  Volume density transforms in real coordinates
statement:
  On a chart overlap, the Riemannian volume density in the first coordinate is
  the volume density in the second coordinate, evaluated after the transition
  map, times the absolute Jacobian determinant of that transition map.
proof:
  This is the real-valued form of the coordinate volume-density
  transformation law from the smooth Riemannian metric construction.
-/
theorem surfaceMetricVolumeDensityInChart_transform_on_overlap_real
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X) :
    ∀ {z : ℂ}, z ∈ e.target → e.symm z ∈ e'.source →
      surfaceMetricVolumeDensityInChart metric e z =
        |(fderivWithin ℝ (surfaceChartTransition e' e)
          (surfaceChartOverlapDomain e' e) z).det| *
          surfaceMetricVolumeDensityInChart metric e'
            (surfaceChartTransition e' e z) := by
  intro z hz_target hz_source
  let J : ℂ →L[ℝ] ℂ :=
    fderivWithin ℝ (surfaceChartTransition e' e)
      (surfaceChartOverlapDomain e' e) z
  have hz_overlap : z ∈ surfaceChartOverlapDomain e' e :=
    ⟨hz_target, hz_source⟩
  have hENN :=
    surfaceMetricVolumeDensityInChart_transform_on_overlap
      X metric e' e _he' _he z hz_overlap
  have hz'_target :
      surfaceChartTransition e' e z ∈ e'.target :=
    e'.map_source hz_source
  have hρ_nonneg :
      0 ≤ surfaceMetricVolumeDensityInChart metric e z :=
    le_of_lt
      ((surfaceMetricVolumeDensityInChart_smooth_positive X metric e _he).2
        z hz_target)
  have hρ'_nonneg :
      0 ≤ surfaceMetricVolumeDensityInChart metric e'
          (surfaceChartTransition e' e z) :=
    le_of_lt
      ((surfaceMetricVolumeDensityInChart_smooth_positive X metric e' _he').2
        (surfaceChartTransition e' e z) hz'_target)
  have hprod_nonneg :
      0 ≤ |J.det| *
          surfaceMetricVolumeDensityInChart metric e'
            (surfaceChartTransition e' e z) :=
    mul_nonneg (abs_nonneg _) hρ'_nonneg
  rw [show fderivWithin ℝ (surfaceChartTransition e' e)
        (surfaceChartOverlapDomain e' e) z = J by rfl] at hENN
  rw [← ENNReal.ofReal_mul (abs_nonneg J.det)] at hENN
  exact (ENNReal.ofReal_eq_ofReal_iff hρ_nonneg hprod_nonneg).mp hENN

/--
%%handwave
name:
  Chart transitions are smooth on overlaps
statement:
  A coordinate transition map between two surface charts is smooth on its
  overlap domain, viewed as a map between real two-dimensional coordinate
  planes.
proof:
  The complex atlas is contained in the maximal real smooth atlas associated
  to the Riemann surface, and this is exactly the smoothness of the extended
  coordinate change.
-/
theorem surfaceChartTransition_contDiffOn_overlap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    (g : SmoothRiemannianMetricOnSurface X) :
    ContDiffOn ℝ ∞ (surfaceChartTransition e e')
      (surfaceChartOverlapDomain e e') := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  have h := SurfaceRealModel.contDiffOn_extendCoordChange
    (IsManifold.subset_maximalAtlas (I := SurfaceRealModel) (n := ∞) _he')
    (IsManifold.subset_maximalAtlas (I := SurfaceRealModel) (n := ∞) _he)
  simpa [SurfaceRealModel, surfaceChartTransition, surfaceChartOverlapDomain,
    ModelWithCorners.extendCoordChange, PartialEquiv.trans_source] using h

private theorem surfaceChartTransition_fderivWithin_isInvertible_on_overlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X) :
    ∀ z ∈ surfaceChartOverlapDomain e' e,
      (fderivWithin ℝ (surfaceChartTransition e' e)
        (surfaceChartOverlapDomain e' e) z).IsInvertible := by
  intro z hz
  letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
  let T : ℂ → ℂ := surfaceChartTransition e' e
  let Ω : Set ℂ := surfaceChartOverlapDomain e' e
  let J : ℂ →L[ℝ] ℂ := fderivWithin ℝ T Ω z
  let A : ℂ →L[ℝ] ℂ := surfaceChartTangentMap e z
  let A' : ℂ →L[ℝ] ℂ := surfaceChartTangentMap e' (T z)
  have hz_target : z ∈ e.target := hz.1
  have hz'_target : T z ∈ e'.target := by
    simpa [T, surfaceChartTransition] using e'.map_source hz.2
  have hframe : A = A'.comp J := by
    simpa [A, A', J, T, Ω] using
      surfaceChartTangentMap_comp_transition_on_overlap
        X e' e _he' _he metric z hz
  have hA : A.IsInvertible := by
    simpa [A] using surfaceChartTangentMap_isInvertible X metric e _he z hz_target
  have hA' : A'.IsInvertible := by
    simpa [A'] using
      surfaceChartTangentMap_isInvertible X metric e' _he'
        (T z) hz'_target
  have hJ_eq : J = A'.inverse.comp A := by
    ext v
    have hAv : A v = A' (J v) := by
      simpa [ContinuousLinearMap.comp_apply] using
        congr_arg (fun L : ℂ →L[ℝ] ℂ ↦ L v) hframe
    exact ((hA'.inverse_apply_eq).2 hAv).symm
  change J.IsInvertible
  rw [hJ_eq]
  exact hA'.inverse.comp hA

private theorem surfaceFunctionChartDerivativeComponent_transform_on_overlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    (f : X → ℝ) (hf : IsSmoothOnSurface (Set.univ : Set X) f) :
    ∀ z ∈ surfaceChartOverlapDomain e' e, ∀ i : Fin 2,
      surfaceFunctionChartDerivativeComponent e f z i =
        fderiv ℝ (fun w : ℂ ↦ f (e'.symm w))
          (surfaceChartTransition e' e z)
          ((fderivWithin ℝ (surfaceChartTransition e' e)
            (surfaceChartOverlapDomain e' e) z) (complexCoordinateVector i)) := by
  intro z hz i
  let T : ℂ → ℂ := surfaceChartTransition e' e
  let Ω : Set ℂ := surfaceChartOverlapDomain e' e
  let φ : ℂ → ℝ := fun w ↦ f (e.symm w)
  let ψ : ℂ → ℝ := fun w ↦ f (e'.symm w)
  let J : ℂ →L[ℝ] ℂ := fderivWithin ℝ T Ω z
  have hΩ : IsOpen Ω := by
    simpa [Ω] using surfaceChartOverlapDomain_isOpen e' e
  have hz' : T z ∈ e'.target := by
    simpa [T, surfaceChartTransition] using e'.map_source hz.2
  have hψ_cont : ContDiffOn ℝ ∞ ψ e'.target := by
    simpa [ψ] using hf e' _he'
  have hψ_deriv :
      HasFDerivWithinAt ψ
        (fderivWithin ℝ ψ e'.target (T z)) e'.target (T z) :=
    (hψ_cont.differentiableOn (by simp) (T z) hz').hasFDerivWithinAt
  have hT_deriv :
      HasFDerivWithinAt T J Ω z := by
    simpa [T, Ω, J] using
      surfaceChartTransition_hasFDerivWithinAt_on_overlap
        X e' e _he' _he metric z hz
  have hmaps : Set.MapsTo T Ω e'.target := by
    intro w hw
    exact e'.map_source hw.2
  have hcomp :
      HasFDerivWithinAt (ψ ∘ T)
        ((fderivWithin ℝ ψ e'.target (T z)).comp J) Ω z :=
    hψ_deriv.comp z hT_deriv hmaps
  have hEq : Set.EqOn φ (ψ ∘ T) Ω := by
    intro w hw
    have hbase : e'.symm (T w) = e.symm w := by
      simpa [T, surfaceChartTransition] using e'.left_inv hw.2
    simp [φ, ψ, hbase]
  have hsource :
      HasFDerivWithinAt φ
        ((fderivWithin ℝ ψ e'.target (T z)).comp J) Ω z :=
    hcomp.congr hEq (hEq hz)
  have hφ_fderiv :
      fderiv ℝ φ z = (fderiv ℝ ψ (T z)).comp J := by
    have hwithin := hsource.fderivWithin (hΩ.uniqueDiffWithinAt hz)
    rw [fderivWithin_of_isOpen hΩ hz] at hwithin
    rw [fderivWithin_of_isOpen e'.open_target hz'] at hwithin
    exact hwithin
  calc
    surfaceFunctionChartDerivativeComponent e f z i =
        fderiv ℝ φ z (complexCoordinateVector i) := by
      rfl
    _ = fderiv ℝ ψ (T z)
        (J (complexCoordinateVector i)) := by
      rw [hφ_fderiv]
      rfl

private theorem surfaceFunctionChartDerivativeComponent_transform_components_on_overlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    (f : X → ℝ) (hf : IsSmoothOnSurface (Set.univ : Set X) f) :
    ∀ z ∈ surfaceChartOverlapDomain e' e, ∀ i : Fin 2,
      surfaceFunctionChartDerivativeComponent e f z i =
        (fderivWithin ℝ (surfaceChartTransition e' e)
            (surfaceChartOverlapDomain e' e) z
            (complexCoordinateVector i)).re *
          surfaceFunctionChartDerivativeComponent e' f
            (surfaceChartTransition e' e z) 0 +
        (fderivWithin ℝ (surfaceChartTransition e' e)
            (surfaceChartOverlapDomain e' e) z
            (complexCoordinateVector i)).im *
          surfaceFunctionChartDerivativeComponent e' f
            (surfaceChartTransition e' e z) 1 := by
  intro z hz i
  let L : ℂ →L[ℝ] ℝ :=
    fderiv ℝ (fun w : ℂ ↦ f (e'.symm w))
      (surfaceChartTransition e' e z)
  let v : ℂ :=
    (fderivWithin ℝ (surfaceChartTransition e' e)
      (surfaceChartOverlapDomain e' e) z) (complexCoordinateVector i)
  rw [surfaceFunctionChartDerivativeComponent_transform_on_overlap
    metric e e' _he _he' f hf z hz i]
  change L v =
    v.re * surfaceFunctionChartDerivativeComponent e' f
      (surfaceChartTransition e' e z) 0 +
    v.im * surfaceFunctionChartDerivativeComponent e' f
      (surfaceChartTransition e' e z) 1
  simpa [L, v, surfaceFunctionChartDerivativeComponent,
    surfaceFunctionChartDirectionalDerivative] using
      realLinearMap_apply_complex_eq_components L v

/--
%%handwave
name:
  Local transformation law for coordinate derivative components
statement:
  On a chart overlap, at a point lying over an open region where the function
  is smooth, the coordinate first derivatives transform by the derivative of
  the coordinate transition.
proof:
  Write the two coordinate representatives and compose one with the transition
  map.  The representatives agree on the overlap.  Smoothness on the open
  region gives an ordinary derivative at the target coordinate point, so the
  chain rule gives the transformation formula.
-/
theorem surfaceFunctionChartDerivativeComponent_transform_components_on_overlap_of_mem_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    {U : Set X} (hU : IsOpen U)
    (f : X → ℝ) (hf : IsSmoothOnSurface U f) :
    ∀ z ∈ surfaceChartOverlapDomain e' e, e.symm z ∈ U → ∀ i : Fin 2,
      surfaceFunctionChartDerivativeComponent e f z i =
        (fderivWithin ℝ (surfaceChartTransition e' e)
            (surfaceChartOverlapDomain e' e) z
            (complexCoordinateVector i)).re *
          surfaceFunctionChartDerivativeComponent e' f
            (surfaceChartTransition e' e z) 0 +
        (fderivWithin ℝ (surfaceChartTransition e' e)
            (surfaceChartOverlapDomain e' e) z
            (complexCoordinateVector i)).im *
          surfaceFunctionChartDerivativeComponent e' f
            (surfaceChartTransition e' e z) 1 := by
  intro z hz hzU i
  let T : ℂ → ℂ := surfaceChartTransition e' e
  let Ω : Set ℂ := surfaceChartOverlapDomain e' e
  let φ : ℂ → ℝ := fun w ↦ f (e.symm w)
  let ψ : ℂ → ℝ := fun w ↦ f (e'.symm w)
  let J : ℂ →L[ℝ] ℂ := fderivWithin ℝ T Ω z
  let L : ℂ →L[ℝ] ℝ := fderiv ℝ ψ (T z)
  let v : ℂ := J (complexCoordinateVector i)
  have hΩ : IsOpen Ω := by
    simpa [Ω] using surfaceChartOverlapDomain_isOpen e' e
  have hz' : T z ∈ e'.target := by
    simpa [T, surfaceChartTransition] using e'.map_source hz.2
  have hbase : e'.symm (T z) = e.symm z := by
    simpa [T, surfaceChartTransition] using e'.left_inv hz.2
  have hz'U : e'.symm (T z) ∈ U := by
    simpa [hbase] using hzU
  have hS' : IsOpen (e'.target ∩ e'.symm ⁻¹' U) :=
    e'.isOpen_inter_preimage_symm hU
  have hψ_cont :
      ContDiffOn ℝ ∞ ψ (e'.target ∩ e'.symm ⁻¹' U) := by
    simpa [ψ] using hf e' _he'
  have hψ_at : ContDiffAt ℝ ∞ ψ (T z) :=
    hψ_cont.contDiffAt (hS'.mem_nhds ⟨hz', hz'U⟩)
  have hψ_deriv :
      HasFDerivAt ψ L (T z) := by
    simpa [L] using (hψ_at.differentiableAt (by simp)).hasFDerivAt
  have hT_deriv :
      HasFDerivWithinAt T J Ω z := by
    simpa [T, Ω, J] using
      surfaceChartTransition_hasFDerivWithinAt_on_overlap
        X e' e _he' _he metric z hz
  have hcomp :
      HasFDerivWithinAt (ψ ∘ T) (L.comp J) Ω z :=
    hψ_deriv.comp_hasFDerivWithinAt z hT_deriv
  have hEq : Set.EqOn φ (ψ ∘ T) Ω := by
    intro w hw
    have hbase_w : e'.symm (T w) = e.symm w := by
      simpa [T, surfaceChartTransition] using e'.left_inv hw.2
    simp [φ, ψ, hbase_w]
  have hsource :
      HasFDerivWithinAt φ (L.comp J) Ω z :=
    hcomp.congr hEq (hEq hz)
  have hφ_fderiv :
      fderiv ℝ φ z = L.comp J := by
    have hwithin := hsource.fderivWithin (hΩ.uniqueDiffWithinAt hz)
    rw [fderivWithin_of_isOpen hΩ hz] at hwithin
    exact hwithin
  have hcomponent :
      surfaceFunctionChartDerivativeComponent e f z i =
        L v := by
    calc
      surfaceFunctionChartDerivativeComponent e f z i =
          fderiv ℝ φ z (complexCoordinateVector i) := by
        rfl
      _ = L (J (complexCoordinateVector i)) := by
        rw [hφ_fderiv]
        rfl
      _ = L v := by
        rfl
  rw [hcomponent]
  change L v =
    v.re * surfaceFunctionChartDerivativeComponent e' f (T z) 0 +
    v.im * surfaceFunctionChartDerivativeComponent e' f (T z) 1
  simpa [L, v, ψ, T, surfaceFunctionChartDerivativeComponent,
    surfaceFunctionChartDirectionalDerivative] using
      realLinearMap_apply_complex_eq_components L v

private theorem twoByTwo_inverseMetricVector_transform_zero
    {a b c d g₁₁ g₁₂ g₂₁ g₂₂ P Q : ℝ}
    (hJ : a * d - b * c ≠ 0)
    (hG : g₁₁ * g₂₂ - g₁₂ * g₂₁ ≠ 0) :
    let G₁₁ := a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂
    let G₁₂ := a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂
    let G₂₁ := b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂
    let G₂₂ := b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂
    let D := g₁₁ * g₂₂ - g₁₂ * g₂₁
    let D' := G₁₁ * G₂₂ - G₁₂ * G₂₁
    let p := a * P + c * Q
    let q := b * P + d * Q
    a * (D'⁻¹ * G₂₂ * p + (-D'⁻¹ * G₁₂) * q) +
        b * ((-D'⁻¹ * G₂₁) * p + D'⁻¹ * G₁₁ * q) =
      D⁻¹ * g₂₂ * P + (-D⁻¹ * g₁₂) * Q := by
  have hD' :
      (a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂) *
          (b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂) -
        (a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂) *
          (b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂) =
        (a * d - b * c) ^ 2 * (g₁₁ * g₂₂ - g₁₂ * g₂₁) := by
    ring
  have hJ_sq : (a * d - b * c) ^ 2 ≠ 0 := pow_ne_zero 2 hJ
  have hJ_sq_nf :
      -(c * b * d * a * 2) + c ^ 2 * b ^ 2 + d ^ 2 * a ^ 2 ≠ 0 := by
    rw [show -(c * b * d * a * 2) + c ^ 2 * b ^ 2 + d ^ 2 * a ^ 2 =
        (a * d - b * c) ^ 2 by ring]
    exact hJ_sq
  dsimp only
  rw [hD']
  field_simp [hJ_sq, hJ_sq_nf, hG]
  ring_nf

private theorem twoByTwo_inverseMetricVector_transform_one
    {a b c d g₁₁ g₁₂ g₂₁ g₂₂ P Q : ℝ}
    (hJ : a * d - b * c ≠ 0)
    (hG : g₁₁ * g₂₂ - g₁₂ * g₂₁ ≠ 0) :
    let G₁₁ := a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂
    let G₁₂ := a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂
    let G₂₁ := b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂
    let G₂₂ := b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂
    let D := g₁₁ * g₂₂ - g₁₂ * g₂₁
    let D' := G₁₁ * G₂₂ - G₁₂ * G₂₁
    let p := a * P + c * Q
    let q := b * P + d * Q
    c * (D'⁻¹ * G₂₂ * p + (-D'⁻¹ * G₁₂) * q) +
        d * ((-D'⁻¹ * G₂₁) * p + D'⁻¹ * G₁₁ * q) =
      (-D⁻¹ * g₂₁) * P + D⁻¹ * g₁₁ * Q := by
  have hD' :
      (a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂) *
          (b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂) -
        (a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂) *
          (b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂) =
        (a * d - b * c) ^ 2 * (g₁₁ * g₂₂ - g₁₂ * g₂₁) := by
    ring
  have hJ_sq : (a * d - b * c) ^ 2 ≠ 0 := pow_ne_zero 2 hJ
  have hJ_sq_nf :
      -(c * b * d * a * 2) + c ^ 2 * b ^ 2 + d ^ 2 * a ^ 2 ≠ 0 := by
    rw [show -(c * b * d * a * 2) + c ^ 2 * b ^ 2 + d ^ 2 * a ^ 2 =
        (a * d - b * c) ^ 2 by ring]
    exact hJ_sq
  have hJ_sq_comm : (a * d - c * b) ^ 2 ≠ 0 := by
    rw [show (a * d - c * b) ^ 2 = (a * d - b * c) ^ 2 by ring]
    exact hJ_sq
  dsimp only
  rw [hD']
  field_simp [hJ_sq, hJ_sq_nf, hG]
  rw [div_eq_iff hJ_sq_comm]
  ring_nf

private theorem surfaceMetricInverseGradientVector_transform_zero_on_overlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    (f : X → ℝ) :
    ∀ z ∈ surfaceChartOverlapDomain e' e,
      (∀ i : Fin 2,
        surfaceFunctionChartDerivativeComponent e f z i =
          (fderivWithin ℝ (surfaceChartTransition e' e)
              (surfaceChartOverlapDomain e' e) z
              (complexCoordinateVector i)).re *
            surfaceFunctionChartDerivativeComponent e' f
              (surfaceChartTransition e' e z) 0 +
          (fderivWithin ℝ (surfaceChartTransition e' e)
              (surfaceChartOverlapDomain e' e) z
              (complexCoordinateVector i)).im *
            surfaceFunctionChartDerivativeComponent e' f
              (surfaceChartTransition e' e z) 1) →
      let J : ℂ →L[ℝ] ℂ :=
        fderivWithin ℝ (surfaceChartTransition e' e)
          (surfaceChartOverlapDomain e' e) z
      (J (1 : ℂ)).re *
          (surfaceMetricInverseGramCoeffInChart metric e z 0 0 *
              surfaceFunctionChartDerivativeComponent e f z 0 +
            surfaceMetricInverseGramCoeffInChart metric e z 0 1 *
              surfaceFunctionChartDerivativeComponent e f z 1) +
        (J Complex.I).re *
          (surfaceMetricInverseGramCoeffInChart metric e z 1 0 *
              surfaceFunctionChartDerivativeComponent e f z 0 +
            surfaceMetricInverseGramCoeffInChart metric e z 1 1 *
              surfaceFunctionChartDerivativeComponent e f z 1) =
        surfaceMetricInverseGramCoeffInChart metric e'
            (surfaceChartTransition e' e z) 0 0 *
          surfaceFunctionChartDerivativeComponent e' f
            (surfaceChartTransition e' e z) 0 +
        surfaceMetricInverseGramCoeffInChart metric e'
            (surfaceChartTransition e' e z) 0 1 *
        surfaceFunctionChartDerivativeComponent e' f
            (surfaceChartTransition e' e z) 1 := by
  intro z hz hcomp
  letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
  let T : ℂ → ℂ := surfaceChartTransition e' e
  let Ω : Set ℂ := surfaceChartOverlapDomain e' e
  let J : ℂ →L[ℝ] ℂ := fderivWithin ℝ T Ω z
  let A : ℂ →L[ℝ] ℂ := surfaceChartTangentMap e z
  let A' : ℂ →L[ℝ] ℂ := surfaceChartTangentMap e' (T z)
  let B := metric.toContMDiffRiemannianMetric.inner (e.symm z)
  let u : TangentSpace SurfaceRealModel (e.symm z) := A' (1 : ℂ)
  let v : TangentSpace SurfaceRealModel (e.symm z) := A' Complex.I
  let a : ℝ := (J (1 : ℂ)).re
  let c : ℝ := (J (1 : ℂ)).im
  let b : ℝ := (J Complex.I).re
  let d : ℝ := (J Complex.I).im
  let g₁₁ : ℝ := B u u
  let g₁₂ : ℝ := B u v
  let g₂₁ : ℝ := B v u
  let g₂₂ : ℝ := B v v
  let P : ℝ :=
    surfaceFunctionChartDerivativeComponent e' f (T z) 0
  let Q : ℝ :=
    surfaceFunctionChartDerivativeComponent e' f (T z) 1
  have hz_target : z ∈ e.target := hz.1
  have hz'_target : T z ∈ e'.target := by
    simpa [T, surfaceChartTransition] using e'.map_source hz.2
  have hbase : e'.symm (T z) = e.symm z := by
    simpa [T, surfaceChartTransition] using e'.left_inv hz.2
  have hframe : A = A'.comp J := by
    simpa [A, A', J, T, Ω] using
      surfaceChartTangentMap_comp_transition_on_overlap
        X e' e _he' _he metric z hz
  have hJdet :
      a * d - b * c ≠ 0 := by
    have hJinv :
        J.IsInvertible :=
      surfaceChartTransition_fderivWithin_isInvertible_on_overlap
        metric e e' _he _he' z hz
    have hdet : J.det ≠ 0 :=
      coordinateComplexDet_ne_zero_of_isInvertible J hJinv
    have hdet_eq : J.det = a * d - b * c := by
      simpa [a, b, c, d] using coordinateComplex_det_eq_components J
    simpa [hdet_eq] using hdet
  have hG :
      g₁₁ * g₂₂ - g₁₂ * g₂₁ ≠ 0 := by
    have hdet :
        surfaceMetricGramDetInChart metric e' (T z) ≠ 0 :=
      ne_of_gt
        (surfaceMetricGramDetInChart_pos X metric e' _he' (T z) hz'_target)
    have hgram :
        surfaceMetricGramDetInChart metric e' (T z) =
          g₁₁ * g₂₂ - g₁₂ * g₂₁ := by
      rw [surfaceMetricGramDetInChart]
      rw [hbase]
    simpa [hgram] using hdet
  have hJ1 :
      J (1 : ℂ) = (a : ℝ) • (1 : ℂ) + (c : ℝ) • Complex.I := by
    apply Complex.ext <;> simp [a, c]
  have hJI :
      J Complex.I = (b : ℝ) • (1 : ℂ) + (d : ℝ) • Complex.I := by
    apply Complex.ext <;> simp [b, d]
  have hA1 : A (1 : ℂ) = (a : ℝ) • u + (c : ℝ) • v := by
    calc
      A (1 : ℂ) = A' (J (1 : ℂ)) := by
        rw [hframe]
        rfl
      _ = A' ((a : ℝ) • (1 : ℂ) + (c : ℝ) • Complex.I) := by
        rw [hJ1]
      _ = (a : ℝ) • A' (1 : ℂ) + (c : ℝ) • A' Complex.I := by
        rw [map_add, map_smul, map_smul]
      _ = (a : ℝ) • u + (c : ℝ) • v := by
        rfl
  have hAI : A Complex.I = (b : ℝ) • u + (d : ℝ) • v := by
    calc
      A Complex.I = A' (J Complex.I) := by
        rw [hframe]
        rfl
      _ = A' ((b : ℝ) • (1 : ℂ) + (d : ℝ) • Complex.I) := by
        rw [hJI]
      _ = (b : ℝ) • A' (1 : ℂ) + (d : ℝ) • A' Complex.I := by
        rw [map_add, map_smul, map_smul]
      _ = (b : ℝ) • u + (d : ℝ) • v := by
        rfl
  have hS11 :
      B (A (1 : ℂ)) (A (1 : ℂ)) =
        a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂ := by
    rw [hA1]
    simp only [map_add, map_smul]
    simp [g₁₁, g₁₂, g₂₁, g₂₂, smul_eq_mul]
    ring_nf
  have hS12 :
      B (A (1 : ℂ)) (A Complex.I) =
        a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂ := by
    rw [hA1, hAI]
    simp only [map_add, map_smul]
    simp [g₁₁, g₁₂, g₂₁, g₂₂, smul_eq_mul]
    ring_nf
  have hS21 :
      B (A Complex.I) (A (1 : ℂ)) =
        b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂ := by
    rw [hAI, hA1]
    simp only [map_add, map_smul]
    simp [g₁₁, g₁₂, g₂₁, g₂₂, smul_eq_mul]
    ring_nf
  have hS22 :
      B (A Complex.I) (A Complex.I) =
        b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂ := by
    rw [hAI]
    simp only [map_add, map_smul]
    simp [g₁₁, g₁₂, g₂₁, g₂₂, smul_eq_mul]
    ring_nf
  have hp :
      surfaceFunctionChartDerivativeComponent e f z 0 = a * P + c * Q := by
    simpa [J, T, Ω, a, c, P, Q] using
      hcomp 0
  have hq :
      surfaceFunctionChartDerivativeComponent e f z 1 = b * P + d * Q := by
    simpa [J, T, Ω, b, d, P, Q] using
      hcomp 1
  have hsource_det :
      surfaceMetricGramDetInChart metric e z =
        (a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂) *
            (b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂) -
          (a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂) *
            (b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂) := by
    simp [surfaceMetricGramDetInChart, A, B, hS11, hS12, hS21, hS22]
  have htarget_det :
      surfaceMetricGramDetInChart metric e' (T z) =
        g₁₁ * g₂₂ - g₁₂ * g₂₁ := by
    rw [surfaceMetricGramDetInChart]
    rw [hbase]
  have hs00 :
      surfaceMetricInverseGramCoeffInChart metric e z 0 0 =
        ((a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂) *
            (b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂) -
          (a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂) *
            (b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂))⁻¹ *
          (b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂) := by
    simp [surfaceMetricInverseGramCoeffInChart, A, B, hsource_det, hS22]
  have hs01 :
      surfaceMetricInverseGramCoeffInChart metric e z 0 1 =
        -(((a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂) *
            (b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂) -
          (a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂) *
            (b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂))⁻¹ *
          (a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂)) := by
    simp [surfaceMetricInverseGramCoeffInChart, A, B, hsource_det, hS12]
  have hs10 :
      surfaceMetricInverseGramCoeffInChart metric e z 1 0 =
        -(((a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂) *
            (b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂) -
          (a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂) *
            (b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂))⁻¹ *
          (b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂)) := by
    simp [surfaceMetricInverseGramCoeffInChart, A, B, hsource_det, hS21]
  have hs11 :
      surfaceMetricInverseGramCoeffInChart metric e z 1 1 =
        ((a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂) *
            (b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂) -
          (a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂) *
            (b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂))⁻¹ *
          (a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂) := by
    simp [surfaceMetricInverseGramCoeffInChart, A, B, hsource_det, hS11]
  have ht00 :
      surfaceMetricInverseGramCoeffInChart metric e' (T z) 0 0 =
        (g₁₁ * g₂₂ - g₁₂ * g₂₁)⁻¹ * g₂₂ := by
    rw [surfaceMetricInverseGramCoeffInChart_zero_zero]
    rw [htarget_det]
    rw [hbase]
  have ht01 :
      surfaceMetricInverseGramCoeffInChart metric e' (T z) 0 1 =
        -((g₁₁ * g₂₂ - g₁₂ * g₂₁)⁻¹) * g₁₂ := by
    rw [surfaceMetricInverseGramCoeffInChart_zero_one]
    rw [htarget_det]
    rw [hbase]
  dsimp only
  rw [hs00, hs01, hs10, hs11, ht00, ht01, hp, hq]
  simpa [P, Q] using
    twoByTwo_inverseMetricVector_transform_zero
      (a := a) (b := b) (c := c) (d := d)
      (g₁₁ := g₁₁) (g₁₂ := g₁₂) (g₂₁ := g₂₁) (g₂₂ := g₂₂)
      (P := P) (Q := Q) hJdet hG

private theorem surfaceMetricInverseGradientVector_transform_one_on_overlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    (f : X → ℝ) :
    ∀ z ∈ surfaceChartOverlapDomain e' e,
      (∀ i : Fin 2,
        surfaceFunctionChartDerivativeComponent e f z i =
          (fderivWithin ℝ (surfaceChartTransition e' e)
              (surfaceChartOverlapDomain e' e) z
              (complexCoordinateVector i)).re *
            surfaceFunctionChartDerivativeComponent e' f
              (surfaceChartTransition e' e z) 0 +
          (fderivWithin ℝ (surfaceChartTransition e' e)
              (surfaceChartOverlapDomain e' e) z
              (complexCoordinateVector i)).im *
            surfaceFunctionChartDerivativeComponent e' f
              (surfaceChartTransition e' e z) 1) →
      let J : ℂ →L[ℝ] ℂ :=
        fderivWithin ℝ (surfaceChartTransition e' e)
          (surfaceChartOverlapDomain e' e) z
      (J (1 : ℂ)).im *
          (surfaceMetricInverseGramCoeffInChart metric e z 0 0 *
              surfaceFunctionChartDerivativeComponent e f z 0 +
            surfaceMetricInverseGramCoeffInChart metric e z 0 1 *
              surfaceFunctionChartDerivativeComponent e f z 1) +
        (J Complex.I).im *
          (surfaceMetricInverseGramCoeffInChart metric e z 1 0 *
              surfaceFunctionChartDerivativeComponent e f z 0 +
            surfaceMetricInverseGramCoeffInChart metric e z 1 1 *
              surfaceFunctionChartDerivativeComponent e f z 1) =
        surfaceMetricInverseGramCoeffInChart metric e'
            (surfaceChartTransition e' e z) 1 0 *
          surfaceFunctionChartDerivativeComponent e' f
            (surfaceChartTransition e' e z) 0 +
        surfaceMetricInverseGramCoeffInChart metric e'
            (surfaceChartTransition e' e z) 1 1 *
        surfaceFunctionChartDerivativeComponent e' f
            (surfaceChartTransition e' e z) 1 := by
  intro z hz hcomp
  letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
  let T : ℂ → ℂ := surfaceChartTransition e' e
  let Ω : Set ℂ := surfaceChartOverlapDomain e' e
  let J : ℂ →L[ℝ] ℂ := fderivWithin ℝ T Ω z
  let A : ℂ →L[ℝ] ℂ := surfaceChartTangentMap e z
  let A' : ℂ →L[ℝ] ℂ := surfaceChartTangentMap e' (T z)
  let B := metric.toContMDiffRiemannianMetric.inner (e.symm z)
  let u : TangentSpace SurfaceRealModel (e.symm z) := A' (1 : ℂ)
  let v : TangentSpace SurfaceRealModel (e.symm z) := A' Complex.I
  let a : ℝ := (J (1 : ℂ)).re
  let c : ℝ := (J (1 : ℂ)).im
  let b : ℝ := (J Complex.I).re
  let d : ℝ := (J Complex.I).im
  let g₁₁ : ℝ := B u u
  let g₁₂ : ℝ := B u v
  let g₂₁ : ℝ := B v u
  let g₂₂ : ℝ := B v v
  let P : ℝ :=
    surfaceFunctionChartDerivativeComponent e' f (T z) 0
  let Q : ℝ :=
    surfaceFunctionChartDerivativeComponent e' f (T z) 1
  have hz'_target : T z ∈ e'.target := by
    simpa [T, surfaceChartTransition] using e'.map_source hz.2
  have hbase : e'.symm (T z) = e.symm z := by
    simpa [T, surfaceChartTransition] using e'.left_inv hz.2
  have hframe : A = A'.comp J := by
    simpa [A, A', J, T, Ω] using
      surfaceChartTangentMap_comp_transition_on_overlap
        X e' e _he' _he metric z hz
  have hJdet :
      a * d - b * c ≠ 0 := by
    have hJinv :
        J.IsInvertible :=
      surfaceChartTransition_fderivWithin_isInvertible_on_overlap
        metric e e' _he _he' z hz
    have hdet : J.det ≠ 0 :=
      coordinateComplexDet_ne_zero_of_isInvertible J hJinv
    have hdet_eq : J.det = a * d - b * c := by
      simpa [a, b, c, d] using coordinateComplex_det_eq_components J
    simpa [hdet_eq] using hdet
  have hG :
      g₁₁ * g₂₂ - g₁₂ * g₂₁ ≠ 0 := by
    have hdet :
        surfaceMetricGramDetInChart metric e' (T z) ≠ 0 :=
      ne_of_gt
        (surfaceMetricGramDetInChart_pos X metric e' _he' (T z) hz'_target)
    have hgram :
        surfaceMetricGramDetInChart metric e' (T z) =
          g₁₁ * g₂₂ - g₁₂ * g₂₁ := by
      rw [surfaceMetricGramDetInChart]
      rw [hbase]
    simpa [hgram] using hdet
  have hJ1 :
      J (1 : ℂ) = (a : ℝ) • (1 : ℂ) + (c : ℝ) • Complex.I := by
    apply Complex.ext <;> simp [a, c]
  have hJI :
      J Complex.I = (b : ℝ) • (1 : ℂ) + (d : ℝ) • Complex.I := by
    apply Complex.ext <;> simp [b, d]
  have hA1 : A (1 : ℂ) = (a : ℝ) • u + (c : ℝ) • v := by
    calc
      A (1 : ℂ) = A' (J (1 : ℂ)) := by
        rw [hframe]
        rfl
      _ = A' ((a : ℝ) • (1 : ℂ) + (c : ℝ) • Complex.I) := by
        rw [hJ1]
      _ = (a : ℝ) • A' (1 : ℂ) + (c : ℝ) • A' Complex.I := by
        rw [map_add, map_smul, map_smul]
      _ = (a : ℝ) • u + (c : ℝ) • v := by
        rfl
  have hAI : A Complex.I = (b : ℝ) • u + (d : ℝ) • v := by
    calc
      A Complex.I = A' (J Complex.I) := by
        rw [hframe]
        rfl
      _ = A' ((b : ℝ) • (1 : ℂ) + (d : ℝ) • Complex.I) := by
        rw [hJI]
      _ = (b : ℝ) • A' (1 : ℂ) + (d : ℝ) • A' Complex.I := by
        rw [map_add, map_smul, map_smul]
      _ = (b : ℝ) • u + (d : ℝ) • v := by
        rfl
  have hS11 :
      B (A (1 : ℂ)) (A (1 : ℂ)) =
        a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂ := by
    rw [hA1]
    simp only [map_add, map_smul]
    simp [g₁₁, g₁₂, g₂₁, g₂₂, smul_eq_mul]
    ring_nf
  have hS12 :
      B (A (1 : ℂ)) (A Complex.I) =
        a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂ := by
    rw [hA1, hAI]
    simp only [map_add, map_smul]
    simp [g₁₁, g₁₂, g₂₁, g₂₂, smul_eq_mul]
    ring_nf
  have hS21 :
      B (A Complex.I) (A (1 : ℂ)) =
        b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂ := by
    rw [hAI, hA1]
    simp only [map_add, map_smul]
    simp [g₁₁, g₁₂, g₂₁, g₂₂, smul_eq_mul]
    ring_nf
  have hS22 :
      B (A Complex.I) (A Complex.I) =
        b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂ := by
    rw [hAI]
    simp only [map_add, map_smul]
    simp [g₁₁, g₁₂, g₂₁, g₂₂, smul_eq_mul]
    ring_nf
  have hp :
      surfaceFunctionChartDerivativeComponent e f z 0 = a * P + c * Q := by
    simpa [J, T, Ω, a, c, P, Q] using
      hcomp 0
  have hq :
      surfaceFunctionChartDerivativeComponent e f z 1 = b * P + d * Q := by
    simpa [J, T, Ω, b, d, P, Q] using
      hcomp 1
  have hsource_det :
      surfaceMetricGramDetInChart metric e z =
        (a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂) *
            (b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂) -
          (a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂) *
            (b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂) := by
    simp [surfaceMetricGramDetInChart, A, B, hS11, hS12, hS21, hS22]
  have htarget_det :
      surfaceMetricGramDetInChart metric e' (T z) =
        g₁₁ * g₂₂ - g₁₂ * g₂₁ := by
    rw [surfaceMetricGramDetInChart]
    rw [hbase]
  have hs00 :
      surfaceMetricInverseGramCoeffInChart metric e z 0 0 =
        ((a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂) *
            (b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂) -
          (a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂) *
            (b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂))⁻¹ *
          (b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂) := by
    simp [surfaceMetricInverseGramCoeffInChart, A, B, hsource_det, hS22]
  have hs01 :
      surfaceMetricInverseGramCoeffInChart metric e z 0 1 =
        -(((a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂) *
            (b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂) -
          (a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂) *
            (b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂))⁻¹ *
          (a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂)) := by
    simp [surfaceMetricInverseGramCoeffInChart, A, B, hsource_det, hS12]
  have hs10 :
      surfaceMetricInverseGramCoeffInChart metric e z 1 0 =
        -(((a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂) *
            (b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂) -
          (a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂) *
            (b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂))⁻¹ *
          (b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂)) := by
    simp [surfaceMetricInverseGramCoeffInChart, A, B, hsource_det, hS21]
  have hs11 :
      surfaceMetricInverseGramCoeffInChart metric e z 1 1 =
        ((a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂) *
            (b * b * g₁₁ + b * d * g₁₂ + d * b * g₂₁ + d * d * g₂₂) -
          (a * b * g₁₁ + a * d * g₁₂ + c * b * g₂₁ + c * d * g₂₂) *
            (b * a * g₁₁ + b * c * g₁₂ + d * a * g₂₁ + d * c * g₂₂))⁻¹ *
          (a * a * g₁₁ + a * c * g₁₂ + c * a * g₂₁ + c * c * g₂₂) := by
    simp [surfaceMetricInverseGramCoeffInChart, A, B, hsource_det, hS11]
  have ht10 :
      surfaceMetricInverseGramCoeffInChart metric e' (T z) 1 0 =
        -((g₁₁ * g₂₂ - g₁₂ * g₂₁)⁻¹) * g₂₁ := by
    rw [surfaceMetricInverseGramCoeffInChart_one_zero]
    rw [htarget_det]
    rw [hbase]
  have ht11 :
      surfaceMetricInverseGramCoeffInChart metric e' (T z) 1 1 =
        (g₁₁ * g₂₂ - g₁₂ * g₂₁)⁻¹ * g₁₁ := by
    rw [surfaceMetricInverseGramCoeffInChart_one_one]
    rw [htarget_det]
    rw [hbase]
  dsimp only
  rw [hs00, hs01, hs10, hs11, ht10, ht11, hp, hq]
  simpa [P, Q] using
    twoByTwo_inverseMetricVector_transform_one
      (a := a) (b := b) (c := c) (d := d)
      (g₁₁ := g₁₁) (g₁₂ := g₁₂) (g₂₁ := g₂₁) (g₂₂ := g₂₂)
      (P := P) (Q := Q) hJdet hG

/--
%%handwave
name:
  Metric flux is a vector density on chart overlaps
statement:
  On an overlap of two coordinate charts, the metric gradient flux
  \(\rho g^{ij}\partial_j f\) transforms as a coordinate vector density.
proof:
  The volume density contributes the Jacobian factor, the inverse metric
  coefficients transform contravariantly, and the coordinate derivatives of
  \(f\) transform by the derivative of the transition map.
-/
theorem surfaceMetricGradientFlux_vectorDensityPullback_on_overlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    (f : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f) :
    IsVectorDensityPullbackBy
      (surfaceChartTransition e' e)
      (surfaceChartOverlapDomain e' e)
      (fun w i ↦ surfaceMetricGradientFluxInChart metric e f w i)
      (fun w i ↦ surfaceMetricGradientFluxInChart metric e' f w i) := by
  intro z hz
  let T : ℂ → ℂ := surfaceChartTransition e' e
  let Ω : Set ℂ := surfaceChartOverlapDomain e' e
  let J : ℂ →L[ℝ] ℂ := fderivWithin ℝ T Ω z
  have hJ :
      J.IsInvertible :=
    surfaceChartTransition_fderivWithin_isInvertible_on_overlap
      metric e e' _he _he' z hz
  refine ⟨hJ, ?_⟩
  apply hJ.injective
  have hright :
      J ((|J.det| : ℝ) •
          J.inverse
            (complexVectorFromComponents
              ((fun w i ↦ surfaceMetricGradientFluxInChart metric e' f w i)
                (T z)))) =
        (|J.det| : ℝ) •
          complexVectorFromComponents
            ((fun w i ↦ surfaceMetricGradientFluxInChart metric e' f w i)
              (T z)) := by
    rw [map_smul, hJ.self_apply_inverse]
  rw [hright]
  have hρ :
      surfaceMetricVolumeDensityInChart metric e z =
        |J.det| *
          surfaceMetricVolumeDensityInChart metric e' (T z) := by
    simpa [J, T, Ω] using
      surfaceMetricVolumeDensityInChart_transform_on_overlap_real
        metric e e' _he _he' hz.1 hz.2
  have hzero :
      (J (1 : ℂ)).re *
          (surfaceMetricInverseGramCoeffInChart metric e z 0 0 *
              surfaceFunctionChartDerivativeComponent e f z 0 +
            surfaceMetricInverseGramCoeffInChart metric e z 0 1 *
              surfaceFunctionChartDerivativeComponent e f z 1) +
        (J Complex.I).re *
          (surfaceMetricInverseGramCoeffInChart metric e z 1 0 *
              surfaceFunctionChartDerivativeComponent e f z 0 +
            surfaceMetricInverseGramCoeffInChart metric e z 1 1 *
              surfaceFunctionChartDerivativeComponent e f z 1) =
        surfaceMetricInverseGramCoeffInChart metric e' (T z) 0 0 *
          surfaceFunctionChartDerivativeComponent e' f (T z) 0 +
        surfaceMetricInverseGramCoeffInChart metric e' (T z) 0 1 *
          surfaceFunctionChartDerivativeComponent e' f (T z) 1 := by
    simpa [J, T, Ω] using
      surfaceMetricInverseGradientVector_transform_zero_on_overlap
        metric e e' _he _he' f z hz
        (surfaceFunctionChartDerivativeComponent_transform_components_on_overlap
          metric e e' _he _he' f hf z hz)
  have hone :
      (J (1 : ℂ)).im *
          (surfaceMetricInverseGramCoeffInChart metric e z 0 0 *
              surfaceFunctionChartDerivativeComponent e f z 0 +
            surfaceMetricInverseGramCoeffInChart metric e z 0 1 *
              surfaceFunctionChartDerivativeComponent e f z 1) +
        (J Complex.I).im *
          (surfaceMetricInverseGramCoeffInChart metric e z 1 0 *
              surfaceFunctionChartDerivativeComponent e f z 0 +
            surfaceMetricInverseGramCoeffInChart metric e z 1 1 *
              surfaceFunctionChartDerivativeComponent e f z 1) =
        surfaceMetricInverseGramCoeffInChart metric e' (T z) 1 0 *
          surfaceFunctionChartDerivativeComponent e' f (T z) 0 +
        surfaceMetricInverseGramCoeffInChart metric e' (T z) 1 1 *
          surfaceFunctionChartDerivativeComponent e' f (T z) 1 := by
    simpa [J, T, Ω] using
      surfaceMetricInverseGradientVector_transform_one_on_overlap
        metric e e' _he _he' f z hz
        (surfaceFunctionChartDerivativeComponent_transform_components_on_overlap
          metric e e' _he _he' f hf z hz)
  apply Complex.ext
  · rw [complexVectorFromComponents]
    rw [map_add, map_smul, map_smul]
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    simp [complexVectorFromComponents]
    rw [surfaceMetricGradientFluxInChart_zero,
      surfaceMetricGradientFluxInChart_one,
      surfaceMetricGradientFluxInChart_zero, hρ]
    rw [← hzero]
    ring
  · rw [complexVectorFromComponents]
    rw [map_add, map_smul, map_smul]
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    simp [complexVectorFromComponents]
    rw [surfaceMetricGradientFluxInChart_zero,
      surfaceMetricGradientFluxInChart_one,
      surfaceMetricGradientFluxInChart_one, hρ]
    rw [← hone]
    ring

/--
%%handwave
name:
  Local metric flux is a vector density on chart overlaps
statement:
  On the part of a chart overlap lying over an open region where the function
  is smooth, the metric gradient flux transforms as a coordinate vector
  density.
proof:
  The same tensorial transformation law as in the global case applies at each
  point of the open region.  The only analytic input is the local
  transformation law for the first coordinate derivatives of the function.
-/
theorem surfaceMetricGradientFlux_vectorDensityPullback_on_overlap_of_mem_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    {U : Set X} (hU : IsOpen U)
    (f : X → ℝ) (hf : IsSmoothOnSurface U f) :
    IsVectorDensityPullbackBy
      (surfaceChartTransition e' e)
      (surfaceChartOverlapDomain e' e ∩ e.symm ⁻¹' U)
      (fun w i ↦ surfaceMetricGradientFluxInChart metric e f w i)
      (fun w i ↦ surfaceMetricGradientFluxInChart metric e' f w i) := by
  intro z hz
  let T : ℂ → ℂ := surfaceChartTransition e' e
  let Ω₀ : Set ℂ := surfaceChartOverlapDomain e' e
  let Ω : Set ℂ := Ω₀ ∩ e.symm ⁻¹' U
  let J : ℂ →L[ℝ] ℂ := fderivWithin ℝ T Ω z
  have hz₀ : z ∈ Ω₀ := hz.1
  have hzU : e.symm z ∈ U := hz.2
  have hΩ₀ : IsOpen Ω₀ := by
    simpa [Ω₀] using surfaceChartOverlapDomain_isOpen e' e
  have hΩ : IsOpen Ω := by
    have hpre :
        IsOpen (e.target ∩ e.symm ⁻¹' (e'.source ∩ U)) :=
      e.isOpen_inter_preimage_symm (e'.open_source.inter hU)
    simpa [Ω, Ω₀, surfaceChartOverlapDomain, Set.preimage_inter,
      Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hpre
  have hJ_eq :
      J = fderivWithin ℝ T Ω₀ z := by
    rw [show J = fderivWithin ℝ T Ω z by rfl]
    rw [fderivWithin_of_isOpen hΩ hz,
      fderivWithin_of_isOpen hΩ₀ hz₀]
  have hJ :
      J.IsInvertible := by
    have hJ₀ :
        (fderivWithin ℝ T Ω₀ z).IsInvertible := by
      simpa [T, Ω₀] using
        surfaceChartTransition_fderivWithin_isInvertible_on_overlap
          metric e e' _he _he' z hz₀
    simpa [hJ_eq] using hJ₀
  refine ⟨hJ, ?_⟩
  apply hJ.injective
  have hright :
      J ((|J.det| : ℝ) •
          J.inverse
            (complexVectorFromComponents
              ((fun w i ↦ surfaceMetricGradientFluxInChart metric e' f w i)
                (T z)))) =
        (|J.det| : ℝ) •
          complexVectorFromComponents
            ((fun w i ↦ surfaceMetricGradientFluxInChart metric e' f w i)
              (T z)) := by
    rw [map_smul, hJ.self_apply_inverse]
  rw [hright]
  have hρ :
      surfaceMetricVolumeDensityInChart metric e z =
        |J.det| *
          surfaceMetricVolumeDensityInChart metric e' (T z) := by
    simpa [J, T, Ω, Ω₀, hJ_eq] using
      surfaceMetricVolumeDensityInChart_transform_on_overlap_real
        metric e e' _he _he' hz₀.1 hz₀.2
  have hzero :
      (J (1 : ℂ)).re *
          (surfaceMetricInverseGramCoeffInChart metric e z 0 0 *
              surfaceFunctionChartDerivativeComponent e f z 0 +
            surfaceMetricInverseGramCoeffInChart metric e z 0 1 *
              surfaceFunctionChartDerivativeComponent e f z 1) +
        (J Complex.I).re *
          (surfaceMetricInverseGramCoeffInChart metric e z 1 0 *
              surfaceFunctionChartDerivativeComponent e f z 0 +
            surfaceMetricInverseGramCoeffInChart metric e z 1 1 *
              surfaceFunctionChartDerivativeComponent e f z 1) =
        surfaceMetricInverseGramCoeffInChart metric e' (T z) 0 0 *
          surfaceFunctionChartDerivativeComponent e' f (T z) 0 +
        surfaceMetricInverseGramCoeffInChart metric e' (T z) 0 1 *
          surfaceFunctionChartDerivativeComponent e' f (T z) 1 := by
    simpa [J, T, Ω₀, hJ_eq] using
      surfaceMetricInverseGradientVector_transform_zero_on_overlap
        metric e e' _he _he' f z hz₀
        (surfaceFunctionChartDerivativeComponent_transform_components_on_overlap_of_mem_open
          metric e e' _he _he' hU f hf z hz₀ hzU)
  have hone :
      (J (1 : ℂ)).im *
          (surfaceMetricInverseGramCoeffInChart metric e z 0 0 *
              surfaceFunctionChartDerivativeComponent e f z 0 +
            surfaceMetricInverseGramCoeffInChart metric e z 0 1 *
              surfaceFunctionChartDerivativeComponent e f z 1) +
        (J Complex.I).im *
          (surfaceMetricInverseGramCoeffInChart metric e z 1 0 *
              surfaceFunctionChartDerivativeComponent e f z 0 +
            surfaceMetricInverseGramCoeffInChart metric e z 1 1 *
              surfaceFunctionChartDerivativeComponent e f z 1) =
        surfaceMetricInverseGramCoeffInChart metric e' (T z) 1 0 *
          surfaceFunctionChartDerivativeComponent e' f (T z) 0 +
        surfaceMetricInverseGramCoeffInChart metric e' (T z) 1 1 *
          surfaceFunctionChartDerivativeComponent e' f (T z) 1 := by
    simpa [J, T, Ω₀, hJ_eq] using
      surfaceMetricInverseGradientVector_transform_one_on_overlap
        metric e e' _he _he' f z hz₀
        (surfaceFunctionChartDerivativeComponent_transform_components_on_overlap_of_mem_open
          metric e e' _he _he' hU f hf z hz₀ hzU)
  apply Complex.ext
  · rw [complexVectorFromComponents]
    rw [map_add, map_smul, map_smul]
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    simp [complexVectorFromComponents]
    rw [surfaceMetricGradientFluxInChart_zero,
      surfaceMetricGradientFluxInChart_one,
      surfaceMetricGradientFluxInChart_zero, hρ]
    rw [← hzero]
    ring
  · rw [complexVectorFromComponents]
    rw [map_add, map_smul, map_smul]
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    simp [complexVectorFromComponents]
    rw [surfaceMetricGradientFluxInChart_zero,
      surfaceMetricGradientFluxInChart_one,
      surfaceMetricGradientFluxInChart_one, hρ]
    rw [← hone]
    ring

/--
%%handwave
name:
  Coordinate divergence of the metric flux transforms on overlaps
statement:
  On a chart overlap, the Euclidean divergence of the Riemannian metric flux
  \(\rho g^{ij}\partial_j f\) transforms as a density: the divergence in the
  first coordinate equals the divergence in the second coordinate after the
  transition map, times the absolute Jacobian determinant.
proof:
  This is the coordinate chain rule for vector densities.  The inverse metric
  coefficients transform contravariantly, the coordinate derivatives of \(f\)
  transform by the derivative of the transition map, and differentiating the
  transformed flux gives the usual divergence-of-vector-density change of
  variables formula.
-/
theorem surfaceMetricGradientFlux_coordinateDivergence_transform_on_overlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    (f : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f) :
    ∀ {z : ℂ}, z ∈ e.target → e.symm z ∈ e'.source →
      surfaceCoordinateDivergence
          (fun w i ↦ surfaceMetricGradientFluxInChart metric e f w i) z =
        |(fderivWithin ℝ (surfaceChartTransition e' e)
          (surfaceChartOverlapDomain e' e) z).det| *
          surfaceCoordinateDivergence
            (fun w i ↦ surfaceMetricGradientFluxInChart metric e' f w i)
            (surfaceChartTransition e' e z) := by
  intro z hz_target hz_source
  let T : ℂ → ℂ := surfaceChartTransition e' e
  let Ω : Set ℂ := surfaceChartOverlapDomain e' e
  let Ω' : Set ℂ := e'.target
  let F : ℂ → Fin 2 → ℝ :=
    fun w i ↦ surfaceMetricGradientFluxInChart metric e f w i
  let F' : ℂ → Fin 2 → ℝ :=
    fun w i ↦ surfaceMetricGradientFluxInChart metric e' f w i
  have hzΩ : z ∈ Ω := ⟨hz_target, hz_source⟩
  have hΩ : IsOpen Ω := by
    simpa [Ω] using surfaceChartOverlapDomain_isOpen e' e
  have hΩ' : IsOpen Ω' := by
    simpa [Ω'] using e'.open_target
  have hT_maps : Set.MapsTo T Ω Ω' := by
    intro w hw
    exact e'.map_source hw.2
  have hT : ContDiffOn ℝ ∞ T Ω := by
    simpa [T, Ω] using
      surfaceChartTransition_contDiffOn_overlap X e' e _he' _he metric
  have hF : ∀ i : Fin 2, ContDiffOn ℝ ∞ (fun w : ℂ ↦ F w i) Ω := by
    intro i
    exact (surfaceMetricGradientFluxInChart_contDiffOn
      metric e _he f hf i).mono (by
        intro w hw
        exact hw.1)
  have hF' : ∀ i : Fin 2, ContDiffOn ℝ ∞ (fun w : ℂ ↦ F' w i) Ω' := by
    intro i
    simpa [F', Ω'] using
      surfaceMetricGradientFluxInChart_contDiffOn metric e' _he' f hf i
  have hpull : IsVectorDensityPullbackBy T Ω F F' := by
    simpa [T, Ω, F, F'] using
      surfaceMetricGradientFlux_vectorDensityPullback_on_overlap
        metric e e' _he _he' f hf
  have hdiv :=
    surfaceCoordinateDivergence_transform_of_vectorDensityPullback
      T Ω Ω' F F' hΩ hΩ' hT_maps hT hF hF' hpull z hzΩ
  simpa [T, Ω, F, F'] using hdiv

/--
%%handwave
name:
  Local coordinate divergence transformation for the metric flux
statement:
  On the part of a chart overlap lying over an open region where the function
  is smooth, the Euclidean divergence of the metric flux transforms as a scalar
  density under the coordinate transition.
proof:
  Apply the Piola transformation formula on the open subset of the overlap
  lying over the smooth region.  The flux components are smooth there, and the
  local vector-density pullback relation supplies the transformation law.
-/
theorem surfaceMetricGradientFlux_coordinateDivergence_transform_on_overlap_of_mem_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    {U : Set X} (hU : IsOpen U)
    (f : X → ℝ) (hf : IsSmoothOnSurface U f) :
    ∀ {z : ℂ}, z ∈ e.target → e.symm z ∈ e'.source → e.symm z ∈ U →
      surfaceCoordinateDivergence
          (fun w i ↦ surfaceMetricGradientFluxInChart metric e f w i) z =
        |(fderivWithin ℝ (surfaceChartTransition e' e)
          (surfaceChartOverlapDomain e' e ∩ e.symm ⁻¹' U) z).det| *
          surfaceCoordinateDivergence
            (fun w i ↦ surfaceMetricGradientFluxInChart metric e' f w i)
            (surfaceChartTransition e' e z) := by
  intro z hz_target hz_source hzU
  let T : ℂ → ℂ := surfaceChartTransition e' e
  let Ω : Set ℂ := surfaceChartOverlapDomain e' e ∩ e.symm ⁻¹' U
  let Ω' : Set ℂ := e'.target ∩ e'.symm ⁻¹' U
  let F : ℂ → Fin 2 → ℝ :=
    fun w i ↦ surfaceMetricGradientFluxInChart metric e f w i
  let F' : ℂ → Fin 2 → ℝ :=
    fun w i ↦ surfaceMetricGradientFluxInChart metric e' f w i
  have hzΩ : z ∈ Ω := ⟨⟨hz_target, hz_source⟩, hzU⟩
  have hΩ : IsOpen Ω := by
    have hpre :
        IsOpen (e.target ∩ e.symm ⁻¹' (e'.source ∩ U)) :=
      e.isOpen_inter_preimage_symm (e'.open_source.inter hU)
    simpa [Ω, surfaceChartOverlapDomain, Set.preimage_inter,
      Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hpre
  have hΩ' : IsOpen Ω' := by
    simpa [Ω'] using e'.isOpen_inter_preimage_symm hU
  have hT_maps : Set.MapsTo T Ω Ω' := by
    intro w hw
    have hw_overlap : w ∈ surfaceChartOverlapDomain e' e := hw.1
    have htarget : T w ∈ e'.target := by
      simpa [T, surfaceChartTransition] using e'.map_source hw_overlap.2
    have hbase : e'.symm (T w) = e.symm w := by
      simpa [T, surfaceChartTransition] using e'.left_inv hw_overlap.2
    exact ⟨htarget, by simpa [hbase] using hw.2⟩
  have hT : ContDiffOn ℝ ∞ T Ω := by
    exact (surfaceChartTransition_contDiffOn_overlap X e' e _he' _he metric).mono
      (by
        intro w hw
        exact hw.1)
  have hF : ∀ i : Fin 2, ContDiffOn ℝ ∞ (fun w : ℂ ↦ F w i) Ω := by
    intro i
    have hfΩ :
        ContDiffOn ℝ ∞ (fun w : ℂ ↦ f (e.symm w)) Ω := by
      exact (hf e _he).mono (by
        intro w hw
        exact ⟨hw.1.1, hw.2⟩)
    exact surfaceMetricGradientFluxInChart_contDiffOn_of_local_contDiffOn
      metric e _he f hΩ (by
        intro w hw
        exact hw.1.1) hfΩ i
  have hF' : ∀ i : Fin 2, ContDiffOn ℝ ∞ (fun w : ℂ ↦ F' w i) Ω' := by
    intro i
    have hfΩ' :
        ContDiffOn ℝ ∞ (fun w : ℂ ↦ f (e'.symm w)) Ω' := by
      simpa [Ω'] using hf e' _he'
    exact surfaceMetricGradientFluxInChart_contDiffOn_of_local_contDiffOn
      metric e' _he' f hΩ' (by
        intro w hw
        exact hw.1) hfΩ' i
  have hpull : IsVectorDensityPullbackBy T Ω F F' := by
    simpa [T, Ω, F, F'] using
      surfaceMetricGradientFlux_vectorDensityPullback_on_overlap_of_mem_open
        metric e e' _he _he' hU f hf
  have hdiv :=
    surfaceCoordinateDivergence_transform_of_vectorDensityPullback
      T Ω Ω' F F' hΩ hΩ' hT_maps hT hF hF' hpull z hzΩ
  simpa [T, Ω, F, F'] using hdiv

/--
%%handwave
name:
  Divergence of the metric flux transforms on overlaps
statement:
  On a chart overlap, the Euclidean divergence of the Riemannian metric flux
  transforms as a density under the coordinate transition.
proof:
  This is the two-coordinate expansion of
  [the coordinate-divergence transformation law]
  (lean:JJMath.Uniformization.surfaceMetricGradientFlux_coordinateDivergence_transform_on_overlap).
-/
theorem surfaceMetricGradientFlux_divergence_transform_on_overlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    (f : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f) :
    ∀ {z : ℂ}, z ∈ e.target → e.symm z ∈ e'.source →
      (fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
          z (1 : ℂ) +
        fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
          z Complex.I) =
        |(fderivWithin ℝ (surfaceChartTransition e' e)
          (surfaceChartOverlapDomain e' e) z).det| *
          (fderiv ℝ
              (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e' f w 0)
              (surfaceChartTransition e' e z) (1 : ℂ) +
            fderiv ℝ
              (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e' f w 1)
              (surfaceChartTransition e' e z) Complex.I) := by
  intro z hz_target hz_source
  have hdiv :=
    surfaceMetricGradientFlux_coordinateDivergence_transform_on_overlap
      metric e e' _he _he' f hf hz_target hz_source
  simpa [surfaceCoordinateDivergence, Fin.sum_univ_two] using hdiv

/--
%%handwave
name:
  Divergence-form chart expressions agree on overlaps
statement:
  On the overlap of two coordinate charts, the two coordinate formulas for
  \(\rho^{-1}\partial_i(\rho g^{ij}\partial_j f)\) agree after the coordinate
  change.
proof:
  The volume density and the divergence of the metric flux both transform by
  the same absolute Jacobian determinant under a coordinate transition, so the
  determinant factors cancel in
  \(\rho^{-1}\operatorname{div}(\rho g^{-1}df)\).
-/
theorem surfaceDivergenceFormLaplaceBeltramiInChart_eq_on_overlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    (f : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f) :
    ∀ {z : ℂ}, z ∈ e.target → e.symm z ∈ e'.source →
      surfaceDivergenceFormLaplaceBeltramiInChart metric e f z =
        surfaceDivergenceFormLaplaceBeltramiInChart metric e' f (e' (e.symm z)) := by
  intro z hz_target hz_source
  let T : ℂ → ℂ := surfaceChartTransition e' e
  let J : ℝ :=
    |(fderivWithin ℝ T (surfaceChartOverlapDomain e' e) z).det|
  let z' : ℂ := T z
  let ρ : ℝ := surfaceMetricVolumeDensityInChart metric e z
  let ρ' : ℝ := surfaceMetricVolumeDensityInChart metric e' z'
  let D : ℝ :=
    fderiv ℝ
        (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
        z (1 : ℂ) +
      fderiv ℝ
        (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
        z Complex.I
  let D' : ℝ :=
    fderiv ℝ
        (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e' f w 0)
        z' (1 : ℂ) +
      fderiv ℝ
        (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e' f w 1)
        z' Complex.I
  have hz'_target : z' ∈ e'.target := by
    simpa [z', T, surfaceChartTransition] using e'.map_source hz_source
  have hρ :
      ρ = J * ρ' := by
    simpa [ρ, ρ', J, T, z'] using
      surfaceMetricVolumeDensityInChart_transform_on_overlap_real
        metric e e' _he _he' hz_target hz_source
  have hD :
      D = J * D' := by
    simpa [D, D', J, T, z'] using
      surfaceMetricGradientFlux_divergence_transform_on_overlap
        metric e e' _he _he' f hf hz_target hz_source
  have hρ_pos : 0 < ρ :=
    (surfaceMetricVolumeDensityInChart_smooth_positive X metric e _he).2
      z hz_target
  have hρ'_pos : 0 < ρ' :=
    (surfaceMetricVolumeDensityInChart_smooth_positive X metric e' _he').2
      z' hz'_target
  have hJ_pos : 0 < J := by
    have hJρ' : 0 < J * ρ' := by
      simpa [hρ] using hρ_pos
    exact pos_of_mul_pos_right (by simpa [mul_comm] using hJρ') (le_of_lt hρ'_pos)
  have hcalc : ρ⁻¹ * D = ρ'⁻¹ * D' := by
    rw [hρ, hD]
    field_simp [hJ_pos.ne', hρ'_pos.ne']
  change ρ⁻¹ * D = ρ'⁻¹ * D'
  exact hcalc

/--
%%handwave
name:
  Local agreement of divergence-form chart expressions on overlaps
statement:
  On a chart overlap, at points lying over an open region where the function is
  smooth, the two coordinate formulas for the divergence-form
  Laplace-Beltrami operator agree.
proof:
  On the open part of the overlap over the smooth region, the metric volume
  density and the Euclidean divergence of the metric flux transform by the
  same absolute Jacobian determinant.  These factors cancel in the
  divergence-form expression.
-/
theorem surfaceDivergenceFormLaplaceBeltramiInChart_eq_on_overlap_of_mem_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e e' : OpenPartialHomeomorph X ℂ)
    (_he : e ∈ atlas ℂ X) (_he' : e' ∈ atlas ℂ X)
    {U : Set X} (hU : IsOpen U)
    (f : X → ℝ) (hf : IsSmoothOnSurface U f) :
    ∀ {z : ℂ}, z ∈ e.target → e.symm z ∈ e'.source → e.symm z ∈ U →
      surfaceDivergenceFormLaplaceBeltramiInChart metric e f z =
        surfaceDivergenceFormLaplaceBeltramiInChart metric e' f (e' (e.symm z)) := by
  intro z hz_target hz_source hzU
  let T : ℂ → ℂ := surfaceChartTransition e' e
  let Ω₀ : Set ℂ := surfaceChartOverlapDomain e' e
  let Ω : Set ℂ := Ω₀ ∩ e.symm ⁻¹' U
  let J : ℝ := |(fderivWithin ℝ T Ω z).det|
  let z' : ℂ := T z
  let ρ : ℝ := surfaceMetricVolumeDensityInChart metric e z
  let ρ' : ℝ := surfaceMetricVolumeDensityInChart metric e' z'
  let D : ℝ :=
    fderiv ℝ
        (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
        z (1 : ℂ) +
      fderiv ℝ
        (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
        z Complex.I
  let D' : ℝ :=
    fderiv ℝ
        (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e' f w 0)
        z' (1 : ℂ) +
      fderiv ℝ
        (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e' f w 1)
        z' Complex.I
  have hzΩ₀ : z ∈ Ω₀ := ⟨hz_target, hz_source⟩
  have hΩ₀ : IsOpen Ω₀ := by
    simpa [Ω₀] using surfaceChartOverlapDomain_isOpen e' e
  have hΩ : IsOpen Ω := by
    have hpre :
        IsOpen (e.target ∩ e.symm ⁻¹' (e'.source ∩ U)) :=
      e.isOpen_inter_preimage_symm (e'.open_source.inter hU)
    simpa [Ω, Ω₀, surfaceChartOverlapDomain, Set.preimage_inter,
      Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hpre
  have hzΩ : z ∈ Ω := ⟨hzΩ₀, hzU⟩
  have hJ_eq :
      fderivWithin ℝ T Ω z = fderivWithin ℝ T Ω₀ z := by
    rw [fderivWithin_of_isOpen hΩ hzΩ,
      fderivWithin_of_isOpen hΩ₀ hzΩ₀]
  have hz'_target : z' ∈ e'.target := by
    simpa [z', T, surfaceChartTransition] using e'.map_source hz_source
  have hρ :
      ρ = J * ρ' := by
    simpa [ρ, ρ', J, T, Ω, Ω₀, z', hJ_eq] using
      surfaceMetricVolumeDensityInChart_transform_on_overlap_real
        metric e e' _he _he' hz_target hz_source
  have hD :
      D = J * D' := by
    have hdiv :=
      surfaceMetricGradientFlux_coordinateDivergence_transform_on_overlap_of_mem_open
        metric e e' _he _he' hU f hf hz_target hz_source hzU
    simpa [D, D', J, T, Ω, z', surfaceCoordinateDivergence,
      Fin.sum_univ_two] using hdiv
  have hρ_pos : 0 < ρ :=
    (surfaceMetricVolumeDensityInChart_smooth_positive X metric e _he).2
      z hz_target
  have hρ'_pos : 0 < ρ' :=
    (surfaceMetricVolumeDensityInChart_smooth_positive X metric e' _he').2
      z' hz'_target
  have hJ_pos : 0 < J := by
    have hJρ' : 0 < J * ρ' := by
      simpa [hρ] using hρ_pos
    exact pos_of_mul_pos_right (by simpa [mul_comm] using hJρ') (le_of_lt hρ'_pos)
  have hcalc : ρ⁻¹ * D = ρ'⁻¹ * D' := by
    rw [hρ, hD]
    field_simp [hJ_pos.ne', hρ'_pos.ne']
  change ρ⁻¹ * D = ρ'⁻¹ * D'
  exact hcalc

/--
%%handwave
name:
  Global divergence-form operator agrees with a chart expression
statement:
  On a coordinate source, the global divergence-form Laplace-Beltrami
  expression agrees with the expression written in that chart.
proof:
  The global operator is defined using the preferred chart at the point.  Apply
  [the overlap invariance of the coordinate divergence-form expression]
  (lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltramiInChart_eq_on_overlap)
  to compare that preferred chart with the requested chart.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_eq_inChart_of_mem_source
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f) :
    ∀ x ∈ e.source,
      surfaceDivergenceFormLaplaceBeltrami metric f x =
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f (e x) := by
  intro x hx
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have hc_atlas : c ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have hx_c_source : x ∈ c.source := mem_chart_source ℂ x
  have hz_target : c x ∈ c.target := c.map_source hx_c_source
  have hleft : c.symm (c x) = x := c.left_inv hx_c_source
  have hx_overlap : c.symm (c x) ∈ e.source := by
    simpa [hleft] using hx
  have hoverlap :=
    surfaceDivergenceFormLaplaceBeltramiInChart_eq_on_overlap
      metric c e hc_atlas _he f hf hz_target hx_overlap
  simpa [surfaceDivergenceFormLaplaceBeltrami, c, hleft] using hoverlap

theorem surfaceDivergenceFormLaplaceBeltrami_left_source_integral_eq_chartMeasure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (_hη_surface_support : tsupport η ⊆ e.source)
    (_hleft :
      Integrable
        (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * η x)
        measureGeometry.volume) :
    ∫ x in e.source,
        surfaceDivergenceFormLaplaceBeltrami metric f x * η x
        ∂measureGeometry.volume =
      ∫ z,
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
          η (e.symm z) ∂riemannianVolumeChartMeasure metric e := by
  refine riemannianVolume_source_integral_eq_chartMeasure_of_pointwise
    metric measureGeometry e _he
    (surfaceChart_source_nullMeasurable_volume metric measureGeometry e _he)
    (surfaceChart_aemeasurable_restrict_volume metric measureGeometry e _he)
    (surfaceDivergenceFormLaplaceBeltrami_left_chartMeasure_aestronglyMeasurable
      metric e _he f η hf hη)
    ?_
  intro x hx
  rw [surfaceDivergenceFormLaplaceBeltrami_eq_inChart_of_mem_source
    metric e _he f hf x hx]
  rw [e.left_inv hx]

/--
%%handwave
name:
  Left weak integral changes variables through one chart
statement:
  The source-localized integral of \(\Delta_g f\,\eta\) changes variables
  through the chart to the coordinate divergence-form Laplacian integrated
  against the Riemannian density on the chart image.
proof:
  Push forward the restricted Riemannian volume measure by the chart.  The
  defining volume-measure compatibility gives the density
  \(\rho\,dz\), and the Laplace-Beltrami expression is identified with the
  coordinate divergence-form expression at corresponding points.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_left_source_integral_eq_chart
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (_hη_surface_support : tsupport η ⊆ e.source)
    (_hleft :
      Integrable
        (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * η x)
        measureGeometry.volume) :
    ∫ x in e.source,
        surfaceDivergenceFormLaplaceBeltrami metric f x * η x
        ∂measureGeometry.volume =
      ∫ z in e.target,
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
          η (e.symm z) * surfaceMetricVolumeDensityInChart metric e z := by
  rw [surfaceDivergenceFormLaplaceBeltrami_left_source_integral_eq_chartMeasure
    metric measureGeometry e _he f η hf hη _hη_surface_support _hleft]
  exact riemannianVolumeChartMeasure_integral_eq_setIntegral_density
    metric e _he
    (fun z : ℂ ↦
      surfaceDivergenceFormLaplaceBeltramiInChart metric e f z * η (e.symm z))

/--
%%handwave
name:
  Left weak integral in one chart
statement:
  For a test function supported in one coordinate chart, the global integral
  of \(\Delta_g f\,\eta\) is the coordinate integral of the divergence-form
  Laplacian multiplied by the Riemannian density.
proof:
  The support condition removes the complement of the chart source.  The
  Riemannian volume measure pushes forward to Lebesgue measure on the chart
  image with density \(\rho\), and the global divergence-form operator agrees
  with its coordinate expression in the chart.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_left_integral_eq_chart
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_surface_support : tsupport η ⊆ e.source)
    (hleft :
      Integrable
        (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * η x)
        measureGeometry.volume) :
    ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * η x
        ∂measureGeometry.volume =
      ∫ z in e.target,
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
          η (e.symm z) * surfaceMetricVolumeDensityInChart metric e z := by
  rw [surfaceDivergenceFormLaplaceBeltrami_left_integral_eq_source
    metric measureGeometry e f η hη_surface_support]
  exact surfaceDivergenceFormLaplaceBeltrami_left_source_integral_eq_chart
    metric measureGeometry e _he f η hf hη hη_surface_support hleft

/--
%%handwave
name:
  Right weak integral localizes to the chart source
statement:
  If the test function is supported in a coordinate source, then the global
  integral of the metric-dual gradient pairing is already the integral over
  that source.
proof:
  Outside the chart source the test function is outside its closed support, so
  [its differential vanishes]
  (lean:JJMath.Uniformization.surfaceDifferential_eq_zero_of_notMem_tsupport).
  Hence its stored gradient is zero there, and the
  [metric-dual cotangent pairing vanishes on zero]
  (lean:JJMath.Uniformization.cotangentInner_zero_right_of_isMetricDual).
-/
theorem surfaceMetricGradientPairing_right_integral_eq_source
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ f : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) f →
        IsSurfaceDifferential f (gradient f))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (e : OpenPartialHomeomorph X ℂ)
    (f η : X → ℝ)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_surface_support : tsupport η ⊆ e.source) :
    ∫ x, gradientInner x (gradient f x) (gradient η x)
        ∂measureGeometry.volume =
      ∫ x in e.source,
        gradientInner x (gradient f x) (gradient η x)
        ∂measureGeometry.volume := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := measureGeometry.volume) (s := e.source)
    (f := fun x ↦ gradientInner x (gradient f x) (gradient η x)) ?_).symm
  intro x hx_source
  letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
  have hxη : x ∉ tsupport η := fun hx ↦ hx_source (hη_surface_support hx)
  have hgradη_zero : gradient η x = 0 :=
    surfaceDifferential_eq_zero_of_notMem_tsupport
      (gradient_is_differential η hη) hxη
  change gradientInner x (gradient f x) (gradient η x) = 0
  rw [hgradη_zero]
  exact cotangentInner_zero_right_of_isMetricDual
    metric gradientInner gradientInner_isMetricDual x (gradient f x)

/--
%%handwave
name:
  Right weak integral changes variables to coordinate volume
statement:
  The source-localized integral of the metric-dual gradient pairing changes
  variables through the chart to the coordinate inverse-metric contraction
  integrated against the coordinate Riemannian volume measure.
proof:
  Push forward the restricted Riemannian volume measure by the chart and use
  [the metric-dual pairing has the coordinate inverse-metric formula]
  (lean:JJMath.Uniformization.surfaceMetricGradientPairingInChart_eq).
-/
theorem surfaceMetricGradientPairing_right_chartMeasure_aestronglyMeasurable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (_hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (_hη : IsSmoothOnSurface (Set.univ : Set X) η) :
    AEStronglyMeasurable
      (fun z : ℂ ↦ surfaceMetricCoordinateGradientPairingInChart metric e f η z)
      (riemannianVolumeChartMeasure metric e) := by
  have hcoeff :
      ∀ i j : Fin 2,
        AEStronglyMeasurable
          (fun z : ℂ ↦ surfaceMetricInverseGramCoeffInChart metric e z i j)
          (riemannianVolumeChartMeasure metric e) :=
    fun i j ↦
      surfaceMetricInverseGramCoeffInChart_aestronglyMeasurable metric e _he i j
  have hdf :
      ∀ i : Fin 2,
        AEStronglyMeasurable
          (fun z : ℂ ↦ surfaceFunctionChartDerivativeComponent e f z i)
          (riemannianVolumeChartMeasure metric e) :=
    fun i ↦ surfaceFunctionChartDerivativeComponent_aestronglyMeasurable e f i
  have hdη :
      ∀ i : Fin 2,
        AEStronglyMeasurable
          (fun z : ℂ ↦ surfaceFunctionChartDerivativeComponent e η z i)
          (riemannianVolumeChartMeasure metric e) :=
    fun i ↦ surfaceFunctionChartDerivativeComponent_aestronglyMeasurable e η i
  simpa [surfaceMetricCoordinateGradientPairingInChart] using
    Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset (Fin 2))
      (fun i _ ↦
        Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset (Fin 2))
          (fun j _ ↦ ((hcoeff i j).mul (hdf i)).mul (hdη j)))

theorem surfaceMetricGradientPairing_right_source_integral_eq_chartMeasure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ f : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) f →
        IsSurfaceDifferential f (gradient f))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (_hη_surface_support : tsupport η ⊆ e.source)
    (_hright :
      Integrable (fun x ↦ gradientInner x (gradient f x) (gradient η x))
        measureGeometry.volume) :
    ∫ x in e.source,
        gradientInner x (gradient f x) (gradient η x)
        ∂measureGeometry.volume =
      ∫ z,
        surfaceMetricCoordinateGradientPairingInChart metric e f η z
          ∂riemannianVolumeChartMeasure metric e := by
  refine riemannianVolume_source_integral_eq_chartMeasure_of_pointwise
    metric measureGeometry e _he
    (surfaceChart_source_nullMeasurable_volume metric measureGeometry e _he)
    (surfaceChart_aemeasurable_restrict_volume metric measureGeometry e _he)
    (surfaceMetricGradientPairing_right_chartMeasure_aestronglyMeasurable
      metric e _he f η hf hη)
    ?_
  intro x hx
  have hpair :=
    surfaceMetricGradientPairingInChart_eq metric gradient gradientInner
      gradient_is_differential gradientInner_isMetricDual e _he f η hf hη
      (e x) (e.map_source hx)
  simpa [e.left_inv hx] using hpair

/--
%%handwave
name:
  Right weak integral changes variables through one chart
statement:
  The source-localized integral of the metric-dual gradient pairing changes
  variables through the chart to the coordinate inverse-metric contraction
  integrated against the Riemannian density on the chart image.
proof:
  Push forward the restricted Riemannian volume measure by the chart and use
  [the metric-dual pairing has the coordinate inverse-metric formula]
  (lean:JJMath.Uniformization.surfaceMetricGradientPairingInChart_eq).
-/
theorem surfaceMetricGradientPairing_right_source_integral_eq_chart
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ f : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) f →
        IsSurfaceDifferential f (gradient f))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (_hη_surface_support : tsupport η ⊆ e.source)
    (_hright :
      Integrable (fun x ↦ gradientInner x (gradient f x) (gradient η x))
        measureGeometry.volume) :
    ∫ x in e.source,
        gradientInner x (gradient f x) (gradient η x)
        ∂measureGeometry.volume =
      ∫ z in e.target,
        surfaceMetricCoordinateGradientPairingInChart metric e f η z *
          surfaceMetricVolumeDensityInChart metric e z := by
  rw [surfaceMetricGradientPairing_right_source_integral_eq_chartMeasure
    metric measureGeometry gradient gradientInner
    gradient_is_differential gradientInner_isMetricDual e _he f η hf hη
    _hη_surface_support _hright]
  exact riemannianVolumeChartMeasure_integral_eq_setIntegral_density
    metric e _he
    (fun z : ℂ ↦ surfaceMetricCoordinateGradientPairingInChart metric e f η z)

/--
%%handwave
name:
  Right weak integral in one chart
statement:
  For a test function supported in one coordinate chart, the global integral
  of the metric-dual gradient pairing is the coordinate integral of
  \(g^{ij}\partial_i f\,\partial_j\eta\) against the Riemannian density.
proof:
  The support condition localizes the integral to the chart source.  The
  Riemannian volume measure is written in coordinates as \(\rho\,dz\), and
  [the metric-dual pairing has the coordinate inverse-metric formula]
  (lean:JJMath.Uniformization.surfaceMetricGradientPairingInChart_eq).
-/
theorem surfaceMetricGradientPairing_right_integral_eq_chart
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ f : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) f →
        IsSurfaceDifferential f (gradient f))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_surface_support : tsupport η ⊆ e.source)
    (hright :
      Integrable (fun x ↦ gradientInner x (gradient f x) (gradient η x))
        measureGeometry.volume) :
    ∫ x, gradientInner x (gradient f x) (gradient η x)
        ∂measureGeometry.volume =
      ∫ z in e.target,
        surfaceMetricCoordinateGradientPairingInChart metric e f η z *
          surfaceMetricVolumeDensityInChart metric e z := by
  rw [surfaceMetricGradientPairing_right_integral_eq_source
    metric measureGeometry gradient gradientInner
    gradient_is_differential gradientInner_isMetricDual e f η hη
    hη_surface_support]
  exact surfaceMetricGradientPairing_right_source_integral_eq_chart
    metric measureGeometry gradient gradientInner
    gradient_is_differential gradientInner_isMetricDual e _he f η hf hη
    hη_surface_support hright

/--
%%handwave
name:
  Global integrability gives chart integrability
statement:
  If a smooth compactly supported test function is supported in a coordinate
  chart, then the global integrability of the Laplace-Beltrami term and the
  metric-dual gradient pairing implies the corresponding integrability of
  their coordinate expressions on the chart image.
proof:
  Use the chart pushforward formula for the Riemannian volume measure and the
  support condition to restrict the global integrals to the chart source.
  Then transfer them to the chart image; the pointwise coordinate formula for
  the metric-dual pairing identifies the right-hand integrand.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_chart_integrableOn_of_global
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ f : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) f →
        IsSurfaceDifferential f (gradient f))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (_hη_surface_support : tsupport η ⊆ e.source)
    (hleft :
      Integrable
        (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * η x)
        measureGeometry.volume)
    (hright :
      Integrable (fun x ↦ gradientInner x (gradient f x) (gradient η x))
        measureGeometry.volume) :
    IntegrableOn
        (fun z : ℂ ↦
          surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
            η (e.symm z) * surfaceMetricVolumeDensityInChart metric e z)
        e.target ∧
      IntegrableOn
        (fun z : ℂ ↦
          surfaceMetricCoordinateGradientPairingInChart metric e f η z *
            surfaceMetricVolumeDensityInChart metric e z)
        e.target := by
  constructor
  · let ψ : ℂ → ℝ :=
      fun z ↦ surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
        η (e.symm z)
    have hψ_int :
        Integrable ψ (riemannianVolumeChartMeasure metric e) := by
      refine riemannianVolume_source_integrable_chartMeasure_of_pointwise
        metric measureGeometry e _he
        (surfaceChart_source_nullMeasurable_volume metric measureGeometry e _he)
        (surfaceChart_aemeasurable_restrict_volume metric measureGeometry e _he)
        (surfaceDivergenceFormLaplaceBeltrami_left_chartMeasure_aestronglyMeasurable
          metric e _he f η hf hη)
        ?_ hleft.restrict
      intro x hx
      rw [surfaceDivergenceFormLaplaceBeltrami_eq_inChart_of_mem_source
        metric e _he f hf x hx]
      change surfaceDivergenceFormLaplaceBeltramiInChart metric e f (e x) *
          η x =
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f (e x) *
          η (e.symm (e x))
      rw [e.left_inv hx]
    simpa [ψ] using
      riemannianVolumeChartMeasure_integrableOn_density metric e _he ψ hψ_int
  · let ψ : ℂ → ℝ :=
      fun z ↦ surfaceMetricCoordinateGradientPairingInChart metric e f η z
    have hψ_int :
        Integrable ψ (riemannianVolumeChartMeasure metric e) := by
      refine riemannianVolume_source_integrable_chartMeasure_of_pointwise
        metric measureGeometry e _he
        (surfaceChart_source_nullMeasurable_volume metric measureGeometry e _he)
        (surfaceChart_aemeasurable_restrict_volume metric measureGeometry e _he)
        (surfaceMetricGradientPairing_right_chartMeasure_aestronglyMeasurable
          metric e _he f η hf hη)
        ?_ hright.restrict
      intro x hx
      have hpair :=
        surfaceMetricGradientPairingInChart_eq metric gradient gradientInner
          gradient_is_differential gradientInner_isMetricDual e _he f η hf hη
          (e x) (e.map_source hx)
      simpa [e.left_inv hx] using hpair
    simpa [ψ] using
      riemannianVolumeChartMeasure_integrableOn_density metric e _he ψ hψ_int

/--
%%handwave
name:
  Compact raw coordinate support
statement:
  If a compactly supported surface function has topological support contained
  in a chart source, and if the raw totalized coordinate pullback already has
  support inside the chart target, then that raw coordinate support is compact.
proof:
  This is a compatibility lemma for older statements written with the
  totalized inverse chart.  The mathematically intrinsic coordinate
  representative is the zero-extended one above; the additional support
  hypothesis compensates for totalization outside the chart image.
-/
theorem chartRepresentative_tsupport_isCompact_of_surface_tsupport_subset
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) {η : X → ℝ}
    (hη_compact : HasCompactSupportOnSurface η)
    (hη_surface_support : tsupport η ⊆ e.source)
    (hη_chart_support : tsupport (fun z : ℂ ↦ η (e.symm z)) ⊆ e.target) :
    IsCompact (tsupport (fun z : ℂ ↦ η (e.symm z))) := by
  have hη_ts_compact : IsCompact (tsupport η) := by
    simpa [HasCompactSupportOnSurface] using hη_compact
  have himage_compact : IsCompact (e '' tsupport η) :=
    hη_ts_compact.image_of_continuousOn
      (e.continuousOn.mono hη_surface_support)
  have hsubset :
      tsupport (fun z : ℂ ↦ η (e.symm z)) ⊆ e '' tsupport η := by
    intro z hz
    have hztarget : z ∈ e.target := hη_chart_support hz
    refine ⟨e.symm z, ?_, e.right_inv hztarget⟩
    by_contra hxη
    have hη_zero : η =ᶠ[𝓝 (e.symm z)] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hxη
    have hψ_zero :
        (fun w : ℂ ↦ η (e.symm w)) =ᶠ[𝓝 z] 0 :=
      (e.continuousAt_symm hztarget).tendsto.eventually hη_zero
    exact (notMem_tsupport_iff_eventuallyEq.mpr hψ_zero) hz
  exact himage_compact.of_isClosed_subset (isClosed_tsupport _) hsubset

/--
%%handwave
name:
  Chart-supported left weak integrand is coordinate-integrable
statement:
  If the coordinate representative of a smooth compactly supported test
  function has compact support inside a chart target, then
  \((\Delta_g f)\eta\) is integrable in that chart with respect to the
  coordinate Riemannian volume measure.
proof:
  The coordinate divergence-form expression is smooth on the chart target and
  the test factor has compact support there.  Hence the product is continuous
  with compact support, and the coordinate Riemannian volume measure is finite
  on compact sets.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_left_chartMeasure_integrable_of_chart_tsupport_isCompact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_chart_support :
      tsupport (fun z : ℂ ↦ η (e.symm z)) ⊆ e.target)
    (hη_chart_compact :
      IsCompact (tsupport (fun z : ℂ ↦ η (e.symm z)))) :
    Integrable
      (fun z : ℂ ↦
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
          η (e.symm z))
      (riemannianVolumeChartMeasure metric e) := by
  have hρ_smooth : ContDiffOn ℝ ∞
      (surfaceMetricVolumeDensityInChart metric e) e.target :=
    (surfaceMetricVolumeDensityInChart_smooth_positive X metric e _he).1
  have hρ_ne :
      ∀ z ∈ e.target, surfaceMetricVolumeDensityInChart metric e z ≠ 0 := by
    intro z hz
    exact ne_of_gt
      ((surfaceMetricVolumeDensityInChart_smooth_positive X metric e _he).2 z hz)
  have hρ_inv_cont : ContinuousOn
      (fun z : ℂ ↦ (surfaceMetricVolumeDensityInChart metric e z)⁻¹)
      e.target :=
    (hρ_smooth.inv hρ_ne).continuousOn
  have hD₀ : ContinuousOn
      (fun z : ℂ ↦
        fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
          z (1 : ℂ))
      e.target :=
    surfaceMetricGradientFluxInChart_fderiv_apply_continuousOn
      metric e _he f hf 0 (1 : ℂ)
  have hD₁ : ContinuousOn
      (fun z : ℂ ↦
        fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
          z Complex.I)
      e.target :=
    surfaceMetricGradientFluxInChart_fderiv_apply_continuousOn
      metric e _he f hf 1 Complex.I
  have hΔ_cont : ContinuousOn
      (fun z : ℂ ↦ surfaceDivergenceFormLaplaceBeltramiInChart metric e f z)
      e.target := by
    simpa [surfaceDivergenceFormLaplaceBeltramiInChart] using
      hρ_inv_cont.mul (hD₀.add hD₁)
  have hη_chart : ContDiffOn ℝ ∞
      (fun z : ℂ ↦ η (e.symm z)) e.target := by
    simpa using hη e _he
  have hη_cont : ContinuousOn (fun z : ℂ ↦ η (e.symm z)) e.target :=
    hη_chart.continuousOn
  have hψ_cont : ContinuousOn
      (fun z : ℂ ↦
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
          η (e.symm z))
      e.target :=
    hΔ_cont.mul hη_cont
  have hψ_support :
      tsupport
          (fun z : ℂ ↦
            surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
              η (e.symm z)) ⊆ e.target :=
    (tsupport_mul_subset_right).trans hη_chart_support
  have hψ_compact : IsCompact
      (tsupport
        (fun z : ℂ ↦
          surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
            η (e.symm z))) :=
    hη_chart_compact.of_isClosed_subset (isClosed_tsupport _)
      tsupport_mul_subset_right
  have hψ_measure :
      riemannianVolumeChartMeasure metric e
          (tsupport
            (fun z : ℂ ↦
              surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
                η (e.symm z))) ≠ (∞ : ℝ≥0∞) :=
    riemannianVolumeChartMeasure_finite_on_compact X metric e _he _
      hψ_compact hψ_support
  exact integrable_of_continuousOn_of_tsupport_subset_isCompact_of_measure_ne_top
    hψ_cont hψ_support hψ_compact hψ_measure

/--
%%handwave
name:
  Chart-supported left weak integrand is coordinate-integrable from surface support
statement:
  If a smooth compactly supported test function has surface support contained
  in a chart source, then \((\Delta_g f)\eta\) is integrable in that chart
  with respect to the coordinate Riemannian volume measure.
proof:
  Use the zero-extended coordinate representative of the test function.  Its
  support is compact and contained in the chart image, so the coordinate
  integrand with this representative is integrable.  The raw inverse-chart
  pullback agrees with the zero-extended representative almost everywhere for
  the coordinate Riemannian measure, because that measure is supported on the
  chart image.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_left_chartMeasure_integrable_of_surface_tsupport_subset
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_compact : HasCompactSupportOnSurface η)
    (hη_surface_support : tsupport η ⊆ e.source) :
    Integrable
      (fun z : ℂ ↦
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
          η (e.symm z))
      (riemannianVolumeChartMeasure metric e) := by
  let ψ₀ : ℂ → ℝ := surfaceChartRepresentative e η
  have hψ₀_support : tsupport ψ₀ ⊆ e.target := by
    simpa [ψ₀] using
      surfaceChartRepresentative_tsupport_subset_target
        e hη_compact hη_surface_support
  have hψ₀_compact : IsCompact (tsupport ψ₀) := by
    simpa [ψ₀] using
      surfaceChartRepresentative_tsupport_isCompact_of_surface_tsupport_subset
        e hη_compact hη_surface_support
  have hρ_smooth : ContDiffOn ℝ ∞
      (surfaceMetricVolumeDensityInChart metric e) e.target :=
    (surfaceMetricVolumeDensityInChart_smooth_positive X metric e _he).1
  have hρ_ne :
      ∀ z ∈ e.target, surfaceMetricVolumeDensityInChart metric e z ≠ 0 := by
    intro z hz
    exact ne_of_gt
      ((surfaceMetricVolumeDensityInChart_smooth_positive X metric e _he).2 z hz)
  have hρ_inv_cont : ContinuousOn
      (fun z : ℂ ↦ (surfaceMetricVolumeDensityInChart metric e z)⁻¹)
      e.target :=
    (hρ_smooth.inv hρ_ne).continuousOn
  have hD₀ : ContinuousOn
      (fun z : ℂ ↦
        fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 0)
          z (1 : ℂ))
      e.target :=
    surfaceMetricGradientFluxInChart_fderiv_apply_continuousOn
      metric e _he f hf 0 (1 : ℂ)
  have hD₁ : ContinuousOn
      (fun z : ℂ ↦
        fderiv ℝ
          (fun w : ℂ ↦ surfaceMetricGradientFluxInChart metric e f w 1)
          z Complex.I)
      e.target :=
    surfaceMetricGradientFluxInChart_fderiv_apply_continuousOn
      metric e _he f hf 1 Complex.I
  have hΔ_cont : ContinuousOn
      (fun z : ℂ ↦ surfaceDivergenceFormLaplaceBeltramiInChart metric e f z)
      e.target := by
    simpa [surfaceDivergenceFormLaplaceBeltramiInChart] using
      hρ_inv_cont.mul (hD₀.add hD₁)
  have hη_raw_cont : ContinuousOn (fun z : ℂ ↦ η (e.symm z)) e.target := by
    have hη_chart : ContDiffOn ℝ ∞ (fun z : ℂ ↦ η (e.symm z)) e.target := by
      simpa using hη e _he
    exact hη_chart.continuousOn
  have hψ₀_cont : ContinuousOn ψ₀ e.target :=
    hη_raw_cont.congr fun z hz ↦ surfaceChartRepresentative_apply_of_mem e η hz
  have hζ_cont : ContinuousOn
      (fun z : ℂ ↦
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f z * ψ₀ z)
      e.target :=
    hΔ_cont.mul hψ₀_cont
  have hζ_support :
      tsupport
          (fun z : ℂ ↦
            surfaceDivergenceFormLaplaceBeltramiInChart metric e f z * ψ₀ z) ⊆
        e.target :=
    (tsupport_mul_subset_right).trans hψ₀_support
  have hζ_compact : IsCompact
      (tsupport
        (fun z : ℂ ↦
          surfaceDivergenceFormLaplaceBeltramiInChart metric e f z * ψ₀ z)) :=
    hψ₀_compact.of_isClosed_subset (isClosed_tsupport _)
      tsupport_mul_subset_right
  have hζ_measure :
      riemannianVolumeChartMeasure metric e
          (tsupport
            (fun z : ℂ ↦
              surfaceDivergenceFormLaplaceBeltramiInChart metric e f z * ψ₀ z)) ≠
        (∞ : ℝ≥0∞) :=
    riemannianVolumeChartMeasure_finite_on_compact X metric e _he _
      hζ_compact hζ_support
  have hζ_int :
      Integrable
        (fun z : ℂ ↦
          surfaceDivergenceFormLaplaceBeltramiInChart metric e f z * ψ₀ z)
        (riemannianVolumeChartMeasure metric e) :=
    integrable_of_continuousOn_of_tsupport_subset_isCompact_of_measure_ne_top
      hζ_cont hζ_support hζ_compact hζ_measure
  have hac :
      riemannianVolumeChartMeasure metric e ≪
        MeasureTheory.volume.restrict e.target := by
    rw [riemannianVolumeChartMeasure]
    exact withDensity_absolutelyContinuous _ _
  have h_eq_restrict :
      (fun z : ℂ ↦
          surfaceDivergenceFormLaplaceBeltramiInChart metric e f z * ψ₀ z) =ᵐ[
        MeasureTheory.volume.restrict e.target]
        (fun z : ℂ ↦
          surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
            η (e.symm z)) := by
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with z hz
    rw [show ψ₀ z = η (e.symm z) from
      surfaceChartRepresentative_apply_of_mem e η hz]
  exact hζ_int.congr (hac.ae_eq h_eq_restrict)

/--
%%handwave
name:
  Chart-supported gradient-pairing integrand is coordinate-integrable
statement:
  If the coordinate representative of a smooth compactly supported test
  function has compact support inside a chart target, then
  \(g^{ij}\partial_i f\,\partial_j\eta\) is integrable in that chart with
  respect to the coordinate Riemannian volume measure.
proof:
  In coordinates the integrand is a finite sum of products of smooth inverse
  metric coefficients and smooth coordinate derivatives.  The derivative of
  the test function is supported in the same compact coordinate support, so
  each summand is continuous with compact support.
-/
theorem surfaceMetricCoordinateGradientPairingInChart_integrable_of_chart_tsupport_isCompact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_chart_support :
      tsupport (fun z : ℂ ↦ η (e.symm z)) ⊆ e.target)
    (hη_chart_compact :
      IsCompact (tsupport (fun z : ℂ ↦ η (e.symm z)))) :
    Integrable
      (fun z : ℂ ↦ surfaceMetricCoordinateGradientPairingInChart metric e f η z)
      (riemannianVolumeChartMeasure metric e) := by
  let ηchart : ℂ → ℝ := fun z ↦ η (e.symm z)
  have hDη_support :
      ∀ j : Fin 2,
        tsupport
            (fun z : ℂ ↦ surfaceFunctionChartDerivativeComponent e η z j) ⊆
          tsupport ηchart := by
    intro j
    simpa [ηchart, surfaceFunctionChartDerivativeComponent,
      surfaceFunctionChartDirectionalDerivative] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := fun z : ℂ ↦ η (e.symm z)) (complexCoordinateVector j))
  have hterm_int :
      ∀ i j : Fin 2,
        Integrable
          (fun z : ℂ ↦
            surfaceMetricInverseGramCoeffInChart metric e z i j *
              surfaceFunctionChartDerivativeComponent e f z i *
                surfaceFunctionChartDerivativeComponent e η z j)
          (riemannianVolumeChartMeasure metric e) := by
    intro i j
    have hcoeff_cont : ContinuousOn
        (fun z : ℂ ↦ surfaceMetricInverseGramCoeffInChart metric e z i j)
        e.target :=
      (surfaceMetricInverseGramCoeffInChart_contDiffOn metric e _he i j).continuousOn
    have hdf_cont : ContinuousOn
        (fun z : ℂ ↦ surfaceFunctionChartDerivativeComponent e f z i)
        e.target :=
      (surfaceFunctionChartDerivativeComponent_contDiffOn e _he f hf i).continuousOn
    have hdη_cont : ContinuousOn
        (fun z : ℂ ↦ surfaceFunctionChartDerivativeComponent e η z j)
        e.target :=
      (surfaceFunctionChartDerivativeComponent_contDiffOn e _he η hη j).continuousOn
    have hterm_cont : ContinuousOn
        (fun z : ℂ ↦
          surfaceMetricInverseGramCoeffInChart metric e z i j *
            surfaceFunctionChartDerivativeComponent e f z i *
              surfaceFunctionChartDerivativeComponent e η z j)
        e.target :=
      (hcoeff_cont.mul hdf_cont).mul hdη_cont
    have hterm_support :
        tsupport
            (fun z : ℂ ↦
              surfaceMetricInverseGramCoeffInChart metric e z i j *
                surfaceFunctionChartDerivativeComponent e f z i *
                  surfaceFunctionChartDerivativeComponent e η z j) ⊆
          e.target :=
      (tsupport_mul_subset_right.trans (hDη_support j)).trans hη_chart_support
    have hterm_compact : IsCompact
        (tsupport
          (fun z : ℂ ↦
            surfaceMetricInverseGramCoeffInChart metric e z i j *
              surfaceFunctionChartDerivativeComponent e f z i *
                surfaceFunctionChartDerivativeComponent e η z j)) :=
      hη_chart_compact.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_mul_subset_right.trans (hDη_support j))
    have hterm_measure :
        riemannianVolumeChartMeasure metric e
            (tsupport
              (fun z : ℂ ↦
                surfaceMetricInverseGramCoeffInChart metric e z i j *
                  surfaceFunctionChartDerivativeComponent e f z i *
                    surfaceFunctionChartDerivativeComponent e η z j)) ≠
          (∞ : ℝ≥0∞) :=
      riemannianVolumeChartMeasure_finite_on_compact X metric e _he _
        hterm_compact hterm_support
    exact integrable_of_continuousOn_of_tsupport_subset_isCompact_of_measure_ne_top
      hterm_cont hterm_support hterm_compact hterm_measure
  simpa [surfaceMetricCoordinateGradientPairingInChart] using
    integrable_finsetSum (Finset.univ : Finset (Fin 2))
      (fun i _hi ↦
        integrable_finsetSum (Finset.univ : Finset (Fin 2))
          (fun j _hj ↦ hterm_int i j))

/--
%%handwave
name:
  Chart-supported gradient-pairing integrand is coordinate-integrable from surface support
statement:
  If a smooth compactly supported test function has surface support contained
  in a chart source, then
  \(g^{ij}\partial_i f\,\partial_j\eta\) is integrable in that chart with
  respect to the coordinate Riemannian volume measure.
proof:
  Replace the coordinate representative of the test function by its
  zero-extension outside the chart image.  The derivative of this
  zero-extension has compact support controlled by the zero-extended
  representative.  The raw derivative components agree with these
  zero-extended derivatives almost everywhere for the coordinate Riemannian
  measure, because that measure is supported on the chart image.
-/
theorem surfaceMetricCoordinateGradientPairingInChart_integrable_of_surface_tsupport_subset
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_compact : HasCompactSupportOnSurface η)
    (hη_surface_support : tsupport η ⊆ e.source) :
    Integrable
      (fun z : ℂ ↦ surfaceMetricCoordinateGradientPairingInChart metric e f η z)
      (riemannianVolumeChartMeasure metric e) := by
  let ψ₀ : ℂ → ℝ := surfaceChartRepresentative e η
  let Ψ : ℂ → ℝ :=
    fun z ↦
      ∑ i : Fin 2, ∑ j : Fin 2,
        surfaceMetricInverseGramCoeffInChart metric e z i j *
          surfaceFunctionChartDerivativeComponent e f z i *
            fderiv ℝ ψ₀ z (complexCoordinateVector j)
  have hψ₀_support : tsupport ψ₀ ⊆ e.target := by
    simpa [ψ₀] using
      surfaceChartRepresentative_tsupport_subset_target
        e hη_compact hη_surface_support
  have hψ₀_compact : IsCompact (tsupport ψ₀) := by
    simpa [ψ₀] using
      surfaceChartRepresentative_tsupport_isCompact_of_surface_tsupport_subset
        e hη_compact hη_surface_support
  have hDψ₀_support :
      ∀ j : Fin 2,
        tsupport
            (fun z : ℂ ↦ fderiv ℝ ψ₀ z (complexCoordinateVector j)) ⊆
          tsupport ψ₀ := by
    intro j
    simpa [ψ₀] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := surfaceChartRepresentative e η) (complexCoordinateVector j))
  have hterm_int :
      ∀ i j : Fin 2,
        Integrable
          (fun z : ℂ ↦
            surfaceMetricInverseGramCoeffInChart metric e z i j *
              surfaceFunctionChartDerivativeComponent e f z i *
                fderiv ℝ ψ₀ z (complexCoordinateVector j))
          (riemannianVolumeChartMeasure metric e) := by
    intro i j
    have hcoeff_cont : ContinuousOn
        (fun z : ℂ ↦ surfaceMetricInverseGramCoeffInChart metric e z i j)
        e.target :=
      (surfaceMetricInverseGramCoeffInChart_contDiffOn metric e _he i j).continuousOn
    have hdf_cont : ContinuousOn
        (fun z : ℂ ↦ surfaceFunctionChartDerivativeComponent e f z i)
        e.target :=
      (surfaceFunctionChartDerivativeComponent_contDiffOn e _he f hf i).continuousOn
    have hdψ₀_cont : ContinuousOn
        (fun z : ℂ ↦ fderiv ℝ ψ₀ z (complexCoordinateVector j))
        e.target := by
      have hraw : ContinuousOn
          (fun z : ℂ ↦
            fderiv ℝ (fun w : ℂ ↦ η (e.symm w)) z
              (complexCoordinateVector j)) e.target := by
        simpa [surfaceFunctionChartDerivativeComponent,
          surfaceFunctionChartDirectionalDerivative] using
          (surfaceFunctionChartDerivativeComponent_contDiffOn
            e _he η hη j).continuousOn
      exact hraw.congr fun z hz ↦ by
        rw [show fderiv ℝ ψ₀ z =
            fderiv ℝ (fun w : ℂ ↦ η (e.symm w)) z from
          surfaceChartRepresentative_fderiv_eq_raw_of_mem e η hz]
    have hterm_cont : ContinuousOn
        (fun z : ℂ ↦
          surfaceMetricInverseGramCoeffInChart metric e z i j *
            surfaceFunctionChartDerivativeComponent e f z i *
              fderiv ℝ ψ₀ z (complexCoordinateVector j))
        e.target :=
      (hcoeff_cont.mul hdf_cont).mul hdψ₀_cont
    have hterm_support :
        tsupport
            (fun z : ℂ ↦
              surfaceMetricInverseGramCoeffInChart metric e z i j *
                surfaceFunctionChartDerivativeComponent e f z i *
                  fderiv ℝ ψ₀ z (complexCoordinateVector j)) ⊆
          e.target :=
      (tsupport_mul_subset_right.trans (hDψ₀_support j)).trans hψ₀_support
    have hterm_compact : IsCompact
        (tsupport
          (fun z : ℂ ↦
            surfaceMetricInverseGramCoeffInChart metric e z i j *
              surfaceFunctionChartDerivativeComponent e f z i *
                fderiv ℝ ψ₀ z (complexCoordinateVector j))) :=
      hψ₀_compact.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_mul_subset_right.trans (hDψ₀_support j))
    have hterm_measure :
        riemannianVolumeChartMeasure metric e
            (tsupport
              (fun z : ℂ ↦
                surfaceMetricInverseGramCoeffInChart metric e z i j *
                  surfaceFunctionChartDerivativeComponent e f z i *
                    fderiv ℝ ψ₀ z (complexCoordinateVector j))) ≠
          (∞ : ℝ≥0∞) :=
      riemannianVolumeChartMeasure_finite_on_compact X metric e _he _
        hterm_compact hterm_support
    exact integrable_of_continuousOn_of_tsupport_subset_isCompact_of_measure_ne_top
      hterm_cont hterm_support hterm_compact hterm_measure
  have hΨ_int :
      Integrable Ψ (riemannianVolumeChartMeasure metric e) := by
    simpa [Ψ] using
      integrable_finsetSum (Finset.univ : Finset (Fin 2))
        (fun i _hi ↦
          integrable_finsetSum (Finset.univ : Finset (Fin 2))
            (fun j _hj ↦ hterm_int i j))
  have hac :
      riemannianVolumeChartMeasure metric e ≪
        MeasureTheory.volume.restrict e.target := by
    rw [riemannianVolumeChartMeasure]
    exact withDensity_absolutelyContinuous _ _
  have h_eq_restrict :
      Ψ =ᵐ[MeasureTheory.volume.restrict e.target]
        (fun z : ℂ ↦
          surfaceMetricCoordinateGradientPairingInChart metric e f η z) := by
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with z hz
    change
      (∑ i : Fin 2, ∑ j : Fin 2,
        surfaceMetricInverseGramCoeffInChart metric e z i j *
          surfaceFunctionChartDerivativeComponent e f z i *
            fderiv ℝ ψ₀ z (complexCoordinateVector j)) =
        surfaceMetricCoordinateGradientPairingInChart metric e f η z
    rw [surfaceMetricCoordinateGradientPairingInChart]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    rw [show fderiv ℝ ψ₀ z (complexCoordinateVector j) =
        surfaceFunctionChartDerivativeComponent e η z j from
      surfaceChartRepresentative_derivativeComponent_eq_of_mem e η hz j]
  exact hΨ_int.congr (hac.ae_eq h_eq_restrict)

/--
%%handwave
name:
  Chart-supported weak identity
statement:
  If the test function is supported in one coordinate chart, then the global
  weak integration-by-parts identity follows from the coordinate
  divergence-form identity in that chart.
proof:
  Use the chart formula for the Riemannian volume measure to rewrite both
  global integrals as integrals over the chart image.  The Laplace-Beltrami
  term becomes the local divergence-form expression, and the metric-dual
  cotangent pairing becomes the
  [coordinate inverse-metric contraction]
  (lean:JJMath.Uniformization.surfaceMetricGradientPairingInChart_eq).
  The result is then exactly the
  [coordinate divergence-form integration-by-parts identity]
  (lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltramiInChart_integral_by_parts_of_chart_tsupport_isCompact).
-/
theorem surfaceDivergenceFormLaplaceBeltrami_chart_supported_weak_identity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ f : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) f →
        IsSurfaceDifferential f (gradient f))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_compact : HasCompactSupportOnSurface η)
    (hη_surface_support : tsupport η ⊆ e.source)
    (hη_chart_support : tsupport (fun z : ℂ ↦ η (e.symm z)) ⊆ e.target)
    (hleft :
      Integrable
        (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * η x)
        measureGeometry.volume)
    (hright :
      Integrable (fun x ↦ gradientInner x (gradient f x) (gradient η x))
        measureGeometry.volume) :
    ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * η x ∂measureGeometry.volume =
      - ∫ x, gradientInner x (gradient f x) (gradient η x)
          ∂measureGeometry.volume := by
  have hη_chart_compact :
      IsCompact (tsupport (fun z : ℂ ↦ η (e.symm z))) :=
    chartRepresentative_tsupport_isCompact_of_surface_tsupport_subset
      e hη_compact hη_surface_support hη_chart_support
  rw [surfaceDivergenceFormLaplaceBeltrami_left_integral_eq_chart
      metric measureGeometry e _he f η hf hη hη_surface_support hleft]
  rw [surfaceMetricGradientPairing_right_integral_eq_chart
      metric measureGeometry gradient gradientInner
      gradient_is_differential gradientInner_isMetricDual e _he f η hf hη
      hη_surface_support hright]
  exact surfaceDivergenceFormLaplaceBeltramiInChart_integral_by_parts_of_chart_tsupport_isCompact
    metric e _he f η hf hη hη_chart_support hη_chart_compact

/--
%%handwave
name:
  Chart-supported weak identity from surface support
statement:
  If a smooth compactly supported test function has surface support contained
  in one coordinate chart, then the global weak integration-by-parts identity
  follows from the coordinate divergence-form identity in that chart.
proof:
  Change variables in the two global integrals.  The chart weak identity is
  then exactly
  [the coordinate divergence-form integration-by-parts theorem obtained from
  surface support]
  (lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltramiInChart_integral_by_parts_of_surface_tsupport_subset).
-/
theorem surfaceDivergenceFormLaplaceBeltrami_chart_supported_weak_identity_of_surface_tsupport_subset
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ f : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) f →
        IsSurfaceDifferential f (gradient f))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_compact : HasCompactSupportOnSurface η)
    (hη_surface_support : tsupport η ⊆ e.source)
    (hleft :
      Integrable
        (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * η x)
        measureGeometry.volume)
    (hright :
      Integrable (fun x ↦ gradientInner x (gradient f x) (gradient η x))
        measureGeometry.volume) :
    ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * η x ∂measureGeometry.volume =
      - ∫ x, gradientInner x (gradient f x) (gradient η x)
          ∂measureGeometry.volume := by
  rw [surfaceDivergenceFormLaplaceBeltrami_left_integral_eq_chart
      metric measureGeometry e _he f η hf hη hη_surface_support hleft]
  rw [surfaceMetricGradientPairing_right_integral_eq_chart
      metric measureGeometry gradient gradientInner
      gradient_is_differential gradientInner_isMetricDual e _he f η hf hη
      hη_surface_support hright]
  exact surfaceDivergenceFormLaplaceBeltramiInChart_integral_by_parts_of_surface_tsupport_subset
    metric e _he f η hf hη hη_compact hη_surface_support

/--
%%handwave
name:
  Chart-supported weak identity with compact coordinate support
statement:
  If the test function is supported in one coordinate chart and its coordinate
  representative has compact support in the chart image, then the global weak
  integration-by-parts identity follows from the compactly supported
  coordinate divergence-form identity.
proof:
  Change variables in the two global integrals exactly as in the
  chart-supported weak identity.  The resulting coordinate identity is the
  compact-support chart integration-by-parts theorem.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_chart_supported_weak_identity_of_chart_tsupport_isCompact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ f : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) f →
        IsSurfaceDifferential f (gradient f))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_surface_support : tsupport η ⊆ e.source)
    (hη_chart_support : tsupport (fun z : ℂ ↦ η (e.symm z)) ⊆ e.target)
    (hη_chart_compact : IsCompact (tsupport (fun z : ℂ ↦ η (e.symm z))))
    (hleft :
      Integrable
        (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * η x)
        measureGeometry.volume)
    (hright :
      Integrable (fun x ↦ gradientInner x (gradient f x) (gradient η x))
        measureGeometry.volume) :
    ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * η x ∂measureGeometry.volume =
      - ∫ x, gradientInner x (gradient f x) (gradient η x)
          ∂measureGeometry.volume := by
  rw [surfaceDivergenceFormLaplaceBeltrami_left_integral_eq_chart
      metric measureGeometry e _he f η hf hη hη_surface_support hleft]
  rw [surfaceMetricGradientPairing_right_integral_eq_chart
      metric measureGeometry gradient gradientInner
      gradient_is_differential gradientInner_isMetricDual e _he f η hf hη
      hη_surface_support hright]
  exact surfaceDivergenceFormLaplaceBeltramiInChart_integral_by_parts_of_chart_tsupport_isCompact
    metric e _he f η hf hη hη_chart_support hη_chart_compact

/--
%%handwave
name:
  Finite localization of the weak identity
statement:
  If a test function is decomposed into finitely many localized test
  functions and both weak integrands decompose as the corresponding finite
  sums, then the weak identity for all localized pieces implies the weak
  identity for the original test function.
proof:
  Rewrite the two global integrands as finite sums, exchange finite sums with
  integrals, apply the localized identities term by term, and sum.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_finite_localization
    {ι X : Type} [Fintype ι]
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (f η : X → ℝ) (θ : ι → X → ℝ)
    (hleft_decomp :
      ∀ x : X,
        surfaceDivergenceFormLaplaceBeltrami metric f x * η x =
          ∑ i : ι,
            surfaceDivergenceFormLaplaceBeltrami metric f x * θ i x)
    (hright_decomp :
      ∀ x : X,
        gradientInner x (gradient f x) (gradient η x) =
          ∑ i : ι,
            gradientInner x (gradient f x) (gradient (θ i) x))
    (hleftθ :
      ∀ i : ι,
        Integrable
          (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ i x)
          measureGeometry.volume)
    (hrightθ :
      ∀ i : ι,
        Integrable
          (fun x ↦ gradientInner x (gradient f x) (gradient (θ i) x))
          measureGeometry.volume)
    (hθ_identity :
      ∀ i : ι,
        ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * θ i x
            ∂measureGeometry.volume =
          - ∫ x, gradientInner x (gradient f x) (gradient (θ i) x)
              ∂measureGeometry.volume) :
    ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * η x
        ∂measureGeometry.volume =
      - ∫ x, gradientInner x (gradient f x) (gradient η x)
          ∂measureGeometry.volume := by
  classical
  let L : ι → X → ℝ :=
    fun i x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ i x
  let R : ι → X → ℝ :=
    fun i x ↦ gradientInner x (gradient f x) (gradient (θ i) x)
  have hleft_sum :
      ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * η x
          ∂measureGeometry.volume =
        ∫ x, ∑ i : ι, L i x ∂measureGeometry.volume := by
    refine integral_congr_ae ?_
    exact ae_of_all _ fun x ↦ by simpa [L] using hleft_decomp x
  have hright_sum :
      ∫ x, gradientInner x (gradient f x) (gradient η x)
          ∂measureGeometry.volume =
        ∫ x, ∑ i : ι, R i x ∂measureGeometry.volume := by
    refine integral_congr_ae ?_
    exact ae_of_all _ fun x ↦ by simpa [R] using hright_decomp x
  have hleft_integral_sum :
      ∫ x, ∑ i : ι, L i x ∂measureGeometry.volume =
        ∑ i : ι, ∫ x, L i x ∂measureGeometry.volume := by
    rw [integral_finsetSum]
    intro i _hi
    exact hleftθ i
  have hright_integral_sum :
      ∫ x, ∑ i : ι, R i x ∂measureGeometry.volume =
        ∑ i : ι, ∫ x, R i x ∂measureGeometry.volume := by
    rw [integral_finsetSum]
    intro i _hi
    exact hrightθ i
  calc
    ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * η x
        ∂measureGeometry.volume
        = ∫ x, ∑ i : ι, L i x ∂measureGeometry.volume := hleft_sum
    _ = ∑ i : ι, ∫ x, L i x ∂measureGeometry.volume := hleft_integral_sum
    _ = ∑ i : ι, - ∫ x, R i x ∂measureGeometry.volume := by
      exact Finset.sum_congr rfl fun i _hi ↦ by simpa [L, R] using hθ_identity i
    _ = - ∑ i : ι, ∫ x, R i x ∂measureGeometry.volume := by
      rw [Finset.sum_neg_distrib]
    _ = - ∫ x, ∑ i : ι, R i x ∂measureGeometry.volume := by
      rw [hright_integral_sum]
    _ = - ∫ x, gradientInner x (gradient f x) (gradient η x)
          ∂measureGeometry.volume := by
      rw [hright_sum]

/--
%%handwave
name:
  Finite chart localization of the weak identity
statement:
  Suppose a compactly supported test function has been written as a finite sum
  of smooth compactly supported pieces, each supported in a coordinate chart.
  If the weak identity is known for every chart-supported piece, and the two
  weak integrands split as the corresponding finite sums, then the weak
  identity holds for the original test function.
proof:
  Apply the chart-supported weak identity to each localized test function and
  then sum the resulting equalities by
  [finite localization of the weak identity]
  (lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltrami_finite_localization).
-/
theorem surfaceDivergenceFormLaplaceBeltrami_partition_of_unity_localization_from_finite_data
    {ι X : Type} [Fintype ι]
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (f η : X → ℝ) (θ : ι → X → ℝ)
    (e : ι → OpenPartialHomeomorph X ℂ) (_he : ∀ i : ι, e i ∈ atlas ℂ X)
    (hθ_smooth : ∀ i : ι, IsSmoothOnSurface (Set.univ : Set X) (θ i))
    (hθ_compact : ∀ i : ι, HasCompactSupportOnSurface (θ i))
    (hθ_surface_support : ∀ i : ι, tsupport (θ i) ⊆ (e i).source)
    (hθ_chart_support :
      ∀ i : ι, tsupport (fun z : ℂ ↦ θ i ((e i).symm z)) ⊆ (e i).target)
    (hleft_decomp :
      ∀ x : X,
        surfaceDivergenceFormLaplaceBeltrami metric f x * η x =
          ∑ i : ι,
            surfaceDivergenceFormLaplaceBeltrami metric f x * θ i x)
    (hright_decomp :
      ∀ x : X,
        gradientInner x (gradient f x) (gradient η x) =
          ∑ i : ι,
            gradientInner x (gradient f x) (gradient (θ i) x))
    (hleftθ :
      ∀ i : ι,
        Integrable
          (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ i x)
          measureGeometry.volume)
    (hrightθ :
      ∀ i : ι,
        Integrable
          (fun x ↦ gradientInner x (gradient f x) (gradient (θ i) x))
          measureGeometry.volume)
    (hchart_supported :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
          (θ : X → ℝ),
        IsSmoothOnSurface (Set.univ : Set X) θ →
          HasCompactSupportOnSurface θ →
            tsupport θ ⊆ e.source →
              tsupport (fun z : ℂ ↦ θ (e.symm z)) ⊆ e.target →
                Integrable
                  (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ x)
                  measureGeometry.volume →
                Integrable
                  (fun x ↦ gradientInner x (gradient f x) (gradient θ x))
                  measureGeometry.volume →
                ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * θ x
                    ∂measureGeometry.volume =
                  - ∫ x, gradientInner x (gradient f x) (gradient θ x)
                      ∂measureGeometry.volume) :
    ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * η x
        ∂measureGeometry.volume =
      - ∫ x, gradientInner x (gradient f x) (gradient η x)
          ∂measureGeometry.volume := by
  refine surfaceDivergenceFormLaplaceBeltrami_finite_localization
    metric measureGeometry gradient gradientInner f η θ
    hleft_decomp hright_decomp hleftθ hrightθ ?_
  intro i
  exact hchart_supported (e i) (_he i) (θ i)
    (hθ_smooth i) (hθ_compact i) (hθ_surface_support i)
    (hθ_chart_support i) (hleftθ i) (hrightθ i)

/--
%%handwave
name:
  Finite chart localization from surface supports
statement:
  Suppose a compactly supported test function has been written as a finite sum
  of smooth compactly supported pieces, each with surface support in a
  coordinate chart.  If the weak identity is known for every such
  chart-supported piece, and the two weak integrands split as the
  corresponding finite sums, then the weak identity holds for the original
  test function.
proof:
  Apply the chart-supported weak identity to each localized test function and
  sum the resulting equalities by
  [finite localization of the weak identity]
  (lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltrami_finite_localization).
-/
theorem surfaceDivergenceFormLaplaceBeltrami_partition_of_unity_localization_from_finite_data_of_surface_support
    {ι X : Type} [Fintype ι]
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (f η : X → ℝ) (θ : ι → X → ℝ)
    (e : ι → OpenPartialHomeomorph X ℂ) (_he : ∀ i : ι, e i ∈ atlas ℂ X)
    (hθ_smooth : ∀ i : ι, IsSmoothOnSurface (Set.univ : Set X) (θ i))
    (hθ_compact : ∀ i : ι, HasCompactSupportOnSurface (θ i))
    (hθ_surface_support : ∀ i : ι, tsupport (θ i) ⊆ (e i).source)
    (hleft_decomp :
      ∀ x : X,
        surfaceDivergenceFormLaplaceBeltrami metric f x * η x =
          ∑ i : ι,
            surfaceDivergenceFormLaplaceBeltrami metric f x * θ i x)
    (hright_decomp :
      ∀ x : X,
        gradientInner x (gradient f x) (gradient η x) =
          ∑ i : ι,
            gradientInner x (gradient f x) (gradient (θ i) x))
    (hleftθ :
      ∀ i : ι,
        Integrable
          (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ i x)
          measureGeometry.volume)
    (hrightθ :
      ∀ i : ι,
        Integrable
          (fun x ↦ gradientInner x (gradient f x) (gradient (θ i) x))
          measureGeometry.volume)
    (hchart_supported :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
          (θ : X → ℝ),
        IsSmoothOnSurface (Set.univ : Set X) θ →
          HasCompactSupportOnSurface θ →
            tsupport θ ⊆ e.source →
              Integrable
                (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ x)
                measureGeometry.volume →
              Integrable
                (fun x ↦ gradientInner x (gradient f x) (gradient θ x))
                measureGeometry.volume →
              ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * θ x
                  ∂measureGeometry.volume =
                - ∫ x, gradientInner x (gradient f x) (gradient θ x)
                    ∂measureGeometry.volume) :
    ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * η x
        ∂measureGeometry.volume =
      - ∫ x, gradientInner x (gradient f x) (gradient η x)
          ∂measureGeometry.volume := by
  refine surfaceDivergenceFormLaplaceBeltrami_finite_localization
    metric measureGeometry gradient gradientInner f η θ
    hleft_decomp hright_decomp hleftθ hrightθ ?_
  intro i
  exact hchart_supported (e i) (_he i) (θ i)
    (hθ_smooth i) (hθ_compact i) (hθ_surface_support i)
    (hleftθ i) (hrightθ i)

/--
%%handwave
name:
  Finite partition localization of the weak identity
statement:
  Suppose a compactly supported test function is a finite sum of smooth
  compactly supported chart-supported test functions.  Then the weak identity
  for each localized test function implies the weak identity for the original
  test function.
proof:
  The left integrand splits by distributivity.  The right integrand splits
  because
  [the represented surface differential also splits as a finite sum]
  (lean:JJMath.Uniformization.surfaceDifferential_eq_finset_sum_of_pointwise_sum)
  and
  [a metric-dual cotangent pairing sends finite sums in its second covector to
  finite sums of pairings]
  (lean:JJMath.Uniformization.cotangentInner_finset_sum_right_of_isMetricDual).
  Then apply
  [finite chart localization of the weak identity]
  (lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltrami_partition_of_unity_localization_from_finite_data).
-/
theorem surfaceDivergenceFormLaplaceBeltrami_partition_of_unity_localization_from_finite_partition
    {ι X : Type} [Fintype ι]
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ g : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) g →
        IsSurfaceDifferential g (gradient g))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (f η : X → ℝ) (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (θ : ι → X → ℝ)
    (e : ι → OpenPartialHomeomorph X ℂ)
    (_he : ∀ i : ι, e i ∈ atlas ℂ X)
    (hθ_smooth : ∀ i : ι, IsSmoothOnSurface (Set.univ : Set X) (θ i))
    (hθ_compact : ∀ i : ι, HasCompactSupportOnSurface (θ i))
    (hθ_surface_support : ∀ i : ι, tsupport (θ i) ⊆ (e i).source)
    (hθ_chart_support :
      ∀ i : ι, tsupport (fun z : ℂ ↦ θ i ((e i).symm z)) ⊆ (e i).target)
    (hη_sum : ∀ x : X, η x = ∑ i : ι, θ i x)
    (hleftθ :
      ∀ i : ι,
        Integrable
          (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ i x)
          measureGeometry.volume)
    (hrightθ :
      ∀ i : ι,
        Integrable
          (fun x ↦ gradientInner x (gradient f x) (gradient (θ i) x))
          measureGeometry.volume)
    (hchart_supported :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
          (θ : X → ℝ),
        IsSmoothOnSurface (Set.univ : Set X) θ →
          HasCompactSupportOnSurface θ →
            tsupport θ ⊆ e.source →
              tsupport (fun z : ℂ ↦ θ (e.symm z)) ⊆ e.target →
                Integrable
                  (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ x)
                  measureGeometry.volume →
                Integrable
                  (fun x ↦ gradientInner x (gradient f x) (gradient θ x))
                  measureGeometry.volume →
                ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * θ x
                    ∂measureGeometry.volume =
                  - ∫ x, gradientInner x (gradient f x) (gradient θ x)
                      ∂measureGeometry.volume) :
    ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * η x
        ∂measureGeometry.volume =
      - ∫ x, gradientInner x (gradient f x) (gradient η x)
          ∂measureGeometry.volume := by
  have hleft_decomp :
      ∀ x : X,
        surfaceDivergenceFormLaplaceBeltrami metric f x * η x =
          ∑ i : ι,
            surfaceDivergenceFormLaplaceBeltrami metric f x * θ i x := by
    intro x
    calc
      surfaceDivergenceFormLaplaceBeltrami metric f x * η x
          = surfaceDivergenceFormLaplaceBeltrami metric f x *
              (∑ i : ι, θ i x) := by
            rw [hη_sum x]
      _ = ∑ i : ι,
            surfaceDivergenceFormLaplaceBeltrami metric f x * θ i x := by
            simpa using
              (Finset.mul_sum Finset.univ
                (fun i : ι ↦ θ i x)
                (surfaceDivergenceFormLaplaceBeltrami metric f x))
  have hgradient_sum :
      ∀ x : X, gradient η x = ∑ i : ι, gradient (θ i) x := by
    intro x
    letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
    have hsum :=
      surfaceDifferential_eq_finset_sum_of_pointwise_sum
        (s := Finset.univ) (η := η) (dη := gradient η)
        θ (fun i : ι ↦ gradient (θ i))
        (gradient_is_differential η hη)
        (fun i _hi ↦ gradient_is_differential (θ i) (hθ_smooth i))
        (by intro y; simpa using hη_sum y) x
    simpa using hsum
  have hright_decomp :
      ∀ x : X,
        gradientInner x (gradient f x) (gradient η x) =
          ∑ i : ι,
            gradientInner x (gradient f x) (gradient (θ i) x) := by
    intro x
    calc
      gradientInner x (gradient f x) (gradient η x)
          = gradientInner x (gradient f x)
              (∑ i : ι, gradient (θ i) x) := by
            rw [hgradient_sum x]
      _ = ∑ i : ι,
            gradientInner x (gradient f x) (gradient (θ i) x) := by
            simpa using
              (cotangentInner_finset_sum_right_of_isMetricDual
                metric gradientInner gradientInner_isMetricDual
                Finset.univ x (gradient f x)
                (fun i : ι ↦ gradient (θ i) x))
  exact surfaceDivergenceFormLaplaceBeltrami_partition_of_unity_localization_from_finite_data
    metric measureGeometry gradient gradientInner f η θ e _he
    hθ_smooth hθ_compact hθ_surface_support hθ_chart_support
    hleft_decomp hright_decomp hleftθ hrightθ hchart_supported

/--
%%handwave
name:
  Finite partition localization from surface supports
statement:
  Suppose a compactly supported test function is a finite sum of smooth
  compactly supported pieces, each with surface support in a coordinate
  chart.  Then the weak identity for each localized test function implies the
  weak identity for the original test function.
proof:
  The two weak integrands split exactly as in the finite partition
  localization theorem.  The only chart-support input needed is surface
  support in a chart source, because the chart identity has been proved using
  zero-extended coordinate representatives.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_partition_of_unity_localization_from_finite_partition_of_surface_support
    {ι X : Type} [Fintype ι]
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ g : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) g →
        IsSurfaceDifferential g (gradient g))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (f η : X → ℝ) (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (θ : ι → X → ℝ)
    (e : ι → OpenPartialHomeomorph X ℂ)
    (_he : ∀ i : ι, e i ∈ atlas ℂ X)
    (hθ_smooth : ∀ i : ι, IsSmoothOnSurface (Set.univ : Set X) (θ i))
    (hθ_compact : ∀ i : ι, HasCompactSupportOnSurface (θ i))
    (hθ_surface_support : ∀ i : ι, tsupport (θ i) ⊆ (e i).source)
    (hη_sum : ∀ x : X, η x = ∑ i : ι, θ i x)
    (hleftθ :
      ∀ i : ι,
        Integrable
          (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ i x)
          measureGeometry.volume)
    (hrightθ :
      ∀ i : ι,
        Integrable
          (fun x ↦ gradientInner x (gradient f x) (gradient (θ i) x))
          measureGeometry.volume)
    (hchart_supported :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
          (θ : X → ℝ),
        IsSmoothOnSurface (Set.univ : Set X) θ →
          HasCompactSupportOnSurface θ →
            tsupport θ ⊆ e.source →
              Integrable
                (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ x)
                measureGeometry.volume →
              Integrable
                (fun x ↦ gradientInner x (gradient f x) (gradient θ x))
                measureGeometry.volume →
              ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * θ x
                  ∂measureGeometry.volume =
                - ∫ x, gradientInner x (gradient f x) (gradient θ x)
                    ∂measureGeometry.volume) :
    ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * η x
        ∂measureGeometry.volume =
      - ∫ x, gradientInner x (gradient f x) (gradient η x)
          ∂measureGeometry.volume := by
  have hleft_decomp :
      ∀ x : X,
        surfaceDivergenceFormLaplaceBeltrami metric f x * η x =
          ∑ i : ι,
            surfaceDivergenceFormLaplaceBeltrami metric f x * θ i x := by
    intro x
    calc
      surfaceDivergenceFormLaplaceBeltrami metric f x * η x
          = surfaceDivergenceFormLaplaceBeltrami metric f x *
              (∑ i : ι, θ i x) := by
            rw [hη_sum x]
      _ = ∑ i : ι,
            surfaceDivergenceFormLaplaceBeltrami metric f x * θ i x := by
            simpa using
              (Finset.mul_sum Finset.univ
                (fun i : ι ↦ θ i x)
                (surfaceDivergenceFormLaplaceBeltrami metric f x))
  have hgradient_sum :
      ∀ x : X, gradient η x = ∑ i : ι, gradient (θ i) x := by
    intro x
    letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
    have hsum :=
      surfaceDifferential_eq_finset_sum_of_pointwise_sum
        (s := Finset.univ) (η := η) (dη := gradient η)
        θ (fun i : ι ↦ gradient (θ i))
        (gradient_is_differential η hη)
        (fun i _hi ↦ gradient_is_differential (θ i) (hθ_smooth i))
        (by intro y; simpa using hη_sum y) x
    simpa using hsum
  have hright_decomp :
      ∀ x : X,
        gradientInner x (gradient f x) (gradient η x) =
          ∑ i : ι,
            gradientInner x (gradient f x) (gradient (θ i) x) := by
    intro x
    calc
      gradientInner x (gradient f x) (gradient η x)
          = gradientInner x (gradient f x)
              (∑ i : ι, gradient (θ i) x) := by
            rw [hgradient_sum x]
      _ = ∑ i : ι,
            gradientInner x (gradient f x) (gradient (θ i) x) := by
            simpa using
              (cotangentInner_finset_sum_right_of_isMetricDual
                metric gradientInner gradientInner_isMetricDual
                Finset.univ x (gradient f x)
                (fun i : ι ↦ gradient (θ i) x))
  exact surfaceDivergenceFormLaplaceBeltrami_partition_of_unity_localization_from_finite_data_of_surface_support
    metric measureGeometry gradient gradientInner f η θ e _he
    hθ_smooth hθ_compact hθ_surface_support
    hleft_decomp hright_decomp hleftθ hrightθ hchart_supported

/--
%%handwave
name:
  Chart-supported weak integrands are integrable
statement:
  If a smooth test function is compactly supported in a single coordinate
  chart, then the two weak integrands appearing in the
  Laplace-Beltrami integration-by-parts identity are integrable.
proof:
  First
  [the coordinate test function has compact support]
  (lean:JJMath.Uniformization.chartRepresentative_tsupport_isCompact_of_surface_tsupport_subset).
  The left and right coordinate integrands are then
  [integrable for the coordinate volume measure]
  (lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltrami_left_chartMeasure_integrable_of_chart_tsupport_isCompact)
  and
  [integrable for the coordinate volume measure]
  (lean:JJMath.Uniformization.surfaceMetricCoordinateGradientPairingInChart_integrable_of_chart_tsupport_isCompact).
  Pull these integrability statements back to the chart source, then use the
  support condition to extend them by zero to the whole surface.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_chart_supported_weak_integrands_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ g : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) g →
        IsSurfaceDifferential g (gradient g))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f θ : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hθ : IsSmoothOnSurface (Set.univ : Set X) θ)
    (hθ_compact : HasCompactSupportOnSurface θ)
    (hθ_surface_support : tsupport θ ⊆ e.source)
    (hθ_chart_support :
      tsupport (fun z : ℂ ↦ θ (e.symm z)) ⊆ e.target) :
    Integrable
        (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ x)
        measureGeometry.volume ∧
      Integrable
        (fun x ↦ gradientInner x (gradient f x) (gradient θ x))
        measureGeometry.volume := by
  have hθ_chart_compact :
      IsCompact (tsupport (fun z : ℂ ↦ θ (e.symm z))) :=
    chartRepresentative_tsupport_isCompact_of_surface_tsupport_subset e
      hθ_compact hθ_surface_support hθ_chart_support
  have hsource_null :
      NullMeasurableSet e.source measureGeometry.volume :=
    surfaceChart_source_nullMeasurable_volume metric measureGeometry e _he
  have he_aemeas :
      AEMeasurable e (measureGeometry.volume.restrict e.source) :=
    surfaceChart_aemeasurable_restrict_volume metric measureGeometry e _he
  constructor
  · let φ : X → ℝ :=
      fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ x
    let ψ : ℂ → ℝ :=
      fun z ↦ surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
        θ (e.symm z)
    have hψ_aemeas :
        AEStronglyMeasurable ψ (riemannianVolumeChartMeasure metric e) := by
      simpa [ψ] using
        surfaceDivergenceFormLaplaceBeltrami_left_chartMeasure_aestronglyMeasurable
          metric e _he f θ hf hθ
    have hψ_int :
        Integrable ψ (riemannianVolumeChartMeasure metric e) := by
      simpa [ψ] using
        surfaceDivergenceFormLaplaceBeltrami_left_chartMeasure_integrable_of_chart_tsupport_isCompact
          metric e _he f θ hf hθ hθ_chart_support hθ_chart_compact
    have hφ_source :
        Integrable φ (measureGeometry.volume.restrict e.source) := by
      refine riemannianVolume_source_integrable_of_chartMeasure_pointwise
        metric measureGeometry e _he hsource_null he_aemeas hψ_aemeas ?_ hψ_int
      intro x hx
      change surfaceDivergenceFormLaplaceBeltrami metric f x * θ x =
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f (e x) *
          θ (e.symm (e x))
      rw [surfaceDivergenceFormLaplaceBeltrami_eq_inChart_of_mem_source
        metric e _he f hf x hx]
      rw [e.left_inv hx]
    have hφ_global : Integrable φ measureGeometry.volume :=
      integrable_of_restrict_integrable_of_forall_notMem_eq_zero hφ_source
        (fun x hx_source ↦ by
          have hθx : θ x = 0 := by
            by_contra hθx
            exact hx_source (hθ_surface_support (subset_tsupport θ hθx))
          simp [φ, hθx])
    simpa [φ] using hφ_global
  · let φ : X → ℝ :=
      fun x ↦ gradientInner x (gradient f x) (gradient θ x)
    let ψ : ℂ → ℝ :=
      fun z ↦ surfaceMetricCoordinateGradientPairingInChart metric e f θ z
    have hψ_aemeas :
        AEStronglyMeasurable ψ (riemannianVolumeChartMeasure metric e) := by
      simpa [ψ] using
        surfaceMetricGradientPairing_right_chartMeasure_aestronglyMeasurable
          metric e _he f θ hf hθ
    have hψ_int :
        Integrable ψ (riemannianVolumeChartMeasure metric e) := by
      simpa [ψ] using
        surfaceMetricCoordinateGradientPairingInChart_integrable_of_chart_tsupport_isCompact
          metric e _he f θ hf hθ hθ_chart_support hθ_chart_compact
    have hφ_source :
        Integrable φ (measureGeometry.volume.restrict e.source) := by
      refine riemannianVolume_source_integrable_of_chartMeasure_pointwise
        metric measureGeometry e _he hsource_null he_aemeas hψ_aemeas ?_ hψ_int
      intro x hx
      have hpair :=
        surfaceMetricGradientPairingInChart_eq metric gradient gradientInner
          gradient_is_differential gradientInner_isMetricDual e _he f θ hf hθ
          (e x) (e.map_source hx)
      simpa [ψ, φ, e.left_inv hx] using hpair
    have hφ_global : Integrable φ measureGeometry.volume :=
      integrable_of_restrict_integrable_of_forall_notMem_eq_zero hφ_source
        (fun x hx_source ↦ by
          letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
          have hxθ : x ∉ tsupport θ :=
            fun hxθ ↦ hx_source (hθ_surface_support hxθ)
          have hgradθ_zero : gradient θ x = 0 :=
            surfaceDifferential_eq_zero_of_notMem_tsupport
              (gradient_is_differential θ hθ) hxθ
          change gradientInner x (gradient f x) (gradient θ x) = 0
          rw [hgradθ_zero]
          exact cotangentInner_zero_right_of_isMetricDual
            metric gradientInner gradientInner_isMetricDual x (gradient f x))
    simpa [φ] using hφ_global

/--
%%handwave
name:
  Chart-supported weak integrands are integrable from surface support
statement:
  If a smooth compactly supported test function has surface support contained
  in one coordinate chart, then the two weak integrands appearing in the
  Laplace-Beltrami integration-by-parts identity are integrable.
proof:
  Use the zero-extended coordinate representative of the test function.  The
  surface support hypothesis gives compact support for that representative in
  the chart image, so the left and right coordinate integrands are
  [integrable in the chart]
  (lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltrami_left_chartMeasure_integrable_of_surface_tsupport_subset)
  and
  [integrable in the chart]
  (lean:JJMath.Uniformization.surfaceMetricCoordinateGradientPairingInChart_integrable_of_surface_tsupport_subset).
  Pull the coordinate integrability statements back through the chart, and
  extend by zero outside the chart source.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_chart_supported_weak_integrands_integrable_of_surface_tsupport_subset
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ g : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) g →
        IsSurfaceDifferential g (gradient g))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (f θ : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hθ : IsSmoothOnSurface (Set.univ : Set X) θ)
    (hθ_compact : HasCompactSupportOnSurface θ)
    (hθ_surface_support : tsupport θ ⊆ e.source) :
    Integrable
        (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ x)
        measureGeometry.volume ∧
      Integrable
        (fun x ↦ gradientInner x (gradient f x) (gradient θ x))
        measureGeometry.volume := by
  have hsource_null :
      NullMeasurableSet e.source measureGeometry.volume :=
    surfaceChart_source_nullMeasurable_volume metric measureGeometry e _he
  have he_aemeas :
      AEMeasurable e (measureGeometry.volume.restrict e.source) :=
    surfaceChart_aemeasurable_restrict_volume metric measureGeometry e _he
  constructor
  · let φ : X → ℝ :=
      fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ x
    let ψ : ℂ → ℝ :=
      fun z ↦ surfaceDivergenceFormLaplaceBeltramiInChart metric e f z *
        θ (e.symm z)
    have hψ_aemeas :
        AEStronglyMeasurable ψ (riemannianVolumeChartMeasure metric e) := by
      simpa [ψ] using
        surfaceDivergenceFormLaplaceBeltrami_left_chartMeasure_aestronglyMeasurable
          metric e _he f θ hf hθ
    have hψ_int :
        Integrable ψ (riemannianVolumeChartMeasure metric e) := by
      simpa [ψ] using
        surfaceDivergenceFormLaplaceBeltrami_left_chartMeasure_integrable_of_surface_tsupport_subset
          metric e _he f θ hf hθ hθ_compact hθ_surface_support
    have hφ_source :
        Integrable φ (measureGeometry.volume.restrict e.source) := by
      refine riemannianVolume_source_integrable_of_chartMeasure_pointwise
        metric measureGeometry e _he hsource_null he_aemeas hψ_aemeas ?_ hψ_int
      intro x hx
      change surfaceDivergenceFormLaplaceBeltrami metric f x * θ x =
        surfaceDivergenceFormLaplaceBeltramiInChart metric e f (e x) *
          θ (e.symm (e x))
      rw [surfaceDivergenceFormLaplaceBeltrami_eq_inChart_of_mem_source
        metric e _he f hf x hx]
      rw [e.left_inv hx]
    have hφ_global : Integrable φ measureGeometry.volume :=
      integrable_of_restrict_integrable_of_forall_notMem_eq_zero hφ_source
        (fun x hx_source ↦ by
          have hθx : θ x = 0 := by
            by_contra hθx
            exact hx_source (hθ_surface_support (subset_tsupport θ hθx))
          simp [φ, hθx])
    simpa [φ] using hφ_global
  · let φ : X → ℝ :=
      fun x ↦ gradientInner x (gradient f x) (gradient θ x)
    let ψ : ℂ → ℝ :=
      fun z ↦ surfaceMetricCoordinateGradientPairingInChart metric e f θ z
    have hψ_aemeas :
        AEStronglyMeasurable ψ (riemannianVolumeChartMeasure metric e) := by
      simpa [ψ] using
        surfaceMetricGradientPairing_right_chartMeasure_aestronglyMeasurable
          metric e _he f θ hf hθ
    have hψ_int :
        Integrable ψ (riemannianVolumeChartMeasure metric e) := by
      simpa [ψ] using
        surfaceMetricCoordinateGradientPairingInChart_integrable_of_surface_tsupport_subset
          metric e _he f θ hf hθ hθ_compact hθ_surface_support
    have hφ_source :
        Integrable φ (measureGeometry.volume.restrict e.source) := by
      refine riemannianVolume_source_integrable_of_chartMeasure_pointwise
        metric measureGeometry e _he hsource_null he_aemeas hψ_aemeas ?_ hψ_int
      intro x hx
      have hpair :=
        surfaceMetricGradientPairingInChart_eq metric gradient gradientInner
          gradient_is_differential gradientInner_isMetricDual e _he f θ hf hθ
          (e x) (e.map_source hx)
      simpa [ψ, φ, e.left_inv hx] using hpair
    have hφ_global : Integrable φ measureGeometry.volume :=
      integrable_of_restrict_integrable_of_forall_notMem_eq_zero hφ_source
        (fun x hx_source ↦ by
          letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
          have hxθ : x ∉ tsupport θ :=
            fun hxθ ↦ hx_source (hθ_surface_support hxθ)
          have hgradθ_zero : gradient θ x = 0 :=
            surfaceDifferential_eq_zero_of_notMem_tsupport
              (gradient_is_differential θ hθ) hxθ
          change gradientInner x (gradient f x) (gradient θ x) = 0
          rw [hgradθ_zero]
          exact cotangentInner_zero_right_of_isMetricDual
            metric gradientInner gradientInner_isMetricDual x (gradient f x))
    simpa [φ] using hφ_global

/--
%%handwave
name:
  Finite chart-supported weights localize a test function
statement:
  If finitely many smooth chart-supported weights sum to one wherever a test
  function is nonzero, then multiplying the test function by these weights
  gives a finite chart-supported smooth compact partition of the test
  function.
proof:
  Each localized test is a product of smooth functions and is compactly
  supported because the test function is compactly supported.  Its support is
  contained in the support of the corresponding weight, hence in the chosen
  chart.  The pointwise sum is
  \((\sum_i \chi_i)\eta\), which is \(\eta\) on the nonzero set of \(\eta\)
  and is zero off it.
-/
theorem finite_chart_supported_weights_localize_testFunction
    {ι X : Type} [Fintype ι]
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (η : X → ℝ)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_support : HasCompactSupportOnSurface η)
    (χ : ι → X → ℝ)
    (e : ι → OpenPartialHomeomorph X ℂ)
    (hχ_smooth : ∀ i : ι, IsSmoothOnSurface (Set.univ : Set X) (χ i))
    (hχ_surface_support : ∀ i : ι, tsupport (χ i) ⊆ (e i).source)
    (hχ_chart_support :
      ∀ i : ι, tsupport (fun z : ℂ ↦ χ i ((e i).symm z)) ⊆ (e i).target)
    (hχ_sum : ∀ x : X, η x ≠ 0 → ∑ i : ι, χ i x = 1) :
    let θ : ι → X → ℝ := fun i x ↦ χ i x * η x
    (∀ i : ι, IsSmoothOnSurface (Set.univ : Set X) (θ i)) ∧
      (∀ i : ι, HasCompactSupportOnSurface (θ i)) ∧
      (∀ i : ι, tsupport (θ i) ⊆ (e i).source) ∧
      (∀ i : ι,
        tsupport (fun z : ℂ ↦ θ i ((e i).symm z)) ⊆ (e i).target) ∧
      (∀ x : X, η x = ∑ i : ι, θ i x) := by
  classical
  intro θ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact isSmoothOnSurface_mul (hχ_smooth i) hη
  · intro i
    exact hasCompactSupportOnSurface_mul_left hη_support
  · intro i
    exact (tsupport_mul_subset_left).trans (hχ_surface_support i)
  · intro i
    exact (tsupport_mul_subset_left).trans (hχ_chart_support i)
  · intro x
    by_cases hx : η x = 0
    · simp [θ, hx]
    · calc
        η x = 1 * η x := by simp
        _ = (∑ i : ι, χ i x) * η x := by rw [hχ_sum x hx]
        _ = ∑ i : ι, χ i x * η x := by
          rw [Finset.sum_mul]
        _ = ∑ i : ι, θ i x := by
          simp [θ]

/--
%%handwave
name:
  Finite surface chart-supported weights localize a test function
statement:
  If finitely many smooth weights supported in chart sources sum to one
  wherever a test function is nonzero, then multiplying the test function by
  those weights gives a finite smooth compact partition whose zero-extended
  coordinate representatives have compact support in the corresponding chart
  images.
proof:
  The localized tests are products \(\chi_i\eta\).  Their surface supports
  lie in the chart sources because the weights do, and they are compactly
  supported because \(\eta\) is.  The zero-extended coordinate support theorem
  then gives compact support inside each chart image.
-/
theorem finite_surface_chart_supported_weights_localize_testFunction
    {ι X : Type} [Fintype ι]
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (η : X → ℝ)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_support : HasCompactSupportOnSurface η)
    (χ : ι → X → ℝ)
    (e : ι → OpenPartialHomeomorph X ℂ)
    (hχ_smooth : ∀ i : ι, IsSmoothOnSurface (Set.univ : Set X) (χ i))
    (hχ_surface_support : ∀ i : ι, tsupport (χ i) ⊆ (e i).source)
    (hχ_sum : ∀ x : X, η x ≠ 0 → ∑ i : ι, χ i x = 1) :
    let θ : ι → X → ℝ := fun i x ↦ χ i x * η x
    (∀ i : ι, IsSmoothOnSurface (Set.univ : Set X) (θ i)) ∧
      (∀ i : ι, HasCompactSupportOnSurface (θ i)) ∧
      (∀ i : ι, tsupport (θ i) ⊆ (e i).source) ∧
      (∀ i : ι,
        tsupport (surfaceChartRepresentative (e i) (θ i)) ⊆ (e i).target) ∧
      (∀ i : ι,
        IsCompact (tsupport (surfaceChartRepresentative (e i) (θ i)))) ∧
      (∀ x : X, η x = ∑ i : ι, θ i x) := by
  classical
  intro θ
  have hθ_smooth : ∀ i : ι, IsSmoothOnSurface (Set.univ : Set X) (θ i) := by
    intro i
    exact isSmoothOnSurface_mul (hχ_smooth i) hη
  have hθ_compact : ∀ i : ι, HasCompactSupportOnSurface (θ i) := by
    intro i
    exact hasCompactSupportOnSurface_mul_left hη_support
  have hθ_surface_support : ∀ i : ι, tsupport (θ i) ⊆ (e i).source := by
    intro i
    exact (tsupport_mul_subset_left).trans (hχ_surface_support i)
  refine ⟨hθ_smooth, hθ_compact, hθ_surface_support, ?_, ?_, ?_⟩
  · intro i
    exact surfaceChartRepresentative_tsupport_subset_target
      (e i) (hθ_compact i) (hθ_surface_support i)
  · intro i
    exact surfaceChartRepresentative_tsupport_isCompact_of_surface_tsupport_subset
      (e i) (hθ_compact i) (hθ_surface_support i)
  · intro x
    by_cases hx : η x = 0
    · simp [θ, hx]
    · calc
        η x = 1 * η x := by simp
        _ = (∑ i : ι, χ i x) * η x := by rw [hχ_sum x hx]
        _ = ∑ i : ι, χ i x * η x := by
          rw [Finset.sum_mul]
        _ = ∑ i : ι, θ i x := by
          simp [θ]

/--
%%handwave
name:
  Finite surface chart-supported partition near a compact set
statement:
  Around any compact set in a surface there are finitely many smooth weights
  whose supports are contained in coordinate chart sources and whose sum is
  one on the compact set.
proof:
  Use Mathlib's smooth partition of unity subordinate to chart sources over
  the closed compact set.  The partition is locally finite, so only finitely
  many topological supports meet the compact set.  At each point of the
  compact set, every nonzero partition function belongs to that finite
  subfamily, so the finite sum agrees with the partition-of-unity finsum.
-/
theorem exists_finite_surface_chart_supported_partition_of_compactSet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [SigmaCompactSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (K : Set X) (hK : IsCompact K) :
    ∃ (ι : Type) (_ : Fintype ι) (χ : ι → X → ℝ)
        (e : ι → OpenPartialHomeomorph X ℂ),
      (∀ i : ι, e i ∈ atlas ℂ X) ∧
      (∀ i : ι, IsSmoothOnSurface (Set.univ : Set X) (χ i)) ∧
      (∀ i : ι, tsupport (χ i) ⊆ (e i).source) ∧
      (∀ x ∈ K, ∑ i : ι, χ i x = 1) := by
  classical
  letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
  obtain ⟨ρ, hρ_sub⟩ :
      ∃ ρ : SmoothPartitionOfUnity K SurfaceRealModel X K,
        ρ.IsSubordinate (fun x : K ↦ (chartAt ℂ (x : X)).source) :=
    SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source_of_isClosed
      (I := SurfaceRealModel) (H := ℂ) (M := X) hK.isClosed
  let A : Set K := {i : K | (tsupport (ρ i) ∩ K).Nonempty}
  have hloc_tsupport : LocallyFinite fun i : K ↦ tsupport (ρ i) := by
    simpa [tsupport] using ρ.toPartitionOfUnity.locallyFinite.closure
  have hA_finite : A.Finite := by
    simpa [A] using hloc_tsupport.finite_nonempty_inter_compact hK
  let ι : Type := {i : K // i ∈ hA_finite.toFinset}
  letI : Fintype ι := Fintype.ofFinite ι
  refine ⟨ι, inferInstance,
    (fun i x ↦ ρ i.1 x),
    (fun i ↦ chartAt ℂ (i.1 : X)), ?_, ?_, ?_, ?_⟩
  · intro i
    exact chart_mem_atlas ℂ (i.1 : X)
  · intro i
    exact isSmoothOnSurface_of_contMDiffMap (ρ i.1)
  · intro i
    exact hρ_sub i.1
  · intro x hxK
    have hsupport_subset :
        Function.support (fun i : K ↦ ρ i x) ⊆ hA_finite.toFinset := by
      intro i hi
      exact (hA_finite.mem_toFinset).mpr
        ⟨x, subset_tsupport (ρ i) hi, hxK⟩
    have hsum_finset :
        ∑ i ∈ hA_finite.toFinset, ρ i x = 1 := by
      have hfinsum :
          ∑ᶠ i : K, ρ i x = ∑ i ∈ hA_finite.toFinset, ρ i x :=
        finsum_eq_sum_of_support_subset _ hsupport_subset
      rw [← hfinsum, ρ.sum_eq_one hxK]
    have hsum_subtype :
        ∑ i ∈ hA_finite.toFinset, ρ i x =
          ∑ i : {i : K // i ∈ hA_finite.toFinset}, ρ i.1 x :=
      Finset.sum_subtype hA_finite.toFinset (fun _ ↦ Iff.rfl)
        (fun i : K ↦ ρ i x)
    change (∑ i : {i : K // i ∈ hA_finite.toFinset}, ρ i.1 x) = 1
    rw [← hsum_subtype]
    exact hsum_finset

/--
%%handwave
name:
  Finite zero-extended chart partition of a compactly supported test
statement:
  A smooth compactly supported test function is a finite sum of smooth
  compactly supported pieces whose surface supports lie in chart sources and
  whose zero-extended coordinate representatives have compact support inside
  the corresponding chart images.
proof:
  Apply the finite surface chart-supported partition theorem to the compact
  topological support of the test function.  Multiplying the test function by
  the resulting weights gives localized pieces, and
  [the zero-extended coordinate representatives have compact support in their
  chart images]
  (lean:JJMath.Uniformization.finite_surface_chart_supported_weights_localize_testFunction).
-/
theorem exists_finite_zeroExtended_chart_supported_partition_of_testFunction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [SigmaCompactSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (η : X → ℝ)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_support : HasCompactSupportOnSurface η) :
    ∃ (ι : Type) (_ : Fintype ι) (θ : ι → X → ℝ)
        (e : ι → OpenPartialHomeomorph X ℂ),
      (∀ i : ι, e i ∈ atlas ℂ X) ∧
      (∀ i : ι, IsSmoothOnSurface (Set.univ : Set X) (θ i)) ∧
      (∀ i : ι, HasCompactSupportOnSurface (θ i)) ∧
      (∀ i : ι, tsupport (θ i) ⊆ (e i).source) ∧
      (∀ i : ι,
        tsupport (surfaceChartRepresentative (e i) (θ i)) ⊆ (e i).target) ∧
      (∀ i : ι,
        IsCompact (tsupport (surfaceChartRepresentative (e i) (θ i)))) ∧
      (∀ x : X, η x = ∑ i : ι, θ i x) := by
  have hK : IsCompact (tsupport η) := by
    simpa [HasCompactSupportOnSurface] using hη_support
  rcases exists_finite_surface_chart_supported_partition_of_compactSet
      metric (tsupport η) hK with
    ⟨ι, hι, χ, e, he, hχ_smooth, hχ_surface_support, hχ_sum⟩
  letI : Fintype ι := hι
  let θ : ι → X → ℝ := fun i x ↦ χ i x * η x
  have hχ_sum' : ∀ x : X, η x ≠ 0 → ∑ i : ι, χ i x = 1 := by
    intro x hx
    exact hχ_sum x (subset_tsupport η hx)
  have hloc :
      (∀ i : ι, IsSmoothOnSurface (Set.univ : Set X) (θ i)) ∧
        (∀ i : ι, HasCompactSupportOnSurface (θ i)) ∧
        (∀ i : ι, tsupport (θ i) ⊆ (e i).source) ∧
        (∀ i : ι,
          tsupport (surfaceChartRepresentative (e i) (θ i)) ⊆ (e i).target) ∧
        (∀ i : ι,
          IsCompact (tsupport (surfaceChartRepresentative (e i) (θ i)))) ∧
        (∀ x : X, η x = ∑ i : ι, θ i x) := by
    simpa [θ] using
      finite_surface_chart_supported_weights_localize_testFunction
        η hη hη_support χ e hχ_smooth hχ_surface_support hχ_sum'
  exact ⟨ι, hι, θ, e, he, hloc.1, hloc.2.1, hloc.2.2.1,
    hloc.2.2.2.1, hloc.2.2.2.2.1, hloc.2.2.2.2.2⟩

/--
%%handwave
name:
  Finite chart localization data from surface supports
statement:
  A smooth compactly supported test function can be decomposed into finitely
  many smooth compactly supported test functions whose surface supports lie
  in coordinate charts, and the two localized weak integrands for each piece
  are integrable.
proof:
  Use
  [a finite zero-extended chart partition of the test function]
  (lean:JJMath.Uniformization.exists_finite_zeroExtended_chart_supported_partition_of_testFunction).
  For each localized piece, apply
  [integrability of the weak integrands from surface support]
  (lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltrami_chart_supported_weak_integrands_integrable_of_surface_tsupport_subset).
-/
theorem exists_surfaceDivergenceFormLaplaceBeltrami_finite_chart_localization_data_of_surface_support
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [T2Space X] [SigmaCompactSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ g : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) g →
        IsSurfaceDifferential g (gradient g))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_support : HasCompactSupportOnSurface η) :
    ∃ (ι : Type) (_ : Fintype ι) (θ : ι → X → ℝ)
        (e : ι → OpenPartialHomeomorph X ℂ),
      (∀ i : ι, e i ∈ atlas ℂ X) ∧
      (∀ i : ι, IsSmoothOnSurface (Set.univ : Set X) (θ i)) ∧
      (∀ i : ι, HasCompactSupportOnSurface (θ i)) ∧
      (∀ i : ι, tsupport (θ i) ⊆ (e i).source) ∧
      (∀ x : X, η x = ∑ i : ι, θ i x) ∧
      (∀ i : ι,
        Integrable
          (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ i x)
          measureGeometry.volume) ∧
      (∀ i : ι,
        Integrable
          (fun x ↦ gradientInner x (gradient f x) (gradient (θ i) x))
          measureGeometry.volume) := by
  rcases exists_finite_zeroExtended_chart_supported_partition_of_testFunction
      metric η hη hη_support with
    ⟨ι, hι, θ, e, he, hθ_smooth, hθ_compact, hθ_surface_support,
      _hθ_zero_support, _hθ_zero_compact, hη_sum⟩
  letI : Fintype ι := hι
  refine ⟨ι, hι, θ, e, he, hθ_smooth, hθ_compact, hθ_surface_support,
    hη_sum, ?_, ?_⟩
  · intro i
    exact (surfaceDivergenceFormLaplaceBeltrami_chart_supported_weak_integrands_integrable_of_surface_tsupport_subset
      metric measureGeometry gradient gradientInner
      gradient_is_differential gradientInner_isMetricDual
      (e i) (he i) f (θ i) hf (hθ_smooth i) (hθ_compact i)
      (hθ_surface_support i)).1
  · intro i
    exact (surfaceDivergenceFormLaplaceBeltrami_chart_supported_weak_integrands_integrable_of_surface_tsupport_subset
      metric measureGeometry gradient gradientInner
      gradient_is_differential gradientInner_isMetricDual
      (e i) (he i) f (θ i) hf (hθ_smooth i) (hθ_compact i)
      (hθ_surface_support i)).2

/--
%%handwave
name:
  Localization by a finite chart partition
statement:
  If the weak identity is known for every smooth compactly supported test
  function whose support lies in a single chart, then it holds for every
  smooth compactly supported test function.
proof:
  Decompose the compactly supported test function into finitely many smooth
  compactly supported pieces whose surface supports lie in coordinate chart
  sources.  Apply the chart-supported identity to each term and then use
  [the resulting finite chart localization data]
  (lean:JJMath.Uniformization.exists_surfaceDivergenceFormLaplaceBeltrami_finite_chart_localization_data_of_surface_support)
  and
  [finite localization of the weak identity]
  (lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltrami_partition_of_unity_localization_from_finite_partition_of_surface_support).
-/
theorem surfaceDivergenceFormLaplaceBeltrami_partition_of_unity_localization
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [T2Space X] [SigmaCompactSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ g : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) g →
        IsSurfaceDifferential g (gradient g))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_support : HasCompactSupportOnSurface η)
    (_hleft :
      Integrable
        (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * η x)
        measureGeometry.volume)
    (_hright :
      Integrable (fun x ↦ gradientInner x (gradient f x) (gradient η x))
        measureGeometry.volume)
    (hchart_supported :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
          (θ : X → ℝ),
        IsSmoothOnSurface (Set.univ : Set X) θ →
          HasCompactSupportOnSurface θ →
            tsupport θ ⊆ e.source →
              Integrable
                (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * θ x)
                measureGeometry.volume →
              Integrable
                (fun x ↦ gradientInner x (gradient f x) (gradient θ x))
                measureGeometry.volume →
              ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * θ x
                  ∂measureGeometry.volume =
                - ∫ x, gradientInner x (gradient f x) (gradient θ x)
                    ∂measureGeometry.volume) :
    ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * η x ∂measureGeometry.volume =
      - ∫ x, gradientInner x (gradient f x) (gradient η x)
          ∂measureGeometry.volume := by
  rcases exists_surfaceDivergenceFormLaplaceBeltrami_finite_chart_localization_data_of_surface_support
    metric measureGeometry gradient gradientInner gradient_is_differential
    gradientInner_isMetricDual
    f η hf hη hη_support with
    ⟨ι, hι, θ, e, he, hθ_smooth, hθ_compact, hθ_surface_support,
      hη_sum, hleftθ, hrightθ⟩
  letI : Fintype ι := hι
  exact surfaceDivergenceFormLaplaceBeltrami_partition_of_unity_localization_from_finite_partition_of_surface_support
    metric measureGeometry gradient gradientInner
    gradient_is_differential gradientInner_isMetricDual
    f η hη θ e he
    hθ_smooth hθ_compact hθ_surface_support
    hη_sum hleftθ hrightθ hchart_supported

/--
%%handwave
name:
  Chartwise divergence identity globalizes
statement:
  The coordinate divergence-form integration-by-parts identity globalizes to
  the whole surface for compactly supported smooth test functions.
proof:
  Cover the compact support of the test function by finitely many coordinate
  charts and choose a smooth partition of unity subordinate to the cover.
  Apply the
  [coordinate divergence-form integration-by-parts identity]
  (lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltramiInChart_integral_by_parts_of_chart_tsupport_isCompact)
  to each localized test function.  The Riemannian volume measure is given in
  each chart by the density \(\rho\,dz\), and the
  [metric-dual pairing has the coordinate inverse-metric formula]
  (lean:JJMath.Uniformization.surfaceMetricGradientPairingInChart_eq).  The
  chart contributions add to the global integral, because the local volume
  measures and the divergence-form expression are compatible on overlaps.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_global_weak_identity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [T2Space X] [SigmaCompactSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ f : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) f →
        IsSurfaceDifferential f (gradient f))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner)
    (f η : X → ℝ)
    (hf : IsSmoothOnSurface (Set.univ : Set X) f)
    (hη : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_support : HasCompactSupportOnSurface η)
    (hleft :
      Integrable
        (fun x ↦ surfaceDivergenceFormLaplaceBeltrami metric f x * η x)
        measureGeometry.volume)
    (hright :
      Integrable (fun x ↦ gradientInner x (gradient f x) (gradient η x))
        measureGeometry.volume) :
    ∫ x, surfaceDivergenceFormLaplaceBeltrami metric f x * η x ∂measureGeometry.volume =
      - ∫ x, gradientInner x (gradient f x) (gradient η x)
          ∂measureGeometry.volume := by
  refine surfaceDivergenceFormLaplaceBeltrami_partition_of_unity_localization
    metric measureGeometry gradient gradientInner
    gradient_is_differential gradientInner_isMetricDual
    f η hf hη hη_support
    hleft hright ?_
  intro e he θ hθ hθ_compact hθ_surface_support hleftθ hrightθ
  exact surfaceDivergenceFormLaplaceBeltrami_chart_supported_weak_identity_of_surface_tsupport_subset
    metric measureGeometry gradient gradientInner
    gradient_is_differential gradientInner_isMetricDual e he f θ hf hθ
    hθ_compact hθ_surface_support hleftθ hrightθ

/--
%%handwave
name:
  Divergence-form Laplacian satisfies integration by parts
statement:
  The divergence-form coordinate Laplacian satisfies the global weak
  integration-by-parts identity against compactly supported smooth test
  functions.
proof:
  Work on a compact set containing the support of the test function.  Refine
  it by finitely many coordinate rectangles and a smooth partition of unity.
  In each chart, the Riemannian measure is Lebesgue measure multiplied by the
  metric density, while the operator is
  \(\rho^{-1}\partial_i(\rho g^{ij}\partial_j f)\).  The density cancels in
  the integral, and the Euclidean divergence theorem, equivalently the
  coordinate integration-by-parts theorem with vanishing boundary terms for
  compact support, gives the local identity.  The transformation law for the
  metric coefficients and volume density makes the chart contributions agree
  on overlaps.
-/
theorem surfaceDivergenceFormLaplaceBeltrami_weak
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [T2Space X] [SigmaCompactSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ f : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) f →
        IsSurfaceDifferential f (gradient f))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner) :
    IsLaplaceBeltramiForSurfaceMetric metric measureGeometry
      gradient gradientInner (surfaceDivergenceFormLaplaceBeltrami metric) := by
  intro f η hf hη hη_support hleft hright
  exact surfaceDivergenceFormLaplaceBeltrami_global_weak_identity
    metric measureGeometry gradient gradientInner
    gradient_is_differential gradientInner_isMetricDual
    f η hf hη hη_support hleft hright

/--
%%handwave
name:
  Differential geometry of a surface metric
statement:
  The differential part of the background geometry consists of the exterior
  derivative on functions, the inverse-metric pairing on covectors, and the
  Laplace-Beltrami operator, all related to the chosen metric and its volume
  measure.
-/
structure SurfaceMetricGradientGeometry (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
  (metric : SmoothRiemannianMetricOnSurface X)
  (measureGeometry : SurfaceMetricMeasureGeometry X metric) where
  /-- The differential of a real-valued function. -/
  gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ
  /-- The stored differential agrees with the manifold exterior derivative. -/
  gradient_is_differential :
    letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
    ∀ f : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) f →
      IsSurfaceDifferential f (gradient f)
  /-- The pointwise cotangent inner product, induced by the inverse metric. -/
  gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ
  /-- The cotangent pairing is symmetric. -/
  gradientInner_symm :
    ∀ x ξ η, gradientInner x ξ η = gradientInner x η ξ
  /-- The cotangent pairing is nonnegative on diagonal terms. -/
  gradientInner_nonneg :
    ∀ x ξ, 0 ≤ gradientInner x ξ ξ
  /-- The cotangent pairing is the metric-dual pairing. -/
  gradientInner_isMetricDual :
    IsCotangentInnerForSurfaceMetric metric gradientInner
  /-- The Laplace-Beltrami operator of the background metric. -/
  laplaceBeltrami : (X → ℝ) → X → ℝ
  /-- The stored Laplace-Beltrami operator is the canonical divergence-form operator. -/
  laplaceBeltrami_eq_divergence :
    laplaceBeltrami = surfaceDivergenceFormLaplaceBeltrami metric
  /-- The Laplacian is characterized by integration by parts. -/
  laplaceBeltrami_weak :
    IsLaplaceBeltramiForSurfaceMetric metric measureGeometry
      gradient gradientInner laplaceBeltrami

/--
%%handwave
name:
  Existence of the inverse-metric cotangent pairing
statement:
  A smooth Riemannian metric induces a symmetric nonnegative pointwise inner
  product on cotangent vectors, dual to the metric inner product on tangent
  vectors.
proof:
  At each point, the positive definite metric identifies the tangent plane
  with its dual by \(v \mapsto g(v,\cdot)\).  Finite-dimensional linear
  algebra gives an inverse map from covectors to tangent vectors.  Define the
  cotangent pairing by evaluating one covector on the metric-dual vector of
  the other, and use symmetry and positive definiteness of the metric.
-/
theorem exists_cotangentInnerForSurfaceMetric
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) :
    ∃ gradientInner :
      X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ,
      (∀ x ξ η, gradientInner x ξ η = gradientInner x η ξ) ∧
        (∀ x ξ, 0 ≤ gradientInner x ξ ξ) ∧
          IsCotangentInnerForSurfaceMetric g gradientInner := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let gradientInner :
      X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ :=
    fun x ξ η ↦ η (surfaceMetricDualCovector g x ξ)
  refine ⟨gradientInner, ?_, ?_, ?_⟩
  · intro x ξ η
    let vξ := surfaceMetricDualCovector g x ξ
    let vη := surfaceMetricDualCovector g x η
    have hξ := surfaceMetricDualCovector_spec g x ξ vη
    have hη := surfaceMetricDualCovector_spec g x η vξ
    calc
      gradientInner x ξ η = η vξ := rfl
      _ = g.toContMDiffRiemannianMetric.inner x vη vξ := hη
      _ = g.toContMDiffRiemannianMetric.inner x vξ vη :=
        g.toContMDiffRiemannianMetric.symm x vη vξ
      _ = ξ vη := hξ.symm
      _ = gradientInner x η ξ := rfl
  · intro x ξ
    have hξ :=
      surfaceMetricDualCovector_spec g x ξ
        (surfaceMetricDualCovector g x ξ)
    rw [show gradientInner x ξ ξ =
        ξ (surfaceMetricDualCovector g x ξ) by rfl, hξ]
    by_cases hvξ : surfaceMetricDualCovector g x ξ = 0
    · rw [hvξ]
      let B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
        g.toContMDiffRiemannianMetric.inner x
      change 0 ≤ B (0 : ℂ) (0 : ℂ)
      have hB0 : B (0 : ℂ) = 0 := B.map_zero
      rw [hB0]
      exact le_rfl
    · exact le_of_lt
        (g.toContMDiffRiemannianMetric.pos x
          (surfaceMetricDualCovector g x ξ) hvξ)
  · intro x ξ
    let vξ := surfaceMetricDualCovector g x ξ
    refine ⟨vξ, ?_, ?_⟩
    · constructor
      · exact surfaceMetricDualCovector_spec g x ξ
      · intro η
        rfl
    · intro v hv
      exact surfaceMetricDualCovector_unique g x ξ hv.1

/--
%%handwave
name:
  Existence of the Laplace-Beltrami operator
statement:
  Given the metric volume measure, exterior derivative, and cotangent pairing,
  there is a Laplace-Beltrami operator characterized weakly by integration by
  parts against compactly supported smooth test functions.
proof:
  In local coordinates, define the operator by the usual divergence-form
  expression determined by the metric coefficients and volume density.  The
  coordinate expressions agree on overlaps by tensoriality of the metric and
  the volume measure.  The
  [divergence-form coordinate operator satisfies the global weak
  identity](lean:JJMath.Uniformization.surfaceDivergenceFormLaplaceBeltrami_weak), by
  reducing compactly supported tests to the Euclidean divergence theorem or
  coordinate integration by parts in charts.
-/
theorem exists_laplaceBeltramiForSurfaceMetric
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [T2Space X] [SigmaCompactSpace X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X metric)
    (gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ)
    (gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ)
    (gradient_is_differential :
      letI : IsManifold SurfaceRealModel ∞ X := metric.isManifold_real
      ∀ f : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) f →
        IsSurfaceDifferential f (gradient f))
    (gradientInner_isMetricDual :
      IsCotangentInnerForSurfaceMetric metric gradientInner) :
    ∃ laplaceBeltrami : (X → ℝ) → X → ℝ,
      IsLaplaceBeltramiForSurfaceMetric metric measureGeometry
        gradient gradientInner laplaceBeltrami := by
  exact ⟨surfaceDivergenceFormLaplaceBeltrami metric,
    surfaceDivergenceFormLaplaceBeltrami_weak metric measureGeometry
      gradient gradientInner gradient_is_differential gradientInner_isMetricDual⟩

/--
%%handwave
name:
  Background surface geometry for energy
statement:
  A background geometry for the energy method consists of a smooth Riemannian
  metric, its Riemannian volume measure, and the differential operators
  induced by that metric.
-/
structure BackgroundSurfaceMetricOnSurface (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] where
  /-- The underlying smooth Riemannian metric on the real tangent bundle. -/
  metric : SmoothRiemannianMetricOnSurface X
  /-- The measure part of the geometry. -/
  measureGeometry : SurfaceMetricMeasureGeometry X metric
  /-- The gradient, cotangent pairing, and Laplace-Beltrami operator. -/
  gradientGeometry : SurfaceMetricGradientGeometry X metric measureGeometry

namespace BackgroundSurfaceMetricOnSurface

/-- The Riemannian area measure. -/
def volume {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) : Measure X :=
  g.measureGeometry.volume

/-- The area measure is smooth and positive in coordinates. -/
theorem volume_smooth_positive {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) :
    SmoothPositiveAreaMeasureOnSurface X g.volume :=
  g.measureGeometry.smoothPositive

/-- The area measure is the Riemannian volume measure of the metric. -/
theorem volume_isRiemannian {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) :
    IsRiemannianVolumeMeasureOnSurface g.metric g.volume :=
  g.measureGeometry.volume_isRiemannian

/-- The background area measure is finite on compact sets. -/
theorem volume_isFiniteMeasureOnCompacts {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) :
    IsFiniteMeasureOnCompacts g.volume :=
  g.measureGeometry.isFiniteMeasureOnCompacts


/-- The weak-gradient representative of a smooth function. -/
def gradient {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) : (X → ℝ) → X → ℂ →L[ℝ] ℝ :=
  g.gradientGeometry.gradient

/-- The pointwise cotangent inner product. -/
def gradientInner {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) :
    X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ :=
  g.gradientGeometry.gradientInner

/-- The cotangent pairing is symmetric. -/
theorem gradientInner_symm {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) :
    ∀ x ξ η, g.gradientInner x ξ η = g.gradientInner x η ξ :=
  g.gradientGeometry.gradientInner_symm

/-- The cotangent pairing is nonnegative on diagonal terms. -/
theorem gradientInner_nonneg {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) :
    ∀ x ξ, 0 ≤ g.gradientInner x ξ ξ :=
  g.gradientGeometry.gradientInner_nonneg

/-- The cotangent pairing is induced by the inverse metric. -/
theorem gradientInner_isMetricDual {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) :
    IsCotangentInnerForSurfaceMetric g.metric g.gradientInner :=
  g.gradientGeometry.gradientInner_isMetricDual

/-- The Laplace-Beltrami operator of the background metric. -/
def laplaceBeltrami {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) : (X → ℝ) → X → ℝ :=
  g.gradientGeometry.laplaceBeltrami

/--
%%handwave
name:
  Background Laplace–Beltrami operator in divergence form
statement:
  For a background surface metric \(g\), the stored Laplace–Beltrami
  operator is the canonical divergence-form operator:
  \[
    \Delta_g f
      =\rho^{-1}\partial_i\!\left(\rho g^{ij}\partial_jf\right),
    \qquad \rho=\sqrt{\det(g_{ij})}.
  \]
proof:
  The background gradient geometry is constructed with this divergence-form
  operator, and its defining compatibility identifies the stored
  Laplace–Beltrami operator with that formula.
-/
theorem laplaceBeltrami_eq_divergence {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) :
    g.laplaceBeltrami = surfaceDivergenceFormLaplaceBeltrami g.metric :=
  g.gradientGeometry.laplaceBeltrami_eq_divergence

/-- The Laplacian is characterized by integration by parts. -/
theorem laplaceBeltrami_weak {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) :
    IsLaplaceBeltramiForSurfaceMetric g.metric g.measureGeometry
      g.gradient g.gradientInner g.laplaceBeltrami :=
  g.gradientGeometry.laplaceBeltrami_weak

end BackgroundSurfaceMetricOnSurface

/--
%%handwave
name:
  Smooth metrics supply their Riemannian volume
statement:
  On a surface equipped with its Borel measurable structure, a smooth
  Riemannian metric determines its smooth positive Riemannian volume measure.
  proof:
  In coordinates, the density is the square root of the determinant of the
  metric Gram matrix.  These coordinate densities agree on overlaps by the
  change-of-variables formula, and therefore define a global measure.
-/
theorem smoothRiemannianMetricOnSurface_induces_measure_geometry
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [T2Space X] [Nonempty X]
    (g : SmoothRiemannianMetricOnSurface X) :
    Nonempty (SurfaceMetricMeasureGeometry X g) := by
  rcases exists_riemannianVolumeMeasureOnSurface X g with ⟨μ, hμ⟩
  exact ⟨SurfaceMetricMeasureGeometry.mk
    (inferInstance : OpensMeasurableSpace X) μ hμ⟩

/--
%%handwave
name:
  Smooth metrics supply their differential operators
statement:
  Given a smooth metric and its Riemannian volume measure, the metric
  determines the exterior derivative on functions, the inverse-metric pairing
  on covectors, and the Laplace-Beltrami operator.
proof:
  Use
  [the exterior derivative of a smooth surface function is its surface
  differential](lean:JJMath.Uniformization.surfaceExteriorDerivative_isSurfaceDifferential)
  for the gradient operator.  The metric supplies
  [a symmetric nonnegative inverse-metric cotangent
  pairing](lean:JJMath.Uniformization.exists_cotangentInnerForSurfaceMetric).
  Finally choose
  [the Laplace-Beltrami operator characterized by integration by
  parts](lean:JJMath.Uniformization.exists_laplaceBeltramiForSurfaceMetric)
  and assemble the differential-geometry structure.
-/
theorem smoothRiemannianMetricOnSurface_induces_gradient_geometry
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [T2Space X] [SigmaCompactSpace X]
    (g : SmoothRiemannianMetricOnSurface X)
    (μg : SurfaceMetricMeasureGeometry X g) :
    Nonempty (SurfaceMetricGradientGeometry X g μg) := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let gradient : (X → ℝ) → X → ℂ →L[ℝ] ℝ :=
    fun f ↦ surfaceExteriorDerivative f
  have gradient_is_differential :
      ∀ f : X → ℝ, IsSmoothOnSurface (Set.univ : Set X) f →
        IsSurfaceDifferential f (gradient f) :=
    fun f hf ↦ surfaceExteriorDerivative_isSurfaceDifferential hf
  rcases exists_cotangentInnerForSurfaceMetric X g with
    ⟨gradientInner, hinner_symm, hinner_nonneg, hinner_dual⟩
  let laplaceBeltrami : (X → ℝ) → X → ℝ :=
    surfaceDivergenceFormLaplaceBeltrami g
  have hlaplace :
      IsLaplaceBeltramiForSurfaceMetric g μg
        gradient gradientInner laplaceBeltrami :=
    surfaceDivergenceFormLaplaceBeltrami_weak g μg gradient gradientInner
      gradient_is_differential hinner_dual
  exact ⟨
    { gradient := gradient
      gradient_is_differential := gradient_is_differential
      gradientInner := gradientInner
      gradientInner_symm := hinner_symm
      gradientInner_nonneg := hinner_nonneg
      gradientInner_isMetricDual := hinner_dual
      laplaceBeltrami := laplaceBeltrami
      laplaceBeltrami_eq_divergence := rfl
      laplaceBeltrami_weak := hlaplace }⟩

/--
%%handwave
name:
  Smooth metrics supply the energy background
statement:
  On a surface equipped with its Borel measurable structure, a smooth
  Riemannian metric supplies the volume measure, Laplace-Beltrami operator,
  and cotangent pairing used in the Green-energy functional.
proof:
  The Riemannian metric determines its volume density, the musical isomorphism
  on cotangent vectors, and the Laplace-Beltrami operator
  \(\Delta_g=\operatorname{div}_g\nabla_g\).  In surface coordinates these
  have smooth coefficients and the pointwise cotangent pairing is symmetric
  and positive definite.
-/
theorem smoothRiemannianMetricOnSurface_induces_energy_background_metric
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [T2Space X] [SigmaCompactSpace X] [Nonempty X]
    (g : SmoothRiemannianMetricOnSurface X) :
    Nonempty (BackgroundSurfaceMetricOnSurface X) := by
  rcases smoothRiemannianMetricOnSurface_induces_measure_geometry X g with ⟨μg⟩
  rcases smoothRiemannianMetricOnSurface_induces_gradient_geometry X g μg with ⟨gradGeom⟩
  exact ⟨{ metric := g, measureGeometry := μg, gradientGeometry := gradGeom }⟩

/--
%%handwave
name:
  Background metrics for the energy method exist
statement:
  Every Riemann surface equipped with its Borel measurable
  structure admits a smooth background metric suitable for the energy
  construction.
proof:
  First obtain
  [a smooth Riemannian metric](lean:JJMath.Uniformization.riemannSurface_has_smoothRiemannianMetric).
  Then use that
  [a smooth Riemannian metric supplies the volume measure, Laplace-Beltrami
  operator, and cotangent pairing](lean:JJMath.Uniformization.smoothRiemannianMetricOnSurface_induces_energy_background_metric).
-/
theorem riemannSurface_has_energy_background_metric
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    [RiemannSurface X] :
    Nonempty (BackgroundSurfaceMetricOnSurface X) := by
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  haveI : Nonempty X := PathConnectedSpace.nonempty
  rcases riemannSurface_has_smoothRiemannianMetric X with ⟨g⟩
  exact smoothRiemannianMetricOnSurface_induces_energy_background_metric X g

/--
%%handwave
name:
  Metric conformal in holomorphic coordinates
statement:
  A smooth surface metric is conformal to the complex structure when, in every
  holomorphic coordinate, the volume density times the inverse metric matrix
  is the identity matrix.
-/
def SurfaceMetricConformalToComplexStructure {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (metric : SmoothRiemannianMetricOnSurface X) : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) (z : ℂ),
    z ∈ e.target →
      ∀ i j : Fin 2,
        surfaceMetricVolumeDensityInChart metric e z *
            surfaceMetricInverseGramCoeffInChart metric e z i j =
          if i = j then 1 else 0

/--
%%handwave
name:
  Background metric conformal in holomorphic coordinates
statement:
  A background metric for the energy method is conformal when its underlying
  smooth Riemannian metric is conformal to the complex structure.
-/
def BackgroundSurfaceMetricConformalToComplexStructure {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) : Prop :=
  SurfaceMetricConformalToComplexStructure g.metric

/--
%%handwave
name:
  Scalar Gram matrices give Euclidean divergence coefficients
statement:
  If the coordinate Gram matrix of a surface metric is a positive scalar
  multiple of the identity, then the divergence-form coefficient
  \(\rho g^{ij}\) is the Euclidean identity matrix.
proof:
  The determinant of the Gram matrix is \(r^2\), the volume density is
  \(\sqrt{r^2}=r\), and the inverse Gram matrix is \(r^{-1}\) times the
  identity.
-/
theorem surfaceMetricConformalCoefficient_eq_of_scalar_gram
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ) (r : ℝ) (hr : 0 < r) :
    ((g.toContMDiffRiemannianMetric.inner (e.symm z))
      ((surfaceChartTangentMap e z) (1 : ℂ)))
      ((surfaceChartTangentMap e z) (1 : ℂ)) = r →
    ((g.toContMDiffRiemannianMetric.inner (e.symm z))
      ((surfaceChartTangentMap e z) Complex.I))
      ((surfaceChartTangentMap e z) Complex.I) = r →
    ((g.toContMDiffRiemannianMetric.inner (e.symm z))
      ((surfaceChartTangentMap e z) (1 : ℂ)))
      ((surfaceChartTangentMap e z) Complex.I) = 0 →
    ((g.toContMDiffRiemannianMetric.inner (e.symm z))
      ((surfaceChartTangentMap e z) Complex.I))
      ((surfaceChartTangentMap e z) (1 : ℂ)) = 0 →
    ∀ i j : Fin 2,
      surfaceMetricVolumeDensityInChart g e z *
          surfaceMetricInverseGramCoeffInChart g e z i j =
        if i = j then 1 else 0 := by
  intro h11 h22 h12 h21 i j
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let A := surfaceChartTangentMap e z
  let b := g.toContMDiffRiemannianMetric.inner (e.symm z)
  let v₁ : TangentSpace SurfaceRealModel (e.symm z) := A (1 : ℂ)
  let v₂ : TangentSpace SurfaceRealModel (e.symm z) := A Complex.I
  have hdet : surfaceMetricGramDetInChart g e z = r * r := by
    simp [surfaceMetricGramDetInChart, h11, h22, h12, h21]
  have hvol : surfaceMetricVolumeDensityInChart g e z = r := by
    rw [surfaceMetricVolumeDensityInChart, hdet]
    have hr_sq : r * r = r ^ 2 := by ring
    rw [hr_sq, Real.sqrt_sq_eq_abs, abs_of_pos hr]
  have hr_ne : r ≠ 0 := ne_of_gt hr
  fin_cases i <;> fin_cases j
  · simp [surfaceMetricInverseGramCoeffInChart, hvol, hdet, h22, hr_ne]
  · simp [surfaceMetricInverseGramCoeffInChart, hvol, hdet, h12]
  · simp [surfaceMetricInverseGramCoeffInChart, hvol, hdet, h21]
  · simp [surfaceMetricInverseGramCoeffInChart, hvol, hdet, h11, hr_ne]

/--
%%handwave
name:
  Holomorphic tangent trivializations are nonzero complex-linear maps
statement:
  In a Riemann surface, the tangent-coordinate map associated to a
  holomorphic tangent trivialization is complex-linear and nonzero in the
  \(1\)-direction.
proof:
  The tangent trivialization comes from a holomorphic coordinate chart.  Its
  fiber coordinate map is the derivative of a holomorphic coordinate change,
  hence complex-linear.  Since coordinate changes are local biholomorphisms,
  this derivative has an inverse and is therefore nonzero.
-/
theorem tangentTrivializationAt_continuousLinearMapAt_complex_linear_nonzero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] (x₀ y : X)
    (hy : y ∈
      (trivializationAt ℂ (TangentSpace SurfaceRealModel : X → Type) x₀).baseSet) :
    (trivializationAt ℂ (TangentSpace SurfaceRealModel : X → Type) x₀).continuousLinearMapAt
        ℝ y Complex.I =
        Complex.I *
          (trivializationAt ℂ (TangentSpace SurfaceRealModel : X → Type) x₀).continuousLinearMapAt
            ℝ y (1 : ℂ) ∧
      (trivializationAt ℂ (TangentSpace SurfaceRealModel : X → Type) x₀).continuousLinearMapAt
          ℝ y (1 : ℂ) ≠ 0 := by
  let e₀ : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀
  let ey : OpenPartialHomeomorph X ℂ := chartAt ℂ y
  let z : ℂ := ey y
  have hy₀ : y ∈ e₀.source := by
    simpa [e₀] using hy
  have hyy : y ∈ ey.source := by
    simp [ey]
  have hz_sourceC : z ∈ ((𝓘(ℂ)).extendCoordChange ey e₀).source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter]
    refine ⟨y, ⟨hyy, hy₀⟩, ?_⟩
    simp [z, ey]
  have hsource_eqC :
      ((𝓘(ℂ)).extendCoordChange ey e₀).source =
        ey.target ∩ ey.symm ⁻¹' e₀.source := by
    simp [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source, e₀, ey]
  have hsource_openC :
      IsOpen ((𝓘(ℂ)).extendCoordChange ey e₀).source := by
    rw [hsource_eqC]
    exact ey.isOpen_inter_preimage_symm e₀.open_source
  have hcomplex :
      ContDiffOn ℂ ⊤ ((𝓘(ℂ)).extendCoordChange ey e₀)
        ((𝓘(ℂ)).extendCoordChange ey e₀).source :=
    (𝓘(ℂ)).contDiffOn_extendCoordChange
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ⊤) y)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ⊤) x₀)
  have hdiffC :
      DifferentiableWithinAt ℂ ((𝓘(ℂ)).extendCoordChange ey e₀)
        ((𝓘(ℂ)).extendCoordChange ey e₀).source z :=
    hcomplex.differentiableOn (by simp) z hz_sourceC
  have huniqueR :
      UniqueDiffWithinAt ℝ ((𝓘(ℂ)).extendCoordChange ey e₀).source z :=
    hsource_openC.uniqueDiffWithinAt hz_sourceC
  have hcr_source :
      fderivWithin ℝ ((𝓘(ℂ)).extendCoordChange ey e₀)
          ((𝓘(ℂ)).extendCoordChange ey e₀).source z Complex.I =
        Complex.I •
          fderivWithin ℝ ((𝓘(ℂ)).extendCoordChange ey e₀)
            ((𝓘(ℂ)).extendCoordChange ey e₀).source z (1 : ℂ) :=
    ((differentiableWithinAt_complex_iff_differentiableWithinAt_real
      huniqueR).1 hdiffC).2
  have hsource_memC : ((𝓘(ℂ)).extendCoordChange ey e₀).source ∈ 𝓝 z :=
    hsource_openC.mem_nhds hz_sourceC
  have hsource_memC' : ey.target ∩ ey.symm ⁻¹' e₀.source ∈ 𝓝 z := by
    simpa [hsource_eqC] using hsource_memC
  have hcr_fderiv :
      fderiv ℝ ((𝓘(ℂ)).extendCoordChange ey e₀) z Complex.I =
        Complex.I * fderiv ℝ ((𝓘(ℂ)).extendCoordChange ey e₀) z (1 : ℂ) := by
    have hcr_source' :
        fderivWithin ℝ (fun w : ℂ => e₀ (ey.symm w))
            (ey.target ∩ ey.symm ⁻¹' e₀.source) z Complex.I =
          Complex.I *
            fderivWithin ℝ (fun w : ℂ => e₀ (ey.symm w))
              (ey.target ∩ ey.symm ⁻¹' e₀.source) z (1 : ℂ) := by
      simpa [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source,
        smul_eq_mul, e₀, ey] using hcr_source
    rw [fderivWithin_of_mem_nhds hsource_memC'] at hcr_source'
    simpa [ModelWithCorners.extendCoordChange, e₀, ey] using hcr_source'
  have hmap_eq :
      (trivializationAt ℂ (TangentSpace SurfaceRealModel : X → Type) x₀).continuousLinearMapAt
          ℝ y =
        fderiv ℝ ((𝓘(ℂ)).extendCoordChange ey e₀) z := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (I := SurfaceRealModel) hy₀]
    simp [SurfaceRealModel, ModelWithCorners.extendCoordChange,
      e₀, ey, z]
  constructor
  · rw [hmap_eq]
    exact hcr_fderiv
  · have hz_sourceR : z ∈ (SurfaceRealModel.extendCoordChange ey e₀).source := by
      simpa [SurfaceRealModel] using hz_sourceC
    have hinv_source :
        (fderivWithin ℝ (SurfaceRealModel.extendCoordChange ey e₀)
          (SurfaceRealModel.extendCoordChange ey e₀).source z).IsInvertible :=
      ModelWithCorners.isInvertible_fderivWithin_extendCoordChange
        (I := SurfaceRealModel) (n := ∞) (e := ey) (e' := e₀)
        (by simp)
        (IsManifold.chart_mem_maximalAtlas (I := SurfaceRealModel) (n := ∞) y)
        (IsManifold.chart_mem_maximalAtlas (I := SurfaceRealModel) (n := ∞) x₀)
        hz_sourceR
    have hsource_memR : (SurfaceRealModel.extendCoordChange ey e₀).source ∈ 𝓝 z := by
      have hsource_openR :
          IsOpen (SurfaceRealModel.extendCoordChange ey e₀).source := by
        simpa [SurfaceRealModel] using hsource_openC
      exact hsource_openR.mem_nhds hz_sourceR
    have hinv_fderiv :
        (fderiv ℝ ((𝓘(ℂ)).extendCoordChange ey e₀) z).IsInvertible := by
      rw [← fderivWithin_of_mem_nhds hsource_memR]
      simpa [SurfaceRealModel] using hinv_source
    rw [hmap_eq]
    intro hzero
    have hinj : Function.Injective (fderiv ℝ ((𝓘(ℂ)).extendCoordChange ey e₀) z) :=
      ContinuousLinearMap.IsInvertible.injective hinv_fderiv
    have hone : (1 : ℂ) = 0 := hinj (by simpa using hzero)
    norm_num at hone

set_option maxHeartbeats 1000000 in
/--
%%handwave
name:
  Holomorphic tangent trivializations pull back the Euclidean form conformally
statement:
  In a holomorphic coordinate trivialization of the tangent bundle, the
  pulled-back Euclidean tangent form is conformal on every fiber over the
  trivializing neighborhood.
proof:
  The tangent trivialization is induced by a holomorphic coordinate chart.
  Its derivative is complex-linear, and the real pullback of the Euclidean
  inner product along a complex-linear isomorphism is a positive scalar
  multiple of the Euclidean inner product on the complex tangent line.
-/
theorem trivialization_symmL_euclideanTangentBilinearForm_conformal
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] (x₀ y : X)
    (hy : y ∈
      (trivializationAt TangentBilinearFormModel
        (fun x : X ↦ TangentBilinearFormAt X x) x₀).baseSet) :
    IsConformalTangentForm y
      ((trivializationAt TangentBilinearFormModel
        (fun x : X ↦ TangentBilinearFormAt X x) x₀).symmL ℝ y
          euclideanTangentBilinearForm) := by
  let eT := trivializationAt ℂ (TangentSpace SurfaceRealModel : X → Type) x₀
  let eB :=
    trivializationAt TangentBilinearFormModel
      (fun x : X ↦ TangentBilinearFormAt X x) x₀
  let b : TangentBilinearFormAt X y :=
    eB.symmL ℝ y euclideanTangentBilinearForm
  have hyB : y ∈ eB.baseSet := by
    simpa [eB] using hy
  have hyT : y ∈ eT.baseSet := by
    simpa [eT, eB, TangentBilinearFormAt, TangentBilinearFormModel,
      hom_trivializationAt] using hy
  have hR : y ∈ (trivializationAt ℝ (Bundle.Trivial X ℝ) x₀).baseSet := by
    simp
  have hcoord :
      ContinuousLinearMap.inCoordinates ℂ
        (TangentSpace SurfaceRealModel : X → Type)
        (ℂ →L[ℝ] ℝ)
        (fun x : X ↦ TangentSpace SurfaceRealModel x →L[ℝ] ℝ)
        x₀ y x₀ y b = euclideanTangentBilinearForm := by
    have h1 :
        eB.continuousLinearMapAt ℝ y b =
          euclideanTangentBilinearForm := by
      exact eB.continuousLinearMapAt_symmL (R := ℝ) hyB
        euclideanTangentBilinearForm
    have h2 :
        eB.continuousLinearMapAt ℝ y b =
          ContinuousLinearMap.inCoordinates ℂ
            (TangentSpace SurfaceRealModel : X → Type)
            (ℂ →L[ℝ] ℝ)
            (fun x : X ↦ TangentSpace SurfaceRealModel x →L[ℝ] ℝ)
            x₀ y x₀ y b := by
      have h :=
        hom_trivializationAt_apply (RingHom.id ℝ)
          (F₁ := ℂ)
          (E₁ := (TangentSpace SurfaceRealModel : X → Type))
          (F₂ := ℂ →L[ℝ] ℝ)
          (E₂ := fun x : X ↦ TangentSpace SurfaceRealModel x →L[ℝ] ℝ)
          x₀ (Bundle.TotalSpace.mk' TangentBilinearFormModel y b)
      have hlin :
          eB.continuousLinearMapAt ℝ y b =
            (eB (Bundle.TotalSpace.mk' TangentBilinearFormModel y b)).2 := by
        rw [Bundle.Trivialization.continuousLinearMapAt_apply,
          Bundle.Trivialization.linearMapAt_apply]
        simp [hyB]
      rw [hlin]
      simpa [eB, TangentBilinearFormAt, TangentBilinearFormModel] using congrArg Prod.snd h
    rw [h2] at h1
    exact h1
  have eval_eq (v w : TangentSpace SurfaceRealModel y) :
      b v w =
        euclideanTangentBilinearForm
          (eT.continuousLinearMapAt ℝ y v)
          (eT.continuousLinearMapAt ℝ y w) := by
    have heq :=
      congrArg
        (fun q : TangentBilinearFormModel ↦
          q (eT.continuousLinearMapAt ℝ y v)
            (eT.continuousLinearMapAt ℝ y w))
        hcoord
    change
      (ContinuousLinearMap.inCoordinates ℂ
        (TangentSpace SurfaceRealModel : X → Type)
        (ℂ →L[ℝ] ℝ)
        (fun x : X ↦ TangentSpace SurfaceRealModel x →L[ℝ] ℝ)
        x₀ y x₀ y b)
          (eT.continuousLinearMapAt ℝ y v)
          (eT.continuousLinearMapAt ℝ y w) =
        euclideanTangentBilinearForm
          (eT.continuousLinearMapAt ℝ y v)
          (eT.continuousLinearMapAt ℝ y w) at heq
    rw [inCoordinates_apply_eq₂ hyT hyT hR] at heq
    have hv_back : eT.symm y (eT.continuousLinearMapAt ℝ y v) = v := by
      simpa [Bundle.Trivialization.coe_symmₗ] using
        eT.symmL_continuousLinearMapAt (R := ℝ) hyT v
    have hw_back : eT.symm y (eT.continuousLinearMapAt ℝ y w) = w := by
      simpa [Bundle.Trivialization.coe_symmₗ] using
        eT.symmL_continuousLinearMapAt (R := ℝ) hyT w
    rw [hv_back, hw_back] at heq
    simpa using heq
  rcases tangentTrivializationAt_continuousLinearMapAt_complex_linear_nonzero
      x₀ y hyT with
    ⟨hI, hnonzero⟩
  let L : ℂ →L[ℝ] ℂ := eT.continuousLinearMapAt ℝ y
  have hI_L : L Complex.I = Complex.I * L (1 : ℂ) := by
    simpa [L, eT] using hI
  have hL_apply (z : ℂ) : L z = z * L (1 : ℂ) := by
    have hz : z = (z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul]
    change (z.re : ℝ) • L (1 : ℂ) + (z.im : ℝ) • L Complex.I =
      z * L (1 : ℂ)
    rw [hI_L]
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]
      ring
    · simp [Complex.mul_re, Complex.mul_im]
  have hinner_mul (z w a : ℂ) :
      Inner.inner ℝ (z * a) (w * a) =
        Complex.normSq a * Inner.inner ℝ z w := by
    simp [Complex.inner, Complex.normSq_apply]
    ring
  refine ⟨Complex.normSq (L (1 : ℂ)),
    Complex.normSq_pos.mpr hnonzero, ?_⟩
  intro v w
  rw [eval_eq v w]
  change Inner.inner ℝ (L (show ℂ from v)) (L (show ℂ from w)) =
    Complex.normSq (L (1 : ℂ)) *
      Inner.inner ℝ (show ℂ from v) (show ℂ from w)
  rw [hL_apply (show ℂ from v), hL_apply (show ℂ from w),
    hinner_mul]

/--
%%handwave
name:
  Holomorphic charts give local conformal tangent forms
statement:
  Around every point of a Riemann surface there is a smooth local section of
  tangent-bilinear forms whose values are conformal.
proof:
  Choose a holomorphic coordinate chart and pull back the Euclidean metric
  from the complex plane.  In any holomorphic coordinate the transition map is
  complex-linear to first order, hence conformal, so the pulled-back form is a
  positive scalar multiple of the Euclidean tangent-line inner product.
-/
theorem exists_local_contMDiff_conformalTangentForm
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] :
    ∀ x₀ : X, ∃ U ∈ 𝓝 x₀, ∃ s_loc : (x : X) → TangentBilinearFormAt X x,
      ContMDiffOn SurfaceRealModel
        (SurfaceRealModel.prod 𝓘(ℝ, TangentBilinearFormModel)) ∞
        (fun x ↦ Bundle.TotalSpace.mk' TangentBilinearFormModel x (s_loc x)) U ∧
        ∀ y ∈ U, IsConformalTangentForm y (s_loc y) := by
  intro x₀
  let e :=
    trivializationAt TangentBilinearFormModel
      (fun x : X ↦ TangentBilinearFormAt X x) x₀
  let s_loc : (x : X) → TangentBilinearFormAt X x :=
    fun x ↦ e.symmL ℝ x euclideanTangentBilinearForm
  refine ⟨e.baseSet, ?_, s_loc, ?_, ?_⟩
  · exact e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt TangentBilinearFormModel
        (fun x : X ↦ TangentBilinearFormAt X x) x₀)
  · rw [Bundle.Trivialization.contMDiffOn_section_baseSet_iff
      (𝕜 := ℝ) (B := X) (F := TangentBilinearFormModel)
      (E := fun x : X ↦ TangentBilinearFormAt X x)
      (IB := SurfaceRealModel) (n := ∞) (s := s_loc) e]
    refine ((contMDiff_const (c := euclideanTangentBilinearForm)).contMDiffOn.congr ?_)
    intro x hx
    have hcoord :=
      e.continuousLinearMapAt_symmL (R := ℝ) hx euclideanTangentBilinearForm
    simp [s_loc, Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.linearMapAt_apply, hx] at hcoord ⊢
  · intro y hy
    exact trivialization_symmL_euclideanTangentBilinearForm_conformal x₀ y
      (by simpa [e] using hy)

/--
%%handwave
name:
  Conformal tangent-form sections from holomorphic partitions of unity
statement:
  On a sigma-compact Riemann surface, holomorphic coordinate charts and a
  smooth partition of unity produce a smooth section of tangent-bilinear forms
  whose value at every point is conformal.
proof:
  Pull back the Euclidean form from the complex plane in each holomorphic
  coordinate chart.  Holomorphic transition maps are complex-linear to first
  order, hence conformal, so each local form is a positive scalar multiple of
  the Euclidean tangent-line inner product in any other holomorphic
  coordinate.  A locally finite partition-of-unity sum of such positive
  scalar multiples is again a positive scalar multiple of the Euclidean form.
-/
theorem exists_conformal_contMDiff_tangentFormSection_via_holomorphic_partitionOfUnity
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [SigmaCompactSpace X] :
    ∃ inner : (x : X) → TangentBilinearFormAt X x,
      ContMDiff SurfaceRealModel
        (SurfaceRealModel.prod 𝓘(ℝ, TangentBilinearFormModel)) ∞
        (fun x ↦ Bundle.TotalSpace.mk' TangentBilinearFormModel x (inner x)) ∧
        ∀ x : X, IsConformalTangentForm x (inner x) := by
  let t : ∀ x : X, Set (TangentBilinearFormAt X x) :=
    fun x ↦ {b | IsConformalTangentForm x b}
  obtain ⟨s, hs⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local
      (I := SurfaceRealModel) (M := X) (F_fiber := TangentBilinearFormModel)
      (V := fun x : X ↦ TangentBilinearFormAt X x) t
      (fun x ↦ conformalTangentForm_convex x)
      (exists_local_contMDiff_conformalTangentForm X)
  exact ⟨fun x ↦ s x, s.contMDiff, hs⟩

/--
%%handwave
name:
  Smooth metric associated to a conformal tangent-form section
statement:
  A smooth pointwise conformal section of positive tangent-bilinear forms
  defines a smooth Riemannian metric on the surface.
-/
noncomputable def conformalContMDiffRiemannianMetricOfTangentFormSection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (inner : (x : X) → TangentBilinearFormAt X x)
    (hinner_conformal : ∀ x : X, IsConformalTangentForm x (inner x))
    (hinner_cont :
      ContMDiff SurfaceRealModel
        (SurfaceRealModel.prod 𝓘(ℝ, TangentBilinearFormModel)) ∞
        (fun x ↦ Bundle.TotalSpace.mk' TangentBilinearFormModel x (inner x))) :
    ContMDiffRiemannianMetricOnSurface X :=
  { inner := inner
    symm := fun x v w ↦ (conformalTangentForm_positiveDefinite
      (hinner_conformal x)).1 v w
    pos := fun x v hv ↦ (conformalTangentForm_positiveDefinite
      (hinner_conformal x)).2 v hv
    isVonNBounded := fun x ↦
      positiveDefiniteSymmetricTangentForm_isVonNBounded x (inner x)
        (conformalTangentForm_positiveDefinite (hinner_conformal x))
    contMDiff := hinner_cont }

/--
%%handwave
name:
  Smooth surface metric associated to a conformal tangent-form section
statement:
  The Riemannian metric associated to a smooth pointwise conformal
  tangent-form section can be regarded as a smooth surface metric.
-/
noncomputable def conformalSmoothMetricOfTangentFormSection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (inner : (x : X) → TangentBilinearFormAt X x)
    (hinner_conformal : ∀ x : X, IsConformalTangentForm x (inner x))
    (hinner_cont :
      ContMDiff SurfaceRealModel
        (SurfaceRealModel.prod 𝓘(ℝ, TangentBilinearFormModel)) ∞
        (fun x ↦ Bundle.TotalSpace.mk' TangentBilinearFormModel x (inner x))) :
    SmoothRiemannianMetricOnSurface X :=
  { isManifold_real := inferInstance
    toContMDiffRiemannianMetric :=
      conformalContMDiffRiemannianMetricOfTangentFormSection
        inner hinner_conformal hinner_cont }

/--
%%handwave
name:
  Multiplication scales the Euclidean real inner product
statement:
  Multiplying two complex tangent vectors by the same complex number scales
  their Euclidean real inner product by the squared norm of that number.
proof:
  Expand both sides in real and imaginary coordinates.
-/
theorem complex_inner_mul_right (z w a : ℂ) :
    Inner.inner ℝ (z * a) (w * a) =
      Complex.normSq a * Inner.inner ℝ z w := by
  simp [Complex.inner, Complex.normSq_apply]
  ring

/--
%%handwave
name:
  A real map satisfying the Cauchy-Riemann equation is multiplication
statement:
  A real-linear map of the complex tangent line satisfying
  \(L(i)=iL(1)\) is multiplication by \(L(1)\).
proof:
  Write \(z=x+iy\), use real-linearity, and substitute the
  Cauchy-Riemann relation.
-/
theorem complexLinearMap_apply_eq_mul
    (L : ℂ →L[ℝ] ℂ)
    (hI : L Complex.I = Complex.I * L (1 : ℂ)) (z : ℂ) :
    L z = z * L (1 : ℂ) := by
  have hz : z = (z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul, hI]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    ring
  · simp [Complex.mul_re, Complex.mul_im]

/-- The real determinant of a complex-linear endomorphism of the complex
line is the squared norm of its value at one. -/
theorem complexLinearMap_det_eq_normSq
    (L : ℂ →L[ℝ] ℂ)
    (hI : L Complex.I = Complex.I * L (1 : ℂ)) :
    L.det = Complex.normSq (L (1 : ℂ)) := by
  change LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) = Complex.normSq (L (1 : ℂ))
  calc
    LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) =
        (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          (L : ℂ →ₗ[ℝ] ℂ)).det :=
      (LinearMap.det_toMatrix Complex.basisOneI (L : ℂ →ₗ[ℝ] ℂ)).symm
    _ = Complex.normSq (L (1 : ℂ)) := by
      rw [Matrix.det_fin_two]
      have h_one : L (1 : ℂ) = L (1 : ℂ) := rfl
      have h_I : L Complex.I = Complex.I * L (1 : ℂ) := hI
      simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one,
        Complex.coe_basisOneI_repr]
      erw [h_one, h_I]
      simp only [Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, one_mul, zero_mul,
        zero_sub, zero_add, Complex.normSq_apply]
      ring

/--
%%handwave
name:
  Complex-linear maps pull back the Euclidean form conformally
statement:
  A nonzero complex-linear real map of the complex tangent line pulls back the
  Euclidean real inner product to a positive scalar multiple of itself.
proof:
  Such a map is multiplication by \(L(1)\).  Multiplication by a complex
  scalar scales the Euclidean real inner product by its squared norm, which is
  positive when \(L(1)\neq0\).
-/
theorem complexLinearMap_pullback_euclidean_conformal
    (L : ℂ →L[ℝ] ℂ)
    (hI : L Complex.I = Complex.I * L (1 : ℂ))
    (h1 : L (1 : ℂ) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      ∀ v w : ℂ,
        Inner.inner ℝ (L v) (L w) =
          c * Inner.inner ℝ v w := by
  refine ⟨Complex.normSq (L (1 : ℂ)), Complex.normSq_pos.mpr h1, ?_⟩
  intro v w
  rw [complexLinearMap_apply_eq_mul L hI v,
    complexLinearMap_apply_eq_mul L hI w,
    complex_inner_mul_right]

/--
%%handwave
name:
  Complex-linear maps send the coordinate frame to a conformal frame
statement:
  A nonzero complex-linear real map of the complex tangent line sends \(1\)
  and \(i\) to an orthogonal pair of equal positive squared length.
proof:
  If \(L(i)=iL(1)\), then multiplication by \(i\) preserves Euclidean length
  and rotates by a right angle.  Since \(L(1)\neq0\), the common squared
  length is positive.
-/
theorem complexLinearMap_conformal_frame
    (L : ℂ →L[ℝ] ℂ)
    (hI : L Complex.I = Complex.I * L (1 : ℂ))
    (h1 : L (1 : ℂ) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      inner ℝ (L (1 : ℂ)) (L (1 : ℂ)) = r ∧
      inner ℝ (L Complex.I) (L Complex.I) = r ∧
      inner ℝ (L (1 : ℂ)) (L Complex.I) = 0 ∧
      inner ℝ (L Complex.I) (L (1 : ℂ)) = 0 := by
  refine ⟨inner ℝ (L (1 : ℂ)) (L (1 : ℂ)),
    real_inner_self_pos.mpr h1, rfl, ?_, ?_, ?_⟩
  · rw [hI]
    simp
  · rw [hI]
    simp
    ring
  · rw [hI]
    simp
    ring

/--
%%handwave
name:
  Holomorphic chart tangent maps are nonzero complex-linear maps
statement:
  The tangent map of a holomorphic coordinate change is complex-linear and
  nonzero in the \(1\)-direction.
proof:
  The coordinate change between two holomorphic charts is biholomorphic on
  the overlap.  Hence its derivative is complex-linear.  Its inverse
  coordinate change differentiates to a two-sided inverse, so the derivative
  is nonzero.
-/
theorem surfaceChartTangentMap_complex_linear_nonzero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (z : ℂ) (_hz : z ∈ e.target) :
    (surfaceChartTangentMap e z) Complex.I =
        Complex.I * (surfaceChartTangentMap e z) (1 : ℂ) ∧
      (surfaceChartTangentMap e z) (1 : ℂ) ≠ 0 := by
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ (e.symm z)
  have hx_c : e.symm z ∈ c.source := by
    simp [c]
  have hz_source : z ∈ ((𝓘(ℂ)).extendCoordChange e c).source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter]
    refine ⟨e.symm z, ⟨?_, hx_c⟩, ?_⟩
    · exact e.symm.mapsTo _hz
    · simp
      exact e.right_inv _hz
  have hcomplex :
      ContDiffOn ℂ ⊤ ((𝓘(ℂ)).extendCoordChange e c)
        ((𝓘(ℂ)).extendCoordChange e c).source :=
    (𝓘(ℂ)).contDiffOn_extendCoordChange
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := ⊤) _he)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ⊤) (e.symm z))
  have hdiffC :
      DifferentiableWithinAt ℂ ((𝓘(ℂ)).extendCoordChange e c)
        ((𝓘(ℂ)).extendCoordChange e c).source z :=
    hcomplex.differentiableOn (by simp) z hz_source
  have hsource_eq :
      ((𝓘(ℂ)).extendCoordChange e c).source =
        e.target ∩ e.symm ⁻¹' c.source := by
    simp [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source, c]
  have hsource_open :
      IsOpen ((𝓘(ℂ)).extendCoordChange e c).source := by
    rw [hsource_eq]
    exact e.isOpen_inter_preimage_symm c.open_source
  have huniqueR :
      UniqueDiffWithinAt ℝ ((𝓘(ℂ)).extendCoordChange e c).source z :=
    hsource_open.uniqueDiffWithinAt hz_source
  have hcr_source :
      fderivWithin ℝ ((𝓘(ℂ)).extendCoordChange e c)
          ((𝓘(ℂ)).extendCoordChange e c).source z Complex.I =
        Complex.I •
          fderivWithin ℝ ((𝓘(ℂ)).extendCoordChange e c)
            ((𝓘(ℂ)).extendCoordChange e c).source z (1 : ℂ) :=
    ((differentiableWithinAt_complex_iff_differentiableWithinAt_real
      huniqueR).1 hdiffC).2
  have hpre_nhds : e.symm ⁻¹' c.source ∈ 𝓝 z :=
    (e.symm.continuousAt _hz).preimage_mem_nhds (c.open_source.mem_nhds hx_c)
  have hderiv_set :
      fderivWithin ℝ ((𝓘(ℂ)).extendCoordChange e c)
        ((𝓘(ℂ)).extendCoordChange e c).source z =
      fderivWithin ℝ ((𝓘(ℂ)).extendCoordChange e c) e.target z := by
    rw [hsource_eq]
    exact fderivWithin_inter hpre_nhds
  have hderiv_fun :
      fderivWithin ℝ ((𝓘(ℂ)).extendCoordChange e c) e.target z =
        surfaceChartTangentMap e z := by
    simp [surfaceChartTangentMap, c, ModelWithCorners.extendCoordChange]
    rfl
  have hderiv_source_to_surface :
      fderivWithin ℝ ((𝓘(ℂ)).extendCoordChange e c)
          ((𝓘(ℂ)).extendCoordChange e c).source z =
        surfaceChartTangentMap e z := by
    rw [hderiv_set, hderiv_fun]
  constructor
  · rw [hderiv_source_to_surface] at hcr_source
    simpa [smul_eq_mul] using hcr_source
  · have hinv : (surfaceChartTangentMap e z).IsInvertible :=
      surfaceChartTangentMap_isInvertible X g e _he z _hz
    intro hzero
    have hinj : Function.Injective (surfaceChartTangentMap e z) :=
      ContinuousLinearMap.IsInvertible.injective hinv
    have hone : (1 : ℂ) = 0 := hinj (by simpa using hzero)
    norm_num at hone

/-- Holomorphic coordinate changes preserve the complex orientation: their
real Jacobian determinant is strictly positive. -/
theorem surfaceChartTangentMap_det_pos
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (z : ℂ) (hz : z ∈ e.target) :
    0 < (surfaceChartTangentMap e z).det := by
  rcases surfaceChartTangentMap_complex_linear_nonzero g e he z hz with
    ⟨hI, hnonzero⟩
  rw [complexLinearMap_det_eq_normSq (surfaceChartTangentMap e z) hI]
  exact Complex.normSq_pos.mpr hnonzero

/--
%%handwave
name:
  Holomorphic chart tangent maps give conformal frames
statement:
  The coordinate tangent frame obtained from a holomorphic chart has
  orthogonal coordinate vectors of equal positive squared length.
proof:
  Apply the elementary conformal-frame computation for nonzero complex-linear
  maps to the tangent map of the holomorphic coordinate change.
-/
theorem surfaceChartTangentMap_conformal_frame
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (z : ℂ) (hz : z ∈ e.target) :
    ∃ r : ℝ, 0 < r ∧
      inner ℝ ((surfaceChartTangentMap e z) (1 : ℂ))
        ((surfaceChartTangentMap e z) (1 : ℂ)) = r ∧
      inner ℝ ((surfaceChartTangentMap e z) Complex.I)
        ((surfaceChartTangentMap e z) Complex.I) = r ∧
      inner ℝ ((surfaceChartTangentMap e z) (1 : ℂ))
        ((surfaceChartTangentMap e z) Complex.I) = 0 ∧
      inner ℝ ((surfaceChartTangentMap e z) Complex.I)
        ((surfaceChartTangentMap e z) (1 : ℂ)) = 0 := by
  rcases surfaceChartTangentMap_complex_linear_nonzero g e he z hz with
    ⟨hI, hnonzero⟩
  exact complexLinearMap_conformal_frame (surfaceChartTangentMap e z) hI hnonzero

/--
%%handwave
name:
  Conformal tangent forms have scalar coordinate Gram matrix
statement:
  At a point of a holomorphic coordinate chart, the coordinate Gram matrix of
  the smooth metric associated to a conformal tangent-form section is a
  positive scalar multiple of the identity.
proof:
  The derivative of a holomorphic chart is complex-linear, hence it sends the
  two coordinate directions to an orthogonal pair of equal Euclidean length in
  the complex tangent line.  Since the tangent form is a positive scalar
  multiple of the Euclidean inner product, the corresponding Gram matrix is
  scalar.
-/
theorem surfaceMetric_scalar_gram_of_conformal_tangentFormSection_at
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X]
    (inner : (x : X) → TangentBilinearFormAt X x)
    (hinner_conformal : ∀ x : X, IsConformalTangentForm x (inner x))
    (hinner_cont :
      ContMDiff SurfaceRealModel
        (SurfaceRealModel.prod 𝓘(ℝ, TangentBilinearFormModel)) ∞
        (fun x ↦ Bundle.TotalSpace.mk' TangentBilinearFormModel x (inner x)))
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (z : ℂ) (_hz : z ∈ e.target) :
    ∃ r : ℝ, 0 < r ∧
      ((conformalSmoothMetricOfTangentFormSection
        inner hinner_conformal hinner_cont).toContMDiffRiemannianMetric.inner
          (e.symm z))
        ((surfaceChartTangentMap e z) (1 : ℂ))
        ((surfaceChartTangentMap e z) (1 : ℂ)) = r ∧
      ((conformalSmoothMetricOfTangentFormSection
        inner hinner_conformal hinner_cont).toContMDiffRiemannianMetric.inner
          (e.symm z))
        ((surfaceChartTangentMap e z) Complex.I)
        ((surfaceChartTangentMap e z) Complex.I) = r ∧
      ((conformalSmoothMetricOfTangentFormSection
        inner hinner_conformal hinner_cont).toContMDiffRiemannianMetric.inner
          (e.symm z))
        ((surfaceChartTangentMap e z) (1 : ℂ))
        ((surfaceChartTangentMap e z) Complex.I) = 0 ∧
      ((conformalSmoothMetricOfTangentFormSection
        inner hinner_conformal hinner_cont).toContMDiffRiemannianMetric.inner
          (e.symm z))
        ((surfaceChartTangentMap e z) Complex.I)
        ((surfaceChartTangentMap e z) (1 : ℂ)) = 0 := by
  rcases hinner_conformal (e.symm z) with ⟨c, hcpos, hc⟩
  rcases surfaceChartTangentMap_conformal_frame
      (conformalSmoothMetricOfTangentFormSection
        inner hinner_conformal hinner_cont) e _he z _hz with
    ⟨a, hapos, h11, h22, h12, h21⟩
  have hb (v w : TangentSpace SurfaceRealModel (e.symm z)) :
      ((conformalSmoothMetricOfTangentFormSection
        inner hinner_conformal hinner_cont).toContMDiffRiemannianMetric.inner
          (e.symm z)) v w =
        c * Inner.inner ℝ (show ℂ from v) (show ℂ from w) := by
    simpa [conformalSmoothMetricOfTangentFormSection,
      conformalContMDiffRiemannianMetricOfTangentFormSection] using hc v w
  refine ⟨c * a, mul_pos hcpos hapos, ?_, ?_, ?_, ?_⟩
  · rw [hb, h11]
  · rw [hb, h22]
  · rw [hb, h12, mul_zero]
  · rw [hb, h21, mul_zero]

/--
%%handwave
name:
  Pointwise conformal tangent forms give Euclidean divergence coefficients
statement:
  At a point of a holomorphic coordinate chart, a smooth Riemannian metric
  built from a conformal tangent form satisfies
  \(\rho g^{ij}=\delta^{ij}\).
proof:
  The coordinate tangent map of a holomorphic chart is conformal as a real
  linear map.  Combining this with the pointwise conformality of the tangent
  form makes the local Gram matrix a positive scalar multiple of the identity.
  The determinant, inverse matrix, and volume density can then be computed
  explicitly.
-/
theorem surfaceMetricConformalToComplexStructure_of_conformal_tangentFormSection_at
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X]
    (inner : (x : X) → TangentBilinearFormAt X x)
    (hinner_conformal : ∀ x : X, IsConformalTangentForm x (inner x))
    (hinner_cont :
      ContMDiff SurfaceRealModel
        (SurfaceRealModel.prod 𝓘(ℝ, TangentBilinearFormModel)) ∞
        (fun x ↦ Bundle.TotalSpace.mk' TangentBilinearFormModel x (inner x)))
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (z : ℂ) (hz : z ∈ e.target) (i j : Fin 2) :
    surfaceMetricVolumeDensityInChart
        (conformalSmoothMetricOfTangentFormSection
          inner hinner_conformal hinner_cont) e z *
        surfaceMetricInverseGramCoeffInChart
          (conformalSmoothMetricOfTangentFormSection
            inner hinner_conformal hinner_cont) e z i j =
      if i = j then 1 else 0 := by
  rcases surfaceMetric_scalar_gram_of_conformal_tangentFormSection_at
      inner hinner_conformal hinner_cont e _he z hz with
    ⟨r, hr, h11, h22, h12, h21⟩
  exact surfaceMetricConformalCoefficient_eq_of_scalar_gram
    (conformalSmoothMetricOfTangentFormSection
      inner hinner_conformal hinner_cont) e z r hr h11 h22 h12 h21 i j

/--
%%handwave
name:
  Conformal tangent-form sections give conformal metric coefficients
statement:
  If a smooth Riemannian metric is built from a pointwise conformal
  tangent-form section, then in every holomorphic coordinate its
  divergence-form coefficient tensor is Euclidean:
  \(\rho g^{ij}=\delta^{ij}\).
proof:
  In a holomorphic coordinate, the coordinate tangent frame is related to the
  complex tangent line by a complex-linear map.  A conformal tangent form is a
  positive scalar multiple of the Euclidean inner product, so its Gram matrix
  in this frame is \(\lambda^2\) times the identity.  The inverse matrix is
  \(\lambda^{-2}\) times the identity and the volume density is \(\lambda^2\),
  so the product \(\rho g^{ij}\) is the identity matrix.
-/
theorem surfaceMetricConformalToComplexStructure_of_conformal_tangentFormSection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X]
    (inner : (x : X) → TangentBilinearFormAt X x)
    (hinner_conformal : ∀ x : X, IsConformalTangentForm x (inner x))
    (hinner_cont :
      ContMDiff SurfaceRealModel
        (SurfaceRealModel.prod 𝓘(ℝ, TangentBilinearFormModel)) ∞
        (fun x ↦ Bundle.TotalSpace.mk' TangentBilinearFormModel x (inner x))) :
    SurfaceMetricConformalToComplexStructure
      (conformalSmoothMetricOfTangentFormSection
        inner hinner_conformal hinner_cont) := by
  intro e he z hz i j
  exact surfaceMetricConformalToComplexStructure_of_conformal_tangentFormSection_at
    inner hinner_conformal hinner_cont e he z hz i j

/--
%%handwave
name:
  Conformal smooth Riemannian metrics from holomorphic partitions of unity
statement:
  On a sigma-compact Riemann surface, the holomorphic-coordinate
  partition-of-unity construction produces a smooth Riemannian metric whose
  coordinate divergence-form tensor is Euclidean.
proof:
  Choose a locally finite smooth partition of unity subordinate to
  holomorphic coordinate charts.  Pull back the Euclidean metric from the
  complex plane in each chart and multiply by the corresponding partition
  function.  On overlaps, holomorphic transition maps are conformal, so every
  pulled-back Euclidean metric is a positive scalar multiple of the Euclidean
  metric in any other holomorphic coordinate.  The locally finite sum is
  therefore again a positive scalar multiple of the Euclidean metric in each
  coordinate.  In dimension two, this is equivalent to
  \(\rho g^{ij}=\delta^{ij}\).
-/
theorem exists_conformal_contMDiffRiemannianMetricOnSurface_via_holomorphic_partitionOfUnity
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [SigmaCompactSpace X] :
    ∃ metric : ContMDiffRiemannianMetricOnSurface X,
      SurfaceMetricConformalToComplexStructure
        { isManifold_real := inferInstance
          toContMDiffRiemannianMetric := metric } := by
  rcases exists_conformal_contMDiff_tangentFormSection_via_holomorphic_partitionOfUnity
      X with
    ⟨inner, hinner_cont, hinner_conformal⟩
  let metric : ContMDiffRiemannianMetricOnSurface X :=
    conformalContMDiffRiemannianMetricOfTangentFormSection
      inner hinner_conformal hinner_cont
  exact ⟨metric,
    surfaceMetricConformalToComplexStructure_of_conformal_tangentFormSection
      inner hinner_conformal hinner_cont⟩

/--
%%handwave
name:
  Conformal smooth metrics from holomorphic partitions of unity
statement:
  A Hausdorff sigma-compact Riemann surface admits a smooth Riemannian metric
  conformal to its complex structure.
proof:
  Use a holomorphic atlas and choose a smooth partition of unity subordinate
  to it.  In each holomorphic chart, pull back the Euclidean metric from the
  complex plane.  Holomorphic coordinate changes are conformal, so every local
  summand is a positive scalar multiple of the Euclidean metric in every
  holomorphic coordinate.  A locally finite positive weighted sum is therefore
  still conformal.
-/
theorem exists_conformal_smoothRiemannianMetricOnSurface_via_holomorphic_partitionOfUnity
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [SigmaCompactSpace X] :
    ∃ metric : SmoothRiemannianMetricOnSurface X,
      SurfaceMetricConformalToComplexStructure metric := by
  haveI : IsManifold SurfaceRealModel ∞ X :=
    complexOneManifold_has_real_smooth_structure X
  rcases
      exists_conformal_contMDiffRiemannianMetricOnSurface_via_holomorphic_partitionOfUnity
        X with
    ⟨metric, hmetric_conformal⟩
  exact ⟨
    { isManifold_real := inferInstance
      toContMDiffRiemannianMetric := metric },
    hmetric_conformal⟩

/--
%%handwave
name:
  Riemann surfaces have conformal smooth metrics
statement:
  Every Riemann surface admits a smooth Riemannian metric conformal
  to the complex structure.
proof:
  Radó second countability gives sigma-compactness, and the conformal
  partition-of-unity construction gives the metric.
-/
theorem riemannSurface_has_conformal_smoothRiemannianMetric
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] :
    ∃ metric : SmoothRiemannianMetricOnSurface X,
      SurfaceMetricConformalToComplexStructure metric := by
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  haveI : SigmaCompactSpace X := inferInstance
  exact exists_conformal_smoothRiemannianMetricOnSurface_via_holomorphic_partitionOfUnity X

/--
%%handwave
name:
  Conformal smooth metrics supply conformal energy backgrounds
statement:
  A conformal smooth metric supplies a conformal background geometry for the
  energy method.
proof:
  Use the existing construction of the Riemannian volume measure, cotangent
  pairing, and Laplace-Beltrami operator from the smooth metric, and retain
  the conformality proof as an additional property of the resulting
  background metric.
-/
theorem smoothRiemannianMetricOnSurface_induces_conformal_energy_background_metric
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [T2Space X] [SigmaCompactSpace X] [Nonempty X]
    (metric : SmoothRiemannianMetricOnSurface X)
    (hconformal : SurfaceMetricConformalToComplexStructure metric) :
    ∃ g : BackgroundSurfaceMetricOnSurface X,
      g.metric = metric ∧ BackgroundSurfaceMetricConformalToComplexStructure g := by
  rcases smoothRiemannianMetricOnSurface_induces_measure_geometry X metric with ⟨μg⟩
  rcases smoothRiemannianMetricOnSurface_induces_gradient_geometry X metric μg with
    ⟨gradGeom⟩
  let g : BackgroundSurfaceMetricOnSurface X :=
    { metric := metric
      measureGeometry := μg
      gradientGeometry := gradGeom }
  refine ⟨g, rfl, ?_⟩
  exact hconformal

/--
%%handwave
name:
  Conformal background metrics exist
statement:
  Every Riemann surface equipped with its Borel measurable structure
  admits a conformal smooth background metric suitable for the energy method.
proof:
  Choose a conformal smooth metric and then apply the background-geometry
  construction for smooth Riemannian metrics.
tags:
  milestone
-/
theorem riemannSurface_has_conformal_energy_background_metric
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    [RiemannSurface X] :
    ∃ g : BackgroundSurfaceMetricOnSurface X,
      BackgroundSurfaceMetricConformalToComplexStructure g := by
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  haveI : SigmaCompactSpace X := inferInstance
  haveI : Nonempty X := PathConnectedSpace.nonempty
  rcases riemannSurface_has_conformal_smoothRiemannianMetric X with
    ⟨metric, hconformal⟩
  rcases smoothRiemannianMetricOnSurface_induces_conformal_energy_background_metric
      X metric hconformal with
    ⟨g, _hg_metric, hg_conformal⟩
  exact ⟨g, hg_conformal⟩


end Uniformization

end JJMath
