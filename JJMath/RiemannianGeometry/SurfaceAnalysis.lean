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

/--
%%handwave
name:
  The packaged surface volume is a smooth positive area measure
statement:
  For every surface metric-measure geometry, its volume measure is smooth and
  strictly positive in local coordinates.
proof:
  By definition, the volume component of a surface metric-measure geometry is
  the Riemannian area measure, whose coordinate density is smooth and positive.
-/
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

/--
%%handwave
name:
  The first real coordinate vector is \(1\)
statement:
  In the standard real basis of \(\mathbb C\), the coordinate vector indexed by \(0\) is \(1\).
proof:
  This is the defining first branch of the coordinate-vector convention.
-/
@[simp]
theorem complexCoordinateVector_zero :
    complexCoordinateVector 0 = (1 : ℂ) := by
  rfl

/--
%%handwave
name:
  The second real coordinate vector is \(i\)
statement:
  In the standard real basis of \(\mathbb C\), the coordinate vector indexed by \(1\) is \(i\).
proof:
  This is the defining second branch of the coordinate-vector convention.
-/
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

/--
%%handwave
name:
  Area measure of a background surface metric
statement:
  The volume of a background surface geometry is its Riemannian area measure on the surface.
-/
def volume {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) : Measure X :=
  g.measureGeometry.volume

/--
%%handwave
name:
  Cotangent inner product of a background surface metric
statement:
  The gradient pairing of a background surface geometry assigns to each point $x$ the inner product of two real cotangent vectors at $x$.
-/
def gradientInner {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) :
    X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ :=
  g.gradientGeometry.gradientInner

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
proof:
  Take the Riemannian volume associated with the smooth metric; its smooth positive chart densities and metric compatibility supply all fields of the required measure geometry.
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

/--
%%handwave
name:
  Determinant of a complex-linear map is a squared norm
statement:
  If a real-linear \(L:\mathbb C\to\mathbb C\) satisfies \(L(i)=iL(1)\), then
  \[
    \det_{\mathbb R}L=\lvert L(1)\rvert^2.
  \]
proof:
  Write the real matrix of \(L\) in the basis \(1,i\); complex linearity makes
  its columns \(L(1)\) and \(iL(1)\), whose determinant is the squared modulus.
-/
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

/--
%%handwave
name:
  Holomorphic surface-chart tangent maps preserve orientation
statement:
  For a complex surface chart \(e\) and \(z\in e.target\), the real determinant
  of its tangent-coordinate map is strictly positive.
proof:
  The tangent map is complex linear and nonzero.  Its real determinant is
  therefore the positive number \(\lvert J(1)\rvert^2\).
-/
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

end Uniformization

end JJMath
