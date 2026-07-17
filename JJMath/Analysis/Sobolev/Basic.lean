import JJMath.RiemannianGeometry.SurfaceAnalysis
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Basic Sobolev spaces on manifolds and surfaces

This file defines the representative-level \(W^{1,2}\) spaces on surfaces,
their zero-trace subspace, and the local seminorms used by the later
compactness, Poincare, Hilbert-space, and capacity files.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff

namespace Uniformization

noncomputable section

/--
%%handwave
name:
  Smooth compactly supported coordinate test
statement:
  A smooth compactly supported coordinate test on an open coordinate region is
  a smooth real-valued function on the coordinate plane whose closed support is
  compact and contained in that region.
-/
structure SmoothCompactlySupportedCoordinateFunction (Ω : Set ℂ) where
  /-- The coordinate test function. -/
  toFun : ℂ → ℝ
  /-- The coordinate test function is smooth. -/
  smooth : ContDiff ℝ ∞ toFun
  /-- The closed support is contained in the coordinate region. -/
  support_subset : tsupport toFun ⊆ Ω
  /-- The closed support is compact. -/
  compact_support : IsCompact (tsupport toFun)

namespace SmoothCompactlySupportedCoordinateFunction

instance {Ω : Set ℂ} : CoeFun (SmoothCompactlySupportedCoordinateFunction Ω)
    (fun _ ↦ ℂ → ℝ) where
  coe φ := φ.toFun

end SmoothCompactlySupportedCoordinateFunction

/--
%%handwave
name:
  Smooth compactly supported coordinate test in a model chart
statement:
  A smooth compactly supported coordinate test on a coordinate region of a
  finite-dimensional smooth manifold is a smooth real-valued function on the
  model vector space whose closed support is compact and contained in that
  region.
-/
structure SmoothCompactlySupportedManifoldCoordinateFunction {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Ω : Set H) where
  /-- The coordinate test function. -/
  toFun : H → ℝ
  /-- The coordinate test function is smooth. -/
  smooth : ContDiff ℝ ∞ toFun
  /-- The closed support is contained in the coordinate region. -/
  support_subset : tsupport toFun ⊆ Ω
  /-- The closed support is compact. -/
  compact_support : IsCompact (tsupport toFun)

namespace SmoothCompactlySupportedManifoldCoordinateFunction

instance {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Ω : Set H} :
    CoeFun (SmoothCompactlySupportedManifoldCoordinateFunction Ω)
      (fun _ ↦ H → ℝ) where
  coe φ := φ.toFun

/--
%%handwave
name:
  Coordinate tests extend to larger regions
statement:
  A smooth compactly supported coordinate test on a region is also a test on
  any larger region.
proof:
  Keep the same smooth function and compact support.  Only the inclusion of
  the closed support changes, by composing it with the region inclusion.
-/
def mono {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Ω Ω' : Set H}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (hΩ : Ω ⊆ Ω') :
    SmoothCompactlySupportedManifoldCoordinateFunction Ω' :=
  { toFun := φ.toFun
    smooth := φ.smooth
    support_subset := φ.support_subset.trans hΩ
    compact_support := φ.compact_support }

@[simp]
theorem mono_coe {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Ω Ω' : Set H}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (hΩ : Ω ⊆ Ω') :
    (φ.mono hΩ : H → ℝ) = φ :=
  rfl

/--
%%handwave
name:
  Compactly supported coordinate tests are bounded
statement:
  A smooth coordinate test with compact topological support is bounded on the
  whole model space.
proof:
  Continuity gives boundedness on the compact support.  Outside the
  topological support the function vanishes.
-/
theorem exists_bound {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Ω : Set H}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω) :
    ∃ C : NNReal, ∀ z : H, ‖(φ : H → ℝ) z‖ ≤ C := by
  have hcont : Continuous (φ : H → ℝ) := φ.smooth.continuous
  rcases φ.compact_support.exists_bound_of_continuousOn hcont.continuousOn with
    ⟨C₀, hC₀⟩
  let C : ℝ := max C₀ 0
  have hC_nonneg : 0 ≤ C := le_max_right C₀ 0
  refine ⟨⟨C, hC_nonneg⟩, ?_⟩
  intro z
  by_cases hz : z ∈ tsupport (φ : H → ℝ)
  · exact le_trans (hC₀ z hz) (le_max_left C₀ 0)
  · have hz_zero : (φ : H → ℝ) z = 0 :=
      image_eq_zero_of_notMem_tsupport hz
    simp [hz_zero, C]

/--
%%handwave
name:
  Directional derivatives of compactly supported coordinate tests are bounded
statement:
  Fix a tangent direction in the model space.  The directional derivative of a
  smooth coordinate test with compact topological support is bounded on the
  whole model space.
proof:
  The derivative is continuous and hence bounded on the compact support.
  Outside that support the original test function vanishes near the point, so
  its derivative is zero.
-/
theorem exists_derivative_bound {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {Ω : Set H}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω) (v : H) :
    ∃ C : NNReal, ∀ z : H, ‖fderiv ℝ (φ : H → ℝ) z v‖ ≤ C := by
  have hcont :
      Continuous (fun z : H ↦ fderiv ℝ (φ : H → ℝ) z v) :=
    (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  rcases φ.compact_support.exists_bound_of_continuousOn hcont.continuousOn with
    ⟨C₀, hC₀⟩
  let C : ℝ := max C₀ 0
  have hC_nonneg : 0 ≤ C := le_max_right C₀ 0
  refine ⟨⟨C, hC_nonneg⟩, ?_⟩
  intro z
  by_cases hz : z ∈ tsupport (φ : H → ℝ)
  · exact le_trans (hC₀ z hz) (le_max_left C₀ 0)
  · have hz_deriv : fderiv ℝ (φ : H → ℝ) z = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := (φ : H → ℝ)) hz
    simp [hz_deriv, C]

end SmoothCompactlySupportedManifoldCoordinateFunction

/--
%%handwave
name:
  Euclidean weak derivative for vector-valued maps
statement:
  A vector-valued map on a region of a finite-dimensional real vector space
  has a weak derivative field if the usual integration-by-parts identity
  holds against all smooth compactly supported scalar coordinate tests and
  all constant directions.
-/
def IsWeakDerivativeOnEuclideanRegionWithValues {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set H) (u : H → E) (du : H → H →L[ℝ] E) : Prop :=
  ∀ (φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω) (v : H),
    Integrable
        (fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • u z)
        (MeasureTheory.volume.restrict Ω) ∧
      Integrable
        (fun z ↦ φ z • du z v)
        (MeasureTheory.volume.restrict Ω) ∧
        ∫ z in Ω,
            (fderiv ℝ (φ : H → ℝ) z v) • u z ∂MeasureTheory.volume =
          -∫ z in Ω, φ z • du z v ∂MeasureTheory.volume

/--
%%handwave
name:
  Euclidean weak derivatives scale
statement:
  Multiplying a vector-valued Euclidean weak Sobolev function and its weak
  derivative field by the same real scalar preserves the weak-derivative
  identity.
proof:
  Pull the scalar through both Bochner integrals in the integration-by-parts
  identity.
-/
theorem IsWeakDerivativeOnEuclideanRegionWithValues.const_smul {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set H} {u : H → E} {du : H → H →L[ℝ] E}
    (c : ℝ) (hu : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du) :
    IsWeakDerivativeOnEuclideanRegionWithValues Ω
      (fun z : H ↦ c • u z) (fun z : H ↦ c • du z) := by
  intro φ v
  rcases hu φ v with ⟨hu_int, hdu_int, h_eq⟩
  let μΩ := MeasureTheory.volume.restrict Ω
  let lhs : H → E := fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • u z
  let rhs : H → E := fun z ↦ φ z • du z v
  have h_eq' : ∫ z, lhs z ∂μΩ = -∫ z, rhs z ∂μΩ := by
    simpa [μΩ, lhs, rhs] using h_eq
  have hrhs_smul :
      (fun z ↦ c • rhs z) =
        fun z ↦ φ z • (c • du z) v := by
    ext z
    simp [rhs, smul_smul, mul_comm]
  constructor
  · convert Integrable.smul c hu_int using 1
    ext z
    simp [smul_smul, mul_comm]
  · constructor
    · convert Integrable.smul c hdu_int using 1
      ext z
      simp [smul_smul, mul_comm]
    · calc
        ∫ z in Ω,
            (fderiv ℝ (φ : H → ℝ) z v) • (c • u z)
              ∂MeasureTheory.volume
            = ∫ z, c • lhs z ∂μΩ := by
                congr 1
                ext z
                simp [lhs, smul_smul, mul_comm]
        _ = c • ∫ z, lhs z ∂μΩ := integral_smul c lhs
        _ = c • (-∫ z, rhs z ∂μΩ) := by rw [h_eq']
        _ = -(c • ∫ z, rhs z ∂μΩ) := by simp
        _ = -∫ z, c • rhs z ∂μΩ := by rw [integral_smul c rhs]
        _ = -∫ z in Ω, φ z • (c • du z) v ∂MeasureTheory.volume := by
              rw [show μΩ = MeasureTheory.volume.restrict Ω from rfl, hrhs_smul]

/--
%%handwave
name:
  Euclidean weak derivatives add
statement:
  If two vector-valued functions on a Euclidean region have weak derivative
  fields, then their sum has the sum of those weak derivative fields as a
  weak derivative.
proof:
  Add the two integration-by-parts identities and use linearity of the
  Bochner integral.
-/
theorem IsWeakDerivativeOnEuclideanRegionWithValues.add {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set H} {u v : H → E} {du dv : H → H →L[ℝ] E}
    (hu : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hv : IsWeakDerivativeOnEuclideanRegionWithValues Ω v dv) :
    IsWeakDerivativeOnEuclideanRegionWithValues Ω
      (fun z : H ↦ u z + v z) (fun z : H ↦ du z + dv z) := by
  intro φ w
  rcases hu φ w with ⟨hu_int, hdu_int, hu_eq⟩
  rcases hv φ w with ⟨hv_int, hdv_int, hv_eq⟩
  let μΩ := MeasureTheory.volume.restrict Ω
  let lhs_u : H → E := fun z ↦ (fderiv ℝ (φ : H → ℝ) z w) • u z
  let lhs_v : H → E := fun z ↦ (fderiv ℝ (φ : H → ℝ) z w) • v z
  let rhs_u : H → E := fun z ↦ φ z • du z w
  let rhs_v : H → E := fun z ↦ φ z • dv z w
  have h_lhs_eq_u : ∫ z, lhs_u z ∂μΩ = -∫ z, rhs_u z ∂μΩ := by
    simpa [μΩ, lhs_u, rhs_u] using hu_eq
  have h_lhs_eq_v : ∫ z, lhs_v z ∂μΩ = -∫ z, rhs_v z ∂μΩ := by
    simpa [μΩ, lhs_v, rhs_v] using hv_eq
  constructor
  · convert hu_int.add hv_int using 1
    ext z
    simp [smul_add]
  · constructor
    · convert hdu_int.add hdv_int using 1
      ext z
      simp [smul_add]
    · calc
        ∫ z in Ω,
            (fderiv ℝ (φ : H → ℝ) z w) • (u z + v z)
              ∂MeasureTheory.volume
            = ∫ z, lhs_u z + lhs_v z ∂μΩ := by
                congr 1
                ext z
                simp [lhs_u, lhs_v, smul_add]
        _ = ∫ z, lhs_u z ∂μΩ + ∫ z, lhs_v z ∂μΩ :=
              integral_add hu_int hv_int
        _ = -∫ z, rhs_u z ∂μΩ + -∫ z, rhs_v z ∂μΩ := by
              rw [h_lhs_eq_u, h_lhs_eq_v]
        _ = -(∫ z, rhs_u z ∂μΩ + ∫ z, rhs_v z ∂μΩ) := by
              abel
        _ = -∫ z, rhs_u z + rhs_v z ∂μΩ := by
              rw [integral_add hdu_int hdv_int]
        _ = -∫ z, φ z • (du z + dv z) w ∂μΩ := by
              congr 1
              refine integral_congr_ae ?_
              exact Filter.Eventually.of_forall fun z ↦ by
                simp [rhs_u, rhs_v, smul_add]
        _ = -∫ z in Ω, φ z • (du z + dv z) w ∂MeasureTheory.volume := rfl

/--
%%handwave
name:
  Euclidean weak derivatives are closed under negation
statement:
  If a vector-valued function on a Euclidean region has a weak derivative
  field, then its negative has the negative weak derivative field.
proof:
  This is the scalar multiplication rule with scalar \(-1\).
-/
theorem IsWeakDerivativeOnEuclideanRegionWithValues.neg {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set H} {u : H → E} {du : H → H →L[ℝ] E}
    (hu : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du) :
    IsWeakDerivativeOnEuclideanRegionWithValues Ω
      (fun z : H ↦ -u z) (fun z : H ↦ -du z) := by
  simpa using hu.const_smul (-1)

/--
%%handwave
name:
  Euclidean weak derivatives subtract
statement:
  If two vector-valued functions on a Euclidean region have weak derivative
  fields, then their difference has the difference of those weak derivative
  fields as a weak derivative.
proof:
  Add the first function to the negative of the second.
-/
theorem IsWeakDerivativeOnEuclideanRegionWithValues.sub {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set H} {u v : H → E} {du dv : H → H →L[ℝ] E}
    (hu : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hv : IsWeakDerivativeOnEuclideanRegionWithValues Ω v dv) :
    IsWeakDerivativeOnEuclideanRegionWithValues Ω
      (fun z : H ↦ u z - v z) (fun z : H ↦ du z - dv z) := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

/--
%%handwave
name:
  Coordinate region of a surface subset
statement:
  The coordinate region associated to a surface subset consists of those
  coordinate points whose corresponding surface point lies in the subset.
-/
def surfaceChartRegion {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (U : Set X) : Set ℂ :=
  e.target ∩ e.symm ⁻¹' U

/--
%%handwave
name:
  Coordinate region of a manifold subset
statement:
  The coordinate region associated to a subset of a smooth manifold consists
  of those coordinate points whose corresponding manifold point lies in the
  subset.
-/
def manifoldChartRegion {H X : Type} [TopologicalSpace H] [TopologicalSpace X]
    [ChartedSpace H X]
    (e : OpenPartialHomeomorph X H) (U : Set X) : Set H :=
  e.target ∩ e.symm ⁻¹' U

/--
%%handwave
name:
  Smooth compactly supported surface function
statement:
  A smooth compactly supported test function on a Riemann surface is a smooth
  real-valued function with compact support, together with its classical
  differential.
-/
structure SmoothCompactlySupportedGlobalSurfaceFunction (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The test function. -/
  toFun : X → ℝ
  /-- Its classical differential, represented in tangent coordinates. -/
  gradient : X → ℂ →L[ℝ] ℝ
  /-- The function is smooth on the surface. -/
  smooth : IsSmoothOnSurface (Set.univ : Set X) toFun
  /-- The stored differential agrees with coordinate directional derivatives. -/
  gradient_eq : ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) z,
    z ∈ e.target → ∀ v : ℂ,
      gradient (e.symm z) (surfaceChartTangentMap e z v) =
        fderiv ℝ (fun w : ℂ ↦ toFun (e.symm w)) z v
  /-- The support is compact. -/
  compact_support : HasCompactSupportOnSurface toFun

namespace SmoothCompactlySupportedGlobalSurfaceFunction

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

instance : CoeFun (SmoothCompactlySupportedGlobalSurfaceFunction X) (fun _ ↦ X → ℝ) where
  coe f := f.toFun

/--
%%handwave
name:
  Zero smooth compactly supported test
statement:
  The zero function is a smooth compactly supported surface test function, with
  zero gradient.
-/
def zero : SmoothCompactlySupportedGlobalSurfaceFunction X where
  toFun := 0
  gradient := 0
  smooth := by
    intro e _he
    exact contDiffOn_const
  gradient_eq := by
    intro e _he z _hz v
    simp
  compact_support := by
    unfold HasCompactSupportOnSurface
    simp

end SmoothCompactlySupportedGlobalSurfaceFunction

/--
Zero-extension of a coordinate test to the surface through one chart.

It is the pullback by the chart on the chart source and is zero outside the
source.  The support hypotheses on actual test functions will ensure that the
extension is smooth across the chart boundary.
-/
noncomputable def chartTestSurfaceZeroExtension {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (η : ℂ → ℝ) : X → ℝ :=
  e.source.indicator (fun x : X ↦ η (e x))

theorem chartTestSurfaceZeroExtension_apply_of_mem {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (η : ℂ → ℝ) {x : X}
    (hx : x ∈ e.source) :
    chartTestSurfaceZeroExtension e η x = η (e x) := by
  simp [chartTestSurfaceZeroExtension, hx]

theorem chartTestSurfaceZeroExtension_apply_of_notMem {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (η : ℂ → ℝ) {x : X}
    (hx : x ∉ e.source) :
    chartTestSurfaceZeroExtension e η x = 0 := by
  simp [chartTestSurfaceZeroExtension, hx]

theorem chartTestSurfaceZeroExtension_apply_symm_of_mem {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (η : ℂ → ℝ) {z : ℂ}
    (hz : z ∈ e.target) :
    chartTestSurfaceZeroExtension e η (e.symm z) = η z := by
  have hx : e.symm z ∈ e.source := e.map_target hz
  simp [chartTestSurfaceZeroExtension, hx, e.right_inv hz]

theorem chartTestSurfaceZeroExtension_support_subset_image_support {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) {η : ℂ → ℝ} :
    Function.support (chartTestSurfaceZeroExtension e η) ⊆
      e.symm '' Function.support η := by
  intro x hx
  have hx_source : x ∈ e.source := by
    by_contra hx_source
    exact hx (chartTestSurfaceZeroExtension_apply_of_notMem e η hx_source)
  refine ⟨e x, ?_, ?_⟩
  · intro hη_zero
    exact hx (by
      rw [chartTestSurfaceZeroExtension_apply_of_mem e η hx_source, hη_zero])
  · exact e.left_inv hx_source

theorem chartTestSurfaceZeroExtension_tsupport_subset_image_tsupport {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) {η : ℂ → ℝ}
    (hη_target : tsupport η ⊆ e.target)
    (hη_compact : IsCompact (tsupport η)) :
    tsupport (chartTestSurfaceZeroExtension e η) ⊆ e.symm '' tsupport η := by
  have himage_compact : IsCompact (e.symm '' tsupport η) :=
    hη_compact.image_of_continuousOn
      (e.continuousOn_symm.mono hη_target)
  have himage_closed : IsClosed (e.symm '' tsupport η) := himage_compact.isClosed
  have hsupport :
      Function.support (chartTestSurfaceZeroExtension e η) ⊆
        e.symm '' tsupport η := by
    exact (chartTestSurfaceZeroExtension_support_subset_image_support e).trans
      (Set.image_mono (subset_tsupport η))
  rw [tsupport]
  exact closure_minimal hsupport himage_closed

theorem chartTestSurfaceZeroExtension_tsupport_subset_source {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) {η : ℂ → ℝ}
    (hη_target : tsupport η ⊆ e.target)
    (hη_compact : IsCompact (tsupport η)) :
    tsupport (chartTestSurfaceZeroExtension e η) ⊆ e.source := by
  intro x hx
  rcases chartTestSurfaceZeroExtension_tsupport_subset_image_tsupport
      e hη_target hη_compact hx with
    ⟨z, hz, rfl⟩
  exact e.map_target (hη_target hz)

theorem chartTestSurfaceZeroExtension_tsupport_subset_set {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) {η : ℂ → ℝ} {U : Set X}
    (hη_region : tsupport η ⊆ e.target ∩ e.symm ⁻¹' U)
    (hη_compact : IsCompact (tsupport η)) :
    tsupport (chartTestSurfaceZeroExtension e η) ⊆ U := by
  have hη_target : tsupport η ⊆ e.target := fun z hz ↦
    (hη_region hz).1
  intro x hx
  rcases chartTestSurfaceZeroExtension_tsupport_subset_image_tsupport
      e hη_target hη_compact hx with
    ⟨z, hz, rfl⟩
  exact (hη_region hz).2

theorem chartTestSurfaceZeroExtension_hasCompactSupport {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) {η : ℂ → ℝ}
    (hη_target : tsupport η ⊆ e.target)
    (hη_compact : IsCompact (tsupport η)) :
    HasCompactSupportOnSurface (chartTestSurfaceZeroExtension e η) := by
  have himage_compact : IsCompact (e.symm '' tsupport η) :=
    hη_compact.image_of_continuousOn
      (e.continuousOn_symm.mono hη_target)
  exact himage_compact.of_isClosed_subset (isClosed_tsupport _)
    (chartTestSurfaceZeroExtension_tsupport_subset_image_tsupport
      e hη_target hη_compact)

theorem chartTestSurfaceZeroExtension_smooth {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {η : ℂ → ℝ}
    (hη_smooth : ContDiff ℝ ∞ η)
    (hη_target : tsupport η ⊆ e.target)
    (hη_compact : IsCompact (tsupport η)) :
    IsSmoothOnSurface (Set.univ : Set X)
      (chartTestSurfaceZeroExtension e η) := by
  intro c hc
  rw [Set.preimage_univ, Set.inter_univ]
  intro z hz_target
  by_cases hx_support :
      c.symm z ∈ tsupport (chartTestSurfaceZeroExtension e η)
  · have hx_source : c.symm z ∈ e.source :=
      chartTestSurfaceZeroExtension_tsupport_subset_source
        e hη_target hη_compact hx_support
    let T : ℂ → ℂ := fun w : ℂ ↦ e (c.symm w)
    let S : Set ℂ := c.target ∩ c.symm ⁻¹' e.source
    have hT : ContDiffOn ℝ ∞ T S := by
      have h := SurfaceRealModel.contDiffOn_extendCoordChange
        (IsManifold.subset_maximalAtlas (I := SurfaceRealModel) (n := ∞) hc)
        (IsManifold.subset_maximalAtlas (I := SurfaceRealModel) (n := ∞) he)
      simpa [SurfaceRealModel, T, S, ModelWithCorners.extendCoordChange,
        PartialEquiv.trans_source] using h
    have hraw : ContDiffOn ℝ ∞ (fun w : ℂ ↦ η (T w)) S := by
      exact hη_smooth.contDiffOn.comp hT (fun w _ ↦ Set.mem_univ (T w))
    have hsource_mem : e.source ∈ 𝓝 (c.symm z) :=
      e.open_source.mem_nhds hx_source
    have hpreimage_mem : c.symm ⁻¹' e.source ∈ 𝓝 z :=
      (c.continuousAt_symm hz_target).preimage_mem_nhds hsource_mem
    have hrelative : S ∈ 𝓝[c.target] z := by
      simpa [S] using inter_mem_nhdsWithin c.target hpreimage_mem
    have hraw_at :
        ContDiffWithinAt ℝ ∞ (fun w : ℂ ↦ η (T w)) c.target z :=
      (hraw z ⟨hz_target, hx_source⟩).mono_of_mem_nhdsWithin hrelative
    have hevent :
        (fun w : ℂ ↦ chartTestSurfaceZeroExtension e η (c.symm w)) =ᶠ[𝓝[c.target] z]
          (fun w : ℂ ↦ η (T w)) := by
      filter_upwards [hrelative] with w hw
      exact chartTestSurfaceZeroExtension_apply_of_mem e η hw.2
    have hz_eq :
        chartTestSurfaceZeroExtension e η (c.symm z) = η (T z) :=
      chartTestSurfaceZeroExtension_apply_of_mem e η hx_source
    exact hraw_at.congr_of_eventuallyEq hevent hz_eq
  · have hcoord_zero :
        (fun w : ℂ ↦ chartTestSurfaceZeroExtension e η (c.symm w)) =ᶠ[𝓝 z]
          fun _ : ℂ ↦ (0 : ℝ) := by
      have hzero_surface :
          chartTestSurfaceZeroExtension e η =ᶠ[𝓝 (c.symm z)]
            fun _ : X ↦ (0 : ℝ) :=
        notMem_tsupport_iff_eventuallyEq.mp hx_support
      exact (c.continuousAt_symm hz_target).tendsto.eventually hzero_surface
    have hz_zero :
        chartTestSurfaceZeroExtension e η (c.symm z) = 0 :=
      hcoord_zero.self_of_nhds
    exact
      (contDiffAt_const (𝕜 := ℝ) (x := z) (c := (0 : ℝ))).contDiffWithinAt
        |>.congr_of_eventuallyEq
          (eventually_nhdsWithin_of_eventually_nhds hcoord_zero) hz_zero

theorem surfaceExteriorDerivative_apply_chartTangentMap_of_smooth {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (f : X → ℝ) (hf : IsSmoothOnSurface (Set.univ : Set X) f) :
    ∀ z ∈ e.target, ∀ v : ℂ,
      surfaceExteriorDerivative f (e.symm z)
          (surfaceChartTangentMap e z v) =
        fderiv ℝ (fun w : ℂ ↦ f (e.symm w)) z v := by
  intro z hz v
  have hdf :
      HasMFDerivAt SurfaceRealModel 𝓘(ℝ, ℝ) f (e.symm z)
        (surfaceExteriorDerivative f (e.symm z)) :=
    surfaceExteriorDerivative_isSurfaceDifferential hf (e.symm z)
  have hgrad :
      mfderiv SurfaceRealModel 𝓘(ℝ, ℝ) f (e.symm z) =
        surfaceExteriorDerivative f (e.symm z) :=
    hdf.mfderiv
  have hsymm :
      MDifferentiableWithinAt SurfaceRealModel SurfaceRealModel e.symm e.target z :=
    mdifferentiableOn_atlas_symm (I := SurfaceRealModel) he z hz
  have huniq : UniqueMDiffWithinAt SurfaceRealModel e.target z := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact e.open_target.uniqueDiffWithinAt hz
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
    fderivWithin_of_isOpen e.open_target hz
  rw [← hgrad, ← hwithin, ← htan]
  change
    ((mfderiv SurfaceRealModel 𝓘(ℝ, ℝ) f (e.symm z)).comp
        (mfderivWithin SurfaceRealModel SurfaceRealModel e.symm e.target z)) v =
      (fderivWithin ℝ (fun w : ℂ ↦ f (e.symm w)) e.target z) v
  rw [← hchain]
  simp [SurfaceRealModel]
  rfl

namespace SmoothCompactlySupportedGlobalSurfaceFunction

noncomputable def ofChartTest {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {Ω : Set ℂ}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (hΩ_target : Ω ⊆ e.target) :
    SmoothCompactlySupportedGlobalSurfaceFunction X where
  toFun := chartTestSurfaceZeroExtension e η
  gradient := surfaceExteriorDerivative (chartTestSurfaceZeroExtension e η)
  smooth :=
    chartTestSurfaceZeroExtension_smooth e he η.smooth
      (η.support_subset.trans hΩ_target) η.compact_support
  gradient_eq := by
    intro c hc z hz v
    exact
      surfaceExteriorDerivative_apply_chartTangentMap_of_smooth c hc
        (chartTestSurfaceZeroExtension e η)
        (chartTestSurfaceZeroExtension_smooth e he η.smooth
          (η.support_subset.trans hΩ_target) η.compact_support)
        z hz v
  compact_support :=
    chartTestSurfaceZeroExtension_hasCompactSupport e
      (η.support_subset.trans hΩ_target) η.compact_support

theorem ofChartTest_apply_symm_of_mem_target {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {Ω : Set ℂ}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (hΩ_target : Ω ⊆ e.target) {z : ℂ} (hz : z ∈ e.target) :
    (ofChartTest e he η hΩ_target).toFun (e.symm z) = η z := by
  exact chartTestSurfaceZeroExtension_apply_symm_of_mem e η hz

theorem ofChartTest_tsupport_subset_source {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {Ω : Set ℂ}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (hΩ_target : Ω ⊆ e.target) :
    tsupport (ofChartTest e he η hΩ_target).toFun ⊆ e.source := by
  exact chartTestSurfaceZeroExtension_tsupport_subset_source e
    (η.support_subset.trans hΩ_target) η.compact_support

theorem ofChartTest_tsupport_subset_set {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {Ω : Set ℂ} {U : Set X}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (hΩ_region : Ω ⊆ e.target ∩ e.symm ⁻¹' U) :
    tsupport (ofChartTest e he η (fun _z hz ↦ (hΩ_region hz).1)).toFun ⊆ U := by
  exact chartTestSurfaceZeroExtension_tsupport_subset_set e
    (η.support_subset.trans hΩ_region) η.compact_support

theorem ofChartTest_gradient_apply_symm_of_mem_target {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {Ω : Set ℂ}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (hΩ_target : Ω ⊆ e.target) {z v : ℂ} (hz : z ∈ e.target) :
    (ofChartTest e he η hΩ_target).gradient (e.symm z)
        (surfaceChartTangentMap e z v) =
      fderiv ℝ (η : ℂ → ℝ) z v := by
  let F : SmoothCompactlySupportedGlobalSurfaceFunction X :=
    ofChartTest e he η hΩ_target
  have hevent :
      (fun w : ℂ ↦ F.toFun (e.symm w)) =ᶠ[𝓝 z] (η : ℂ → ℝ) := by
    filter_upwards [e.open_target.mem_nhds hz] with w hw
    simpa [F] using
      chartTestSurfaceZeroExtension_apply_symm_of_mem e (η : ℂ → ℝ) hw
  calc
    (ofChartTest e he η hΩ_target).gradient (e.symm z)
        (surfaceChartTangentMap e z v) =
        fderiv ℝ (fun w : ℂ ↦
          (ofChartTest e he η hΩ_target).toFun (e.symm w)) z v := by
          exact (ofChartTest e he η hΩ_target).gradient_eq e he z hz v
    _ = fderiv ℝ (η : ℂ → ℝ) z v := by
          exact congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v)
            (Filter.EventuallyEq.fderiv_eq hevent)

end SmoothCompactlySupportedGlobalSurfaceFunction

/--
%%handwave
name:
  Weak gradient on a surface region
statement:
  A cotangent field is the weak gradient of a function on a surface region if,
  in every coordinate chart, its coordinate components are the distributional
  first derivatives of the coordinate representative against all smooth
  compactly supported coordinate tests in the corresponding coordinate region.
-/
def IsWeakGradientOnRegion {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (U : Set X) (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ) : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (φ : SmoothCompactlySupportedCoordinateFunction (surfaceChartRegion e U))
    (v : ℂ),
    Integrable
        (fun z ↦ u (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v)
        (MeasureTheory.volume.restrict (surfaceChartRegion e U)) ∧
      Integrable
        (fun z ↦ du (e.symm z) (surfaceChartTangentMap e z v) * φ z)
        (MeasureTheory.volume.restrict (surfaceChartRegion e U)) ∧
        ∫ z in surfaceChartRegion e U,
            u (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume =
          -∫ z in surfaceChartRegion e U,
            du (e.symm z) (surfaceChartTangentMap e z v) * φ z ∂MeasureTheory.volume

/--
%%handwave
name:
  Weak gradients restrict to smaller surface regions
statement:
  If a cotangent field is the weak gradient of a function on a surface region,
  then it is also the weak gradient on every smaller region.
proof:
  A test function compactly supported in the smaller coordinate region is also
  compactly supported in the larger one.  The integrands vanish outside the
  smaller coordinate region, so the two integration-by-parts identities have
  the same integrals.
-/
theorem IsWeakGradientOnRegion.mono_set {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    {V U : Set X} {u : X → ℝ} {du : X → ℂ →L[ℝ] ℝ}
    (hweak : IsWeakGradientOnRegion U u du) (hVU : V ⊆ U) :
    IsWeakGradientOnRegion V u du := by
  intro e he φ v
  let ΩV : Set ℂ := surfaceChartRegion e V
  let ΩU : Set ℂ := surfaceChartRegion e U
  have hΩVU : ΩV ⊆ ΩU := by
    intro z hz
    exact ⟨hz.1, hVU hz.2⟩
  let ψ : SmoothCompactlySupportedCoordinateFunction ΩU :=
    { toFun := φ
      smooth := φ.smooth
      support_subset := φ.support_subset.trans hΩVU
      compact_support := φ.compact_support }
  rcases hweak e he ψ v with ⟨hleftΩ, hrightΩ, heqΩ⟩
  let left : ℂ → ℝ :=
    fun z ↦ u (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
  let right : ℂ → ℝ :=
    fun z ↦ du (e.symm z) (surfaceChartTangentMap e z v) * φ z
  have hleft_int_V : Integrable left (MeasureTheory.volume.restrict ΩV) := by
    have hres := hleftΩ.restrict (s := ΩV)
    simpa [left, ψ, ΩV, ΩU, Measure.restrict_restrict_of_subset hΩVU] using hres
  have hright_int_V : Integrable right (MeasureTheory.volume.restrict ΩV) := by
    have hres := hrightΩ.restrict (s := ΩV)
    simpa [right, ψ, ΩV, ΩU, Measure.restrict_restrict_of_subset hΩVU] using hres
  have hleft_zero_V : ∀ z : ℂ, z ∉ ΩV → left z = 0 := by
    intro z hzV
    have hz_not :
        z ∉ tsupport (fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z v) := by
      intro hz
      exact hzV <| φ.support_subset <|
        (tsupport_fderiv_apply_subset (𝕜 := ℝ)
          (f := (φ : ℂ → ℝ)) v) hz
    have hzero :
        fderiv ℝ (φ : ℂ → ℝ) z v = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : ℂ ↦ fderiv ℝ (φ : ℂ → ℝ) y v) hz_not
    simp [left, hzero]
  have hright_zero_V : ∀ z : ℂ, z ∉ ΩV → right z = 0 := by
    intro z hzV
    have hz_not : z ∉ tsupport (φ : ℂ → ℝ) := by
      intro hz
      exact hzV (φ.support_subset hz)
    have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport hz_not
    simp [right, hzero]
  have hleft_zero_U : ∀ z : ℂ, z ∉ ΩU → left z = 0 := by
    intro z hzU
    exact hleft_zero_V z (fun hzV ↦ hzU (hΩVU hzV))
  have hright_zero_U : ∀ z : ℂ, z ∉ ΩU → right z = 0 := by
    intro z hzU
    exact hright_zero_V z (fun hzV ↦ hzU (hΩVU hzV))
  have hleft_V_eq_U :
      ∫ z in ΩV, left z ∂MeasureTheory.volume =
        ∫ z in ΩU, left z ∂MeasureTheory.volume := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hleft_zero_V,
      setIntegral_eq_integral_of_forall_compl_eq_zero hleft_zero_U]
  have hright_V_eq_U :
      ∫ z in ΩV, right z ∂MeasureTheory.volume =
        ∫ z in ΩU, right z ∂MeasureTheory.volume := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hright_zero_V,
      setIntegral_eq_integral_of_forall_compl_eq_zero hright_zero_U]
  refine ⟨?_, ?_, ?_⟩
  · simpa [left, ΩV] using hleft_int_V
  · simpa [right, ΩV] using hright_int_V
  · calc
      ∫ z in surfaceChartRegion e V,
          u (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume
          = ∫ z in ΩV, left z ∂MeasureTheory.volume := rfl
      _ = ∫ z in ΩU, left z ∂MeasureTheory.volume := hleft_V_eq_U
      _ = -∫ z in ΩU, right z ∂MeasureTheory.volume := by
            simpa [left, right, ψ, ΩU] using heqΩ
      _ = -∫ z in ΩV, right z ∂MeasureTheory.volume := by
            rw [hright_V_eq_U]
      _ = -∫ z in surfaceChartRegion e V,
          du (e.symm z) (surfaceChartTangentMap e z v) * φ z
            ∂MeasureTheory.volume := rfl

/--
%%handwave
name:
  Local weak gradients add
statement:
  The sum of two weak gradients is the weak gradient of the sum of the
  functions on a surface region.
proof:
  Add the two chartwise integration-by-parts identities and use linearity of
  the integral.
-/
theorem IsWeakGradientOnRegion.add {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u₁ u₂ : X → ℝ} {du₁ du₂ : X → ℂ →L[ℝ] ℝ}
    (hu₁ : IsWeakGradientOnRegion U u₁ du₁)
    (hu₂ : IsWeakGradientOnRegion U u₂ du₂) :
    IsWeakGradientOnRegion U (u₁ + u₂) (du₁ + du₂) := by
  intro e he φ v
  rcases hu₁ e he φ v with ⟨hu₁_int, hdu₁_int, h₁_eq⟩
  rcases hu₂ e he φ v with ⟨hu₂_int, hdu₂_int, h₂_eq⟩
  let Ω : Set ℂ := surfaceChartRegion e U
  let μΩ : Measure ℂ := MeasureTheory.volume.restrict Ω
  let lhs₁ : ℂ → ℝ :=
    fun z ↦ u₁ (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
  let lhs₂ : ℂ → ℝ :=
    fun z ↦ u₂ (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
  let rhs₁ : ℂ → ℝ :=
    fun z ↦ du₁ (e.symm z) (surfaceChartTangentMap e z v) * φ z
  let rhs₂ : ℂ → ℝ :=
    fun z ↦ du₂ (e.symm z) (surfaceChartTangentMap e z v) * φ z
  have hrhs_add :
      (fun z ↦ rhs₁ z + rhs₂ z) =
        fun z ↦
          (du₁ + du₂) (e.symm z) (surfaceChartTangentMap e z v) * φ z := by
    ext z
    simp [rhs₁, rhs₂, add_mul]
  have h₁_eq' : ∫ z, lhs₁ z ∂μΩ = -∫ z, rhs₁ z ∂μΩ := by
    simpa [Ω, μΩ, lhs₁, rhs₁] using h₁_eq
  have h₂_eq' : ∫ z, lhs₂ z ∂μΩ = -∫ z, rhs₂ z ∂μΩ := by
    simpa [Ω, μΩ, lhs₂, rhs₂] using h₂_eq
  refine ⟨?_, ?_, ?_⟩
  · convert hu₁_int.add hu₂_int using 1
    ext z
    simp [add_mul]
  · convert hdu₁_int.add hdu₂_int using 1
    ext z
    simp [add_mul]
  · calc
      ∫ z in surfaceChartRegion e U,
          (u₁ + u₂) (e.symm z) *
            fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume
          = ∫ z, lhs₁ z + lhs₂ z ∂μΩ := by
              congr 1
              ext z
              simp [lhs₁, lhs₂, add_mul]
      _ = ∫ z, lhs₁ z ∂μΩ + ∫ z, lhs₂ z ∂μΩ :=
            integral_add hu₁_int hu₂_int
      _ = -∫ z, rhs₁ z ∂μΩ + -∫ z, rhs₂ z ∂μΩ := by
            rw [h₁_eq', h₂_eq']
      _ = -∫ z, rhs₁ z + rhs₂ z ∂μΩ := by
            rw [integral_add hdu₁_int hdu₂_int]
            ring
      _ = -∫ z in surfaceChartRegion e U,
          (du₁ + du₂) (e.symm z) (surfaceChartTangentMap e z v) * φ z
            ∂MeasureTheory.volume := by
              rw [show μΩ = MeasureTheory.volume.restrict Ω from rfl, hrhs_add]

/--
%%handwave
name:
  Local weak gradients scale
statement:
  Multiplying a function and its weak gradient by the same real scalar
  preserves the weak-gradient identity on a surface region.
proof:
  Pull the scalar through both integrals in the chartwise
  integration-by-parts identity.
-/
theorem IsWeakGradientOnRegion.const_smul {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u : X → ℝ} {du : X → ℂ →L[ℝ] ℝ}
    (c : ℝ) (hweak : IsWeakGradientOnRegion U u du) :
    IsWeakGradientOnRegion U (c • u) (c • du) := by
  intro e he φ v
  rcases hweak e he φ v with ⟨hu_int, hdu_int, h_eq⟩
  let Ω : Set ℂ := surfaceChartRegion e U
  let μΩ : Measure ℂ := MeasureTheory.volume.restrict Ω
  let lhs : ℂ → ℝ :=
    fun z ↦ u (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
  let rhs : ℂ → ℝ :=
    fun z ↦ du (e.symm z) (surfaceChartTangentMap e z v) * φ z
  have hrhs_smul :
      (fun z ↦ c * rhs z) =
        fun z ↦
          (c • du) (e.symm z) (surfaceChartTangentMap e z v) * φ z := by
    ext z
    simp [rhs, mul_assoc]
  have h_eq' : ∫ z, lhs z ∂μΩ = -∫ z, rhs z ∂μΩ := by
    simpa [Ω, μΩ, lhs, rhs] using h_eq
  refine ⟨?_, ?_, ?_⟩
  · convert hu_int.const_mul c using 1
    ext z
    simp [mul_assoc]
  · convert hdu_int.const_mul c using 1
    ext z
    simp [mul_assoc]
  · calc
      ∫ z in surfaceChartRegion e U,
          (c • u) (e.symm z) *
            fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume
          = ∫ z, c * lhs z ∂μΩ := by
              congr 1
              ext z
              simp [lhs, mul_assoc]
      _ = c * ∫ z, lhs z ∂μΩ := integral_const_mul c lhs
      _ = c * (-∫ z, rhs z ∂μΩ) := by rw [h_eq']
      _ = -(c * ∫ z, rhs z ∂μΩ) := by ring
      _ = -∫ z, c * rhs z ∂μΩ := by rw [integral_const_mul c rhs]
      _ = -∫ z in surfaceChartRegion e U,
          (c • du) (e.symm z) (surfaceChartTangentMap e z v) * φ z
            ∂MeasureTheory.volume := by
              rw [show μΩ = MeasureTheory.volume.restrict Ω from rfl, hrhs_smul]

/--
%%handwave
name:
  Weak gradient on a surface
statement:
  A cotangent field is the weak gradient of a function on the whole surface if
  it is the weak gradient on the full surface region.  The measure parameter is
  used for \(L^2\) membership in Sobolev spaces; the distributional derivative
  itself is expressed in smooth coordinate charts.
-/
def IsWeakGradientOnSurface {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (_μ : Measure X) (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ) : Prop :=
  IsWeakGradientOnRegion (Set.univ : Set X) u du

/--
%%handwave
name:
  Surface \(W^{1,2}\) function
statement:
  A representative-level surface \(W^{1,2}\) function is an \(L^2\)
  real-valued function together with an \(L^2\) cotangent field which is its
  weak gradient.
-/
structure SobolevH1OnSurface {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (μ : Measure X) where
  /-- The Sobolev representative. -/
  toFun : X → ℝ
  /-- The weak gradient. -/
  weakGradient : X → ℂ →L[ℝ] ℝ
  /-- The function is square-integrable. -/
  memLp_toFun : MemLp toFun 2 μ
  /-- The weak gradient is square-integrable. -/
  memLp_weakGradient : MemLp weakGradient 2 μ
  /-- The stored cotangent field is the weak gradient of the function. -/
  weakGradient_is_gradient : IsWeakGradientOnSurface μ toFun weakGradient

namespace SobolevH1OnSurface

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {μ : Measure X}

instance : CoeFun (SobolevH1OnSurface μ) (fun _ ↦ X → ℝ) where
  coe u := u.toFun

/--
%%handwave
name:
  Hilbert square norm for representative \(W^{1,2}\)
statement:
  The representative \(W^{1,2}\) Hilbert norm squared is the sum of the
  squared \(L^2\) norm of the function and the squared \(L^2\) norm of its
  weak gradient.
-/
def w12NormSq (u : SobolevH1OnSurface μ) : ℝ :=
  (eLpNorm u.toFun 2 μ).toReal ^ 2 +
    (eLpNorm u.weakGradient 2 μ).toReal ^ 2

/--
%%handwave
name:
  Representative \(W^{1,2}\) Hilbert norm
statement:
  The representative \(W^{1,2}\) Hilbert norm is the square root of the sum
  of the squared \(L^2\) norm of the function and the squared \(L^2\) norm of
  its weak gradient.
-/
def w12Norm (u : SobolevH1OnSurface μ) : ℝ :=
  Real.sqrt (w12NormSq u)

end SobolevH1OnSurface

/--
%%handwave
name:
  Strong convergence in global zero-trace \(W^{1,2}\) space
statement:
  A sequence of smooth compactly supported functions converges in the global
  \(W_0^{1,2}\) norm when the functions and their gradients converge in
  \(L^2\).
-/
def TendstoInGlobalSobolevH1Zero {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (μ : Measure X)
    (F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X)
    (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ) : Prop :=
  Filter.Tendsto
      (fun n : ℕ ↦ eLpNorm (fun x ↦ F n x - u x) 2 μ)
      Filter.atTop (𝓝 0) ∧
    Filter.Tendsto
      (fun n : ℕ ↦ eLpNorm (fun x ↦ (F n).gradient x - du x) 2 μ)
      Filter.atTop (𝓝 0)

/--
%%handwave
name:
  Global zero Sobolev trace
statement:
  A Sobolev function has zero trace at infinity when it is a \(W^{1,2}\)-limit
  of smooth compactly supported functions.
-/
def HasGlobalZeroSobolevTrace {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (μ : Measure X) (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ) : Prop :=
  ∃ F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X,
    TendstoInGlobalSobolevH1Zero μ F u du

/--
%%handwave
name:
  Global zero-trace \(W^{1,2}\) function
statement:
  A representative-level global \(W_0^{1,2}\) function is an \(L^2\) function
  together with its \(L^2\) weak gradient, approximable by smooth compactly
  supported functions.
-/
structure SobolevH1ZeroOnSurface {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (μ : Measure X) where
  /-- The Sobolev representative. -/
  toFun : X → ℝ
  /-- The weak gradient. -/
  weakGradient : X → ℂ →L[ℝ] ℝ
  /-- The function is square-integrable. -/
  memLp_toFun : MemLp toFun 2 μ
  /-- The weak gradient is square-integrable. -/
  memLp_weakGradient : MemLp weakGradient 2 μ
  /-- The stored cotangent field is the weak gradient of the function. -/
  weakGradient_is_gradient : IsWeakGradientOnSurface μ toFun weakGradient
  /-- The function has zero trace at infinity. -/
  zero_trace : HasGlobalZeroSobolevTrace μ toFun weakGradient

namespace SobolevH1ZeroOnSurface

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {μ : Measure X}

instance : CoeFun (SobolevH1ZeroOnSurface μ) (fun _ ↦ X → ℝ) where
  coe u := u.toFun

/--
%%handwave
name:
  Hilbert square norm for representative zero-trace \(W^{1,2}\)
statement:
  The representative \(W_0^{1,2}\) Hilbert norm squared is the sum of the
  squared \(L^2\) norm of the function and the squared \(L^2\) norm of its
  weak gradient.
-/
def w12NormSq (u : SobolevH1ZeroOnSurface μ) : ℝ :=
  (eLpNorm u.toFun 2 μ).toReal ^ 2 +
    (eLpNorm u.weakGradient 2 μ).toReal ^ 2

/--
%%handwave
name:
  Representative zero-trace \(W^{1,2}\) Hilbert norm
statement:
  The representative \(W_0^{1,2}\) Hilbert norm is the square root of the sum
  of the squared \(L^2\) norm of the function and the squared \(L^2\) norm of
  its weak gradient.
-/
def w12Norm (u : SobolevH1ZeroOnSurface μ) : ℝ :=
  Real.sqrt (w12NormSq u)

/--
%%handwave
name:
  Ambient gradient square seminorm on \(H^1_0\)
statement:
  The representative ambient gradient seminorm squared on the zero-trace
  Sobolev space is the squared \(L^2\) norm of the weak gradient, using the
  fixed model norm on cotangent coordinates.  The geometric Dirichlet energy
  is defined separately from the background metric.
-/
def dirichletNormSq (u : SobolevH1ZeroOnSurface μ) : ℝ :=
  (eLpNorm u.weakGradient 2 μ).toReal ^ 2

/--
%%handwave
name:
  Ambient gradient seminorm on \(H^1_0\)
statement:
  The representative ambient gradient seminorm on \(H^1_0\) is the \(L^2\)
  norm of the weak gradient, using the fixed model norm on cotangent
  coordinates.
-/
def dirichletNorm (u : SobolevH1ZeroOnSurface μ) : ℝ :=
  (eLpNorm u.weakGradient 2 μ).toReal

/--
%%handwave
name:
  Forgetting the zero trace
statement:
  A zero-trace Sobolev function is, in particular, a Sobolev \(W^{1,2}\)
  function.
-/
def toSobolevH1 (u : SobolevH1ZeroOnSurface μ) : SobolevH1OnSurface μ where
  toFun := u.toFun
  weakGradient := u.weakGradient
  memLp_toFun := u.memLp_toFun
  memLp_weakGradient := u.memLp_weakGradient
  weakGradient_is_gradient := u.weakGradient_is_gradient

end SobolevH1ZeroOnSurface

/--
%%handwave
name:
  Local Sobolev regularity on a surface
statement:
  A function is locally \(W^{1,2}\) on a surface region, with a chosen weak
  gradient, if the chosen cotangent field is its weak gradient on the region
  and both the function and the chosen gradient are square-integrable on every
  compact subset of the region.
-/
def IsLocalSobolevH1OnSurface {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (μ : Measure X) (U : Set X) (u : X → ℝ)
    (du : X → ℂ →L[ℝ] ℝ) : Prop :=
  IsWeakGradientOnRegion U u du ∧
    ∀ K : Set X, IsCompact K → K ⊆ U →
      MemLp u 2 (μ.restrict K) ∧ MemLp du 2 (μ.restrict K)

namespace SobolevH1ZeroOnSurface

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {μ : Measure X}

/--
%%handwave
name:
  Zero-trace Sobolev functions are locally Sobolev
statement:
  A global zero-trace \(W^{1,2}\) surface function, together with its stored
  weak gradient, is locally \(W^{1,2}\) on every surface region.
proof:
  Restrict the global weak-gradient identity to the region.  The global
  \(L^2\) bounds restrict to every compact subset of the region.
-/
theorem isLocalSobolevH1OnSurface (u : SobolevH1ZeroOnSurface μ)
    (U : Set X) :
    IsLocalSobolevH1OnSurface μ U u.toFun u.weakGradient := by
  refine ⟨?_, ?_⟩
  · exact u.weakGradient_is_gradient.mono_set (Set.subset_univ U)
  · intro K _hK _hKU
    exact ⟨u.memLp_toFun.mono_measure Measure.restrict_le_self,
      u.memLp_weakGradient.mono_measure Measure.restrict_le_self⟩

end SobolevH1ZeroOnSurface

/--
%%handwave
name:
  Local \(L^2\) seminorm on a surface set
statement:
  The local \(L^2\) seminorm squared of a real-valued function on a set is the
  integral of its square over that set.
-/
def surfaceLocalL2SeminormSq {X : Type} [MeasurableSpace X]
    (μ : Measure X) (K : Set X) (u : X → ℝ) : ℝ :=
  ∫ x in K, u x ^ 2 ∂μ

/--
%%handwave
name:
  Local gradient seminorm on a surface set
statement:
  The local gradient seminorm squared on a set is the integral of the
  background cotangent norm squared of the weak gradient over that set.
-/
def surfaceLocalGradientSeminormSq {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) (K : Set X)
    (du : X → ℂ →L[ℝ] ℝ) : ℝ :=
  ∫ x in K, g.gradientInner x (du x) (du x) ∂g.volume

/--
%%handwave
name:
  Local \(W^{1,2}\) seminorm on a surface set
statement:
  The local \(W^{1,2}\) seminorm squared on a set is the sum of the local
  \(L^2\) seminorm squared and the local gradient seminorm squared.
-/
def surfaceLocalH1SeminormSq {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) (K : Set X)
    (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ) : ℝ :=
  surfaceLocalL2SeminormSq g.volume K u +
    surfaceLocalGradientSeminormSq g K du

/--
%%handwave
name:
  Bounded local Sobolev family
statement:
  A sequence of surface Sobolev functions is bounded in \(W^{1,2}\) on a set
  if the local \(W^{1,2}\) seminorms of the sequence on that set are uniformly
  bounded.
-/
def BoundedInLocalSobolevH1OnSurface {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) (K : Set X)
    (H : ℕ → SobolevH1OnSurface g.volume) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ,
    surfaceLocalH1SeminormSq g K (H n).toFun (H n).weakGradient ≤ C

/--
%%handwave
name:
  Local \(L^2\) convergence on a compact set
statement:
  A sequence of functions converges locally in \(L^2\) on a set if the
  \(L^2\) seminorm of the difference on that set tends to zero.
-/
def TendstoInLocalL2OnSurface {X : Type} [MeasurableSpace X]
    (μ : Measure X) (K : Set X) (H : ℕ → X → ℝ) (u : X → ℝ) : Prop :=
  Filter.Tendsto
    (fun n : ℕ ↦ eLpNorm (fun x ↦ H n x - u x) 2 (μ.restrict K))
    Filter.atTop (𝓝 0)

end

end Uniformization

end JJMath
