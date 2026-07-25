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
  Directional derivative of a coordinate test
statement:
  If $\eta$ is a smooth compactly supported test on
  $\Omega\subseteq\mathbb C$ and $v\in\mathbb C$, then
  $z\mapsto D\eta(z)v$ is another smooth compactly supported test on
  $\Omega$.
proof:
  Smoothness is preserved by differentiation. The support of a derivative is
  contained in the closed support of the original test, so compactness and
  containment in $\Omega$ are inherited.
-/
def directionalDerivative
    {Ω : Set ℂ}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction Ω) (v : ℂ) :
    SmoothCompactlySupportedManifoldCoordinateFunction Ω where
  toFun := fun z ↦ fderiv ℝ (η : ℂ → ℝ) z v
  smooth := by
    have hD :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z ↦ fderiv ℝ (η : ℂ → ℝ) z) :=
      η.smooth.fderiv_right (by simp)
    exact hD.clm_apply contDiff_const
  support_subset :=
    (tsupport_fderiv_apply_subset (𝕜 := ℝ)
      (f := (η : ℂ → ℝ)) v).trans η.support_subset
  compact_support :=
    η.compact_support.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := (η : ℂ → ℝ)) v)

/--
%%handwave
name:
  Value of a directional-derivative test
statement:
  The directional-derivative test associated to $\eta$ and $v$ has value
  $D\eta(z)v$ at every $z\in\mathbb C$.
proof:
  This is its defining function.
-/
@[simp]
theorem directionalDerivative_apply
    {Ω : Set ℂ}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction Ω) (v z : ℂ) :
    η.directionalDerivative v z = fderiv ℝ (η : ℂ → ℝ) z v :=
  rfl

/--
%%handwave
name:
  Commutation of directional derivatives of a coordinate test
statement:
  If $\eta$ is a smooth compactly supported test and $v,w\in\mathbb C$, then
  $$
    D(D\eta(\,\cdot\,)v)(z)w=D(D\eta(\,\cdot\,)w)(z)v
  $$
  for every $z\in\mathbb C$.
proof:
  A smooth real-valued function has a symmetric second Fréchet derivative.
-/
theorem fderiv_directionalDerivative_comm
    {Ω : Set ℂ}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction Ω) (v w z : ℂ) :
    fderiv ℝ (η.directionalDerivative v : ℂ → ℝ) z w =
      fderiv ℝ (η.directionalDerivative w : ℂ → ℝ) z v := by
  have hs := ContDiffAt.isSymmSndFDerivAt (x := z)
    η.smooth.contDiffAt (by
      simpa [minSmoothness] using
        (WithTop.coe_le_coe.mpr
          (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
  have htwo_top :
      ((2 : ℕ∞) : WithTop ℕ∞) ≤ (((⊤ : ℕ∞) : WithTop ℕ∞)) :=
    WithTop.coe_le_coe.mpr le_top
  have hD :
      DifferentiableAt ℝ (fun y ↦ fderiv ℝ (η : ℂ → ℝ) y) z :=
    (η.smooth.contDiffAt.fderiv_right (m := 1)
      (by simpa using htwo_top)).differentiableAt
        (by norm_num)
  change
    fderiv ℝ (fun y ↦ fderiv ℝ (η : ℂ → ℝ) y v) z w =
      fderiv ℝ (fun y ↦ fderiv ℝ (η : ℂ → ℝ) y w) z v
  rw [fderiv_clm_apply hD (differentiableAt_const v),
    fderiv_clm_apply hD (differentiableAt_const w)]
  simpa using hs.eq w v

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








end

end Uniformization

end JJMath
