import JJMath.Hyperbolic.Converse.Setup.LocalSolving

/-!
# Split partial-converse setup declarations
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/-- A pointed tangent frame in the upper half-plane model. -/
structure UpperHalfPlaneTangentFrame where
  /-- The base point of the frame. -/
  base : ℍ
  /-- The complex tangent vector in the standard coordinate. -/
  tangent : ℂ
  /-- A frame vector is nonzero. -/
  tangent_ne_zero : tangent ≠ 0

namespace UpperHalfPlaneTangentFrame

/-- Squared hyperbolic norm of an upper-half-plane tangent frame. -/
def hyperbolicNormSq (F : UpperHalfPlaneTangentFrame) : ℝ :=
  Complex.normSq F.tangent / ((F.base : ℂ).im ^ 2)

end UpperHalfPlaneTangentFrame

/--
The complex derivative of a real Mobius representative at a point of `ℍ`.

This is the tangent multiplier for the standard upper-half-plane coordinate.
-/
def realMobiusRepresentativeDerivativeAt
    (A : RealMobiusRepresentative) (p : ℍ) : ℂ :=
  deriv
    (fun z : ℂ ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
    p

/-- A real Mobius representative maps one pointed tangent frame to another. -/
def RealMobiusRepresentativeMapsTangentFrame
    (A : RealMobiusRepresentative)
    (F G : UpperHalfPlaneTangentFrame) : Prop :=
  G.base = realMobiusRepresentativeAction A F.base ∧
    G.tangent = realMobiusRepresentativeDerivativeAt A F.base * F.tangent

/--
Frame-transitivity target for the upper-half-plane real Mobius action.

The intended analytic input is the standard fact that orientation-preserving
hyperbolic isometries act transitively on pointed tangent frames with the same
positive hyperbolic length.
-/
def RealMobiusTangentFrameTransitivityTheorem : Prop :=
  ∀ F G : UpperHalfPlaneTangentFrame,
    F.hyperbolicNormSq = G.hyperbolicNormSq →
      ∃ A : RealMobiusRepresentative,
        RealMobiusRepresentativeMapsTangentFrame A F G

/--
Real Mobius transformations act transitively on upper-half-plane tangent
frames with the same squared hyperbolic norm.

Move the base point of the first frame to the base point of the second, then
use a conjugated rotation in the stabilizer of the second base point to match
the transported tangent vector.
-/
theorem realMobiusTangentFrameTransitivityTheorem :
    RealMobiusTangentFrameTransitivityTheorem := by
  intro F G hNorm
  rcases realMobiusValueTransitivityOnUpperHalfPlaneTheorem F.base G.base with
    ⟨A, hA⟩
  let vA : ℂ := realMobiusRepresentativeDerivativeAt A F.base * F.tangent
  have hvA_norm : Complex.normSq vA = Complex.normSq G.tangent := by
    dsimp [vA, realMobiusRepresentativeDerivativeAt]
    exact
      realMobiusRepresentativeAction_deriv_mul_normSq_eq_of_hyperbolicNormSq
        A F.base (by
          simpa [UpperHalfPlaneTangentFrame.hyperbolicNormSq, hA] using hNorm)
  have hvA_ne : vA ≠ 0 := by
    dsimp [vA, realMobiusRepresentativeDerivativeAt]
    exact mul_ne_zero
      (realMobiusRepresentativeAction_deriv_ne_zero A F.base)
      F.tangent_ne_zero
  let dMinv : ℂ :=
    deriv
      (fun z : ℂ ↦
        (realMobiusRepresentativeAction ((realMobiusRepresentativeMapITo G.base)⁻¹)
          ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
      G.base
  have hdMinv_ne : dMinv ≠ 0 := by
    dsimp [dMinv]
    exact realMobiusRepresentativeAction_deriv_ne_zero
      ((realMobiusRepresentativeMapITo G.base)⁻¹) G.base
  have htransport_ne : dMinv * vA ≠ 0 :=
    mul_ne_zero hdMinv_ne hvA_ne
  have htransport_norm :
      Complex.normSq (dMinv * vA) =
        Complex.normSq (dMinv * G.tangent) := by
    calc
      Complex.normSq (dMinv * vA) =
          Complex.normSq dMinv * Complex.normSq vA := by
        rw [Complex.normSq_mul]
      _ = Complex.normSq dMinv * Complex.normSq G.tangent := by
        rw [hvA_norm]
      _ = Complex.normSq (dMinv * G.tangent) := by
        rw [Complex.normSq_mul]
  rcases realMobiusRotationAtITangentTransitivityTheorem
      (dMinv * vA) (dMinv * G.tangent) htransport_ne htransport_norm with
    ⟨θ, hθ⟩
  let R : RealMobiusRepresentative := realMobiusConjugatedRotationAt G.base θ
  refine ⟨R * A, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [realMobiusRepresentativeAction_mul, ← hA]
    exact (realMobiusConjugatedRotationAt_fixes G.base θ).symm
  · have hmul :
        realMobiusRepresentativeDerivativeAt (R * A) F.base =
          realMobiusRepresentativeDerivativeAt R G.base *
            realMobiusRepresentativeDerivativeAt A F.base := by
      dsimp [realMobiusRepresentativeDerivativeAt]
      exact realMobiusRepresentativeAction_deriv_mul_of_action_eq R A F.base G.base hA
    have hR :
        realMobiusRepresentativeDerivativeAt R G.base * vA = G.tangent := by
      dsimp [R, realMobiusRepresentativeDerivativeAt]
      exact realMobiusConjugatedRotationAt_deriv_mul_eq_of_transported
        G.base θ vA G.tangent (by simpa [dMinv] using hθ)
    calc
      G.tangent = realMobiusRepresentativeDerivativeAt R G.base * vA := hR.symm
      _ = realMobiusRepresentativeDerivativeAt (R * A) F.base * F.tangent := by
        rw [hmul]
        dsimp [vA]
        ring

/--
The local expression of a hyperbolic chart in the ambient complex coordinate
at a surface point.
-/
def hyperbolicLocalChartCoordinateExpressionAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U : HyperbolicLocalChart X g) (x₀ : X) (z : ℂ) : ℂ :=
  (U.toUpperHalfPlane ((chartAt ℂ x₀).symm z) : ℂ)

/--
The complex derivative of a hyperbolic local chart in the ambient coordinate
at a surface point.
-/
def hyperbolicLocalChartCoordinateDerivativeAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U : HyperbolicLocalChart X g) (x₀ : X) : ℂ :=
  deriv (hyperbolicLocalChartCoordinateExpressionAt U x₀) ((chartAt ℂ x₀) x₀)

/--
The squared density of the source metric in the ambient chart used to compute
the coordinate derivative at the pointed surface point.
-/
def hyperbolicLocalChartCoordinateDensitySqAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (_U : HyperbolicLocalChart X g) (x₀ : X) : ℝ :=
  g.toConformalMetric.densitySqInChart
    (chartAt ℂ x₀)
    (chart_mem_atlas ℂ x₀)
    ((chartAt ℂ x₀) x₀)

/-- The ambient chartwise density is positive at the pointed surface point. -/
theorem hyperbolicLocalChartCoordinateDensitySqAt_pos
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U : HyperbolicLocalChart X g) {x₀ : X} (_hx₀ : x₀ ∈ U.domain) :
    0 < hyperbolicLocalChartCoordinateDensitySqAt U x₀ := by
  have hsource : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  have htarget :
      (chartAt ℂ x₀) x₀ ∈ (chartAt ℂ x₀).target :=
    (chartAt ℂ x₀).map_source hsource
  simpa [hyperbolicLocalChartCoordinateDensitySqAt] using
    (g.toConformalMetric.positive_densitySqInChart
      (chartAt ℂ x₀) (chart_mem_atlas ℂ x₀) htarget)

/--
The normalized derivative vector of a hyperbolic local chart.

The coordinate derivative is divided by the square root of the source squared
metric density, so the Poincare pullback formula makes the result a unit
hyperbolic tangent vector.
-/
def hyperbolicLocalChartNormalizedCoordinateDerivativeAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U : HyperbolicLocalChart X g) (x₀ : X) : ℂ :=
  hyperbolicLocalChartCoordinateDerivativeAt U x₀ /
    (Real.sqrt (hyperbolicLocalChartCoordinateDensitySqAt U x₀) : ℂ)

/--
A chart frame realized by a hyperbolic local coordinate at a chosen surface
point.

The final field is now an actual equality: the frame tangent is the canonical
normalized coordinate derivative of the chart.
-/
structure HyperbolicLocalChartPointedFrame
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U : HyperbolicLocalChart X g) (x₀ : X) where
  /-- The upper-half-plane tangent frame. -/
  frame : UpperHalfPlaneTangentFrame
  /-- The surface point lies in the local chart domain. -/
  mem_domain : x₀ ∈ U.domain
  /-- The frame is based at the value of the local chart. -/
  base_eq : frame.base = U.toUpperHalfPlane x₀
  /-- We normalize to a unit hyperbolic frame. -/
  unit_hyperbolicNormSq : frame.hyperbolicNormSq = 1
  /-- The frame tangent is the normalized coordinate derivative of the local chart. -/
  represents_oriented_derivative :
    frame.tangent = hyperbolicLocalChartNormalizedCoordinateDerivativeAt U x₀

/--
The pointwise Poincare pullback squared-density formula for a hyperbolic
local chart in the ambient complex coordinate.
-/
def HyperbolicLocalChartPullbackSquaredDensityFormulaAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U : HyperbolicLocalChart X g) (x₀ : X) : Prop :=
  Complex.normSq (hyperbolicLocalChartCoordinateDerivativeAt U x₀) /
      ((U.toUpperHalfPlane x₀ : ℂ).im ^ 2) =
    hyperbolicLocalChartCoordinateDensitySqAt U x₀

/--
The local-isometry boundary saying that the abstract pullback-metric field of
a hyperbolic local chart gives the concrete ambient-coordinate squared-density
formula.
-/
def HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U : HyperbolicLocalChart X g) (x₀ : X),
    x₀ ∈ U.domain →
      HyperbolicLocalChartPullbackSquaredDensityFormulaAt U x₀

/--
The stored local-isometry pullback identity gives the concrete ambient
`chartAt` squared-density formula.

The only real content is the chart change from the local chart coordinate
stored in `U.local_isometry` to the ambient coordinate centered at `x₀`.
Riemann-surface regularity supplies differentiability of that transition; the
metric transition law and the chain rule then cancel the same transition
derivative on both sides.
-/
theorem hyperbolicLocalChart_pullbackSquaredDensityFormulaAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    {g : HyperbolicMetric X} (U : HyperbolicLocalChart X g) {x₀ : X}
    (hx₀ : x₀ ∈ U.domain) :
    HyperbolicLocalChartPullbackSquaredDensityFormulaAt U x₀ := by
  let L := U.local_isometry
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀
  let z₀ : ℂ := e x₀
  let τ : ℂ → ℂ := fun z ↦ L.chart (e.symm z)
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
      Filter.EventuallyEq (nhds z₀)
        (hyperbolicLocalChartCoordinateExpressionAt U x₀)
        (fun z : ℂ ↦ (L.localMap (τ z) : ℂ)) := by
    filter_upwards [hdomain] with z hz
    dsimp [hyperbolicLocalChartCoordinateExpressionAt, τ]
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
      DifferentiableAt ℂ (fun z : ℂ ↦ (L.localMap z : ℂ))
        (L.coordinate x₀) :=
    L.holomorphic_on_domain (L.coordinate x₀)
      (L.coordinate_mem_domain x₀ hx₀)
  have hchain :
      deriv (hyperbolicLocalChartCoordinateExpressionAt U x₀) z₀ =
        deriv (fun z : ℂ ↦ (L.localMap z : ℂ)) (L.coordinate x₀) *
          deriv τ z₀ := by
    calc
      deriv (hyperbolicLocalChartCoordinateExpressionAt U x₀) z₀ =
          deriv (fun z : ℂ ↦ (L.localMap (τ z) : ℂ)) z₀ :=
        Filter.EventuallyEq.deriv_eq hExpr
      _ =
          deriv (fun z : ℂ ↦ (L.localMap z : ℂ)) (L.coordinate x₀) *
            deriv τ z₀ := by
            simpa [Function.comp_def, hτ_point] using
              (deriv_comp_of_eq z₀ hlocal_diff hτ_diff hτ_point)
  have hnorm :
      Complex.normSq (hyperbolicLocalChartCoordinateDerivativeAt U x₀) =
        Complex.normSq
            (deriv (fun z : ℂ ↦ (L.localMap z : ℂ)) (L.coordinate x₀)) *
          Complex.normSq (deriv τ z₀) := by
    rw [hyperbolicLocalChartCoordinateDerivativeAt]
    dsimp [z₀] at hchain
    rw [hchain]
    exact Complex.normSq_mul _ _
  have hstored :
      g.toConformalMetric.densitySqInChart L.chart L.chart_mem_atlas
          (L.coordinate x₀) =
        Complex.normSq
            (deriv (fun z : ℂ ↦ (L.localMap z : ℂ)) (L.coordinate x₀)) /
          ((U.toUpperHalfPlane x₀ : ℂ).im ^ 2) :=
    L.pulls_back_metric_on_domain x₀ hx₀
  have hchart_point : L.chart x₀ = L.coordinate x₀ :=
    (L.coordinate_eq_chart hx₀).symm
  have hdensity_transition :
      hyperbolicLocalChartCoordinateDensitySqAt U x₀ =
        g.toConformalMetric.densitySqInChart L.chart L.chart_mem_atlas
            (L.coordinate x₀) *
          Complex.normSq (deriv τ z₀) := by
    have htransition :=
      g.toConformalMetric.densitySq_transition e (chart_mem_atlas ℂ x₀)
        L.chart L.chart_mem_atlas hz₀_target (by
          dsimp [z₀] at hsymm_z₀
          rw [hsymm_z₀]
          exact hx₀_Lsource)
    dsimp [hyperbolicLocalChartCoordinateDensitySqAt, e, z₀, τ] at htransition ⊢
    simpa [e, z₀, τ, hsymm_z₀, hchart_point] using htransition
  change
    Complex.normSq (hyperbolicLocalChartCoordinateDerivativeAt U x₀) /
        ((U.toUpperHalfPlane x₀ : ℂ).im ^ 2) =
      hyperbolicLocalChartCoordinateDensitySqAt U x₀
  rw [hnorm, hdensity_transition, hstored]
  ring

/--
Every hyperbolic local chart satisfies the concrete ambient-coordinate
Poincare pullback squared-density formula on a Riemann surface.
-/
theorem hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X] :
    HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X := by
  intro g U x₀ hx₀
  exact hyperbolicLocalChart_pullbackSquaredDensityFormulaAt U hx₀

/--
The local-biholomorphism boundary saying that the ambient-coordinate
derivative of a hyperbolic local chart is nonzero.
-/
def HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U : HyperbolicLocalChart X g) (x₀ : X),
    x₀ ∈ U.domain →
      hyperbolicLocalChartCoordinateDerivativeAt U x₀ ≠ 0

/--
The Poincare pullback squared-density formula forces the coordinate
derivative to be nonzero, since the source conformal density is positive.
-/
theorem HyperbolicLocalChartPullbackSquaredDensityFormulaAt.coordinateDerivative_ne_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U : HyperbolicLocalChart X g} {x₀ : X}
    (hPull : HyperbolicLocalChartPullbackSquaredDensityFormulaAt U x₀)
    (hx₀ : x₀ ∈ U.domain) :
    hyperbolicLocalChartCoordinateDerivativeAt U x₀ ≠ 0 := by
  intro hzeroDeriv
  have hzero :
      Complex.normSq (hyperbolicLocalChartCoordinateDerivativeAt U x₀) /
          ((U.toUpperHalfPlane x₀ : ℂ).im ^ 2) = 0 := by
    simp [hzeroDeriv]
  have h0 :
      0 = hyperbolicLocalChartCoordinateDensitySqAt U x₀ :=
    hzero.symm.trans hPull
  exact (ne_of_gt (hyperbolicLocalChartCoordinateDensitySqAt_pos U hx₀)) h0.symm

/--
The concrete pullback squared-density formula supplies nonvanishing of the
ambient-coordinate derivative.
-/
def hyperbolicLocalChartCoordinateDerivativeNonzeroTheorem_of_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X) :
    HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X := by
  intro g U x₀ hx₀
  exact (hPull g U x₀ hx₀).coordinateDerivative_ne_zero hx₀

/--
The coordinate-level pullback squared-density formula stored in a
`CoordinateUpperHalfPlanePullbackFormula`, written in the same orientation as
the hyperbolic local-chart formula.
-/
def CoordinateUpperHalfPlanePullbackSquaredDensityFormulaAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) (x₀ : X) : Prop :=
  complexDerivativeNormSq F.localMap (F.coordinate x₀) /
      ((F.localMap (F.coordinate x₀) : ℂ).im ^ 2) =
    g.toConformalMetric.densitySqInChart F.chart F.chart_mem_atlas (F.coordinate x₀)

/--
A coordinate pullback formula immediately gives its stored coordinate-level
Poincare squared-density identity.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.pullbackSquaredDensityFormulaAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hx₀ : x₀ ∈ F.domain) :
    CoordinateUpperHalfPlanePullbackSquaredDensityFormulaAt F x₀ :=
  (F.densitySqInChart_eq_pullback x₀ hx₀).symm

/--
If the stored coordinate is locally the ambient chart at `x₀`, then the
chartwise density used by a coordinate pullback formula agrees at `x₀` with
the ambient `chartAt` density.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.densitySqInChart_eq_chartAt_of_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hx₀ : x₀ ∈ F.domain)
    (hEq : Set.EqOn F.coordinate (chartAt ℂ x₀) F.domain) :
    g.toConformalMetric.densitySqInChart F.chart F.chart_mem_atlas (F.coordinate x₀) =
      g.toConformalMetric.densitySqInChart (chartAt ℂ x₀)
        (chart_mem_atlas ℂ x₀) ((chartAt ℂ x₀) x₀) := by
  let z₀ : ℂ := (chartAt ℂ x₀) x₀
  have htarget : z₀ ∈ (chartAt ℂ x₀).target := by
    simp [z₀]
  have hsymm : (chartAt ℂ x₀).symm z₀ = x₀ := by
    simp [z₀]
  have hstored_source : (chartAt ℂ x₀).symm z₀ ∈ F.chart.source := by
    simpa [hsymm] using F.domain_subset_chart_source hx₀
  have hpoint :
      F.chart ((chartAt ℂ x₀).symm z₀) = F.coordinate x₀ := by
    rw [hsymm]
    exact (F.coordinate_eq_chart hx₀).symm
  have hdomain :
      ∀ᶠ z in nhds z₀, (chartAt ℂ x₀).symm z ∈ F.domain :=
    ((chartAt ℂ x₀).tendsto_symm (mem_chart_source ℂ x₀))
      (F.isOpen_domain.mem_nhds hx₀)
  have hright :
      ∀ᶠ z in nhds z₀,
        (chartAt ℂ x₀) ((chartAt ℂ x₀).symm z) = z := by
    simpa [z₀] using
      (chartAt ℂ x₀).eventually_right_inverse (mem_chart_target ℂ x₀)
  have htransition_eventual :
      Filter.EventuallyEq (nhds z₀)
        (fun z : ℂ ↦ F.chart ((chartAt ℂ x₀).symm z))
        (fun z : ℂ ↦ z) := by
    filter_upwards [hdomain, hright] with z hzdomain hzright
    exact (F.coordinate_eq_chart hzdomain).symm.trans ((hEq hzdomain).trans hzright)
  have hderiv :
      deriv (fun z : ℂ ↦ F.chart ((chartAt ℂ x₀).symm z)) z₀ = 1 := by
    simpa using Filter.EventuallyEq.deriv_eq htransition_eventual
  have htransition :=
    g.toConformalMetric.densitySq_transition
      (chartAt ℂ x₀) (chart_mem_atlas ℂ x₀)
      F.chart F.chart_mem_atlas
      htarget hstored_source
  rw [hpoint, hderiv] at htransition
  simpa [z₀] using htransition.symm

/--
For a coordinate pullback formula, the stored coordinate derivative is nonzero
on the surface domain.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.coordinateDerivative_ne_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hx₀ : x₀ ∈ F.domain) :
    deriv (fun z : ℂ ↦ (F.localMap z : ℂ)) (F.coordinate x₀) ≠ 0 :=
  F.derivative_ne_zero_on_domain x₀ hx₀

/--
Orientation-preservation datum carried by a coordinate pullback formula at a
surface point.

At this lightweight stage holomorphicity and local-biholomorphism are still
abstract propositions, so the oriented-derivative assertion is recorded as the
standard package of those fields plus membership in the formula domain.
-/
def CoordinateUpperHalfPlanePullbackFormulaOrientationPreservingAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) (x₀ : X) : Prop :=
  CoordinateUpperHalfPlaneMapHolomorphicOn F.coordinateDomain F.localMap ∧
    CoordinateUpperHalfPlaneMapDerivativeNonzeroOn F.coordinateDomain F.localMap ∧
      x₀ ∈ F.domain

/--
Derivative identification boundary for extracting the ambient local-chart
formula from a coordinate pullback formula.

The coordinate formula already knows the derivative norm of the explicit
coordinate map.  To use it for the hyperbolic local chart induced by the
surface chart, we must identify that norm with the derivative of
`toUpperHalfPlane ∘ (chartAt ℂ x₀).symm`.
-/
def CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) (x₀ : X) : Prop :=
  Complex.normSq
      (hyperbolicLocalChartCoordinateDerivativeAt
        F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀) =
    complexDerivativeNormSq F.localMap (F.coordinate x₀)

/--
Actual derivative identification for extracting the ambient local-chart
derivative from a coordinate pullback formula.
-/
def CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) (x₀ : X) : Prop :=
  hyperbolicLocalChartCoordinateDerivativeAt
      F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ =
    deriv (fun z : ℂ ↦ (F.localMap z : ℂ)) (F.coordinate x₀)

/--
The ambient-coordinate expression of the local chart induced by a coordinate
pullback formula agrees near `x₀` with the stored coordinate map.
-/
def CoordinateUpperHalfPlanePullbackFormulaAmbientExpressionEventuallyEqAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) (x₀ : X) : Prop :=
  Filter.EventuallyEq (nhds ((chartAt ℂ x₀) x₀))
    (fun z : ℂ ↦
      (F.localMap (F.coordinate ((chartAt ℂ x₀).symm z)) : ℂ))
    (fun z : ℂ ↦ (F.localMap z : ℂ))

/--
The source-coordinate part of the ambient expression: after passing to the
surface chart centered at `x₀`, the stored coordinate is locally the identity.
-/
def CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) (x₀ : X) : Prop :=
  F.coordinate x₀ = (chartAt ℂ x₀) x₀ ∧
    Filter.EventuallyEq (nhds ((chartAt ℂ x₀) x₀))
      (fun z : ℂ ↦ F.coordinate ((chartAt ℂ x₀).symm z))
      (fun z : ℂ ↦ z)

/--
If the stored coordinate agrees with the ambient chart on the formula domain,
then it is locally the ambient coordinate after passing through the inverse
chart at any domain point.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.ambientCoordinateEventuallyEqAt_of_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hx₀ : x₀ ∈ F.domain)
    (hEq : Set.EqOn F.coordinate (chartAt ℂ x₀) F.domain) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt F x₀ := by
  constructor
  · exact hEq hx₀
  · have hdomain :
        ∀ᶠ z in nhds ((chartAt ℂ x₀) x₀),
          (chartAt ℂ x₀).symm z ∈ F.domain :=
      ((chartAt ℂ x₀).tendsto_symm (mem_chart_source ℂ x₀))
        (F.isOpen_domain.mem_nhds hx₀)
    have hright :
        ∀ᶠ z in nhds ((chartAt ℂ x₀) x₀),
          (chartAt ℂ x₀) ((chartAt ℂ x₀).symm z) = z :=
      (chartAt ℂ x₀).eventually_right_inverse (mem_chart_target ℂ x₀)
    filter_upwards [hdomain, hright] with z hzdomain hzright
    exact (hEq hzdomain).trans hzright

/--
The local ambient-coordinate identity is enough to compare the stored
chartwise density with the ambient `chartAt` density at the point.  This is
the local replacement for requiring the stored coordinate to equal
`chartAt x₀` on the whole formula domain.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.densitySqInChart_eq_chartAt_of_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hx₀ : x₀ ∈ F.domain)
    (hCoord :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        F x₀) :
    g.toConformalMetric.densitySqInChart F.chart F.chart_mem_atlas (F.coordinate x₀) =
      g.toConformalMetric.densitySqInChart (chartAt ℂ x₀)
        (chart_mem_atlas ℂ x₀) ((chartAt ℂ x₀) x₀) := by
  let z₀ : ℂ := (chartAt ℂ x₀) x₀
  have htarget : z₀ ∈ (chartAt ℂ x₀).target := by
    simp [z₀]
  have hsymm : (chartAt ℂ x₀).symm z₀ = x₀ := by
    simp [z₀]
  have hstored_source : (chartAt ℂ x₀).symm z₀ ∈ F.chart.source := by
    simpa [hsymm] using F.domain_subset_chart_source hx₀
  have hpoint :
      F.chart ((chartAt ℂ x₀).symm z₀) = F.coordinate x₀ := by
    rw [hsymm]
    exact (F.coordinate_eq_chart hx₀).symm
  have hdomain :
      ∀ᶠ z in nhds z₀, (chartAt ℂ x₀).symm z ∈ F.domain :=
    ((chartAt ℂ x₀).tendsto_symm (mem_chart_source ℂ x₀))
      (F.isOpen_domain.mem_nhds hx₀)
  have htransition_eventual :
      Filter.EventuallyEq (nhds z₀)
        (fun z : ℂ ↦ F.chart ((chartAt ℂ x₀).symm z))
        (fun z : ℂ ↦ z) := by
    filter_upwards [hdomain, hCoord.2] with z hzdomain hzcoord
    exact (F.coordinate_eq_chart hzdomain).symm.trans hzcoord
  have hderiv :
      deriv (fun z : ℂ ↦ F.chart ((chartAt ℂ x₀).symm z)) z₀ = 1 := by
    simpa using Filter.EventuallyEq.deriv_eq htransition_eventual
  have htransition :=
    g.toConformalMetric.densitySq_transition
      (chartAt ℂ x₀) (chart_mem_atlas ℂ x₀)
      F.chart F.chart_mem_atlas
      htarget hstored_source
  rw [hpoint, hderiv] at htransition
  simpa [z₀] using htransition.symm

/--
If the stored coordinate becomes the identity in the ambient chart, then the
upper-half-plane coordinate expressions are eventually equal.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.ambientExpressionEventuallyEqAt_of_coordinate
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (h :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        F x₀) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientExpressionEventuallyEqAt
      F x₀ :=
  h.2.mono fun _z hz ↦ congrArg (fun w : ℂ ↦ (F.localMap w : ℂ)) hz

/--
Eventual equality of the ambient expression with the stored coordinate map
gives the ambient derivative-norm identification.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeNormSqAt_of_eventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hbase : F.coordinate x₀ = (chartAt ℂ x₀) x₀)
    (h :
      CoordinateUpperHalfPlanePullbackFormulaAmbientExpressionEventuallyEqAt
        F x₀) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt F x₀ := by
  dsimp [CoordinateUpperHalfPlanePullbackFormulaAmbientExpressionEventuallyEqAt] at h
  change
    Complex.normSq
        (deriv
          (fun z : ℂ ↦
            (F.localMap (F.coordinate ((chartAt ℂ x₀).symm z)) : ℂ))
          ((chartAt ℂ x₀) x₀)) =
      Complex.normSq
        (deriv (fun w : ℂ ↦ (F.localMap w : ℂ)) (F.coordinate x₀))
  rw [Filter.EventuallyEq.deriv_eq h, hbase]

/--
Eventual equality of the ambient expression with the stored coordinate map
gives the actual ambient derivative identification.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_eventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hbase : F.coordinate x₀ = (chartAt ℂ x₀) x₀)
    (h :
      CoordinateUpperHalfPlanePullbackFormulaAmbientExpressionEventuallyEqAt
        F x₀) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt F x₀ := by
  dsimp [CoordinateUpperHalfPlanePullbackFormulaAmbientExpressionEventuallyEqAt] at h
  change
    deriv
        (fun z : ℂ ↦
          (F.localMap (F.coordinate ((chartAt ℂ x₀).symm z)) : ℂ))
        ((chartAt ℂ x₀) x₀) =
      deriv (fun w : ℂ ↦ (F.localMap w : ℂ)) (F.coordinate x₀)
  rw [Filter.EventuallyEq.deriv_eq h, hbase]

/--
Actual ambient derivative identification immediately gives the corresponding
derivative-norm identification.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeNormSqAt_of_ambientDerivativeAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (h :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt F x₀) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt F x₀ := by
  dsimp [CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt,
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt] at h ⊢
  rw [h]
  rfl

/--
The ambient-coordinate identity gives the ambient derivative-norm
identification.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeNormSqAt_of_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (h :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        F x₀) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt F x₀ :=
  CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeNormSqAt_of_eventuallyEq
    F h.1
    (CoordinateUpperHalfPlanePullbackFormula.ambientExpressionEventuallyEqAt_of_coordinate F h)

/--
The ambient-coordinate identity gives the actual ambient derivative
identification.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (h :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        F x₀) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt F x₀ :=
  CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_eventuallyEq
    F h.1
    (CoordinateUpperHalfPlanePullbackFormula.ambientExpressionEventuallyEqAt_of_coordinate F h)

/--
If the stored coordinate is the ambient chart on the formula domain, then the
ambient derivative norm of the induced hyperbolic local chart is exactly the
stored coordinate derivative norm.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeNormSqAt_of_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hx₀ : x₀ ∈ F.domain)
    (hEq : Set.EqOn F.coordinate (chartAt ℂ x₀) F.domain) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt F x₀ :=
  CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeNormSqAt_of_coordinateEventuallyEq F
    (CoordinateUpperHalfPlanePullbackFormula.ambientCoordinateEventuallyEqAt_of_eqOn_chartAt
      F hx₀ hEq)

/--
If the stored coordinate is the ambient chart on the formula domain, then the
actual ambient derivative of the induced hyperbolic local chart is the stored
coordinate derivative.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hx₀ : x₀ ∈ F.domain)
    (hEq : Set.EqOn F.coordinate (chartAt ℂ x₀) F.domain) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt F x₀ :=
  CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_coordinateEventuallyEq F
    (CoordinateUpperHalfPlanePullbackFormula.ambientCoordinateEventuallyEqAt_of_eqOn_chartAt
      F hx₀ hEq)

/--
Global derivative-identification target for coordinate pullback formulae.
-/
def CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (F : CoordinateUpperHalfPlanePullbackFormula X g)
    (x₀ : X),
    x₀ ∈ F.domain →
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt F x₀

/--
Global actual derivative-identification target for coordinate pullback
formulae.
-/
def CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (F : CoordinateUpperHalfPlanePullbackFormula X g)
    (x₀ : X),
    x₀ ∈ F.domain →
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt F x₀

/--
Global eventual-coordinate identity target for coordinate pullback formulae.
-/
def CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (F : CoordinateUpperHalfPlanePullbackFormula X g)
    (x₀ : X),
    x₀ ∈ F.domain →
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt F x₀

/--
Global chart-compatibility target for coordinate pullback formulae.
-/
def CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (F : CoordinateUpperHalfPlanePullbackFormula X g)
    (x₀ : X),
    x₀ ∈ F.domain →
      Set.EqOn F.coordinate (chartAt ℂ x₀) F.domain

/--
For an atlas of coordinate pullback formulae, the formula chosen at `x` uses
the ambient chart centered at `x` on its own domain.
-/
def CoordinateUpperHalfPlanePullbackFormulaAtlasCoordinateEqOnChartAtCenters
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (A : CoordinateUpperHalfPlanePullbackFormulaAtlas X g) : Prop :=
  ∀ x : X,
    Set.EqOn (A.formulaAt x).coordinate (chartAt ℂ x) (A.formulaAt x).domain

/--
Aligned Liouville developing constructions inherit chart-compatibility of
coordinates from their metric formula.
-/
theorem LocalLiouvilleDevelopingConstruction.pullbackFormula_coordinate_eqOn_chartAt_of_metricFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (C : LocalLiouvilleDevelopingConstruction X g) {center : X}
    (hChart :
      C.metricFormula.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn C.metricFormula.coordinate (chartAt ℂ center)
          C.metricFormula.domain) :
    Set.EqOn C.pullbackFormula.coordinate (chartAt ℂ center)
      C.pullbackFormula.domain := by
  intro y hy
  rw [C.same_coordinate]
  exact hChart.2 (C.mem_metricFormula_domain hy)

/--
At the center of an aligned construction, metric-formula chart-compatibility
gives the ambient derivative-norm identification for the pullback formula.
-/
theorem LocalLiouvilleDevelopingConstruction.pullbackFormula_ambientDerivativeNormSqAt_of_metricFormula_charted
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (C : LocalLiouvilleDevelopingConstruction X g) {center : X}
    (hcenter : center ∈ C.pullbackFormula.domain)
    (hChart :
      C.metricFormula.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn C.metricFormula.coordinate (chartAt ℂ center)
          C.metricFormula.domain) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt
      C.pullbackFormula center :=
  CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeNormSqAt_of_eqOn_chartAt
    C.pullbackFormula hcenter
    (LocalLiouvilleDevelopingConstruction.pullbackFormula_coordinate_eqOn_chartAt_of_metricFormula
      C hChart)

/--
At the center of an aligned construction, metric-formula chart-compatibility
gives the actual ambient derivative identification for the pullback formula.
-/
theorem LocalLiouvilleDevelopingConstruction.pullbackFormula_ambientDerivativeAt_of_metricFormula_charted
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (C : LocalLiouvilleDevelopingConstruction X g) {center : X}
    (hcenter : center ∈ C.pullbackFormula.domain)
    (hChart :
      C.metricFormula.domain ⊆ (chartAt ℂ center).source ∧
        Set.EqOn C.metricFormula.coordinate (chartAt ℂ center)
          C.metricFormula.domain) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt
      C.pullbackFormula center :=
  CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_eqOn_chartAt
    C.pullbackFormula hcenter
    (LocalLiouvilleDevelopingConstruction.pullbackFormula_coordinate_eqOn_chartAt_of_metricFormula
      C hChart)

/--
A developing-construction atlas whose metric formulas are chart-compatible
has centerwise chart-compatible pullback formulas.
-/
def LocalLiouvilleDevelopingConstructionAtlas.coordinatePullbackAtlasCoordinateEqOnChartAtCenters_of_metricFormulaCharted
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (A : LocalLiouvilleDevelopingConstructionAtlas X g)
    (hChart :
      LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain
        A.toLocalLiouvilleMetricFormulaAtlas) :
    CoordinateUpperHalfPlanePullbackFormulaAtlasCoordinateEqOnChartAtCenters
      A.toCoordinateUpperHalfPlanePullbackFormulaAtlas := by
  intro x
  exact
    LocalLiouvilleDevelopingConstruction.pullbackFormula_coordinate_eqOn_chartAt_of_metricFormula
      (A.constructionAt x) (hChart x)

/--
Chart-compatibility proves the eventual-coordinate identity theorem.
-/
def coordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqTheorem_of_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqTheorem X := by
  intro g F x₀ hx₀
  exact CoordinateUpperHalfPlanePullbackFormula.ambientCoordinateEventuallyEqAt_of_eqOn_chartAt
    F hx₀ (hChart g F x₀ hx₀)

/--
The eventual-coordinate identity proves the ambient derivative-norm theorem.
-/
def coordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqTheorem_of_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hCoord :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqTheorem
        X) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqTheorem X := by
  intro g F x₀ hx₀
  exact CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeNormSqAt_of_coordinateEventuallyEq F
    (hCoord g F x₀ hx₀)

/--
The eventual-coordinate identity proves the actual ambient derivative theorem.
-/
def coordinateUpperHalfPlanePullbackFormulaAmbientDerivativeTheorem_of_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hCoord :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqTheorem
        X) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeTheorem X := by
  intro g F x₀ hx₀
  exact CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_coordinateEventuallyEq F
    (hCoord g F x₀ hx₀)

/--
Chart-compatibility proves the ambient derivative-norm theorem.
-/
def coordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqTheorem_of_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqTheorem X :=
  coordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqTheorem_of_coordinateEventuallyEq
    (coordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqTheorem_of_eqOn_chartAt
      hChart)

/--
Chart-compatibility proves the actual ambient derivative theorem.
-/
def coordinateUpperHalfPlanePullbackFormulaAmbientDerivativeTheorem_of_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X) :
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeTheorem X :=
  coordinateUpperHalfPlanePullbackFormulaAmbientDerivativeTheorem_of_coordinateEventuallyEq
    (coordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqTheorem_of_eqOn_chartAt
      hChart)

/--
Once the ambient derivative norm is identified with the stored coordinate
derivative norm, the hyperbolic local chart induced by a coordinate pullback
formula satisfies the pointwise pullback squared-density formula.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChart_pullbackSquaredDensityFormulaAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hx₀ : x₀ ∈ F.domain)
    (hEq : Set.EqOn F.coordinate (chartAt ℂ x₀) F.domain)
    (hDeriv :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt F x₀) :
    HyperbolicLocalChartPullbackSquaredDensityFormulaAt
      F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ := by
  dsimp [HyperbolicLocalChartPullbackSquaredDensityFormulaAt,
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt] at hDeriv ⊢
  rw [hDeriv]
  exact (CoordinateUpperHalfPlanePullbackFormula.pullbackSquaredDensityFormulaAt F hx₀).trans
    (CoordinateUpperHalfPlanePullbackFormula.densitySqInChart_eq_chartAt_of_eqOn_chartAt
      F hx₀ hEq)

/--
The local ambient-coordinate identity extracts the hyperbolic local-chart
pullback formula from a coordinate pullback formula.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChart_pullbackSquaredDensityFormulaAt_of_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hx₀ : x₀ ∈ F.domain)
    (hCoord :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        F x₀) :
    HyperbolicLocalChartPullbackSquaredDensityFormulaAt
      F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ := by
  have hDeriv :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt F x₀ :=
    CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeNormSqAt_of_coordinateEventuallyEq
      F hCoord
  dsimp [HyperbolicLocalChartPullbackSquaredDensityFormulaAt,
    CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt] at hDeriv ⊢
  rw [hDeriv]
  exact (CoordinateUpperHalfPlanePullbackFormula.pullbackSquaredDensityFormulaAt F hx₀).trans
    (CoordinateUpperHalfPlanePullbackFormula.densitySqInChart_eq_chartAt_of_coordinateEventuallyEq
      F hx₀ hCoord)

/--
The same derivative norm identification also gives nonvanishing of the
ambient local-chart derivative.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChart_coordinateDerivative_ne_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hx₀ : x₀ ∈ F.domain)
    (hDeriv :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt F x₀) :
    hyperbolicLocalChartCoordinateDerivativeAt
      F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ ≠ 0 := by
  let d :=
    hyperbolicLocalChartCoordinateDerivativeAt
      F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀
  have hpos : 0 < Complex.normSq d := by
    dsimp [d]
    rw [hDeriv]
    exact F.derivativeNormSq_pos hx₀
  intro hd
  have hzero : Complex.normSq d = 0 := by
    simp [d, hd]
  exact (ne_of_gt hpos) hzero

/--
Coordinate pullback formulae give the hyperbolic local-chart pullback
squared-density formula once the ambient derivative identification is supplied.
-/
def CoordinateUpperHalfPlanePullbackFormulaHyperbolicLocalChartPullbackSquaredDensityTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (F : CoordinateUpperHalfPlanePullbackFormula X g)
    (x₀ : X),
    x₀ ∈ F.domain →
      HyperbolicLocalChartPullbackSquaredDensityFormulaAt
        F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀

/--
The converted hyperbolic local chart of any coordinate pullback formula
satisfies the ambient `chartAt` Poincare pullback formula on a Riemann
surface.

This uses the genuine chart-transition argument in
`hyperbolicLocalChart_pullbackSquaredDensityFormulaAt`; no assumption that the
stored coordinate is literally `chartAt x₀` is needed.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChart_pullbackSquaredDensityFormulaAt_from_chartTransition
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hx₀ : x₀ ∈ F.domain) :
    HyperbolicLocalChartPullbackSquaredDensityFormulaAt
      F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ :=
  _root_.JJMath.HyperbolicMetric.hyperbolicLocalChart_pullbackSquaredDensityFormulaAt
    F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart hx₀

/--
Coordinate pullback formulae give the hyperbolic local-chart pullback
squared-density formula directly on a Riemann surface.
-/
theorem coordinateUpperHalfPlanePullbackFormulaHyperbolicLocalChartPullbackSquaredDensityTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X] :
    CoordinateUpperHalfPlanePullbackFormulaHyperbolicLocalChartPullbackSquaredDensityTheorem
      X := by
  intro g F x₀ hx₀
  exact
    _root_.JJMath.HyperbolicMetric.CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChart_pullbackSquaredDensityFormulaAt_from_chartTransition
      F hx₀

/--
The derivative-identification theorem extracts the hyperbolic local-chart
pullback squared-density formula from coordinate pullback formulae.
-/
def coordinateUpperHalfPlanePullbackFormulaHyperbolicLocalChartPullbackSquaredDensityTheorem_of_ambientDerivativeNormSq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqTheorem X)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X) :
    CoordinateUpperHalfPlanePullbackFormulaHyperbolicLocalChartPullbackSquaredDensityTheorem
      X := by
  intro g F x₀ hx₀
  exact CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChart_pullbackSquaredDensityFormulaAt F hx₀
    (hChart g F x₀ hx₀)
    (hDeriv g F x₀ hx₀)

/--
Chart-compatibility extracts the hyperbolic local-chart pullback
squared-density formula from coordinate pullback formulae.
-/
def coordinateUpperHalfPlanePullbackFormulaHyperbolicLocalChartPullbackSquaredDensityTheorem_of_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X) :
    CoordinateUpperHalfPlanePullbackFormulaHyperbolicLocalChartPullbackSquaredDensityTheorem
      X :=
  coordinateUpperHalfPlanePullbackFormulaHyperbolicLocalChartPullbackSquaredDensityTheorem_of_ambientDerivativeNormSq
    (coordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqTheorem_of_eqOn_chartAt
      hChart)
    hChart

/--
Coordinate derivative data extracted from a holomorphic local isometry.

This is the precise analytic boundary behind the statement that a local
hyperbolic coordinate determines a normalized oriented tangent frame.  The
pullback formula is stated in squared-density form, matching the rest of the
development.
-/
structure HyperbolicLocalChartPointedCoordinateDerivativeData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U : HyperbolicLocalChart X g) (x₀ : X) where
  /-- The surface point lies in the local chart domain. -/
  mem_domain : x₀ ∈ U.domain
  /-- The local coordinate derivative is nonzero. -/
  coordinate_derivative_ne_zero :
    hyperbolicLocalChartCoordinateDerivativeAt U x₀ ≠ 0
  /-- Pullback of the Poincare squared density in the ambient coordinate. -/
  coordinate_pullback_normSq :
    HyperbolicLocalChartPullbackSquaredDensityFormulaAt U x₀

/--
A coordinate pullback formula supplies the pointed derivative data for its
induced hyperbolic local chart once the ambient derivative norm is identified.
-/
def CoordinateUpperHalfPlanePullbackFormula.toHyperbolicLocalChartPointedCoordinateDerivativeData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hx₀ : x₀ ∈ F.domain)
    (hEq : Set.EqOn F.coordinate (chartAt ℂ x₀) F.domain)
    (hDeriv :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt F x₀) :
    HyperbolicLocalChartPointedCoordinateDerivativeData
      F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ where
  mem_domain := hx₀
  coordinate_derivative_ne_zero :=
    CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChart_coordinateDerivative_ne_zero
      F hx₀ hDeriv
  coordinate_pullback_normSq :=
    CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChart_pullbackSquaredDensityFormulaAt
      F hx₀ hEq hDeriv

/--
A coordinate pullback formula supplies pointed derivative data from the local
ambient-coordinate identity, without requiring domainwise equality with
`chartAt x₀`.
-/
def CoordinateUpperHalfPlanePullbackFormula.toHyperbolicLocalChartPointedCoordinateDerivativeData_of_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hx₀ : x₀ ∈ F.domain)
    (hCoord :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        F x₀) :
    HyperbolicLocalChartPointedCoordinateDerivativeData
      F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ where
  mem_domain := hx₀
  coordinate_derivative_ne_zero :=
    CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChart_coordinateDerivative_ne_zero
      F hx₀
      (CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeNormSqAt_of_coordinateEventuallyEq
        F hCoord)
  coordinate_pullback_normSq :=
    CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChart_pullbackSquaredDensityFormulaAt_of_coordinateEventuallyEq
      F hx₀ hCoord

/--
The pointed coordinate-derivative data theorem for hyperbolic local charts
coming from coordinate pullback formulae.
-/
def CoordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (F : CoordinateUpperHalfPlanePullbackFormula X g)
    (x₀ : X),
    x₀ ∈ F.domain →
      Nonempty
        (HyperbolicLocalChartPointedCoordinateDerivativeData
          F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀)

/--
A coordinate pullback formula supplies pointed derivative data for its induced
hyperbolic local chart using the actual ambient chart-transition pullback
formula.
-/
def CoordinateUpperHalfPlanePullbackFormula.toHyperbolicLocalChartPointedCoordinateDerivativeData_from_chartTransition
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    {g : HyperbolicMetric X}
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x₀ : X}
    (hx₀ : x₀ ∈ F.domain) :
    HyperbolicLocalChartPointedCoordinateDerivativeData
      F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ where
  mem_domain := hx₀
  coordinate_derivative_ne_zero := by
    exact
      (_root_.JJMath.HyperbolicMetric.CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChart_pullbackSquaredDensityFormulaAt_from_chartTransition
        F hx₀).coordinateDerivative_ne_zero hx₀
  coordinate_pullback_normSq :=
    _root_.JJMath.HyperbolicMetric.CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChart_pullbackSquaredDensityFormulaAt_from_chartTransition
      F hx₀

/--
Pointed coordinate-derivative data for coordinate pullback formulae is
available directly on a Riemann surface, with the chart-transition derivative
handled by the already-proved hyperbolic local-chart pullback formula.
-/
theorem coordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X] :
    CoordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem
      X := by
  intro g F x₀ hx₀
  exact
    ⟨_root_.JJMath.HyperbolicMetric.CoordinateUpperHalfPlanePullbackFormula.toHyperbolicLocalChartPointedCoordinateDerivativeData_from_chartTransition
      F hx₀⟩

/--
The ambient derivative-norm identification extracts pointed coordinate data
from every coordinate pullback formula.
-/
def coordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem_of_ambientDerivativeNormSq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqTheorem X)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X) :
    CoordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem
      X := by
  intro g F x₀ hx₀
  exact
    ⟨CoordinateUpperHalfPlanePullbackFormula.toHyperbolicLocalChartPointedCoordinateDerivativeData
      F hx₀ (hChart g F x₀ hx₀)
      (hDeriv g F x₀ hx₀)⟩

/--
Chart-compatibility extracts pointed coordinate data from every coordinate
pullback formula.
-/
def coordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem_of_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X) :
    CoordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem
      X :=
  coordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem_of_ambientDerivativeNormSq
    (coordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqTheorem_of_eqOn_chartAt
      hChart)
    hChart

/--
The normalized coordinate derivative is nonzero.
-/
theorem HyperbolicLocalChartPointedCoordinateDerivativeData.normalized_ne_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U : HyperbolicLocalChart X g} {x₀ : X}
    (D : HyperbolicLocalChartPointedCoordinateDerivativeData U x₀) :
    hyperbolicLocalChartNormalizedCoordinateDerivativeAt U x₀ ≠ 0 := by
  have hρ_pos : 0 < hyperbolicLocalChartCoordinateDensitySqAt U x₀ :=
    hyperbolicLocalChartCoordinateDensitySqAt_pos U D.mem_domain
  have hsqrt_ne :
      (Real.sqrt (hyperbolicLocalChartCoordinateDensitySqAt U x₀) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.2 hρ_pos)
  rw [hyperbolicLocalChartNormalizedCoordinateDerivativeAt]
  exact div_ne_zero D.coordinate_derivative_ne_zero hsqrt_ne

/--
The normalized coordinate derivative has squared hyperbolic norm `1`.
-/
theorem HyperbolicLocalChartPointedCoordinateDerivativeData.normalized_hyperbolicNormSq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U : HyperbolicLocalChart X g} {x₀ : X}
    (D : HyperbolicLocalChartPointedCoordinateDerivativeData U x₀) :
    Complex.normSq (hyperbolicLocalChartNormalizedCoordinateDerivativeAt U x₀) /
        ((U.toUpperHalfPlane x₀ : ℂ).im ^ 2) = 1 := by
  let ρ : ℝ := hyperbolicLocalChartCoordinateDensitySqAt U x₀
  let d2 : ℝ := Complex.normSq (hyperbolicLocalChartCoordinateDerivativeAt U x₀)
  let i2 : ℝ := (U.toUpperHalfPlane x₀ : ℂ).im ^ 2
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact hyperbolicLocalChartCoordinateDensitySqAt_pos U D.mem_domain
  have hρ_ne : ρ ≠ 0 := ne_of_gt hρ_pos
  have hi2_pos : 0 < i2 := by
    dsimp [i2]
    exact sq_pos_of_ne_zero (U.toUpperHalfPlane x₀).im_ne_zero
  have hi2_ne : i2 ≠ 0 := ne_of_gt hi2_pos
  have hsqrt_norm :
      Complex.normSq (Real.sqrt ρ : ℂ) = ρ := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (le_of_lt hρ_pos)]
  have hpull : d2 / i2 = ρ := by
    simpa [d2, i2, ρ] using D.coordinate_pullback_normSq
  have hunit : (d2 / ρ) / i2 = 1 := by
    have h := hpull
    field_simp [hρ_ne, hi2_ne] at h ⊢
    nlinarith
  rw [hyperbolicLocalChartNormalizedCoordinateDerivativeAt,
    Complex.normSq_div, hsqrt_norm]
  simpa [d2, i2, ρ] using hunit

/--
Coordinate derivative data determines the normalized pointed frame used in the
pointed real-transition theorem.
-/
def HyperbolicLocalChartPointedCoordinateDerivativeData.toPointedFrame
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U : HyperbolicLocalChart X g} {x₀ : X}
    (D : HyperbolicLocalChartPointedCoordinateDerivativeData U x₀) :
    HyperbolicLocalChartPointedFrame U x₀ where
  frame :=
    { base := U.toUpperHalfPlane x₀
      tangent := hyperbolicLocalChartNormalizedCoordinateDerivativeAt U x₀
      tangent_ne_zero := D.normalized_ne_zero }
  mem_domain := D.mem_domain
  base_eq := rfl
  unit_hyperbolicNormSq := by
    simpa [UpperHalfPlaneTangentFrame.hyperbolicNormSq] using
      D.normalized_hyperbolicNormSq
  represents_oriented_derivative := rfl

/--
Analytic target: every holomorphic local isometry supplies the coordinate
derivative data needed to build its normalized oriented frame.
-/
def HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U : HyperbolicLocalChart X g) (x₀ : X),
    x₀ ∈ U.domain →
      Nonempty (HyperbolicLocalChartPointedCoordinateDerivativeData U x₀)

/--
Nonzero coordinate derivative plus the concrete pullback squared-density
formula supply the pointed coordinate-derivative data.
-/
def hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X) :
    HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X := by
  intro g U x₀ hx₀
  exact
    ⟨{ mem_domain := hx₀
       coordinate_derivative_ne_zero :=
        hDeriv g U x₀ hx₀
       coordinate_pullback_normSq :=
        hPull g U x₀ hx₀ }⟩

/--
The concrete pullback squared-density formula alone supplies the pointed
coordinate-derivative data; nonvanishing follows from positivity of the source
conformal density.
-/
def hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula_proved
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X) :
    HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X :=
  hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula
    (hyperbolicLocalChartCoordinateDerivativeNonzeroTheorem_of_pullbackSquaredDensityFormula
      hPull)
    hPull

/--
Analytic differential-geometric target behind pointed matching.

Every hyperbolic local coordinate should supply a normalized oriented tangent
frame at each point of its domain.
-/
def HyperbolicLocalChartsHavePointedFramesTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U : HyperbolicLocalChart X g) (x₀ : X),
    x₀ ∈ U.domain → Nonempty (HyperbolicLocalChartPointedFrame U x₀)

/--
The coordinate derivative data theorem proves the pointed-frame theorem.
-/
def hyperbolicLocalChartsHavePointedFramesTheorem_of_coordinateDerivativeData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X) :
    HyperbolicLocalChartsHavePointedFramesTheorem X := by
  intro g U x₀ hx₀
  rcases h g U x₀ hx₀ with ⟨D⟩
  exact ⟨D.toPointedFrame⟩

/--
Pointed real-Mobius first-order matching for two hyperbolic local charts.

This is now a genuine oriented-frame condition: the representative must carry
the frame induced by the first chart to the frame induced by the second chart.
-/
def HyperbolicLocalChartPointedFirstOrderMatch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) (A : RealMobiusRepresentative) (x₀ : X) :
    Prop :=
  ∃ (FU : HyperbolicLocalChartPointedFrame U x₀)
    (FV : HyperbolicLocalChartPointedFrame V x₀),
      RealMobiusRepresentativeMapsTangentFrame A FU.frame FV.frame

/--
Concrete first-order matching for two hyperbolic local charts in the ambient
complex coordinate at a surface point.

This is the coordinate-derivative version of pointed frame matching: the
derivative of the second chart is the derivative of the real Mobius
postcomposition applied to the derivative of the first chart.
-/
def HyperbolicLocalChartConcreteFirstOrderMatch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) (A : RealMobiusRepresentative) (x₀ : X) :
    Prop :=
  hyperbolicLocalChartCoordinateDerivativeAt V x₀ =
    realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x₀) *
      hyperbolicLocalChartCoordinateDerivativeAt U x₀

/--
Canonical pointed first-order matching for two hyperbolic local charts.

Unlike `HyperbolicLocalChartPointedFirstOrderMatch`, this predicate insists
that the two pointed frames are the canonical normalized coordinate-derivative
frames supplied by the pullback metric formula.
-/
def HyperbolicLocalChartCanonicalPointedFirstOrderMatch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) (A : RealMobiusRepresentative) (x₀ : X) :
    Prop :=
  ∃ (DU : HyperbolicLocalChartPointedCoordinateDerivativeData U x₀)
    (DV : HyperbolicLocalChartPointedCoordinateDerivativeData V x₀),
      RealMobiusRepresentativeMapsTangentFrame A
        DU.toPointedFrame.frame DV.toPointedFrame.frame

/-- Even the abstract first-order frame match includes the value equation. -/
theorem HyperbolicLocalChartPointedFirstOrderMatch.value_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative} {x₀ : X}
    (h : HyperbolicLocalChartPointedFirstOrderMatch U V A x₀) :
    V.toUpperHalfPlane x₀ =
      realMobiusRepresentativeAction A (U.toUpperHalfPlane x₀) := by
  rcases h with ⟨FU, FV, hmap⟩
  rw [← FV.base_eq, ← FU.base_eq]
  exact hmap.1

/-- The abstract first-order frame match includes membership in the left chart domain. -/
theorem HyperbolicLocalChartPointedFirstOrderMatch.mem_left
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative} {x₀ : X}
    (h : HyperbolicLocalChartPointedFirstOrderMatch U V A x₀) :
    x₀ ∈ U.domain := by
  rcases h with ⟨FU, _FV, _hmap⟩
  exact FU.mem_domain

/-- The abstract first-order frame match includes membership in the right chart domain. -/
theorem HyperbolicLocalChartPointedFirstOrderMatch.mem_right
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative} {x₀ : X}
    (h : HyperbolicLocalChartPointedFirstOrderMatch U V A x₀) :
    x₀ ∈ V.domain := by
  rcases h with ⟨_FU, FV, _hmap⟩
  exact FV.mem_domain

/--
The abstract pointed-frame match already forces the concrete coordinate
first-order chain-rule identity.

The point is that `HyperbolicLocalChartPointedFrame` is no longer an arbitrary
frame witness: its tangent is definitionally tied to the normalized ambient
coordinate derivative of the chart.  Multiplying by the common positive source
density removes the normalization.
-/
theorem HyperbolicLocalChartPointedFirstOrderMatch.concreteFirstOrderMatch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative} {x₀ : X}
    (h : HyperbolicLocalChartPointedFirstOrderMatch U V A x₀) :
    HyperbolicLocalChartConcreteFirstOrderMatch U V A x₀ := by
  rcases h with ⟨FU, FV, hmap⟩
  let s : ℂ := (Real.sqrt (hyperbolicLocalChartCoordinateDensitySqAt U x₀) : ℂ)
  have hs : s ≠ 0 := by
    have hρ_pos : 0 < hyperbolicLocalChartCoordinateDensitySqAt U x₀ :=
      hyperbolicLocalChartCoordinateDensitySqAt_pos U FU.mem_domain
    dsimp [s]
    exact_mod_cast (Real.sqrt_ne_zero'.2 hρ_pos)
  have hnorm :
      hyperbolicLocalChartNormalizedCoordinateDerivativeAt V x₀ =
        realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x₀) *
          hyperbolicLocalChartNormalizedCoordinateDerivativeAt U x₀ := by
    have htangent := hmap.2
    rw [FV.represents_oriented_derivative,
      FU.represents_oriented_derivative] at htangent
    simpa [FU.base_eq] using htangent
  have hmul := congrArg (fun t : ℂ ↦ t * s) hnorm
  dsimp [HyperbolicLocalChartConcreteFirstOrderMatch,
    hyperbolicLocalChartNormalizedCoordinateDerivativeAt,
    hyperbolicLocalChartCoordinateDensitySqAt, s] at hmul ⊢
  have hs' :
      (Real.sqrt
        (g.toConformalMetric.densitySqInChart (chartAt ℂ x₀)
          (chart_mem_atlas ℂ x₀) ((chartAt ℂ x₀) x₀)) : ℂ) ≠ 0 := by
    simpa [s, hyperbolicLocalChartCoordinateDensitySqAt] using hs
  rw [div_mul_cancel₀ _ hs', mul_assoc, div_mul_cancel₀ _ hs'] at hmul
  exact hmul

/--
Faithfulness target for the older abstract frame predicate.

The current abstract predicate existentially quantifies pointed frames.  This
target says that such an abstract match is always represented by the canonical
normalized coordinate-derivative frames.
-/
def HyperbolicLocalChartAbstractFirstOrderMatchCanonicalityTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g)
    (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedFirstOrderMatch U V A x₀ →
        HyperbolicLocalChartCanonicalPointedFirstOrderMatch U V A x₀

/--
Coordinate-derivative data plus equality of normalized derivative vectors gives
the abstract first-order frame match.
-/
theorem HyperbolicLocalChartPointedFirstOrderMatch_of_normalizedCoordinateDerivative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative} {x₀ : X}
    (DU : HyperbolicLocalChartPointedCoordinateDerivativeData U x₀)
    (DV : HyperbolicLocalChartPointedCoordinateDerivativeData V x₀)
    (hvalue :
      V.toUpperHalfPlane x₀ =
        realMobiusRepresentativeAction A (U.toUpperHalfPlane x₀))
    (hderiv :
      hyperbolicLocalChartNormalizedCoordinateDerivativeAt V x₀ =
        realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x₀) *
          hyperbolicLocalChartNormalizedCoordinateDerivativeAt U x₀) :
    HyperbolicLocalChartPointedFirstOrderMatch U V A x₀ := by
  refine ⟨DU.toPointedFrame, DV.toPointedFrame, ?_⟩
  constructor
  · simpa [HyperbolicLocalChartPointedCoordinateDerivativeData.toPointedFrame]
      using hvalue
  · simpa [HyperbolicLocalChartPointedCoordinateDerivativeData.toPointedFrame]
      using hderiv

/--
An unnormalized derivative equality gives equality of normalized derivative
vectors, since both local charts are normalized by the same source metric
density at the surface point.
-/
theorem hyperbolicLocalChart_normalizedCoordinateDerivative_eq_of_coordinateDerivative_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative} {x₀ : X}
    (hderiv :
      hyperbolicLocalChartCoordinateDerivativeAt V x₀ =
        realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x₀) *
          hyperbolicLocalChartCoordinateDerivativeAt U x₀) :
    hyperbolicLocalChartNormalizedCoordinateDerivativeAt V x₀ =
      realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x₀) *
        hyperbolicLocalChartNormalizedCoordinateDerivativeAt U x₀ := by
  rw [hyperbolicLocalChartNormalizedCoordinateDerivativeAt,
    hyperbolicLocalChartNormalizedCoordinateDerivativeAt, hderiv]
  simp [hyperbolicLocalChartCoordinateDensitySqAt]
  ring

/--
Coordinate-derivative data plus the ordinary chain-rule derivative equality
gives the abstract first-order frame match.
-/
theorem HyperbolicLocalChartPointedFirstOrderMatch_of_coordinateDerivative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative} {x₀ : X}
    (DU : HyperbolicLocalChartPointedCoordinateDerivativeData U x₀)
    (DV : HyperbolicLocalChartPointedCoordinateDerivativeData V x₀)
    (hvalue :
      V.toUpperHalfPlane x₀ =
        realMobiusRepresentativeAction A (U.toUpperHalfPlane x₀))
    (hderiv :
      hyperbolicLocalChartCoordinateDerivativeAt V x₀ =
        realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x₀) *
          hyperbolicLocalChartCoordinateDerivativeAt U x₀) :
    HyperbolicLocalChartPointedFirstOrderMatch U V A x₀ :=
  HyperbolicLocalChartPointedFirstOrderMatch_of_normalizedCoordinateDerivative
    DU DV hvalue
    (hyperbolicLocalChart_normalizedCoordinateDerivative_eq_of_coordinateDerivative_eq
      hderiv)

/--
Concrete first-order matching, together with the pointed derivative data,
gives the abstract oriented-frame match.
-/
theorem HyperbolicLocalChartPointedFirstOrderMatch_of_concreteFirstOrderMatch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative} {x₀ : X}
    (DU : HyperbolicLocalChartPointedCoordinateDerivativeData U x₀)
    (DV : HyperbolicLocalChartPointedCoordinateDerivativeData V x₀)
    (hvalue :
      V.toUpperHalfPlane x₀ =
        realMobiusRepresentativeAction A (U.toUpperHalfPlane x₀))
    (hfirst : HyperbolicLocalChartConcreteFirstOrderMatch U V A x₀) :
    HyperbolicLocalChartPointedFirstOrderMatch U V A x₀ :=
  HyperbolicLocalChartPointedFirstOrderMatch_of_coordinateDerivative
    DU DV hvalue hfirst

/-- Canonical first-order matching forgets to the abstract frame predicate. -/
theorem HyperbolicLocalChartPointedFirstOrderMatch_of_canonical
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative} {x₀ : X}
    (h : HyperbolicLocalChartCanonicalPointedFirstOrderMatch U V A x₀) :
    HyperbolicLocalChartPointedFirstOrderMatch U V A x₀ := by
  rcases h with ⟨DU, DV, hmap⟩
  exact ⟨DU.toPointedFrame, DV.toPointedFrame, hmap⟩

/-- Canonical first-order matching includes the value equation. -/
theorem HyperbolicLocalChartCanonicalPointedFirstOrderMatch.value_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative} {x₀ : X}
    (h : HyperbolicLocalChartCanonicalPointedFirstOrderMatch U V A x₀) :
    V.toUpperHalfPlane x₀ =
      realMobiusRepresentativeAction A (U.toUpperHalfPlane x₀) := by
  rcases h with ⟨DU, DV, hmap⟩
  simpa [HyperbolicLocalChartPointedCoordinateDerivativeData.toPointedFrame]
    using hmap.1

/--
Canonical first-order matching is faithful to the concrete coordinate
derivative chain-rule identity.
-/
theorem HyperbolicLocalChartCanonicalPointedFirstOrderMatch.concreteFirstOrderMatch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative} {x₀ : X}
    (h : HyperbolicLocalChartCanonicalPointedFirstOrderMatch U V A x₀) :
    HyperbolicLocalChartConcreteFirstOrderMatch U V A x₀ := by
  rcases h with ⟨DU, DV, hmap⟩
  let s : ℂ := (Real.sqrt (hyperbolicLocalChartCoordinateDensitySqAt U x₀) : ℂ)
  have hs : s ≠ 0 := by
    have hρ_pos : 0 < hyperbolicLocalChartCoordinateDensitySqAt U x₀ :=
      hyperbolicLocalChartCoordinateDensitySqAt_pos U DU.mem_domain
    dsimp [s]
    exact_mod_cast (Real.sqrt_ne_zero'.2 hρ_pos)
  have hnorm :
      hyperbolicLocalChartNormalizedCoordinateDerivativeAt V x₀ =
        realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x₀) *
          hyperbolicLocalChartNormalizedCoordinateDerivativeAt U x₀ := by
    simpa [HyperbolicLocalChartPointedCoordinateDerivativeData.toPointedFrame]
      using hmap.2
  have hmul := congrArg (fun t : ℂ ↦ t * s) hnorm
  dsimp [HyperbolicLocalChartConcreteFirstOrderMatch,
    hyperbolicLocalChartNormalizedCoordinateDerivativeAt,
    hyperbolicLocalChartCoordinateDensitySqAt, s] at hmul ⊢
  have hs' :
      (Real.sqrt
        (g.toConformalMetric.densitySqInChart (chartAt ℂ x₀)
          (chart_mem_atlas ℂ x₀) ((chartAt ℂ x₀) x₀)) : ℂ) ≠ 0 := by
    simpa [s, hyperbolicLocalChartCoordinateDensitySqAt] using hs
  rw [div_mul_cancel₀ _ hs', mul_assoc, div_mul_cancel₀ _ hs'] at hmul
  exact hmul

/--
If abstract first-order matches are canonical, then an abstract match gives
the concrete ambient coordinate derivative chain-rule identity.
-/
theorem HyperbolicLocalChartConcreteFirstOrderMatch_of_pointedFirstOrderMatch_of_canonicality
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hCanon :
      HyperbolicLocalChartAbstractFirstOrderMatchCanonicalityTheorem X)
    {g : HyperbolicMetric X} {U V : HyperbolicLocalChart X g}
    {A : RealMobiusRepresentative} {x₀ : X}
    (h : HyperbolicLocalChartPointedFirstOrderMatch U V A x₀) :
    HyperbolicLocalChartConcreteFirstOrderMatch U V A x₀ :=
  (hCanon g U V A x₀ h).concreteFirstOrderMatch

/--
Concrete first-order matching with pointed derivative data is the same as
canonical pointed first-order matching.
-/
theorem HyperbolicLocalChartCanonicalPointedFirstOrderMatch_of_concreteFirstOrderMatch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative} {x₀ : X}
    (DU : HyperbolicLocalChartPointedCoordinateDerivativeData U x₀)
    (DV : HyperbolicLocalChartPointedCoordinateDerivativeData V x₀)
    (hvalue :
      V.toUpperHalfPlane x₀ =
        realMobiusRepresentativeAction A (U.toUpperHalfPlane x₀))
    (hfirst : HyperbolicLocalChartConcreteFirstOrderMatch U V A x₀) :
    HyperbolicLocalChartCanonicalPointedFirstOrderMatch U V A x₀ := by
  refine ⟨DU, DV, ?_⟩
  constructor
  · simpa [HyperbolicLocalChartPointedCoordinateDerivativeData.toPointedFrame]
      using hvalue
  · have hnorm :=
      hyperbolicLocalChart_normalizedCoordinateDerivative_eq_of_coordinateDerivative_eq
        hfirst
    simpa [HyperbolicLocalChartPointedCoordinateDerivativeData.toPointedFrame]
      using hnorm

/--
For two coordinate pullback formulae, actual ambient derivative identification
turns the ordinary coordinate derivative chain rule into the abstract
first-order frame match for the induced hyperbolic local charts.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.pointedFirstOrderMatch_of_coordinateDerivative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F G : CoordinateUpperHalfPlanePullbackFormula X g)
    {A : RealMobiusRepresentative} {x₀ : X}
    (hxF : x₀ ∈ F.domain) (hxG : x₀ ∈ G.domain)
    (hEqF : Set.EqOn F.coordinate (chartAt ℂ x₀) F.domain)
    (hEqG : Set.EqOn G.coordinate (chartAt ℂ x₀) G.domain)
    (hF :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt F x₀)
    (hG :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt G x₀)
    (hvalue :
      G.localMap (G.coordinate x₀) =
        realMobiusRepresentativeAction A (F.localMap (F.coordinate x₀)))
    (hderiv :
      deriv (fun z : ℂ ↦ (G.localMap z : ℂ)) (G.coordinate x₀) =
        realMobiusRepresentativeDerivativeAt A (F.localMap (F.coordinate x₀)) *
          deriv (fun z : ℂ ↦ (F.localMap z : ℂ)) (F.coordinate x₀)) :
    HyperbolicLocalChartPointedFirstOrderMatch
      F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart
      G.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart A x₀ := by
  let U := F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart
  let V := G.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart
  have hFnorm :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt F x₀ :=
    CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeNormSqAt_of_ambientDerivativeAt
      F hF
  have hGnorm :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqAt G x₀ :=
    CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeNormSqAt_of_ambientDerivativeAt
      G hG
  let DF :
      HyperbolicLocalChartPointedCoordinateDerivativeData
        F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ :=
    CoordinateUpperHalfPlanePullbackFormula.toHyperbolicLocalChartPointedCoordinateDerivativeData
      F hxF hEqF hFnorm
  let DG :
      HyperbolicLocalChartPointedCoordinateDerivativeData
        G.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ :=
    CoordinateUpperHalfPlanePullbackFormula.toHyperbolicLocalChartPointedCoordinateDerivativeData
      G hxG hEqG hGnorm
  refine
    HyperbolicLocalChartPointedFirstOrderMatch_of_coordinateDerivative
      DF DG ?_ ?_
  · simpa [U, V, CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlane] using hvalue
  · dsimp [CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt] at hF hG
    rw [hG, hF]
    simpa [U, V, CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlane] using hderiv

/--
Chart-compatible coordinate pullback formulae satisfy the pairwise first-order
frame bridge as soon as their stored coordinate values and derivatives satisfy
the real-Mobius value and chain-rule equations.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.pointedFirstOrderMatch_of_coordinateDerivative_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F G : CoordinateUpperHalfPlanePullbackFormula X g)
    {A : RealMobiusRepresentative} {x₀ : X}
    (hxF : x₀ ∈ F.domain) (hxG : x₀ ∈ G.domain)
    (hEqF : Set.EqOn F.coordinate (chartAt ℂ x₀) F.domain)
    (hEqG : Set.EqOn G.coordinate (chartAt ℂ x₀) G.domain)
    (hvalue :
      G.localMap (G.coordinate x₀) =
        realMobiusRepresentativeAction A (F.localMap (F.coordinate x₀)))
    (hderiv :
      deriv (fun z : ℂ ↦ (G.localMap z : ℂ)) (G.coordinate x₀) =
        realMobiusRepresentativeDerivativeAt A (F.localMap (F.coordinate x₀)) *
          deriv (fun z : ℂ ↦ (F.localMap z : ℂ)) (F.coordinate x₀)) :
    HyperbolicLocalChartPointedFirstOrderMatch
      F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart
      G.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart A x₀ :=
  CoordinateUpperHalfPlanePullbackFormula.pointedFirstOrderMatch_of_coordinateDerivative
    F G hxF hxG hEqF hEqG
    (CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_eqOn_chartAt
      F hxF hEqF)
    (CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_eqOn_chartAt
      G hxG hEqG)
    hvalue hderiv

/--
Locally chart-compatible coordinate pullback formulae satisfy the pairwise
first-order frame bridge as soon as their stored coordinate values and
derivatives satisfy the real-Mobius value and chain-rule equations.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.pointedFirstOrderMatch_of_coordinateDerivative_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F G : CoordinateUpperHalfPlanePullbackFormula X g)
    {A : RealMobiusRepresentative} {x₀ : X}
    (hxF : x₀ ∈ F.domain) (hxG : x₀ ∈ G.domain)
    (hCoordF :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        F x₀)
    (hCoordG :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        G x₀)
    (hvalue :
      G.localMap (G.coordinate x₀) =
        realMobiusRepresentativeAction A (F.localMap (F.coordinate x₀)))
    (hderiv :
      deriv (fun z : ℂ ↦ (G.localMap z : ℂ)) (G.coordinate x₀) =
        realMobiusRepresentativeDerivativeAt A (F.localMap (F.coordinate x₀)) *
          deriv (fun z : ℂ ↦ (F.localMap z : ℂ)) (F.coordinate x₀)) :
    HyperbolicLocalChartPointedFirstOrderMatch
      F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart
      G.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart A x₀ := by
  let U := F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart
  let V := G.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart
  let DF :
      HyperbolicLocalChartPointedCoordinateDerivativeData
        F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ :=
    CoordinateUpperHalfPlanePullbackFormula.toHyperbolicLocalChartPointedCoordinateDerivativeData_of_coordinateEventuallyEq
      F hxF hCoordF
  let DG :
      HyperbolicLocalChartPointedCoordinateDerivativeData
        G.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart x₀ :=
    CoordinateUpperHalfPlanePullbackFormula.toHyperbolicLocalChartPointedCoordinateDerivativeData_of_coordinateEventuallyEq
      G hxG hCoordG
  refine
    HyperbolicLocalChartPointedFirstOrderMatch_of_coordinateDerivative
      DF DG ?_ ?_
  · simpa [U, V, CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlane] using hvalue
  · have hF :
        CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt F x₀ :=
      CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_coordinateEventuallyEq
        F hCoordF
    have hG :
        CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt G x₀ :=
      CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_coordinateEventuallyEq
        G hCoordG
    dsimp [CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt] at hF hG
    rw [hG, hF]
    simpa [U, V, CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlane] using hderiv

/--
Pointed real-Mobius matching data for two hyperbolic local charts.

The value equation is formalized directly, and the first-order condition is a
real Mobius equality of the pointed oriented tangent frames induced by the two
local hyperbolic coordinates.
-/
structure HyperbolicLocalChartPointedRealMobiusTransition
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) (A : RealMobiusRepresentative) (x₀ : X) :
    Prop where
  mem_left : x₀ ∈ U.domain
  mem_right : x₀ ∈ V.domain
  value_match :
    V.toUpperHalfPlane x₀ =
      realMobiusRepresentativeAction A (U.toUpperHalfPlane x₀)
  first_order_match : HyperbolicLocalChartPointedFirstOrderMatch U V A x₀

/--
Pointed coordinate-derivative data at one surface point gives a pointed real
Mobius comparison there, by transitivity on pointed unit hyperbolic tangent
frames.
-/
theorem HyperbolicLocalChartPointedRealMobiusTransition.exists_of_coordinateDerivativeData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {x₀ : X}
    (DU : HyperbolicLocalChartPointedCoordinateDerivativeData U x₀)
    (DV : HyperbolicLocalChartPointedCoordinateDerivativeData V x₀) :
    ∃ A : RealMobiusRepresentative,
      HyperbolicLocalChartPointedRealMobiusTransition U V A x₀ := by
  let FU := DU.toPointedFrame
  let FV := DV.toPointedFrame
  have hNorm : FU.frame.hyperbolicNormSq = FV.frame.hyperbolicNormSq := by
    rw [FU.unit_hyperbolicNormSq, FV.unit_hyperbolicNormSq]
  rcases realMobiusTangentFrameTransitivityTheorem FU.frame FV.frame hNorm with
    ⟨A, hA⟩
  refine ⟨A, ?_⟩
  refine
    { mem_left := DU.mem_domain
      mem_right := DV.mem_domain
      value_match := ?_
      first_order_match := ⟨FU, FV, hA⟩ }
  rw [← FU.base_eq, ← FV.base_eq]
  exact hA.1

/--
For two coordinate pullback formulae, value agreement and the coordinate
derivative chain rule give the full pointed real-Mobius transition package for
the induced hyperbolic local charts, provided the actual ambient derivatives
are identified with the stored coordinate derivatives.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.pointedRealMobiusTransition_of_coordinateDerivative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F G : CoordinateUpperHalfPlanePullbackFormula X g)
    {A : RealMobiusRepresentative} {x₀ : X}
    (hxF : x₀ ∈ F.domain) (hxG : x₀ ∈ G.domain)
    (hEqF : Set.EqOn F.coordinate (chartAt ℂ x₀) F.domain)
    (hEqG : Set.EqOn G.coordinate (chartAt ℂ x₀) G.domain)
    (hF :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt F x₀)
    (hG :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeAt G x₀)
    (hvalue :
      G.localMap (G.coordinate x₀) =
        realMobiusRepresentativeAction A (F.localMap (F.coordinate x₀)))
    (hderiv :
      deriv (fun z : ℂ ↦ (G.localMap z : ℂ)) (G.coordinate x₀) =
        realMobiusRepresentativeDerivativeAt A (F.localMap (F.coordinate x₀)) *
          deriv (fun z : ℂ ↦ (F.localMap z : ℂ)) (F.coordinate x₀)) :
    HyperbolicLocalChartPointedRealMobiusTransition
      F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart
      G.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart A x₀ where
  mem_left := hxF
  mem_right := hxG
  value_match := by
    simpa [CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlane] using hvalue
  first_order_match :=
    CoordinateUpperHalfPlanePullbackFormula.pointedFirstOrderMatch_of_coordinateDerivative
      F G hxF hxG hEqF hEqG hF hG hvalue hderiv

/--
Chart-compatible coordinate pullback formulae give the full pointed
real-Mobius transition package from the stored value and derivative chain-rule
equations.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.pointedRealMobiusTransition_of_coordinateDerivative_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F G : CoordinateUpperHalfPlanePullbackFormula X g)
    {A : RealMobiusRepresentative} {x₀ : X}
    (hxF : x₀ ∈ F.domain) (hxG : x₀ ∈ G.domain)
    (hEqF : Set.EqOn F.coordinate (chartAt ℂ x₀) F.domain)
    (hEqG : Set.EqOn G.coordinate (chartAt ℂ x₀) G.domain)
    (hvalue :
      G.localMap (G.coordinate x₀) =
        realMobiusRepresentativeAction A (F.localMap (F.coordinate x₀)))
    (hderiv :
      deriv (fun z : ℂ ↦ (G.localMap z : ℂ)) (G.coordinate x₀) =
        realMobiusRepresentativeDerivativeAt A (F.localMap (F.coordinate x₀)) *
          deriv (fun z : ℂ ↦ (F.localMap z : ℂ)) (F.coordinate x₀)) :
    HyperbolicLocalChartPointedRealMobiusTransition
      F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart
      G.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart A x₀ :=
  CoordinateUpperHalfPlanePullbackFormula.pointedRealMobiusTransition_of_coordinateDerivative
    F G hxF hxG hEqF hEqG
    (CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_eqOn_chartAt
      F hxF hEqF)
    (CoordinateUpperHalfPlanePullbackFormula.ambientDerivativeAt_of_eqOn_chartAt
      G hxG hEqG)
    hvalue hderiv

/--
Locally chart-compatible coordinate pullback formulae give the full pointed
real-Mobius transition package from the stored value and derivative chain-rule
equations.
-/
theorem CoordinateUpperHalfPlanePullbackFormula.pointedRealMobiusTransition_of_coordinateDerivative_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (F G : CoordinateUpperHalfPlanePullbackFormula X g)
    {A : RealMobiusRepresentative} {x₀ : X}
    (hxF : x₀ ∈ F.domain) (hxG : x₀ ∈ G.domain)
    (hCoordF :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        F x₀)
    (hCoordG :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        G x₀)
    (hvalue :
      G.localMap (G.coordinate x₀) =
        realMobiusRepresentativeAction A (F.localMap (F.coordinate x₀)))
    (hderiv :
      deriv (fun z : ℂ ↦ (G.localMap z : ℂ)) (G.coordinate x₀) =
        realMobiusRepresentativeDerivativeAt A (F.localMap (F.coordinate x₀)) *
          deriv (fun z : ℂ ↦ (F.localMap z : ℂ)) (F.coordinate x₀)) :
    HyperbolicLocalChartPointedRealMobiusTransition
      F.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart
      G.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart A x₀ where
  mem_left := hxF
  mem_right := hxG
  value_match := by
    simpa [CoordinateUpperHalfPlanePullbackFormula.toUpperHalfPlane] using hvalue
  first_order_match :=
    CoordinateUpperHalfPlanePullbackFormula.pointedFirstOrderMatch_of_coordinateDerivative_coordinateEventuallyEq
      F G hxF hxG hCoordF hCoordG hvalue hderiv

/--
A coordinate-branch one-jet equality gives the pointed real-Mobius transition
for the two induced surface hyperbolic charts, once the shared surface
coordinate is chart-compatible at the point.
-/
theorem LocalUpperHalfPlaneDevelopingMap.pointedRealMobiusTransition_of_coordinateBranchOneJet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    {A : RealMobiusRepresentative} {x₀ : X}
    (hx₀ : x₀ ∈ F.domain)
    (hEq : Set.EqOn F.coordinate (chartAt ℂ x₀) F.domain)
    (hz : F.coordinate x₀ ∈ H₁.domain ∩ H₂.domain)
    (hjet :
      (⟨F.coordinate x₀, hz⟩ :
        {z : ℂ // z ∈ H₁.domain ∩ H₂.domain}) ∈
          pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A) :
    HyperbolicLocalChartPointedRealMobiusTransition
      (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₁).toHyperbolicLocalChart
      (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₂).toHyperbolicLocalChart
      A x₀ := by
  let P₁ :=
    (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₁).pullbackFormula
  let P₂ :=
    (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₂).pullbackFormula
  have hvalue :
      P₂.localMap (P₂.coordinate x₀) =
        realMobiusRepresentativeAction A (P₁.localMap (P₁.coordinate x₀)) := by
    simpa [P₁, P₂,
      LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula,
      pointedRealMobiusTransitionOneJetEqualitySet] using hjet.1
  have hderiv :
      deriv (fun z : ℂ ↦ (P₂.localMap z : ℂ)) (P₂.coordinate x₀) =
        realMobiusRepresentativeDerivativeAt A (P₁.localMap (P₁.coordinate x₀)) *
          deriv (fun z : ℂ ↦ (P₁.localMap z : ℂ)) (P₁.coordinate x₀) := by
    have hchain :=
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H₁ A hz.1
    have hderiv' := hjet.2.trans hchain
    simpa [P₁, P₂,
      LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula,
      realMobiusRepresentativeDerivativeAt,
      pointedRealMobiusTransitionOneJetEqualitySet] using hderiv'
  exact
    CoordinateUpperHalfPlanePullbackFormula.pointedRealMobiusTransition_of_coordinateDerivative_eqOn_chartAt
      P₁ P₂ (by simpa [P₁,
        LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula] using hx₀)
      (by simpa [P₂,
        LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula] using hx₀)
      (by simpa [P₁,
        LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula] using hEq)
      (by simpa [P₂,
        LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula] using hEq)
      hvalue hderiv

/--
A coordinate-branch one-jet equality gives the pointed real-Mobius transition
for the two induced surface hyperbolic charts from local ambient-coordinate
compatibility at the point.
-/
theorem LocalUpperHalfPlaneDevelopingMap.pointedRealMobiusTransition_of_coordinateBranchOneJet_coordinateEventuallyEq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X} {F : LocalLiouvilleMetricFormula X g}
    {S₁ S₂ : LocalSchwarzianData F.conformalFactor}
    (H₁ : LocalUpperHalfPlaneDevelopingMap S₁)
    (H₂ : LocalUpperHalfPlaneDevelopingMap S₂)
    (hImage₁ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₁.domain)
    (hImage₂ : ∀ x, x ∈ F.domain → F.coordinate x ∈ H₂.domain)
    {A : RealMobiusRepresentative} {x₀ : X}
    (hx₀ : x₀ ∈ F.domain)
    (hCoord₁ :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        ((H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₁).pullbackFormula) x₀)
    (hCoord₂ :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqAt
        ((H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula
          hImage₂).pullbackFormula) x₀)
    (hz : F.coordinate x₀ ∈ H₁.domain ∩ H₂.domain)
    (hjet :
      (⟨F.coordinate x₀, hz⟩ :
        {z : ℂ // z ∈ H₁.domain ∩ H₂.domain}) ∈
          pointedRealMobiusTransitionOneJetEqualitySet H₁ H₂ A) :
    HyperbolicLocalChartPointedRealMobiusTransition
      (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₁).toHyperbolicLocalChart
      (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₂).toHyperbolicLocalChart
      A x₀ := by
  let P₁ :=
    (H₁.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₁).pullbackFormula
  let P₂ :=
    (H₂.toLocalLiouvilleDevelopingSolutionOfMetricFormula hImage₂).pullbackFormula
  have hvalue :
      P₂.localMap (P₂.coordinate x₀) =
        realMobiusRepresentativeAction A (P₁.localMap (P₁.coordinate x₀)) := by
    simpa [P₁, P₂,
      LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula,
      pointedRealMobiusTransitionOneJetEqualitySet] using hjet.1
  have hderiv :
      deriv (fun z : ℂ ↦ (P₂.localMap z : ℂ)) (P₂.coordinate x₀) =
        realMobiusRepresentativeDerivativeAt A (P₁.localMap (P₁.coordinate x₀)) *
          deriv (fun z : ℂ ↦ (P₁.localMap z : ℂ)) (P₁.coordinate x₀) := by
    have hchain :=
      realMobiusBranchPostcompositionDerivativeChainRuleTheorem H₁ A hz.1
    have hderiv' := hjet.2.trans hchain
    simpa [P₁, P₂,
      LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula,
      realMobiusRepresentativeDerivativeAt,
      pointedRealMobiusTransitionOneJetEqualitySet] using hderiv'
  exact
    CoordinateUpperHalfPlanePullbackFormula.pointedRealMobiusTransition_of_coordinateDerivative_coordinateEventuallyEq
      P₁ P₂ (by simpa [P₁,
        LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula] using hx₀)
      (by simpa [P₂,
        LocalUpperHalfPlaneDevelopingMap.toLocalLiouvilleDevelopingSolutionOfMetricFormula] using hx₀)
      (by simpa [P₁] using hCoord₁)
      (by simpa [P₂] using hCoord₂)
      hvalue hderiv

/--
Pointed real-Mobius matching target for two hyperbolic local charts.

Classically this is obtained by evaluating the two local isometries and their
oriented tangent maps at one point of the overlap, then using transitivity of
orientation-preserving isometries of `ℍ` on oriented orthonormal frames.
-/
def HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g) (x₀ : X),
    x₀ ∈ U.domain → x₀ ∈ V.domain →
      ∃ A : RealMobiusRepresentative,
        HyperbolicLocalChartPointedRealMobiusTransition U V A x₀

/--
Pointed chart frames plus transitivity of real Mobius transformations on
equal-length upper-half-plane tangent frames give the pointed real-Mobius
matching theorem.
-/
def hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem_of_frames
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hFrames : HyperbolicLocalChartsHavePointedFramesTheorem X)
    (hTrans : RealMobiusTangentFrameTransitivityTheorem) :
    HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X := by
  intro g U V x₀ hxU hxV
  rcases hFrames g U x₀ hxU with ⟨FU⟩
  rcases hFrames g V x₀ hxV with ⟨FV⟩
  have hNorm : FU.frame.hyperbolicNormSq = FV.frame.hyperbolicNormSq := by
    rw [FU.unit_hyperbolicNormSq, FV.unit_hyperbolicNormSq]
  rcases hTrans FU.frame FV.frame hNorm with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  refine
    { mem_left := hxU
      mem_right := hxV
      value_match := ?_
      first_order_match := ⟨FU, FV, hA⟩ }
  rw [← FU.base_eq, ← FV.base_eq]
  exact hA.1

/--
Pointed chart frames alone give the pointed real-Mobius matching theorem,
using the proved real-Mobius tangent-frame transitivity theorem.
-/
def hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem_of_frames_proved
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hFrames : HyperbolicLocalChartsHavePointedFramesTheorem X) :
    HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem_of_frames
    hFrames realMobiusTangentFrameTransitivityTheorem

/--
Coordinate derivative data plus frame transitivity gives the pointed
real-Mobius matching theorem.
-/
def hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem_of_coordinateDerivativeData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X)
    (hTrans : RealMobiusTangentFrameTransitivityTheorem) :
    HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem_of_frames
    (hyperbolicLocalChartsHavePointedFramesTheorem_of_coordinateDerivativeData hDeriv)
    hTrans

/--
Coordinate derivative data alone gives the pointed real-Mobius matching
theorem, using the proved real-Mobius tangent-frame transitivity theorem.
-/
def hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem_of_coordinateDerivativeData_proved
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hDeriv :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X) :
    HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem_of_coordinateDerivativeData
    hDeriv realMobiusTangentFrameTransitivityTheorem

/--
The Poincare pullback squared-density formula gives pointed real-Mobius
matching for all hyperbolic local charts.
-/
def hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] :
    HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X :=
  hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem_of_coordinateDerivativeData_proved
    (hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula_proved
      hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem)

end HyperbolicMetric

end

end JJMath
