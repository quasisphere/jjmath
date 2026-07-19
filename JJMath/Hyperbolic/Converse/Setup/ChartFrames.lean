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

%%handwave
name:
  Real Möbius transformations are transitive on equal-length tangent frames
statement:
  If pointed tangent frames \((p,v)\) and \((q,w)\) in the upper half-plane satisfy \(|v|^2/(\operatorname{Im}p)^2=|w|^2/(\operatorname{Im}q)^2\), then some \(A\in\mathrm{PSL}_2(\mathbb R)\) satisfies \(A(p)=q\) and \(A'(p)v=w\).
proof:
  First choose a real Möbius transformation sending \(p\) to \(q\). Transport both tangent vectors to \(i\); their Euclidean norms agree there, so a rotation about \(i\) matches them. Conjugate that rotation back to the stabilizer of \(q\) and compose, using the derivative chain rule.
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

/-- The ambient chartwise density is positive at the pointed surface point.

%%handwave
name:
  The coordinate density of a hyperbolic metric is positive
statement:
  For a hyperbolic local chart \(U\) and \(x_0\in U\), the squared density \(\rho^2(x_0)\) of the source metric in the ambient complex chart is strictly positive.
proof:
  The ambient coordinate of \(x_0\) lies in the chart target, where the squared density of a conformal metric is positive.
-/
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

%%handwave
name:
  A hyperbolic local chart pulls back the Poincaré density
statement:
  Let \(U\) be a hyperbolic local chart on a Riemann surface and \(x_0\in U\). If \(dU_{x_0}\) denotes its derivative in the ambient chart and \(\rho^2(x_0)\) the source squared density, then \(|dU_{x_0}|^2/(\operatorname{Im}U(x_0))^2=\rho^2(x_0)\).
proof:
  Write the ambient expression as the stored local isometry composed with the transition from the ambient chart to its own chart. The holomorphic chain rule factors the derivative norm, while the conformal-density transition law contributes the same transition factor. Substitute the stored Poincaré pullback identity and cancel.
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

%%handwave
name:
  All hyperbolic local charts satisfy the Poincaré pullback formula
statement:
  On a Riemann surface, every hyperbolic local chart \(U\) and every \(x_0\in U\) satisfy \(|dU_{x_0}|^2/(\operatorname{Im}U(x_0))^2=\rho^2(x_0)\).
proof:
  Apply [the ambient-coordinate Poincaré pullback identity for a hyperbolic local chart](lean:JJMath.HyperbolicMetric.hyperbolicLocalChart_pullbackSquaredDensityFormulaAt) at each point of its domain.
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

%%handwave
name:
  The Poincaré pullback identity forces a nonzero derivative
statement:
  If \(x_0\in U\) and \(|dU_{x_0}|^2/(\operatorname{Im}U(x_0))^2=\rho^2(x_0)\), then \(dU_{x_0}\ne0\).
proof:
  If the derivative vanished, the left side would be zero. The right side is the strictly positive source squared density, a contradiction.
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

%%handwave
name:
  The stored coordinate formula is the Poincaré pullback identity
statement:
  For a coordinate pullback formula \((\kappa,f)\) and \(x_0\) in its surface domain, \(|f'(\kappa(x_0))|^2/(\operatorname{Im}f(\kappa(x_0)))^2\) equals the source metric squared density in the stored chart at \(\kappa(x_0)\).
proof:
  This is the defining stored pullback-density equality, read in the required orientation.
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

%%handwave
name:
  Chart-compatible coordinates give the ambient density
statement:
  Let a coordinate pullback formula have coordinate \(\kappa\), stored chart \(e\), and let \(x_0\) lie in its domain. If \(\kappa=\varphi_{x_0}\) throughout that domain, then \(\rho_e^2(\kappa(x_0))=\rho_{\varphi_{x_0}}^2(\varphi_{x_0}(x_0))\).
proof:
  Near \(\varphi_{x_0}(x_0)\), the transition \(e\circ\varphi_{x_0}^{-1}\) is the identity because both charts equal \(\kappa\) on the domain. Its derivative is therefore one, and the conformal-density transition law gives the equality.
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

%%handwave
name:
  The stored upper-half-plane coordinate has nonzero derivative
statement:
  For a coordinate pullback formula \((\kappa,f)\) and \(x_0\) in its domain, \(f'(\kappa(x_0))\ne0\).
proof:
  The local-map data explicitly asserts nonvanishing of the derivative throughout its coordinate domain.
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

%%handwave
name:
  Domainwise chart compatibility gives local ambient coordinates
statement:
  If the stored coordinate \(\kappa\) equals the ambient chart \(\varphi_{x_0}\) on the formula domain containing \(x_0\), then \(\kappa(x_0)=\varphi_{x_0}(x_0)\) and \(\kappa\circ\varphi_{x_0}^{-1}\) is the identity near \(\varphi_{x_0}(x_0)\).
proof:
  The point equality is the hypothesis at \(x_0\). Openness of the domain makes its inverse-chart preimage a neighborhood, and on that neighborhood chart compatibility combines with the local inverse identity.
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

%%handwave
name:
  Local ambient coordinates identify chartwise densities
statement:
  Suppose \(x_0\) lies in a coordinate pullback formula and \(\kappa(x_0)=\varphi_{x_0}(x_0)\), with \(\kappa\circ\varphi_{x_0}^{-1}\) locally equal to the identity. Then the source squared density in the stored chart at \(\kappa(x_0)\) equals its density in \(\varphi_{x_0}\) at \(\varphi_{x_0}(x_0)\).
proof:
  The stored chart transition agrees locally with the identity and hence has derivative one. Substitute this into the conformal-density transition law.
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

%%handwave
name:
  Local coordinate identity gives local equality of map expressions
statement:
  If \(\kappa\circ\varphi_{x_0}^{-1}\) is locally the identity at \(\varphi_{x_0}(x_0)\), then \(f\circ\kappa\circ\varphi_{x_0}^{-1}\) is locally equal to \(f\) there.
proof:
  Postcompose the local coordinate equality by the stored upper-half-plane map \(f\).
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

%%handwave
name:
  Locally equal coordinate expressions have equal derivative norms
statement:
  If \(\kappa(x_0)=\varphi_{x_0}(x_0)\) and \(f\circ\kappa\circ\varphi_{x_0}^{-1}\) agrees locally with \(f\), then the squared norm of the induced chart derivative at \(x_0\) is \(|f'(\kappa(x_0))|^2\).
proof:
  Functions with the same germ have equal derivatives. Replace the ambient expression by \(f\) and use the base-point equality.
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

%%handwave
name:
  Locally equal coordinate expressions have equal derivatives
statement:
  If \(\kappa(x_0)=\varphi_{x_0}(x_0)\) and \(f\circ\kappa\circ\varphi_{x_0}^{-1}\) agrees locally with \(f\), then the induced chart derivative at \(x_0\) is \(f'(\kappa(x_0))\).
proof:
  The derivative depends only on the germ. Replace the ambient coordinate expression by \(f\), then identify the two base points.
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

%%handwave
name:
  Derivative identification implies derivative-norm identification
statement:
  If the ambient derivative of the induced chart at \(x_0\) equals \(f'(\kappa(x_0))\), then its squared norm equals \(|f'(\kappa(x_0))|^2\).
proof:
  Apply the squared complex norm to the given derivative equality.
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

%%handwave
name:
  Local ambient coordinates identify the derivative norm
statement:
  If \(\kappa(x_0)=\varphi_{x_0}(x_0)\) and \(\kappa\circ\varphi_{x_0}^{-1}\) is locally the identity, then the induced chart has derivative norm \(|f'(\kappa(x_0))|^2\) at \(x_0\).
proof:
  Postcomposition by \(f\) gives local equality of the ambient and stored expressions; equality of germs then gives equality of their derivative norms.
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

%%handwave
name:
  Local ambient coordinates identify the derivative
statement:
  If \(\kappa(x_0)=\varphi_{x_0}(x_0)\) and \(\kappa\circ\varphi_{x_0}^{-1}\) is locally the identity, then the induced chart derivative at \(x_0\) is \(f'(\kappa(x_0))\).
proof:
  Postcompose the local coordinate identity by \(f\), then use invariance of the derivative under equality of germs and the base-point equality.
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

%%handwave
name:
  Chart-compatible coordinates identify the derivative norm
statement:
  If \(x_0\) lies in the formula domain and \(\kappa=\varphi_{x_0}\) on that domain, then the induced chart derivative has squared norm \(|f'(\kappa(x_0))|^2\).
proof:
  Domainwise chart compatibility yields the local ambient-coordinate identity, which identifies the two derivative norms.
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

%%handwave
name:
  Chart-compatible coordinates identify the derivative
statement:
  If \(x_0\) lies in the formula domain and \(\kappa=\varphi_{x_0}\) on that domain, then the induced chart derivative at \(x_0\) equals \(f'(\kappa(x_0))\).
proof:
  Domainwise chart compatibility yields the local ambient-coordinate identity, which identifies the two derivatives.
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

%%handwave
name:
  An aligned developing construction inherits its surface coordinate
statement:
  Suppose the metric formula of an aligned Liouville developing construction uses the ambient chart \(\varphi_c\) on its domain. Then its induced coordinate pullback formula also uses \(\varphi_c\) throughout its domain.
proof:
  The pullback formula has the same coordinate as the metric formula, and its domain is contained in the metric-formula domain.
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

%%handwave
name:
  A coordinate pullback formula induces the Poincaré density identity
statement:
  Let \((\kappa,f)\) be a coordinate pullback formula at \(x_0\). If \(\kappa\) agrees with the ambient chart on the domain and the induced chart derivative has squared norm \(|f'(\kappa(x_0))|^2\), then the induced chart satisfies \(|d(f\circ\kappa)_{x_0}|^2/(\operatorname{Im}f(\kappa(x_0)))^2=\rho^2(x_0)\).
proof:
  Replace the ambient derivative norm by the stored derivative norm. The stored Poincaré pullback identity gives the density in the stored chart, and chart compatibility identifies that density with the ambient one.
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

%%handwave
name:
  A locally ambient coordinate formula induces the Poincaré density identity
statement:
  Let \((\kappa,f)\) be a coordinate pullback formula at \(x_0\). If \(\kappa\circ\varphi_{x_0}^{-1}\) is locally the identity with the correct base value, then the induced chart satisfies \(|d(f\circ\kappa)_{x_0}|^2/(\operatorname{Im}f(\kappa(x_0)))^2=\rho^2(x_0)\).
proof:
  Local coordinate identity identifies both the ambient derivative norm and the stored chart density. Substitute these identifications into the stored Poincaré pullback formula.
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

%%handwave
name:
  Derivative-norm identification makes the induced chart regular
statement:
  Let \((\kappa,f)\) be a coordinate pullback formula at \(x_0\). If the squared norm of the induced chart derivative equals \(|f'(\kappa(x_0))|^2\), then that induced derivative is nonzero.
proof:
  The stored derivative norm is strictly positive on the formula domain. Hence the identified ambient derivative norm is positive and the derivative cannot vanish.
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

%%handwave
name:
  An induced hyperbolic chart satisfies the Poincaré pullback identity
statement:
  On a Riemann surface, the hyperbolic local chart induced by any coordinate pullback formula satisfies the ambient-coordinate Poincaré squared-density identity at every point of its domain.
proof:
  Apply [the Poincaré pullback identity for every hyperbolic local chart](lean:JJMath.HyperbolicMetric.hyperbolicLocalChart_pullbackSquaredDensityFormulaAt) to the induced chart.
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

%%handwave
name:
  Every coordinate pullback formula induces the Poincaré density identity
statement:
  On a Riemann surface, for every coordinate pullback formula and every point of its domain, the induced hyperbolic local chart satisfies the ambient-coordinate Poincaré squared-density formula.
proof:
  Apply [the induced chart satisfies the pullback identity pointwise](lean:JJMath.HyperbolicMetric.CoordinateUpperHalfPlanePullbackFormula.hyperbolicLocalChart_pullbackSquaredDensityFormulaAt_from_chartTransition) to each formula and point.
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

%%handwave
name:
  Every coordinate pullback formula has a nonzero Poincare-normalized derivative
statement:
  On a Riemann surface, every coordinate pullback formula and every point \(x_0\) of its domain determine nonzero ambient coordinate derivative data satisfying the Poincaré pullback identity for the induced hyperbolic chart.
proof:
  The chart-transition pullback formula supplies the squared-density identity, and positivity of the source density makes its derivative nonzero. Package these facts with the domain membership.
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

%%handwave
name:
  The normalized chart derivative is nonzero
statement:
  Let \(U\) be a hyperbolic local chart and \(x_0\in U\). If its ambient coordinate derivative \(dU_{x_0}\) is nonzero and satisfies the Poincaré pullback identity, then \(dU_{x_0}/\sqrt{\rho^2(x_0)}\ne0\).
proof:
  The squared density \(\rho^2(x_0)\) is positive, so its square root is nonzero. Division by it therefore preserves nonvanishing of the coordinate derivative.
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

%%handwave
name:
  The normalized chart derivative has unit hyperbolic norm
statement:
  Let \(U\) be a hyperbolic local chart and \(x_0\in U\). If \(|dU_{x_0}|^2/(\operatorname{Im}U(x_0))^2=\rho^2(x_0)\), then \(\bigl|dU_{x_0}/\sqrt{\rho^2(x_0)}\bigr|^2/(\operatorname{Im}U(x_0))^2=1\).
proof:
  Expand the squared norm of the quotient and substitute the pullback identity. Positivity of \(\rho^2(x_0)\) permits cancellation of its square root.
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

/-- Even the abstract first-order frame match includes the value equation.

%%handwave
name:
  A pointed frame match matches chart values
statement:
  If the pointed frames of hyperbolic charts \(U,V\) at \(x_0\) are carried into one another by \(A\in\mathrm{PSL}_2(\mathbb R)\), then \(V(x_0)=A\cdot U(x_0)\).
proof:
  The bases of the two frames are respectively \(U(x_0)\) and \(V(x_0)\). The base-point component of the frame equality is therefore exactly the asserted value equation.
-/
theorem HyperbolicLocalChartPointedFirstOrderMatch.value_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative} {x₀ : X}
    (h : HyperbolicLocalChartPointedFirstOrderMatch U V A x₀) :
    V.toUpperHalfPlane x₀ =
      realMobiusRepresentativeAction A (U.toUpperHalfPlane x₀) := by
  rcases h with ⟨FU, FV, hmap⟩
  rw [← FV.base_eq, ← FU.base_eq]
  exact hmap.1

/-- The abstract first-order frame match includes membership in the left chart domain.

%%handwave
name:
  A pointed frame match lies in the first chart
statement:
  If hyperbolic charts \(U,V\) have a pointed first-order match at \(x_0\), then \(x_0\in U\).
proof:
  The first pointed frame contained in the match records membership of \(x_0\) in the domain of \(U\).
-/
theorem HyperbolicLocalChartPointedFirstOrderMatch.mem_left
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative} {x₀ : X}
    (h : HyperbolicLocalChartPointedFirstOrderMatch U V A x₀) :
    x₀ ∈ U.domain := by
  rcases h with ⟨FU, _FV, _hmap⟩
  exact FU.mem_domain

/-- The abstract first-order frame match includes membership in the right chart domain.

%%handwave
name:
  A pointed frame match lies in the second chart
statement:
  If hyperbolic charts \(U,V\) have a pointed first-order match at \(x_0\), then \(x_0\in V\).
proof:
  The second pointed frame contained in the match records membership of \(x_0\) in the domain of \(V\).
-/
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

%%handwave
name:
  A pointed frame match gives the coordinate derivative chain rule
statement:
  If the normalized pointed frames of \(U,V\) at \(x_0\) are matched by \(A\in\mathrm{PSL}_2(\mathbb R)\), then \(dV_{x_0}=A'(U(x_0))\,dU_{x_0}\).
proof:
  The frame equality gives this identity after both derivatives are divided by the same positive square root of the source metric density. Multiply by that nonzero factor and cancel it.
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

%%handwave
name:
  Normalized value and derivative equations give a pointed frame match
statement:
  Let \(U,V\) carry pointed coordinate-derivative data at \(x_0\). If \(V(x_0)=A\cdot U(x_0)\) and \(\widehat{dV}_{x_0}=A'(U(x_0))\widehat{dU}_{x_0}\), then their pointed frames are matched by \(A\).
proof:
  Use the canonical frames supplied by the two derivative-data packages. Their base and tangent equations are precisely the two hypotheses.
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

%%handwave
name:
  The coordinate chain rule survives metric normalization
statement:
  If \(dV_{x_0}=A'(U(x_0))\,dU_{x_0}\), then the normalized derivatives satisfy \(\widehat{dV}_{x_0}=A'(U(x_0))\widehat{dU}_{x_0}\).
proof:
  Both charts use the same ambient source metric density at \(x_0\). Divide the given equality by its square root and reassociate multiplication.
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

%%handwave
name:
  Value and coordinate derivative equations give a pointed frame match
statement:
  Let \(U,V\) carry pointed coordinate-derivative data at \(x_0\). If \(V(x_0)=A\cdot U(x_0)\) and \(dV_{x_0}=A'(U(x_0))\,dU_{x_0}\), then their pointed frames are matched by \(A\).
proof:
  The coordinate derivative equation passes to normalized derivatives because both charts use the same source density. The resulting value and normalized-derivative equations define the required frame match.
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

%%handwave
name:
  A concrete first-order match gives a pointed frame match
statement:
  For charts \(U,V\) with pointed coordinate-derivative data at \(x_0\), the equations \(V(x_0)=A\cdot U(x_0)\) and \(dV_{x_0}=A'(U(x_0))\,dU_{x_0}\) yield a pointed first-order frame match.
proof:
  Apply the construction from the value and coordinate derivative equations.
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

/-- Canonical first-order matching forgets to the abstract frame predicate.

%%handwave
name:
  Canonical pointed matching gives an abstract frame match
statement:
  An explicit match between the canonical normalized derivative frames of \(U\) and \(V\) at \(x_0\) is a pointed first-order frame match.
proof:
  Forget that the two frames were canonically constructed and retain the frames together with their matching equation.
-/
theorem HyperbolicLocalChartPointedFirstOrderMatch_of_canonical
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {A : RealMobiusRepresentative} {x₀ : X}
    (h : HyperbolicLocalChartCanonicalPointedFirstOrderMatch U V A x₀) :
    HyperbolicLocalChartPointedFirstOrderMatch U V A x₀ := by
  rcases h with ⟨DU, DV, hmap⟩
  exact ⟨DU.toPointedFrame, DV.toPointedFrame, hmap⟩

/-- Canonical first-order matching includes the value equation.

%%handwave
name:
  A canonical pointed match matches chart values
statement:
  If the canonical normalized derivative frames of \(U,V\) at \(x_0\) are matched by \(A\), then \(V(x_0)=A\cdot U(x_0)\).
proof:
  The base points of the canonical frames are the two chart values, so the base component of their frame match is the stated equality.
-/
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

%%handwave
name:
  A canonical pointed match gives the coordinate chain rule
statement:
  If the canonical normalized derivative frames of \(U,V\) at \(x_0\) are matched by \(A\), then \(dV_{x_0}=A'(U(x_0))\,dU_{x_0}\).
proof:
  The tangent component matches the derivatives after division by the common factor \(\sqrt{\rho^2(x_0)}\). Positivity of the source density makes this factor nonzero, so multiplying through gives the unnormalized chain rule.
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
For two coordinate pullback formulae, actual ambient derivative identification
turns the ordinary coordinate derivative chain rule into the abstract
first-order frame match for the induced hyperbolic local charts.

%%handwave
name:
  Coordinate one-jets induce a pointed frame match
statement:
  Let \((\kappa_F,f)\) and \((\kappa_G,g)\) be coordinate pullback formulae at \(x_0\), compatible there with the ambient chart. If their induced ambient derivatives equal \(f'(\kappa_F(x_0))\) and \(g'(\kappa_G(x_0))\), and \(g(\kappa_G(x_0))=A\cdot f(\kappa_F(x_0))\) with \(g'=A'(f)f'\) at that point, then the induced hyperbolic charts have a pointed first-order match by \(A\).
proof:
  The derivative-norm identifications supply canonical pointed derivative data for both induced charts. Substitute the actual derivative identifications into the coordinate chain rule and apply the value-and-derivative frame construction.
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
Locally chart-compatible coordinate pullback formulae satisfy the pairwise
first-order frame bridge as soon as their stored coordinate values and
derivatives satisfy the real-Mobius value and chain-rule equations.

%%handwave
name:
  Locally ambient coordinate one-jets induce a pointed frame match
statement:
  Let two coordinate pullback formulae have source coordinates that become the identity in the ambient chart near \(x_0\). If their stored values and derivatives satisfy the value and chain-rule equations for \(A\in\mathrm{PSL}_2(\mathbb R)\), then their induced hyperbolic charts have a pointed first-order match by \(A\).
proof:
  Local coordinate identity supplies the canonical derivative data and identifies each ambient derivative with the stored derivative. The given one-jet equations then produce the frame match.
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

%%handwave
name:
  Two pointed hyperbolic chart frames differ by a real Möbius transformation
statement:
  If hyperbolic charts \(U,V\) carry pointed coordinate-derivative data at \(x_0\), then some \(A\in\mathrm{PSL}_2(\mathbb R)\) matches their values and normalized first derivatives at \(x_0\).
proof:
  The canonical normalized derivative frames both have unit hyperbolic norm. Transitivity of \(\mathrm{PSL}_2(\mathbb R)\) on equal-length pointed tangent frames supplies \(A\); its base and tangent equations give the transition package.
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

%%handwave
name:
  Coordinate one-jets give a pointed real Möbius transition
statement:
  For two chart-compatible coordinate pullback formulae at \(x_0\), suppose their ambient derivatives are identified with their stored derivatives and their stored values and derivatives obey the one-jet equations for \(A\). Then \(A\) is a pointed real Möbius transition between the induced hyperbolic charts.
proof:
  The domain and value components are immediate. The derivative hypotheses and one-jet equations give the pointed first-order frame component.
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

%%handwave
name:
  Chart-compatible coordinate one-jets give a pointed real Möbius transition
statement:
  If two coordinate pullback formulae agree with the ambient chart on their domains at \(x_0\), and their stored values and derivatives obey the one-jet equations for \(A\), then \(A\) is a pointed real Möbius transition between their induced hyperbolic charts.
proof:
  Chart compatibility identifies both ambient derivatives with the stored derivatives. Apply the coordinate one-jet transition result.
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

%%handwave
name:
  Locally ambient coordinate one-jets give a pointed real Möbius transition
statement:
  If the source coordinates of two pullback formulae become the identity in the ambient chart near \(x_0\), and their stored values and derivatives satisfy the one-jet equations for \(A\), then \(A\) is a pointed real Möbius transition between the induced hyperbolic charts.
proof:
  The two domain assumptions and the value equation give the first three components. Local coordinate identity turns the stored derivative chain rule into the required first-order frame match.
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

%%handwave
name:
  A developing-branch one-jet gives a pointed real Möbius transition
statement:
  Let \(H_1,H_2\) be upper-half-plane developing branches over the same chart coordinate \(\kappa\), and let \(x_0\) lie in their common domain. If \(\kappa\) agrees with the ambient chart and the value and derivative one-jets of the branches at \(\kappa(x_0)\) agree after postcomposition by \(A\in\mathrm{PSL}_2(\mathbb R)\), then \(A\) gives a pointed transition between the induced hyperbolic charts at \(x_0\).
proof:
  The one-jet hypothesis gives the value equation. Combine its derivative equality with the chain rule for postcomposition by \(A\), then apply the chart-compatible coordinate transition theorem.
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

%%handwave
name:
  A locally ambient developing-branch one-jet gives a pointed transition
statement:
  Let \(H_1,H_2\) be upper-half-plane developing branches over the same surface coordinate near \(x_0\). If both induced source coordinates become the ambient coordinate locally and their one-jets at the common coordinate value agree after postcomposition by \(A\in\mathrm{PSL}_2(\mathbb R)\), then \(A\) gives a pointed transition between the induced hyperbolic charts.
proof:
  Extract the value equality from the one-jet hypothesis and combine its derivative equality with the postcomposition chain rule. The locally ambient coordinate transition theorem then supplies the full pointed transition.
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
