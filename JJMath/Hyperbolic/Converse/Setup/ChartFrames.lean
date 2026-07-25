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

/-- Squared hyperbolic norm of an upper-half-plane tangent frame.

%%handwave
name: Squared hyperbolic norm of an upper-half-plane tangent frame
statement:
  For a tangent frame $(p,v)$ in the upper half-plane, define its squared
  hyperbolic norm by $\lVert(p,v)\rVert_{\mathbb H}^2
  =|v|^2/(\operatorname{Im}p)^2$.
-/
def hyperbolicNormSq (F : UpperHalfPlaneTangentFrame) : ℝ :=
  Complex.normSq F.tangent / ((F.base : ℂ).im ^ 2)

end UpperHalfPlaneTangentFrame

/--
The complex derivative of a real Mobius representative at a point of `ℍ`.

This is the tangent multiplier for the standard upper-half-plane coordinate.

%%handwave
name: The complex derivative of a real Möbius representative at a point of ℍ
statement:
  For a real Möbius transformation $A$ and $p\in\mathbb H$, define
  $A'(p)$ as the complex derivative of its standard upper-half-plane action
  at $p$.
-/
def realMobiusRepresentativeDerivativeAt
    (A : RealMobiusRepresentative) (p : ℍ) : ℂ :=
  deriv
    (fun z : ℂ ↦
      (realMobiusRepresentativeAction A ((UpperHalfPlane.ofComplex : ℂ → ℍ) z) : ℂ))
    p

/-- A real Mobius representative maps one pointed tangent frame to another.

%%handwave
name: A real Möbius representative maps one pointed tangent frame to another
statement:
  A real Möbius transformation $A$ maps $(p,v)$ to $(q,w)$ precisely when
  $q=A(p)$ and $w=A'(p)v$.
-/
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

%%handwave
name: Frame transitivity of the upper-half-plane real Möbius action
statement:
  If two nonzero tangent frames $(p,v)$ and $(q,w)$ in $\mathbb H$ have
  equal hyperbolic norm, then some real Möbius transformation $A$ satisfies
  $A(p)=q$ and $A'(p)v=w$.
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

%%handwave
name: The local expression of a hyperbolic chart in the ambient complex coordinate at a surface point
statement:
  For a hyperbolic chart $U$ and $x_0\in X$, define its ambient-coordinate
  expression by $z\mapsto U((\varphi_{x_0})^{-1}(z))$, where
  $\varphi_{x_0}$ is the ambient complex chart at $x_0$.
-/
def hyperbolicLocalChartCoordinateExpressionAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U : HyperbolicLocalChart X g) (x₀ : X) (z : ℂ) : ℂ :=
  (U.toUpperHalfPlane ((chartAt ℂ x₀).symm z) : ℂ)

/--
The complex derivative of a hyperbolic local chart in the ambient coordinate
at a surface point.

%%handwave
name: The complex derivative of a hyperbolic local chart in the ambient coordinate at a surface point
statement:
  Define $dU_{x_0}$ as the complex derivative at $\varphi_{x_0}(x_0)$ of
  the ambient-coordinate expression
  $z\mapsto U((\varphi_{x_0})^{-1}(z))$.
-/
def hyperbolicLocalChartCoordinateDerivativeAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U : HyperbolicLocalChart X g) (x₀ : X) : ℂ :=
  deriv (hyperbolicLocalChartCoordinateExpressionAt U x₀) ((chartAt ℂ x₀) x₀)

/--
The squared density of the source metric in the ambient chart used to compute
the coordinate derivative at the pointed surface point.

%%handwave
name: The squared density of the source metric in the ambient chart used to compute the coordinate derivative at the pointed surface point
statement:
  Define $\rho_g^2(x_0)$ as the squared conformal density of $g$ at
  $\varphi_{x_0}(x_0)$ in the ambient complex chart centered at $x_0$.
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

%%handwave
name: The normalized derivative vector of a hyperbolic local chart
statement:
  Define the normalized chart derivative by
  $\widehat{dU}_{x_0}=dU_{x_0}/\sqrt{\rho_g^2(x_0)}$; the Poincaré pullback
  identity makes this a unit hyperbolic tangent vector at $U(x_0)$.
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

%%handwave
name: The pointwise Poincaré pullback squared-density formula for a hyperbolic local chart in the ambient complex coordinate
statement:
  At $x_0$, the chart $U$ satisfies the pointwise pullback formula when
  $|dU_{x_0}|^2/(\operatorname{Im}U(x_0))^2=\rho_g^2(x_0)$.
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

%%handwave
name: The local-isometry principle saying that the abstract pullback-metric field of a hyperbolic local chart gives the concrete ambient-coordinate squared-density formula
statement:
  Every hyperbolic local chart $U$ satisfies
  $|dU_{x_0}|^2/(\operatorname{Im}U(x_0))^2=\rho_g^2(x_0)$ at every
  $x_0\in\operatorname{dom}U$.
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

%%handwave
name: The local-biholomorphism principle saying that the ambient-coordinate derivative of a hyperbolic local chart is nonzero
statement:
  For every hyperbolic local chart $U$ and every
  $x_0\in\operatorname{dom}U$, its ambient-coordinate derivative satisfies
  $dU_{x_0}\ne0$.
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

%%handwave
name: The concrete pullback squared-density formula supplies nonvanishing of the ambient-coordinate derivative
statement:
  The concrete pullback squared-density formula supplies nonvanishing of the ambient-coordinate
  derivative.
-/
def hyperbolicLocalChartCoordinateDerivativeNonzeroTheorem_of_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X) :
    HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X := by
  intro g U x₀ hx₀
  exact (hPull g U x₀ hx₀).coordinateDerivative_ne_zero hx₀

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

%%handwave
name: Coordinate derivative data determines the normalized pointed frame used in the pointed real-transition theorem
statement:
  Pointed chart data consisting of $x_0\in\operatorname{dom}U$, a nonzero
  derivative $dU_{x_0}$, and the Poincaré pullback identity determines the
  unit tangent frame $(U(x_0),\widehat{dU}_{x_0})$.
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

%%handwave
name: every holomorphic local isometry supplies the coordinate derivative data needed to build its normalized oriented frame
statement:
  Every hyperbolic local chart $U$ and point
  $x_0\in\operatorname{dom}U$ admit pointed derivative data: $dU_{x_0}$ is
  nonzero and satisfies the Poincaré pullback squared-density identity.
-/
def HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U : HyperbolicLocalChart X g) (x₀ : X),
    x₀ ∈ U.domain →
      Nonempty (HyperbolicLocalChartPointedCoordinateDerivativeData U x₀)

/--
Nonzero coordinate derivative plus the concrete pullback squared-density
formula supply the pointed coordinate-derivative data.

%%handwave
name: Nonzero coordinate derivative plus the concrete pullback squared-density formula supply the pointed coordinate-derivative data
statement:
  Nonzero coordinate derivative plus the concrete pullback squared-density formula supply the
  pointed coordinate-derivative data.
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

%%handwave
name: The concrete pullback squared-density formula alone supplies the pointed coordinate-derivative data; nonvanishing follows from positivity of the source conformal density
statement:
  The concrete pullback squared-density formula alone supplies the pointed coordinate-derivative
  data; nonvanishing follows from positivity of the source conformal density.
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

%%handwave
name: Analytic differential-geometric target behind pointed matching
statement:
  Every hyperbolic local chart $U$ and point
  $x_0\in\operatorname{dom}U$ admit a nonzero unit hyperbolic tangent frame
  based at $U(x_0)$ and represented by $\widehat{dU}_{x_0}$.
-/
def HyperbolicLocalChartsHavePointedFramesTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U : HyperbolicLocalChart X g) (x₀ : X),
    x₀ ∈ U.domain → Nonempty (HyperbolicLocalChartPointedFrame U x₀)

/--
The coordinate derivative data theorem proves the pointed-frame theorem.

%%handwave
name: The coordinate derivative data theorem proves the pointed-frame theorem
statement:
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

%%handwave
name: Pointed real-Möbius first-order matching for two hyperbolic local charts
statement:
  Charts $U,V$ have a pointed first-order match by $A$ at $x_0$ when they
  admit normalized derivative frames at $x_0$ and $A$ maps the frame of
  $U$ to the frame of $V$.
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

%%handwave
name: Concrete first-order matching for two hyperbolic local charts in the ambient complex coordinate at a surface point
statement:
  Charts $U,V$ have a concrete first-order match by $A$ at $x_0$ when
  $dV_{x_0}=A'(U(x_0))\,dU_{x_0}$.
-/
def HyperbolicLocalChartConcreteFirstOrderMatch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}
    (U V : HyperbolicLocalChart X g) (A : RealMobiusRepresentative) (x₀ : X) :
    Prop :=
  hyperbolicLocalChartCoordinateDerivativeAt V x₀ =
    realMobiusRepresentativeDerivativeAt A (U.toUpperHalfPlane x₀) *
      hyperbolicLocalChartCoordinateDerivativeAt U x₀

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
Pointed real-Mobius matching target for two hyperbolic local charts.

Classically this is obtained by evaluating the two local isometries and their
oriented tangent maps at one point of the overlap, then using transitivity of
orientation-preserving isometries of `ℍ` on oriented orthonormal frames.

%%handwave
name: Pointed real-Möbius matching of two hyperbolic local charts
statement:
  For every pair of hyperbolic local charts $U,V$ and every
  $x_0\in\operatorname{dom}U\cap\operatorname{dom}V$, some real Möbius
  transformation $A$ satisfies $V(x_0)=A(U(x_0))$ and maps the normalized
  derivative frame of $U$ to that of $V$.
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

%%handwave
name: Pointed chart frames plus transitivity of real Möbius transformations on equal-length upper-half-plane tangent frames give the pointed real-Möbius matching theorem
statement:
  Pointed chart frames plus transitivity of real Möbius transformations on equal-length
  upper-half-plane tangent frames give the pointed real-Möbius matching theorem.
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
Coordinate derivative data plus frame transitivity gives the pointed
real-Mobius matching theorem.

%%handwave
name: Coordinate derivative data plus frame transitivity gives the pointed real-Möbius matching theorem
statement:
  Coordinate derivative data plus frame transitivity gives the pointed real-Möbius matching
  theorem.
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

%%handwave
name: Coordinate derivative data alone gives the pointed real-Möbius matching theorem, using the proved real-Möbius tangent-frame transitivity theorem
statement:
  Coordinate derivative data alone gives the pointed real-Möbius matching theorem, using the
  proved real-Möbius tangent-frame transitivity theorem.
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

%%handwave
name: The Poincaré pullback squared-density formula gives pointed real-Möbius matching for all hyperbolic local charts
statement:
  The Poincaré pullback squared-density formula gives pointed real-Möbius matching for all
  hyperbolic local charts.
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
