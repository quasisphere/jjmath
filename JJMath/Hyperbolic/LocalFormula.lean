import JJMath.Hyperbolic.LocalModels
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Local formulas for hyperbolic conformal metrics

This file names the coordinate formulas feeding the local analytic theorem
inputs.

For a conformal metric `g = λ^2 |dz|^2`, write `λ = exp u`, so that the
squared density is `λ^2 = exp (2u)`.  In a complex coordinate, the curvature
equation `K = -1` is the Liouville equation

`Δ u = exp (2 * u)`.

If `f : U → ℍ` is a local developing map, then the pullback of the Poincare
metric has squared density

`|f'|^2 / (Im f)^2`.

The structures below isolate those two formulas while keeping the existing
project-level `HyperbolicLocalChart` interface stable.
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

/--
A local logarithmic conformal factor for a metric in a complex coordinate.

The intended metric on `coordinateDomain` is `exp (2 * u) |dz|^2`, where
`u = logDensity`.
-/
structure LocalConformalFactor where
  /-- The coordinate domain. -/
  coordinateDomain : Set ℂ
  /-- The coordinate domain is open. -/
  isOpen_coordinateDomain : IsOpen coordinateDomain
  /-- The logarithm of the conformal density. -/
  logDensity : ℂ → ℝ
  /-- The logarithmic density is `C^3` on the coordinate domain. -/
  logDensity_contDiffOn : ContDiffOn ℝ 3 logDensity coordinateDomain
  /-- The logarithmic density is `C^2` on the coordinate domain. -/
  twice_differentiable_on_domain : ContDiffOn ℝ 2 logDensity coordinateDomain

namespace LocalConformalFactor

/-- The squared conformal density `λ^2 = exp (2u)`. -/
def densitySq (u : LocalConformalFactor) (z : ℂ) : ℝ :=
  Real.exp (2 * u.logDensity z)

/--
%%handwave
name:
  Positivity of an exponential conformal density
statement:
  If a local conformal factor has logarithmic density $u$, then its squared density $e^{2u(z)}$ is positive for every $z\in\mathbb C$.
proof:
  The real exponential is strictly positive.
-/
theorem densitySq_pos (u : LocalConformalFactor) (z : ℂ) : 0 < u.densitySq z := by
  exact Real.exp_pos _

/-- The Liouville equation for curvature `-1`: `Δ u = exp (2u)`. -/
def SolvesLiouvilleEquation (u : LocalConformalFactor) : Prop :=
  ∀ z, z ∈ u.coordinateDomain →
    Laplacian.laplacian u.logDensity z = Real.exp (2 * u.logDensity z)

/-- Restrict a local conformal factor to an open subdomain. -/
def restrict (u : LocalConformalFactor) (V : Set ℂ) (hVOpen : IsOpen V)
    (_hV : V ⊆ u.coordinateDomain) : LocalConformalFactor where
  coordinateDomain := V
  isOpen_coordinateDomain := hVOpen
  logDensity := u.logDensity
  logDensity_contDiffOn := u.logDensity_contDiffOn.mono _hV
  twice_differentiable_on_domain := u.twice_differentiable_on_domain.mono _hV

/--
%%handwave
name:
  Coordinate domain of a restricted conformal factor
statement:
  Restricting a local conformal factor from $\Omega$ to an open subset $V\subseteq\Omega$ gives a conformal factor whose coordinate domain is exactly $V$.
proof:
  The restricted conformal factor is defined with coordinate domain $V$.
-/
@[simp]
theorem restrict_coordinateDomain (u : LocalConformalFactor) (V : Set ℂ)
    (hVOpen : IsOpen V) (hV : V ⊆ u.coordinateDomain) :
    (u.restrict V hVOpen hV).coordinateDomain = V :=
  rfl

/--
%%handwave
name:
  Logarithmic density under restriction
statement:
  If a local conformal factor $u$ on $\Omega$ is restricted to an open subset $V\subseteq\Omega$, its logarithmic density remains the same function $u$.
proof:
  Restriction changes only the certified domain, not the logarithmic-density function.
-/
@[simp]
theorem restrict_logDensity (u : LocalConformalFactor) (V : Set ℂ)
    (hVOpen : IsOpen V) (hV : V ⊆ u.coordinateDomain) :
    (u.restrict V hVOpen hV).logDensity = u.logDensity :=
  rfl

/--
%%handwave
name:
  Squared density under restriction
statement:
  For a local conformal factor on $\Omega$, its restriction to $V\subseteq\Omega$ has the same squared density $e^{2u(z)}$ at every $z\in\mathbb C$.
proof:
  The logarithmic-density function is unchanged by restriction, hence so is its exponential square.
-/
@[simp]
theorem restrict_densitySq (u : LocalConformalFactor) (V : Set ℂ)
    (hVOpen : IsOpen V) (hV : V ⊆ u.coordinateDomain) (z : ℂ) :
    (u.restrict V hVOpen hV).densitySq z = u.densitySq z :=
  rfl

/-- The Liouville equation restricts to open subdomains.

%%handwave
name:
  The Liouville equation restricts to open subdomains
statement:
  If $u$ satisfies $\Delta u=e^{2u}$ on $\Omega$ and $V\subseteq\Omega$ is open, then the restricted conformal factor satisfies $\Delta u=e^{2u}$ on $V$.
proof:
  Every point of $V$ lies in $\Omega$, so apply the original equation there.
-/
theorem restrict_solvesLiouvilleEquation
    (u : LocalConformalFactor) (V : Set ℂ) (hVOpen : IsOpen V)
    (hV : V ⊆ u.coordinateDomain) (hu : u.SolvesLiouvilleEquation) :
    (u.restrict V hVOpen hV).SolvesLiouvilleEquation := by
  intro z hz
  exact hu z (hV hz)

/--
The Gaussian curvature of the conformal metric `exp (2u) |dz|^2` in a local
complex coordinate:

`K = - exp (-2u) * Δ u`.
-/
def gaussianCurvature (u : LocalConformalFactor) (z : ℂ) : ℝ :=
  - Real.exp (-(2 * u.logDensity z)) * Laplacian.laplacian u.logDensity z

/-- The local conformal metric `exp (2u) |dz|^2` has Gaussian curvature `-1`. -/
def HasGaussianCurvatureMinusOne (u : LocalConformalFactor) : Prop :=
  ∀ z, z ∈ u.coordinateDomain → u.gaussianCurvature z = -1

/--
The local curvature formula `K = -exp (-2u) Δu` implies the Liouville equation
when `K = -1`.

%%handwave
name:
  Curvature minus one implies the Liouville equation
statement:
  Let $e^{2u}|dz|^2$ be a local conformal metric on $\Omega$. If $-e^{-2u}\Delta u=-1$ throughout $\Omega$, then $\Delta u=e^{2u}$ throughout $\Omega$.
proof:
  Since $e^{-2u}$ is nonzero, multiply the curvature identity by $e^{2u}$ and simplify $e^{-2u}e^{2u}=1$.
-/
theorem solvesLiouvilleEquation_of_hasGaussianCurvatureMinusOne
    (u : LocalConformalFactor) (hK : u.HasGaussianCurvatureMinusOne) :
    u.SolvesLiouvilleEquation := by
  intro z hz
  have hKz : - Real.exp (-(2 * u.logDensity z)) *
        Laplacian.laplacian u.logDensity z = -1 := by
    simpa [HasGaussianCurvatureMinusOne, gaussianCurvature] using hK z hz
  have hne : Real.exp (-(2 * u.logDensity z)) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  calc
    Laplacian.laplacian u.logDensity z
        = (Real.exp (-(2 * u.logDensity z)))⁻¹ := by
            field_simp [hne] at hKz ⊢
            linarith
    _ = Real.exp (2 * u.logDensity z) := by
            rw [← Real.exp_neg]
            ring_nf

/--
Conversely, the Liouville equation implies `K = -1` for the local conformal
curvature expression.

%%handwave
name:
  The Liouville equation implies curvature minus one
statement:
  Let $e^{2u}|dz|^2$ be a local conformal metric on $\Omega$. If $\Delta u=e^{2u}$ throughout $\Omega$, then its Gaussian curvature $-e^{-2u}\Delta u$ is identically $-1$.
proof:
  Substitute the Liouville equation into the curvature formula and cancel $e^{-2u}e^{2u}=1$.
-/
theorem hasGaussianCurvatureMinusOne_of_solvesLiouvilleEquation
    (u : LocalConformalFactor) (hL : u.SolvesLiouvilleEquation) :
    u.HasGaussianCurvatureMinusOne := by
  intro z hz
  have hpos : 0 < Real.exp (2 * u.logDensity z) := Real.exp_pos _
  calc
    u.gaussianCurvature z
        = - Real.exp (-(2 * u.logDensity z)) *
            Real.exp (2 * u.logDensity z) := by
            rw [gaussianCurvature, hL z hz]
    _ = -1 := by
            rw [Real.exp_neg]
            field_simp [ne_of_gt hpos]

/-- The local curvature `-1` equation is equivalent to the Liouville equation.

%%handwave
name:
  Equivalence of curvature minus one and the Liouville equation
statement:
  For a local conformal metric $e^{2u}|dz|^2$ on $\Omega$, the condition $K\equiv-1$ is equivalent to the Liouville equation $\Delta u=e^{2u}$ on $\Omega$.
proof:
  One implication rearranges $-e^{-2u}\Delta u=-1$; the reverse implication substitutes $\Delta u=e^{2u}$ into the curvature formula.
-/
theorem hasGaussianCurvatureMinusOne_iff_solvesLiouvilleEquation
    (u : LocalConformalFactor) :
    u.HasGaussianCurvatureMinusOne ↔ u.SolvesLiouvilleEquation :=
  ⟨u.solvesLiouvilleEquation_of_hasGaussianCurvatureMinusOne,
    u.hasGaussianCurvatureMinusOne_of_solvesLiouvilleEquation⟩

end LocalConformalFactor

/-- The squared norm `|f'(z)|^2` of the complex derivative of a map to `ℍ`. -/
def complexDerivativeNormSq (f : ℂ → ℍ) (z : ℂ) : ℝ :=
  Complex.normSq (deriv (fun w : ℂ ↦ (f w : ℂ)) z)

/--
%%handwave
name:
  Nonnegativity of the squared complex derivative norm
statement:
  For every map $f:\mathbb C\to\mathbb H$ and every $z\in\mathbb C$, the quantity $|f'(z)|^2$ is nonnegative.
proof:
  A complex norm-square is always nonnegative.
-/
theorem complexDerivativeNormSq_nonneg (f : ℂ → ℍ) (z : ℂ) :
    0 ≤ complexDerivativeNormSq f z :=
  Complex.normSq_nonneg _

/--
Regularity certificate for an abstract upper-half-plane pullback formula on a
surface domain.
-/
structure UpperHalfPlanePullbackFormulaRegularity
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (domain : Set X) (toUpperHalfPlane : X → ℍ) where
  /-- The coordinate domain in `ℂ`. -/
  coordinateDomain : Set ℂ
  /-- The coordinate domain is open. -/
  isOpen_coordinateDomain : IsOpen coordinateDomain
  /-- The local complex coordinate. -/
  coordinate : X → ℂ
  /-- Points in the surface domain lie in the coordinate domain. -/
  coordinate_mem_domain : ∀ x, x ∈ domain → coordinate x ∈ coordinateDomain
  /-- The coordinate expression of the map to `ℍ`. -/
  localMap : ℂ → ℍ
  /-- The surface map agrees with the coordinate expression on the domain. -/
  toUpperHalfPlane_eq :
    ∀ x, x ∈ domain → toUpperHalfPlane x = localMap (coordinate x)
  /-- The coordinate expression is holomorphic on the coordinate domain. -/
  holomorphic_on_domain :
    ∀ z, z ∈ coordinateDomain →
      DifferentiableAt ℂ (fun w : ℂ ↦ (localMap w : ℂ)) z
  /-- The coordinate expression has nonzero derivative on the surface domain. -/
  local_biholomorph_on_domain :
    ∀ x, x ∈ domain →
      deriv (fun z : ℂ ↦ (localMap z : ℂ)) (coordinate x) ≠ 0

/--
The local Poincare pullback squared-density formula for a map to the upper half-plane.

The field `derivativeNormSq` is intended to be `|f'|^2` in the chosen complex
coordinate.  Later, once the coordinate-level holomorphic API is in place, this
should be tied directly to the norm square of `deriv`.
-/
structure UpperHalfPlanePullbackFormula (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) where
  /-- The domain on which the formula is asserted. -/
  domain : Set X
  /-- The domain is open. -/
  isOpen_domain : IsOpen domain
  /-- The local map to the upper half-plane. -/
  toUpperHalfPlane : X → ℍ
  /-- Holomorphicity and local-biholomorphism data for the local map. -/
  regularity : UpperHalfPlanePullbackFormulaRegularity X domain toUpperHalfPlane
  /-- The chart in which the coordinate formula is written. -/
  chart : OpenPartialHomeomorph X ℂ
  /-- The chosen chart belongs to the complex atlas. -/
  chart_mem_atlas : chart ∈ atlas ℂ X
  /-- The formula domain lies in the source of the chosen chart. -/
  domain_subset_chart_source : domain ⊆ chart.source
  /-- The stored coordinate agrees with the chosen chart on the formula domain. -/
  coordinate_eq_chart : Set.EqOn regularity.coordinate chart domain
  /-- The squared norm of the complex derivative in local coordinates. -/
  derivativeNormSq : X → ℝ
  /-- The stored squared derivative norm is the norm square of the coordinate derivative. -/
  derivativeNormSq_eq_coordinate :
    ∀ x, x ∈ domain →
      derivativeNormSq x =
        Complex.normSq
          (deriv (fun z : ℂ ↦ (regularity.localMap z : ℂ))
            (regularity.coordinate x))
  /-- The squared derivative norm is positive on the domain. -/
  derivativeNormSq_pos : ∀ x, x ∈ domain → 0 < derivativeNormSq x
  /-- Poincare pullback squared-density formula in the chosen chart. -/
  densitySqInChart_eq_pullback :
    ∀ x, x ∈ domain →
      g.toConformalMetric.densitySqInChart chart chart_mem_atlas (regularity.coordinate x) =
        derivativeNormSq x / ((toUpperHalfPlane x : ℂ).im ^ 2)

namespace UpperHalfPlanePullbackFormula

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/-- The local map is holomorphic on the domain. -/
def holomorphic_on_domain (F : UpperHalfPlanePullbackFormula X g) : Prop :=
  ∀ z, z ∈ F.regularity.coordinateDomain →
    DifferentiableAt ℂ (fun w : ℂ ↦ (F.regularity.localMap w : ℂ)) z

/-- The local map is a local biholomorphism on the domain. -/
def local_biholomorph_on_domain (F : UpperHalfPlanePullbackFormula X g) : Prop :=
  ∀ x, x ∈ F.domain →
    deriv (fun z : ℂ ↦ (F.regularity.localMap z : ℂ))
      (F.regularity.coordinate x) ≠ 0

/-- The formula package determines the lightweight local chart used upstream. -/
def toHyperbolicLocalChart (F : UpperHalfPlanePullbackFormula X g) :
    HyperbolicLocalChart X g where
  domain := F.domain
  isOpen_domain := F.isOpen_domain
  toUpperHalfPlane := F.toUpperHalfPlane
  local_isometry := {
    coordinateDomain := F.regularity.coordinateDomain
    isOpen_coordinateDomain := F.regularity.isOpen_coordinateDomain
    coordinate := F.regularity.coordinate
    chart := F.chart
    chart_mem_atlas := F.chart_mem_atlas
    domain_subset_chart_source := F.domain_subset_chart_source
    coordinate_eq_chart := F.coordinate_eq_chart
    coordinate_mem_domain := F.regularity.coordinate_mem_domain
    localMap := F.regularity.localMap
    toUpperHalfPlane_eq := F.regularity.toUpperHalfPlane_eq
    holomorphic_on_domain := F.regularity.holomorphic_on_domain
    local_biholomorph_on_domain := F.regularity.local_biholomorph_on_domain
    pulls_back_metric_on_domain := by
      intro x hx
      calc
        g.toConformalMetric.densitySqInChart F.chart F.chart_mem_atlas
              (F.regularity.coordinate x) =
            F.derivativeNormSq x / ((F.toUpperHalfPlane x : ℂ).im ^ 2) :=
          F.densitySqInChart_eq_pullback x hx
        _ =
            Complex.normSq
                (deriv (fun z : ℂ ↦ (F.regularity.localMap z : ℂ))
                  (F.regularity.coordinate x)) /
              ((F.toUpperHalfPlane x : ℂ).im ^ 2) := by
          rw [F.derivativeNormSq_eq_coordinate x hx] }

/--
%%handwave
name:
  Density identity for an upper-half-plane pullback formula
statement:
  Let $F:D\to\mathbb H$ be a local map written in a surface coordinate $\zeta$. For every $x\in D$, the metric density satisfies $\lambda_g^2(\zeta(x))=|F'(\zeta(x))|^2/\operatorname{Im}(F(x))^2$.
proof:
  This is the pullback identity recorded for the local formula at $x$.
-/
theorem densitySq_eq (F : UpperHalfPlanePullbackFormula X g) {x : X} (hx : x ∈ F.domain) :
    g.toConformalMetric.densitySqInChart F.chart F.chart_mem_atlas
        (F.regularity.coordinate x) =
      F.derivativeNormSq x / ((F.toUpperHalfPlane x : ℂ).im ^ 2) :=
  F.densitySqInChart_eq_pullback x hx

/--
%%handwave
name:
  Positivity of the derivative scale in a pullback formula
statement:
  For a locally biholomorphic map $F:D\to\mathbb H$ appearing in an upper-half-plane pullback formula, $|F'(\zeta(x))|^2>0$ for every $x\in D$.
proof:
  The local formula records positivity of its derivative norm-square on the domain.
-/
theorem derivativeNormSq_positive (F : UpperHalfPlanePullbackFormula X g)
    {x : X} (hx : x ∈ F.domain) : 0 < F.derivativeNormSq x :=
  F.derivativeNormSq_pos x hx

/-- The local chart obtained from a pullback formula carries the same density identity.

%%handwave
name:
  An upper-half-plane pullback formula defines a local isometry
statement:
  The local upper-half-plane chart associated with a pullback formula $F:D\to\mathbb H$ satisfies $F^*g_{\mathbb H}=g$ on $D$.
proof:
  Its local-isometry structure uses exactly the density pullback identity of the original formula.
-/
theorem toHyperbolicLocalChart_pulls_back_metric_on_domain
    (F : UpperHalfPlanePullbackFormula X g) :
    F.toHyperbolicLocalChart.pulls_back_metric_on_domain :=
  F.toHyperbolicLocalChart.local_isometry.pulls_back_metric_on_domain

end UpperHalfPlanePullbackFormula

/--
Regularity certificate for a coordinate-level upper-half-plane pullback formula.
-/
def CoordinateUpperHalfPlaneMapHolomorphicOn
    (coordinateDomain : Set ℂ) (localMap : ℂ → ℍ) : Prop :=
  ∀ z, z ∈ coordinateDomain →
    DifferentiableAt ℂ (fun w : ℂ ↦ (localMap w : ℂ)) z

/-- Nonvanishing of the complex derivative of a coordinate upper-half-plane map. -/
def CoordinateUpperHalfPlaneMapDerivativeNonzeroOn
    (coordinateDomain : Set ℂ) (localMap : ℂ → ℍ) : Prop :=
  ∀ z, z ∈ coordinateDomain →
    deriv (fun w : ℂ ↦ (localMap w : ℂ)) z ≠ 0

structure CoordinateUpperHalfPlanePullbackFormulaRegularity
    (_coordinateDomain : Set ℂ) (_localMap : ℂ → ℍ) where
  /-- The coordinate local map is holomorphic on the coordinate domain. -/
  holomorphic_on_coordinateDomain :
    CoordinateUpperHalfPlaneMapHolomorphicOn _coordinateDomain _localMap
  /-- The coordinate local map has nonzero complex derivative on the coordinate domain. -/
  local_biholomorph_on_domain :
    CoordinateUpperHalfPlaneMapDerivativeNonzeroOn _coordinateDomain _localMap

/--
A coordinate-level Poincare pullback formula.

Here the squared derivative norm is no longer an abstract field: it is
`Complex.normSq (deriv f z)` in the chosen complex coordinate.  This is the
version we should use when proving local formulas in explicit charts.
-/
structure CoordinateUpperHalfPlanePullbackFormula (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] (g : HyperbolicMetric X) where
  /-- The surface domain on which the formula is asserted. -/
  domain : Set X
  /-- The surface domain is open. -/
  isOpen_domain : IsOpen domain
  /-- The coordinate domain in `ℂ`. -/
  coordinateDomain : Set ℂ
  /-- The coordinate domain is open. -/
  isOpen_coordinateDomain : IsOpen coordinateDomain
  /-- The local complex coordinate. -/
  coordinate : X → ℂ
  /-- The chart in which the coordinate formula is written. -/
  chart : OpenPartialHomeomorph X ℂ
  /-- The chosen chart belongs to the complex atlas. -/
  chart_mem_atlas : chart ∈ atlas ℂ X
  /-- The formula domain lies in the source of the chosen chart. -/
  domain_subset_chart_source : domain ⊆ chart.source
  /-- The stored coordinate agrees with the chosen chart on the formula domain. -/
  coordinate_eq_chart : Set.EqOn coordinate chart domain
  /-- Points in `domain` are sent into the coordinate domain. -/
  coordinate_mem_domain : ∀ x, x ∈ domain → coordinate x ∈ coordinateDomain
  /-- The local map to the upper half-plane in the chosen coordinate. -/
  localMap : ℂ → ℍ
  /-- Holomorphicity and local-biholomorphism data for the coordinate map. -/
  regularity : CoordinateUpperHalfPlanePullbackFormulaRegularity coordinateDomain localMap
  /-- The complex derivative is nonzero on the coordinate domain over `domain`. -/
  derivative_ne_zero_on_domain :
    ∀ x, x ∈ domain → deriv (fun z : ℂ ↦ (localMap z : ℂ)) (coordinate x) ≠ 0
  /-- Poincare pullback squared-density formula in the chosen coordinate. -/
  densitySqInChart_eq_pullback :
    ∀ x, x ∈ domain →
      g.toConformalMetric.densitySqInChart chart chart_mem_atlas (coordinate x) =
        complexDerivativeNormSq localMap (coordinate x) /
          ((localMap (coordinate x) : ℂ).im ^ 2)
namespace CoordinateUpperHalfPlanePullbackFormula

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/-- The actual local map to `ℍ` on the surface domain. -/
def toUpperHalfPlane (F : CoordinateUpperHalfPlanePullbackFormula X g) : X → ℍ :=
  fun x ↦ F.localMap (F.coordinate x)

/-- The coordinate local map is holomorphic on the coordinate domain. -/
def holomorphic_on_coordinateDomain (F : CoordinateUpperHalfPlanePullbackFormula X g) :
    CoordinateUpperHalfPlaneMapHolomorphicOn F.coordinateDomain F.localMap :=
  F.regularity.holomorphic_on_coordinateDomain

/-- The coordinate local map has nonzero derivative on the coordinate domain. -/
def local_biholomorph_on_domain (F : CoordinateUpperHalfPlanePullbackFormula X g) :
    CoordinateUpperHalfPlaneMapDerivativeNonzeroOn F.coordinateDomain F.localMap :=
  F.regularity.local_biholomorph_on_domain

/--
%%handwave
name:
  Positive derivative norm for a coordinate pullback map
statement:
  If $F$ is a coordinate upper-half-plane pullback map and $x$ lies in its surface domain, then $|F'(\zeta(x))|^2>0$.
proof:
  The derivative $F'(\zeta(x))$ is nonzero by local biholomorphicity, so its norm-square is positive.
-/
theorem derivativeNormSq_pos (F : CoordinateUpperHalfPlanePullbackFormula X g)
    {x : X} (hx : x ∈ F.domain) :
    0 < complexDerivativeNormSq F.localMap (F.coordinate x) := by
  exact Complex.normSq_pos.mpr (F.derivative_ne_zero_on_domain x hx)

/--
%%handwave
name:
  Coordinate density formula for a Poincaré pullback
statement:
  For every $x$ in the domain of a coordinate map $F:D\to\mathbb H$, one has $\lambda_g^2(\zeta(x))=|F'(\zeta(x))|^2/\operatorname{Im}(F(\zeta(x)))^2$.
proof:
  This is the defining coordinate pullback identity at $x$.
-/
theorem densitySqInChart_eq
    (F : CoordinateUpperHalfPlanePullbackFormula X g) {x : X} (hx : x ∈ F.domain) :
    g.toConformalMetric.densitySqInChart F.chart F.chart_mem_atlas (F.coordinate x) =
      complexDerivativeNormSq F.localMap (F.coordinate x) /
        ((F.localMap (F.coordinate x) : ℂ).im ^ 2) :=
  F.densitySqInChart_eq_pullback x hx

/-- Forget the chosen coordinate, retaining the abstract pullback-formula package. -/
def toUpperHalfPlanePullbackFormula (F : CoordinateUpperHalfPlanePullbackFormula X g) :
    UpperHalfPlanePullbackFormula X g where
  domain := F.domain
  isOpen_domain := F.isOpen_domain
  toUpperHalfPlane := F.toUpperHalfPlane
  regularity := {
    coordinateDomain := F.coordinateDomain
    isOpen_coordinateDomain := F.isOpen_coordinateDomain
    coordinate := F.coordinate
    coordinate_mem_domain := F.coordinate_mem_domain
    localMap := F.localMap
    toUpperHalfPlane_eq := by
      intro x hx
      rfl
    holomorphic_on_domain :=
      F.holomorphic_on_coordinateDomain
    local_biholomorph_on_domain :=
      F.derivative_ne_zero_on_domain }
  chart := F.chart
  chart_mem_atlas := F.chart_mem_atlas
  domain_subset_chart_source := F.domain_subset_chart_source
  coordinate_eq_chart := F.coordinate_eq_chart
  derivativeNormSq := fun x ↦ complexDerivativeNormSq F.localMap (F.coordinate x)
  derivativeNormSq_eq_coordinate := fun x hx ↦ rfl
  derivativeNormSq_pos := fun _ hx ↦ F.derivativeNormSq_pos hx
  densitySqInChart_eq_pullback := F.densitySqInChart_eq_pullback

/--
%%handwave
name:
  The underlying map of the abstract pullback formula
statement:
  Passing from a coordinate upper-half-plane pullback formula to its surface-level pullback formula leaves the map $D\to\mathbb H$ unchanged.
proof:
  The surface-level formula is defined using the same upper-half-plane map.
-/
@[simp]
theorem toUpperHalfPlanePullbackFormula_toUpperHalfPlane
    (F : CoordinateUpperHalfPlanePullbackFormula X g) :
    F.toUpperHalfPlanePullbackFormula.toUpperHalfPlane = F.toUpperHalfPlane :=
  rfl

end CoordinateUpperHalfPlanePullbackFormula

/--
A local Liouville formula for the metric alone.

This is the curvature-to-PDE layer without a developing map: in the chosen
coordinate, the metric squared density is `exp (2u)` and `u` solves the
Liouville equation.
-/
structure LocalLiouvilleMetricFormula (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] (g : HyperbolicMetric X) where
  /-- The surface domain on which the coordinate formula is asserted. -/
  domain : Set X
  /-- The surface domain is open. -/
  isOpen_domain : IsOpen domain
  /-- The local complex coordinate. -/
  coordinate : X → ℂ
  /-- The chart in which the coordinate formula is written. -/
  chart : OpenPartialHomeomorph X ℂ
  /-- The chosen chart belongs to the complex atlas. -/
  chart_mem_atlas : chart ∈ atlas ℂ X
  /-- The formula domain lies in the source of the chosen chart. -/
  domain_subset_chart_source : domain ⊆ chart.source
  /-- The stored coordinate agrees with the chosen chart on the formula domain. -/
  coordinate_eq_chart : Set.EqOn coordinate chart domain
  /-- The local logarithmic conformal factor in the coordinate. -/
  conformalFactor : LocalConformalFactor
  /-- Points in `domain` are sent into the conformal factor's coordinate domain. -/
  coordinate_mem_conformalFactor_domain :
    ∀ x, x ∈ domain → coordinate x ∈ conformalFactor.coordinateDomain
  /-- The logarithmic factor solves the Liouville equation. -/
  solves_liouville : conformalFactor.SolvesLiouvilleEquation
  /-- The metric squared density is `exp (2u)` in this coordinate. -/
  densitySqInChart_eq_conformalFactor :
    ∀ x, x ∈ domain →
      g.toConformalMetric.densitySqInChart chart chart_mem_atlas (coordinate x) =
        conformalFactor.densitySq (coordinate x)
namespace LocalLiouvilleMetricFormula

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/--
%%handwave
name:
  Metric density represented by a local conformal factor
statement:
  If a metric is locally represented by $e^{2u}|dz|^2$, then at every $x$ in the surface domain its chart density satisfies $\lambda_g^2(\zeta(x))=e^{2u(\zeta(x))}$.
proof:
  This is the density agreement required of the local metric formula.
-/
theorem densitySqInChart_eq
    (F : LocalLiouvilleMetricFormula X g) {x : X} (hx : x ∈ F.domain) :
    g.toConformalMetric.densitySqInChart F.chart F.chart_mem_atlas (F.coordinate x) =
      F.conformalFactor.densitySq (F.coordinate x) :=
  F.densitySqInChart_eq_conformalFactor x hx

/--
%%handwave
name:
  Local metric density as an exponential
statement:
  For a local Liouville metric formula and every $x$ in its surface domain, $\lambda_g^2(\zeta(x))=\exp(2u(\zeta(x)))$.
proof:
  Substitute the definition of the squared density $e^{2u}$ into the recorded density agreement.
-/
theorem densitySq_eq_exp_logDensity
    (F : LocalLiouvilleMetricFormula X g) {x : X} (hx : x ∈ F.domain) :
    g.toConformalMetric.densitySqInChart F.chart F.chart_mem_atlas (F.coordinate x) =
      Real.exp (2 * F.conformalFactor.logDensity (F.coordinate x)) := by
  simpa [LocalConformalFactor.densitySq] using F.densitySqInChart_eq hx

/--
%%handwave
name:
  The Liouville equation at a surface coordinate
statement:
  If $u$ is the logarithmic density of a local Liouville metric formula, then for every $x$ in its surface domain, $\Delta u(\zeta(x))=e^{2u(\zeta(x))}$.
proof:
  The coordinate $\zeta(x)$ belongs to the conformal-factor domain, so evaluate the recorded Liouville equation there.
-/
theorem liouville_at_coordinate
    (F : LocalLiouvilleMetricFormula X g) {x : X} (hx : x ∈ F.domain) :
    Laplacian.laplacian F.conformalFactor.logDensity (F.coordinate x) =
      Real.exp (2 * F.conformalFactor.logDensity (F.coordinate x)) :=
  F.solves_liouville (F.coordinate x)
    (F.coordinate_mem_conformalFactor_domain x hx)

/--
Restrict a local Liouville metric formula to points whose coordinate lies in a
smaller open coordinate domain.

The openness of the restricted surface domain is supplied explicitly, since the
lightweight formula structure currently records only a bare coordinate map, not
continuity or chart-local homeomorphism data.
-/
def restrictCoordinateDomain
    (F : LocalLiouvilleMetricFormula X g) (V : Set ℂ) (hVOpen : IsOpen V)
    (hV : V ⊆ F.conformalFactor.coordinateDomain)
    (hDomainOpen : IsOpen {x : X | x ∈ F.domain ∧ F.coordinate x ∈ V}) :
    LocalLiouvilleMetricFormula X g where
  domain := {x : X | x ∈ F.domain ∧ F.coordinate x ∈ V}
  isOpen_domain := hDomainOpen
  coordinate := F.coordinate
  chart := F.chart
  chart_mem_atlas := F.chart_mem_atlas
  domain_subset_chart_source := by
    intro x hx
    exact F.domain_subset_chart_source hx.1
  coordinate_eq_chart := by
    intro x hx
    exact F.coordinate_eq_chart hx.1
  conformalFactor := F.conformalFactor.restrict V hVOpen hV
  coordinate_mem_conformalFactor_domain := by
    intro x hx
    exact hx.2
  solves_liouville :=
    F.conformalFactor.restrict_solvesLiouvilleEquation V hVOpen hV
      F.solves_liouville
  densitySqInChart_eq_conformalFactor := by
    intro x hx
    simpa [LocalConformalFactor.restrict_densitySq]
      using F.densitySqInChart_eq_conformalFactor x hx.1

/--
%%handwave
name:
  Surface domain after restricting the coordinate domain
statement:
  Restricting a local Liouville formula to $V$ in coordinates gives the surface domain $\{x\in D:\zeta(x)\in V\}$.
proof:
  This set is the domain used in the definition of the restricted formula.
-/
@[simp]
theorem restrictCoordinateDomain_domain
    (F : LocalLiouvilleMetricFormula X g) (V : Set ℂ) (hVOpen : IsOpen V)
    (hV : V ⊆ F.conformalFactor.coordinateDomain)
    (hDomainOpen : IsOpen {x : X | x ∈ F.domain ∧ F.coordinate x ∈ V}) :
    (F.restrictCoordinateDomain V hVOpen hV hDomainOpen).domain =
      {x : X | x ∈ F.domain ∧ F.coordinate x ∈ V} :=
  rfl

/--
%%handwave
name:
  Coordinate map after restricting a Liouville formula
statement:
  Restricting the coordinate domain of a local Liouville metric formula leaves its surface coordinate map $\zeta$ unchanged.
proof:
  The restricted formula is defined with the original coordinate map.
-/
@[simp]
theorem restrictCoordinateDomain_coordinate
    (F : LocalLiouvilleMetricFormula X g) (V : Set ℂ) (hVOpen : IsOpen V)
    (hV : V ⊆ F.conformalFactor.coordinateDomain)
    (hDomainOpen : IsOpen {x : X | x ∈ F.domain ∧ F.coordinate x ∈ V}) :
    (F.restrictCoordinateDomain V hVOpen hV hDomainOpen).coordinate =
      F.coordinate :=
  rfl

/--
%%handwave
name:
  Conformal factor after coordinate restriction
statement:
  Restricting a local Liouville metric formula to $V$ replaces its conformal factor on $\Omega$ by the same logarithmic density restricted to $V$.
proof:
  This restricted conformal factor is used directly in the definition.
-/
@[simp]
theorem restrictCoordinateDomain_conformalFactor
    (F : LocalLiouvilleMetricFormula X g) (V : Set ℂ) (hVOpen : IsOpen V)
    (hV : V ⊆ F.conformalFactor.coordinateDomain)
    (hDomainOpen : IsOpen {x : X | x ∈ F.domain ∧ F.coordinate x ∈ V}) :
    (F.restrictCoordinateDomain V hVOpen hV hDomainOpen).conformalFactor =
      F.conformalFactor.restrict V hVOpen hV :=
  rfl

/--
Restrict the surface domain of a local Liouville metric formula to points whose
coordinate lies in a chosen coordinate subset, while keeping the ambient
coordinate conformal factor unchanged.

This is useful when a subsequent construction, such as a local Schwarzian
branch, is defined only on a smaller coordinate neighborhood but still uses the
same Schwarzian data for the original conformal factor.
-/
def restrictDomainToCoordinateSubset
    (F : LocalLiouvilleMetricFormula X g) (V : Set ℂ)
    (hV : V ⊆ F.conformalFactor.coordinateDomain)
    (hDomainOpen : IsOpen {x : X | x ∈ F.domain ∧ F.coordinate x ∈ V}) :
    LocalLiouvilleMetricFormula X g where
  domain := {x : X | x ∈ F.domain ∧ F.coordinate x ∈ V}
  isOpen_domain := hDomainOpen
  coordinate := F.coordinate
  chart := F.chart
  chart_mem_atlas := F.chart_mem_atlas
  domain_subset_chart_source := by
    intro x hx
    exact F.domain_subset_chart_source hx.1
  coordinate_eq_chart := by
    intro x hx
    exact F.coordinate_eq_chart hx.1
  conformalFactor := F.conformalFactor
  coordinate_mem_conformalFactor_domain := by
    intro x hx
    exact hV hx.2
  solves_liouville := F.solves_liouville
  densitySqInChart_eq_conformalFactor := by
    intro x hx
    exact F.densitySqInChart_eq_conformalFactor x hx.1

/--
%%handwave
name:
  Surface domain selected by a coordinate subset
statement:
  Selecting the points whose coordinates lie in $V$ changes the surface domain of a local Liouville formula to $\{x\in D:\zeta(x)\in V\}$.
proof:
  The selected formula is defined on exactly this set.
-/
@[simp]
theorem restrictDomainToCoordinateSubset_domain
    (F : LocalLiouvilleMetricFormula X g) (V : Set ℂ)
    (hV : V ⊆ F.conformalFactor.coordinateDomain)
    (hDomainOpen : IsOpen {x : X | x ∈ F.domain ∧ F.coordinate x ∈ V}) :
    (F.restrictDomainToCoordinateSubset V hV hDomainOpen).domain =
      {x : X | x ∈ F.domain ∧ F.coordinate x ∈ V} :=
  rfl

/--
%%handwave
name:
  Coordinate map under surface-domain selection
statement:
  Restricting a local Liouville formula to the surface points with $\zeta(x)\in V$ leaves the coordinate map $\zeta$ unchanged.
proof:
  Only the certified surface domain is changed.
-/
@[simp]
theorem restrictDomainToCoordinateSubset_coordinate
    (F : LocalLiouvilleMetricFormula X g) (V : Set ℂ)
    (hV : V ⊆ F.conformalFactor.coordinateDomain)
    (hDomainOpen : IsOpen {x : X | x ∈ F.domain ∧ F.coordinate x ∈ V}) :
    (F.restrictDomainToCoordinateSubset V hV hDomainOpen).coordinate =
      F.coordinate :=
  rfl

/--
%%handwave
name:
  Conformal factor under surface-domain selection
statement:
  Restricting the surface domain of a local Liouville formula to points with coordinates in $V$ leaves its conformal factor unchanged.
proof:
  The construction changes the surface domain but retains the original conformal factor.
-/
@[simp]
theorem restrictDomainToCoordinateSubset_conformalFactor
    (F : LocalLiouvilleMetricFormula X g) (V : Set ℂ)
    (hV : V ⊆ F.conformalFactor.coordinateDomain)
    (hDomainOpen : IsOpen {x : X | x ∈ F.domain ∧ F.coordinate x ∈ V}) :
    (F.restrictDomainToCoordinateSubset V hV hDomainOpen).conformalFactor =
      F.conformalFactor :=
  rfl

end LocalLiouvilleMetricFormula

/--
A local curvature formula for the metric before rewriting it as Liouville's
equation.

The conformal factor is required to have Gaussian curvature `-1` according to
the local formula `K = -exp (-2u) Δu`; the conversion to a Liouville formula is
then a proved algebraic consequence.
-/
structure LocalCurvatureMetricFormula (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] (g : HyperbolicMetric X) where
  /-- The surface domain on which the coordinate formula is asserted. -/
  domain : Set X
  /-- The surface domain is open. -/
  isOpen_domain : IsOpen domain
  /-- The local complex coordinate. -/
  coordinate : X → ℂ
  /-- The chart in which the coordinate formula is written. -/
  chart : OpenPartialHomeomorph X ℂ
  /-- The chosen chart belongs to the complex atlas. -/
  chart_mem_atlas : chart ∈ atlas ℂ X
  /-- The formula domain lies in the source of the chosen chart. -/
  domain_subset_chart_source : domain ⊆ chart.source
  /-- The stored coordinate agrees with the chosen chart on the formula domain. -/
  coordinate_eq_chart : Set.EqOn coordinate chart domain
  /-- The local logarithmic conformal factor in the coordinate. -/
  conformalFactor : LocalConformalFactor
  /-- Points in `domain` are sent into the conformal factor's coordinate domain. -/
  coordinate_mem_conformalFactor_domain :
    ∀ x, x ∈ domain → coordinate x ∈ conformalFactor.coordinateDomain
  /-- The local conformal factor has Gaussian curvature `-1`. -/
  curvature_minus_one : conformalFactor.HasGaussianCurvatureMinusOne
  /-- The metric squared density is `exp (2u)` in this coordinate. -/
  densitySqInChart_eq_conformalFactor :
    ∀ x, x ∈ domain →
      g.toConformalMetric.densitySqInChart chart chart_mem_atlas (coordinate x) =
        conformalFactor.densitySq (coordinate x)
namespace LocalCurvatureMetricFormula

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/-- The curvature formula implies the corresponding Liouville metric formula. -/
def toLocalLiouvilleMetricFormula
    (F : LocalCurvatureMetricFormula X g) :
    LocalLiouvilleMetricFormula X g where
  domain := F.domain
  isOpen_domain := F.isOpen_domain
  coordinate := F.coordinate
  chart := F.chart
  chart_mem_atlas := F.chart_mem_atlas
  domain_subset_chart_source := F.domain_subset_chart_source
  coordinate_eq_chart := F.coordinate_eq_chart
  conformalFactor := F.conformalFactor
  coordinate_mem_conformalFactor_domain := F.coordinate_mem_conformalFactor_domain
  solves_liouville :=
    F.conformalFactor.solvesLiouvilleEquation_of_hasGaussianCurvatureMinusOne
      F.curvature_minus_one
  densitySqInChart_eq_conformalFactor := F.densitySqInChart_eq_conformalFactor

/--
%%handwave
name:
  A curvature-derived conformal factor solves the Liouville equation
statement:
  If a local conformal metric $e^{2u}|dz|^2$ has curvature $-1$, then its logarithmic density satisfies $\Delta u=e^{2u}$ throughout its coordinate domain.
proof:
  Rearrange the curvature equation $-e^{-2u}\Delta u=-1$.
-/
theorem solves_liouville
    (F : LocalCurvatureMetricFormula X g) :
    F.conformalFactor.SolvesLiouvilleEquation :=
  F.conformalFactor.solvesLiouvilleEquation_of_hasGaussianCurvatureMinusOne
    F.curvature_minus_one

/--
%%handwave
name:
  Curvature yields the Liouville equation at surface points
statement:
  For every $x$ in the domain of a local curvature formula, its logarithmic density satisfies $\Delta u(\zeta(x))=e^{2u(\zeta(x))}$.
proof:
  The coordinate $\zeta(x)$ lies in the conformal-factor domain; evaluate the Liouville equation obtained from curvature there.
-/
theorem liouville_at_coordinate
    (F : LocalCurvatureMetricFormula X g) {x : X} (hx : x ∈ F.domain) :
    Laplacian.laplacian F.conformalFactor.logDensity (F.coordinate x) =
      Real.exp (2 * F.conformalFactor.logDensity (F.coordinate x)) :=
  F.solves_liouville (F.coordinate x)
    (F.coordinate_mem_conformalFactor_domain x hx)

/--
%%handwave
name:
  Density agreement in a local curvature formula
statement:
  At every $x$ in the domain of a local curvature formula, the metric density in the chosen chart is $\lambda_g^2(\zeta(x))=e^{2u(\zeta(x))}$.
proof:
  This is the density agreement recorded by the local curvature formula.
-/
theorem densitySqInChart_eq
    (F : LocalCurvatureMetricFormula X g) {x : X} (hx : x ∈ F.domain) :
    g.toConformalMetric.densitySqInChart F.chart F.chart_mem_atlas (F.coordinate x) =
      F.conformalFactor.densitySq (F.coordinate x) :=
  F.densitySqInChart_eq_conformalFactor x hx

end LocalCurvatureMetricFormula

/--
A local solution package for the hyperbolic developing-map equation.

It combines:

* a coordinate-level Poincare pullback formula;
* a logarithmic conformal factor `u`;
* the Liouville equation `Δ u = exp (2u)`;
* the assertion that the metric's squared density is `exp (2u)` in the chosen
  coordinate.

This is the local object we expect to construct from the curvature `-1`
condition before assembling an atlas.
-/
structure LocalLiouvilleDevelopingSolution (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] (g : HyperbolicMetric X) where
  /-- The coordinate-level Poincare pullback formula. -/
  pullbackFormula : CoordinateUpperHalfPlanePullbackFormula X g
  /-- The local logarithmic conformal factor. -/
  conformalFactor : LocalConformalFactor
  /-- The coordinate domains agree with the formula's coordinate domain. -/
  coordinateDomain_eq :
    conformalFactor.coordinateDomain = pullbackFormula.coordinateDomain
  /-- The chart in which the metric conformal factor is written. -/
  chart : OpenPartialHomeomorph X ℂ
  /-- The chosen chart belongs to the complex atlas. -/
  chart_mem_atlas : chart ∈ atlas ℂ X
  /-- The solution domain lies in the source of the chosen chart. -/
  domain_subset_chart_source : pullbackFormula.domain ⊆ chart.source
  /-- The pullback coordinate agrees with the chosen chart on the solution domain. -/
  coordinate_eq_chart : Set.EqOn pullbackFormula.coordinate chart pullbackFormula.domain
  /-- The logarithmic factor solves the Liouville equation. -/
  solves_liouville : conformalFactor.SolvesLiouvilleEquation
  /-- The metric squared density is `exp (2u)` in this coordinate. -/
  densitySqInChart_eq_conformalFactor :
    ∀ x, x ∈ pullbackFormula.domain →
      g.toConformalMetric.densitySqInChart chart chart_mem_atlas (pullbackFormula.coordinate x) =
        conformalFactor.densitySq (pullbackFormula.coordinate x)
  /-- The coordinate pullback formula rewritten in the solution chart. -/
  densitySqInChart_eq_pullback :
    ∀ x, x ∈ pullbackFormula.domain →
      g.toConformalMetric.densitySqInChart chart chart_mem_atlas (pullbackFormula.coordinate x) =
        complexDerivativeNormSq pullbackFormula.localMap (pullbackFormula.coordinate x) /
          ((pullbackFormula.localMap (pullbackFormula.coordinate x) : ℂ).im ^ 2)
namespace LocalLiouvilleDevelopingSolution

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/-- Forget the Liouville provenance and keep the coordinate pullback formula. -/
def toCoordinateUpperHalfPlanePullbackFormula
    (S : LocalLiouvilleDevelopingSolution X g) :
    CoordinateUpperHalfPlanePullbackFormula X g :=
  S.pullbackFormula

/-- Forget all formula data and keep the underlying local hyperbolic chart. -/
def toHyperbolicLocalChart (S : LocalLiouvilleDevelopingSolution X g) :
    HyperbolicLocalChart X g :=
  S.pullbackFormula.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart

/-- Forget the developing map and keep the local Liouville formula for the metric. -/
def toLocalLiouvilleMetricFormula
    (S : LocalLiouvilleDevelopingSolution X g) :
    LocalLiouvilleMetricFormula X g where
  domain := S.pullbackFormula.domain
  isOpen_domain := S.pullbackFormula.isOpen_domain
  coordinate := S.pullbackFormula.coordinate
  chart := S.chart
  chart_mem_atlas := S.chart_mem_atlas
  domain_subset_chart_source := S.domain_subset_chart_source
  coordinate_eq_chart := S.coordinate_eq_chart
  conformalFactor := S.conformalFactor
  coordinate_mem_conformalFactor_domain := by
    intro x hx
    rw [S.coordinateDomain_eq]
    exact S.pullbackFormula.coordinate_mem_domain x hx
  solves_liouville := S.solves_liouville
  densitySqInChart_eq_conformalFactor := S.densitySqInChart_eq_conformalFactor

/--
%%handwave
name:
  Surface coordinates lie in the conformal-factor domain
statement:
  For a local Liouville developing solution and every $x$ in its surface domain, the coordinate $\zeta(x)$ lies in the domain $\Omega$ of its conformal factor.
proof:
  The solution identifies the conformal-factor domain with the coordinate domain of its pullback formula, which contains $\zeta(x)$.
-/
theorem coordinate_mem_conformalFactor_domain
    (S : LocalLiouvilleDevelopingSolution X g) {x : X}
    (hx : x ∈ S.pullbackFormula.domain) :
    S.pullbackFormula.coordinate x ∈ S.conformalFactor.coordinateDomain := by
  rw [S.coordinateDomain_eq]
  exact S.pullbackFormula.coordinate_mem_domain x hx

/--
%%handwave
name:
  The Liouville equation along a local developing solution
statement:
  If $u$ is the logarithmic density in a local Liouville developing solution, then for every surface point $x$ in its domain, $\Delta u(\zeta(x))=e^{2u(\zeta(x))}$.
proof:
  The coordinate $\zeta(x)$ belongs to the conformal-factor domain, so evaluate the recorded Liouville equation there.
-/
theorem liouville_at_coordinate
    (S : LocalLiouvilleDevelopingSolution X g) {x : X}
    (hx : x ∈ S.pullbackFormula.domain) :
    Laplacian.laplacian S.conformalFactor.logDensity (S.pullbackFormula.coordinate x) =
      Real.exp (2 * S.conformalFactor.logDensity (S.pullbackFormula.coordinate x)) :=
  S.solves_liouville (S.pullbackFormula.coordinate x)
    (S.coordinate_mem_conformalFactor_domain hx)

/--
The local conformal factor equals the Poincare pullback squared density in the
chosen coordinate.

%%handwave
name:
  The conformal density equals the Poincaré pullback density
statement:
  For a local Liouville developing solution $F$ and every $x$ in its domain, $e^{2u(\zeta(x))}=|F'(\zeta(x))|^2/\operatorname{Im}(F(\zeta(x)))^2$.
proof:
  Both sides equal the density of $g$ in the same chart: the first by the conformal-factor formula and the second by the Poincaré pullback formula.
-/
theorem conformalFactor_densitySq_eq_pullback
  (S : LocalLiouvilleDevelopingSolution X g) {x : X}
    (hx : x ∈ S.pullbackFormula.domain) :
    S.conformalFactor.densitySq (S.pullbackFormula.coordinate x) =
      complexDerivativeNormSq S.pullbackFormula.localMap (S.pullbackFormula.coordinate x) /
        ((S.pullbackFormula.localMap (S.pullbackFormula.coordinate x) : ℂ).im ^ 2) :=
  (S.densitySqInChart_eq_conformalFactor x hx).symm.trans
    (S.densitySqInChart_eq_pullback x hx)

/--
Expanded form of `conformalFactor_densitySq_eq_pullback`, using
`densitySq = exp (2u)`.

%%handwave
name:
  Exponential Liouville density as a developing-map pullback
statement:
  For a local Liouville developing solution $F$, $\exp(2u(\zeta(x)))=|F'(\zeta(x))|^2/\operatorname{Im}(F(\zeta(x)))^2$ at every $x$ in its domain.
proof:
  Substitute the definition $\lambda^2=e^{2u}$ into the equality between the conformal density and the Poincaré pullback density.
-/
theorem exp_logDensity_eq_pullback
    (S : LocalLiouvilleDevelopingSolution X g) {x : X}
    (hx : x ∈ S.pullbackFormula.domain) :
    Real.exp (2 * S.conformalFactor.logDensity (S.pullbackFormula.coordinate x)) =
      complexDerivativeNormSq S.pullbackFormula.localMap (S.pullbackFormula.coordinate x) /
        ((S.pullbackFormula.localMap (S.pullbackFormula.coordinate x) : ℂ).im ^ 2) := by
  simpa [LocalConformalFactor.densitySq]
    using S.conformalFactor_densitySq_eq_pullback hx

/--
At a local developing solution, the Liouville equation identifies the Laplacian
of the logarithmic density with the Poincare pullback expression.

%%handwave
name:
  Laplacian of the logarithmic density as a Poincaré pullback
statement:
  For a local Liouville developing solution $F$, $\Delta u(\zeta(x))=|F'(\zeta(x))|^2/\operatorname{Im}(F(\zeta(x)))^2$ at every $x$ in its domain.
proof:
  The Liouville equation gives $\Delta u=e^{2u}$, and the developing-map pullback formula identifies $e^{2u}$ with the displayed quotient.
-/
theorem laplacian_logDensity_eq_pullback
    (S : LocalLiouvilleDevelopingSolution X g) {x : X}
    (hx : x ∈ S.pullbackFormula.domain) :
    Laplacian.laplacian S.conformalFactor.logDensity (S.pullbackFormula.coordinate x) =
      complexDerivativeNormSq S.pullbackFormula.localMap (S.pullbackFormula.coordinate x) /
        ((S.pullbackFormula.localMap (S.pullbackFormula.coordinate x) : ℂ).im ^ 2) :=
  (S.liouville_at_coordinate hx).trans (S.exp_logDensity_eq_pullback hx)

end LocalLiouvilleDevelopingSolution

/--
A local construction of a Liouville developing solution.

This is the named bridge between the metric-only Liouville formula and an
actual coordinate map to the upper half-plane.  The fields assert that the
metric formula and the Poincare pullback formula use the same local coordinate
data.
-/
structure LocalLiouvilleDevelopingConstruction (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] (g : HyperbolicMetric X) where
  /-- The metric-only Liouville formula. -/
  metricFormula : LocalLiouvilleMetricFormula X g
  /-- The coordinate-level Poincare pullback formula. -/
  pullbackFormula : CoordinateUpperHalfPlanePullbackFormula X g
  /-- The two formulas are asserted on the same surface domain. -/
  same_domain : pullbackFormula.domain = metricFormula.domain
  /-- The two formulas use the same local coordinate. -/
  same_coordinate : pullbackFormula.coordinate = metricFormula.coordinate
  /-- The conformal factor is written on the pullback formula's coordinate domain. -/
  same_coordinateDomain :
    metricFormula.conformalFactor.coordinateDomain = pullbackFormula.coordinateDomain
  /-- The pullback formula rewritten in the metric formula's chart. -/
  densitySqInMetricChart_eq_pullback :
    ∀ x, x ∈ pullbackFormula.domain →
      g.toConformalMetric.densitySqInChart metricFormula.chart metricFormula.chart_mem_atlas
          (metricFormula.coordinate x) =
        complexDerivativeNormSq pullbackFormula.localMap (metricFormula.coordinate x) /
          ((pullbackFormula.localMap (metricFormula.coordinate x) : ℂ).im ^ 2)

namespace LocalLiouvilleDevelopingConstruction

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/-- Assemble the aligned metric and pullback formulas into a local developing solution. -/
def toLocalLiouvilleDevelopingSolution
    (C : LocalLiouvilleDevelopingConstruction X g) :
    LocalLiouvilleDevelopingSolution X g where
  pullbackFormula := C.pullbackFormula
  conformalFactor := C.metricFormula.conformalFactor
  coordinateDomain_eq := C.same_coordinateDomain
  chart := C.metricFormula.chart
  chart_mem_atlas := C.metricFormula.chart_mem_atlas
  domain_subset_chart_source := by
    intro x hx
    exact C.metricFormula.domain_subset_chart_source (by
      rw [← C.same_domain]
      exact hx)
  coordinate_eq_chart := by
    intro x hx
    rw [C.same_coordinate]
    exact C.metricFormula.coordinate_eq_chart (by
      rw [← C.same_domain]
      exact hx)
  solves_liouville := C.metricFormula.solves_liouville
  densitySqInChart_eq_conformalFactor := by
    intro x hx
    rw [C.same_coordinate]
    exact C.metricFormula.densitySqInChart_eq_conformalFactor x (by
      rw [← C.same_domain]
      exact hx)
  densitySqInChart_eq_pullback := by
    intro x hx
    rw [C.same_coordinate]
    exact C.densitySqInMetricChart_eq_pullback x hx

/--
%%handwave
name:
  Pullback formula of a completed local Liouville solution
statement:
  The local Liouville developing solution obtained from an aligned metric-and-map construction uses exactly the original upper-half-plane pullback formula.
proof:
  The solution is defined with that pullback formula unchanged.
-/
@[simp]
theorem toLocalLiouvilleDevelopingSolution_pullbackFormula
    (C : LocalLiouvilleDevelopingConstruction X g) :
    C.toLocalLiouvilleDevelopingSolution.pullbackFormula = C.pullbackFormula :=
  rfl

/--
%%handwave
name:
  Conformal factor of a completed local Liouville solution
statement:
  The local Liouville developing solution obtained from an aligned construction uses the conformal factor of the original local metric formula.
proof:
  This conformal factor is retained in the definition of the solution.
-/
@[simp]
theorem toLocalLiouvilleDevelopingSolution_conformalFactor
    (C : LocalLiouvilleDevelopingConstruction X g) :
    C.toLocalLiouvilleDevelopingSolution.conformalFactor =
      C.metricFormula.conformalFactor :=
  rfl

/-- In a construction, membership in the pullback-formula domain gives membership in the metric domain.

%%handwave
name:
  Pullback-domain points lie in the metric-formula domain
statement:
  In an aligned local Liouville developing construction, every point in the domain of the upper-half-plane pullback formula lies in the domain of the local metric formula.
proof:
  The construction records equality of the two surface domains.
-/
theorem mem_metricFormula_domain
    (C : LocalLiouvilleDevelopingConstruction X g) {x : X}
    (hx : x ∈ C.pullbackFormula.domain) :
    x ∈ C.metricFormula.domain := by
  rw [← C.same_domain]
  exact hx

/-- In a construction, membership in the metric domain gives membership in the pullback domain.

%%handwave
name:
  Metric-formula points lie in the pullback domain
statement:
  In an aligned local Liouville developing construction, every point in the domain of the local metric formula lies in the domain of the upper-half-plane pullback formula.
proof:
  Rewrite using the recorded equality of the two surface domains.
-/
theorem mem_pullbackFormula_domain
    (C : LocalLiouvilleDevelopingConstruction X g) {x : X}
    (hx : x ∈ C.metricFormula.domain) :
    x ∈ C.pullbackFormula.domain := by
  rw [C.same_domain]
  exact hx

/--
The metric conformal factor of an aligned construction equals the Poincare
pullback squared density of its local map.

%%handwave
name:
  Aligned metric and developing formulas have the same density
statement:
  For every point $x$ in an aligned local construction, $e^{2u(\zeta(x))}=|F'(\zeta(x))|^2/\operatorname{Im}(F(\zeta(x)))^2$.
proof:
  The conformal density and Poincaré pullback quotient both equal the chart density of $g$; the construction identifies the two coordinate maps.
-/
theorem conformalFactor_densitySq_eq_pullback
    (C : LocalLiouvilleDevelopingConstruction X g) {x : X}
    (hx : x ∈ C.pullbackFormula.domain) :
    C.metricFormula.conformalFactor.densitySq (C.metricFormula.coordinate x) =
      complexDerivativeNormSq C.pullbackFormula.localMap (C.pullbackFormula.coordinate x) /
        ((C.pullbackFormula.localMap (C.pullbackFormula.coordinate x) : ℂ).im ^ 2) := by
  rw [C.same_coordinate]
  exact (C.metricFormula.densitySqInChart_eq_conformalFactor x
    (C.mem_metricFormula_domain hx)).symm.trans
    (C.densitySqInMetricChart_eq_pullback x hx)

/-- Expanded `exp (2u)` version of `conformalFactor_densitySq_eq_pullback`.

%%handwave
name:
  Exponential density identity in an aligned construction
statement:
  For every point $x$ in an aligned local construction, $\exp(2u(\zeta(x)))=|F'(\zeta(x))|^2/\operatorname{Im}(F(\zeta(x)))^2$.
proof:
  Replace the conformal squared density in the density-matching identity by its definition $e^{2u}$.
-/
theorem exp_logDensity_eq_pullback
    (C : LocalLiouvilleDevelopingConstruction X g) {x : X}
    (hx : x ∈ C.pullbackFormula.domain) :
    Real.exp (2 * C.metricFormula.conformalFactor.logDensity (C.metricFormula.coordinate x)) =
      complexDerivativeNormSq C.pullbackFormula.localMap (C.pullbackFormula.coordinate x) /
        ((C.pullbackFormula.localMap (C.pullbackFormula.coordinate x) : ℂ).im ^ 2) := by
  simpa [LocalConformalFactor.densitySq]
    using C.conformalFactor_densitySq_eq_pullback hx

/--
The Liouville equation in an aligned construction identifies the Laplacian of
the metric logarithmic density with the Poincare pullback expression.

%%handwave
name:
  Liouville Laplacian identity in an aligned construction
statement:
  For every point $x$ in an aligned local construction, $\Delta u(\zeta(x))=|F'(\zeta(x))|^2/\operatorname{Im}(F(\zeta(x)))^2$.
proof:
  The local metric formula gives $\Delta u=e^{2u}$, and the aligned pullback identity gives the displayed expression for $e^{2u}$.
-/
theorem laplacian_logDensity_eq_pullback
    (C : LocalLiouvilleDevelopingConstruction X g) {x : X}
    (hx : x ∈ C.pullbackFormula.domain) :
    Laplacian.laplacian C.metricFormula.conformalFactor.logDensity
        (C.metricFormula.coordinate x) =
      complexDerivativeNormSq C.pullbackFormula.localMap (C.pullbackFormula.coordinate x) /
        ((C.pullbackFormula.localMap (C.pullbackFormula.coordinate x) : ℂ).im ^ 2) :=
  (C.metricFormula.liouville_at_coordinate (C.mem_metricFormula_domain hx)).trans
    (C.exp_logDensity_eq_pullback hx)

end LocalLiouvilleDevelopingConstruction

/--
An atlas of explicit Poincare pullback formulas for a hyperbolic metric.

This is a sharpened version of `HyperbolicLocalModelAtlas`: each chart carries
the squared-density formula that says it is a local isometry to `ℍ`.
-/
structure UpperHalfPlanePullbackFormulaAtlas (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] (g : HyperbolicMetric X) where
  /-- A chosen local formula near each point. -/
  formulaAt : X → UpperHalfPlanePullbackFormula X g
  /-- The chosen formula at `x` is defined at `x`. -/
  mem_formulaAt_domain : ∀ x, x ∈ (formulaAt x).domain
  /-- The underlying local charts have real-Mobius transitions. -/
  transition_realMobius :
    ∀ x y,
      ((formulaAt x).toHyperbolicLocalChart).HasRealMobiusTransition
        ((formulaAt y).toHyperbolicLocalChart)

namespace UpperHalfPlanePullbackFormulaAtlas

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/-- The formula chosen near `x`. -/
def formulaNear (A : UpperHalfPlanePullbackFormulaAtlas X g) (x : X) :
    UpperHalfPlanePullbackFormula X g :=
  A.formulaAt x

/--
%%handwave
name:
  A point lies in its selected abstract pullback domain
statement:
  For every $x\in X$, the upper-half-plane pullback formula selected near $x$ is defined at $x$.
proof:
  This is the centering condition of the pullback-formula atlas.
-/
theorem mem_formulaNear_domain (A : UpperHalfPlanePullbackFormulaAtlas X g) (x : X) :
    x ∈ (A.formulaNear x).domain :=
  A.mem_formulaAt_domain x

/-- The domains of the chosen local formulas cover the surface.

%%handwave
name:
  Abstract pullback-formula domains cover the surface
statement:
  The union of the domains of all selected upper-half-plane pullback formulas is $X$.
proof:
  Each $x\in X$ belongs to the domain of the formula selected near $x$.
-/
theorem domain_cover (A : UpperHalfPlanePullbackFormulaAtlas X g) :
    (⋃ x : X, (A.formulaNear x).domain) = Set.univ := by
  ext y
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    exact Set.mem_iUnion.mpr ⟨y, A.mem_formulaNear_domain y⟩

/-- Forget explicit density formulas and keep the local-model atlas. -/
def toHyperbolicLocalModelAtlas (A : UpperHalfPlanePullbackFormulaAtlas X g) :
    HyperbolicLocalModelAtlas X g where
  chartAt x := (A.formulaAt x).toHyperbolicLocalChart
  mem_chartAt_domain := A.mem_formulaAt_domain
  transition_realMobius := A.transition_realMobius

end UpperHalfPlanePullbackFormulaAtlas

/--
An atlas of coordinate-level Poincare pullback formulas.

This is the version closest to concrete Riemann-surface charts: every local
formula carries a coordinate map into `ℂ`, a local map from that coordinate
domain to `ℍ`, and the squared derivative term `Complex.normSq (deriv f z)`.
-/
structure CoordinateUpperHalfPlanePullbackFormulaAtlas (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] (g : HyperbolicMetric X) where
  /-- A chosen coordinate-level formula near each point. -/
  formulaAt : X → CoordinateUpperHalfPlanePullbackFormula X g
  /-- The chosen coordinate-level formula at `x` is defined at `x`. -/
  mem_formulaAt_domain : ∀ x, x ∈ (formulaAt x).domain
  /-- The underlying local charts have real-Mobius transitions. -/
  transition_realMobius :
    ∀ x y,
      ((formulaAt x).toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart).HasRealMobiusTransition
        ((formulaAt y).toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart)

namespace CoordinateUpperHalfPlanePullbackFormulaAtlas

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/-- The coordinate-level formula chosen near `x`. -/
def formulaNear (A : CoordinateUpperHalfPlanePullbackFormulaAtlas X g) (x : X) :
    CoordinateUpperHalfPlanePullbackFormula X g :=
  A.formulaAt x

/--
%%handwave
name:
  A point lies in its selected coordinate pullback domain
statement:
  For every $x\in X$, the coordinate upper-half-plane pullback formula selected near $x$ is defined at $x$.
proof:
  This is the centering condition required of the coordinate pullback atlas.
-/
theorem mem_formulaNear_domain (A : CoordinateUpperHalfPlanePullbackFormulaAtlas X g) (x : X) :
    x ∈ (A.formulaNear x).domain :=
  A.mem_formulaAt_domain x

/-- The domains of the chosen coordinate-level formulas cover the surface.

%%handwave
name:
  Coordinate pullback-formula domains cover the surface
statement:
  The union of the domains of all selected coordinate upper-half-plane pullback formulas is $X$.
proof:
  The formula selected at each $x$ contains $x$ in its domain.
-/
theorem domain_cover (A : CoordinateUpperHalfPlanePullbackFormulaAtlas X g) :
    (⋃ x : X, (A.formulaNear x).domain) = Set.univ := by
  ext y
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    exact Set.mem_iUnion.mpr ⟨y, A.mem_formulaNear_domain y⟩

/-- Forget coordinate-level data and keep only the abstract pullback-formula atlas. -/
def toUpperHalfPlanePullbackFormulaAtlas
    (A : CoordinateUpperHalfPlanePullbackFormulaAtlas X g) :
    UpperHalfPlanePullbackFormulaAtlas X g where
  formulaAt x := (A.formulaAt x).toUpperHalfPlanePullbackFormula
  mem_formulaAt_domain := A.mem_formulaAt_domain
  transition_realMobius := A.transition_realMobius

end CoordinateUpperHalfPlanePullbackFormulaAtlas

/--
An atlas of local Liouville formulas for the metric.

This is the local curvature formula layer before solving for maps to the upper
half-plane.
-/
structure LocalLiouvilleMetricFormulaAtlas (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] (g : HyperbolicMetric X) where
  /-- A chosen local Liouville metric formula near each point. -/
  formulaAt : X → LocalLiouvilleMetricFormula X g
  /-- The chosen formula at `x` is defined at `x`. -/
  mem_formulaAt_domain : ∀ x, x ∈ (formulaAt x).domain

namespace LocalLiouvilleMetricFormulaAtlas

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/-- The local Liouville metric formula chosen near `x`. -/
def formulaNear (A : LocalLiouvilleMetricFormulaAtlas X g) (x : X) :
    LocalLiouvilleMetricFormula X g :=
  A.formulaAt x

/--
%%handwave
name:
  A point lies in its selected Liouville metric-formula domain
statement:
  For every $x\in X$, the local Liouville metric formula selected near $x$ is defined at $x$.
proof:
  This is the centering property of the local metric-formula atlas.
-/
theorem mem_formulaNear_domain (A : LocalLiouvilleMetricFormulaAtlas X g) (x : X) :
    x ∈ (A.formulaNear x).domain :=
  A.mem_formulaAt_domain x

/-- The domains of the chosen local Liouville metric formulas cover the surface.

%%handwave
name:
  Local Liouville metric-formula domains cover the surface
statement:
  The union of the domains of the selected local Liouville metric formulas is $X$.
proof:
  Every point is contained in the domain of the formula selected at that point.
-/
theorem domain_cover (A : LocalLiouvilleMetricFormulaAtlas X g) :
    (⋃ x : X, (A.formulaNear x).domain) = Set.univ := by
  ext y
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    exact Set.mem_iUnion.mpr ⟨y, A.mem_formulaNear_domain y⟩

end LocalLiouvilleMetricFormulaAtlas

/--
An atlas of local curvature formulas before rewriting them as Liouville
formulas.
-/
structure LocalCurvatureMetricFormulaAtlas (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] (g : HyperbolicMetric X) where
  /-- A chosen local curvature formula near each point. -/
  formulaAt : X → LocalCurvatureMetricFormula X g
  /-- The chosen formula at `x` is defined at `x`. -/
  mem_formulaAt_domain : ∀ x, x ∈ (formulaAt x).domain

namespace LocalCurvatureMetricFormulaAtlas

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/-- The local curvature formula chosen near `x`. -/
def formulaNear (A : LocalCurvatureMetricFormulaAtlas X g) (x : X) :
    LocalCurvatureMetricFormula X g :=
  A.formulaAt x

/--
%%handwave
name:
  A point lies in its selected curvature-formula domain
statement:
  For every $x\in X$, the local curvature metric formula selected near $x$ is defined at $x$.
proof:
  This is the centering property of the curvature-formula atlas.
-/
theorem mem_formulaNear_domain (A : LocalCurvatureMetricFormulaAtlas X g) (x : X) :
    x ∈ (A.formulaNear x).domain :=
  A.mem_formulaAt_domain x

/-- The domains of the chosen local curvature formulas cover the surface.

%%handwave
name:
  Local curvature-formula domains cover the surface
statement:
  The union of the domains of the selected local curvature metric formulas is $X$.
proof:
  Each point lies in the domain of its selected local curvature formula.
-/
theorem domain_cover (A : LocalCurvatureMetricFormulaAtlas X g) :
    (⋃ x : X, (A.formulaNear x).domain) = Set.univ := by
  ext y
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    exact Set.mem_iUnion.mpr ⟨y, A.mem_formulaNear_domain y⟩

/-- Rewrite every local curvature formula as a local Liouville metric formula. -/
def toLocalLiouvilleMetricFormulaAtlas
    (A : LocalCurvatureMetricFormulaAtlas X g) :
    LocalLiouvilleMetricFormulaAtlas X g where
  formulaAt x := (A.formulaAt x).toLocalLiouvilleMetricFormula
  mem_formulaAt_domain := A.mem_formulaAt_domain

end LocalCurvatureMetricFormulaAtlas

/--
Curvature-to-Liouville local formula package.

This is the formal target for expanding the symbolic curvature predicate in
`HyperbolicMetric` into local logarithmic conformal factors satisfying
`Δ u = exp (2u)`.
-/
structure CurvatureLiouvilleFormulaAtlas (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] (g : HyperbolicMetric X) where
  /-- The local Liouville metric formulas produced from the curvature equation. -/
  metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g
  /-- The construction uses the `K = -1` field of the hyperbolic metric. -/
  derived_from_curvature_minus_one : g.toConformalMetric.HasCurvatureMinusOne
  /-- The construction uses smoothness of the metric density in charts. -/
  uses_smooth_density : g.toConformalMetric.IsSmooth

namespace CurvatureLiouvilleFormulaAtlas

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/-- Forget curvature provenance and keep the metric-formula atlas. -/
def toLocalLiouvilleMetricFormulaAtlas
    (A : CurvatureLiouvilleFormulaAtlas X g) :
    LocalLiouvilleMetricFormulaAtlas X g :=
  A.metricFormulaAtlas

/-- The local Liouville metric formula chosen near `x`. -/
def formulaNear (A : CurvatureLiouvilleFormulaAtlas X g) (x : X) :
    LocalLiouvilleMetricFormula X g :=
  A.metricFormulaAtlas.formulaNear x

/--
%%handwave
name:
  A point lies in its curvature-derived Liouville formula domain
statement:
  For every $x\in X$, the curvature-derived local Liouville formula selected near $x$ is defined at $x$.
proof:
  The underlying metric-formula atlas contains $x$ in the domain of its selected formula.
-/
theorem mem_formulaNear_domain (A : CurvatureLiouvilleFormulaAtlas X g) (x : X) :
    x ∈ (A.formulaNear x).domain :=
  A.metricFormulaAtlas.mem_formulaNear_domain x

/-- The domains of the curvature-derived local formulas cover the surface.

%%handwave
name:
  Curvature-derived Liouville formula domains cover the surface
statement:
  The union of the domains of all curvature-derived local Liouville formulas is $X$.
proof:
  This is the covering identity of the underlying local metric-formula atlas.
-/
theorem domain_cover (A : CurvatureLiouvilleFormulaAtlas X g) :
    (⋃ x : X, (A.formulaNear x).domain) = Set.univ :=
  A.metricFormulaAtlas.domain_cover

end CurvatureLiouvilleFormulaAtlas

/--
An atlas of local Liouville developing solutions.

This is the strongest local package currently recorded: each point gets a
coordinate-level developing formula together with the local Liouville equation
for the metric's logarithmic conformal factor.
-/
structure LocalLiouvilleDevelopingSolutionAtlas (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] (g : HyperbolicMetric X) where
  /-- A chosen local Liouville developing solution near each point. -/
  solutionAt : X → LocalLiouvilleDevelopingSolution X g
  /-- The chosen solution at `x` is defined at `x`. -/
  mem_solutionAt_domain : ∀ x, x ∈ (solutionAt x).pullbackFormula.domain
  /-- The underlying local charts have real-Mobius transitions. -/
  transition_realMobius :
    ∀ x y,
      ((solutionAt x).toHyperbolicLocalChart).HasRealMobiusTransition
        ((solutionAt y).toHyperbolicLocalChart)

namespace LocalLiouvilleDevelopingSolutionAtlas

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/-- The local Liouville developing solution chosen near `x`. -/
def solutionNear (A : LocalLiouvilleDevelopingSolutionAtlas X g) (x : X) :
    LocalLiouvilleDevelopingSolution X g :=
  A.solutionAt x

/--
%%handwave
name:
  A point lies in its selected local developing-solution domain
statement:
  For every $x\in X$, the local Liouville developing solution selected near $x$ is defined at $x$.
proof:
  This is the centering condition of the developing-solution atlas.
-/
theorem mem_solutionNear_domain (A : LocalLiouvilleDevelopingSolutionAtlas X g) (x : X) :
    x ∈ (A.solutionNear x).pullbackFormula.domain :=
  A.mem_solutionAt_domain x

/-- The domains of the chosen local Liouville solutions cover the surface.

%%handwave
name:
  Local Liouville developing-solution domains cover the surface
statement:
  The union of the domains of the selected local Liouville developing solutions is $X$.
proof:
  Each point belongs to the domain of the solution selected at that point.
-/
theorem domain_cover (A : LocalLiouvilleDevelopingSolutionAtlas X g) :
    (⋃ x : X, (A.solutionNear x).pullbackFormula.domain) = Set.univ := by
  ext y
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    exact Set.mem_iUnion.mpr ⟨y, A.mem_solutionNear_domain y⟩

/-- Forget developing maps and keep the local Liouville metric-formula atlas. -/
def toLocalLiouvilleMetricFormulaAtlas
    (A : LocalLiouvilleDevelopingSolutionAtlas X g) :
    LocalLiouvilleMetricFormulaAtlas X g where
  formulaAt x := (A.solutionAt x).toLocalLiouvilleMetricFormula
  mem_formulaAt_domain := A.mem_solutionAt_domain

/-- Forget Liouville provenance and keep the coordinate pullback-formula atlas. -/
def toCoordinateUpperHalfPlanePullbackFormulaAtlas
    (A : LocalLiouvilleDevelopingSolutionAtlas X g) :
    CoordinateUpperHalfPlanePullbackFormulaAtlas X g where
  formulaAt x := (A.solutionAt x).toCoordinateUpperHalfPlanePullbackFormula
  mem_formulaAt_domain := A.mem_solutionAt_domain
  transition_realMobius := A.transition_realMobius

/-- Forget Liouville provenance and keep the local-model atlas. -/
def toHyperbolicLocalModelAtlas (A : LocalLiouvilleDevelopingSolutionAtlas X g) :
    HyperbolicLocalModelAtlas X g :=
  A.toCoordinateUpperHalfPlanePullbackFormulaAtlas
    |>.toUpperHalfPlanePullbackFormulaAtlas
    |>.toHyperbolicLocalModelAtlas

end LocalLiouvilleDevelopingSolutionAtlas

/--
An atlas of local constructions of Liouville developing solutions.

This is the explicit target for the step that solves the local Liouville metric
formula by maps to the upper half-plane, before forgetting to the final local
developing-solution atlas.
-/
structure LocalLiouvilleDevelopingConstructionAtlas (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] (g : HyperbolicMetric X) where
  /-- A chosen aligned local construction near each point. -/
  constructionAt : X → LocalLiouvilleDevelopingConstruction X g
  /-- The chosen construction at `x` is defined at `x`. -/
  mem_constructionAt_domain :
    ∀ x, x ∈ (constructionAt x).pullbackFormula.domain
  /-- The resulting local charts have real-Mobius transitions. -/
  transition_realMobius :
    ∀ x y,
      HyperbolicLocalChart.HasRealMobiusTransition
        (((constructionAt x).toLocalLiouvilleDevelopingSolution).toHyperbolicLocalChart)
        (((constructionAt y).toLocalLiouvilleDevelopingSolution).toHyperbolicLocalChart)

namespace LocalLiouvilleDevelopingConstructionAtlas

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

/-- The aligned local construction chosen near `x`. -/
def constructionNear (A : LocalLiouvilleDevelopingConstructionAtlas X g) (x : X) :
    LocalLiouvilleDevelopingConstruction X g :=
  A.constructionAt x

/--
%%handwave
name:
  A point lies in its selected local developing-construction domain
statement:
  For every $x\in X$, the aligned local Liouville developing construction selected near $x$ is defined at $x$.
proof:
  This is the centering condition of the construction atlas.
-/
theorem mem_constructionNear_domain
    (A : LocalLiouvilleDevelopingConstructionAtlas X g) (x : X) :
    x ∈ (A.constructionNear x).pullbackFormula.domain :=
  A.mem_constructionAt_domain x

/-- The domains of the chosen local developing constructions cover the surface.

%%handwave
name:
  Local Liouville developing-construction domains cover the surface
statement:
  The union of the domains of the selected aligned local Liouville developing constructions is $X$.
proof:
  Every point lies in the domain of the construction selected at that point.
-/
theorem domain_cover (A : LocalLiouvilleDevelopingConstructionAtlas X g) :
    (⋃ x : X, (A.constructionNear x).pullbackFormula.domain) = Set.univ := by
  ext y
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    exact Set.mem_iUnion.mpr ⟨y, A.mem_constructionNear_domain y⟩

/-- Forget aligned constructions and keep only the local Liouville metric formulas. -/
def toLocalLiouvilleMetricFormulaAtlas
    (A : LocalLiouvilleDevelopingConstructionAtlas X g) :
    LocalLiouvilleMetricFormulaAtlas X g where
  formulaAt x := (A.constructionAt x).metricFormula
  mem_formulaAt_domain := fun x ↦
    (A.constructionAt x).mem_metricFormula_domain (A.mem_constructionAt_domain x)

/-- Forget aligned constructions and keep only the coordinate pullback formulas. -/
def toCoordinateUpperHalfPlanePullbackFormulaAtlas
    (A : LocalLiouvilleDevelopingConstructionAtlas X g) :
    CoordinateUpperHalfPlanePullbackFormulaAtlas X g where
  formulaAt x := (A.constructionAt x).pullbackFormula
  mem_formulaAt_domain := A.mem_constructionAt_domain
  transition_realMobius := A.transition_realMobius

/-- Forget the aligned-construction provenance and keep local developing solutions. -/
def toLocalLiouvilleDevelopingSolutionAtlas
    (A : LocalLiouvilleDevelopingConstructionAtlas X g) :
    LocalLiouvilleDevelopingSolutionAtlas X g where
  solutionAt x := (A.constructionAt x).toLocalLiouvilleDevelopingSolution
  mem_solutionAt_domain := A.mem_constructionAt_domain
  transition_realMobius := A.transition_realMobius

end LocalLiouvilleDevelopingConstructionAtlas

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/--
Target formula theorem: a hyperbolic metric admits local Poincare-pullback
formulas.
-/
def HasUpperHalfPlanePullbackFormulaAtlas (g : HyperbolicMetric X) : Prop :=
  Nonempty (UpperHalfPlanePullbackFormulaAtlas X g)

/--
Target coordinate-formula theorem: a hyperbolic metric admits local
Poincare-pullback formulas in actual complex coordinates.
-/
def HasCoordinateUpperHalfPlanePullbackFormulaAtlas (g : HyperbolicMetric X) : Prop :=
  Nonempty (CoordinateUpperHalfPlanePullbackFormulaAtlas X g)

/--
Target local curvature-formula theorem: a hyperbolic metric admits local
logarithmic conformal factors satisfying the curvature expression `K = -1`.
-/
def HasLocalCurvatureMetricFormulaAtlas (g : HyperbolicMetric X) : Prop :=
  Nonempty (LocalCurvatureMetricFormulaAtlas X g)

/--
Target curvature-formula theorem: a hyperbolic metric admits local logarithmic
conformal factors satisfying the Liouville equation.
-/
def HasLocalLiouvilleMetricFormulaAtlas (g : HyperbolicMetric X) : Prop :=
  Nonempty (LocalLiouvilleMetricFormulaAtlas X g)

/--
Target curvature-expansion theorem: the local Liouville metric formulas are
obtained by expanding the curvature `-1` predicate.
-/
def HasCurvatureLiouvilleFormulaAtlas (g : HyperbolicMetric X) : Prop :=
  Nonempty (CurvatureLiouvilleFormulaAtlas X g)

/--
Target local solving theorem: the local Liouville metric formulas are solved by
aligned maps to the upper half-plane.
-/
def HasLocalLiouvilleDevelopingConstructionAtlas (g : HyperbolicMetric X) : Prop :=
  Nonempty (LocalLiouvilleDevelopingConstructionAtlas X g)

/--
Target local theorem with curvature provenance: curvature-derived Liouville
formulas have been solved by aligned upper-half-plane maps.
-/
structure HasCurvatureLiouvilleDevelopingConstructionAtlas
    (g : HyperbolicMetric X) where
  /-- Curvature has been expanded into local Liouville metric formulas. -/
  curvatureFormulaAtlas : CurvatureLiouvilleFormulaAtlas X g
  /-- Those formulas have been solved by aligned local maps to `ℍ`. -/
  developingConstructionAtlas : LocalLiouvilleDevelopingConstructionAtlas X g
  /-- The developing constructions solve the curvature-derived metric formulas. -/
  constructions_solve_curvature_formulas :
    developingConstructionAtlas.toLocalLiouvilleMetricFormulaAtlas =
      curvatureFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas

/--
Target local PDE theorem: a hyperbolic metric admits local Liouville developing
solutions.
-/
def HasLocalLiouvilleDevelopingSolutionAtlas (g : HyperbolicMetric X) : Prop :=
  Nonempty (LocalLiouvilleDevelopingSolutionAtlas X g)

/--
%%handwave
name:
  Solved curvature formulas include curvature-derived Liouville formulas
statement:
  If a hyperbolic metric has local curvature-derived Liouville formulas together with aligned local developing maps solving them, then it has an atlas of curvature-derived Liouville formulas.
proof:
  Retain the curvature-derived formula atlas from the assumed solved data.
-/
theorem hasCurvatureLiouvilleFormulaAtlas_of_hasCurvatureLiouvilleDevelopingConstructionAtlas
    {g : HyperbolicMetric X} (h : g.HasCurvatureLiouvilleDevelopingConstructionAtlas) :
    g.HasCurvatureLiouvilleFormulaAtlas :=
  ⟨h.curvatureFormulaAtlas⟩

/--
%%handwave
name:
  Solved curvature formulas include aligned local developing constructions
statement:
  If a hyperbolic metric has curvature-derived Liouville formulas equipped with aligned local upper-half-plane solutions, then it has an atlas of aligned local Liouville developing constructions.
proof:
  Retain the atlas of aligned local developing constructions.
-/
theorem hasLocalLiouvilleDevelopingConstructionAtlas_of_hasCurvatureLiouvilleDevelopingConstructionAtlas
    {g : HyperbolicMetric X} (h : g.HasCurvatureLiouvilleDevelopingConstructionAtlas) :
    g.HasLocalLiouvilleDevelopingConstructionAtlas :=
  ⟨h.developingConstructionAtlas⟩

/--
%%handwave
name:
  Curvature-derived Liouville formulas yield local Liouville metric formulas
statement:
  If a hyperbolic metric has an atlas obtained by expanding curvature $-1$ into $\Delta u=e^{2u}$, then it has an atlas of local metric formulas $g=e^{2u}|dz|^2$ satisfying the Liouville equation.
proof:
  Forget the curvature provenance and retain the underlying local Liouville metric formulas.
-/
theorem hasLocalLiouvilleMetricFormulaAtlas_of_hasCurvatureLiouvilleFormulaAtlas
    {g : HyperbolicMetric X} (h : g.HasCurvatureLiouvilleFormulaAtlas) :
    g.HasLocalLiouvilleMetricFormulaAtlas :=
  h.elim fun A ↦ ⟨A.toLocalLiouvilleMetricFormulaAtlas⟩

/--
%%handwave
name:
  Local curvature formulas yield local Liouville metric formulas
statement:
  If $g$ has local conformal formulas $e^{2u}|dz|^2$ with curvature $-1$, then it has local Liouville metric formulas satisfying $\Delta u=e^{2u}$.
proof:
  For each local curvature formula, derive the Liouville equation from $-e^{-2u}\Delta u=-1$ and retain the same chart and density formula.
-/
theorem hasLocalLiouvilleMetricFormulaAtlas_of_hasLocalCurvatureMetricFormulaAtlas
    {g : HyperbolicMetric X} (h : g.HasLocalCurvatureMetricFormulaAtlas) :
    g.HasLocalLiouvilleMetricFormulaAtlas :=
  h.elim fun A ↦ ⟨A.toLocalLiouvilleMetricFormulaAtlas⟩

/--
Once curvature has been expanded into the local expression
`K = -exp (-2u) Δu`, the Liouville formula atlas follows by algebra.
-/
def curvatureLiouvilleFormulaAtlas_of_localCurvatureMetricFormulaAtlas
    {g : HyperbolicMetric X} (A : LocalCurvatureMetricFormulaAtlas X g) :
    CurvatureLiouvilleFormulaAtlas X g where
  metricFormulaAtlas := A.toLocalLiouvilleMetricFormulaAtlas
  derived_from_curvature_minus_one := g.curvature_minus_one
  uses_smooth_density := g.smooth

/--
%%handwave
name:
  Local curvature formulas assemble into a curvature-derived Liouville atlas
statement:
  If $g$ has an atlas of local conformal formulas with curvature $-1$, then it has an atlas of local formulas $g=e^{2u}|dz|^2$ in which $\Delta u=e^{2u}$ is explicitly derived from curvature.
proof:
  Keep the same local formulas, derive the Liouville equation algebraically from curvature $-1$, and retain the smoothness and curvature provenance of $g$.
-/
theorem hasCurvatureLiouvilleFormulaAtlas_of_hasLocalCurvatureMetricFormulaAtlas
    {g : HyperbolicMetric X} (h : g.HasLocalCurvatureMetricFormulaAtlas) :
    g.HasCurvatureLiouvilleFormulaAtlas :=
  h.elim fun A ↦
    ⟨curvatureLiouvilleFormulaAtlas_of_localCurvatureMetricFormulaAtlas A⟩

/--
%%handwave
name:
  Aligned local constructions yield local Liouville developing solutions
statement:
  If $g$ has aligned local metric formulas and upper-half-plane pullback maps on matching domains and coordinates, then $g$ has an atlas of local maps $F$ satisfying both $\Delta u=e^{2u}$ and $e^{2u}=|F'|^2/(\operatorname{Im}F)^2$.
proof:
  Combine each aligned pair into the corresponding local Liouville developing solution.
-/
theorem hasLocalLiouvilleDevelopingSolutionAtlas_of_hasLocalLiouvilleDevelopingConstructionAtlas
    {g : HyperbolicMetric X} (h : g.HasLocalLiouvilleDevelopingConstructionAtlas) :
    g.HasLocalLiouvilleDevelopingSolutionAtlas :=
  h.elim fun A ↦ ⟨A.toLocalLiouvilleDevelopingSolutionAtlas⟩

/--
%%handwave
name:
  Aligned local developing constructions retain their metric formulas
statement:
  If $g$ has an atlas of aligned local Liouville metric formulas and upper-half-plane maps, then $g$ has an atlas of local Liouville metric formulas.
proof:
  Retain the local metric formula from each aligned construction.
-/
theorem hasLocalLiouvilleMetricFormulaAtlas_of_hasLocalLiouvilleDevelopingConstructionAtlas
    {g : HyperbolicMetric X} (h : g.HasLocalLiouvilleDevelopingConstructionAtlas) :
    g.HasLocalLiouvilleMetricFormulaAtlas :=
  h.elim fun A ↦ ⟨A.toLocalLiouvilleMetricFormulaAtlas⟩

/--
%%handwave
name:
  Solved curvature-derived formulas yield local Liouville metric formulas
statement:
  If the curvature-derived local Liouville formulas of $g$ have aligned upper-half-plane solutions, then $g$ has an atlas of local formulas $g=e^{2u}|dz|^2$ satisfying $\Delta u=e^{2u}$.
proof:
  Retain the aligned local developing constructions, then retain their local metric formulas.
-/
theorem hasLocalLiouvilleMetricFormulaAtlas_of_hasCurvatureLiouvilleDevelopingConstructionAtlas
    {g : HyperbolicMetric X} (h : g.HasCurvatureLiouvilleDevelopingConstructionAtlas) :
    g.HasLocalLiouvilleMetricFormulaAtlas :=
  hasLocalLiouvilleMetricFormulaAtlas_of_hasLocalLiouvilleDevelopingConstructionAtlas
    (hasLocalLiouvilleDevelopingConstructionAtlas_of_hasCurvatureLiouvilleDevelopingConstructionAtlas h)

/--
%%handwave
name:
  Local Liouville developing solutions determine local metric formulas
statement:
  If $g$ has local developing maps $F$ whose pullback density agrees with a Liouville factor $e^{2u}$, then $g$ has an atlas of local metric formulas $g=e^{2u}|dz|^2$ satisfying $\Delta u=e^{2u}$.
proof:
  Retain the conformal factor, chart, coordinate, density identity, and Liouville equation from each local solution.
-/
theorem hasLocalLiouvilleMetricFormulaAtlas_of_hasLocalLiouvilleDevelopingSolutionAtlas
    {g : HyperbolicMetric X} (h : g.HasLocalLiouvilleDevelopingSolutionAtlas) :
    g.HasLocalLiouvilleMetricFormulaAtlas :=
  h.elim fun A ↦ ⟨A.toLocalLiouvilleMetricFormulaAtlas⟩

/--
%%handwave
name:
  Local Liouville developing solutions give coordinate Poincaré pullback formulas
statement:
  If $g$ has local Liouville developing solutions, then it has local coordinate maps $F$ to $\mathbb H$ satisfying $\lambda_g^2=|F'|^2/(\operatorname{Im}F)^2$ with nonvanishing derivative.
proof:
  Retain the coordinate upper-half-plane pullback formula from each local solution.
-/
theorem hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasLocalLiouvilleDevelopingSolutionAtlas
    {g : HyperbolicMetric X} (h : g.HasLocalLiouvilleDevelopingSolutionAtlas) :
    g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas :=
  h.elim fun A ↦ ⟨A.toCoordinateUpperHalfPlanePullbackFormulaAtlas⟩

/--
%%handwave
name:
  Aligned local constructions give coordinate Poincaré pullback formulas
statement:
  If $g$ has aligned local Liouville metric formulas and upper-half-plane maps, then it has an atlas of coordinate maps $F$ satisfying $\lambda_g^2=|F'|^2/(\operatorname{Im}F)^2$.
proof:
  Retain the coordinate pullback formula from each aligned local construction.
-/
theorem hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasLocalLiouvilleDevelopingConstructionAtlas
    {g : HyperbolicMetric X} (h : g.HasLocalLiouvilleDevelopingConstructionAtlas) :
    g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas :=
  h.elim fun A ↦ ⟨A.toCoordinateUpperHalfPlanePullbackFormulaAtlas⟩

/--
%%handwave
name:
  Solved curvature-derived formulas give coordinate Poincaré pullbacks
statement:
  If the curvature-derived local Liouville formulas of $g$ have aligned upper-half-plane solutions, then $g$ has local coordinate maps $F$ with $\lambda_g^2=|F'|^2/(\operatorname{Im}F)^2$.
proof:
  Retain the atlas of aligned local constructions and then their coordinate pullback formulas.
-/
theorem hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasCurvatureLiouvilleDevelopingConstructionAtlas
    {g : HyperbolicMetric X} (h : g.HasCurvatureLiouvilleDevelopingConstructionAtlas) :
    g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas :=
  hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasLocalLiouvilleDevelopingConstructionAtlas
    (hasLocalLiouvilleDevelopingConstructionAtlas_of_hasCurvatureLiouvilleDevelopingConstructionAtlas h)

/--
%%handwave
name:
  Coordinate Poincaré pullback formulas yield surface-level pullback formulas
statement:
  If $g$ is locally expressed by coordinate maps $F$ with $\lambda_g^2=|F'|^2/(\operatorname{Im}F)^2$, then it has local surface maps to $\mathbb H$ satisfying the same Poincaré pullback identity.
proof:
  Compose each coordinate formula with its surface coordinate and retain its regularity and density identity.
-/
theorem hasUpperHalfPlanePullbackFormulaAtlas_of_hasCoordinateUpperHalfPlanePullbackFormulaAtlas
    {g : HyperbolicMetric X} (h : g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas) :
    g.HasUpperHalfPlanePullbackFormulaAtlas :=
  h.elim fun A ↦ ⟨A.toUpperHalfPlanePullbackFormulaAtlas⟩

/--
%%handwave
name:
  Poincaré pullback formulas define local hyperbolic models
statement:
  If $g$ has local maps $F:D\to\mathbb H$ that are holomorphic local biholomorphisms and satisfy $F^*g_{\mathbb H}=g$ on $D$, then $g$ admits an atlas of local upper-half-plane isometries with real Möbius transitions.
proof:
  Convert each pullback formula into its associated local hyperbolic chart and retain the recorded transition maps.
-/
theorem hasUpperHalfPlaneLocalModels_of_hasUpperHalfPlanePullbackFormulaAtlas
    {g : HyperbolicMetric X} (h : g.HasUpperHalfPlanePullbackFormulaAtlas) :
    g.HasUpperHalfPlaneLocalModels :=
  h.elim fun A ↦ ⟨A.toHyperbolicLocalModelAtlas⟩

/--
%%handwave
name:
  Coordinate Poincaré pullbacks define local upper-half-plane models
statement:
  If $g$ has local coordinate maps $F$ with nonzero derivative and $\lambda_g^2=|F'|^2/(\operatorname{Im}F)^2$, together with real Möbius overlaps, then $g$ has local upper-half-plane isometry charts.
proof:
  Turn the coordinate formulas into surface-level Poincaré pullback formulas and then into local hyperbolic charts.
-/
theorem hasUpperHalfPlaneLocalModels_of_hasCoordinateUpperHalfPlanePullbackFormulaAtlas
    {g : HyperbolicMetric X} (h : g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas) :
    g.HasUpperHalfPlaneLocalModels :=
  hasUpperHalfPlaneLocalModels_of_hasUpperHalfPlanePullbackFormulaAtlas
    (hasUpperHalfPlanePullbackFormulaAtlas_of_hasCoordinateUpperHalfPlanePullbackFormulaAtlas h)

/--
%%handwave
name:
  Local Liouville developing solutions define local hyperbolic models
statement:
  If $g$ has local solutions $F$ with $\Delta u=e^{2u}=|F'|^2/(\operatorname{Im}F)^2$ and real Möbius transitions, then $g$ admits local upper-half-plane isometry charts.
proof:
  Retain the coordinate Poincaré pullback formula of each solution and convert these formulas into local hyperbolic charts.
-/
theorem hasUpperHalfPlaneLocalModels_of_hasLocalLiouvilleDevelopingSolutionAtlas
    {g : HyperbolicMetric X} (h : g.HasLocalLiouvilleDevelopingSolutionAtlas) :
    g.HasUpperHalfPlaneLocalModels :=
  hasUpperHalfPlaneLocalModels_of_hasCoordinateUpperHalfPlanePullbackFormulaAtlas
    (hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasLocalLiouvilleDevelopingSolutionAtlas h)

/--
%%handwave
name:
  Aligned local Liouville constructions define local hyperbolic models
statement:
  If $g$ has aligned local Liouville metric formulas and upper-half-plane pullback maps with real Möbius transitions, then $g$ admits an atlas of local upper-half-plane isometries.
proof:
  Combine each aligned construction into a local developing solution and then retain its local hyperbolic chart.
-/
theorem hasUpperHalfPlaneLocalModels_of_hasLocalLiouvilleDevelopingConstructionAtlas
    {g : HyperbolicMetric X} (h : g.HasLocalLiouvilleDevelopingConstructionAtlas) :
    g.HasUpperHalfPlaneLocalModels :=
  hasUpperHalfPlaneLocalModels_of_hasLocalLiouvilleDevelopingSolutionAtlas
    (hasLocalLiouvilleDevelopingSolutionAtlas_of_hasLocalLiouvilleDevelopingConstructionAtlas h)

/--
%%handwave
name:
  Solved curvature-derived Liouville formulas define local hyperbolic models
statement:
  If the curvature-derived Liouville formulas of $g$ admit aligned local maps to $\mathbb H$ with real Möbius overlaps, then $g$ admits an atlas of local upper-half-plane isometries.
proof:
  Retain the aligned local developing constructions and convert them successively into local solutions, Poincaré pullback formulas, and local hyperbolic charts.
-/
theorem hasUpperHalfPlaneLocalModels_of_hasCurvatureLiouvilleDevelopingConstructionAtlas
    {g : HyperbolicMetric X} (h : g.HasCurvatureLiouvilleDevelopingConstructionAtlas) :
    g.HasUpperHalfPlaneLocalModels :=
  hasUpperHalfPlaneLocalModels_of_hasLocalLiouvilleDevelopingConstructionAtlas
    (hasLocalLiouvilleDevelopingConstructionAtlas_of_hasCurvatureLiouvilleDevelopingConstructionAtlas h)

end HyperbolicMetric

end

end JJMath
