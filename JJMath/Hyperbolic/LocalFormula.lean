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

/-- The squared conformal density `λ^2 = exp (2u)`.
%%handwave
name:
  Squared density of a local conformal factor
statement:
  A logarithmic conformal factor $u$ determines the squared density $\rho(z)=e^{2u(z)}$.
-/
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

/-- The Liouville equation for curvature `-1`: `Δ u = exp (2u)`.
%%handwave
name:
  Hyperbolic Liouville equation
statement:
  A local conformal factor $u$ solves the Liouville equation on $\Omega$ when $\Delta u(z)=e^{2u(z)}$ for every $z\in\Omega$.
-/
def SolvesLiouvilleEquation (u : LocalConformalFactor) : Prop :=
  ∀ z, z ∈ u.coordinateDomain →
    Laplacian.laplacian u.logDensity z = Real.exp (2 * u.logDensity z)

/-- Restrict a local conformal factor to an open subdomain.
%%handwave
name:
  Restriction of a local conformal factor
statement:
  For an open subset $V\subseteq\Omega$, the restriction of a local conformal factor on $\Omega$ retains the same logarithmic-density function and regards it as a conformal factor on $V$.
-/
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

%%handwave
name:
  Gaussian curvature of a local conformal factor
statement:
  The Gaussian curvature of the conformal metric $e^{2u}|dz|^2$ is $K_u(z)=-e^{-2u(z)}\Delta u(z)$.
-/
def gaussianCurvature (u : LocalConformalFactor) (z : ℂ) : ℝ :=
  - Real.exp (-(2 * u.logDensity z)) * Laplacian.laplacian u.logDensity z

/-- The local conformal metric `exp (2u) |dz|^2` has Gaussian curvature `-1`.
%%handwave
name:
  Local conformal factor of curvature minus one
statement:
  A local conformal factor $u$ has curvature $-1$ when $-e^{-2u(z)}\Delta u(z)=-1$ for every point of its coordinate domain.
-/
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

end LocalConformalFactor

/-- The squared norm `|f'(z)|^2` of the complex derivative of a map to `ℍ`.
%%handwave
name:
  Squared norm of a complex derivative
statement:
  For a map $f:\mathbb C\to\mathbb H$, its derivative norm-square at $z$ is $|f'(z)|^2$ after viewing $f$ as complex-valued.
-/
def complexDerivativeNormSq (f : ℂ → ℍ) (z : ℂ) : ℝ :=
  Complex.normSq (deriv (fun w : ℂ ↦ (f w : ℂ)) z)

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

/-- The formula package determines the lightweight local chart used upstream.
%%handwave
name:
  Hyperbolic chart associated to a pullback formula
statement:
  A local Poincaré pullback formula determines a local map to $\mathbb H$ together with its coordinate, holomorphicity, local biholomorphism, and metric-pullback data.
-/
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

end UpperHalfPlanePullbackFormula

/--
Regularity certificate for a coordinate-level upper-half-plane pullback formula.

%%handwave
name:
  Holomorphic coordinate map to the upper half-plane
statement:
  For $\Omega\subseteq\mathbb C$ and $f:\mathbb C\to\mathbb H$, this predicate asserts that the complex-valued map $f$ is differentiable at every point of $\Omega$.
-/
def CoordinateUpperHalfPlaneMapHolomorphicOn
    (coordinateDomain : Set ℂ) (localMap : ℂ → ℍ) : Prop :=
  ∀ z, z ∈ coordinateDomain →
    DifferentiableAt ℂ (fun w : ℂ ↦ (localMap w : ℂ)) z

/-- Nonvanishing of the complex derivative of a coordinate upper-half-plane map.
%%handwave
name:
  Nonvanishing derivative of an upper-half-plane coordinate map
statement:
  For $\Omega\subseteq\mathbb C$ and $f:\mathbb C\to\mathbb H$, this predicate asserts that $f'(z)\ne0$ for every $z\in\Omega$.
-/
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

/-- The actual local map to `ℍ` on the surface domain.
%%handwave
name:
  Surface map defined by an upper-half-plane coordinate formula
statement:
  A coordinate pullback formula with surface coordinate $\zeta$ and coordinate map $f$ defines the surface map $x\mapsto f(\zeta(x))$ into $\mathbb H$.
-/
def toUpperHalfPlane (F : CoordinateUpperHalfPlanePullbackFormula X g) : X → ℍ :=
  fun x ↦ F.localMap (F.coordinate x)

/-- The coordinate local map is holomorphic on the coordinate domain.
%%handwave
name:
  Holomorphicity supplied by a coordinate pullback formula
statement:
  The coordinate map in a coordinate-level Poincaré pullback formula is holomorphic throughout its coordinate domain.
-/
def holomorphic_on_coordinateDomain (F : CoordinateUpperHalfPlanePullbackFormula X g) :
    CoordinateUpperHalfPlaneMapHolomorphicOn F.coordinateDomain F.localMap :=
  F.regularity.holomorphic_on_coordinateDomain

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

/-- Forget the chosen coordinate, retaining the abstract pullback-formula package.
%%handwave
name:
  Abstract pullback formula from a coordinate formula
statement:
  A coordinate Poincaré pullback formula canonically yields an abstract local pullback formula by retaining its surface map, regularity, derivative norm-square, and metric-density identity.
-/
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
Restrict the surface domain of a local Liouville metric formula to points whose
coordinate lies in a chosen coordinate subset, while keeping the ambient
coordinate conformal factor unchanged.

This is useful when a subsequent construction, such as a local Schwarzian
branch, is defined only on a smaller coordinate neighborhood but still uses the
same Schwarzian data for the original conformal factor.

%%handwave
name:
  Restriction of a local Liouville metric formula
statement:
  Given a local Liouville metric formula and $V$ inside its coordinate domain, restrict its surface domain to the points whose coordinate lies in $V$, while keeping the same conformal factor and Liouville equation.
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

/-- The curvature formula implies the corresponding Liouville metric formula.
%%handwave
name:
  Liouville formula obtained from curvature minus one
statement:
  A local metric formula with $K=-1$ determines a local Liouville formula on the same domain because $-e^{-2u}\Delta u=-1$ implies $\Delta u=e^{2u}$.
-/
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

/-- Forget all formula data and keep the underlying local hyperbolic chart.
%%handwave
name:
  Hyperbolic chart underlying a local Liouville developing solution
statement:
  A local Liouville developing solution determines the local upper-half-plane chart carried by its Poincaré pullback formula.
-/
def toHyperbolicLocalChart (S : LocalLiouvilleDevelopingSolution X g) :
    HyperbolicLocalChart X g :=
  S.pullbackFormula.toUpperHalfPlanePullbackFormula.toHyperbolicLocalChart

end LocalLiouvilleDevelopingSolution







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

/-- Rewrite every local curvature formula as a local Liouville metric formula.
%%handwave
name:
  Liouville atlas obtained from a curvature atlas
statement:
  An atlas of local curvature-$-1$ formulas canonically yields an atlas of local Liouville formulas by converting each $-e^{-2u}\Delta u=-1$ identity into $\Delta u=e^{2u}$.
-/
def toLocalLiouvilleMetricFormulaAtlas
    (A : LocalCurvatureMetricFormulaAtlas X g) :
    LocalLiouvilleMetricFormulaAtlas X g where
  formulaAt x := (A.formulaAt x).toLocalLiouvilleMetricFormula
  mem_formulaAt_domain := A.mem_formulaAt_domain

end LocalCurvatureMetricFormulaAtlas





namespace LocalLiouvilleDevelopingConstructionAtlas

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {g : HyperbolicMetric X}

end LocalLiouvilleDevelopingConstructionAtlas

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

end HyperbolicMetric

end

end JJMath
