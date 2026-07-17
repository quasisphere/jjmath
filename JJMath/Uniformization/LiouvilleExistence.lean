import JJMath.Uniformization.Hyperbolic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Existence of complete Liouville solutions

This file expands the analytic existence part of the hyperbolic
uniformization strategy.  The proof target is that a simply connected surface
in the hyperbolic case carries a complete solution of the Liouville equation.

The intended construction is by exhaustion: solve Dirichlet problems on
smooth relatively compact domains, prove monotonicity and interior estimates,
pass to a smooth local limit, and then prove completeness of the limiting
metric.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal

namespace Uniformization

/-- A real function on the complex plane is smooth on one neighborhood of a
point.  Thus the same neighborhood works simultaneously for every finite
differentiability order. -/
def ContDiffOnNhdAt (r : ℂ → ℝ) (z : ℂ) : Prop :=
  ∃ V : Set ℂ, V ∈ 𝓝 z ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r V

theorem ContDiffOnNhdAt.contDiffAt {r : ℂ → ℝ} {z : ℂ}
    (h : ContDiffOnNhdAt r z) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r z := by
  rcases h with ⟨V, hV, hr⟩
  exact hr.contDiffAt hV

theorem ContDiffOnNhdAt.neg {r : ℂ → ℝ} {z : ℂ}
    (h : ContDiffOnNhdAt r z) :
    ContDiffOnNhdAt (fun w => -r w) z := by
  rcases h with ⟨V, hV, hr⟩
  exact ⟨V, hV, hr.neg⟩

/--
%%handwave
name:
  Smooth boundary predicate
statement:
  An open set has smooth boundary if, near each boundary point and in a
  complex coordinate, it is cut out by a smooth real defining function with
  nonzero differential.
-/
def HasSmoothBoundary {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (U : Set X) : Prop :=
  ∀ x ∈ frontier U,
    ∃ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X ∧ x ∈ e.source ∧
      ∃ r : ℂ → ℝ, ContDiffOnNhdAt r (e x) ∧
        ∃ dr : ℂ →L[ℝ] ℝ,
          HasFDerivAt r dr (e x) ∧ dr ≠ 0 ∧
            ∀ᶠ y in 𝓝 x,
              y ∈ e.source ∧
                (y ∈ U ↔ r (e y) < 0) ∧
                  (y ∈ frontier U ↔ r (e y) = 0)

/--
%%handwave
name:
  Smooth boundary domain
statement:
  A smooth boundary domain in a Riemann surface is a nonempty relatively
  compact open set whose boundary is a smooth one-dimensional submanifold.
-/
structure SmoothBoundaryDomain (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The underlying open subset. -/
  carrier : Set X
  /-- The domain is open. -/
  isOpen : IsOpen carrier
  /-- The domain is nonempty. -/
  nonempty : carrier.Nonempty
  /-- The closure is compact. -/
  compact_closure : IsCompact (closure carrier)
  /-- The boundary is smooth. -/
  smooth_boundary : HasSmoothBoundary carrier

namespace SmoothBoundaryDomain

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The boundary of a smooth boundary domain. -/
def boundary (Ω : SmoothBoundaryDomain X) : Set X :=
  frontier Ω.carrier

end SmoothBoundaryDomain

/--
%%handwave
name:
  Smooth function on a surface region
statement:
  A function is smooth on a region of a Riemann surface if its expression in
  every complex coordinate is smooth on the part of the coordinate image lying
  over that region.
-/
def IsSmoothOnSurface {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (U : Set X) (u : X → ℝ) : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ ↦ u (e.symm z))
      (e.target ∩ e.symm ⁻¹' U)

/--
%%handwave
name:
  Liouville equation on a domain
statement:
  A real-valued function on a surface domain solves the Liouville equation if,
  in every complex coordinate, its local expression satisfies
  $\Delta u = e^{2u}$ at every point of the domain.
-/
def SolvesLiouvilleEquationOn {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : SmoothBoundaryDomain X) (u : X → ℝ) : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) z,
    z ∈ e.target →
      e.symm z ∈ Ω.carrier →
        Laplacian.laplacian (fun w : ℂ ↦ u (e.symm w)) z =
          Real.exp (2 * u (e.symm z))

/--
%%handwave
name:
  Dirichlet boundary data
statement:
  Boundary data for the Liouville Dirichlet problem is a smooth real-valued
  function prescribed along the boundary of the domain.
-/
structure DirichletBoundaryData {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : SmoothBoundaryDomain X) where
  /-- The prescribed boundary value, represented by an ambient function. -/
  toFun : X → ℝ
  /-- The boundary value is smooth near the boundary. -/
  smooth_near_boundary :
    ∃ U : Set X, IsOpen U ∧ Ω.boundary ⊆ U ∧ IsSmoothOnSurface U toFun

namespace DirichletBoundaryData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Ω : SmoothBoundaryDomain X}

instance : CoeFun (DirichletBoundaryData Ω) (fun _ ↦ X → ℝ) where
  coe φ := φ.toFun

end DirichletBoundaryData

/--
%%handwave
name:
  Liouville Dirichlet problem
statement:
  A function solves the Liouville Dirichlet problem on a smooth boundary
  domain when it is smooth in the domain, continuous up to the boundary,
  satisfies $\Delta u=e^{2u}$ in the interior, and equals the prescribed
  boundary value on the boundary.
-/
def SolvesLiouvilleDirichletProblem {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : SmoothBoundaryDomain X) (φ : DirichletBoundaryData Ω) (u : X → ℝ) : Prop :=
  IsSmoothOnSurface Ω.carrier u ∧
    ContinuousOn u (closure Ω.carrier) ∧
      SolvesLiouvilleEquationOn Ω u ∧
        ∀ x ∈ Ω.boundary, u x = φ x

/--
%%handwave
name:
  Dirichlet solution on a smooth domain
statement:
  A Dirichlet solution on a smooth boundary domain is a function satisfying
  the Liouville equation in the domain and the prescribed boundary values.
-/
structure LiouvilleDirichletSolution {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : SmoothBoundaryDomain X) (φ : DirichletBoundaryData Ω) where
  /-- The solution function. -/
  potential : X → ℝ
  /-- The solution satisfies the Dirichlet problem. -/
  solves : SolvesLiouvilleDirichletProblem Ω φ potential

/--
%%handwave
name:
  Cotangent inner product in a complex coordinate
statement:
  In a complex coordinate, two real cotangent vectors are paired by evaluating
  them on the coordinate vectors $1$ and $i$ and taking the Euclidean dot
  product.
-/
noncomputable def realCotangentInner (ξ η : ℂ →L[ℝ] ℝ) : ℝ :=
  ξ 1 * η 1 + ξ Complex.I * η Complex.I

/--
%%handwave
name:
  Smooth positive area measure on a domain
statement:
  A smooth positive area measure on a smoothly bounded domain is a finite
  measure on the domain whose local coordinate densities are smooth and
  positive.
-/
structure SmoothPositiveAreaMeasureOnDomain {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (Ω : SmoothBoundaryDomain X) (μ : Measure X) where
  /-- The domain has finite measure. -/
  finite_on_domain : μ Ω.carrier ≠ ∞
  /-- In each complex coordinate, the area density is represented by a smooth positive function. -/
  chart_density :
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
      ∃ ρ : ℂ → ℝ,
        ContDiffOn ℝ ⊤ ρ (e.target ∩ e.symm ⁻¹' Ω.carrier) ∧
          ∀ z ∈ e.target, e.symm z ∈ Ω.carrier → 0 < ρ z

/--
%%handwave
name:
  Background surface metric on a domain
statement:
  A background surface metric on a smoothly bounded domain supplies the
  intrinsic operators and pairings used in the Liouville equation: its volume
  measure, Laplace-Beltrami operator, Gaussian curvature, and cotangent
  metric.
-/
structure BackgroundSurfaceMetricOnDomain {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (Ω : SmoothBoundaryDomain X) where
  /-- The Riemannian area measure of the background metric. -/
  volume : Measure X
  /-- The area measure is smooth and positive in complex coordinates. -/
  volume_smooth_positive : SmoothPositiveAreaMeasureOnDomain Ω volume
  /-- The Laplace-Beltrami operator of the background metric. -/
  laplaceBeltrami : (X → ℝ) → X → ℝ
  /-- The Gaussian curvature of the background metric. -/
  gaussianCurvature : X → ℝ
  /-- The pointwise pairing on real cotangent vectors induced by the background metric. -/
  gradientInner : X → (ℂ →L[ℝ] ℝ) → (ℂ →L[ℝ] ℝ) → ℝ
  /-- The cotangent pairing is symmetric. -/
  gradientInner_symm :
    ∀ x ξ η, gradientInner x ξ η = gradientInner x η ξ
  /-- The cotangent pairing is nonnegative on diagonal terms. -/
  gradientInner_nonneg :
    ∀ x ξ, 0 ≤ gradientInner x ξ ξ
  /-- The background curvature is smooth on the domain. -/
  curvature_smooth : IsSmoothOnSurface Ω.carrier gaussianCurvature

/--
%%handwave
name:
  Background Liouville equation
statement:
  Relative to a fixed background metric, a conformal factor solves the
  Liouville equation when its Laplace-Beltrami operator equals the background
  curvature plus the exponential conformal term.
-/
def SolvesBackgroundLiouvilleEquationOn {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X}
    (G : BackgroundSurfaceMetricOnDomain Ω) (u : X → ℝ) : Prop :=
  ∀ x ∈ Ω.carrier,
    G.laplaceBeltrami u x = G.gaussianCurvature x + Real.exp (2 * u x)

/--
%%handwave
name:
  Background Liouville Dirichlet problem
statement:
  The intrinsic Dirichlet problem asks for a conformal factor which is smooth
  in the domain, continuous up to the boundary, satisfies the background
  Liouville equation, and equals the prescribed boundary values.
-/
def SolvesBackgroundLiouvilleDirichletProblem {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X}
    (G : BackgroundSurfaceMetricOnDomain Ω) (φ : DirichletBoundaryData Ω)
    (u : X → ℝ) : Prop :=
  IsSmoothOnSurface Ω.carrier u ∧
    ContinuousOn u (closure Ω.carrier) ∧
      SolvesBackgroundLiouvilleEquationOn G u ∧
        ∀ x ∈ Ω.boundary, u x = φ x

/--
%%handwave
name:
  Background Liouville Dirichlet solution
statement:
  A solution of the intrinsic Dirichlet problem is a conformal factor solving
  the background Liouville equation with the prescribed boundary values.
-/
structure BackgroundLiouvilleDirichletSolution {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X}
    (G : BackgroundSurfaceMetricOnDomain Ω) (φ : DirichletBoundaryData Ω) where
  /-- The solution conformal factor. -/
  potential : X → ℝ
  /-- The solution satisfies the intrinsic Dirichlet problem. -/
  solves : SolvesBackgroundLiouvilleDirichletProblem G φ potential

/--
%%handwave
name:
  Boundary extension relative to a background metric
statement:
  A background conformal factor for the variational problem is a smooth
  extension of the boundary value, together with its Laplace-Beltrami operator
  relative to the fixed background metric.
-/
structure DirichletBackgroundConformalFactor {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X}
    (G : BackgroundSurfaceMetricOnDomain Ω) (φ : DirichletBoundaryData Ω) where
  /-- The boundary-extending conformal factor. -/
  toFun : X → ℝ
  /-- The background Laplace-Beltrami operator applied to this factor. -/
  laplaceBeltrami : X → ℝ
  /-- The background factor is smooth up to the closed domain. -/
  smooth : IsSmoothOnSurface (closure Ω.carrier) toFun
  /-- The background factor is continuous up to the boundary. -/
  continuousOn_closure : ContinuousOn toFun (closure Ω.carrier)
  /-- The background factor extends the prescribed boundary value. -/
  boundary_eq : ∀ x ∈ Ω.boundary, toFun x = φ x
  /-- The stored Laplace-Beltrami term agrees with the background operator. -/
  laplaceBeltrami_eq :
    ∀ x ∈ Ω.carrier, G.laplaceBeltrami toFun x = laplaceBeltrami x

namespace DirichletBackgroundConformalFactor

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X} {G : BackgroundSurfaceMetricOnDomain Ω}
    {φ : DirichletBoundaryData Ω}

instance : CoeFun (DirichletBackgroundConformalFactor G φ) (fun _ ↦ X → ℝ) where
  coe v := v.toFun

end DirichletBackgroundConformalFactor

/--
%%handwave
name:
  Corrected conformal factor
statement:
  Given a background conformal factor and a zero-trace correction, the total
  conformal factor is their sum.
-/
def correctedConformalFactor {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] {Ω : SmoothBoundaryDomain X}
    {G : BackgroundSurfaceMetricOnDomain Ω} {φ : DirichletBoundaryData Ω}
    (v : DirichletBackgroundConformalFactor G φ) (u : X → ℝ) : X → ℝ :=
  fun x ↦ u x + v x

/--
%%handwave
name:
  Classical surface gradient
statement:
  A cotangent field is the classical surface gradient of a smooth function
  when, in every complex coordinate, it is the real derivative of the local
  expression of the function.
-/
def IsClassicalSurfaceGradient {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : SmoothBoundaryDomain X) (f : X → ℝ)
    (df : X → ℂ →L[ℝ] ℝ) : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) z,
    z ∈ e.target →
      e.symm z ∈ Ω.carrier →
        df (e.symm z) = fderiv ℝ (fun w : ℂ ↦ f (e.symm w)) z

/--
%%handwave
name:
  Compact support in a domain
statement:
  A function has compact support in a domain if the closure of the set where
  it is nonzero is compact and contained in the domain.
-/
def HasCompactSupportInDomain {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : SmoothBoundaryDomain X) (f : X → ℝ) : Prop :=
  closure {x | f x ≠ 0} ⊆ Ω.carrier ∧
    IsCompact (closure {x | f x ≠ 0})

/--
%%handwave
name:
  Smooth compactly supported surface function
statement:
  A smooth compactly supported surface function on a domain is a smooth
  function with compact support in the domain, together with its classical
  coordinate gradient.
-/
structure SmoothCompactlySupportedSurfaceFunction {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] (Ω : SmoothBoundaryDomain X) where
  /-- The smooth test function. -/
  toFun : X → ℝ
  /-- Its classical gradient, represented in complex coordinates. -/
  gradient : X → ℂ →L[ℝ] ℝ
  /-- The function is smooth on the domain. -/
  smooth : IsSmoothOnSurface Ω.carrier toFun
  /-- The support is compactly contained in the domain. -/
  compact_support : HasCompactSupportInDomain Ω toFun
  /-- The stored gradient is the classical surface gradient. -/
  gradient_eq : IsClassicalSurfaceGradient Ω toFun gradient

namespace SmoothCompactlySupportedSurfaceFunction

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Ω : SmoothBoundaryDomain X}

instance : CoeFun (SmoothCompactlySupportedSurfaceFunction Ω) (fun _ ↦ X → ℝ) where
  coe f := f.toFun

end SmoothCompactlySupportedSurfaceFunction

/--
%%handwave
name:
  Strong convergence in the zero-trace Sobolev norm
statement:
  A sequence of smooth compactly supported functions converges in the
  zero-trace $H^1$ norm to a function and cotangent field when both the
  functions and the gradients converge in $L^2$ on the domain.
-/
def TendstoInSobolevH1Zero {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (Ω : SmoothBoundaryDomain X) (μ : Measure X)
    (F : ℕ → SmoothCompactlySupportedSurfaceFunction Ω)
    (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ) : Prop :=
  Filter.Tendsto
      (fun n : ℕ ↦ eLpNorm (fun x ↦ F n x - u x) 2 (μ.restrict Ω.carrier))
      Filter.atTop (𝓝 0) ∧
    Filter.Tendsto
      (fun n : ℕ ↦ eLpNorm (fun x ↦ (F n).gradient x - du x) 2
        (μ.restrict Ω.carrier))
      Filter.atTop (𝓝 0)

/--
%%handwave
name:
  Zero Sobolev trace
statement:
  A Sobolev function has zero trace on the boundary if it is the strong
  $H^1$ limit of smooth functions compactly supported in the domain.
-/
def HasZeroSobolevTrace {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (Ω : SmoothBoundaryDomain X) (μ : Measure X)
    (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ) : Prop :=
  ∃ F : ℕ → SmoothCompactlySupportedSurfaceFunction Ω,
    TendstoInSobolevH1Zero Ω μ F u du

/--
%%handwave
name:
  Zero-trace Sobolev function
statement:
  A zero-trace $H^1$ function on a smoothly bounded surface domain is an
  $L^2$ function with an $L^2$ weak gradient, obtained as an $H^1$ limit of
  smooth compactly supported functions.
-/
structure SobolevH1ZeroFunction {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (Ω : SmoothBoundaryDomain X) (μ : Measure X) where
  /-- The underlying function. -/
  toFun : X → ℝ
  /-- The weak gradient, represented as a cotangent field in complex coordinates. -/
  weakGradient : X → ℂ →L[ℝ] ℝ
  /-- The function is square-integrable on the domain. -/
  memLp_toFun : MemLp toFun 2 (μ.restrict Ω.carrier)
  /-- The weak gradient is square-integrable on the domain. -/
  memLp_weakGradient : MemLp weakGradient 2 (μ.restrict Ω.carrier)
  /-- The boundary trace is zero. -/
  zero_trace : HasZeroSobolevTrace Ω μ toFun weakGradient

namespace SobolevH1ZeroFunction

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X} {μ : Measure X}

instance : CoeFun (SobolevH1ZeroFunction Ω μ) (fun _ ↦ X → ℝ) where
  coe u := u.toFun

end SobolevH1ZeroFunction

/--
%%handwave
name:
  Coordinate Sobolev Dirichlet seminorm
statement:
  The coordinate Dirichlet seminorm of a zero-trace Sobolev function is the
  integral of the squared Euclidean norm of its weak gradient in complex
  coordinates.
-/
noncomputable def sobolevDirichletSeminormSq {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X} {μ : Measure X}
    (u : SobolevH1ZeroFunction Ω μ) : ℝ :=
  ∫ x in Ω.carrier, realCotangentInner (u.weakGradient x) (u.weakGradient x) ∂μ

/--
%%handwave
name:
  Background Sobolev Dirichlet seminorm
statement:
  Relative to a background metric, the Dirichlet seminorm is the integral of
  the background cotangent norm squared of the weak gradient.
-/
noncomputable def backgroundSobolevDirichletSeminormSq {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X} (G : BackgroundSurfaceMetricOnDomain Ω)
    (u : SobolevH1ZeroFunction Ω G.volume) : ℝ :=
  ∫ x in Ω.carrier, G.gradientInner x (u.weakGradient x) (u.weakGradient x) ∂G.volume

/--
%%handwave
name:
  Liouville Dirichlet energy
statement:
  For a fixed background metric and a boundary extension $v$, the Liouville
  Dirichlet energy of a zero-trace correction $u$ is
  \[
    \frac12\int |\nabla u|_{G}^{2}
      +\frac12\int e^{2(u+v)}
      +\int u\,(K_G-\Delta_G v).
  \]
  Its Euler-Lagrange equation is the weak form of
  $\Delta_G(u+v)=K_G+e^{2(u+v)}$.
-/
noncomputable def liouvilleDirichletEnergy {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X} {G : BackgroundSurfaceMetricOnDomain Ω}
    {φ : DirichletBoundaryData Ω}
    (v : DirichletBackgroundConformalFactor G φ)
    (u : SobolevH1ZeroFunction Ω G.volume) : ℝ :=
  (1 / 2 : ℝ) * backgroundSobolevDirichletSeminormSq G u +
    (1 / 2 : ℝ) *
      ∫ x in Ω.carrier, Real.exp (2 * (u x + v x)) ∂G.volume +
        ∫ x in Ω.carrier,
          u x * (G.gaussianCurvature x - v.laplaceBeltrami x) ∂G.volume

/--
%%handwave
name:
  Finite Liouville Dirichlet energy
statement:
  A zero-trace correction has finite Liouville energy when its gradient
  energy, exponential term, and curvature-background coupling are integrable.
-/
def HasFiniteLiouvilleDirichletEnergy {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X} {G : BackgroundSurfaceMetricOnDomain Ω}
    {φ : DirichletBoundaryData Ω}
    (v : DirichletBackgroundConformalFactor G φ)
    (u : SobolevH1ZeroFunction Ω G.volume) : Prop :=
  IntegrableOn
      (fun x ↦ G.gradientInner x (u.weakGradient x) (u.weakGradient x))
      Ω.carrier G.volume ∧
    IntegrableOn (fun x ↦ Real.exp (2 * (u x + v x))) Ω.carrier G.volume ∧
      IntegrableOn
        (fun x ↦ u x * (G.gaussianCurvature x - v.laplaceBeltrami x))
        Ω.carrier G.volume

/--
%%handwave
name:
  Weak Liouville correction
statement:
  A zero-trace Sobolev correction solves the weak Liouville equation relative
  to a fixed background metric and boundary extension when testing against
  every zero-trace $H^1$ function gives
  \[
    \int \langle\nabla u,\nabla\eta\rangle
      = \int (\Delta_G v-K_G-e^{2(u+v)})\eta .
  \]
-/
def IsWeakLiouvilleCorrection {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X} {G : BackgroundSurfaceMetricOnDomain Ω}
    {φ : DirichletBoundaryData Ω}
    (v : DirichletBackgroundConformalFactor G φ)
    (u : SobolevH1ZeroFunction Ω G.volume) : Prop :=
  HasFiniteLiouvilleDirichletEnergy v u ∧
    ∀ η : SobolevH1ZeroFunction Ω G.volume,
      ∫ x in Ω.carrier,
          G.gradientInner x (u.weakGradient x) (η.weakGradient x) ∂G.volume =
        ∫ x in Ω.carrier,
          (v.laplaceBeltrami x - G.gaussianCurvature x -
            Real.exp (2 * (u x + v x))) * η x ∂G.volume

/--
%%handwave
name:
  Energy minimizer
statement:
  A zero-trace Sobolev correction minimizes the Liouville Dirichlet energy if
  it has finite energy and its energy is no larger than that of any other
  finite-energy zero-trace correction.
-/
def IsLiouvilleEnergyMinimizer {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X} {G : BackgroundSurfaceMetricOnDomain Ω}
    {φ : DirichletBoundaryData Ω}
    (v : DirichletBackgroundConformalFactor G φ)
    (u : SobolevH1ZeroFunction Ω G.volume) : Prop :=
  HasFiniteLiouvilleDirichletEnergy v u ∧
    ∀ w : SobolevH1ZeroFunction Ω G.volume,
      HasFiniteLiouvilleDirichletEnergy v w →
        liouvilleDirichletEnergy v u ≤ liouvilleDirichletEnergy v w

/--
%%handwave
name:
  Weak convergence in zero-trace Sobolev space
statement:
  A sequence converges weakly in $H_0^1$ if its pairing with every zero-trace
  Sobolev test function converges.
-/
def WeaklyTendstoInSobolevH1Zero {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X} {μ : Measure X}
    (U : ℕ → SobolevH1ZeroFunction Ω μ)
    (u : SobolevH1ZeroFunction Ω μ) : Prop :=
  ∀ η : SobolevH1ZeroFunction Ω μ,
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ x in Ω.carrier,
          (U n x * η x +
            realCotangentInner ((U n).weakGradient x) (η.weakGradient x)) ∂μ)
      Filter.atTop
      (𝓝 (∫ x in Ω.carrier,
        (u x * η x + realCotangentInner (u.weakGradient x) (η.weakGradient x)) ∂μ))

/--
%%handwave
name:
  Coercivity of the Liouville energy
statement:
  The Liouville Dirichlet energy is coercive on $H_0^1$: large Dirichlet
  seminorm forces large energy.
-/
def IsCoerciveLiouvilleEnergy {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X} {G : BackgroundSurfaceMetricOnDomain Ω}
    {φ : DirichletBoundaryData Ω}
    (v : DirichletBackgroundConformalFactor G φ) : Prop :=
  ∀ A : ℝ, ∃ R : ℝ, ∀ u : SobolevH1ZeroFunction Ω G.volume,
    R ≤ backgroundSobolevDirichletSeminormSq G u →
      A ≤ liouvilleDirichletEnergy v u

/--
%%handwave
name:
  Weak lower semicontinuity of the Liouville energy
statement:
  The Liouville Dirichlet energy is weakly lower semicontinuous on $H_0^1$.
-/
def IsWeaklyLowerSemicontinuousLiouvilleEnergy {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X} {G : BackgroundSurfaceMetricOnDomain Ω}
    {φ : DirichletBoundaryData Ω}
    (v : DirichletBackgroundConformalFactor G φ) : Prop :=
  ∀ (U : ℕ → SobolevH1ZeroFunction Ω G.volume)
    (u : SobolevH1ZeroFunction Ω G.volume) (a : ℝ),
    WeaklyTendstoInSobolevH1Zero U u →
      Filter.Tendsto (fun n : ℕ ↦ liouvilleDirichletEnergy v (U n))
        Filter.atTop (𝓝 a) →
        liouvilleDirichletEnergy v u ≤ a

/--
%%handwave
name:
  Background correction equation
statement:
  If the background Laplace-Beltrami operator of the total conformal factor
  splits as the correction term plus the background-extension term, then
  writing the total conformal factor as $u+v$ turns the intrinsic Liouville
  equation into
  $\Delta_G u=K_G+e^{2(u+v)}-\Delta_G v$.
proof:
  Expand the background Laplace-Beltrami operator of $u+v$, use the supplied
  splitting identity, and subtract the stored background-extension term.
-/
theorem correctedConformalFactor_solves_liouville_iff
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {Ω : SmoothBoundaryDomain X} {G : BackgroundSurfaceMetricOnDomain Ω}
    {φ : DirichletBoundaryData Ω}
    (v : DirichletBackgroundConformalFactor G φ) (u : X → ℝ)
    (hlap :
      ∀ x ∈ Ω.carrier,
        G.laplaceBeltrami (correctedConformalFactor v u) x =
          G.laplaceBeltrami u x + v.laplaceBeltrami x) :
    SolvesBackgroundLiouvilleEquationOn G (correctedConformalFactor v u) ↔
      ∀ x ∈ Ω.carrier,
        G.laplaceBeltrami u x =
          G.gaussianCurvature x + Real.exp (2 * (u x + v x)) -
            v.laplaceBeltrami x := by
  constructor
  · intro h x hx
    have hsolve := h x hx
    have hsplit := hlap x hx
    simp [correctedConformalFactor] at hsolve hsplit ⊢
    linarith
  · intro h x hx
    have hcorr := h x hx
    have hsplit := hlap x hx
    simp [correctedConformalFactor] at hcorr hsplit ⊢
    linarith







/--
%%handwave
name:
  Liouville subsolution
statement:
  A subsolution for the Liouville equation is a smooth function whose
  Laplacian is bounded below by the nonlinear term $e^{2u}$ in local
  coordinates.
-/
def IsLiouvilleSubsolutionOn {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : SmoothBoundaryDomain X) (u : X → ℝ) : Prop :=
  IsSmoothOnSurface Ω.carrier u ∧
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) z,
      z ∈ e.target →
        e.symm z ∈ Ω.carrier →
          Real.exp (2 * u (e.symm z)) ≤
            Laplacian.laplacian (fun w : ℂ ↦ u (e.symm w)) z

/--
%%handwave
name:
  Liouville supersolution
statement:
  A supersolution for the Liouville equation is a smooth function whose
  Laplacian is bounded above by the nonlinear term $e^{2u}$ in local
  coordinates.
-/
def IsLiouvilleSupersolutionOn {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : SmoothBoundaryDomain X) (u : X → ℝ) : Prop :=
  IsSmoothOnSurface Ω.carrier u ∧
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) z,
      z ∈ e.target →
        e.symm z ∈ Ω.carrier →
          Laplacian.laplacian (fun w : ℂ ↦ u (e.symm w)) z ≤
            Real.exp (2 * u (e.symm z))

/--
%%handwave
name:
  Barrier family for the Dirichlet problem
statement:
  A barrier family consists of a subsolution and a supersolution that trap the
  prescribed boundary values and therefore provide the order interval in which
  the Dirichlet solution is constructed.
-/
structure LiouvilleBarrierFamily {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : SmoothBoundaryDomain X) (φ : DirichletBoundaryData Ω) where
  /-- The lower barrier. -/
  lower : X → ℝ
  /-- The upper barrier. -/
  upper : X → ℝ
  /-- The lower barrier is a subsolution. -/
  lower_subsolution : IsLiouvilleSubsolutionOn Ω lower
  /-- The upper barrier is a supersolution. -/
  upper_supersolution : IsLiouvilleSupersolutionOn Ω upper
  /-- The barriers trap the boundary values. -/
  boundary_trap : ∀ x ∈ Ω.boundary, lower x ≤ φ x ∧ φ x ≤ upper x





/--
%%handwave
name:
  Smooth relatively compact exhaustion
statement:
  A smooth relatively compact exhaustion is an increasing sequence of smooth
  boundary domains whose closures lie in the next domain and whose union is the
  whole surface.
-/
structure SmoothRelativelyCompactExhaustion (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The exhausting domains. -/
  domain : ℕ → SmoothBoundaryDomain X
  /-- The domains are increasing. -/
  monotone : ∀ n, (domain n).carrier ⊆ (domain (n + 1)).carrier
  /-- The closure of each domain lies in the next one. -/
  closure_subset_next : ∀ n, closure (domain n).carrier ⊆ (domain (n + 1)).carrier
  /-- The domains cover the whole surface. -/
  exhausts : ∀ x : X, ∃ n, x ∈ (domain n).carrier


/--
%%handwave
name:
  Dirichlet solutions along an exhaustion
statement:
  Along a smooth exhaustion one can choose Liouville Dirichlet solutions with
  boundary values tending to infinity.
-/
structure ExhaustionDirichletSolutionSequence {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (E : SmoothRelativelyCompactExhaustion X) where
  /-- Boundary data on each exhausting domain. -/
  boundaryData : (n : ℕ) → DirichletBoundaryData (E.domain n)
  /-- The solution on each exhausting domain. -/
  solution : ℕ → X → ℝ
  /-- Each term solves its Dirichlet problem. -/
  solves :
    ∀ n, SolvesLiouvilleDirichletProblem (E.domain n) (boundaryData n) (solution n)
  /-- The sequence is monotone on earlier domains. -/
  monotone_on_previous :
    ∀ n x, x ∈ (E.domain n).carrier → solution n x ≤ solution (n + 1) x
  /-- The prescribed boundary values diverge along the exhaustion boundary. -/
  boundary_tends_to_infinity :
    ∀ A : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ (E.domain n).boundary, A ≤ boundaryData n x


/--
%%handwave
name:
  Local a priori estimates along the exhaustion
statement:
  On every compact subset of the surface, the exhaustion Dirichlet solutions
  satisfy uniform interior bounds and elliptic estimates.
-/
def HasLocalAveragedEllipticEstimates {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    {E : SmoothRelativelyCompactExhaustion X}
    (S : ExhaustionDirichletSolutionSequence E) : Prop :=
  ∀ K : Set X, IsCompact K →
    ∃ n₀ : ℕ, K ⊆ (E.domain n₀).carrier ∧
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
        (k : ℕ), ∃ C : ℝ, 0 ≤ C ∧
          ∀ n ≥ n₀, ∀ z ∈ e.target,
            e.symm z ∈ K →
              ‖iteratedFDeriv ℝ k (fun w : ℂ ↦ S.solution n (e.symm w)) z‖ ≤ C


/--
%%handwave
name:
  Liouville limit of an exhaustion
statement:
  A Liouville limit of an exhaustion Dirichlet sequence is a smooth function
  on the whole surface obtained as the local smooth limit of the solutions,
  and it satisfies the Liouville equation.
-/
structure LiouvilleExhaustionLimit {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    {E : SmoothRelativelyCompactExhaustion X}
    (S : ExhaustionDirichletSolutionSequence E) where
  /-- The limiting potential. -/
  potential : X → ℝ
  /-- The limit is smooth on the surface. -/
  smooth : IsSmoothOnSurface Set.univ potential
  /-- The limit satisfies the Liouville equation in every coordinate. -/
  liouville :
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) z,
      z ∈ e.target →
        Laplacian.laplacian (fun w : ℂ ↦ potential (e.symm w)) z =
          Real.exp (2 * potential (e.symm z))
  /-- The exhaustion sequence converges locally smoothly to the limit. -/
  locally_smooth_limit :
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
      (k : ℕ) z,
        z ∈ e.target →
          Filter.Tendsto
            (fun n : ℕ ↦
              iteratedFDeriv ℝ k (fun w : ℂ ↦ S.solution n (e.symm w)) z)
            Filter.atTop
            (𝓝 (iteratedFDeriv ℝ k (fun w : ℂ ↦ potential (e.symm w)) z))




end Uniformization

end JJMath
