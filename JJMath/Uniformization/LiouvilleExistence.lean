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

/--
%%handwave
name: A real function on the complex plane is smooth on one neighborhood of a point
statement:
  A real function on the complex plane is smooth on one neighborhood of a
  point.  Thus the same neighborhood works simultaneously for every finite
  differentiability order.
-/
def ContDiffOnNhdAt (r : ℂ → ℝ) (z : ℂ) : Prop :=
  ∃ V : Set ℂ, V ∈ 𝓝 z ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r V

/--
%%handwave
name: Smoothness at a point from smoothness on a neighborhood
statement:
  If a real-valued function on $\mathbb C$ is smooth on some neighborhood of $z$, then it is smooth at $z$.
proof:
  Use the same neighborhood in the definition of smoothness at the point.
-/
theorem ContDiffOnNhdAt.contDiffAt {r : ℂ → ℝ} {z : ℂ}
    (h : ContDiffOnNhdAt r z) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r z := by
  rcases h with ⟨V, hV, hr⟩
  exact hr.contDiffAt hV

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

/--
%%handwave
name: The boundary of a smooth boundary domain
statement:
  For a smooth relatively compact domain $\Omega$, define
  $\partial\Omega=\operatorname{fr}(\Omega)$.
-/
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


end Uniformization

end JJMath
