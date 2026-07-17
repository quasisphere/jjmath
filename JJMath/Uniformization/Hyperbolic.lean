import JJMath.Hyperbolic
import JJMath.Uniformization.Biholomorphic

/-!
# Hyperbolic uniformization targets

This file records the formalization targets for the hyperbolic case of the
uniformization theorem.  The intended route is analytic: solve the Liouville
equation to obtain a complete curvature `-1` conformal metric, construct the
upper-half-plane developing map, and prove that in the simply connected case
this developing map is a biholomorphic equivalence.
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold Topology

namespace Uniformization

/--
%%handwave
name:
  Complete metric realizing a conformal metric
statement:
  A complete metric realizing a conformal metric \(g\) on a Riemann surface is
  a complete metric inducing the original topology and whose first-order
  distance in every complex chart is the norm prescribed by the conformal
  density of \(g\).
-/
structure CompleteMetricSpaceRealizingConformalMetric {Y : Type}
    [t : TopologicalSpace Y] [ChartedSpace ℂ Y] (g : ConformalMetric Y) where
  /-- The metric space structure. -/
  metricSpace : MetricSpace Y
  /-- The metric topology is the original topology. -/
  compatible_topology : metricSpace.toUniformSpace.toTopologicalSpace = t
  /-- The metric space is complete. -/
  complete : @CompleteSpace Y metricSpace.toUniformSpace
  /-- In charts, the infinitesimal metric is given by the conformal density. -/
  chartwise_infinitesimal_distance :
    letI : MetricSpace Y := metricSpace
    ∀ (e : OpenPartialHomeomorph Y ℂ) (he : e ∈ atlas ℂ Y)
      (y : Y), y ∈ e.source →
        ∀ v : ℂ,
          Filter.Tendsto
            (fun s : ℝ ↦
              dist y (e.symm (e y + (s : ℂ) • v)) / ‖s‖)
            (𝓝[≠] (0 : ℝ))
            (𝓝 (Real.sqrt (g.densitySqInChart e he (e y)) * ‖v‖))

/--
%%handwave
name:
  Complete hyperbolic metric
statement:
  A hyperbolic metric is complete when its underlying conformal metric is
  realized by a complete metric space whose infinitesimal norm is the
  conformal density.
-/
def IsCompleteHyperbolicMetric {Y : Type}
    [TopologicalSpace Y] [ChartedSpace ℂ Y] (g : HyperbolicMetric Y) : Prop :=
  Nonempty (CompleteMetricSpaceRealizingConformalMetric g.toConformalMetric)

/--
%%handwave
name:
  Biholomorphic to the complex plane
statement:
  A Riemann surface is biholomorphic to the complex plane when there is a
  biholomorphic equivalence from the surface to the standard complex plane.
-/
def BiholomorphicToComplexPlane (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (@Biholomorphic X ℂ inferInstance inferInstance inferInstance inferInstance)

/--
%%handwave
name:
  Biholomorphic to the upper half-plane
statement:
  A Riemann surface is biholomorphic to the upper half-plane when there is a
  biholomorphic equivalence from the surface to the standard upper half-plane.
-/
def BiholomorphicToUpperHalfPlane (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (@Biholomorphic X ℍ inferInstance inferInstance inferInstance inferInstance)

/--
%%handwave
name:
  Liouville equation for a conformal metric
statement:
  A conformal metric satisfies the Liouville equation when, in every complex
  coordinate, the logarithm of its squared conformal density satisfies
  $\Delta u = e^{2u}$.  Since the squared density is stored directly, this is
  expressed as $\Delta(\frac12\log \rho)=\rho$.
-/
def SatisfiesLiouvilleEquation {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] (g : ConformalMetric X) : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) z,
    z ∈ e.target →
      Laplacian.laplacian (logDensityFromDensitySq (g.densitySqInChart e he)) z =
        g.densitySqInChart e he z

/--
%%handwave
name:
  Complete Liouville solution
statement:
  A complete Liouville solution is a complete hyperbolic metric whose curvature
  condition comes from a global solution of the Liouville equation.
-/
structure CompleteLiouvilleSolution (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The resulting hyperbolic metric. -/
  metric : HyperbolicMetric X
  /-- The metric is complete. -/
  complete : IsCompleteHyperbolicMetric metric
  /-- The underlying conformal metric satisfies the Liouville equation. -/
  liouville :
    SatisfiesLiouvilleEquation metric.toConformalMetric

/--
%%handwave
name:
  Liouville solutions produce hyperbolic metrics
statement:
  A smooth conformal metric satisfying the Liouville equation is a hyperbolic
  metric.
proof:
  In a coordinate, write the metric as $\rho |dz|^2$ and put
  $u=\frac12\log\rho$.  The Gaussian curvature formula is
  $K=-e^{-2u}\Delta u$.  The Liouville equation gives
  $\Delta u=\rho=e^{2u}$, hence $K=-1$ in every chart.
-/
theorem hyperbolicMetric_of_liouville_solution
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : ConformalMetric X) (hsmooth : g.IsSmooth)
    (hL : SatisfiesLiouvilleEquation g) :
    Nonempty (HyperbolicMetric X) := by
  refine ⟨{ toConformalMetric := g, smooth := hsmooth, curvature_minus_one := ?_ }⟩
  intro e he z hz
  exact gaussianCurvatureOfDensitySq_eq_minus_one_of_liouville
    (g.positive_densitySqInChart e he hz) (hL e he z hz)

/--
%%handwave
name:
  Simply connected hyperbolic case
statement:
  The simply connected hyperbolic case consists of a simply connected Riemann
  surface which is neither compact nor biholomorphic to the complex plane.
  These are exactly the simply connected surfaces that should uniformize to
  the upper half-plane.
-/
def IsSimplyConnectedHyperbolicCase (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ¬ CompactSpace X ∧ ¬ BiholomorphicToComplexPlane X

/--
%%handwave
name:
  Global upper-half-plane developing map
statement:
  A global upper-half-plane developing map is a holomorphic local
  biholomorphism to the upper half-plane whose pullback of the Poincare metric
  is the given hyperbolic metric.
-/
structure GlobalUpperHalfPlaneDevelopingMap (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] (g : HyperbolicMetric X) where
  /-- The developing map. -/
  toFun : X → ℍ
  /-- The developing map is holomorphic. -/
  holomorphic : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) toFun
  /-- The developing map is locally biholomorphic. -/
  locally_biholomorphic :
    ∀ x : X,
      deriv (fun z : ℂ ↦ ((toFun ((chartAt ℂ x).symm z) : ℍ) : ℂ))
        ((chartAt ℂ x) x) ≠ 0
  /-- The developing map pulls back the Poincare metric to the given metric. -/
  pulls_back_poincare :
    PullsBackMetric toFun upperHalfPlaneConformalMetric g.toConformalMetric





/--
%%handwave
name:
  Parabolic universal cover
statement:
  A Riemann surface has parabolic universal cover when its universal cover is
  biholomorphic to the complex plane.
-/
def HasParabolicUniversalCover (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] [LocallySimplyConnectedSpace X] : Prop :=
  ∀ x₀ : X,
    @BiholomorphicToComplexPlane (PathHomotopyUniversalCover X x₀)
      inferInstance inferInstance

/--
%%handwave
name:
  Hyperbolic uniformization case
statement:
  The hyperbolic case for an arbitrary Riemann surface is the case in
  which the surface is not compact and its universal cover is not the complex
  plane.
-/
def IsHyperbolicUniformizationCase (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] [LocallySimplyConnectedSpace X] : Prop :=
  ¬ CompactSpace X ∧ ¬ HasParabolicUniversalCover X

/--
%%handwave
name:
  Upper-half-plane universal cover
statement:
  A Riemann surface has upper-half-plane universal cover when every based
  universal cover is biholomorphic to the upper half-plane.
-/
def HasUpperHalfPlaneUniformizingCover (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] [LocallySimplyConnectedSpace X] : Prop :=
  ∀ x₀ : X,
    @BiholomorphicToUpperHalfPlane (PathHomotopyUniversalCover X x₀)
      inferInstance inferInstance


end Uniformization

end JJMath
