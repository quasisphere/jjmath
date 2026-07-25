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
