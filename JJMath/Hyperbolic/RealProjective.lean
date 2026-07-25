import JJMath.ComplexProjective.Holonomy
import JJMath.Hyperbolic.DevelopingMap

/-!
# Real projective structures and singular hyperbolic metrics

This file records the relationship between complex projective structures with
real holonomy and the hyperbolic metrics induced by their developing maps.
-/

namespace JJMath

open scoped MatrixGroups

namespace HolonomyRepresentation

variable {X : Type} [TopologicalSpace X] {x₀ : X}

end HolonomyRepresentation


namespace HolonomyRepresentation

variable {X : Type} [TopologicalSpace X] {x₀ : X}

end HolonomyRepresentation


namespace HolonomyRepresentation

variable {X : Type} [TopologicalSpace X] {x₀ : X}

end HolonomyRepresentation

/--
A concrete unlifted real-holonomy certificate for a based complex projective
structure.

The important point is that the holonomy representation is not floating freely:
it is accompanied by the atlas data saying that it is the holonomy constructed
from this particular projective structure.
-/
structure ComplexProjectiveStructure.RealHolonomyData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) (P : ComplexProjectiveStructure X) where
  /-- The complex projective holonomy read from the projective atlas. -/
  projectiveHolonomy : HolonomyRepresentation X x₀
  /-- Concrete atlas data tying the holonomy to `P`. -/
  holonomy_constructed_from_projective_charts :
    ProjectiveHolonomyConstructionData X x₀ P projectiveHolonomy
  /-- The underlying real holonomy representation. -/
  realHolonomy : RealHolonomyRepresentation X x₀
  /-- The projective holonomy is the complexification of the real holonomy. -/
  projectiveHolonomy_eq_real :
    projectiveHolonomy.toMonoidHom = realMobiusToMobiusGroup.comp realHolonomy.toMonoidHom

namespace ComplexProjectiveStructure.RealHolonomyData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {P : ComplexProjectiveStructure X}

end ComplexProjectiveStructure.RealHolonomyData


/--
A complex projective structure has real holonomy if the holonomy constructed
from its own projective atlas is the complexification of a real representation.

%%handwave
name:
  Complex projective structure with real holonomy
statement:
  A based complex projective structure has $\mathrm{PSL}_2(\mathbb R)$ holonomy when its atlas holonomy is the complexification of some representation $\pi_1(X,x_0)\to\mathrm{PSL}_2(\mathbb R)$.
-/
def HasPSL2RHolonomy {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (x₀ : X) (P : ComplexProjectiveStructure X) : Prop :=
  Nonempty (P.RealHolonomyData x₀)

/-- A projective structure with coordinate changes in the complexified `PSL(2, ℝ)` subgroup. -/
abbrev PSL2RProjectiveStructure (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [RiemannSurface X] : Type :=
  ProjectiveStructureWithGroup psl2rMobiusSubgroup X

end JJMath
