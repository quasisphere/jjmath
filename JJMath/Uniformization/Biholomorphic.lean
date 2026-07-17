import JJMath.ComplexProjective.Prerequisites.RiemannSurface

/-!
# Biholomorphic maps of complex manifolds

This file contains the small, model-independent interface used by the
uniformization theorems.  In particular, it does not choose or construct any
special target surface.
-/

namespace JJMath

open scoped Manifold Topology

namespace Uniformization

universe u v

/--
%%handwave
name:
  Holomorphic map
statement:
  A map \(f:X\to Y\) between complex manifolds is holomorphic when it is
  complex differentiable at every point in manifold coordinates.
-/
def HolomorphicMap (X : Type u) (Y : Type v)
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] (f : X → Y) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f

/--
%%handwave
name:
  Pointed holomorphic map
statement:
  A pointed holomorphic map \((X,p)\to(Y,q)\) is a holomorphic map
  \(f:X\to Y\) satisfying \(f(p)=q\).
-/
structure PointedHolomorphicMap (X : Type u) (Y : Type v)
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] (p : X) (q : Y) where
  /-- The underlying map. -/
  toFun : X → Y
  /-- The map is holomorphic. -/
  holomorphic : HolomorphicMap X Y toFun
  /-- The source base point maps to the target base point. -/
  base_eq : toFun p = q

namespace PointedHolomorphicMap

variable {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] {p : X} {q : Y}

instance : CoeFun (PointedHolomorphicMap X Y p q) (fun _ ↦ X → Y) where
  coe F := F.toFun

end PointedHolomorphicMap

/--
%%handwave
name:
  Biholomorphic equivalence
statement:
  A biholomorphic equivalence \(X\simeq Y\) is a homeomorphism whose forward
  and inverse maps are holomorphic.
-/
structure Biholomorphic (X : Type u) (Y : Type v)
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] where
  /-- The underlying homeomorphism. -/
  toHomeomorph : X ≃ₜ Y
  /-- The forward map is holomorphic. -/
  holomorphic_toFun : HolomorphicMap X Y toHomeomorph
  /-- The inverse map is holomorphic. -/
  holomorphic_invFun : HolomorphicMap Y X toHomeomorph.symm

/--
%%handwave
name:
  Biholomorphic complex manifolds
statement:
  Complex manifolds \(X\) and \(Y\) are biholomorphic if there exists a
  biholomorphic equivalence \(X\simeq Y\).
-/
def BiholomorphicSurfaces (X : Type u) (Y : Type v)
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] : Prop :=
  Nonempty (@Biholomorphic X Y inferInstance inferInstance inferInstance inferInstance)

end Uniformization

end JJMath
