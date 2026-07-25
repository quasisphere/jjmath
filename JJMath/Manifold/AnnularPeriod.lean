import JJMath.Manifold.OneFormPeriod
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The standard annular period form

This file constructs Hubbard's closed one-form on the standard cylinder.  It
is the differential of a smooth step function in the normal coordinate.  The
step is zero on one end of the cylinder and one on the other, so its integral
along a transverse segment is one.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

/-- The smooth model used for the standard cylinder `Circle × ℝ`. -/
abbrev AnnularCylinderModel :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 1) × ℝ)
      (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) :=
  (𝓡 1).prod 𝓘(ℝ, ℝ)

/--
%%handwave
name:
  Smooth annular step
statement:
  The annular step is the smooth function $\chi(y)=\theta((y+1)/2)$, equal to $0$ for $y\le-1$ and to $1$ for $y\ge1$, where $\theta$ is the standard smooth transition.
-/
def annularStep (y : ℝ) : ℝ :=
  Real.smoothTransition ((y + 1) / 2)

/--
%%handwave
name:
  Smoothness of the annular step function
statement:
  The function \(\chi(y)=\theta((y+1)/2)\), where \(\theta\) is the standard
  smooth transition from \(0\) to \(1\), is smooth on \(\mathbb R\).
proof:
  It is the composition of the smooth transition function with an affine map.
-/
@[fun_prop]
theorem contDiff_annularStep : ContDiff ℝ ∞ annularStep := by
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_id.add contDiff_const).div_const (2 : ℝ))

/--
%%handwave
name:
  Value of the annular step below the transition interval
statement:
  If \(y\le-1\), then \(\chi(y)=0\).
proof:
  The rescaled argument \((y+1)/2\) is nonpositive, where the standard smooth
  transition function vanishes.
-/
@[simp]
theorem annularStep_eq_zero_of_le_neg_one {y : ℝ} (hy : y ≤ -1) :
    annularStep y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

/--
%%handwave
name:
  Value of the annular step above the transition interval
statement:
  If \(y\ge1\), then \(\chi(y)=1\).
proof:
  The rescaled argument \((y+1)/2\) is at least \(1\), where the standard
  smooth transition function equals \(1\).
-/
@[simp]
theorem annularStep_eq_one_of_one_le {y : ℝ} (hy : 1 ≤ y) :
    annularStep y = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

section AnnularCollar

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M]

end AnnularCollar

section AnnularCollarPeriod

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M]

end AnnularCollarPeriod

end

end Manifold
end JJMath
