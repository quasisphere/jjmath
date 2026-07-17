import JJMath.Uniformization.RadoSecondCountable
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Basic smooth Riemannian metric structures

General and surface-specialized smooth Riemannian metric structures used by
Relative WP.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff

namespace Uniformization
/--
%%handwave
name:
  Real model of a Riemann surface
statement:
  The real smooth model underlying a Riemann surface is the complex plane
  regarded as a two-dimensional real vector space.
-/
noncomputable abbrev SurfaceRealModel : ModelWithCorners ℝ ℂ ℂ :=
  𝓘(ℝ, ℂ)

/-- The model-with-corners is the ordinary identity model on its real model
space.  The local Sobolev and Rellich coordinate estimates currently use this
case. -/
class IsIdentityManifoldModel (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) : Prop where
  eq_identity : I = 𝓘(ℝ, H)

instance instIsIdentityManifoldModel_self
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    IsIdentityManifoldModel H (𝓘(ℝ, H)) where
  eq_identity := rfl

/--
%%handwave
name:
  Smooth inner product on a real tangent bundle
statement:
  On a real smooth manifold, a smooth Riemannian metric is a smooth family of
  positive definite inner products on tangent spaces.
-/
abbrev ContMDiffRiemannianMetricOnManifold {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) (X : Type) [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] : Type :=
  Bundle.ContMDiffRiemannianMetric I ∞ H (fun x : X ↦ TangentSpace I x)

/--
%%handwave
name:
  Smooth Riemannian metric on a real manifold
statement:
  A smooth Riemannian metric on a real smooth manifold is a smooth positive
  definite inner product on its tangent bundle.
-/
structure SmoothRiemannianMetricOnManifold {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) (X : Type)
    [TopologicalSpace X] [ChartedSpace H X] where
  /-- The base space, with its real smooth manifold structure. -/
  isManifold : IsManifold I ∞ X
  /-- The smooth Riemannian metric on the tangent bundle. -/
  toContMDiffRiemannianMetric :
    letI : IsManifold I ∞ X := isManifold
    ContMDiffRiemannianMetricOnManifold I X

/--
%%handwave
name:
  Smooth inner product on the real tangent bundle
statement:
  On a real smooth surface, a smooth Riemannian metric is a smooth family of
  positive definite inner products on tangent spaces.
-/
abbrev ContMDiffRiemannianMetricOnSurface (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X] : Type :=
  ContMDiffRiemannianMetricOnManifold SurfaceRealModel X

/--
%%handwave
name:
  Smooth Riemannian metric on a surface
statement:
  A smooth Riemannian metric on a Riemann surface is a smooth positive
  definite inner product on the real tangent bundle.
-/
structure SmoothRiemannianMetricOnSurface (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The complex surface, regarded as a real smooth surface. -/
  isManifold_real : IsManifold SurfaceRealModel ∞ X
  /-- The smooth Riemannian metric on the real tangent bundle. -/
  toContMDiffRiemannianMetric :
    letI : IsManifold SurfaceRealModel ∞ X := isManifold_real
    ContMDiffRiemannianMetricOnSurface X

/-- A surface Riemannian metric, regarded as a metric on its underlying real manifold. -/
noncomputable def SmoothRiemannianMetricOnSurface.toManifoldMetric {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) :
    SmoothRiemannianMetricOnManifold SurfaceRealModel X :=
  { isManifold := g.isManifold_real
    toContMDiffRiemannianMetric := g.toContMDiffRiemannianMetric }

/--
%%handwave
name:
  Coordinate tangent vector on a manifold
statement:
  A coordinate tangent vector on a smooth manifold is obtained by pushing a
  tangent vector in the model space through the inverse coordinate chart.
-/
noncomputable def manifoldChartTangentVector {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    (e : OpenPartialHomeomorph X H) (z v : H) :
    TangentSpace I (e.symm z) :=
  show TangentSpace I (e.symm z) from
    fderivWithin ℝ
      (fun w : H ↦ chartAt H (e.symm z) (e.symm w)) e.target z v

/--
%%handwave
name:
  Coordinate tangent vector
statement:
  A coordinate tangent vector is obtained by pushing a tangent vector in the
  coordinate plane through the inverse coordinate chart.
-/
noncomputable def surfaceChartTangentVector {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (z v : ℂ) :
    TangentSpace SurfaceRealModel (e.symm z) :=
  manifoldChartTangentVector SurfaceRealModel e z v

/--
%%handwave
name:
  Tangent bilinear form model fiber
statement:
  The model fiber for a tangent-bilinear form is the space of continuous real
  bilinear forms on the model tangent plane.
-/
abbrev TangentBilinearFormModel : Type :=
  ℂ →L[ℝ] ℂ →L[ℝ] ℝ

/--
%%handwave
name:
  Tangent bilinear form at a point
statement:
  A tangent-bilinear form at a point is a continuous real bilinear form on the
  tangent space at that point.
-/
abbrev TangentBilinearFormAt (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X] (x : X) : Type :=
  TangentSpace SurfaceRealModel x →L[ℝ] TangentSpace SurfaceRealModel x →L[ℝ] ℝ

/--
%%handwave
name:
  Positive definite symmetric tangent form
statement:
  A tangent-bilinear form is positive definite and symmetric when it is
  symmetric on tangent vectors and takes strictly positive values on every
  nonzero tangent vector.
-/
def IsPositiveDefiniteSymmetricTangentForm {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold SurfaceRealModel ∞ X]
    (x : X) (b : TangentBilinearFormAt X x) : Prop :=
  (∀ v w : TangentSpace SurfaceRealModel x, b v w = b w v) ∧
    ∀ v : TangentSpace SurfaceRealModel x, v ≠ 0 → 0 < b v v

/--
%%handwave
name:
  Conformal tangent form
statement:
  A tangent-bilinear form on a Riemann surface is conformal when it is a
  positive scalar multiple of the Euclidean real inner product on the complex
  tangent line.
-/
def IsConformalTangentForm {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold SurfaceRealModel ∞ X]
    (x : X) (b : TangentBilinearFormAt X x) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ v w : TangentSpace SurfaceRealModel x,
      b v w = c * inner ℝ (show ℂ from v) (show ℂ from w)


end Uniformization

end JJMath
