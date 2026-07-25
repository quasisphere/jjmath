import JJMath.RiemannianGeometry.Basic
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Riemannian volume on finite-dimensional manifolds

Coordinate densities, chart-measure gluing, and existence of the Riemannian
volume measure for smooth finite-dimensional real Riemannian manifolds.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff Bundle MatrixOrder

namespace Uniformization

noncomputable section

/--
%%handwave
name:
  Smooth positive measure on a manifold
statement:
  A smooth positive measure on a finite-dimensional smooth manifold is a
  Borel measure whose local coordinate densities with respect to Lebesgue
  measure on the model space are smooth and strictly positive, and which is
  finite on compact sets.
-/
structure SmoothPositiveMeasureOnManifold {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] (μ : Measure X) : Prop where
  /-- Compact sets have finite measure. -/
  finite_on_compact : ∀ K : Set X, IsCompact K → μ K ≠ (∞ : ℝ≥0∞)
  /-- In each coordinate chart the measure has a smooth positive density. -/
  chart_density :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X),
      ∃ ρ : H → ℝ,
        ContDiffOn ℝ ∞ ρ e.target ∧
          (∀ z ∈ e.target, 0 < ρ z) ∧
          Measure.map e (μ.restrict e.source) =
            (MeasureTheory.volume.restrict e.target).withDensity
              (fun z : H ↦ ENNReal.ofReal (ρ z))

namespace SmoothRiemannianMetricOnManifold

end SmoothRiemannianMetricOnManifold

end

end Uniformization

end JJMath
