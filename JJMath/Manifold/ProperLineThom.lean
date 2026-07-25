import JJMath.Manifold.AnnularPeriod

/-!
# A transverse Thom form on a proper-line tube

This file constructs the standard closed one-form on `ℝ × ℝ` obtained by
differentiating a step in the second coordinate.  Its support lies in the
closed strip `ℝ × [-1,1]`, and its integral across that strip is one.  The
strip is noncompact; when a tube is placed in another manifold, closedness of
its image is the geometric condition that permits extension by zero.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

section ProperLineTube

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M]

end ProperLineTube

section ProperLineTubePeriod

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M]

end ProperLineTubePeriod

end
end Manifold
end JJMath
