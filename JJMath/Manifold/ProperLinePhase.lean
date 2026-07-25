import JJMath.Manifold.ProperLineThom

/-!
# The periodic phase of a proper-line Thom form

The transverse Thom form on a product tube is the differential of a smooth
step.  Although that step does not extend to a real-valued function on the
ambient manifold, its exponential does: the two constant ends differ by one,
and hence both have complex phase one.  This file constructs the resulting
global smooth phase.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

section ProperLineTubePhase

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M]

end ProperLineTubePhase

end
end Manifold
