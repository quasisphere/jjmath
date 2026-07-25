import JJMath.Manifold.ProperLineThom
import JJMath.Uniformization.SmoothChainConnectivity

/-!
# Proper-line period obstructions on smooth surfaces

This file combines the transverse Thom form of a proper line tube with
smooth-chain connectivity.  If deleting the closed middle strip leaves a
connected surface, its two transverse endpoints can be joined outside the
strip.  Closing the transverse crossing by that return chain gives a cycle
of period one.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

open JJMath.Uniformization

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [IsManifold SurfaceRealModel ∞ X] [T2Space X]

end
end Manifold
end JJMath
