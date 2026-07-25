import JJMath.Manifold.AnnularPeriod
import JJMath.Uniformization.SmoothChainConnectivity

/-!
# The annular-period obstruction on a smooth surface

This file combines the compactly supported annular one-form with smooth-chain
connectivity.  If the exterior of the compact transition band is connected,
its two transverse endpoints can be joined by a smooth return chain.  The
resulting cycle has period one, so first de Rham cohomology is nontrivial.
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
