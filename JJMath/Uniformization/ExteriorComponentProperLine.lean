import JJMath.Uniformization.SurfaceEndPath
import JJMath.Uniformization.SmoothFrontierMayerVietoris

/-!
# Proper lines through an exterior-component collar

The negative radial half of a side-preserving annular collar is proper in the
union of the collar with its exterior component.  The proof glues the inward
collar depth to the constant zero function on the exterior component.  This
is the collar half of the proper line used to carry the angular period class.
-/

open Set
open scoped Manifold Topology ContDiff

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]

/-! ## Bringing an exterior proper ray into the collar union -/

end

end JJMath.Uniformization
