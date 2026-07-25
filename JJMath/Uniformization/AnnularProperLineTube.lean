import JJMath.Manifold.AnnularCohomology
import JJMath.Manifold.ProperLineThom

/-!
# A radial proper-line tube in the annular cylinder

Deleting one radial line from the annular cylinder gives a plane.  Ordering
the resulting coordinates as radial position followed by stereographic
angular position identifies this plane with the standard proper-line tube.
The transition strip has compact angular width, so its image is closed in the
full annular cylinder.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

attribute [local instance] finrank_real_complex_fact'

end

end JJMath.Uniformization
