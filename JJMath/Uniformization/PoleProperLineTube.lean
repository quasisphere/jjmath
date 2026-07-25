import JJMath.Uniformization.AnnularProperLineTube
import JJMath.Uniformization.ExteriorComponentProperLine
import JJMath.Uniformization.GreenFunctionResidue

/-!
# The radial proper-line tube in Green pole coordinates

The canonical radial tube in the annular cylinder transports through the
Green pole coordinate.  Its transition strip is closed relative to the
punctured coordinate disk.  Extending its positive radial end through an
exterior component is the remaining global geometric step.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

attribute [local instance] finrank_real_complex_fact'

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  [RiemannSurface X]
  {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
  {P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G}

end

end JJMath.Uniformization
