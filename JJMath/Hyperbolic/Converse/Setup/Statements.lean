import JJMath.Hyperbolic.ProjectiveStructure
import JJMath.Hyperbolic.Schwarzian
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Split partial-converse setup declarations
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

namespace HyperbolicDevelopingAnalyticData

variable {x₀ : X} {g : HyperbolicMetric X}

end HyperbolicDevelopingAnalyticData

end HyperbolicMetric

end

end JJMath
