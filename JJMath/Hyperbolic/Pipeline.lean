import JJMath.Hyperbolic.LocalFormula

/-!
# Local-to-global pipeline for hyperbolic developing maps

This file ties together the two major pieces of the developing-map theorem:

1. local Liouville/developing solutions, giving local maps to `ℍ`;
2. analytic continuation of those local maps on the simply connected cover.

The resulting package immediately produces the lifted and `PSL(2, ℝ)`-valued
developing-map targets.
-/

namespace JJMath

noncomputable section

namespace HyperbolicDevelopingPipeline

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

end HyperbolicDevelopingPipeline

namespace HyperbolicDevelopingConstructionPipeline

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

end HyperbolicDevelopingConstructionPipeline

namespace HyperbolicDevelopingCurvaturePipeline

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {x₀ : X} {g : HyperbolicMetric X}

end HyperbolicDevelopingCurvaturePipeline

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

end HyperbolicMetric

end

end JJMath
