import JJMath.Hyperbolic.Converse.Setup.BranchSelection

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

namespace CanonicalChartedCurvatureBranchBallShrinkData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (((localCurvatureMetricFormulaAtlasInChartAt g)
            |>.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).conformalFactor}

end CanonicalChartedCurvatureBranchBallShrinkData

namespace CanonicalChartedCurvaturePreconnectedOverlapBranchSelection

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}

end CanonicalChartedCurvaturePreconnectedOverlapBranchSelection

namespace CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelection

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}

end CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelection

end HyperbolicMetric

end

end JJMath
