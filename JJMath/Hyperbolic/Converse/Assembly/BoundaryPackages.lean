import JJMath.Hyperbolic.Converse.ProjectiveAtlas
import JJMath.Hyperbolic.Schwarzian.Theorems.Curvature

/-!
# Minimal boundary package for the selected componentwise converse route

This module contains only the assembly declarations used by the public
`complete_partial_converse_theorem` proof.
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/-- The local-transition model atlas selected by a canonical branch-data package.

%%handwave
name: The local-transition model atlas selected by a canonical branch-data package
statement:
  Given a hyperbolic metric $g$ and a nonempty canonical choice of real
  upper-half-plane branches with compatible overlap transitions, choose one
  such package and retain its local-transition atlas for $g$.
-/
@[reducible] noncomputable def canonicalChartedCurvatureLocalTransitionModels
    (hLocal :
      CanonicalChartedCurvatureLocalTransitionSelectionTheorem X)
    (g : HyperbolicMetric X) :
    HyperbolicLocalModelLocalTransitionAtlas X g :=
  (Classical.choice (hLocal g)).toHyperbolicLocalModelLocalTransitionAtlas

/--
The canonical local-transition model atlas obtained from local real branches
and an abstract componentwise local-transition uniqueness theorem.

%%handwave
name: The canonical local-transition model atlas obtained from local real branches and an abstract componentwise local-transition uniqueness theorem
statement:
  If every hyperbolic metric admits canonical local real
  upper-half-plane branches, and a pointed real Möbius transition extends
  across its entire overlap component, then every hyperbolic metric has a
  canonically selected local-transition atlas.
-/
@[reducible] noncomputable def canonicalChartedCurvatureLocalTransitionModels_of_localRealBranches_componentExtension
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
        X) :
    ∀ (g : HyperbolicMetric X),
      HyperbolicLocalModelLocalTransitionAtlas X g :=
  canonicalChartedCurvatureLocalTransitionModels
    (canonicalChartedCurvatureLocalTransitionSelectionTheorem_of_branchPreDataSelection_pointedTransitions_componentExtension
      (canonicalChartedCurvatureBranchPreDataSelectionTheorem_of_localRealBranches
        hLocal)
      hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem
      hExtend)

/--
The canonical local-transition atlas for the componentwise-overlap route,
with local real branches supplied by the closed Liouville-Schwarzian
construction.

%%handwave
name: The canonical local-transition atlas for the componentwise-overlap route, with local real branches supplied by the closed Liouville-Schwarzian construction
statement:
  If pointed real Möbius transitions extend across overlap components, then
  the Liouville--Schwarzian local branches of every hyperbolic metric determine
  a local-transition atlas whose transitions are constant on each overlap
  component.
-/
@[reducible] noncomputable def metricBoundPartialConverseComponentwiseLocalTransitionModels
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
        X) :
    ∀ (g : HyperbolicMetric X),
      HyperbolicLocalModelLocalTransitionAtlas X g :=
  canonicalChartedCurvatureLocalTransitionModels_of_localRealBranches_componentExtension
    hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem
    hExtend

end HyperbolicMetric

end

end JJMath
