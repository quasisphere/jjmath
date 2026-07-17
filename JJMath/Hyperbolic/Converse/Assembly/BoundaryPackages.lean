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

/--
PSL-valued selected local-transition continuation plus projective-atlas
construction gives the main partial-converse outputs.
-/
theorem partial_converse_main_outputs_theorem_of_selected_local_transition_continuation_psl_and_projective_atlas
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g)
    (selectedContinuation :
      SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
        X chosenLocalModels)
    (projectiveAtlasTheorem :
      ProjectiveAtlasFromProjectivizedDevelopingMapTheorem X) :
    PartialConverseMainOutputsTheorem X := by
  intro x₀ g
  let F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
        x₀ g (chosenLocalModels g) :=
    Classical.choice (selectedContinuation x₀ g)
  let D : HyperbolicDevelopingMap X x₀ g :=
    F.toHyperbolicDevelopingMap
  let P : ProjectivizedHyperbolicDevelopingMap X x₀ g :=
    D.toProjectivized D.projectiveEquivariant
  exact
    ⟨⟨D⟩,
      ⟨P⟩,
      inducesRealProjectiveStructure_of_hasProjectiveAtlasFromDevelopingMap
        ⟨P, projectiveAtlasTheorem x₀ g P⟩⟩

/-- The local-transition model atlas selected by a canonical branch-data package. -/
@[reducible] noncomputable def canonicalChartedCurvatureLocalTransitionModels
    (hLocal :
      CanonicalChartedCurvatureLocalTransitionSelectionTheorem X)
    (g : HyperbolicMetric X) :
    HyperbolicLocalModelLocalTransitionAtlas X g :=
  (Classical.choice (hLocal g)).toHyperbolicLocalModelLocalTransitionAtlas

/--
Unlifted PSL-valued local-transition continuation, together with the local
componentwise construction and projective-atlas theorem, gives the completed
main-output theorem.
-/
theorem complete_partial_converse_theorem_of_branch_pre_data_selection_pointed_transitions_component_extension_selected_continuation_psl_projective_atlas
    (hSelection :
      CanonicalChartedCurvatureBranchPreDataSelectionTheorem X)
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
        X)
    (selectedContinuation :
      SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL X
        (canonicalChartedCurvatureLocalTransitionModels
          (canonicalChartedCurvatureLocalTransitionSelectionTheorem_of_branchPreDataSelection_pointedTransitions_componentExtension
            hSelection hPoint hExtend)))
    (projectiveAtlasTheorem :
      ProjectiveAtlasFromProjectivizedDevelopingMapTheorem X) :
    CompletePartialConverseTheorem X :=
  complete_partial_converse_theorem_of_partial_converse_main_outputs_theorem
    (partial_converse_main_outputs_theorem_of_selected_local_transition_continuation_psl_and_projective_atlas
      (canonicalChartedCurvatureLocalTransitionModels
        (canonicalChartedCurvatureLocalTransitionSelectionTheorem_of_branchPreDataSelection_pointedTransitions_componentExtension
          hSelection hPoint hExtend))
      selectedContinuation
      projectiveAtlasTheorem)

/--
The canonical local-transition model atlas obtained from local real branches
and an abstract componentwise local-transition uniqueness theorem.
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
