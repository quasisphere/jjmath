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

%%handwave
name:
  Continued local models and projective atlas construction give the converse outputs
statement:
  Suppose every hyperbolic metric $g$ has a selected atlas of local
  upper-half-plane models, continuation of those models on the canonical cover
  yields an equivariant developing map with
  $\mathrm{PSL}_2(\mathbb R)$ holonomy and the Poincaré pullback identity, and
  every projectivized developing map produces a compatible complex projective
  atlas. Then for every basepoint $x_0$ and metric $g$, there exist a
  hyperbolic developing map, its projectivization, and a complex projective
  structure induced by $g$ with real holonomy.
proof:
  Choose the continued developing data for $x_0$ and $g$, retain its
  hyperbolic developing map, and projectivize it using equivariance. Apply the
  assumed atlas construction to this projectivized map; the resulting atlas
  gives the induced complex projective structure, whose holonomy lies in
  $\mathrm{PSL}_2(\mathbb R)$.
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

%%handwave
name:
  Local branch selection and continuation imply the complete partial converse
statement:
  Suppose local real Liouville branches can be selected canonically, any two
  pointed local hyperbolic charts are related by a real Möbius transformation,
  this relation extends across their overlap component, the selected local
  models continue on the canonical cover with
  $\mathrm{PSL}_2(\mathbb R)$ holonomy, and every projectivized developing map
  yields a compatible complex projective atlas. Then every hyperbolic metric
  $g$ on $X$ induces a complex projective structure $P$ whose holonomy lies in
  $\mathrm{PSL}_2(\mathbb R)$ at some basepoint.
proof:
  The branch-selection and component-extension hypotheses construct the
  canonical atlas of local upper-half-plane models. Continuation and the
  projective-atlas hypothesis then give the three converse outputs; applying
  the assembly theorem converts those outputs into an induced projective
  structure with real holonomy.
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
