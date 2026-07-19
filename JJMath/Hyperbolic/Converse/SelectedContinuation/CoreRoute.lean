import JJMath.Hyperbolic.Converse.ComponentwiseValuePropagation.Core

set_option linter.unusedSectionVars false

/-!
# Split selected/componentwise converse route
-/

namespace JJMath

open UpperHalfPlane
open scoped Manifold

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/--
The exact remaining selected PSL continuation theorem for the canonical
fixed-left-source componentwise local-transition atlas.
-/
def SelectedComponentwiseLeftSourcePSLContinuationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/--
The homotopy-grid walk boundary for the canonical fixed-left-source
componentwise local-transition atlas.
-/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/--
The elementary homotopy-grid move boundary for the componentwise PSL route.
-/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/--
The one-column terminal-value witness boundary for the componentwise PSL route.
-/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnValueWitnessTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/--
The decomposed one-column terminal-value witness boundary for the componentwise
PSL route.
-/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/--
The exact cut-reparameterization transfer boundary for the componentwise PSL
route.
-/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/--
The sharp explicit cut-reparameterization witness boundary for the
componentwise PSL route.
-/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/-- The monotone subpath-merge branch-data boundary for the componentwise route. -/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/-- The normalized unit-split branch-data boundary for the componentwise route. -/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffUnitSplitBranchDataWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffUnitSplitBranchDataWitnessTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/-- The interior normalized unit-split branch-data boundary for the componentwise route. -/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffInteriorUnitSplitBranchDataWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffInteriorUnitSplitBranchDataWitnessTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)


/-- The monotone prefixed subpath-merge value boundary for the componentwise route. -/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)




/-- The endpoint-normalization boundary for raw-to-public cut paths. -/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)


/--
The one-column chart-grid replacement boundary for the componentwise PSL route.
-/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnMovePrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnMovePrincipleTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/--
The one-strip chart-grid replacement boundary for the componentwise PSL route.
-/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripMovePrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripMovePrincipleTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/--
The chart-grid local replacement boundary for the componentwise PSL route.
-/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartGridMovePrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartGridMovePrincipleTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/--
The same-path terminal-value uniqueness boundary for the componentwise PSL
route.
-/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/--
The common aligned mutual vertex-refinement boundary for the componentwise PSL
route.
-/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/--
The own-split parameter-alignment boundary for the componentwise PSL route.

This is the finite ordered-subdivision statement that remains after the
length count has been proven: mutual endpoint-chart insertion plus one plain
split along each side's original vertices should give the same parameter list.
-/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/--
The own-split parameter-permutation boundary for the componentwise PSL route.

Sortedness of skeleton parameter lists turns this multiset statement into the
own-split alignment theorem.
-/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/--
Construct the canonical continuation directly from the finite path and
homotopy comparison results, without retaining each theorem-valued adapter as
a separate public declaration.
-/
private noncomputable def selectedComponentwiseLeftSourcePSLContinuation :
    SelectedComponentwiseLeftSourcePSLContinuationTheorem X := by
  have hInterior :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffInteriorUnitSplitBranchDataWitnessTheorem
        X := by
    intro g
    exact pathLocalTransitionBasedWeakHandoffInteriorUnitSplitBranchDataWitnessPrinciple
  have hUnit :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffUnitSplitBranchDataWitnessTheorem X := by
    intro g
    exact
      pathLocalTransitionBasedWeakHandoffUnitSplitBranchDataWitnessPrinciple_of_interior
        (hInterior g)
  have hMerge :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem
        X := by
    intro g
    exact
      pathLocalTransitionBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessPrinciple_of_unitSplit
        (hUnit g)
  have hPrefixed :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessTheorem
        X := by
    intro g
    exact
      pathLocalTransitionBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessPrinciple_of_monotoneSubpathMergeBranchData
        (hMerge g)
  have hNormalize :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessTheorem
        X := by
    intro x₀ g
    exact
      pathLocalTransitionBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessPrinciple_unconditional
        x₀ g
        (metricBoundPartialConverseComponentwiseLocalTransitionModels
          pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem g)
  have hExplicit :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem
        X := by
    intro x₀ g
    exact
      pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple_of_monotoneSubpathMerge_and_endpointNormalization
        (hMerge g) (hPrefixed g) (hNormalize x₀ g)
  have hCut :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferTheorem
        X := by
    intro x₀ g
    exact
      pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferPrinciple_of_explicitValueWitness_unconditional
        (hExplicit x₀ g)
  have hDecomposed :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessTheorem
        X := by
    intro x₀ g
    exact
      pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessPrinciple_unconditional
        x₀ g
        (metricBoundPartialConverseComponentwiseLocalTransitionModels
          pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem g)
  have hColumnValue :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnValueWitnessTheorem
        X := by
    intro x₀ g
    exact
      pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnValueWitnessPrinciple_of_decomposed_and_cutReparam
        (hDecomposed x₀ g) (hCut x₀ g)
  have hColumnMove :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnMovePrincipleTheorem
        X := by
    intro x₀ g basedWeakHandoffAlong
    exact
      pathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnMovePrinciple_of_valueWitness_unconditional
        (basedWeakHandoffAlong := basedWeakHandoffAlong) (hColumnValue x₀ g)
  have hStripMove :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripMovePrincipleTheorem X := by
    intro x₀ g basedWeakHandoffAlong
    exact
      pathLocalTransitionBasedWeakHandoffHomotopyChartStripMovePrinciple_of_columnMovePrinciple
        (hColumnMove x₀ g basedWeakHandoffAlong)
  have hGridMove :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartGridMovePrincipleTheorem X := by
    intro x₀ g basedWeakHandoffAlong
    exact
      pathLocalTransitionBasedWeakHandoffHomotopyChartGridMovePrinciple_of_stripMovePrinciple
        (hStripMove x₀ g basedWeakHandoffAlong)
  have hElementary :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
        X :=
    selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem_of_selectedHomotopyChartGridMove
      hGridMove
  have hGridWalk :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem X :=
    selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem_of_selectedElementaryGridMoveWalk
      hElementary
  have hPermutation :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationTheorem
        X := by
    intro x₀ g
    exact
      pathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationPrinciple
  have hOwnAlignment :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem
        X :=
    selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem_of_selectedOwnSplitParameterPermutation
      hPermutation
  have hCommonAlignment :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem
        X :=
    selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem_of_selectedOwnSplitParameterAlignment
      hOwnAlignment
  have hUnique :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
        X :=
    selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedMutualVertexRefinementCommonAlignedSubdivision
      hCommonAlignment
  exact
    selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathTerminalValueUniqueness
      hGridWalk hUnique























/--
Completed metric-bound partial converse with the conclusion phrased as a
`PSL(2, ℝ)`-projective structure.  The proof chooses the H-valued developing
map obtained by analytic continuation and uses its real-equivariant branch
atlas directly.

%%handwave
name:
  A hyperbolic metric induces a real projective structure
statement:
  For every hyperbolic metric $g$ on a Riemann surface $X$, there exists a
  projective structure with transition maps in
  $\mathrm{PSL}_2(\mathbb R)$ whose underlying complex projective structure
  is induced by $g$.
proof:
  Continue the canonical local upper-half-plane charts on a based simply
  connected cover to obtain an equivariant map
  $D:\widetilde X\to\mathbb H$ with real projective holonomy and
  $D^*g_{\mathbb H}=\pi^*g$. Projectivizing $D$ produces the required real
  projective atlas, and the pullback identity shows that its underlying
  complex projective structure is induced by $g$.
-/
theorem exists_psl2r_projective_structure_induced_by_metric
    (g : HyperbolicMetric X) :
    ∃ P : PSL2RProjectiveStructure X,
      ComplexProjectiveStructure.IsInducedByHyperbolicMetric
        P.toComplexProjectiveStructure g := by
  let solveSchwarzian :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
    hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem
  let propagateRealMobiusTransitions :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
        X :=
    pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
  let continueAnalytically :
      SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL X
        (metricBoundPartialConverseComponentwiseLocalTransitionModels
          propagateRealMobiusTransitions) :=
    selectedComponentwiseLeftSourcePSLContinuation
  let x₀ : X := Classical.choice inferInstance
  let F :
      HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
        x₀ g
        (metricBoundPartialConverseComponentwiseLocalTransitionModels
          propagateRealMobiusTransitions g) :=
    Classical.choice (continueAnalytically x₀ g)
  let D : HyperbolicDevelopingMap X x₀ g :=
    F.toHyperbolicDevelopingMap
  let P : ProjectivizedHyperbolicDevelopingMap X x₀ g :=
    D.toProjectivized D.projectiveEquivariant
  exact
    ⟨psl2rProjectiveStructureOfProjectivizedDevelopingMap P,
      psl2rProjectiveStructureOfProjectivizedDevelopingMap_isInducedByHyperbolicMetric P⟩

/--
%%handwave
name:
  Hyperbolic metrics induce projective structures
statement:
  Let $g$ be a hyperbolic metric on a Riemann surface $X$. There is
  a complex projective structure $P$ on $X$, induced by a developing map
  $\operatorname{dev}:\widetilde X_{x_0}\to\mathbb H$ for $g$, whose based
  holonomy representation takes values in $\mathrm{PSL}_2(\mathbb R)$.
proof:
  [Solve the local Schwarzian problem to obtain metric-recovering upper-half-plane branches with real Möbius transitions](lean:JJMath.solveLocalSchwarzianProblem). Continue a chosen branch along paths from $x_0$ by composing these transitions. A finite homotopy grid shows that the terminal branch depends only on the endpoint-fixed homotopy class, so continuation defines an equivariant map on $\widetilde X_{x_0}$. Projectivizing this map and composing it with local sections of the covering projection produces the projective atlas; real transition maps give the stated holonomy.
tags:
  milestone
-/
theorem complete_partial_converse_theorem :
    ∀ g : HyperbolicMetric X,
      ∃ P : ComplexProjectiveStructure X,
        P.IsInducedByHyperbolicMetric g ∧
          ∃ x₀ : X, HasPSL2RHolonomy x₀ P := by
  let solveSchwarzian :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem :=
    hyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem
  let propagateRealMobiusTransitions :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
        X :=
    pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
  let continueAnalytically :
      SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL X
        (metricBoundPartialConverseComponentwiseLocalTransitionModels
          propagateRealMobiusTransitions) :=
    selectedComponentwiseLeftSourcePSLContinuation
  let assembleProjectiveAtlas :
      ProjectiveAtlasFromProjectivizedDevelopingMapTheorem X :=
    projectiveAtlasFromProjectivizedDevelopingMapTheorem
  exact
    complete_partial_converse_theorem_of_branch_pre_data_selection_pointed_transitions_component_extension_selected_continuation_psl_projective_atlas
      (canonicalChartedCurvatureBranchPreDataSelectionTheorem_of_localRealBranches
        solveSchwarzian)
      hyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem
      propagateRealMobiusTransitions
      continueAnalytically
      assembleProjectiveAtlas

end HyperbolicMetric

end

end JJMath
