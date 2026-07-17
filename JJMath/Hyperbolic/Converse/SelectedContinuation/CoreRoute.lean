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

/- The interior unit-split branch-data boundary is discharged by explicit
split-reparameterization transport of finite handoff skeletons. -/
theorem selectedComponentwiseLeftSourceInteriorUnitSplitBranchDataWitnessTheorem :
    SelectedComponentwiseLeftSourcePathBasedWeakHandoffInteriorUnitSplitBranchDataWitnessTheorem
      X :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffInteriorUnitSplitBranchDataWitnessTheorem

/-- The monotone prefixed subpath-merge value boundary for the componentwise route. -/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/--
On the componentwise route, the monotone prefixed value witness follows from
the monotone unprefixed branch-data witness by prepending the common prefix
through the actual source chart.
-/
theorem selectedComponentwiseLeftSourceMonotonePrefixedSubpathMergeValueWitness_of_monotoneSubpathMergeBranchData
    (hMerge :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem X) :
    SelectedComponentwiseLeftSourcePathBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessTheorem X :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessTheorem_of_monotoneSubpathMergeBranchData
    hMerge

/-- The normalized unit-split boundary gives the monotone branch-data boundary. -/
theorem selectedComponentwiseLeftSourceMonotoneSubpathMergeBranchDataWitness_of_unitSplit
    (hUnit :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffUnitSplitBranchDataWitnessTheorem X) :
    SelectedComponentwiseLeftSourcePathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem X :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem_of_unitSplit
    hUnit

/-- The interior unit-split boundary gives the unit-split boundary. -/
theorem selectedComponentwiseLeftSourceUnitSplitBranchDataWitness_of_interior
    (hInterior :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffInteriorUnitSplitBranchDataWitnessTheorem X) :
    SelectedComponentwiseLeftSourcePathBasedWeakHandoffUnitSplitBranchDataWitnessTheorem X :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffUnitSplitBranchDataWitnessTheorem_of_interior
    hInterior

/-- The endpoint-normalization boundary for raw-to-public cut paths. -/
def SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] : Prop :=
  SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessTheorem
    X
    (metricBoundPartialConverseComponentwiseLocalTransitionModels
      pointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem)

/-- Endpoint normalization for raw-to-public cut paths is unconditional. -/
theorem selectedComponentwiseLeftSourceHomotopyStripCutEndpointNormalizationValueWitness_unconditional :
    SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessTheorem X :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessTheorem_unconditional

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

omit [RiemannSurface X] in
/--
The componentwise own-split parameter-permutation boundary is unconditional.
-/
theorem selectedComponentwiseLeftSourceMutualVertexRefinementOwnSplitParameterPermutation
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] :
    SelectedComponentwiseLeftSourcePathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationTheorem
      X :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationTheorem

/--
Finite homotopy-grid walks plus same-path terminal-value uniqueness give
selected PSL continuation for the componentwise route.
-/
theorem selectedComponentwiseLeftSourcePSLContinuation_of_homotopyGridWalk_and_samePathTerminalValueUniqueness
    (hGrid :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem X)
    (hUnique :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem X) :
    SelectedComponentwiseLeftSourcePSLContinuationTheorem X :=
  selectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL_of_selectedHomotopyGridWalk_and_selectedSamePathTerminalValueUniqueness
    hGrid hUnique

/--
Finite homotopy-grid walks plus common aligned mutual vertex refinements give
selected PSL continuation for the componentwise route.
-/
theorem selectedComponentwiseLeftSourcePSLContinuation_of_homotopyGridWalk_and_mutualVertexRefinementCommonAlignedSubdivision
    (hGrid :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem X)
    (hAlign :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem X) :
    SelectedComponentwiseLeftSourcePSLContinuationTheorem X :=
  selectedComponentwiseLeftSourcePSLContinuation_of_homotopyGridWalk_and_samePathTerminalValueUniqueness
    hGrid
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedMutualVertexRefinementCommonAlignedSubdivision
      hAlign)

/--
Finite homotopy-grid walks plus own-split parameter alignment give selected
PSL continuation for the componentwise route.
-/
theorem selectedComponentwiseLeftSourcePSLContinuation_of_homotopyGridWalk_and_ownSplitParameterAlignment
    (hGrid :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem X)
    (hAlign :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem X) :
    SelectedComponentwiseLeftSourcePSLContinuationTheorem X :=
  selectedComponentwiseLeftSourcePSLContinuation_of_homotopyGridWalk_and_mutualVertexRefinementCommonAlignedSubdivision
    hGrid
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem_of_selectedOwnSplitParameterAlignment
      hAlign)

/--
Finite homotopy-grid walks plus own-split parameter permutations give selected
PSL continuation for the componentwise route.
-/
theorem selectedComponentwiseLeftSourcePSLContinuation_of_homotopyGridWalk_and_ownSplitParameterPermutation
    (hGrid :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem X)
    (hPerm :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationTheorem X) :
    SelectedComponentwiseLeftSourcePSLContinuationTheorem X :=
  selectedComponentwiseLeftSourcePSLContinuation_of_homotopyGridWalk_and_ownSplitParameterAlignment
    hGrid
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem_of_selectedOwnSplitParameterPermutation
      hPerm)

/--
Elementary grid-move walks plus own-split parameter permutations give selected
PSL continuation for the componentwise route.
-/
theorem selectedComponentwiseLeftSourcePSLContinuation_of_elementaryGridMoveWalk_and_ownSplitParameterPermutation
    (hElementary :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem X)
    (hPerm :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationTheorem X) :
    SelectedComponentwiseLeftSourcePSLContinuationTheorem X :=
  selectedComponentwiseLeftSourcePSLContinuation_of_homotopyGridWalk_and_ownSplitParameterPermutation
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem_of_selectedElementaryGridMoveWalk
      hElementary)
    hPerm

/--
Elementary grid-move walks give selected PSL continuation for the componentwise
route; the own-split parameter-permutation part is unconditional.
-/
theorem selectedComponentwiseLeftSourcePSLContinuation_of_elementaryGridMoveWalk
    (hElementary :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem X) :
    SelectedComponentwiseLeftSourcePSLContinuationTheorem X :=
  selectedComponentwiseLeftSourcePSLContinuation_of_elementaryGridMoveWalk_and_ownSplitParameterPermutation
    hElementary
    (selectedComponentwiseLeftSourceMutualVertexRefinementOwnSplitParameterPermutation X)

/--
Chart-grid local replacement gives selected PSL continuation for the
componentwise route; compactness of the homotopy square supplies the finite
chart grid.
-/
theorem selectedComponentwiseLeftSourcePSLContinuation_of_homotopyChartGridMove
    (hChartGrid :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartGridMovePrincipleTheorem X) :
    SelectedComponentwiseLeftSourcePSLContinuationTheorem X :=
  selectedComponentwiseLeftSourcePSLContinuation_of_elementaryGridMoveWalk
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem_of_selectedHomotopyChartGridMove
      hChartGrid)

/--
One-strip chart-grid replacement gives selected PSL continuation for the
componentwise route by finite concatenation of homotopy strips.
-/
theorem selectedComponentwiseLeftSourcePSLContinuation_of_homotopyChartStripMove
    (hStrip :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripMovePrincipleTheorem X) :
    SelectedComponentwiseLeftSourcePSLContinuationTheorem X :=
  selectedComponentwiseLeftSourcePSLContinuation_of_homotopyChartGridMove
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartGridMovePrincipleTheorem_of_selectedHomotopyChartStripMove
      hStrip)

/--
One-column chart-grid replacement gives selected PSL continuation for the
componentwise route by finite concatenation across columns and strips.
-/
theorem selectedComponentwiseLeftSourcePSLContinuation_of_homotopyChartStripColumnMove
    (hColumn :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnMovePrincipleTheorem X) :
    SelectedComponentwiseLeftSourcePSLContinuationTheorem X :=
  selectedComponentwiseLeftSourcePSLContinuation_of_homotopyChartStripMove
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripMovePrincipleTheorem_of_selectedHomotopyChartStripColumnMove
      hColumn)

/--
Decomposed one-column witnesses plus exact cut-reparameterization transfer
give the public one-column terminal-value witness boundary.
-/
theorem selectedComponentwiseLeftSourceHomotopyChartStripColumnValueWitness_of_decomposed_and_cutReparam
    (hDecomp :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessTheorem X)
    (hCut :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferTheorem X) :
    SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnValueWitnessTheorem X :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnValueWitnessTheorem_of_selectedDecomposed_and_selectedCutReparam
    hDecomp hCut

/--
Explicit cut-reparameterization witnesses imply the selected cut-transfer
boundary; same-path uniqueness has already been discharged in `Continuation`.
-/
theorem selectedComponentwiseLeftSourceHomotopyChartStripColumnCutReparam_of_explicitValueWitness
    (hExplicit :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem X) :
    SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferTheorem X :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferTheorem_of_explicitValueWitness
    hExplicit

/--
The explicit cut-reparameterization witness follows from monotone subpath-merge
data and endpoint normalization.
-/
theorem selectedComponentwiseLeftSourceHomotopyChartStripColumnCutReparamExplicitValueWitness_of_monotoneSubpathMerge_and_endpointNormalization
    (hMerge :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem X)
    (hNormalize :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessTheorem X) :
    SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem X :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem_of_monotoneSubpathMerge_and_endpointNormalization
    hMerge
    (selectedComponentwiseLeftSourceMonotonePrefixedSubpathMergeValueWitness_of_monotoneSubpathMergeBranchData
      hMerge)
    hNormalize

/--
The public cut-reparameterization witness follows from monotone subpath-merge;
endpoint normalization is now unconditional.
-/
theorem selectedComponentwiseLeftSourceHomotopyChartStripColumnCutReparamExplicitValueWitness_of_monotoneSubpathMerge
    (hMerge :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem X) :
    SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem X :=
  selectedComponentwiseLeftSourceHomotopyChartStripColumnCutReparamExplicitValueWitness_of_monotoneSubpathMerge_and_endpointNormalization
    hMerge
    selectedComponentwiseLeftSourceHomotopyStripCutEndpointNormalizationValueWitness_unconditional

/-- The selected decomposed one-column witness theorem is unconditional. -/
theorem selectedComponentwiseLeftSourceHomotopyChartStripColumnDecomposedValueWitness_unconditional :
    SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessTheorem X :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessTheorem_unconditional

/--
After the exact componentwise suffix append, only cut-reparameterization
transfer is needed to get the public one-column terminal-value witness
boundary.
-/
theorem selectedComponentwiseLeftSourceHomotopyChartStripColumnValueWitness_of_cutReparam
    (hCut :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferTheorem X) :
    SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnValueWitnessTheorem X :=
  selectedComponentwiseLeftSourceHomotopyChartStripColumnValueWitness_of_decomposed_and_cutReparam
    selectedComponentwiseLeftSourceHomotopyChartStripColumnDecomposedValueWitness_unconditional
    hCut

/--
After the exact componentwise suffix append and same-path uniqueness, only the
explicit raw/decomposed cut witness remains to get the public one-column
terminal-value witness boundary.
-/
theorem selectedComponentwiseLeftSourceHomotopyChartStripColumnValueWitness_of_cutReparamExplicitValueWitness
    (hExplicit :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem X) :
    SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnValueWitnessTheorem X :=
  selectedComponentwiseLeftSourceHomotopyChartStripColumnValueWitness_of_cutReparam
    (selectedComponentwiseLeftSourceHomotopyChartStripColumnCutReparam_of_explicitValueWitness
      hExplicit)

/--
One-column terminal-value witnesses give selected PSL continuation for the
componentwise route; arbitrary skeleton choices are removed by same-path
uniqueness.
-/
theorem selectedComponentwiseLeftSourcePSLContinuation_of_homotopyChartStripColumnValueWitness
    (hValue :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnValueWitnessTheorem X) :
    SelectedComponentwiseLeftSourcePSLContinuationTheorem X :=
  selectedComponentwiseLeftSourcePSLContinuation_of_homotopyChartStripColumnMove
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnMovePrincipleTheorem_of_selectedHomotopyChartStripColumnValueWitness
      hValue)

/--
An explicit cut-reparameterization witness gives selected PSL continuation for
the componentwise route.
-/
theorem selectedComponentwiseLeftSourcePSLContinuation_of_homotopyChartStripColumnCutReparamExplicitValueWitness
    (hExplicit :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem X) :
    SelectedComponentwiseLeftSourcePSLContinuationTheorem X :=
  selectedComponentwiseLeftSourcePSLContinuation_of_homotopyChartStripColumnValueWitness
    (selectedComponentwiseLeftSourceHomotopyChartStripColumnValueWitness_of_cutReparamExplicitValueWitness
      hExplicit)

/--
Monotone subpath-merge data suffices for selected PSL continuation.
-/
theorem selectedComponentwiseLeftSourcePSLContinuation_of_monotoneSubpathMerge
    (hMerge :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem X) :
    SelectedComponentwiseLeftSourcePSLContinuationTheorem X :=
  selectedComponentwiseLeftSourcePSLContinuation_of_homotopyChartStripColumnCutReparamExplicitValueWitness
    (selectedComponentwiseLeftSourceHomotopyChartStripColumnCutReparamExplicitValueWitness_of_monotoneSubpathMerge
      hMerge)

/--
The normalized unit-split branch-data boundary suffices for selected PSL
continuation.
-/
theorem selectedComponentwiseLeftSourcePSLContinuation_of_unitSplit
    (hUnit :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffUnitSplitBranchDataWitnessTheorem X) :
    SelectedComponentwiseLeftSourcePSLContinuationTheorem X :=
  selectedComponentwiseLeftSourcePSLContinuation_of_monotoneSubpathMerge
    (selectedComponentwiseLeftSourceMonotoneSubpathMergeBranchDataWitness_of_unitSplit
      hUnit)

/--
The interior normalized unit-split branch-data boundary suffices for selected
PSL continuation.
-/
theorem selectedComponentwiseLeftSourcePSLContinuation_of_interiorUnitSplit
    (hInterior :
      SelectedComponentwiseLeftSourcePathBasedWeakHandoffInteriorUnitSplitBranchDataWitnessTheorem X) :
    SelectedComponentwiseLeftSourcePSLContinuationTheorem X :=
  selectedComponentwiseLeftSourcePSLContinuation_of_unitSplit
    (selectedComponentwiseLeftSourceUnitSplitBranchDataWitness_of_interior hInterior)

/--
Completed metric-bound partial converse with the conclusion phrased as a
`PSL(2, ℝ)`-projective structure.  The proof chooses the H-valued developing
map obtained by analytic continuation and uses its real-equivariant branch
atlas directly.
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
    selectedComponentwiseLeftSourcePSLContinuation_of_interiorUnitSplit
      selectedComponentwiseLeftSourceInteriorUnitSplitBranchDataWitnessTheorem
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
    selectedComponentwiseLeftSourcePSLContinuation_of_interiorUnitSplit
      selectedComponentwiseLeftSourceInteriorUnitSplitBranchDataWitnessTheorem
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
