import JJMath.Hyperbolic.Converse.Continuation.CanonicalLoopPSL

/-!
# Split analytic continuation targets for the partial converse
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/--
Reduced PSL-valued local-transition continuation fields on the canonical cover
for a fixed selected local-transition atlas.

%%handwave
name: Equivariant continuation fields for a selected local atlas
statement:
  For every basepoint $x_0$ and hyperbolic metric $g$, there exist a map
  $\operatorname{dev}:\widetilde X_{x_0}\to\mathbb H$ and real projective
  holonomy such that $\operatorname{dev}$ is deck-equivariant and locally a
  real Möbius transform of a chart in the selected atlas for $g$.
-/
def SelectedLocalTransitionModelContinuationDerivedRegularityCanonicalCoverMetricFieldTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (HyperbolicDevelopingLocalTransitionContinuationDataFieldsOnCanonicalCoverMetricWithDerivedRegularityPSL
        x₀ g (chosenLocalModels g))

/--
PSL-valued path-class monodromy data only for a fixed selected
local-transition atlas.

%%handwave
name: Path-class continuation with real projective monodromy
statement:
  For every $x_0$ and $g$, the selected atlas admits continuation values
  $V(x,[p])$ with local terminal-branch formulae and a representation
  $\rho:\pi_1(X,x_0)\to\mathrm{PSL}_2(\mathbb R)$ satisfying
  $V(x,\gamma^{-1}[p])=\rho(\gamma)V(x,[p])$.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathClassMonodromyTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathClassLocalTransitionAnalyticContinuationMonodromyDataPSL
        x₀ g (chosenLocalModels g))

/--
Selected canonical-terminal-sheet agreement for based weak handoff terminal
sheets, before PSL loop monodromy/equivariance is imposed.

%%handwave
name: Canonical-sheet agreement of pathwise continuation branches
statement:
  For every $x_0$ and $g$, one can choose a finite weak-handoff continuation
  skeleton along every based path so that all representatives of a point of
  the canonical cover give the same terminal branch formula on each canonical
  terminal sheet.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g))

/--
Selected terminal-sheet homotopy principle for based weak handoff skeletons.

This is the implementation-facing form of the finite homotopy-grid uniqueness
argument: it must hold for any choices of based weak handoff skeletons along
representative paths.

%%handwave
name: Homotopy compatibility on terminal continuation sheets
statement:
  For every $x_0,g$ and every choice of weak-handoff skeleton along each
  based path, endpoint-fixed homotopy to a path followed by a local path
  inside its terminal sheet implies equality of the two terminal branch
  values at the new endpoint.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyPrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected finite homotopy-grid walk principle for based weak handoff skeletons.

%%handwave
name: Finite homotopy-grid invariance for selected continuation chains
statement:
  For every $x_0,g$, every pathwise choice of continuation skeletons, and
  endpoint-fixed homotopic paths $p,q:x_0\rightsquigarrow x$, there exists a
  finite homotopy-grid walk from $p$ to $q$ whose moves preserve the terminal
  branch formula.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffHomotopyGridWalkPrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected elementary homotopy-grid move walk principle for based weak handoff
skeletons.

%%handwave
name: Elementary grid-move invariance for selected continuation chains
statement:
  For every $x_0,g$, every pathwise choice of continuation skeletons, and
  endpoint-fixed homotopic paths $p,q:x_0\rightsquigarrow x$, there exists a
  finite walk from $p$ to $q$ by elementary grid moves preserving terminal
  branch formulae.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffElementaryGridMoveWalkPrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected one-column terminal-value witness theorem for based weak handoff
skeletons.

%%handwave
name: Equal continuation values across one homotopy-grid column
statement:
  For every chart-contained rectangle in a subdivided endpoint-fixed
  homotopy, there exist weak-handoff skeletons on its adjacent normalized cut
  paths with equal terminal values.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnValueWitnessPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected decomposed one-column terminal-value witness theorem for based weak
handoff skeletons.

%%handwave
name: Equal continuation values on decomposed column paths
statement:
  For every chart-contained rectangle in a subdivided endpoint-fixed
  homotopy, there exist skeletons on the decomposed top and bottom column
  paths, with their common prefix and suffix, whose terminal values are equal.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnDecomposedValueWitnessPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected exact transfer from decomposed one-column witnesses to the public
cut-path witnesses.

%%handwave
name: Terminal-value transfer from decomposed columns to cut paths
statement:
  For every chart-contained homotopy rectangle, every skeleton on either
  decomposed column path has a skeleton on the corresponding normalized cut
  path with the same terminal value.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamValueTransferPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected explicit witness form of the cut-reparameterization boundary.

%%handwave
name: Equal-valued witnesses for column reparameterization
statement:
  For every chart-contained homotopy rectangle, there is an equal-valued pair
  of skeletons on the decomposed top path and its upper cut path, and an
  equal-valued pair on the decomposed bottom path and its lower cut path.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnCutReparamExplicitValueWitnessPrinciple
      x₀ g (chosenLocalModels g)

/-- Selected normalized unit-split branch-data boundary.

%%handwave
name: A unit-interval split preserves terminal branch data
statement:
  For every path $\gamma$ and $r\in[0,1]$, there are continuation skeletons
  over $\gamma|_{[0,r]}*\gamma|_{[r,1]}$ and $\gamma|_{[0,1]}$ with the same
  terminal chart and accumulated real Möbius transformation.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffUnitSplitBranchDataWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffUnitSplitBranchDataWitnessPrinciple
      g (chosenLocalModels g)

/-- Selected interior normalized unit-split branch-data boundary.

%%handwave
name: An interior unit split preserves terminal branch data
statement:
  For every path $\gamma$ and $0<r<1$, there are continuation skeletons over
  $\gamma|_{[0,r]}*\gamma|_{[r,1]}$ and $\gamma|_{[0,1]}$ with identical
  terminal chart and accumulated real Möbius transformation.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffInteriorUnitSplitBranchDataWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffInteriorUnitSplitBranchDataWitnessPrinciple
      g (chosenLocalModels g)

/-- Selected monotone subpath-merge branch-data boundary.

%%handwave
name: Monotone subpath merging preserves terminal branch data
statement:
  For every path $\gamma$ and $t_0\le t_1\le t_2$, there are skeletons over
  $\gamma|_{[t_0,t_1]}*\gamma|_{[t_1,t_2]}$ and
  $\gamma|_{[t_0,t_2]}$ with identical terminal branch data.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffMonotoneSubpathMergeBranchDataWitnessPrinciple
      g (chosenLocalModels g)

/-- Selected monotone prefixed subpath-merge value boundary.

%%handwave
name: Prefixed monotone subpath merging preserves terminal value
statement:
  If a path ending at $\gamma(t_0)$ is prefixed to the two sides of a
  monotone subpath merge $t_0\le t_1\le t_2$, then suitable continuation
  skeletons over the split and merged paths have equal terminal values.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffMonotonePrefixedSubpathMergeValueWitnessPrinciple
      g (chosenLocalModels g)


/-- Selected endpoint-normalization boundary from raw cut paths to public cuts.

%%handwave
name: Endpoint normalization preserves strip-cut continuation values
statement:
  For every endpoint-fixed homotopy $F$ and $a,b,r\in[0,1]$, there are
  skeletons over the raw strip-cut path and its endpoint-normalized version
  whose terminal values agree.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffHomotopyStripCutEndpointNormalizationValueWitnessPrinciple
      x₀ g (chosenLocalModels g)


/--
Selected one-column chart-grid replacement principle for based weak handoff
skeletons.

%%handwave
name: One homotopy-grid column yields an elementary-move walk
statement:
  For every pathwise choice of skeletons and every chart-contained rectangle
  in a subdivided homotopy, the upper and lower cut paths of that rectangle
  are joined by a finite elementary grid-move walk.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripColumnMovePrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripColumnMovePrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected one-strip chart-grid replacement principle for based weak handoff
skeletons.

%%handwave
name: One chart-subdivided homotopy strip yields an elementary-move walk
statement:
  If every rectangle in one horizontal strip of a finite homotopy subdivision
  lies in a selected chart, then the two boundary rows of the strip are joined
  by a finite elementary grid-move walk.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartStripMovePrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffHomotopyChartStripMovePrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected chart-grid local replacement principle for based weak handoff
skeletons.

%%handwave
name: A finite chart grid yields a pathwise elementary-move walk
statement:
  If an endpoint-fixed homotopy has a finite monotone rectangular
  subdivision whose cells lie in selected charts, then its endpoint paths are
  joined by a finite elementary grid-move walk.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartGridMovePrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffHomotopyChartGridMovePrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected local-extension compatibility for terminal-sheet paths.

%%handwave
name: Continuation is unchanged by extension inside a terminal sheet
statement:
  For every chosen skeleton along $p$ and every point $y$ of its terminal
  sheet, the fresh skeleton chosen along $p$ followed by the canonical path
  to $y$ has the same terminal branch value at $\pi(y)$ as the original
  skeleton.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (basedWeakHandoffAlong :
      ∀ {x : X} (p : Path x₀ x),
        PathLocalTransitionModelBasedWeakHandoffSkeleton
          x₀ g (chosenLocalModels g) p),
    PathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionPrinciple
      x₀ g (chosenLocalModels g) basedWeakHandoffAlong

/--
Selected same-path terminal-value uniqueness for based weak handoff skeletons.

This is the choice-independence boundary left after terminal-sheet extensions
are constructed explicitly.

%%handwave
name: Continuation along a fixed path has a unique terminal value
statement:
  For every $x_0,g$, path $p:x_0\rightsquigarrow x$, and two weak-handoff
  continuation skeletons $S,T$ over $p$, their terminal values are equal:
  $v(S)=v(T)$.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected mutual vertex-refinement terminal-value comparison for based weak
handoff skeletons over the same representative path.

%%handwave
name: Mutual vertex refinement preserves the common terminal value
statement:
  For skeletons $S,T$ over the same path, insert all vertices of $T$ into
  $S$ and all vertices of $S$ into $T$; the resulting two refinements have
  equal terminal values.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementTerminalValueTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffMutualVertexRefinementTerminalValuePrinciple
      x₀ g (chosenLocalModels g)

/--
Selected mutual vertex-refinement aligned-subdivision comparison.

This is the selected theorem-package form of the remaining combinatorial
boundary: the branch comparison is already local-analytic, so the only data
requested here is equality of the two mutually refined parameter lists.

%%handwave
name: Mutual refinements admit a common aligned subdivision
statement:
  For skeletons $S,T$ over one path, their mutual vertex refinements can be
  moved, without changing terminal value, to skeletons $U,V$ of equal length
  whose subdivision parameters agree at every index.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected own-split parameter-alignment comparison.

This is the sharper finite-subdivision boundary behind common aligned mutual
vertex refinements: mutual endpoint-chart insertion is followed by one plain
split along the original vertices on each side; the lengths are already a
theorem, so this package only asks for pointwise agreement of the resulting
parameter lists.

%%handwave
name: Own-split mutual refinements have identical parameters
statement:
  After inserting all vertices of $T$ into $S$ and splitting again at the
  vertices of $S$, and performing the symmetric construction on $T$, the two
  resulting subdivision parameters agree pointwise.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected own-split parameter-permutation comparison.

This is the multiset form of the own-split boundary; sortedness converts it to
the pointwise alignment theorem above.

%%handwave
name: Own-split mutual refinements have the same parameter multiset
statement:
  For skeletons $S,T$ over one path, the parameter lists obtained by mutual
  vertex insertion followed by splitting at each skeleton's own vertices are
  permutations of one another.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    PathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationPrinciple
      x₀ g (chosenLocalModels g)

/--
Selected canonical-terminal-sheet agreement with PSL monodromy for the
constructed canonical-cover map.

%%handwave
name: Canonical-sheet continuation with real projective monodromy
statement:
  For every $x_0$ and $g$, there exist canonical-sheet agreement data and a
  representation $\rho:\pi_1(X,x_0)\to\mathrm{PSL}_2(\mathbb R)$ such that
  the induced map $\operatorname{dev}:\widetilde X_{x_0}\to\mathbb H$ is
  equivariant under deck transformations by $\rho$.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementMonodromyTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementMonodromyDataPSL
        x₀ g (chosenLocalModels g))

/--
Selected transition-adjusted terminal-Mobius PSL covariance for
canonical-terminal-sheet agreement data.

%%handwave
name: Transition-adjusted covariance of terminal Möbius classes
statement:
  For every canonical-sheet continuation and every loop representing
  $\gamma^{-1}$, there exist real projective holonomy $\rho$ and a transition
  $A$ between the old and loop-prepended terminal charts such that
  $[M_{\gamma*p}A]=\rho(\gamma)[M_p]$ for every based path $p$.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementTerminalTransitionProjectionEquivarianceDataPSL
        agreementContinuation)

/--
Selected terminal-Mobius PSL covariance using the automatic endpoint chart
transition supplied by the local-transition atlas.

%%handwave
name: Covariance using the canonical terminal-chart transition
statement:
  Every canonical-sheet continuation admits real projective holonomy
  $\rho$ such that, for the terminal-chart transition $A_{\gamma,p}$ selected
  by the local atlas,
  $[M_{\gamma*p}A_{\gamma,p}]=\rho(\gamma)[M_p]$.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionEquivarianceDataPSL
        agreementContinuation)

/--
Selected automatic endpoint-transition terminal-Mobius PSL covariance with
holonomy derived from base-loop terminal continuation.

%%handwave
name: Terminal covariance for the holonomy derived from loop continuation
statement:
  For every canonical-sheet continuation, the projective class obtained from
  continuing the base normalization path around a loop is the value of a
  group representation $H$, and every path satisfies
  $[M_{\gamma*p}A_{\gamma,p}]=H(\gamma)[M_p]$.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementAutomaticTerminalTransitionProjectionDerivedHolonomyDataPSL
        agreementContinuation)

/--
Selected reduced derived-holonomy PSL covariance for canonical-sheet
agreement data.  The PSL identity and multiplication laws are recovered from
the derived loop-terminal classes, so this is the smaller monodromy boundary.

%%handwave
name: Covariance under the derived loop-terminal holonomy
statement:
  For every canonical-sheet continuation, every loop representing
  $\gamma^{-1}$, and every based path $p$, the canonical endpoint transition
  satisfies $[M_{\gamma*p}A_{\gamma,p}]=H(\gamma)[M_p]$, where $H$ is the
  projective loop-terminal class derived from the base normalization path.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementReducedDerivedHolonomyDataPSL
        agreementContinuation)

/--
Selected canonical-loop covariance for canonical-sheet agreement data.  This
is smaller than reduced derived-holonomy covariance: it only asks for the
covariance formula for the canonical loop representative selected by
`Quot.out`.

%%handwave
name: Covariance along canonical loop representatives
statement:
  For every canonical-sheet continuation, loop class $\gamma$, and based
  path $p$, continuation along the fixed representative $L_\gamma$ obeys
  $[M_{L_\gamma*p}A_{p,L_\gamma*p}]=H(\gamma)[M_p]$, with $H$ the derived
  loop-terminal class.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopCovarianceDataPSL
        agreementContinuation)

/--
Selected normalized canonical-loop projection propagation for
canonical-sheet agreement data.  This is the path-propagation form of the
canonical-loop covariance boundary.

%%handwave
name: Path independence of normalized canonical-loop transport
statement:
  For every canonical-sheet continuation and loop class $\gamma$, the
  normalized transport
  $N_\gamma(p)=[M_{L_\gamma*p}A_{p,L_\gamma*p}][M_p]^{-1}$ has the same
  value for every based path $p$ as for the base normalization path.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionPropagationDataPSL
        agreementContinuation)

/--
Selected canonical-cover constancy of the normalized canonical-loop
projection.

%%handwave
name: Constancy of normalized loop transport on the canonical cover
statement:
  For every canonical-sheet continuation and $\gamma\in\pi_1(X,x_0)$, the
  normalized canonical-loop transport $N_\gamma(y)$ has the same value at
  every $y\in\widetilde X_{x_0}$ as at the distinguished base lift.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionConstancyOnCoverDataPSL
        agreementContinuation)

/--
Selected local constancy on the canonical cover of the normalized
canonical-loop projection.

%%handwave
name: Local constancy of normalized loop transport
statement:
  For every canonical-sheet continuation and $\gamma\in\pi_1(X,x_0)$, the
  normalized canonical-loop transport
  $N_\gamma:\widetilde X_{x_0}\to\mathrm{PSL}_2(\mathbb R)$ is locally
  constant.
-/
def SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverTheoremPSL
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g) : Prop :=
  ∀ (x₀ : X) (g : HyperbolicMetric X)
    (agreementContinuation :
      PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementData
        x₀ g (chosenLocalModels g)),
    Nonempty
      (PathLocalTransitionBasedWeakHandoffCanonicalSheetAgreementCanonicalLoopNormalizedProjectionLocalConstancyOnCoverDataPSL
        agreementContinuation)

/--
Selected elementary grid-move walks imply the selected finite homotopy-grid
walk principle.

%%handwave
name: Elementary grid moves give homotopy-grid invariance
statement:
  If every pair of endpoint-fixed homotopic paths is connected by a finite
  elementary grid-move walk, then it is connected by a finite homotopy-grid
  walk preserving terminal branch formulae.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem_of_selectedElementaryGridMoveWalk
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hElementary :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffHomotopyGridWalkPrinciple_of_elementaryGridMoveWalkPrinciple
      (hElementary x₀ g basedWeakHandoffAlong)





/--
Selected chart-grid local replacement implies selected elementary grid-move
walks; compactness of the homotopy square supplies the finite chart grid.

%%handwave
name: Local chart-grid replacement gives elementary-move invariance
statement:
  If every finite chart subdivision of a path homotopy yields a local
  replacement walk, then compactness supplies such a subdivision for every
  endpoint-fixed homotopy, hence an elementary-move walk between its boundary
  paths.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem_of_selectedHomotopyChartGridMove
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hChartGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyChartGridMovePrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffElementaryGridMoveWalkPrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffElementaryGridMoveWalkPrinciple_of_homotopyChartGridMovePrinciple
      (hChartGrid x₀ g basedWeakHandoffAlong)

/--
Selected finite homotopy-grid walks plus selected local extension imply the
selected terminal-sheet homotopy principle.

%%handwave
name: Grid invariance and local extension give terminal-sheet compatibility
statement:
  If homotopic paths are connected by terminal-value-preserving grid walks
  and continuation is unchanged by extension inside a terminal sheet, then
  homotopic terminal-sheet extensions have equal terminal branch values.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedHomotopyGridWalk_and_selectedLocalExtension
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hLocal :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffTerminalSheetHomotopyPrinciple_of_homotopyGridWalk_and_localExtension
      basedWeakHandoffAlong
      (hGrid x₀ g basedWeakHandoffAlong)
      (hLocal x₀ g basedWeakHandoffAlong)

/--
Selected same-path terminal-value uniqueness gives selected terminal-sheet
local extension, using the explicit terminal-extension skeleton.

%%handwave
name: Same-path uniqueness gives terminal-sheet extension compatibility
statement:
  If all weak-handoff skeletons over a fixed path have the same terminal
  value, then the chosen skeleton along a path extended inside its terminal
  sheet agrees with the explicit terminal-extension skeleton and therefore
  with the original terminal branch.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem_of_selectedSamePathTerminalValueUniqueness
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hUnique :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem
      X chosenLocalModels := by
  intro x₀ g basedWeakHandoffAlong
  exact
    pathLocalTransitionBasedWeakHandoffTerminalSheetLocalExtensionPrinciple_of_samePathTerminalValueUniqueness
      (hUnique x₀ g)

/--
Selected own-split parameter alignment implies selected common aligned mutual
vertex refinements.

%%handwave
name: Own-split alignment gives common aligned mutual refinements
statement:
  If the canonical own-split mutual refinements of any two skeletons have
  pointwise equal parameters, then those refinements furnish a pair of
  terminal-value-preserving common aligned subdivisions.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem_of_selectedOwnSplitParameterAlignment
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAlign :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionPrinciple_of_ownSplitParameterAlignment
      (hAlign x₀ g)


/--
Selected own-split parameter permutations imply selected own-split parameter
alignment.

%%handwave
name: Parameter permutation gives pointwise own-split alignment
statement:
  If the two own-split mutual refinements have permuted parameter lists, then
  their weakly increasing parameter lists agree pointwise and hence define
  aligned subdivisions.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem_of_selectedOwnSplitParameterPermutation
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hPerm :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterPermutationTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffMutualVertexRefinementOwnSplitParameterAlignmentPrinciple_of_parameterPermutation
      (hPerm x₀ g)

/--
Selected mutual vertex-refinement comparison implies selected same-path
terminal-value uniqueness.

%%handwave
name: Mutual-refinement equality gives same-path uniqueness
statement:
  If the two mutual vertex refinements of any skeletons $S,T$ over the same
  path have equal terminal values, then insertion preserves each original
  terminal value and therefore $v(S)=v(T)$.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedMutualVertexRefinementTerminalValue
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hMutual :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementTerminalValueTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffSamePathTerminalValueUniquenessPrinciple_of_mutualVertexRefinementTerminalValue
      (hMutual x₀ g)

/--
Selected aligned mutual vertex refinements give selected mutual-refinement
terminal-value comparison.

%%handwave
name: Common aligned refinements give mutual-refinement equality
statement:
  If the mutual refinements of $S,T$ can be moved without changing terminal
  value to a common aligned subdivision, then local projective transition
  comparison on the aligned pair yields equality of the two refined terminal
  values.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementTerminalValueTheorem_of_selectedMutualVertexRefinementCommonAlignedSubdivision
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAlign :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementTerminalValueTheorem
      X chosenLocalModels := by
  intro x₀ g
  exact
    pathLocalTransitionBasedWeakHandoffMutualVertexRefinementTerminalValuePrinciple_of_mutualVertexRefinementCommonAlignedSubdivision
      (hAlign x₀ g)

/--
Selected aligned mutual vertex refinements give selected same-path
terminal-value uniqueness.

%%handwave
name: Common aligned refinements give same-path terminal-value uniqueness
statement:
  If every pair of skeletons over one path admits terminal-value-preserving
  common aligned mutual refinements, then every such pair has equal terminal
  value.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedMutualVertexRefinementCommonAlignedSubdivision
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hAlign :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementCommonAlignedSubdivisionTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem_of_selectedMutualVertexRefinementTerminalValue
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffMutualVertexRefinementTerminalValueTheorem_of_selectedMutualVertexRefinementCommonAlignedSubdivision
      hAlign)

/--
Selected finite homotopy-grid walks plus selected same-path terminal-value
uniqueness imply the selected terminal-sheet homotopy principle.

%%handwave
name: Grid invariance and same-path uniqueness give terminal-sheet compatibility
statement:
  If homotopic paths admit terminal-value-preserving grid walks and
  continuation over a fixed path has a unique terminal value, then
  continuation is compatible with homotopic local extensions inside terminal
  sheets.
-/
def selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedHomotopyGridWalk_and_selectedSamePathTerminalValueUniqueness
    {chosenLocalModels :
      ∀ (g : HyperbolicMetric X),
        HyperbolicLocalModelLocalTransitionAtlas X g}
    (hGrid :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffHomotopyGridWalkPrincipleTheorem
        X chosenLocalModels)
    (hUnique :
      SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffSamePathTerminalValueUniquenessTheorem
        X chosenLocalModels) :
    SelectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem
      X chosenLocalModels :=
  selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetHomotopyPrincipleTheorem_of_selectedHomotopyGridWalk_and_selectedLocalExtension
    hGrid
    (selectedLocalTransitionModelAnalyticContinuationPathBasedWeakHandoffTerminalSheetLocalExtensionPrincipleTheorem_of_selectedSamePathTerminalValueUniqueness
      hUnique)

end HyperbolicMetric

end

end JJMath
