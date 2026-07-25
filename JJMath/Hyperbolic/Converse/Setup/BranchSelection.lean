import JJMath.Hyperbolic.Converse.Setup.OverlapStability

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

/--
Trivial componentwise topology of the selected surface overlaps.

For analytic continuation one should work on the connected component of the
overlap containing the transition point.  On a locally path-connected surface,
those components of open overlaps are open; they are preconnected by
definition of `connectedComponentIn`.

%%handwave
name: Trivial componentwise topology of the selected surface overlaps
statement:
  Trivial componentwise topology of the selected surface overlaps. For analytic continuation one
  should work on the connected component of the overlap containing the transition point. On a
  locally path-connected surface, those components of open overlaps are open; they are
  preconnected by definition of the connected component.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapComponentsGood
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas) :
    Prop :=
  ∀ x y p : X,
    IsOpen
      (connectedComponentIn
        ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain)
        p) ∧
      IsPreconnected
        (connectedComponentIn
          ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
            (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain)
          p)

/--
%%handwave
name: Components of selected branch overlaps are open and preconnected
statement:
  On a locally path-connected surface, for any two selected local upper-half-plane chart domains $U_x,U_y$ and any point $p$, the component of $p$ in $U_x\cap U_y$ is open and preconnected.
proof:
  The intersection $U_x\cap U_y$ is open. In a locally path-connected space its component containing $p$ is open, and every connected component in a set is preconnected.
-/
theorem surfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapComponentsGood
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [LocPathConnectedSpace X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapComponentsGood preData := by
  intro x y p
  exact
    ⟨((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).isOpen_domain.inter
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).isOpen_domain).connectedComponentIn,
      isPreconnected_connectedComponentIn⟩

/--
Componentwise selected-overlap propagation for one concrete surface predata
object.

This is the selected-predata version of the honest analytic-continuation
boundary: a pointed transition propagates only on the connected component of
the selected overlap which contains the pointed transition.

%%handwave
name: Componentwise selected-overlap propagation for one concrete surface predata object
statement:
  Componentwise selected-overlap propagation for one concrete surface predata object. This is
  the selected-predata version of the honest analytic-continuation principle: a pointed
  transition propagates only on the connected component of the selected overlap which contains
  the pointed transition.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas) :
    Prop :=
  ∀ x y : X,
    ∀ (A : RealMobiusRepresentative) (x₀ : X),
      HyperbolicLocalChartPointedRealMobiusTransition
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
        A x₀ →
      ∀ z,
        z ∈
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain →
        z ∈
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain →
        z ∈
          connectedComponentIn
            ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
              (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain)
            x₀ →
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).toUpperHalfPlane z =
          realMobiusRepresentativeAction A
            ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).toUpperHalfPlane z)

/--
Pointed real-Mobius transition data at every point of every selected
off-diagonal overlap.

This is stronger than the older nonempty-overlap target because the pointed
transition is required at the overlap point where a local transition chart is
being built.

%%handwave
name: Pointed real-Möbius transition data at every point of every selected off-diagonal overlap
statement:
  Pointed real-Möbius transition data at every point of every selected off-diagonal overlap.
  This is stronger than the older nonempty-overlap assertion because the pointed transition is
  required at the overlap point where a local transition chart is being built.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionsAtOverlapPoints
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas) :
    Prop :=
  ∀ x y : X, x ≠ y →
    ∀ p : X,
      p ∈
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain →
      p ∈
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain →
      ∃ A : RealMobiusRepresentative,
        HyperbolicLocalChartPointedRealMobiusTransition
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
          A p

/--
The selected surface branch predata has local real-Mobius transitions on all
selected overlaps.

%%handwave
name: The selected surface branch predata has local real-Möbius transitions on all selected overlaps
statement:
  The selected surface branch predata has local real-Möbius transitions on all selected
  overlaps.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas) :
    Prop :=
  ∀ x y : X,
    HyperbolicLocalChart.HasLocalRealMobiusTransition
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)

/--
Selected surface branch predata with local real-Mobius transitions gives the
natural local-transition local-model atlas.

%%handwave
name: Selected surface branch predata with local real-Möbius transitions gives the natural local-transition local-model atlas
statement:
  Selected surface branch predata with local real-Möbius transitions gives the natural
  local-transition local-model atlas.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreData_toHyperbolicLocalModelLocalTransitionAtlas
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hTransition :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions
        preData) :
    HyperbolicLocalModelLocalTransitionAtlas X g where
  chartAt x :=
    ((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart
  mem_chartAt_domain := by
    intro x
    change x ∈
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).pullbackFormula).domain
    exact
      ((preData.toSurfaceSchwarzianPointedBranchPreData).toRestrictedMetricFormulaAtlas).mem_formulaAt_domain
        x
  transition_localRealMobius := hTransition

/--
Selected surface branch data with the natural local-transition compatibility.

This is the replacement local output for the componentwise route: it keeps the
actual selected branch predata and asks only for local real-Mobius transition
data on its overlaps.
-/
structure SurfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- The selected coordinate branch atlases and open restricted domains. -/
  preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas
  /-- The selected shrunk local surface charts have local real-Mobius transitions. -/
  local_transition :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions
      preData

namespace SurfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

/-- The local-transition local-model atlas produced by the selected branches.

%%handwave
name: The local-transition local-model atlas produced by the selected branches
statement:
  The local-transition local-model atlas produced by the selected branches.
-/
def toHyperbolicLocalModelLocalTransitionAtlas
    (S :
      SurfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection
        metricFormulaAtlas) :
    HyperbolicLocalModelLocalTransitionAtlas X g :=
  surfaceRealUpperHalfPlaneBranchAtlasPreData_toHyperbolicLocalModelLocalTransitionAtlas
    S.preData S.local_transition

end SurfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection

/--
The global componentwise pointed propagation theorem implies its selected
predata version.

%%handwave
name: The global componentwise pointed propagation theorem implies its selected predata version
statement:
  The global componentwise pointed propagation theorem implies its selected predata version.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents_of_global
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents
      preData := by
  intro x y A x₀ hpoint z hzU hzV hzComponent
  exact
    hExtend g
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
      A x₀ hpoint z hzU hzV hzComponent

/--
Global pointed real-Mobius matching for hyperbolic local charts gives pointed
transitions at every point of every selected off-diagonal overlap.

%%handwave
name: Global pointed real-Möbius matching for hyperbolic local charts gives pointed transitions at every point of every selected off-diagonal overlap
statement:
  Global pointed real-Möbius matching for hyperbolic local charts gives pointed transitions at
  every point of every selected off-diagonal overlap.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionsAtOverlapPoints_of_localChartPointedTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionsAtOverlapPoints
      preData := by
  intro x y _hxy p hpU hpV
  exact
    hPoint g
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
      p hpU hpV

/--
Pointed transitions at overlap points plus componentwise propagation produce
local real-Mobius transitions on the selected surface overlaps.

%%handwave
name: Pointed transitions at overlap points plus componentwise propagation produce local real-Möbius transitions on the selected surface overlaps
statement:
  Pointed transitions at overlap points plus componentwise propagation produce local real-Möbius
  transitions on the selected surface overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions_of_pointedTransitionsAtOverlapPoints_and_componentExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hComponents :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapComponentsGood
        preData)
    (hPointAt :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionsAtOverlapPoints
        preData)
    (hExtend :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents
        preData) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions
      preData := by
  intro x y
  by_cases hxy : x = y
  · subst y
    exact
      HyperbolicLocalChart.hasLocalRealMobiusTransition_self
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
  · intro p hp
    let U :=
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
    let V :=
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
    have hpU : p ∈ U.domain := hp.1
    have hpV : p ∈ V.domain := hp.2
    rcases hPointAt x y hxy p hpU hpV with ⟨A, hpoint⟩
    let overlap : Set X := U.domain ∩ V.domain
    let component : Set X := connectedComponentIn overlap p
    refine ⟨
      { neighborhood := component
        isOpen_neighborhood := by
          simpa [component, overlap, U, V] using (hComponents x y p).1
        mem_neighborhood := by
          exact mem_connectedComponentIn hp
        subset_overlap := by
          intro z hz
          exact connectedComponentIn_subset overlap p hz
        representative := A
        transition_eq := ?_ }⟩
    intro z hz
    have hzOverlap : z ∈ overlap :=
      connectedComponentIn_subset overlap p hz
    exact
      hExtend x y A p hpoint z hzOverlap.1 hzOverlap.2
        (by simpa [component, overlap, U, V] using hz)

/--
Global pointed matching and componentwise propagation produce local
real-Mobius transitions on the selected surface overlaps.

%%handwave
name: Global pointed matching and componentwise propagation produce local real-Möbius transitions on the selected surface overlaps
statement:
  Global pointed matching and componentwise propagation produce local real-Möbius transitions on
  the selected surface overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions_of_localChartPointedTransitions_and_componentExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hComponents :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapComponentsGood
        preData)
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hExtend :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents
        preData) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions
      preData :=
  surfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions_of_pointedTransitionsAtOverlapPoints_and_componentExtension
    preData hComponents
    (surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionsAtOverlapPoints_of_localChartPointedTransitions
      preData hPoint)
    hExtend

/--
Componentwise selected-overlap propagation assembles the local-transition
selected branch package.

%%handwave
name: Componentwise selected-overlap propagation assembles the local-transition selected branch package
statement:
  Componentwise selected-overlap propagation assembles the local-transition selected branch
  package.
-/
def surfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection_of_preData_componentExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hComponents :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapComponentsGood
        preData)
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hExtend :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents
        preData) :
    SurfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection
      metricFormulaAtlas where
  preData := preData
  local_transition :=
    surfaceRealUpperHalfPlaneBranchAtlasPreDataHasLocalRealMobiusTransitions_of_localChartPointedTransitions_and_componentExtension
      preData hComponents hPoint hExtend

/--
Branch-predata selection for the canonical chart-at curvature atlas.

This is the local branch-choice target with no good-cover or preconnected
overlap condition.

%%handwave
name: Branch-predata selection for the canonical chart-at curvature atlas
statement:
  Branch-predata selection for the canonical chart-at curvature atlas. This is the local
  branch-choice assertion with no good-cover or preconnected overlap condition.
-/
def CanonicalChartedCurvatureBranchPreDataSelectionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X),
    Nonempty
      (SurfaceRealUpperHalfPlaneBranchAtlasPreData
        ((localCurvatureMetricFormulaAtlasInChartAt g)
          |>.toLocalLiouvilleMetricFormulaAtlas))

/--
Local-transition branch selection for the canonical chart-at curvature atlas.

The selected branches are required only to have local real-Mobius transition
data on overlaps; representatives may vary from one overlap component to
another.

%%handwave
name: Local-transition branch selection for the canonical chart-at curvature atlas
statement:
  Local-transition branch selection for the canonical chart-at curvature atlas. The selected
  branches are required only to have local real-Möbius transition data on overlaps;
  representatives may vary from one overlap component to another.
-/
def CanonicalChartedCurvatureLocalTransitionSelectionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X),
    Nonempty
      (SurfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection
        ((localCurvatureMetricFormulaAtlasInChartAt g)
          |>.toLocalLiouvilleMetricFormulaAtlas))

/--
Canonical branch predata, pointed matching, and componentwise propagation
produce local-transition selected branch data.

%%handwave
name: Canonical branch predata, pointed matching, and componentwise propagation produce local-transition selected branch data
statement:
  Canonical branch predata, pointed matching, and componentwise propagation produce
  local-transition selected branch data.
-/
noncomputable def canonicalChartedCurvatureLocalTransitionSelectionTheorem_of_branchPreDataSelection_pointedTransitions_componentExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [LocPathConnectedSpace X]
    (hSelection :
      CanonicalChartedCurvatureBranchPreDataSelectionTheorem X)
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnOverlapComponentTheorem
        X) :
    CanonicalChartedCurvatureLocalTransitionSelectionTheorem X := by
  intro g
  rcases hSelection g with ⟨preData⟩
  exact
    ⟨surfaceRealUpperHalfPlaneBranchAtlasLocalTransitionSelection_of_preData_componentExtension
      preData
      (surfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapComponentsGood preData)
      hPoint
      (surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlapComponents_of_global
        preData hExtend)⟩

namespace SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

end SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection

namespace SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

end SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection

namespace SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

end SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection

namespace SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagation

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

end SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagation

namespace SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagation

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

end SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagation

namespace SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionWithPropagation

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

end SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionWithPropagation

/--
Pointwise chart-compatibility supplies surface-domain openness for one chosen
Liouville metric formula atlas.

%%handwave
name: Pointwise chart-compatibility supplies surface-domain openness for one chosen Liouville metric formula atlas
statement:
  Pointwise chart-compatibility supplies surface-domain openness for one chosen Liouville metric
  formula atlas.
-/
def surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_coordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (hChart :
      LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor metricFormulaAtlas := by
  intro realBranchAtlasAt x
  let p : (metricFormulaAtlas.formulaAt x).conformalFactor.coordinateDomain :=
    ⟨(metricFormulaAtlas.formulaAt x).coordinate x,
      (metricFormulaAtlas.formulaAt x).coordinate_mem_conformalFactor_domain x
        (metricFormulaAtlas.mem_formulaAt_domain x)⟩
  let H := (realBranchAtlasAt x).branchNear p
  have hOpenH : IsOpen H.domain := by
    simpa [LocalUpperHalfPlaneDevelopingMap.domain] using H.projective.isOpen_domain
  rcases hChart x with ⟨hSub, hEq⟩
  exact
    isOpen_formulaCoordinate_preimage_of_eqOn_chartAt
      (metricFormulaAtlas.formulaAt x).isOpen_domain hSub hEq hOpenH

/--
The canonical chart-at curvature atlas, rewritten as a Liouville atlas, has
coordinates given by the ambient `chartAt` maps on their domains.

%%handwave
name: The canonical chart-at curvature atlas has the ambient chart maps as its coordinates
statement:
  In the canonical curvature atlas, the formula centered at $x$ is defined
  on the source of the ambient chart $\varphi_x$ and its coordinate equals
  $\varphi_x$ throughout that domain.
-/
def canonicalChartedCurvatureCoordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) :
    LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain
      ((localCurvatureMetricFormulaAtlasInChartAt g)
        |>.toLocalLiouvilleMetricFormulaAtlas) := by
  intro x
  exact ⟨fun _ hy ↦ hy, fun _ _ ↦ rfl⟩

/--
For one chosen Liouville metric formula atlas, local real branches and
surface-domain openness build the raw branch predata, with no overlap
connectedness condition.

%%handwave
name: For one chosen Liouville metric formula atlas, local real branches and surface-domain openness build the raw branch predata, with no overlap connectedness condition
statement:
  For one chosen Liouville metric formula atlas, local real branches and surface-domain openness
  build the raw branch predata, with no overlap connectedness condition.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasPreData_of_localRealBranches_openness_for
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (hLocal :
      ∀ x : X,
        Nonempty
          (LocalRealUpperHalfPlaneBranchAtlas
            (metricFormulaAtlas.formulaAt x).conformalFactor))
    (hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas :=
  let realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (metricFormulaAtlas.formulaAt x).conformalFactor :=
    fun x ↦ Classical.choice (hLocal x)
  { realBranchAtlasAt := realBranchAtlasAt
    restricted_domain_open := hOpen realBranchAtlasAt }

/--
For the canonical chart-at curvature atlas, local real Liouville branches
alone select the raw branch predata.  The surface-domain openness is supplied
by the fact that the formula coordinates are the ambient charts on their
domains.

%%handwave
name: For the canonical chart-at curvature atlas, local real Liouville branches alone select the raw branch predata
statement:
  For the canonical chart-at curvature atlas, local real Liouville branches alone select the raw
  branch predata. The surface-domain openness is supplied by the fact that the formula
  coordinates are the ambient charts on their domains.
-/
noncomputable def canonicalChartedCurvatureBranchPreDataSelectionTheorem_of_localRealBranches
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem) :
    CanonicalChartedCurvatureBranchPreDataSelectionTheorem X := by
  intro g
  let metricFormulaAtlas :=
    ((localCurvatureMetricFormulaAtlasInChartAt g)
      |>.toLocalLiouvilleMetricFormulaAtlas)
  exact
    ⟨surfaceRealUpperHalfPlaneBranchAtlasPreData_of_localRealBranches_openness_for
      (metricFormulaAtlas := metricFormulaAtlas)
      (fun x ↦
        hLocal (metricFormulaAtlas.formulaAt x).conformalFactor
          (metricFormulaAtlas.formulaAt x).solves_liouville)
      (surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_coordinateChartedOnDomain
        (canonicalChartedCurvatureCoordinateChartedOnDomain g))⟩

end HyperbolicMetric

end

end JJMath
