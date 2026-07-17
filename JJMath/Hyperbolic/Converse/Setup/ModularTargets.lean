import JJMath.Hyperbolic.Converse.Setup.CurvatureAtlas

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

/-- Global theorem target for expanding curvature `-1` into Liouville formulas. -/
def CurvatureFormulaExpansionTheorem (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X), g.HasCurvatureLiouvilleFormulaAtlas

/--
The local curvature formula `K = -exp (-2u) Δu` implies the Liouville formula
atlas by algebra.
-/
def curvatureFormulaExpansionTheorem_of_localCurvatureFormulaExpansionTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h : LocalCurvatureFormulaExpansionTheorem X) :
    CurvatureFormulaExpansionTheorem X :=
  fun g ↦
    hasCurvatureLiouvilleFormulaAtlas_of_hasLocalCurvatureMetricFormulaAtlas
      (h g)

/--
Global theorem target for solving any chosen curvature-derived Liouville
formula atlas by local maps to `ℍ`.
-/
def LocalSolvingFromCurvatureFormulaTheorem (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (curvatureFormulaAtlas : CurvatureLiouvilleFormulaAtlas X g),
    Nonempty (LocalSolvingFromCurvatureFormula g curvatureFormulaAtlas)

/--
Global theorem target for solving any chosen Liouville formula atlas by local
maps to `ℍ`.
-/
def LocalSolvingFromLiouvilleFormulaAtlasTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g),
    Nonempty (LocalSolvingFromLiouvilleFormulaAtlas g metricFormulaAtlas)

/--
Solving arbitrary Liouville formula atlases specializes to solving
curvature-derived Liouville formula atlases.
-/
def localSolvingFromCurvatureFormulaTheorem_of_localSolvingFromLiouvilleFormulaAtlasTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h : LocalSolvingFromLiouvilleFormulaAtlasTheorem X) :
    LocalSolvingFromCurvatureFormulaTheorem X :=
  fun g curvatureFormulaAtlas ↦
    let S := Classical.choice
      (h g curvatureFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas)
    ⟨{
      developingConstructionAtlas := S.developingConstructionAtlas
      constructions_solve_curvature_formulas :=
        S.constructions_solve_metric_formulas
    }⟩

/--
Two-step local theorem package: first derive Liouville formulas from curvature,
then solve the selected formulas by local upper-half-plane maps.
-/
structure LocalCurvatureSolvingModularTheorems (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] where
  /-- Curvature `-1` expands to local Liouville metric formulas. -/
  curvatureExpansion : CurvatureFormulaExpansionTheorem X
  /-- The resulting local Liouville formulas have local developing constructions. -/
  solveCurvatureFormulas : LocalSolvingFromCurvatureFormulaTheorem X

/-- Prop-level wrapper for the two-step local theorem package. -/
def HasLocalCurvatureSolvingModularTheorems (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] : Prop :=
  Nonempty (LocalCurvatureSolvingModularTheorems X)

/--
More refined local theorem package: first expand abstract curvature into the
local conformal curvature formula, then use the proved algebraic bridge to get
Liouville formulas, then solve those Liouville formulas by maps to `ℍ`.
-/
structure LocalCurvatureFormulaSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Solve the resulting Liouville formulas by local maps to `ℍ`. -/
  solveCurvatureFormulas : LocalSolvingFromCurvatureFormulaTheorem X

/-- Prop-level wrapper for the curvature-formula-refined local theorem package. -/
def HasLocalCurvatureFormulaSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (LocalCurvatureFormulaSolvingModularTheorems X)

/--
Local theorem package with the PDE step stated for arbitrary Liouville formula
atlases rather than only curvature-derived ones.
-/
structure LocalLiouvilleSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Solve any Liouville formula atlas by local maps to `ℍ`. -/
  solveLiouvilleFormulas : LocalSolvingFromLiouvilleFormulaAtlasTheorem X

/-- Prop-level wrapper for the Liouville-solver-refined local theorem package. -/
def HasLocalLiouvilleSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (LocalLiouvilleSolvingModularTheorems X)

/--
Schwarzian-refined local theorem package.

This states the local analytic step in the form closest to the current
construction: after expanding curvature to Liouville formulas, solve the
associated Schwarzian equation locally, choose upper-half-plane branches, and
verify real Mobius transitions.
-/
structure LocalSchwarzianSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Solve any Liouville formula atlas by Schwarzian upper-half-plane branches. -/
  solveSchwarzianBranches : LocalSolvingFromSchwarzianBranchDataTheorem X

/-- Prop-level wrapper for the Schwarzian-refined local theorem package. -/
def HasLocalSchwarzianSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (LocalSchwarzianSolvingModularTheorems X)

/--
Surface-branch-refined local theorem package.

This exposes the local analytic boundary before it is wrapped as local solving
data: choose `SurfaceSchwarzianBranchData` over every Liouville metric-formula
atlas.
-/
structure LocalSurfaceSchwarzianSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Choose surface-level Schwarzian branch data over any Liouville formula atlas. -/
  solveSurfaceBranches : SurfaceSchwarzianBranchDataTheorem X

/-- Prop-level wrapper for the surface-branch-refined local theorem package. -/
def HasLocalSurfaceSchwarzianSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (LocalSurfaceSchwarzianSolvingModularTheorems X)

/--
Pointed-surface-branch-refined local theorem package.

This is the current sharp local boundary: local Schwarzian ODE branches are
chosen only near each base coordinate, and the associated surface domains are
shrunk before assembling local upper-half-plane models.
-/
structure LocalPointedSurfaceSchwarzianSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Choose pointed Schwarzian branch data over any Liouville formula atlas. -/
  solvePointedSurfaceBranches : SurfaceSchwarzianPointedBranchDataTheorem X

/-- Prop-level wrapper for the pointed-surface-branch-refined local theorem package. -/
def HasLocalPointedSurfaceSchwarzianSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (LocalPointedSurfaceSchwarzianSolvingModularTheorems X)

/--
Surface-real-branch-refined local theorem package.

This splits pointed surface branch construction into coordinate-domain real
branch atlases for each Liouville factor and a separate surface assembly
theorem that handles shrinking, openness, and cross-chart real transitions.
-/
structure LocalSurfaceRealBranchAtlasSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Hyperbolic Liouville factors produce coordinate real branch atlases. -/
  coordinateRealBranches :
    HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem
  /-- Assemble coordinate real branch atlases into pointed surface branch data. -/
  surfaceAssembly : SurfaceRealUpperHalfPlaneBranchAtlasAssemblyTheorem X

/-- Prop-level wrapper for the surface-real-branch-refined local package. -/
def HasLocalSurfaceRealBranchAtlasSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (LocalSurfaceRealBranchAtlasSolvingModularTheorems X)

/--
Schwarzian-analytic local theorem package.

This replaces the raw coordinate-real-branch theorem by the local Schwarzian
analytic boundary bundle from `Schwarzian.lean`.  That bundle already contains
holomorphic Schwarzian production, Frobenius construction from local
holomorphicity, ball-shrunk 2-jet normalization, Riccati metric recovery,
ball-pre-atlas construction, and real-transition uniqueness.
-/
structure LocalSchwarzianAnalyticBoundarySolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Produce coordinate real branch atlases from the local Schwarzian boundary. -/
  schwarzianBoundary : HyperbolicLiouvilleSchwarzianAnalyticBoundaryTheorems
  /-- Assemble coordinate real branch atlases into pointed surface branch data. -/
  surfaceAssembly : SurfaceRealUpperHalfPlaneBranchAtlasAssemblyTheorem X

/-- Prop-level wrapper for the Schwarzian-analytic local package. -/
def HasLocalSchwarzianAnalyticBoundarySolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (LocalSchwarzianAnalyticBoundarySolvingModularTheorems X)

/--
Schwarzian-analytic local theorem package with the sharpened overlap-only real
transition boundary.

The real-transition input is now exactly the atlas-level condition needed for
distinct metric-recovering branches with nonempty overlap; diagonal and empty
overlap cases are handled by the local Schwarzian atlas machinery.
-/
structure LocalSchwarzianAnalyticOverlappingBoundarySolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Produce coordinate real branch atlases from the overlap-sharp local Schwarzian boundary. -/
  schwarzianBoundary : HyperbolicLiouvilleSchwarzianAnalyticOverlappingBoundaryTheorems
  /-- Assemble coordinate real branch atlases into pointed surface branch data. -/
  surfaceAssembly : SurfaceRealUpperHalfPlaneBranchAtlasAssemblyTheorem X

/-- Prop-level wrapper for the overlap-sharp Schwarzian-analytic local package. -/
def HasLocalSchwarzianAnalyticOverlappingBoundarySolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (LocalSchwarzianAnalyticOverlappingBoundarySolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local theorem package.

The coordinate-domain branch construction is now supplied by the proved
metric-Schwarzian Frobenius derivative-algebra theorem.  The only remaining
coordinate overlap input in this local package is the real-transition
uniqueness theorem; surface shrinking and cross-chart compatibility are kept
as the separate surface assembly field.
-/
structure LocalMetricSchwarzianFrobeniusSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Metric-recovering coordinate branches have real Mobius transitions. -/
  realTransitions : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem
  /-- Assemble coordinate real branch atlases into pointed surface branch data. -/
  surfaceAssembly : SurfaceRealUpperHalfPlaneBranchAtlasAssemblyTheorem X

/-- Prop-level wrapper for the metric-Schwarzian Frobenius local package. -/
def HasLocalMetricSchwarzianFrobeniusSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (LocalMetricSchwarzianFrobeniusSolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local theorem package with overlap-sharp real
transition input.

Compared with `LocalMetricSchwarzianFrobeniusSolvingModularTheorems`, this
asks only for the atlas-level condition that distinct metric-recovering
coordinate branches with nonempty overlap have real Mobius transitions.
-/
structure LocalMetricSchwarzianFrobeniusOverlappingSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Distinct overlapping metric-recovering coordinate branches have real Mobius transitions. -/
  overlappingOffDiagonalRealTransitions :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem
  /-- Assemble coordinate real branch atlases into pointed surface branch data. -/
  surfaceAssembly : SurfaceRealUpperHalfPlaneBranchAtlasAssemblyTheorem X

/-- Prop-level wrapper for the overlap-sharp metric-Schwarzian Frobenius local package. -/
def HasLocalMetricSchwarzianFrobeniusOverlappingSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (LocalMetricSchwarzianFrobeniusOverlappingSolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local theorem package with the surface assembly
boundary split into openness and cross-chart transition compatibility.
-/
structure LocalMetricSchwarzianFrobeniusSplitAssemblySolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Metric-recovering coordinate branches have real Mobius transitions. -/
  realTransitions : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem
  /-- Pulled-back selected coordinate branch domains are open on the surface. -/
  restrictedDomainOpenness :
    SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X
  /-- The selected shrunk surface branches have real Mobius transitions. -/
  surfaceTransitions :
    SurfaceRealUpperHalfPlaneBranchAtlasSurfaceTransitionTheorem X

/-- Prop-level wrapper for the split-assembly metric-Schwarzian Frobenius local package. -/
def HasLocalMetricSchwarzianFrobeniusSplitAssemblySolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (LocalMetricSchwarzianFrobeniusSplitAssemblySolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local theorem package where surface-domain
openness is reduced to coordinate-preimage openness for the Liouville formula
atlas.
-/
structure LocalMetricSchwarzianFrobeniusCoordinateOpennessSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Metric-recovering coordinate branches have real Mobius transitions. -/
  realTransitions : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem
  /-- Formula coordinate preimages of open coordinate sets are open on the surface. -/
  coordinatePreimageOpenness :
    LocalLiouvilleMetricFormulaAtlasCoordinatePreimageOpennessTheorem X
  /-- The selected shrunk surface branches have real Mobius transitions. -/
  surfaceTransitions :
    SurfaceRealUpperHalfPlaneBranchAtlasSurfaceTransitionTheorem X

/-- Prop-level wrapper for the coordinate-openness metric-Schwarzian Frobenius local package. -/
def HasLocalMetricSchwarzianFrobeniusCoordinateOpennessSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty (LocalMetricSchwarzianFrobeniusCoordinateOpennessSolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local theorem package where surface-domain
openness is coordinate-preimage openness and transition compatibility is needed
only for distinct centers.
-/
structure LocalMetricSchwarzianFrobeniusCoordinateOpennessOffDiagonalSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Metric-recovering coordinate branches have real Mobius transitions. -/
  realTransitions : MetricRecoveringUpperHalfPlaneBranchesHaveRealMobiusTransitionsTheorem
  /-- Formula coordinate preimages of open coordinate sets are open on the surface. -/
  coordinatePreimageOpenness :
    LocalLiouvilleMetricFormulaAtlasCoordinatePreimageOpennessTheorem X
  /-- Distinct selected shrunk surface branches have real Mobius transitions. -/
  offDiagonalSurfaceTransitions :
    SurfaceRealUpperHalfPlaneBranchAtlasOffDiagonalSurfaceTransitionTheorem X

/-- Prop-level wrapper for the off-diagonal transition metric-Schwarzian Frobenius package. -/
def HasLocalMetricSchwarzianFrobeniusCoordinateOpennessOffDiagonalSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusCoordinateOpennessOffDiagonalSolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local theorem package with both diagonal
transition cases removed.

The local coordinate branch construction only asks for real-transition
uniqueness between distinct chosen local branches; the diagonal coordinate
transition is identity.  Likewise, the surface transition field is only for
distinct surface centers.
-/
structure LocalMetricSchwarzianFrobeniusCoordinateOpennessDoubleOffDiagonalSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Distinct metric-recovering coordinate branches have real Mobius transitions. -/
  localOffDiagonalRealTransitions :
    MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem
  /-- Formula coordinate preimages of open coordinate sets are open on the surface. -/
  coordinatePreimageOpenness :
    LocalLiouvilleMetricFormulaAtlasCoordinatePreimageOpennessTheorem X
  /-- Distinct selected shrunk surface branches have real Mobius transitions. -/
  offDiagonalSurfaceTransitions :
    SurfaceRealUpperHalfPlaneBranchAtlasOffDiagonalSurfaceTransitionTheorem X

/-- Prop-level wrapper for the double-off-diagonal metric-Schwarzian Frobenius package. -/
def HasLocalMetricSchwarzianFrobeniusCoordinateOpennessDoubleOffDiagonalSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusCoordinateOpennessDoubleOffDiagonalSolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local package with diagonal transition cases
removed and coordinate-preimage openness reduced to continuity on the local
formula domains.
-/
structure LocalMetricSchwarzianFrobeniusCoordinateContinuousDoubleOffDiagonalSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Distinct metric-recovering coordinate branches have real Mobius transitions. -/
  localOffDiagonalRealTransitions :
    MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem
  /-- Formula coordinates are continuous on their local formula domains. -/
  coordinateContinuousOnDomain :
    LocalLiouvilleMetricFormulaAtlasCoordinateContinuousOnDomainTheorem X
  /-- Distinct selected shrunk surface branches have real Mobius transitions. -/
  offDiagonalSurfaceTransitions :
    SurfaceRealUpperHalfPlaneBranchAtlasOffDiagonalSurfaceTransitionTheorem X

/-- Prop-level wrapper for the coordinate-continuity double-off-diagonal package. -/
def HasLocalMetricSchwarzianFrobeniusCoordinateContinuousDoubleOffDiagonalSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusCoordinateContinuousDoubleOffDiagonalSolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local package where the topological coordinate
input is that formula coordinates are ambient chart coordinates on their
formula domains.
-/
structure LocalMetricSchwarzianFrobeniusCoordinateChartedDoubleOffDiagonalSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Distinct metric-recovering coordinate branches have real Mobius transitions. -/
  localOffDiagonalRealTransitions :
    MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem
  /-- Formula coordinates agree with ambient chart coordinates on their domains. -/
  coordinateChartedOnDomain :
    LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomainTheorem X
  /-- Distinct selected shrunk surface branches have real Mobius transitions. -/
  offDiagonalSurfaceTransitions :
    SurfaceRealUpperHalfPlaneBranchAtlasOffDiagonalSurfaceTransitionTheorem X

/-- Prop-level wrapper for the coordinate-charted double-off-diagonal package. -/
def HasLocalMetricSchwarzianFrobeniusCoordinateChartedDoubleOffDiagonalSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusCoordinateChartedDoubleOffDiagonalSolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local package where formula coordinates are
ambient chart coordinates and surface transition compatibility is only
required for distinct selected domains with nonempty overlap.
-/
structure LocalMetricSchwarzianFrobeniusCoordinateChartedOverlappingDoubleOffDiagonalSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Distinct metric-recovering coordinate branches have real Mobius transitions. -/
  localOffDiagonalRealTransitions :
    MetricRecoveringSchwarzianNormalizationAtlasHasOffDiagonalRealTransitionsTheorem
  /-- Formula coordinates agree with ambient chart coordinates on their domains. -/
  coordinateChartedOnDomain :
    LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomainTheorem X
  /-- Distinct selected shrunk surface branches with nonempty overlap have real Mobius transitions. -/
  overlappingOffDiagonalSurfaceTransitions :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionTheorem X

/-- Prop-level wrapper for the overlapping coordinate-charted double-off-diagonal package. -/
def HasLocalMetricSchwarzianFrobeniusCoordinateChartedOverlappingDoubleOffDiagonalSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusCoordinateChartedOverlappingDoubleOffDiagonalSolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local package where formula coordinates are
ambient chart coordinates and both coordinate-domain and surface-domain
transition compatibility are required only for distinct selected branches with
nonempty overlap.
-/
structure LocalMetricSchwarzianFrobeniusCoordinateChartedOverlappingTransitionsSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Distinct overlapping metric-recovering coordinate branches have real Mobius transitions. -/
  localOverlappingOffDiagonalRealTransitions :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem
  /-- Formula coordinates agree with ambient chart coordinates on their domains. -/
  coordinateChartedOnDomain :
    LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomainTheorem X
  /-- Distinct selected shrunk surface branches with nonempty overlap have real Mobius transitions. -/
  overlappingOffDiagonalSurfaceTransitions :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionTheorem X

/-- Prop-level wrapper for the fully overlapping coordinate-charted transition package. -/
def HasLocalMetricSchwarzianFrobeniusCoordinateChartedOverlappingTransitionsSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusCoordinateChartedOverlappingTransitionsSolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local package where the surface real-transition
input is replaced by the standard local-isometry uniqueness theorem plus
preconnectedness of the selected surface overlaps.
-/
structure LocalMetricSchwarzianFrobeniusCoordinateChartedPreconnectedSurfaceOverlapSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Distinct overlapping metric-recovering coordinate branches have real Mobius transitions. -/
  localOverlappingOffDiagonalRealTransitions :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem
  /-- Formula coordinates agree with ambient chart coordinates on their domains. -/
  coordinateChartedOnDomain :
    LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomainTheorem X
  /-- Hyperbolic local charts have real Mobius transitions on preconnected overlaps. -/
  localChartPreconnectedTransitions :
    HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X
  /-- The selected shrunk surface overlaps are preconnected whenever they are nonempty. -/
  surfaceOverlapPreconnected :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem X

/-- Prop-level wrapper for the preconnected-surface-overlap package. -/
def HasLocalMetricSchwarzianFrobeniusCoordinateChartedPreconnectedSurfaceOverlapSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusCoordinateChartedPreconnectedSurfaceOverlapSolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local package where the surface real-transition
input is supplied by the bundled analytic local-isometry consequences, plus
preconnectedness of the selected surface overlaps.
-/
structure LocalMetricSchwarzianFrobeniusCoordinateChartedAnalyticSurfaceOverlapSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Distinct overlapping metric-recovering coordinate branches have real Mobius transitions. -/
  localOverlappingOffDiagonalRealTransitions :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem
  /-- Formula coordinates agree with ambient chart coordinates on their domains. -/
  coordinateChartedOnDomain :
    LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomainTheorem X
  /-- Bundled analytic consequences for holomorphic hyperbolic local isometries. -/
  analyticLocalIsometryConsequences :
    HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X
  /-- The selected shrunk surface overlaps are preconnected whenever they are nonempty. -/
  surfaceOverlapPreconnected :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem X

/-- Prop-level wrapper for the analytic local-isometry surface-overlap package. -/
def HasLocalMetricSchwarzianFrobeniusCoordinateChartedAnalyticSurfaceOverlapSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusCoordinateChartedAnalyticSurfaceOverlapSolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local package with the coordinate-domain
Schwarzian overlap theorem already discharged by the closed derivative-data
construction.

Compared with
`LocalMetricSchwarzianFrobeniusCoordinateChartedAnalyticSurfaceOverlapSolvingModularTheorems`,
this no longer asks for a separate
`MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem`.
The coordinate real branch atlases are supplied by the closed local
Schwarzian theorem, while the surface-level transition input remains the
analytic local-isometry consequence package plus preconnectedness of the
selected surface overlaps.
-/
structure LocalMetricSchwarzianFrobeniusCoordinateChartedClosedSchwarzianAnalyticSurfaceOverlapSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Formula coordinates agree with ambient chart coordinates on their domains. -/
  coordinateChartedOnDomain :
    LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomainTheorem X
  /-- Bundled analytic consequences for holomorphic hyperbolic local isometries. -/
  analyticLocalIsometryConsequences :
    HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X
  /-- The selected shrunk surface overlaps are preconnected whenever they are nonempty. -/
  surfaceOverlapPreconnected :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem X

/-- Prop-level wrapper for the closed-Schwarzian analytic surface-overlap package. -/
def HasLocalMetricSchwarzianFrobeniusCoordinateChartedClosedSchwarzianAnalyticSurfaceOverlapSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusCoordinateChartedClosedSchwarzianAnalyticSurfaceOverlapSolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local package where local hyperbolic-chart
uniqueness is supplied in pointed form: choose a real Mobius representative by
matching value and first-order data at one point, then propagate it over a
preconnected overlap.
-/
structure LocalMetricSchwarzianFrobeniusCoordinateChartedPointedSurfaceOverlapSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Distinct overlapping metric-recovering coordinate branches have real Mobius transitions. -/
  localOverlappingOffDiagonalRealTransitions :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem
  /-- Formula coordinates agree with ambient chart coordinates on their domains. -/
  coordinateChartedOnDomain :
    LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomainTheorem X
  /-- Pointed real-Mobius matching for hyperbolic local charts. -/
  localChartPointedTransitions :
    HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X
  /-- Pointed matches extend over preconnected chart overlaps. -/
  localChartPointedTransitionExtension :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X
  /-- The selected shrunk surface overlaps are preconnected whenever they are nonempty. -/
  surfaceOverlapPreconnected :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem X

/-- Prop-level wrapper for the pointed preconnected-surface-overlap package. -/
def HasLocalMetricSchwarzianFrobeniusCoordinateChartedPointedSurfaceOverlapSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusCoordinateChartedPointedSurfaceOverlapSolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local package where the pointed transition input is
only required on the actual selected off-diagonal surface overlaps.
-/
structure LocalMetricSchwarzianFrobeniusCoordinateChartedSelectedPointedSurfaceOverlapSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Distinct overlapping metric-recovering coordinate branches have real Mobius transitions. -/
  localOverlappingOffDiagonalRealTransitions :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem
  /-- Formula coordinates agree with ambient chart coordinates on their domains. -/
  coordinateChartedOnDomain :
    LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomainTheorem X
  /-- Pointed real-Mobius matching on each actual selected nonempty off-diagonal overlap. -/
  selectedOverlapPointedTransitions :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem X
  /-- Pointed matches extend over preconnected chart overlaps. -/
  localChartPointedTransitionExtension :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X
  /-- The selected shrunk surface overlaps are preconnected whenever they are nonempty. -/
  surfaceOverlapPreconnected :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem X

/-- Prop-level wrapper for the selected-pointed surface-overlap package. -/
def HasLocalMetricSchwarzianFrobeniusCoordinateChartedSelectedPointedSurfaceOverlapSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusCoordinateChartedSelectedPointedSurfaceOverlapSolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local package where the chart-compatibility input
is required only for curvature formula atlases.  The selected curvature atlas
is then rewritten as a Liouville formula atlas internally.
-/
structure LocalMetricSchwarzianFrobeniusCurvatureChartedOverlappingTransitionsSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Distinct overlapping metric-recovering coordinate branches have real Mobius transitions. -/
  localOverlappingOffDiagonalRealTransitions :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem
  /-- Curvature formula coordinates agree with ambient chart coordinates on their domains. -/
  curvatureCoordinateChartedOnDomain :
    LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomainTheorem X
  /-- Distinct selected shrunk surface branches with nonempty overlap have real Mobius transitions. -/
  overlappingOffDiagonalSurfaceTransitions :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionTheorem X

/-- Prop-level wrapper for the curvature-charted overlapping-transition local package. -/
def HasLocalMetricSchwarzianFrobeniusCurvatureChartedOverlappingTransitionsSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusCurvatureChartedOverlappingTransitionsSolvingModularTheorems X)

/--
Metric-Schwarzian Frobenius local package where both chart-compatibility and
cross-chart surface transitions are stated only for curvature formula atlases.
-/
structure LocalMetricSchwarzianFrobeniusCurvatureChartedCurvatureTransitionsSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Distinct overlapping metric-recovering coordinate branches have real Mobius transitions. -/
  localOverlappingOffDiagonalRealTransitions :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem
  /-- Curvature formula coordinates agree with ambient chart coordinates on their domains. -/
  curvatureCoordinateChartedOnDomain :
    LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomainTheorem X
  /-- Curvature-derived selected surface branches with nonempty overlap have real Mobius transitions. -/
  curvatureOverlappingOffDiagonalSurfaceTransitions :
    LocalCurvatureMetricFormulaAtlasOverlappingOffDiagonalSurfaceTransitionTheorem X

/-- Prop-level wrapper for the curvature-charted curvature-transition local package. -/
def HasLocalMetricSchwarzianFrobeniusCurvatureChartedCurvatureTransitionsSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusCurvatureChartedCurvatureTransitionsSolvingModularTheorems X)

/--
Selected-curvature-atlas local package.

This is sharper than
`LocalMetricSchwarzianFrobeniusCurvatureChartedCurvatureTransitionsSolvingModularTheorems`:
for each metric it chooses the curvature formula atlas directly and asks for
chart compatibility and curvature-derived surface transitions only for that
chosen atlas.
-/
structure LocalMetricSchwarzianFrobeniusSelectedCurvatureAtlasSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The selected curvature formula atlas for each metric. -/
  selectedCurvatureFormulaAtlas :
    ∀ (g : HyperbolicMetric X), LocalCurvatureMetricFormulaAtlas X g
  /-- Distinct overlapping metric-recovering coordinate branches have real Mobius transitions. -/
  localOverlappingOffDiagonalRealTransitions :
    MetricRecoveringSchwarzianNormalizationAtlasHasOverlappingOffDiagonalRealTransitionsTheorem
  /-- The selected curvature formula coordinates are ambient chart coordinates on their domains. -/
  selectedCurvatureCoordinateChartedOnDomain :
    ∀ (g : HyperbolicMetric X),
      LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomain
        (selectedCurvatureFormulaAtlas g)
  /-- Selected curvature-derived surface branches with nonempty overlap have real Mobius transitions. -/
  selectedCurvatureOverlappingOffDiagonalSurfaceTransitions :
    ∀ (g : HyperbolicMetric X),
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionFor
        (selectedCurvatureFormulaAtlas g).toLocalLiouvilleMetricFormulaAtlas

/-- Prop-level wrapper for the selected-curvature-atlas local package. -/
def HasLocalMetricSchwarzianFrobeniusSelectedCurvatureAtlasSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusSelectedCurvatureAtlasSolvingModularTheorems X)

/--
Selected-curvature-atlas local package with the coordinate Schwarzian
transition theorem already discharged.

This is the selected-atlas analogue of
`LocalMetricSchwarzianFrobeniusCoordinateChartedClosedSchwarzianAnalyticSurfaceOverlapSolvingModularTheorems`:
for each metric we choose the curvature formula atlas directly, use the
closed metric-Schwarzian derivative-data construction for coordinate real
branches, and keep only the selected chart-compatibility, selected overlap
preconnectedness, and analytic local-isometry consequences as the surface
inputs.
-/
structure LocalMetricSchwarzianFrobeniusSelectedCurvatureAtlasClosedSchwarzianAnalyticSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The selected curvature formula atlas for each metric. -/
  selectedCurvatureFormulaAtlas :
    ∀ (g : HyperbolicMetric X), LocalCurvatureMetricFormulaAtlas X g
  /-- The selected curvature formula coordinates are ambient chart coordinates on their domains. -/
  selectedCurvatureCoordinateChartedOnDomain :
    ∀ (g : HyperbolicMetric X),
      LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomain
        (selectedCurvatureFormulaAtlas g)
  /-- Bundled analytic consequences for holomorphic hyperbolic local isometries. -/
  analyticLocalIsometryConsequences :
    HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X
  /-- The selected curvature-derived surface overlaps are preconnected whenever nonempty. -/
  selectedCurvatureSurfaceOverlapPreconnected :
    ∀ (g : HyperbolicMetric X),
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedFor
        (selectedCurvatureFormulaAtlas g).toLocalLiouvilleMetricFormulaAtlas

/-- Prop-level wrapper for the closed selected-curvature analytic local package. -/
def HasLocalMetricSchwarzianFrobeniusSelectedCurvatureAtlasClosedSchwarzianAnalyticSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusSelectedCurvatureAtlasClosedSchwarzianAnalyticSolvingModularTheorems X)

/--
Curvature-charted local package with the coordinate Schwarzian transition
theorem already discharged.

This version no longer asks the user to select the curvature formula atlas
manually.  It chooses one from the curvature expansion theorem, uses the
curvature chart-compatibility theorem for that chosen atlas, and uses the
closed metric-Schwarzian derivative-data construction for coordinate real
branches.  The remaining surface inputs are analytic local-isometry
consequences and preconnectedness of selected surface overlaps.
-/
structure LocalMetricSchwarzianFrobeniusCurvatureChartedClosedSchwarzianAnalyticSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand abstract curvature into local coordinate curvature formulas. -/
  localCurvatureExpansion : LocalCurvatureFormulaExpansionTheorem X
  /-- Curvature formula coordinates agree with ambient chart coordinates on their domains. -/
  curvatureCoordinateChartedOnDomain :
    LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomainTheorem X
  /-- Bundled analytic consequences for holomorphic hyperbolic local isometries. -/
  analyticLocalIsometryConsequences :
    HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X
  /-- The selected shrunk surface overlaps are preconnected whenever they are nonempty. -/
  surfaceOverlapPreconnected :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem X

/-- Prop-level wrapper for the closed curvature-charted analytic local package. -/
def HasLocalMetricSchwarzianFrobeniusCurvatureChartedClosedSchwarzianAnalyticSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusCurvatureChartedClosedSchwarzianAnalyticSolvingModularTheorems X)

/--
Charted-curvature-expansion local package with the coordinate Schwarzian
transition theorem already discharged.

Compared with `LocalMetricSchwarzianFrobeniusCurvatureChartedClosed...`, this
package asks for a single charted curvature expansion theorem: the selected
curvature formulae already come with the proof that their coordinates are
ambient chart restrictions.
-/
structure LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionClosedSchwarzianAnalyticSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand curvature directly into chart-compatible local curvature formulae. -/
  chartedLocalCurvatureExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X
  /-- Bundled analytic consequences for holomorphic hyperbolic local isometries. -/
  analyticLocalIsometryConsequences :
    HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X
  /-- The selected shrunk surface overlaps are preconnected whenever they are nonempty. -/
  surfaceOverlapPreconnected :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem X

/-- Prop-level wrapper for the charted-curvature-expansion local package. -/
def HasLocalMetricSchwarzianFrobeniusChartedCurvatureExpansionClosedSchwarzianAnalyticSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionClosedSchwarzianAnalyticSolvingModularTheorems X)

/--
Charted-curvature-expansion local package with an explicit selected-overlap
predata object.

This is sharper than asking for a global preconnectedness theorem on all
possible predata.  For each metric, the curvature expansion chooses a
chart-compatible curvature formula atlas, and the package supplies one
concrete choice of coordinate real branches and restricted surface domains
whose nonempty off-diagonal overlaps are preconnected.
-/
structure LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand curvature directly into chart-compatible local curvature formulae. -/
  chartedLocalCurvatureExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X
  /-- The concrete chart-compatible curvature formula atlas selected for each metric. -/
  selectedChartedCurvatureFormulaAtlas :
    ∀ (g : HyperbolicMetric X),
      {curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g //
        LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomain
          curvatureFormulaAtlas}
  /-- Bundled analytic consequences for holomorphic hyperbolic local isometries. -/
  analyticLocalIsometryConsequences :
    HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X
  /-- The selected branch predata for the chosen chart-compatible curvature atlas has preconnected overlaps. -/
  selectedOverlapSelection :
    ∀ (g : HyperbolicMetric X),
      Nonempty
        (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
          ((selectedChartedCurvatureFormulaAtlas g).val
            |>.toLocalLiouvilleMetricFormulaAtlas))

/-- Prop-level wrapper for the charted-curvature-expansion selected-overlap local package. -/
def HasLocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems X)

/--
Constructor for the selected-overlap closed analytic local package using the
now-proved charted curvature expansion.

This is intentionally not the final no-argument constructor: the remaining
inputs are exactly the still-open local analytic uniqueness package and the
selected preconnected-overlap construction for the chart-at curvature atlas.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_analyticLocalIsometryConsequences_and_selectedOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hAnalytic :
      HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X)
    (hSelection :
      ∀ (g : HyperbolicMetric X),
        Nonempty
          (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
            ((localCurvatureMetricFormulaAtlasInChartAt g)
              |>.toLocalLiouvilleMetricFormulaAtlas))) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems
      X where
  chartedLocalCurvatureExpansion := chartedLocalCurvatureFormulaExpansionTheorem X
  selectedChartedCurvatureFormulaAtlas := fun g ↦
    ⟨localCurvatureMetricFormulaAtlasInChartAt g, by
      intro x
      exact ⟨fun _ hy ↦ hy, fun _ _ ↦ rfl⟩⟩
  analyticLocalIsometryConsequences := hAnalytic
  selectedOverlapSelection := hSelection

/--
Selected-overlap local package from the global concrete selected-overlap
theorem, specialized to the canonical chart-at curvature atlas.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_analyticLocalIsometryConsequences_and_overlapSelectionTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hAnalytic :
      HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_analyticLocalIsometryConsequences_and_selectedOverlapSelection
    hAnalytic
    (fun g =>
      hSelection g
        ((localCurvatureMetricFormulaAtlasInChartAt g)
          |>.toLocalLiouvilleMetricFormulaAtlas))

/--
Selected-overlap local package from the chart-compatible selected-overlap
theorem, specialized to the canonical chart-at curvature atlas.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_analyticLocalIsometryConsequences_and_chartedOverlapSelectionTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hAnalytic :
      HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_analyticLocalIsometryConsequences_and_overlapSelectionTheorem
    hAnalytic
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_chartedSelection
      hSelection)

/--
Selected-overlap local package with the analytic consequence input reduced to
the Poincare pullback squared-density formula plus openness of pointed
real-Mobius equality loci.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_pullbackSquaredDensityFormula_equalitySetOpen_and_selectedOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem
        X)
    (hSelection :
      ∀ (g : HyperbolicMetric X),
        Nonempty
          (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
            ((localCurvatureMetricFormulaAtlasInChartAt g)
              |>.toLocalLiouvilleMetricFormulaAtlas))) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_analyticLocalIsometryConsequences_and_selectedOverlapSelection
    (hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_pullbackSquaredDensityFormula_equalitySetOpen
      hPull hOpen)
    hSelection

/--
Selected-overlap local package from the Poincare pullback formula, openness
of pointed equality loci, and the global concrete selected-overlap theorem.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_pullbackSquaredDensityFormula_equalitySetOpen_and_overlapSelectionTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem
        X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_analyticLocalIsometryConsequences_and_overlapSelectionTheorem
    (hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_pullbackSquaredDensityFormula_equalitySetOpen
      hPull hOpen)
    hSelection

/--
Selected-overlap local package from the Poincare pullback formula, openness
of pointed equality loci, and the chart-compatible selected-overlap theorem.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_pullbackSquaredDensityFormula_equalitySetOpen_and_chartedOverlapSelectionTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem
        X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_pullbackSquaredDensityFormula_equalitySetOpen_and_overlapSelectionTheorem
    hPull hOpen
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_chartedSelection
      hSelection)

/--
Selected-overlap local package from openness of pointed equality loci and
the global concrete selected-overlap theorem.  The Poincare pullback formula
is now proved from the stored local-isometry data on a Riemann surface.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_equalitySetOpen_and_overlapSelectionTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem
        X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_pullbackSquaredDensityFormula_equalitySetOpen_and_overlapSelectionTheorem
    hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem hOpen hSelection

/--
Selected-overlap local package from openness of pointed equality loci and
the chart-compatible selected-overlap theorem, using the proved Poincare
pullback formula.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_equalitySetOpen_and_chartedOverlapSelectionTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionEqualitySetIsOpenTheorem
        X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_pullbackSquaredDensityFormula_equalitySetOpen_and_chartedOverlapSelectionTheorem
    hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem hOpen hSelection

/--
Selected-overlap local package with the analytic consequence input reduced to
the Poincare pullback squared-density formula plus value-stability for actual
holomorphic local isometries.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_pullbackSquaredDensityFormula_valueStability_and_selectedOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hValue :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityLocalStabilityFromHolomorphicLocalIsometryTheorem
        X)
    (hSelection :
      ∀ (g : HyperbolicMetric X),
        Nonempty
          (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
            ((localCurvatureMetricFormulaAtlasInChartAt g)
              |>.toLocalLiouvilleMetricFormulaAtlas))) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_analyticLocalIsometryConsequences_and_selectedOverlapSelection
    (hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_pullbackSquaredDensityFormula_valueStability
      hPull hValue)
    hSelection

/--
Selected-overlap local package from the Poincare pullback formula,
value-stability for actual holomorphic local isometries, and the global
concrete selected-overlap theorem.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_pullbackSquaredDensityFormula_valueStability_and_overlapSelectionTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hValue :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityLocalStabilityFromHolomorphicLocalIsometryTheorem
        X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_analyticLocalIsometryConsequences_and_overlapSelectionTheorem
    (hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_pullbackSquaredDensityFormula_valueStability
      hPull hValue)
    hSelection

/--
Selected-overlap local package from the Poincare pullback formula,
value-stability for actual holomorphic local isometries, and the
chart-compatible selected-overlap theorem.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_pullbackSquaredDensityFormula_valueStability_and_chartedOverlapSelectionTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hValue :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityLocalStabilityFromHolomorphicLocalIsometryTheorem
        X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_pullbackSquaredDensityFormula_valueStability_and_overlapSelectionTheorem
    hPull hValue
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_chartedSelection
      hSelection)

/--
Selected-overlap local package from value-stability for actual holomorphic
local isometries and the global concrete selected-overlap theorem, using the
proved Poincare pullback formula.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_valueStability_and_overlapSelectionTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (hValue :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityLocalStabilityFromHolomorphicLocalIsometryTheorem
        X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_pullbackSquaredDensityFormula_valueStability_and_overlapSelectionTheorem
    hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem hValue hSelection

/--
Selected-overlap local package from value-stability for actual holomorphic
local isometries and the chart-compatible selected-overlap theorem, using the
proved Poincare pullback formula.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_valueStability_and_chartedOverlapSelectionTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (hValue :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityLocalStabilityFromHolomorphicLocalIsometryTheorem
        X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems_of_pullbackSquaredDensityFormula_valueStability_and_chartedOverlapSelectionTheorem
    hyperbolicLocalChartPullbackSquaredDensityFormulaTheorem hValue hSelection

/--
Charted-curvature-expansion selected-overlap package with the surface
pointed-transition input reduced to coordinate-pullback derivative data.

Compared with
`LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapClosedSchwarzianAnalyticSolvingModularTheorems`,
this no longer asks for the bundled analytic local-isometry consequence
theorem.  The selected overlaps are supplied concretely, pointed Mobius
matches come from the coordinate-pullback frame normalization, and the only
remaining propagation input is the pointed connected-overlap extension
theorem.
-/
structure LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand curvature directly into chart-compatible local curvature formulae. -/
  chartedLocalCurvatureExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X
  /-- The concrete chart-compatible curvature formula atlas selected for each metric. -/
  selectedChartedCurvatureFormulaAtlas :
    ∀ (g : HyperbolicMetric X),
      {curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g //
        LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomain
          curvatureFormulaAtlas}
  /-- Coordinate pullback formulae provide the pointed derivative data. -/
  coordinatePullbackPointedDerivativeData :
    CoordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem
      X
  /-- Pointed matches extend over preconnected chart overlaps. -/
  pointedTransitionExtension :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
      X
  /-- The selected branch predata for the chosen chart-compatible curvature atlas has preconnected overlaps. -/
  selectedOverlapSelection :
    ∀ (g : HyperbolicMetric X),
      Nonempty
        (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
          ((selectedChartedCurvatureFormulaAtlas g).val
            |>.toLocalLiouvilleMetricFormulaAtlas))

/-- Prop-level wrapper for the coordinate-pullback pointed selected-overlap package. -/
def HasLocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedSolvingModularTheorems X)

/--
Canonical chart-at curvature formulae with a selected-overlap package and
pointed connected-overlap propagation give the coordinate-pullback pointed
local package directly.

The pointed coordinate-derivative data is supplied by the proved ambient
chart-transition pullback formula for hyperbolic local charts, so this route
does not require the placeholder-style global assertion that every coordinate
pullback formula uses `chartAt x₀` as its stored coordinate.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedSolvingModularTheorems_of_selectedOverlapSelection_and_pointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedSolvingModularTheorems
      X where
  chartedLocalCurvatureExpansion := chartedLocalCurvatureFormulaExpansionTheorem X
  selectedChartedCurvatureFormulaAtlas := fun g ↦
    ⟨localCurvatureMetricFormulaAtlasInChartAt g, by
      intro x
      exact ⟨fun _ hy ↦ hy, fun _ _ ↦ rfl⟩⟩
  coordinatePullbackPointedDerivativeData :=
    coordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem
  pointedTransitionExtension := hExtend
  selectedOverlapSelection := hSelection

/--
Charted-curvature-expansion selected-overlap package using coordinate-pullback
pointed derivative data and selected-overlap propagation.

This is the coordinate-pullback pointed route with the global connected-overlap
extension removed from the local package.  It asks only for propagation on the
chosen selected predata objects.
-/
structure LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedWithPropagationSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand curvature directly into chart-compatible local curvature formulae. -/
  chartedLocalCurvatureExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X
  /-- The concrete chart-compatible curvature formula atlas selected for each metric. -/
  selectedChartedCurvatureFormulaAtlas :
    ∀ (g : HyperbolicMetric X),
      {curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g //
        LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomain
          curvatureFormulaAtlas}
  /-- Coordinate pullback formulae provide the pointed derivative data. -/
  coordinatePullbackPointedDerivativeData :
    CoordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem
      X
  /-- The selected branch predata carries both preconnected overlaps and selected propagation. -/
  selectedOverlapSelectionWithPropagation :
    ∀ (g : HyperbolicMetric X),
      Nonempty
        (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionWithPropagation
          ((selectedChartedCurvatureFormulaAtlas g).val
            |>.toLocalLiouvilleMetricFormulaAtlas))

/--
Prop-level wrapper for the coordinate-pullback pointed selected-propagation
package.
-/
def HasLocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedWithPropagationSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedWithPropagationSolvingModularTheorems X)

/--
Canonical chart-at curvature formulae with selected-overlap propagation give
the coordinate-pullback pointed local package without any global overlap
extension or coordinate-equality placeholder.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedWithPropagationSolvingModularTheorems_of_canonicalSelectionWithPropagation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapSelectionWithPropagationTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedWithPropagationSolvingModularTheorems
      X where
  chartedLocalCurvatureExpansion := chartedLocalCurvatureFormulaExpansionTheorem X
  selectedChartedCurvatureFormulaAtlas := fun g ↦
    ⟨localCurvatureMetricFormulaAtlasInChartAt g, by
      intro x
      exact ⟨fun _ hy ↦ hy, fun _ _ ↦ rfl⟩⟩
  coordinatePullbackPointedDerivativeData :=
    coordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem
  selectedOverlapSelectionWithPropagation := hSelection

/--
Coordinate-pullback pointed local package from split canonical selected-overlap
inputs: selected predata and propagation on that selected predata.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedWithPropagationSolvingModularTheorems_of_canonicalSelection_and_selectedPointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X)
    (hExtend :
      CanonicalChartedCurvatureSelectedOverlapPointedTransitionExtendsTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedWithPropagationSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedWithPropagationSolvingModularTheorems_of_canonicalSelectionWithPropagation
    (canonicalChartedCurvaturePreconnectedOverlapSelectionWithPropagationTheorem_of_selection_and_selectedPointedExtension
      hSelection hExtend)

/--
Coordinate-pullback pointed local package from a canonical selected-overlap
theorem and propagation only for the selected witnesses it chooses.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedWithPropagationSolvingModularTheorems_of_canonicalSelection_and_chosenSelectedPointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X)
    (hExtend :
      CanonicalChartedCurvatureChosenSelectedOverlapPointedTransitionExtendsTheorem
        hSelection) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedWithPropagationSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedWithPropagationSolvingModularTheorems_of_canonicalSelectionWithPropagation
    (canonicalChartedCurvaturePreconnectedOverlapSelectionWithPropagationTheorem_of_selection_and_chosenSelectedPointedExtension
      hSelection hExtend)

/--
Charted-curvature-expansion selected-overlap package where the coordinate
pullback pointed derivative data are extracted from chart-compatibility of
the coordinate pullback formulae.

This is the same selected-overlap route as
`LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinatePullbackPointedSolvingModularTheorems`,
but with the derivative-identification input replaced by the more geometric
statement that each stored coordinate agrees with the ambient chart on its
formula domain.
-/
structure LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinateEqOnChartAtSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand curvature directly into chart-compatible local curvature formulae. -/
  chartedLocalCurvatureExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X
  /-- The concrete chart-compatible curvature formula atlas selected for each metric. -/
  selectedChartedCurvatureFormulaAtlas :
    ∀ (g : HyperbolicMetric X),
      {curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g //
        LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomain
          curvatureFormulaAtlas}
  /-- Coordinate pullback formulae use the ambient chart on their formula domains. -/
  coordinatePullbackCoordinateEqOnChartAt :
    CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X
  /-- Pointed matches extend over preconnected chart overlaps. -/
  pointedTransitionExtension :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
      X
  /-- The selected branch predata for the chosen chart-compatible curvature atlas has preconnected overlaps. -/
  selectedOverlapSelection :
    ∀ (g : HyperbolicMetric X),
      Nonempty
        (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
          ((selectedChartedCurvatureFormulaAtlas g).val
            |>.toLocalLiouvilleMetricFormulaAtlas))

/-- Prop-level wrapper for the coordinate-charted selected-overlap package. -/
def HasLocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinateEqOnChartAtSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinateEqOnChartAtSolvingModularTheorems X)

/--
Charted-curvature-expansion selected-overlap package where chart-compatibility
is required only for the chosen surface predata object.

This is sharper than
`LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapCoordinateEqOnChartAtSolvingModularTheorems`:
it does not require every coordinate pullback formula to be chart-compatible,
only the coordinate pullback formulae actually selected for the surface
branch atlas.
-/
structure LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand curvature directly into chart-compatible local curvature formulae. -/
  chartedLocalCurvatureExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X
  /-- The concrete chart-compatible curvature formula atlas selected for each metric. -/
  selectedChartedCurvatureFormulaAtlas :
    ∀ (g : HyperbolicMetric X),
      {curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g //
        LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomain
          curvatureFormulaAtlas}
  /-- Pointed matches extend over preconnected chart overlaps. -/
  pointedTransitionExtension :
    PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
      X
  /-- The selected branch predata for the chosen chart-compatible curvature atlas is chart-compatible and has preconnected overlaps. -/
  selectedOverlapChartedSelection :
    ∀ (g : HyperbolicMetric X),
      Nonempty
        (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
          ((selectedChartedCurvatureFormulaAtlas g).val
            |>.toLocalLiouvilleMetricFormulaAtlas))

/-- Prop-level wrapper for the selected charted-predata package. -/
def HasLocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataSolvingModularTheorems X)

/--
Charted-curvature-expansion selected-overlap package where all surface
assembly data are carried by one selected predata object.

The selected object includes open restricted domains, preconnected overlaps,
chart-compatibility of its own coordinate pullback formulae, and propagation
of pointed comparisons on its own overlaps.
-/
structure LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand curvature directly into chart-compatible local curvature formulae. -/
  chartedLocalCurvatureExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X
  /-- The concrete chart-compatible curvature formula atlas selected for each metric. -/
  selectedChartedCurvatureFormulaAtlas :
    ∀ (g : HyperbolicMetric X),
      {curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g //
        LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomain
          curvatureFormulaAtlas}
  /-- The selected branch predata for the chosen chart-compatible curvature atlas carries all surface assembly data. -/
  selectedOverlapChartedSelectionWithPropagation :
    ∀ (g : HyperbolicMetric X),
      Nonempty
        (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagation
          ((selectedChartedCurvatureFormulaAtlas g).val
            |>.toLocalLiouvilleMetricFormulaAtlas))

/-- Prop-level wrapper for the selected charted-predata-with-propagation package. -/
def HasLocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems X)

/--
Charted-curvature-expansion selected-overlap package where all surface
assembly data are carried by one locally charted selected predata object.

Compared with the charted-predata package, the coordinate compatibility is
local at each point of the selected pullback formula domains.
-/
structure LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- Expand curvature directly into chart-compatible local curvature formulae. -/
  chartedLocalCurvatureExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X
  /-- The concrete chart-compatible curvature formula atlas selected for each metric. -/
  selectedChartedCurvatureFormulaAtlas :
    ∀ (g : HyperbolicMetric X),
      {curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g //
        LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomain
          curvatureFormulaAtlas}
  /-- The selected branch predata carries local chart-compatibility and selected-overlap propagation. -/
  selectedOverlapLocallyChartedSelectionWithPropagation :
    ∀ (g : HyperbolicMetric X),
      Nonempty
        (SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagation
          ((selectedChartedCurvatureFormulaAtlas g).val
            |>.toLocalLiouvilleMetricFormulaAtlas))

/-- Prop-level wrapper for the selected locally charted predata-with-propagation package. -/
def HasLocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  Nonempty
    (LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems X)

/--
Charted curvature expansion, a global charted selected-predata theorem, and
global pointed connected-overlap propagation produce the selected-predata
with-propagation local package.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems_of_chartedSelection_and_pointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems
      X where
  chartedLocalCurvatureExpansion := hExpansion
  selectedChartedCurvatureFormulaAtlas := fun g ↦ Classical.choice (hExpansion g)
  selectedOverlapChartedSelectionWithPropagation := by
    intro g
    exact
      surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagationTheorem_of_chartedSelection_and_pointedExtension
        hSelection hExtend g
        ((Classical.choice (hExpansion g)).val
          |>.toLocalLiouvilleMetricFormulaAtlas)

/--
Charted curvature expansion, a global charted selected-predata theorem, and
selected one-jet local uniqueness produce the selected-predata
with-propagation local package.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems_of_chartedSelection_and_selectedOneJetLocalUniqueness
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X)
    (hUnique :
      SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems
      X where
  chartedLocalCurvatureExpansion := hExpansion
  selectedChartedCurvatureFormulaAtlas := fun g ↦ Classical.choice (hExpansion g)
  selectedOverlapChartedSelectionWithPropagation := by
    intro g
    exact
      surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagationTheorem_of_chartedSelection_and_selectedOneJetLocalUniqueness
        hSelection hUnique g
        ((Classical.choice (hExpansion g)).val
          |>.toLocalLiouvilleMetricFormulaAtlas)

/--
Charted curvature expansion and charted selected predata can use global
one-jet connected-overlap propagation directly.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems_of_chartedSelection_and_pointedOneJetExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems_of_chartedSelection_and_selectedOneJetLocalUniqueness
    hExpansion hSelection
    (surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem_of_oneJetExtension
      hExtend)

/--
Charted selected predata can also be driven by the one-jet clopen-locus
propagation theorem.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems_of_chartedSelection_and_oneJetEqualitySetClopen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X)
    (hClopen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems_of_chartedSelection_and_pointedOneJetExtension
    hExpansion hSelection
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySetClopen
      hClopen)

/--
Canonical chart-at curvature formulae with one selected preconnected-overlap
selector per metric give the selected-overlap charted-predata-with-propagation
package.  Coordinate-pullback `chartAt` compatibility supplies the charted
part of the selected predata, and selected one-jet local uniqueness supplies
propagation across the selected overlaps.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems_of_selectedOverlapSelection_coordinateEqOnChartAt_and_selectedOneJetLocalUniqueness
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X)
    (hUnique :
      SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems
      X where
  chartedLocalCurvatureExpansion := chartedLocalCurvatureFormulaExpansionTheorem X
  selectedChartedCurvatureFormulaAtlas := fun g ↦
    ⟨localCurvatureMetricFormulaAtlasInChartAt g, by
      intro x
      exact ⟨fun _ hy ↦ hy, fun _ _ ↦ rfl⟩⟩
  selectedOverlapChartedSelectionWithPropagation := by
    intro g
    rcases hSelection g with ⟨S⟩
    let C :=
      surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection_of_selection_and_coordinateEqOnChartAt_for
        S hChart
    exact
      ⟨{ chartedSelection := C
         selected_pointed_extension := by
          exact
            surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps_of_oneJet
              (by
                simpa [SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection.toPreconnectedOverlapPreData]
                  using hUnique C) }⟩

/--
Canonical chart-at curvature formulae with a selected branch/topology package
give the selected-overlap charted-predata-with-propagation package directly.
This keeps the sharp overlap-selection target visible at the modular boundary.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems_of_canonicalBranchSelection_coordinateEqOnChartAt_and_selectedOneJetLocalUniqueness
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem X)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X)
    (hUnique :
      SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapChartedPreDataWithPropagationSolvingModularTheorems_of_selectedOverlapSelection_coordinateEqOnChartAt_and_selectedOneJetLocalUniqueness
    (canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_branchSelection
      hSelection)
    hChart hUnique

/--
Charted curvature expansion, a global locally charted selected-predata
theorem, and selected one-jet local uniqueness produce the locally charted
selected-predata-with-propagation local package.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems_of_locallyChartedSelection_and_selectedOneJetLocalUniqueness
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionTheorem
        X)
    (hUnique :
      SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems
      X where
  chartedLocalCurvatureExpansion := hExpansion
  selectedChartedCurvatureFormulaAtlas := fun g ↦ Classical.choice (hExpansion g)
  selectedOverlapLocallyChartedSelectionWithPropagation := by
    intro g
    exact
      surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagationTheorem_of_locallyChartedSelection_and_selectedOneJetLocalUniqueness
        hSelection hUnique g
        ((Classical.choice (hExpansion g)).val
          |>.toLocalLiouvilleMetricFormulaAtlas)

/--
The locally charted selected-predata package can be built directly from
global one-jet connected-overlap propagation.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems_of_locallyChartedSelection_and_pointedOneJetExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionTheorem
        X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems_of_locallyChartedSelection_and_selectedOneJetLocalUniqueness
    hExpansion hSelection
    (surfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem_of_oneJetExtension
      hExtend)

/--
The locally charted selected-predata package can be built from one-jet clopen
propagation on local-chart overlaps.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems_of_locallyChartedSelection_and_oneJetEqualitySetClopen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionTheorem
        X)
    (hClopen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsClopenTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems_of_locallyChartedSelection_and_pointedOneJetExtension
    hExpansion hSelection
    (pointedHyperbolicLocalChartRealMobiusTransitionOneJetExtendsOnPreconnectedOverlapTheorem_of_oneJetEqualitySetClopen
      hClopen)

/--
A coordinate-eventual identity theorem turns ordinary selected overlaps for
the canonical chart-at curvature atlas into locally charted selected overlaps;
selected one-jet local uniqueness supplies propagation.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems_of_selectedOverlapSelection_coordinateEventuallyEqOnChartAt_and_selectedOneJetLocalUniqueness
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqTheorem
        X)
    (hUnique :
      SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems
      X where
  chartedLocalCurvatureExpansion := chartedLocalCurvatureFormulaExpansionTheorem X
  selectedChartedCurvatureFormulaAtlas := fun g ↦
    ⟨localCurvatureMetricFormulaAtlasInChartAt g, by
      intro x
      exact ⟨fun _ hy ↦ hy, fun _ _ ↦ rfl⟩⟩
  selectedOverlapLocallyChartedSelectionWithPropagation := by
    intro g
    rcases hSelection g with ⟨S⟩
    let C :
        SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection
          ((localCurvatureMetricFormulaAtlasInChartAt g)
            |>.toLocalLiouvilleMetricFormulaAtlas) :=
      { selection := S
        coordinate_eventuallyEqOn_chartAt := by
          intro x x₀ hx₀
          exact
            hChart g
              (((S.toPreData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).pullbackFormula)
              x₀ hx₀ }
    exact
      ⟨{ locallyChartedSelection := C
         selected_pointed_extension := by
          exact
            surfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps_of_oneJet
              (by
                simpa [SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection.toPreconnectedOverlapPreData]
                  using hUnique C) }⟩

/--
Canonical chart-at curvature formulae with a selected branch/topology package
give the locally charted selected-overlap-with-propagation package directly.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems_of_canonicalBranchSelection_coordinateEventuallyEqOnChartAt_and_selectedOneJetLocalUniqueness
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem X)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqTheorem
        X)
    (hUnique :
      SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems_of_selectedOverlapSelection_coordinateEventuallyEqOnChartAt_and_selectedOneJetLocalUniqueness
    (canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_branchSelection
      hSelection)
    hChart hUnique

/--
The older domainwise charted selected one-jet route also gives the locally
charted package by forgetting charted selectors to locally charted selectors.
-/
noncomputable def localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems_of_chartedSelection_and_selectedOneJetLocalUniqueness
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hExpansion : ChartedLocalCurvatureFormulaExpansionTheorem X)
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X)
    (hUnique :
      SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessLocallyChartedTheorem
        X) :
    LocalMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems
      X :=
  localMetricSchwarzianFrobeniusChartedCurvatureExpansionSelectedOverlapLocallyChartedPreDataWithPropagationSolvingModularTheorems_of_locallyChartedSelection_and_selectedOneJetLocalUniqueness
    hExpansion
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionTheorem_of_chartedSelection
      hSelection)
    hUnique

end HyperbolicMetric

end

end JJMath
