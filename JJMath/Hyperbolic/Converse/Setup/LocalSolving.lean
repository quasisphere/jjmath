import JJMath.Hyperbolic.Converse.Setup.Statements

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

/-- Global data target for local curvature-derived solving. -/
abbrev LocalCurvatureSolvingTheorem (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] :=
  ∀ (g : HyperbolicMetric X), g.HasCurvatureLiouvilleDevelopingConstructionAtlas

/--
Global theorem target for expanding the abstract curvature predicate into the
local conformal curvature formula `K = -exp (-2u) Δu`.

This is the remaining geometric bridge between the lightweight
`ConformalMetric.curvature_eq` predicate and the coordinate formula layer.
-/
def LocalCurvatureFormulaExpansionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X), g.HasLocalCurvatureMetricFormulaAtlas

/--
Local solving data for one curvature-derived Liouville formula atlas.

This isolates the PDE step after curvature has already been expanded into
local Liouville formulas.
-/
structure LocalSolvingFromCurvatureFormula (g : HyperbolicMetric X)
    (curvatureFormulaAtlas : CurvatureLiouvilleFormulaAtlas X g) where
  /-- Local upper-half-plane developing constructions solving the metric formulas. -/
  developingConstructionAtlas : LocalLiouvilleDevelopingConstructionAtlas X g
  /-- The constructions solve exactly the chosen curvature-derived formulas. -/
  constructions_solve_curvature_formulas :
    developingConstructionAtlas.toLocalLiouvilleMetricFormulaAtlas =
      curvatureFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas

/--
Local solving data for an arbitrary Liouville metric-formula atlas.

This isolates the local PDE/ODE step independently of curvature provenance:
given local conformal factors satisfying Liouville's equation, construct local
maps to `ℍ` whose Poincare pullback formulas realize the metric, with
real-Mobius overlap transitions.
-/
structure LocalSolvingFromLiouvilleFormulaAtlas (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- Local upper-half-plane developing constructions solving the metric formulas. -/
  developingConstructionAtlas : LocalLiouvilleDevelopingConstructionAtlas X g
  /-- The constructions solve exactly the chosen Liouville metric formulas. -/
  constructions_solve_metric_formulas :
    developingConstructionAtlas.toLocalLiouvilleMetricFormulaAtlas =
      metricFormulaAtlas

/--
Local solving data obtained from Schwarzian branches over a Liouville
metric-formula atlas.

This is slightly weaker, and closer to the analytic construction, than
`LocalSolvingFromLiouvilleFormulaAtlas`: the Schwarzian solution branch may be
defined on a smaller coordinate neighbourhood, so the produced developing
solution uses the restricted conformal factor recorded in
`SurfaceSchwarzianBranchData`.
-/
structure LocalSolvingFromSchwarzianBranchData (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) where
  /-- Schwarzian data, upper-half-plane branches, and real Mobius transitions. -/
  branchData : SurfaceSchwarzianBranchData metricFormulaAtlas

namespace LocalSolvingFromSchwarzianBranchData

variable {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

/-- The local Liouville developing-solution atlas produced by the branch data. -/
def toLocalLiouvilleDevelopingSolutionAtlas
    (S : LocalSolvingFromSchwarzianBranchData g metricFormulaAtlas) :
    LocalLiouvilleDevelopingSolutionAtlas X g :=
  S.branchData.toLocalLiouvilleDevelopingSolutionAtlas

omit [RiemannSurface X] in
/-- Schwarzian branch solving gives the metric-level local developing-solution target. -/
theorem hasLocalLiouvilleDevelopingSolutionAtlas
    (S : LocalSolvingFromSchwarzianBranchData g metricFormulaAtlas) :
    g.HasLocalLiouvilleDevelopingSolutionAtlas :=
  ⟨S.toLocalLiouvilleDevelopingSolutionAtlas⟩

omit [RiemannSurface X] in
/-- Schwarzian branch solving gives coordinate Poincare pullback formulas. -/
theorem hasCoordinateUpperHalfPlanePullbackFormulaAtlas
    (S : LocalSolvingFromSchwarzianBranchData g metricFormulaAtlas) :
    g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas :=
  HyperbolicMetric.hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasLocalLiouvilleDevelopingSolutionAtlas
    S.hasLocalLiouvilleDevelopingSolutionAtlas

omit [RiemannSurface X] in
/-- Schwarzian branch solving gives local upper-half-plane models. -/
theorem hasUpperHalfPlaneLocalModels
    (S : LocalSolvingFromSchwarzianBranchData g metricFormulaAtlas) :
    g.HasUpperHalfPlaneLocalModels :=
  HyperbolicMetric.hasUpperHalfPlaneLocalModels_of_hasLocalLiouvilleDevelopingSolutionAtlas
    S.hasLocalLiouvilleDevelopingSolutionAtlas

end LocalSolvingFromSchwarzianBranchData

/--
Local solving data obtained from pointed Schwarzian branches over a Liouville
metric-formula atlas.

This matches the actual local ODE output more closely than
`LocalSolvingFromSchwarzianBranchData`: each branch is only required to contain
the coordinate of its base point.  The branch data then shrinks the surface
formula domains before producing the local developing atlas.
-/
structure LocalSolvingFromPointedSchwarzianBranchData (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) where
  /--
  Pointed Schwarzian data, upper-half-plane branches, surface-domain shrinkings,
  and real Mobius transitions after shrinking.
  -/
  branchData : SurfaceSchwarzianPointedBranchData metricFormulaAtlas

namespace LocalSolvingFromPointedSchwarzianBranchData

variable {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}

/-- The local Liouville developing-solution atlas produced by pointed branch data. -/
def toLocalLiouvilleDevelopingSolutionAtlas
    (S : LocalSolvingFromPointedSchwarzianBranchData g metricFormulaAtlas) :
    LocalLiouvilleDevelopingSolutionAtlas X g :=
  S.branchData.toLocalLiouvilleDevelopingSolutionAtlas

omit [RiemannSurface X] in
/-- Pointed Schwarzian branch solving gives the metric-level local target. -/
theorem hasLocalLiouvilleDevelopingSolutionAtlas
    (S : LocalSolvingFromPointedSchwarzianBranchData g metricFormulaAtlas) :
    g.HasLocalLiouvilleDevelopingSolutionAtlas :=
  ⟨S.toLocalLiouvilleDevelopingSolutionAtlas⟩

omit [RiemannSurface X] in
/-- Pointed Schwarzian branch solving gives coordinate Poincare pullback formulas. -/
theorem hasCoordinateUpperHalfPlanePullbackFormulaAtlas
    (S : LocalSolvingFromPointedSchwarzianBranchData g metricFormulaAtlas) :
    g.HasCoordinateUpperHalfPlanePullbackFormulaAtlas :=
  HyperbolicMetric.hasCoordinateUpperHalfPlanePullbackFormulaAtlas_of_hasLocalLiouvilleDevelopingSolutionAtlas
    S.hasLocalLiouvilleDevelopingSolutionAtlas

omit [RiemannSurface X] in
/-- Pointed Schwarzian branch solving gives local upper-half-plane models. -/
theorem hasUpperHalfPlaneLocalModels
    (S : LocalSolvingFromPointedSchwarzianBranchData g metricFormulaAtlas) :
    g.HasUpperHalfPlaneLocalModels :=
  HyperbolicMetric.hasUpperHalfPlaneLocalModels_of_hasLocalLiouvilleDevelopingSolutionAtlas
    S.hasLocalLiouvilleDevelopingSolutionAtlas

end LocalSolvingFromPointedSchwarzianBranchData

/--
Global theorem target for choosing Schwarzian data and upper-half-plane
branches over any Liouville metric-formula atlas.
-/
def SurfaceSchwarzianBranchDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g),
    Nonempty (SurfaceSchwarzianBranchData metricFormulaAtlas)

/--
Global theorem target for choosing pointed Schwarzian branches over any
Liouville metric-formula atlas.

This is currently the sharper local ODE boundary: branches only need to be
defined at the base coordinate, and the surface domains are then shrunk to fit
the branch domains.
-/
def SurfaceSchwarzianPointedBranchDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g),
    Nonempty (SurfaceSchwarzianPointedBranchData metricFormulaAtlas)

/--
Global theorem target for assembling coordinate real branch atlases into
pointed surface branch data over any Liouville metric-formula atlas.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g),
    Nonempty (SurfaceRealUpperHalfPlaneBranchAtlasData metricFormulaAtlas)

/--
Surface assembly theorem target.

Given a real upper-half-plane branch atlas in every coordinate conformal factor
of a Liouville formula atlas, assemble the selected pointed branches into
surface data by proving the required surface-domain openness and real Mobius
compatibility after shrinking.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasAssemblyTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g),
    (∀ x : X,
      Nonempty
        (LocalRealUpperHalfPlaneBranchAtlas
          (metricFormulaAtlas.formulaAt x).conformalFactor)) →
      Nonempty (SurfaceRealUpperHalfPlaneBranchAtlasData metricFormulaAtlas)

/--
Surface-domain openness target for coordinate real branch atlases.

Once the local Liouville formulas are tied to genuine continuous coordinate
charts, this should follow by taking the preimage of the open branch domain and
intersecting with the open formula domain.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g)
    (realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (metricFormulaAtlas.formulaAt x).conformalFactor),
    ∀ x : X, IsOpen
      {y : X | y ∈ (metricFormulaAtlas.formulaAt x).domain ∧
        (metricFormulaAtlas.formulaAt x).coordinate y ∈
          ((realBranchAtlasAt x).branchNear
            ⟨(metricFormulaAtlas.formulaAt x).coordinate x,
              (metricFormulaAtlas.formulaAt x).coordinate_mem_conformalFactor_domain x
                (metricFormulaAtlas.mem_formulaAt_domain x)⟩).domain}

/--
Surface-domain openness for one chosen Liouville metric formula atlas.

This is the pointwise version of
`SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem`.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) : Prop :=
  ∀ (realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (metricFormulaAtlas.formulaAt x).conformalFactor),
    ∀ x : X, IsOpen
      {y : X | y ∈ (metricFormulaAtlas.formulaAt x).domain ∧
        (metricFormulaAtlas.formulaAt x).coordinate y ∈
          ((realBranchAtlasAt x).branchNear
            ⟨(metricFormulaAtlas.formulaAt x).coordinate x,
              (metricFormulaAtlas.formulaAt x).coordinate_mem_conformalFactor_domain x
                (metricFormulaAtlas.mem_formulaAt_domain x)⟩).domain}

/--
Surface real-Mobius transition compatibility for one chosen Liouville metric
formula atlas.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasSurfaceTransitionFor
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) : Prop :=
  ∀ (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas),
    ∀ x y : X,
      HyperbolicLocalChart.HasRealMobiusTransition
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)

/--
Overlapping off-diagonal surface real-Mobius transition compatibility for one
chosen Liouville metric formula atlas.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionFor
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) : Prop :=
  ∀ (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas),
    ∀ x y : X, x ≠ y →
      Set.Nonempty
        ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) →
      HyperbolicLocalChart.HasRealMobiusTransition
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)

/--
Curvature-derived overlapping off-diagonal surface transition target.

This is sharper than the Liouville-atlas target: it only asks for the
Liouville formula atlases obtained by rewriting local curvature formula
atlases.
-/
def LocalCurvatureMetricFormulaAtlasOverlappingOffDiagonalSurfaceTransitionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g),
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionFor
      curvatureFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas

/--
Coordinate-preimage openness for Liouville metric formula atlases.

This is the formula-atlas topological input behind restricted branch-domain
openness.  It says that if one restricts a local metric formula by an open set
in its coordinate image, the resulting surface domain is open.
-/
def LocalLiouvilleMetricFormulaAtlasCoordinatePreimageOpennessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g)
    (x : X) (V : Set ℂ),
    IsOpen V →
      IsOpen
        {y : X | y ∈ (metricFormulaAtlas.formulaAt x).domain ∧
          (metricFormulaAtlas.formulaAt x).coordinate y ∈ V}

/--
Global continuity of the coordinate maps in a Liouville metric formula atlas.

This is stronger than ultimately necessary, but gives a simple mathlib-backed
route to coordinate-preimage openness while the formula structure stores bare
coordinate functions.
-/
def LocalLiouvilleMetricFormulaAtlasCoordinateContinuityTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g)
    (x : X),
    Continuous (metricFormulaAtlas.formulaAt x).coordinate

/--
Continuity of the coordinate maps on their formula domains.

This is the natural topological hypothesis for restricting local Liouville
formulae: preimages only need to be open after intersecting with the formula
domain.
-/
def LocalLiouvilleMetricFormulaAtlasCoordinateContinuousOnDomainTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g)
    (x : X),
    ContinuousOn (metricFormulaAtlas.formulaAt x).coordinate
      (metricFormulaAtlas.formulaAt x).domain

/--
Pointwise chart-compatibility predicate for a chosen Liouville metric formula
atlas.
-/
def LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g) : Prop :=
  ∀ x : X,
    (metricFormulaAtlas.formulaAt x).domain ⊆ (chartAt ℂ x).source ∧
      Set.EqOn (metricFormulaAtlas.formulaAt x).coordinate
        (chartAt ℂ x) (metricFormulaAtlas.formulaAt x).domain

/--
Pointwise chart-compatibility predicate for a chosen local curvature formula
atlas.
-/
def LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g) : Prop :=
  ∀ x : X,
    (curvatureFormulaAtlas.formulaAt x).domain ⊆ (chartAt ℂ x).source ∧
      Set.EqOn (curvatureFormulaAtlas.formulaAt x).coordinate
        (chartAt ℂ x) (curvatureFormulaAtlas.formulaAt x).domain

/--
The local formula coordinates are restrictions of the ambient charted-space
coordinates.

This is the geometric source of the domainwise continuity condition: each
formula domain is contained in the source of the chosen chart, and the stored
coordinate function agrees there with that chart.
-/
def LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomainTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g),
    LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain metricFormulaAtlas

/--
The curvature formula coordinates are restrictions of the ambient
charted-space coordinates.
-/
def LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomainTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g),
    LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomain curvatureFormulaAtlas

/--
Charted curvature expansion theorem.

This is the sharper geometric form of local curvature expansion: for every
hyperbolic metric, choose local curvature formulae whose coordinate maps are
already restrictions of the ambient charted-space coordinates.
-/
def ChartedLocalCurvatureFormulaExpansionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X),
    Nonempty
      {curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g //
        LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomain
          curvatureFormulaAtlas}

/--
Separate curvature expansion and global chart-compatibility imply the bundled
charted curvature expansion theorem.
-/
theorem chartedLocalCurvatureFormulaExpansionTheorem_of_expansion_and_coordinateCharted
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hExpansion : LocalCurvatureFormulaExpansionTheorem X)
    (hCharted : LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomainTheorem X) :
    ChartedLocalCurvatureFormulaExpansionTheorem X := by
  intro g
  refine ⟨⟨Classical.choice (hExpansion g), ?_⟩⟩
  exact hCharted g (Classical.choice (hExpansion g))

/--
The charted curvature expansion carried by a hyperbolic metric.

For each point we use the ambient chart `chartAt ℂ x` and the logarithmic
density `logDensityFromDensitySq` of the metric in that chart.  The stored
smoothness of the metric gives the required regularity of the logarithmic
density, positivity gives `exp (2u) = densitySq`, and
`g.curvature_minus_one` is exactly the local curvature equation for this
choice of `u`.
-/
noncomputable def localCurvatureMetricFormulaInChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) (x : X) :
    LocalCurvatureMetricFormula X g where
  domain := (chartAt ℂ x).source
  isOpen_domain := (chartAt ℂ x).open_source
  coordinate := chartAt ℂ x
  chart := chartAt ℂ x
  chart_mem_atlas := chart_mem_atlas ℂ x
  domain_subset_chart_source := fun _ hy ↦ hy
  coordinate_eq_chart := fun _ _ ↦ rfl
  conformalFactor :=
    let ρ : ℂ → ℝ :=
      g.toConformalMetric.densitySqInChart
        (chartAt ℂ x) (chart_mem_atlas ℂ x)
    { coordinateDomain := (chartAt ℂ x).target
      isOpen_coordinateDomain := (chartAt ℂ x).open_target
      logDensity := logDensityFromDensitySq ρ
      logDensity_contDiffOn := by
        have hρ : ContDiffOn ℝ ⊤ ρ ((chartAt ℂ x).target) :=
          g.smooth (chartAt ℂ x) (chart_mem_atlas ℂ x)
        have hlog :
            ContDiffOn ℝ ⊤ (fun z : ℂ ↦ Real.log (ρ z))
              ((chartAt ℂ x).target) :=
          hρ.log (fun z hz ↦
            ne_of_gt
              (g.toConformalMetric.positive_densitySqInChart
                (chartAt ℂ x) (chart_mem_atlas ℂ x) hz))
        have hlogDiv :
            ContDiffOn ℝ ⊤ (fun z : ℂ ↦ Real.log (ρ z) / 2)
              ((chartAt ℂ x).target) :=
          hlog.div_const 2
        simpa [logDensityFromDensitySq] using hlogDiv.of_le le_top
      twice_differentiable_on_domain := by
        have hρ : ContDiffOn ℝ ⊤ ρ ((chartAt ℂ x).target) :=
          g.smooth (chartAt ℂ x) (chart_mem_atlas ℂ x)
        have hlog :
            ContDiffOn ℝ ⊤ (fun z : ℂ ↦ Real.log (ρ z))
              ((chartAt ℂ x).target) :=
          hρ.log (fun z hz ↦
            ne_of_gt
              (g.toConformalMetric.positive_densitySqInChart
                (chartAt ℂ x) (chart_mem_atlas ℂ x) hz))
        have hlogDiv :
            ContDiffOn ℝ ⊤ (fun z : ℂ ↦ Real.log (ρ z) / 2)
              ((chartAt ℂ x).target) :=
          hlog.div_const 2
        simpa [logDensityFromDensitySq] using hlogDiv.of_le le_top }
  coordinate_mem_conformalFactor_domain := by
    intro y hy
    exact (chartAt ℂ x).map_source hy
  curvature_minus_one := by
    intro z hz
    change
      gaussianCurvatureOfDensitySq
        (g.toConformalMetric.densitySqInChart
          (chartAt ℂ x) (chart_mem_atlas ℂ x)) z = -1
    simpa [ConformalMetric.gaussianCurvatureInChart] using
      g.curvature_minus_one (chartAt ℂ x) (chart_mem_atlas ℂ x) z hz
  densitySqInChart_eq_conformalFactor := by
    intro y hy
    let ρ : ℂ → ℝ :=
      g.toConformalMetric.densitySqInChart
        (chartAt ℂ x) (chart_mem_atlas ℂ x)
    have htarget : (chartAt ℂ x) y ∈ (chartAt ℂ x).target :=
      (chartAt ℂ x).map_source hy
    have hpos : 0 < ρ ((chartAt ℂ x) y) :=
      g.toConformalMetric.positive_densitySqInChart
        (chartAt ℂ x) (chart_mem_atlas ℂ x) htarget
    have hlog :
        ρ ((chartAt ℂ x) y) =
          Real.exp (Real.log (ρ ((chartAt ℂ x) y))) :=
      (Real.exp_log hpos).symm
    calc
      ρ ((chartAt ℂ x) y)
          = Real.exp (Real.log (ρ ((chartAt ℂ x) y))) := hlog
      _ = Real.exp (2 * (Real.log (ρ ((chartAt ℂ x) y)) / 2)) := by
            ring_nf

/-- The curvature formula atlas obtained from the ambient complex charts. -/
noncomputable def localCurvatureMetricFormulaAtlasInChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) :
    LocalCurvatureMetricFormulaAtlas X g where
  formulaAt x := localCurvatureMetricFormulaInChartAt g x
  mem_formulaAt_domain x := mem_chart_source ℂ x

/--
Every hyperbolic metric has a chart-compatible local curvature formula atlas.
-/
theorem chartedLocalCurvatureFormulaExpansionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] :
    ChartedLocalCurvatureFormulaExpansionTheorem X := by
  intro g
  refine ⟨⟨localCurvatureMetricFormulaAtlasInChartAt g, ?_⟩⟩
  intro x
  exact ⟨fun _ hy ↦ hy, fun _ _ ↦ rfl⟩

/--
If a local formula coordinate agrees with the ambient chart on an open formula
domain, then preimages of open coordinate subsets are open in the surface.

This is the basic topological bridge used below: it is exactly mathlib's
`ContinuousOn.isOpen_inter_preimage` applied to the chart map.
-/
theorem isOpen_formulaCoordinate_preimage_of_eqOn_chartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x : X} {U : Set X} (hU : IsOpen U)
    {coordinate : X → ℂ}
    (hSub : U ⊆ (chartAt ℂ x).source)
    (hEq : Set.EqOn coordinate (chartAt ℂ x) U)
    {V : Set ℂ} (hV : IsOpen V) :
    IsOpen {y : X | y ∈ U ∧ coordinate y ∈ V} := by
  have hCont : ContinuousOn coordinate U :=
    ((chartAt ℂ x).continuousOn_toFun.mono hSub).congr hEq
  simpa [Set.preimage, Set.inter_def] using
    hCont.isOpen_inter_preimage hU hV

/--
Pointwise chart-compatibility supplies coordinate-preimage openness for one
chosen Liouville metric formula atlas.
-/
def localLiouvilleMetricFormulaAtlasCoordinatePreimageOpenness_of_coordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (hChart :
      LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain
        metricFormulaAtlas) :
    ∀ (x : X) (V : Set ℂ),
      IsOpen V →
        IsOpen
          {y : X | y ∈ (metricFormulaAtlas.formulaAt x).domain ∧
            (metricFormulaAtlas.formulaAt x).coordinate y ∈ V} := by
  intro x V hV
  rcases hChart x with ⟨hSub, hEq⟩
  exact
    isOpen_formulaCoordinate_preimage_of_eqOn_chartAt
      (metricFormulaAtlas.formulaAt x).isOpen_domain hSub hEq hV

/--
Coordinate-preimage openness for one chosen local curvature formula atlas.

This is the curvature-atlas version of
`LocalLiouvilleMetricFormulaAtlasCoordinatePreimageOpennessTheorem`: it only
asks for the Liouville atlases obtained by rewriting curvature formulas.
-/
def LocalCurvatureMetricFormulaAtlasCoordinatePreimageOpenness
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    (curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g) : Prop :=
  ∀ (x : X) (V : Set ℂ),
    IsOpen V →
      IsOpen
        {y : X | y ∈ (curvatureFormulaAtlas.formulaAt x).domain ∧
          (curvatureFormulaAtlas.formulaAt x).coordinate y ∈ V}

/--
Curvature-atlas coordinate-preimage openness theorem.

This is weaker than the corresponding Liouville-atlas theorem, since it is
required only for curvature formula atlases.
-/
def LocalCurvatureMetricFormulaAtlasCoordinatePreimageOpennessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g),
    LocalCurvatureMetricFormulaAtlasCoordinatePreimageOpenness
      curvatureFormulaAtlas

/--
Restricted surface-domain openness for Liouville atlases obtained from
curvature formula atlases.
-/
def LocalCurvatureMetricFormulaAtlasRestrictedDomainOpennessTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g),
    SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor
      curvatureFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas

/--
Surface transition target for the shrunk branches selected from coordinate
real branch atlases.

The local real atlases give transitions only inside a single coordinate
formula.  This target is the cross-chart compatibility needed after the
surface domains have been shrunk.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasSurfaceTransitionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g)
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas),
    ∀ x y : X,
      HyperbolicLocalChart.HasRealMobiusTransition
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)

/--
Off-diagonal surface transition target for the shrunk branches selected from
coordinate real branch atlases.

The diagonal case is formal: a chart has identity transition to itself.  Thus
the actual cross-chart compatibility input only needs to address `x ≠ y`.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasOffDiagonalSurfaceTransitionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g)
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas),
    ∀ x y : X, x ≠ y →
      HyperbolicLocalChart.HasRealMobiusTransition
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)

/--
Overlapping off-diagonal surface transition target.

For disjoint surface domains, the real-Mobius transition condition is
vacuous.  Thus the geometric transition input only needs to be supplied for
distinct centers whose selected surface domains actually overlap.
-/
def SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g)
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas),
    ∀ x y : X, x ≠ y →
      Set.Nonempty
        ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) →
      HyperbolicLocalChart.HasRealMobiusTransition
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)

/--
Standard uniqueness target for hyperbolic local coordinates.

Two holomorphic local isometries from the same hyperbolic surface to `ℍ`
should differ by a single real Mobius transformation on each preconnected
nonempty overlap.  This is the geometric theorem behind the remaining
cross-chart surface transition boundary.
-/
def HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (U V : HyperbolicLocalChart X g),
    Set.Nonempty (U.domain ∩ V.domain) →
      IsPreconnected (U.domain ∩ V.domain) →
        U.HasRealMobiusTransition V

end HyperbolicMetric

end

end JJMath
