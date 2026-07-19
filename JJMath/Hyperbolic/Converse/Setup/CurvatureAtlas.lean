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

/-- Ball-shaped canonical shrink data forgets to ordinary shrink data. -/
def toBranchShrinkData
    (D : CanonicalChartedCurvatureBranchBallShrinkData g realBranchAtlasAt) :
    CanonicalChartedCurvatureBranchShrinkData g realBranchAtlasAt where
  shrinkDataAt := fun x ↦ (D.ballShrinkDataAt x).toShrinkData
  overlap_preconnected := by
    simpa [CanonicalChartedCurvatureBranchBallShrinkData]
      using D.overlap_preconnected

end CanonicalChartedCurvatureBranchBallShrinkData

/--
Topological shrink-data theorem for the canonical chart-at curvature atlas.

For every already chosen analytic real-branch family, choose smaller branch
domains whose induced surface overlaps are preconnected whenever nonempty.
-/
def CanonicalChartedCurvatureBranchShrinkDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (((localCurvatureMetricFormulaAtlasInChartAt g)
            |>.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).conformalFactor),
    Nonempty
      (CanonicalChartedCurvatureBranchShrinkData g realBranchAtlasAt)

/--
Ball-shaped topological shrink-data theorem for the canonical chart-at
curvature atlas.

This is stronger than `CanonicalChartedCurvatureBranchShrinkDataTheorem`, but
its coordinate-overlap part is automatic from convexity of balls; only the
surface-overlap choice remains substantive.
-/
def CanonicalChartedCurvatureBranchBallShrinkDataTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (((localCurvatureMetricFormulaAtlasInChartAt g)
            |>.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).conformalFactor),
    Nonempty
      (CanonicalChartedCurvatureBranchBallShrinkData g realBranchAtlasAt)

/--
%%handwave
name: Pointwise ball shrinking of canonical curvature branches
statement:
  Let a real-transition upper-half-plane branch atlas be chosen in the canonical curvature coordinate at every point $x$ of a surface. Then one can choose, for every $x$, positive-radius balls centered at each coordinate point and contained in the corresponding branch domains.
proof:
  Each branch atlas admits canonical ball-shrink data because its branch domains are open neighborhoods of their centers; choose this data independently for every $x$.
-/
theorem canonicalChartedCurvatureBranchBallShrinkDataAt_nonempty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X)
    (realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (((localCurvatureMetricFormulaAtlasInChartAt g)
            |>.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).conformalFactor) :
    Nonempty
      (∀ x : X, (realBranchAtlasAt x).toBranchAtlas.BallShrinkData) :=
  ⟨fun x ↦ (realBranchAtlasAt x).toBranchAtlas.ballShrinkData⟩

/--
Surface good-cover selection theorem for branch-contained coordinate balls.

The analytic/local part of ball shrinking is already proved by
`LocalUpperHalfPlaneBranchAtlas.ballShrinkData`; this theorem target asks only
for a choice of such branch-contained balls whose induced selected surface
overlaps are preconnected whenever nonempty.
-/
def CanonicalChartedCurvatureBranchBallSurfaceOverlapSelectionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (((localCurvatureMetricFormulaAtlasInChartAt g)
            |>.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).conformalFactor),
    ∃ ballShrinkDataAt :
      ∀ x : X, (realBranchAtlasAt x).toBranchAtlas.BallShrinkData,
      let metricFormulaAtlas :=
        ((localCurvatureMetricFormulaAtlasInChartAt g)
          |>.toLocalLiouvilleMetricFormulaAtlas)
      let shrunkRealBranchAtlasAt :
          ∀ x : X,
            LocalRealUpperHalfPlaneBranchAtlas
              (metricFormulaAtlas.formulaAt x).conformalFactor :=
        fun x ↦ (realBranchAtlasAt x).shrink ((ballShrinkDataAt x).toShrinkData)
      SurfaceRealUpperHalfPlaneBranchAtlasSelectedPreDataOverlapPreconnected
        metricFormulaAtlas
        shrunkRealBranchAtlasAt
        ((surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_coordinateChartedOnDomain
          (canonicalChartedCurvatureCoordinateChartedOnDomain g))
            shrunkRealBranchAtlasAt)

/-- The base coordinate used by the canonical chart-at curvature atlas at `x`. -/
def canonicalChartedCurvatureBaseCoordinate
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) (x : X) :
    (((localCurvatureMetricFormulaAtlasInChartAt g)
      |>.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).conformalFactor.coordinateDomain :=
  ⟨(((localCurvatureMetricFormulaAtlasInChartAt g)
      |>.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).coordinate x,
    (((localCurvatureMetricFormulaAtlasInChartAt g)
      |>.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).coordinate_mem_conformalFactor_domain
        x
        (((localCurvatureMetricFormulaAtlasInChartAt g)
          |>.toLocalLiouvilleMetricFormulaAtlas).mem_formulaAt_domain x)⟩

/--
The explicit surface overlap cut out by base coordinate balls in the canonical
chart-at curvature atlas.
-/
def CanonicalChartedCurvatureBaseBallSurfaceOverlapSet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) (baseRadiusAt : X → ℝ) (x y : X) :
    Set X :=
  let metricFormulaAtlas :=
    ((localCurvatureMetricFormulaAtlasInChartAt g)
      |>.toLocalLiouvilleMetricFormulaAtlas)
  {z : X |
    z ∈ (metricFormulaAtlas.formulaAt x).domain ∧
    (metricFormulaAtlas.formulaAt x).coordinate z ∈
      Metric.ball
        ((canonicalChartedCurvatureBaseCoordinate g x : _) : ℂ)
        (baseRadiusAt x) ∧
    z ∈ (metricFormulaAtlas.formulaAt y).domain ∧
    (metricFormulaAtlas.formulaAt y).coordinate z ∈
      Metric.ball
        ((canonicalChartedCurvatureBaseCoordinate g y : _) : ℂ)
        (baseRadiusAt y)}

/--
Base-branch surface good-cover theorem for branch-contained coordinate balls.

This is the sharpest charted-overlap target in the current route: for the
selected base branch at each surface point, choose one branch-contained
coordinate ball so that the induced nonempty off-diagonal surface overlaps are
preconnected.  The values of the shrink on non-base branches are irrelevant to
the selected surface predata and are filled in automatically later.
-/
def CanonicalChartedCurvatureBranchBaseBallSurfaceOverlapSelectionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X)
    (realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (((localCurvatureMetricFormulaAtlasInChartAt g)
            |>.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).conformalFactor),
    ∃ baseRadiusAt : X → ℝ,
      (∀ x : X, 0 < baseRadiusAt x) ∧
      (∀ x : X,
        Metric.ball
          ((canonicalChartedCurvatureBaseCoordinate g x : _) : ℂ)
          (baseRadiusAt x) ⊆
            ((realBranchAtlasAt x).branchNear
              (canonicalChartedCurvatureBaseCoordinate g x)).domain) ∧
      ∀ x y : X, x ≠ y →
        Set.Nonempty
          (CanonicalChartedCurvatureBaseBallSurfaceOverlapSet g baseRadiusAt x y) →
        IsPreconnected
          (CanonicalChartedCurvatureBaseBallSurfaceOverlapSet g baseRadiusAt x y)

/--
Pure bounded base-ball surface-good-cover theorem for the canonical chart-at
curvature atlas.

Given any positive coordinate-radius bound at each point, choose smaller
positive radii whose explicit nonempty surface overlaps are preconnected.  This
is independent of the analytic branch atlases; those only provide the bounds.
-/
def CanonicalChartedCurvatureBoundedBaseBallSurfaceOverlapSelectionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X) (radiusBoundAt : X → ℝ),
    (∀ x : X, 0 < radiusBoundAt x) →
      ∃ baseRadiusAt : X → ℝ,
        (∀ x : X, 0 < baseRadiusAt x) ∧
        (∀ x : X, baseRadiusAt x ≤ radiusBoundAt x) ∧
        ∀ x y : X, x ≠ y →
          Set.Nonempty
            (CanonicalChartedCurvatureBaseBallSurfaceOverlapSet g baseRadiusAt x y) →
          IsPreconnected
            (CanonicalChartedCurvatureBaseBallSurfaceOverlapSet g baseRadiusAt x y)

/--
The explicit overlap of two ambient chart balls, independent of any metric or
analytic branch data.
-/
def ChartedSpaceBaseBallSurfaceOverlapSet
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (baseRadiusAt : X → ℝ) (x y : X) : Set X :=
  {z : X |
    z ∈ (chartAt ℂ x).source ∧
    (chartAt ℂ x) z ∈ Metric.ball ((chartAt ℂ x) x) (baseRadiusAt x) ∧
    z ∈ (chartAt ℂ y).source ∧
    (chartAt ℂ y) z ∈ Metric.ball ((chartAt ℂ y) y) (baseRadiusAt y)}

/--
Pure charted-space bounded ball-overlap selection theorem.

This is the metric-free and branch-free topological good-cover boundary: below
any positive radius bound, choose ambient chart balls whose nonempty pairwise
overlaps are preconnected.
-/
def ChartedSpaceBoundedBaseBallSurfaceOverlapSelectionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ radiusBoundAt : X → ℝ,
    (∀ x : X, 0 < radiusBoundAt x) →
      ∃ baseRadiusAt : X → ℝ,
        (∀ x : X, 0 < baseRadiusAt x) ∧
        (∀ x : X, baseRadiusAt x ≤ radiusBoundAt x) ∧
        ∀ x y : X, x ≠ y →
          Set.Nonempty
            (ChartedSpaceBaseBallSurfaceOverlapSet X baseRadiusAt x y) →
          IsPreconnected
            (ChartedSpaceBaseBallSurfaceOverlapSet X baseRadiusAt x y)

/--
%%handwave
name: Canonical curvature ball overlaps are charted-space ball overlaps
statement:
  For any surface points $x,y$ and radius function $r$, the overlap of the canonical curvature-coordinate balls centered at $x$ and $y$ is exactly
  $$\{z:z\in\operatorname{source}(\phi_x),\ |\phi_x(z)-\phi_x(x)|<r(x),\ z\in\operatorname{source}(\phi_y),\ |\phi_y(z)-\phi_y(y)|<r(y)\}.$$
proof:
  Expand the canonical curvature formulas: their coordinate maps and domains are precisely the ambient chart maps and chart sources. The two set descriptions then agree pointwise.
-/
@[simp]
theorem canonicalChartedCurvatureBaseBallSurfaceOverlapSet_eq_chartedSpace
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : HyperbolicMetric X) (baseRadiusAt : X → ℝ) (x y : X) :
    CanonicalChartedCurvatureBaseBallSurfaceOverlapSet g baseRadiusAt x y =
      ChartedSpaceBaseBallSurfaceOverlapSet X baseRadiusAt x y := by
  ext z
  simp only [CanonicalChartedCurvatureBaseBallSurfaceOverlapSet,
    ChartedSpaceBaseBallSurfaceOverlapSet,
    canonicalChartedCurvatureBaseCoordinate,
    localCurvatureMetricFormulaAtlasInChartAt,
    localCurvatureMetricFormulaInChartAt,
    LocalCurvatureMetricFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas,
    LocalCurvatureMetricFormula.toLocalLiouvilleMetricFormula,
    Set.mem_setOf_eq, Metric.mem_ball]

/--
The pure charted-space ball-overlap selector implies the canonical bounded
base-ball selector for every hyperbolic metric.
-/
def canonicalChartedCurvatureBoundedBaseBallSurfaceOverlapSelectionTheorem_of_chartedSpaceBoundedBaseBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hCharted :
      ChartedSpaceBoundedBaseBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvatureBoundedBaseBallSurfaceOverlapSelectionTheorem X := by
  intro g radiusBoundAt radiusBound_pos
  rcases hCharted radiusBoundAt radiusBound_pos with
    ⟨baseRadiusAt, baseRadius_pos, baseRadius_le_bound, hOverlap⟩
  refine ⟨baseRadiusAt, baseRadius_pos, baseRadius_le_bound, ?_⟩
  intro x y hxy hne
  rw [canonicalChartedCurvatureBaseBallSurfaceOverlapSet_eq_chartedSpace] at hne ⊢
  exact hOverlap x y hxy hne

/--
Branch-domain openness turns the bounded pure surface-good-cover theorem into
the branch-contained base-ball theorem.
-/
noncomputable def canonicalChartedCurvatureBranchBaseBallSurfaceOverlapSelectionTheorem_of_boundedBaseBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hBounded :
      CanonicalChartedCurvatureBoundedBaseBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvatureBranchBaseBallSurfaceOverlapSelectionTheorem X := by
  intro g realBranchAtlasAt
  let radiusBoundAt : X → ℝ := fun x ↦
    Classical.choose
      ((realBranchAtlasAt x).toBranchAtlas.exists_ball_subset_branchNear_domain
        (canonicalChartedCurvatureBaseCoordinate g x))
  have radiusBound_pos : ∀ x : X, 0 < radiusBoundAt x := by
    intro x
    exact
      (Classical.choose_spec
        ((realBranchAtlasAt x).toBranchAtlas.exists_ball_subset_branchNear_domain
          (canonicalChartedCurvatureBaseCoordinate g x))).1
  have radiusBound_subset :
      ∀ x : X,
        Metric.ball
          ((canonicalChartedCurvatureBaseCoordinate g x : _) : ℂ)
          (radiusBoundAt x) ⊆
            ((realBranchAtlasAt x).branchNear
              (canonicalChartedCurvatureBaseCoordinate g x)).domain := by
    intro x
    exact
      (Classical.choose_spec
        ((realBranchAtlasAt x).toBranchAtlas.exists_ball_subset_branchNear_domain
          (canonicalChartedCurvatureBaseCoordinate g x))).2
  rcases hBounded g radiusBoundAt radiusBound_pos with
    ⟨baseRadiusAt, baseRadius_pos, baseRadius_le_bound, hOverlap⟩
  refine ⟨baseRadiusAt, baseRadius_pos, ?_, hOverlap⟩
  intro x z hz
  apply radiusBound_subset x
  have hz_dist :
      dist z (((canonicalChartedCurvatureBaseCoordinate g x : _) : ℂ)) <
        baseRadiusAt x := by
    simpa [Metric.mem_ball] using hz
  have hz_bound :
      dist z (((canonicalChartedCurvatureBaseCoordinate g x : _) : ℂ)) <
        radiusBoundAt x :=
    lt_of_lt_of_le hz_dist (baseRadius_le_bound x)
  simpa [Metric.mem_ball] using hz_bound

/--
Extend base-branch ball radii to full coordinate ball-shrink data by using the
canonical local openness shrink away from the base branch.
-/
noncomputable def canonicalChartedCurvatureBallShrinkDataAt_of_baseRadii
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (((localCurvatureMetricFormulaAtlasInChartAt g)
            |>.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).conformalFactor}
    (baseRadiusAt : X → ℝ)
    (baseRadius_pos : ∀ x : X, 0 < baseRadiusAt x)
    (baseBall_subset :
      ∀ x : X,
        Metric.ball
          ((canonicalChartedCurvatureBaseCoordinate g x : _) : ℂ)
          (baseRadiusAt x) ⊆
            ((realBranchAtlasAt x).branchNear
              (canonicalChartedCurvatureBaseCoordinate g x)).domain)
    (x : X) :
    (realBranchAtlasAt x).toBranchAtlas.BallShrinkData :=
  let base := canonicalChartedCurvatureBaseCoordinate g x
  let fallback := (realBranchAtlasAt x).toBranchAtlas.ballShrinkData
  { radiusAt := fun z ↦ if z = base then baseRadiusAt x else fallback.radiusAt z
    radius_pos := by
      intro z
      by_cases hz : z = base
      · subst hz
        simp [baseRadius_pos x]
      · simp [hz, fallback.radius_pos z]
    ball_subset := by
      intro z
      by_cases hz : z = base
      · subst hz
        simpa using baseBall_subset x
      · simpa [hz] using fallback.ball_subset z }

/--
The surface-good-cover formulation is equivalent to the bundled ball-shrink
data theorem in the direction used by the converse assembly.
-/
def canonicalChartedCurvatureBranchBallShrinkDataTheorem_of_branchBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSurface :
      CanonicalChartedCurvatureBranchBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvatureBranchBallShrinkDataTheorem X := by
  intro g realBranchAtlasAt
  rcases hSurface g realBranchAtlasAt with ⟨ballShrinkDataAt, hOverlap⟩
  exact
    ⟨{ ballShrinkDataAt := ballShrinkDataAt
       overlap_preconnected := hOverlap }⟩

/-- Bundled ball-shrink data gives the surface-good-cover formulation. -/
def canonicalChartedCurvatureBranchBallSurfaceOverlapSelectionTheorem_of_branchBallShrinkData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hBall :
      CanonicalChartedCurvatureBranchBallShrinkDataTheorem X) :
    CanonicalChartedCurvatureBranchBallSurfaceOverlapSelectionTheorem X := by
  intro g realBranchAtlasAt
  rcases hBall g realBranchAtlasAt with ⟨D⟩
  exact ⟨D.ballShrinkDataAt, D.overlap_preconnected⟩

/--
The base-branch surface-good-cover theorem gives the full ball-shrink surface
selection theorem.
-/
noncomputable def canonicalChartedCurvatureBranchBallSurfaceOverlapSelectionTheorem_of_branchBaseBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hBase :
      CanonicalChartedCurvatureBranchBaseBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvatureBranchBallSurfaceOverlapSelectionTheorem X := by
  intro g realBranchAtlasAt
  rcases hBase g realBranchAtlasAt with
    ⟨baseRadiusAt, baseRadius_pos, baseBall_subset, hOverlap⟩
  let metricFormulaAtlas :=
    ((localCurvatureMetricFormulaAtlasInChartAt g)
      |>.toLocalLiouvilleMetricFormulaAtlas)
  let ballShrinkDataAt :
      ∀ x : X, (realBranchAtlasAt x).toBranchAtlas.BallShrinkData :=
    fun x ↦
      canonicalChartedCurvatureBallShrinkDataAt_of_baseRadii
        (g := g) (realBranchAtlasAt := realBranchAtlasAt)
        baseRadiusAt baseRadius_pos baseBall_subset x
  refine ⟨ballShrinkDataAt, ?_⟩
  let shrunkRealBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (metricFormulaAtlas.formulaAt x).conformalFactor :=
    fun x ↦ (realBranchAtlasAt x).shrink ((ballShrinkDataAt x).toShrinkData)
  let restricted_domain_open :=
    (surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_coordinateChartedOnDomain
      (canonicalChartedCurvatureCoordinateChartedOnDomain g))
        shrunkRealBranchAtlasAt
  let preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas :=
    { realBranchAtlasAt := shrunkRealBranchAtlasAt
      restricted_domain_open := restricted_domain_open }
  change SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapPreconnected preData
  intro x y hxy hne
  have hDomain :
      ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
          (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) =
        CanonicalChartedCurvatureBaseBallSurfaceOverlapSet g baseRadiusAt x y := by
    rw [surfaceRealUpperHalfPlaneBranchAtlasPreData_solutionAt_toHyperbolicLocalChart_domain_inter
      preData x y]
    ext z
    simp [preData, shrunkRealBranchAtlasAt, ballShrinkDataAt,
      canonicalChartedCurvatureBallShrinkDataAt_of_baseRadii,
      CanonicalChartedCurvatureBaseBallSurfaceOverlapSet,
      canonicalChartedCurvatureBaseCoordinate, metricFormulaAtlas]
  rw [hDomain] at hne ⊢
  exact hOverlap x y hxy hne

/--
Ball-shaped canonical shrink data implies the ordinary canonical shrink-data
theorem.
-/
def canonicalChartedCurvatureBranchShrinkDataTheorem_of_branchBallShrinkData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hBall :
      CanonicalChartedCurvatureBranchBallShrinkDataTheorem X) :
    CanonicalChartedCurvatureBranchShrinkDataTheorem X := by
  intro g realBranchAtlasAt
  rcases hBall g realBranchAtlasAt with ⟨D⟩
  exact ⟨D.toBranchShrinkData⟩

/--
Global theorem target for the explicit-shrink version of the canonical
branch/topology selection.
-/
def CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ (g : HyperbolicMetric X),
    Nonempty (CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelection g)

namespace CanonicalChartedCurvaturePreconnectedOverlapBranchSelection

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}

/-- A selected canonical branch family gives the canonical overlap selector. -/
def toPreconnectedOverlapSelection
    (S : CanonicalChartedCurvaturePreconnectedOverlapBranchSelection g) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
      ((localCurvatureMetricFormulaAtlasInChartAt g)
        |>.toLocalLiouvilleMetricFormulaAtlas) where
  realBranchAtlasAt := S.realBranchAtlasAt
  restricted_domain_open :=
    (surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_coordinateChartedOnDomain
      (canonicalChartedCurvatureCoordinateChartedOnDomain g)) S.realBranchAtlasAt
  overlap_preconnected := S.overlap_preconnected

end CanonicalChartedCurvaturePreconnectedOverlapBranchSelection

namespace CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelection

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}

/-- Build the bundled explicit-shrink selection from a branch family and its shrink data. -/
def ofBranchShrinkData
    (realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (((localCurvatureMetricFormulaAtlasInChartAt g)
            |>.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).conformalFactor)
    (D : CanonicalChartedCurvatureBranchShrinkData g realBranchAtlasAt) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelection g where
  realBranchAtlasAt := realBranchAtlasAt
  shrinkDataAt := D.shrinkDataAt
  overlap_preconnected := D.overlap_preconnected

/-- The shrunk branch family as an ordinary canonical branch/topology selection. -/
def toBranchSelection
    (S : CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelection g) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchSelection g where
  realBranchAtlasAt := fun x ↦ (S.realBranchAtlasAt x).shrink (S.shrinkDataAt x)
  overlap_preconnected := by
    simpa [CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelection]
      using S.overlap_preconnected

end CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelection

/--
A selected canonical branch/topology theorem gives the canonical overlap
selector theorem needed by the selected one-jet route.
-/
def canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_branchSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X := by
  intro g
  rcases hSelection g with ⟨S⟩
  exact ⟨S.toPreconnectedOverlapSelection⟩

/--
The explicit-shrink branch/topology target implies the ordinary selected
canonical branch/topology target.
-/
def canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_branchShrinkSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem X := by
  intro g
  rcases hSelection g with ⟨S⟩
  exact ⟨S.toBranchSelection⟩

/--
The explicit-shrink branch/topology target also gives the canonical selected
overlap selector theorem.
-/
def canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_branchShrinkSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X :=
  canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_branchSelection
    (canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_branchShrinkSelection
      hSelection)

/--
Local real-branch existence plus pure branch-shrink data gives the explicit
canonical branch/topology shrink-selection theorem.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchShrinkData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hShrink :
      CanonicalChartedCurvatureBranchShrinkDataTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem
      X := by
  intro g
  let metricFormulaAtlas :=
    ((localCurvatureMetricFormulaAtlasInChartAt g)
      |>.toLocalLiouvilleMetricFormulaAtlas)
  let realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (metricFormulaAtlas.formulaAt x).conformalFactor :=
    fun x ↦
      Classical.choice
        (hLocal (metricFormulaAtlas.formulaAt x).conformalFactor
          (metricFormulaAtlas.formulaAt x).solves_liouville)
  rcases hShrink g realBranchAtlasAt with ⟨D⟩
  exact
    ⟨CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelection.ofBranchShrinkData
      realBranchAtlasAt D⟩

/--
Local real-branch existence plus pure branch-shrink data gives the ordinary
canonical branch/topology selection theorem.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_localRealBranches_and_branchShrinkData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hShrink :
      CanonicalChartedCurvatureBranchShrinkDataTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_branchShrinkSelection
    (canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchShrinkData
      hLocal hShrink)

/--
Local real-branch existence plus pure branch-shrink data gives the canonical
selected-overlap theorem used by the selected one-jet route.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_localRealBranches_and_branchShrinkData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hShrink :
      CanonicalChartedCurvatureBranchShrinkDataTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_branchShrinkSelection
    (canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchShrinkData
      hLocal hShrink)

/--
Local real-branch existence plus ball-shaped branch-shrink data gives the
explicit canonical branch/topology shrink-selection theorem.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchBallShrinkData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hBall :
      CanonicalChartedCurvatureBranchBallShrinkDataTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchShrinkData
    hLocal
    (canonicalChartedCurvatureBranchShrinkDataTheorem_of_branchBallShrinkData
      hBall)

/--
Local real-branch existence plus ball-shaped branch-shrink data gives the
ordinary canonical branch/topology selection theorem.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_localRealBranches_and_branchBallShrinkData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hBall :
      CanonicalChartedCurvatureBranchBallShrinkDataTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_branchShrinkSelection
    (canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchBallShrinkData
      hLocal hBall)

/--
Local real-branch existence plus ball-shaped branch-shrink data gives the
canonical selected-overlap theorem used by the selected one-jet route.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_localRealBranches_and_branchBallShrinkData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hBall :
      CanonicalChartedCurvatureBranchBallShrinkDataTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_branchShrinkSelection
    (canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchBallShrinkData
      hLocal hBall)

/--
Local real-branch existence plus the surface-good-cover ball selection theorem
gives the explicit canonical branch/topology shrink-selection theorem.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hSurface :
      CanonicalChartedCurvatureBranchBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchBallShrinkData
    hLocal
    (canonicalChartedCurvatureBranchBallShrinkDataTheorem_of_branchBallSurfaceOverlapSelection
      hSurface)

/--
Local real-branch existence plus the surface-good-cover ball selection theorem
gives the ordinary canonical branch/topology selection theorem.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_localRealBranches_and_branchBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hSurface :
      CanonicalChartedCurvatureBranchBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_branchShrinkSelection
    (canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchBallSurfaceOverlapSelection
      hLocal hSurface)

/--
Local real-branch existence plus the surface-good-cover ball selection theorem
gives the canonical selected-overlap theorem used by the selected one-jet route.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_localRealBranches_and_branchBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hSurface :
      CanonicalChartedCurvatureBranchBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_branchShrinkSelection
    (canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchBallSurfaceOverlapSelection
      hLocal hSurface)

/--
Local real-branch existence plus base-branch surface-good-cover ball selection
gives the explicit canonical branch/topology shrink-selection theorem.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchBaseBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hBase :
      CanonicalChartedCurvatureBranchBaseBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchBallSurfaceOverlapSelection
    hLocal
    (canonicalChartedCurvatureBranchBallSurfaceOverlapSelectionTheorem_of_branchBaseBallSurfaceOverlapSelection
      hBase)

/--
Local real-branch existence plus base-branch surface-good-cover ball selection
gives the ordinary canonical branch/topology selection theorem.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_localRealBranches_and_branchBaseBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hBase :
      CanonicalChartedCurvatureBranchBaseBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_branchShrinkSelection
    (canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchBaseBallSurfaceOverlapSelection
      hLocal hBase)

/--
Local real-branch existence plus base-branch surface-good-cover ball selection
gives the canonical selected-overlap theorem used by the selected one-jet route.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_localRealBranches_and_branchBaseBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hBase :
      CanonicalChartedCurvatureBranchBaseBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_branchShrinkSelection
    (canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchBaseBallSurfaceOverlapSelection
      hLocal hBase)

/--
Local real-branch existence plus the bounded pure surface-good-cover theorem
gives the explicit canonical branch/topology shrink-selection theorem.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_boundedBaseBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hBounded :
      CanonicalChartedCurvatureBoundedBaseBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_branchBaseBallSurfaceOverlapSelection
    hLocal
    (canonicalChartedCurvatureBranchBaseBallSurfaceOverlapSelectionTheorem_of_boundedBaseBallSurfaceOverlapSelection
      hBounded)

/--
Local real-branch existence plus the bounded pure surface-good-cover theorem
gives the ordinary canonical branch/topology selection theorem.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_localRealBranches_and_boundedBaseBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hBounded :
      CanonicalChartedCurvatureBoundedBaseBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_branchShrinkSelection
    (canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_boundedBaseBallSurfaceOverlapSelection
      hLocal hBounded)

/--
Local real-branch existence plus the bounded pure surface-good-cover theorem
gives the canonical selected-overlap theorem used by the selected one-jet route.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_localRealBranches_and_boundedBaseBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hBounded :
      CanonicalChartedCurvatureBoundedBaseBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_branchShrinkSelection
    (canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_boundedBaseBallSurfaceOverlapSelection
      hLocal hBounded)

/--
Local real-branch existence plus the pure charted-space good-cover theorem
gives the explicit canonical branch/topology shrink-selection theorem.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_chartedSpaceBoundedBaseBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hCharted :
      ChartedSpaceBoundedBaseBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_boundedBaseBallSurfaceOverlapSelection
    hLocal
    (canonicalChartedCurvatureBoundedBaseBallSurfaceOverlapSelectionTheorem_of_chartedSpaceBoundedBaseBallSurfaceOverlapSelection
      hCharted)

/--
Local real-branch existence plus the pure charted-space good-cover theorem
gives the ordinary canonical branch/topology selection theorem.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_localRealBranches_and_chartedSpaceBoundedBaseBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hCharted :
      ChartedSpaceBoundedBaseBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_branchShrinkSelection
    (canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_chartedSpaceBoundedBaseBallSurfaceOverlapSelection
      hLocal hCharted)

/--
Local real-branch existence plus the pure charted-space good-cover theorem
gives the canonical selected-overlap theorem used by the selected one-jet route.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_localRealBranches_and_chartedSpaceBoundedBaseBallSurfaceOverlapSelection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hCharted :
      ChartedSpaceBoundedBaseBallSurfaceOverlapSelectionTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem
      X :=
  canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_branchShrinkSelection
    (canonicalChartedCurvaturePreconnectedOverlapBranchShrinkSelectionTheorem_of_localRealBranches_and_chartedSpaceBoundedBaseBallSurfaceOverlapSelection
      hLocal hCharted)

/--
Curvature-formula chart-compatibility supplies surface-domain openness for the
Liouville formula atlas obtained by rewriting curvature as Liouville.
-/
def surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_localCurvatureMetricFormulaAtlasCoordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g}
    (hChart :
      LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomain curvatureFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor
      curvatureFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas :=
  surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_coordinateChartedOnDomain
    (by
      intro x
      exact hChart x)

/--
For one chosen Liouville metric formula atlas, local real branches, charted
formula coordinates, and preconnectedness of selected overlaps build the
ordinary overlap selector.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection_of_localRealBranches_coordinateChartedOnDomain_overlapPreconnected_for
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (hLocal :
      ∀ x : X,
        Nonempty
          (LocalRealUpperHalfPlaneBranchAtlas
            (metricFormulaAtlas.formulaAt x).conformalFactor))
    (hChart :
      LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain
        metricFormulaAtlas)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedFor
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection
      metricFormulaAtlas :=
  surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection_of_localRealBranches_openness_overlapPreconnected_for
    hLocal
    (surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_coordinateChartedOnDomain
      hChart)
    hOverlapPreconnected

/--
Local real branches plus the strong canonical surface-overlap
preconnectedness theorem produce a selected canonical branch/topology package.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_localRealBranches_and_surfaceOverlapPreconnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOverlap :
      CanonicalChartedCurvatureSurfaceOverlapPreconnectedTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem X := by
  intro g
  let metricFormulaAtlas :=
    ((localCurvatureMetricFormulaAtlasInChartAt g)
      |>.toLocalLiouvilleMetricFormulaAtlas)
  let hChart :
      LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain
        metricFormulaAtlas :=
    canonicalChartedCurvatureCoordinateChartedOnDomain g
  let hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor
        metricFormulaAtlas :=
    surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_coordinateChartedOnDomain
      hChart
  let realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (metricFormulaAtlas.formulaAt x).conformalFactor :=
    fun x ↦
      Classical.choice
        (hLocal (metricFormulaAtlas.formulaAt x).conformalFactor
          (metricFormulaAtlas.formulaAt x).solves_liouville)
  exact
    ⟨{ realBranchAtlasAt := realBranchAtlasAt
       overlap_preconnected := by
        simpa [CanonicalChartedCurvaturePreconnectedOverlapBranchSelection,
          SurfaceRealUpperHalfPlaneBranchAtlasSelectedPreDataOverlapPreconnected,
          metricFormulaAtlas, hOpen, hChart, realBranchAtlasAt] using
          hOverlap g
            { realBranchAtlasAt := realBranchAtlasAt
              restricted_domain_open := hOpen realBranchAtlasAt } }⟩

/--
Local real branches plus canonical surface-overlap preconnectedness construct
the canonical chart-at curvature overlap selector.
-/
noncomputable def canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_localRealBranches_and_surfaceOverlapPreconnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOverlap :
      CanonicalChartedCurvatureSurfaceOverlapPreconnectedTheorem X) :
    CanonicalChartedCurvaturePreconnectedOverlapSelectionTheorem X :=
  canonicalChartedCurvaturePreconnectedOverlapSelectionTheorem_of_branchSelection
    (canonicalChartedCurvaturePreconnectedOverlapBranchSelectionTheorem_of_localRealBranches_and_surfaceOverlapPreconnected
      hLocal hOverlap)

/--
Coordinate-preimage openness for a curvature formula atlas follows from
ambient chart agreement on its formula domains.
-/
def localCurvatureMetricFormulaAtlasCoordinatePreimageOpenness_of_coordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g}
    (hChart :
      LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomain
        curvatureFormulaAtlas) :
    LocalCurvatureMetricFormulaAtlasCoordinatePreimageOpenness
      curvatureFormulaAtlas := by
  intro x V hV
  rcases hChart x with ⟨hSub, hEq⟩
  exact
    isOpen_formulaCoordinate_preimage_of_eqOn_chartAt
      (curvatureFormulaAtlas.formulaAt x).isOpen_domain hSub hEq hV

/--
The global curvature chart-compatibility theorem implies the curvature-only
coordinate-preimage openness theorem.
-/
def localCurvatureMetricFormulaAtlasCoordinatePreimageOpennessTheorem_of_coordinateChartedOnDomainTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hChart :
      LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomainTheorem X) :
    LocalCurvatureMetricFormulaAtlasCoordinatePreimageOpennessTheorem X := by
  intro g curvatureFormulaAtlas
  exact
    localCurvatureMetricFormulaAtlasCoordinatePreimageOpenness_of_coordinateChartedOnDomain
      (hChart g curvatureFormulaAtlas)

/--
Curvature-atlas coordinate-preimage openness gives restricted branch-domain
openness after rewriting the atlas as a Liouville atlas.
-/
def surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_localCurvatureMetricFormulaAtlasCoordinatePreimageOpenness
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g}
    (hPreimage :
      LocalCurvatureMetricFormulaAtlasCoordinatePreimageOpenness
        curvatureFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor
      curvatureFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas := by
  intro realBranchAtlasAt x
  let p :
      ((curvatureFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).conformalFactor.coordinateDomain :=
    ⟨((curvatureFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).coordinate x,
      ((curvatureFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas).formulaAt x).coordinate_mem_conformalFactor_domain x
        ((curvatureFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas).mem_formulaAt_domain x)⟩
  let H := (realBranchAtlasAt x).branchNear p
  have hOpenH : IsOpen H.domain := by
    simpa [LocalUpperHalfPlaneDevelopingMap.domain] using H.projective.isOpen_domain
  simpa only [LocalCurvatureMetricFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas,
    LocalCurvatureMetricFormula.toLocalLiouvilleMetricFormula] using
    hPreimage x H.domain hOpenH

/--
Curvature-atlas coordinate-preimage openness supplies restricted branch-domain
openness for every curvature-derived Liouville atlas.
-/
def localCurvatureMetricFormulaAtlasRestrictedDomainOpennessTheorem_of_coordinatePreimageOpenness
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPreimage :
      LocalCurvatureMetricFormulaAtlasCoordinatePreimageOpennessTheorem X) :
    LocalCurvatureMetricFormulaAtlasRestrictedDomainOpennessTheorem X := by
  intro g curvatureFormulaAtlas
  exact
    surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessFor_of_localCurvatureMetricFormulaAtlasCoordinatePreimageOpenness
      (hPreimage g curvatureFormulaAtlas)

/--
Curvature formula chart-compatibility supplies restricted branch-domain
openness for every curvature-derived Liouville atlas.
-/
def localCurvatureMetricFormulaAtlasRestrictedDomainOpennessTheorem_of_coordinateChartedOnDomainTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hChart :
      LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomainTheorem X) :
    LocalCurvatureMetricFormulaAtlasRestrictedDomainOpennessTheorem X :=
  localCurvatureMetricFormulaAtlasRestrictedDomainOpennessTheorem_of_coordinatePreimageOpenness
    (localCurvatureMetricFormulaAtlasCoordinatePreimageOpennessTheorem_of_coordinateChartedOnDomainTheorem
      hChart)

/--
Continuous coordinate maps imply coordinate-preimage openness for Liouville
metric formula atlases.
-/
def localLiouvilleMetricFormulaAtlasCoordinatePreimageOpennessTheorem_of_coordinateContinuity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hCont : LocalLiouvilleMetricFormulaAtlasCoordinateContinuityTheorem X) :
    LocalLiouvilleMetricFormulaAtlasCoordinatePreimageOpennessTheorem X := by
  intro g metricFormulaAtlas x V hV
  simpa [Set.preimage, Set.inter_def] using
    (metricFormulaAtlas.formulaAt x).isOpen_domain.inter
      (hV.preimage (hCont g metricFormulaAtlas x))

/--
Continuity on each formula domain implies coordinate-preimage openness.

This is exactly the mathlib `ContinuousOn` open-preimage theorem for an open
domain.
-/
def localLiouvilleMetricFormulaAtlasCoordinatePreimageOpennessTheorem_of_coordinateContinuousOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hCont : LocalLiouvilleMetricFormulaAtlasCoordinateContinuousOnDomainTheorem X) :
    LocalLiouvilleMetricFormulaAtlasCoordinatePreimageOpennessTheorem X := by
  intro g metricFormulaAtlas x V hV
  simpa [Set.preimage, Set.inter_def] using
    (hCont g metricFormulaAtlas x).isOpen_inter_preimage
      (metricFormulaAtlas.formulaAt x).isOpen_domain hV

/--
Formula coordinates that agree with ambient charts on open formula domains
have open preimages of open coordinate subsets.
-/
def localLiouvilleMetricFormulaAtlasCoordinatePreimageOpennessTheorem_of_coordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hChart :
      LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomainTheorem X) :
    LocalLiouvilleMetricFormulaAtlasCoordinatePreimageOpennessTheorem X := by
  intro g metricFormulaAtlas
  exact
    localLiouvilleMetricFormulaAtlasCoordinatePreimageOpenness_of_coordinateChartedOnDomain
      (hChart g metricFormulaAtlas)

/--
Local real branches, coordinate-preimage openness, and overlap
preconnectedness build the ordinary preconnected-overlap selector theorem.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_localRealBranches_coordinatePreimageOpenness_overlapPreconnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hPreimage :
      LocalLiouvilleMetricFormulaAtlasCoordinatePreimageOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_localRealBranches_openness_overlapPreconnected
    hLocal
    (surfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem_of_coordinatePreimageOpenness
      hPreimage)
    hOverlapPreconnected

/--
Local real branches, charted formula coordinates, and overlap
preconnectedness build the ordinary preconnected-overlap selector theorem.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_localRealBranches_coordinateChartedOnDomain_overlapPreconnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hChart :
      LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomainTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X := by
  intro g metricFormulaAtlas
  exact
    ⟨surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelection_of_localRealBranches_coordinateChartedOnDomain_overlapPreconnected_for
      (fun x ↦
        hLocal (metricFormulaAtlas.formulaAt x).conformalFactor
          (metricFormulaAtlas.formulaAt x).solves_liouville)
      (hChart g metricFormulaAtlas)
      (hOverlapPreconnected g metricFormulaAtlas)⟩

/--
The charted-overlap selector follows from local real branches, charted formula
coordinates, overlap preconnectedness, and coordinate compatibility for the
chosen upper-half-plane pullback formulae.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem_of_localRealBranches_coordinateChartedOnDomain_overlapPreconnected_coordinateEqOnChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hMetricChart :
      LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomainTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hPullbackChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem_of_selection_and_coordinateEqOnChartAt
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_localRealBranches_coordinateChartedOnDomain_overlapPreconnected
      hLocal hMetricChart hOverlapPreconnected)
    hPullbackChart

/--
The locally charted overlap selector follows from local real branches, charted
formula coordinates, overlap preconnectedness, and local coordinate
compatibility for the chosen upper-half-plane pullback formulae.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionTheorem_of_localRealBranches_coordinateChartedOnDomain_overlapPreconnected_coordinateEventuallyEqOnChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hMetricChart :
      LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomainTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hPullbackChart :
      CoordinateUpperHalfPlanePullbackFormulaAmbientCoordinateEventuallyEqTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionTheorem
      X :=
  surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionTheorem_of_selection_and_coordinateEventuallyEqOnChartAt
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_localRealBranches_coordinateChartedOnDomain_overlapPreconnected
      hLocal hMetricChart hOverlapPreconnected)
    hPullbackChart

/--
Global coordinate continuity is a sufficient source of the sharper
domainwise-continuity target.
-/
def localLiouvilleMetricFormulaAtlasCoordinateContinuousOnDomainTheorem_of_coordinateContinuity
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hCont : LocalLiouvilleMetricFormulaAtlasCoordinateContinuityTheorem X) :
    LocalLiouvilleMetricFormulaAtlasCoordinateContinuousOnDomainTheorem X := by
  intro g metricFormulaAtlas x
  exact (hCont g metricFormulaAtlas x).continuousOn

/--
Formula coordinates that are restrictions of ambient charts are continuous on
their formula domains.
-/
def localLiouvilleMetricFormulaAtlasCoordinateContinuousOnDomainTheorem_of_coordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hChart :
      LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomainTheorem X) :
    LocalLiouvilleMetricFormulaAtlasCoordinateContinuousOnDomainTheorem X := by
  intro g metricFormulaAtlas x
  rcases hChart g metricFormulaAtlas x with ⟨hSub, hEq⟩
  exact ((chartAt ℂ x).continuousOn_toFun.mono hSub).congr hEq

/--
Chart-compatibility is preserved when a local curvature formula atlas is
rewritten as a Liouville metric formula atlas.
-/
def localLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain_of_localCurvatureMetricFormulaAtlasCoordinateChartedOnDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g}
    (hChart :
      LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomain curvatureFormulaAtlas) :
    LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain
      curvatureFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas := by
  intro x
  exact hChart x

/--
The global curvature-formula chart-compatibility target gives
chart-compatibility for every Liouville atlas obtained from such a curvature
formula atlas.
-/
def localLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain_of_localCurvatureMetricFormulaAtlasCoordinateChartedOnDomainTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hChart :
      LocalCurvatureMetricFormulaAtlasCoordinateChartedOnDomainTheorem X) :
    ∀ (g : HyperbolicMetric X)
      (curvatureFormulaAtlas : LocalCurvatureMetricFormulaAtlas X g),
      LocalLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain
        curvatureFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas := by
  intro g curvatureFormulaAtlas
  exact
    localLiouvilleMetricFormulaAtlasCoordinateChartedOnDomain_of_localCurvatureMetricFormulaAtlasCoordinateChartedOnDomain
      (hChart g curvatureFormulaAtlas)

/--
Off-diagonal surface transition compatibility gives the full surface transition
target, because the diagonal transition is the identity real Mobius map.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSurfaceTransitionTheorem_of_offDiagonal
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hOff :
      SurfaceRealUpperHalfPlaneBranchAtlasOffDiagonalSurfaceTransitionTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasSurfaceTransitionTheorem X := by
  intro g metricFormulaAtlas preData x y
  by_cases hxy : x = y
  · subst y
    exact HyperbolicLocalChart.hasRealMobiusTransition_self
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
  · exact hOff g metricFormulaAtlas preData x y hxy

/--
Overlapping off-diagonal compatibility gives the off-diagonal transition
target; disjoint overlaps are discharged vacuously using the identity real
Mobius representative.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOffDiagonalSurfaceTransitionTheorem_of_overlappingOffDiagonal
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hOverlap :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasOffDiagonalSurfaceTransitionTheorem X := by
  intro g metricFormulaAtlas preData x y hxy
  let U :=
    (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
  let V :=
    (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
  change U.HasRealMobiusTransition V
  by_cases hUV : Set.Nonempty (U.domain ∩ V.domain)
  · exact hOverlap g metricFormulaAtlas preData x y hxy hUV
  · refine ⟨1, ?_⟩
    intro z hzU hzV
    exfalso
    exact hUV ⟨z, hzU, hzV⟩

/--
Pointwise overlapping off-diagonal compatibility gives pointwise full surface
transition compatibility for one chosen Liouville metric formula atlas.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSurfaceTransitionFor_of_overlappingOffDiagonalFor
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (hOverlap :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionFor
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasSurfaceTransitionFor metricFormulaAtlas := by
  intro preData x y
  by_cases hxy : x = y
  · subst y
    exact HyperbolicLocalChart.hasRealMobiusTransition_self
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
  · let U :=
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
    let V :=
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
    change U.HasRealMobiusTransition V
    by_cases hUV : Set.Nonempty (U.domain ∩ V.domain)
    · exact hOverlap preData x y hxy hUV
    · refine ⟨1, ?_⟩
      intro z hzU hzV
      exfalso
      exact hUV ⟨z, hzU, hzV⟩

/--
Local hyperbolic-chart uniqueness plus preconnected selected overlaps gives
the overlap-only surface transition target.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionTheorem_of_localChartPreconnectedOverlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal :
      HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionTheorem X := by
  intro g metricFormulaAtlas preData x y hxy hne
  let U :=
    (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
  let V :=
    (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
  change U.HasRealMobiusTransition V
  exact hLocal g U V hne
    (hOverlapPreconnected g metricFormulaAtlas preData x y hxy hne)

/--
Pointwise local hyperbolic-chart uniqueness plus preconnected selected
overlaps gives pointwise overlap-only surface transitions.
-/
def surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionFor_of_localChartPreconnectedOverlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (hLocal :
      HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedFor
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionFor
      metricFormulaAtlas := by
  intro preData x y hxy hne
  let U :=
    (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
  let V :=
    (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
  change U.HasRealMobiusTransition V
  exact hLocal g U V hne
    (hOverlapPreconnected preData x y hxy hne)

/--
For one selected surface predata object, local hyperbolic-chart uniqueness plus
preconnected selected overlaps gives all surface transition maps.  Diagonal
overlaps are identity transitions, and empty off-diagonal overlaps are
vacuous.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSurfaceTransitionForPreData_of_localChartPreconnectedOverlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hLocal :
      HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapPreconnected preData) :
    ∀ x y : X,
      HyperbolicLocalChart.HasRealMobiusTransition
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart) := by
  intro x y
  by_cases hxy : x = y
  · subst y
    exact HyperbolicLocalChart.hasRealMobiusTransition_self
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
  · let U :=
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
    let V :=
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
    change U.HasRealMobiusTransition V
    by_cases hUV : Set.Nonempty (U.domain ∩ V.domain)
    · exact hLocal g U V hUV (hOverlapPreconnected x y hxy hUV)
    · refine ⟨1, ?_⟩
      intro z hzU hzV
      exfalso
      exact hUV ⟨z, hzU, hzV⟩

/--
For one selected surface predata object, pointed transitions on its actual
nonempty off-diagonal overlaps plus connected-overlap extension give all
surface transition maps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasSurfaceTransitionForPreData_of_pointed_extension_overlapPreconnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas)
    (hPoint :
      ∀ x y : X, x ≠ y →
        Set.Nonempty
          ((((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
            (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) →
        ∃ (x₀ : X) (A : RealMobiusRepresentative),
          HyperbolicLocalChartPointedRealMobiusTransition
            (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
            (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
            A x₀)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataOverlapPreconnected preData) :
    ∀ x y : X,
      HyperbolicLocalChart.HasRealMobiusTransition
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
        (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart) := by
  intro x y
  by_cases hxy : x = y
  · subst y
    exact HyperbolicLocalChart.hasRealMobiusTransition_self
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
  · let U :=
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
    let V :=
      (((preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
    change U.HasRealMobiusTransition V
    by_cases hUV : Set.Nonempty (U.domain ∩ V.domain)
    · rcases hPoint x y hxy hUV with ⟨x₀, A, hpoint⟩
      refine ⟨A, ?_⟩
      intro z hzU hzV
      exact
        hExtend g U V A x₀ hpoint
          (hOverlapPreconnected x y hxy hUV) z hzU hzV
    · refine ⟨1, ?_⟩
      intro z hzU hzV
      exfalso
      exact hUV ⟨z, hzU, hzV⟩

/--
A selected surface predata object with preconnected overlaps assembles to
surface real branch-atlas data once local hyperbolic-chart uniqueness on
preconnected overlaps is available.
-/
def surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapPreData_and_localChartPreconnectedOverlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preconnectedPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
        metricFormulaAtlas)
    (hLocal :
      HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasData metricFormulaAtlas where
  preData := preconnectedPreData.preData
  transition_realMobius :=
    surfaceRealUpperHalfPlaneBranchAtlasSurfaceTransitionForPreData_of_localChartPreconnectedOverlap
      preconnectedPreData.preData hLocal preconnectedPreData.overlap_preconnected

/--
A selected surface predata object with preconnected overlaps assembles to
surface real branch-atlas data from pointed transitions on its actual overlaps
and connected-overlap extension.
-/
def surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapPreData_and_pointedOverlapTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preconnectedPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
        metricFormulaAtlas)
    (hPoint :
      ∀ x y : X, x ≠ y →
        Set.Nonempty
          ((((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
            (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) →
        ∃ (x₀ : X) (A : RealMobiusRepresentative),
          HyperbolicLocalChartPointedRealMobiusTransition
            (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
            (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
            A x₀)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasData metricFormulaAtlas where
  preData := preconnectedPreData.preData
  transition_realMobius :=
    surfaceRealUpperHalfPlaneBranchAtlasSurfaceTransitionForPreData_of_pointed_extension_overlapPreconnected
      preconnectedPreData.preData hPoint hExtend
      preconnectedPreData.overlap_preconnected

/--
A selected surface predata object with preconnected overlaps assembles to
surface real branch-atlas data from pointed transitions on its actual overlaps
and propagation on those same selected overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapPreData_and_pointedOverlapTransitions_selectedPointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (preconnectedPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreData
        metricFormulaAtlas)
    (hPoint :
      ∀ x y : X, x ≠ y →
        Set.Nonempty
          ((((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart).domain ∩
            (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart).domain) →
        ∃ (x₀ : X) (A : RealMobiusRepresentative),
          HyperbolicLocalChartPointedRealMobiusTransition
            (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
            (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
            A x₀)
    (hExtend :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps
        preconnectedPreData) :
    SurfaceRealUpperHalfPlaneBranchAtlasData metricFormulaAtlas where
  preData := preconnectedPreData.preData
  transition_realMobius := by
    intro x y
    by_cases hxy : x = y
    · subst y
      exact HyperbolicLocalChart.hasRealMobiusTransition_self
        (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
    · let U :=
        (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
      let V :=
        (((preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
      change U.HasRealMobiusTransition V
      by_cases hUV : Set.Nonempty (U.domain ∩ V.domain)
      · rcases hPoint x y hxy hUV with ⟨x₀, A, hpoint⟩
        refine ⟨A, ?_⟩
        intro z hzU hzV
        exact hExtend x y hxy hUV A x₀ hpoint z hzU hzV
      · refine ⟨1, ?_⟩
        intro z hzU hzV
        exfalso
        exact hUV ⟨z, hzU, hzV⟩

/--
A selected chart-compatible predata object with preconnected overlaps
assembles to surface real branch-atlas data once pointed matches extend over
preconnected overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapChartedPreData_and_pointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (chartedPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedPreData
        metricFormulaAtlas)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasData metricFormulaAtlas :=
  surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapPreData_and_pointedOverlapTransitions
    chartedPreData.preconnectedPreData
    (surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionForPreData_of_coordinateEqOnChartAt
      chartedPreData.preconnectedPreData.preData
      chartedPreData.coordinate_eqOn_chartAt)
    hExtend

/--
A concrete charted selector assembles to surface real branch-atlas data once
pointed matches extend over preconnected overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapChartedSelection_and_pointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (selection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
        metricFormulaAtlas)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasData metricFormulaAtlas :=
  surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapChartedPreData_and_pointedExtension
    selection.toPreconnectedOverlapChartedPreData hExtend

/--
A selected chart-compatible predata object assembles to surface real branch
atlas data from propagation on its own selected overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapChartedPreData_and_selectedPointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (chartedPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedPreData
        metricFormulaAtlas)
    (hExtend :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps
        chartedPreData.preconnectedPreData) :
    SurfaceRealUpperHalfPlaneBranchAtlasData metricFormulaAtlas where
  preData := chartedPreData.preconnectedPreData.preData
  transition_realMobius := by
    intro x y
    by_cases hxy : x = y
    · subst y
      exact HyperbolicLocalChart.hasRealMobiusTransition_self
        (((chartedPreData.preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
    · let U :=
        (((chartedPreData.preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
      let V :=
        (((chartedPreData.preconnectedPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
      change U.HasRealMobiusTransition V
      by_cases hUV : Set.Nonempty (U.domain ∩ V.domain)
      · rcases
          surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionForPreData_of_coordinateEqOnChartAt
            chartedPreData.preconnectedPreData.preData
            chartedPreData.coordinate_eqOn_chartAt x y hxy hUV with
          ⟨x₀, A, hpoint⟩
        refine ⟨A, ?_⟩
        intro z hzU hzV
        exact hExtend x y hxy hUV A x₀ hpoint z hzU hzV
      · refine ⟨1, ?_⟩
        intro z hzU hzV
        exfalso
        exact hUV ⟨z, hzU, hzV⟩

/--
A concrete charted selector assembles to surface real branch-atlas data from
propagation on its own selected overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapChartedSelection_and_selectedPointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (selection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelection
        metricFormulaAtlas)
    (hExtend :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps
        selection.toPreconnectedOverlapPreData) :
    SurfaceRealUpperHalfPlaneBranchAtlasData metricFormulaAtlas :=
  surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapChartedPreData_and_selectedPointedExtension
    selection.toPreconnectedOverlapChartedPreData hExtend

/--
A locally charted selected predata object assembles to surface real branch
atlas data from propagation on its own selected overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapLocallyChartedSelection_and_selectedPointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (selection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelection
        metricFormulaAtlas)
    (hExtend :
      SurfaceRealUpperHalfPlaneBranchAtlasPreDataPointedTransitionExtendsOnOverlaps
        selection.toPreconnectedOverlapPreData) :
    SurfaceRealUpperHalfPlaneBranchAtlasData metricFormulaAtlas where
  preData := selection.toPreconnectedOverlapPreData.preData
  transition_realMobius := by
    intro x y
    by_cases hxy : x = y
    · subst y
      exact HyperbolicLocalChart.hasRealMobiusTransition_self
        (((selection.toPreconnectedOverlapPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
    · let U :=
        (((selection.toPreconnectedOverlapPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt x).toHyperbolicLocalChart)
      let V :=
        (((selection.toPreconnectedOverlapPreData.preData.toSurfaceSchwarzianPointedBranchPreData).solutionAt y).toHyperbolicLocalChart)
      change U.HasRealMobiusTransition V
      by_cases hUV : Set.Nonempty (U.domain ∩ V.domain)
      · rcases
          surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionForPreData_of_coordinateEventuallyEqOnChartAt
            selection.toPreconnectedOverlapPreData.preData
            selection.coordinate_eventuallyEqOn_chartAt x y hxy hUV with
          ⟨x₀, A, hpoint⟩
        refine ⟨A, ?_⟩
        intro z hzU hzV
        exact hExtend x y hxy hUV A x₀ hpoint z hzU hzV
      · refine ⟨1, ?_⟩
        intro z hzU hzV
        exfalso
        exact hUV ⟨z, hzU, hzV⟩

/--
A concrete charted selector with selected-overlap propagation assembles to
surface real branch-atlas data.
-/
def surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapChartedSelectionWithPropagation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (selection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagation
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasData metricFormulaAtlas :=
  surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapChartedSelection_and_selectedPointedExtension
    selection.toChartedSelection
    selection.selected_pointed_extension

/--
A locally charted selector with selected-overlap propagation assembles to
surface real branch-atlas data.
-/
def surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapLocallyChartedSelectionWithPropagation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : HyperbolicMetric X}
    {metricFormulaAtlas : LocalLiouvilleMetricFormulaAtlas X g}
    (selection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapLocallyChartedSelectionWithPropagation
        metricFormulaAtlas) :
    SurfaceRealUpperHalfPlaneBranchAtlasData metricFormulaAtlas :=
  surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapLocallyChartedSelection_and_selectedPointedExtension
    selection.toLocallyChartedSelection
    selection.selected_pointed_extension

/--
If the surface branch predata can be selected with preconnected overlaps, then
local hyperbolic-chart uniqueness gives the surface real-branch data theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_localChartPreconnectedOverlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem X)
    (hLocal :
      HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X := by
  intro g metricFormulaAtlas
  let preconnectedPreData := Classical.choice (hPreData g metricFormulaAtlas)
  exact ⟨
    surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapPreData_and_localChartPreconnectedOverlap
      preconnectedPreData hLocal⟩

/--
If the surface branch predata can be selected with preconnected overlaps, then
pointed transitions on the selected overlaps plus connected-overlap extension
give the surface real-branch data theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_pointedOverlapTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem X)
    (hPoint :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem
        X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X := by
  intro g metricFormulaAtlas
  let preconnectedPreData := Classical.choice (hPreData g metricFormulaAtlas)
  exact ⟨
    surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapPreData_and_pointedOverlapTransitions
      preconnectedPreData
      (fun x y hxy hne ↦
        hPoint g metricFormulaAtlas preconnectedPreData.preData x y hxy hne)
      hExtend⟩

/--
If the surface branch predata can be selected with preconnected overlaps and
chart-compatible coordinate pullback formulae, then pointed connected-overlap
extension gives the surface real-branch data theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapChartedSelection_and_pointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X := by
  intro g metricFormulaAtlas
  rcases hSelection g metricFormulaAtlas with ⟨S⟩
  exact
    ⟨surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapChartedSelection_and_pointedExtension
      S hExtend⟩

/--
If the surface branch predata can be selected with chart-compatible coordinate
pullback formulae and selected-overlap propagation, then it gives the surface
real-branch data theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapChartedSelectionWithPropagation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagationTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X := by
  intro g metricFormulaAtlas
  rcases hSelection g metricFormulaAtlas with ⟨S⟩
  exact
    ⟨surfaceRealUpperHalfPlaneBranchAtlasData_of_preconnectedOverlapChartedSelectionWithPropagation
      S⟩

/--
If the surface branch predata can be selected with chart-compatible
coordinates and selected one-jet local uniqueness, then it gives the surface
real-branch data theorem without using the global value-only equality
openness package.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapChartedSelection_and_selectedOneJetLocalUniqueness
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionTheorem
        X)
    (hUnique :
      SurfaceRealUpperHalfPlaneBranchAtlasSelectedOneJetLocalUniquenessTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapChartedSelectionWithPropagation
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapChartedSelectionWithPropagationTheorem_of_chartedSelection_and_selectedOneJetLocalUniqueness
      hSelection hUnique)

/--
The older global pointed-local-chart transition input supplies the selected
pointed-overlap transition input, hence also the surface real-branch data
theorem by the selected-overlap route.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_pointedLocalChartTransitions_via_pointedOverlaps
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem X)
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_pointedOverlapTransitions
    hPreData
    (surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem_of_localChartPointedTransitions
      hPoint)
    hExtend

/--
Coordinate derivative data supplies the selected pointed-overlap transitions,
so a selected surface predata object with preconnected overlaps assembles once
pointed matches extend over preconnected overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_coordinateDerivativeData_pointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem X)
    (hDeriv :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_pointedOverlapTransitions
    hPreData
    (surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem_of_coordinateDerivativeData
      hDeriv)
    hExtend

/--
Pointed derivative data for coordinate pullback formulae supplies the selected
pointed-overlap transitions needed for assembly from a selected predata object
with preconnected overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_coordinatePullbackFormulaPointedDerivativeData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem X)
    (hData :
      CoordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem
        X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_pointedOverlapTransitions
    hPreData
    (surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem_of_coordinatePullbackFormulaPointedDerivativeData
      hData)
    hExtend

/--
Ambient derivative-norm identification for coordinate pullback formulae
supplies the selected pointed-overlap transitions needed for assembly from a
selected predata object with preconnected overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_coordinatePullbackFormulaAmbientDerivativeNormSq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem X)
    (hDeriv :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqTheorem X)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_coordinatePullbackFormulaPointedDerivativeData
    hPreData
    (coordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem_of_ambientDerivativeNormSq
      hDeriv hChart)
    hExtend

/--
Chart-compatibility for coordinate pullback formulae supplies the selected
pointed-overlap transitions needed for assembly from a selected predata object
with preconnected overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_coordinatePullbackFormulaEqOnChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem X)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_coordinatePullbackFormulaPointedDerivativeData
    hPreData
    (coordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem_of_eqOn_chartAt
      hChart)
    hExtend

/--
Nonzero coordinate derivatives and the Poincare pullback squared-density
formula supply the selected pointed-overlap transitions needed for assembly
from a selected predata object with preconnected overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_pullbackSquaredDensity_pointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem X)
    (hDeriv : HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull : HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_coordinateDerivativeData_pointedExtension
    hPreData
    (hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula
      hDeriv hPull)
    hExtend

/--
The Poincare pullback squared-density formula alone supplies selected
pointed-overlap transitions for a selected predata object with preconnected
overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_pullbackSquaredDensityFormula_pointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem X)
    (hPull : HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_coordinateDerivativeData_pointedExtension
    hPreData
    (hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula_proved
      hPull)
    hExtend

/--
If the concrete surface-predata selector exists, then local hyperbolic-chart
uniqueness gives the surface real-branch data theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_localChartPreconnectedOverlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hLocal :
      HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_localChartPreconnectedOverlap
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem_of_selection
      hSelection)
    hLocal

/--
If the concrete surface-predata selector exists, selected-overlap pointed
transitions plus connected-overlap extension give the surface real-branch data
theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_pointedOverlapTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hPoint :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem
        X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_pointedOverlapTransitions
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem_of_selection
      hSelection)
    hPoint hExtend

/--
Coordinate derivative data supplies the selected pointed-overlap transitions
for a concrete preconnected-overlap selection.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_coordinateDerivativeData_pointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hDeriv :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_pointedOverlapTransitions
    hSelection
    (surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem_of_coordinateDerivativeData
      hDeriv)
    hExtend

/--
Pointed derivative data for coordinate pullback formulae supplies selected
pointed-overlap transitions for a concrete preconnected-overlap selection.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_coordinatePullbackFormulaPointedDerivativeData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hData :
      CoordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem
        X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_pointedOverlapTransitions
    hSelection
    (surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem_of_coordinatePullbackFormulaPointedDerivativeData
      hData)
    hExtend

/--
Ambient derivative-norm identification for coordinate pullback formulae
supplies selected pointed-overlap transitions for a concrete
preconnected-overlap selection.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_coordinatePullbackFormulaAmbientDerivativeNormSq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hDeriv :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqTheorem X)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_coordinatePullbackFormulaPointedDerivativeData
    hSelection
    (coordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem_of_ambientDerivativeNormSq
      hDeriv hChart)
    hExtend

/--
Chart-compatibility for coordinate pullback formulae supplies selected
pointed-overlap transitions for a concrete preconnected-overlap selection.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_coordinatePullbackFormulaEqOnChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_coordinatePullbackFormulaPointedDerivativeData
    hSelection
    (coordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem_of_eqOn_chartAt
      hChart)
    hExtend

/--
Nonzero coordinate derivatives and the Poincare pullback squared-density
formula supply selected pointed-overlap transitions for a concrete
preconnected-overlap selection.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_pullbackSquaredDensity_pointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hDeriv : HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull : HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_coordinateDerivativeData_pointedExtension
    hSelection
    (hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula
      hDeriv hPull)
    hExtend

/--
The Poincare pullback squared-density formula alone supplies selected
pointed-overlap transitions for a concrete preconnected-overlap selection.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_pullbackSquaredDensityFormula_pointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hPull : HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_coordinateDerivativeData_pointedExtension
    hSelection
    (hyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem_of_pullbackSquaredDensityFormula_proved
      hPull)
    hExtend

/--
Local real branch existence, restricted-domain openness, selected-overlap
preconnectedness, and local hyperbolic-chart uniqueness give surface real
branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_localChartPreconnectedOverlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hLocalChart :
      HyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_localChartPreconnectedOverlap
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_localRealBranches_openness_overlapPreconnected
      hLocalBranches hOpen hOverlapPreconnected)
    hLocalChart

/--
Local real branch existence, restricted-domain openness, selected-overlap
preconnectedness, selected-overlap pointed transitions, and connected-overlap
extension give surface real branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_pointedOverlapTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hPoint :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalPointedTransitionTheorem
        X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_pointedOverlapTransitions
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_localRealBranches_openness_overlapPreconnected
      hLocalBranches hOpen hOverlapPreconnected)
    hPoint hExtend

/--
Local real branch existence, restricted-domain openness, selected-overlap
preconnectedness, coordinate derivative data, and connected-overlap extension
give surface real branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_coordinateDerivativeData_pointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hDeriv :
      HyperbolicLocalChartsHavePointedCoordinateDerivativeDataTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_coordinateDerivativeData_pointedExtension
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_localRealBranches_openness_overlapPreconnected
      hLocalBranches hOpen hOverlapPreconnected)
    hDeriv hExtend

/--
Local real branch existence, restricted-domain openness, selected-overlap
preconnectedness, coordinate-pullback pointed derivative data, and
connected-overlap extension give surface real branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_coordinatePullbackFormulaPointedDerivativeData
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hData :
      CoordinateUpperHalfPlanePullbackFormulaPointedCoordinateDerivativeDataTheorem
        X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_coordinatePullbackFormulaPointedDerivativeData
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_localRealBranches_openness_overlapPreconnected
      hLocalBranches hOpen hOverlapPreconnected)
    hData hExtend

/--
Local real branch existence, restricted-domain openness, selected-overlap
preconnectedness, ambient derivative-norm identification for coordinate
pullback formulae, and connected-overlap extension give surface real
branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_coordinatePullbackFormulaAmbientDerivativeNormSq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hDeriv :
      CoordinateUpperHalfPlanePullbackFormulaAmbientDerivativeNormSqTheorem X)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_coordinatePullbackFormulaAmbientDerivativeNormSq
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_localRealBranches_openness_overlapPreconnected
      hLocalBranches hOpen hOverlapPreconnected)
    hDeriv hChart hExtend

/--
Local real branch existence, restricted-domain openness, selected-overlap
preconnectedness, chart-compatibility for coordinate pullback formulae, and
connected-overlap extension give surface real branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_coordinatePullbackFormulaEqOnChartAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hChart :
      CoordinateUpperHalfPlanePullbackFormulaCoordinateEqOnChartAtTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_coordinatePullbackFormulaEqOnChartAt
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_localRealBranches_openness_overlapPreconnected
      hLocalBranches hOpen hOverlapPreconnected)
    hChart hExtend

/--
Local real branch existence, restricted-domain openness, selected-overlap
preconnectedness, nonzero coordinate derivatives, the Poincare pullback
squared-density formula, and connected-overlap extension give surface real
branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_pullbackSquaredDensity_pointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hDeriv : HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull : HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_pullbackSquaredDensity_pointedExtension
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_localRealBranches_openness_overlapPreconnected
      hLocalBranches hOpen hOverlapPreconnected)
    hDeriv hPull hExtend

/--
Local real branch existence, restricted-domain openness, selected-overlap
preconnectedness, the Poincare pullback squared-density formula, and
connected-overlap extension give surface real branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_pullbackSquaredDensityFormula_pointedExtension
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hPull : HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_pullbackSquaredDensityFormula_pointedExtension
    (surfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem_of_localRealBranches_openness_overlapPreconnected
      hLocalBranches hOpen hOverlapPreconnected)
    hPull hExtend

/--
Pointed frame matching plus connected-overlap propagation are enough to use a
selected predata object with preconnected overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_pointedLocalChartTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem X)
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_localChartPreconnectedOverlap
    hPreData
    (hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_extension
      hPoint hExtend)

/--
Pointed frame matching plus connected-overlap propagation are enough to use a
concretely selected predata object with preconnected overlaps.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_pointedLocalChartTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_localChartPreconnectedOverlap
    hSelection
    (hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_extension
      hPoint hExtend)

/--
Local real branch existence, restricted-domain openness, selected-overlap
preconnectedness, and pointed local-chart uniqueness give surface real
branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_pointedLocalChartTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hPoint :
      HyperbolicLocalChartsAdmitPointedRealMobiusTransitionTheorem X)
    (hExtend :
      PointedHyperbolicLocalChartRealMobiusTransitionExtendsOnPreconnectedOverlapTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_localChartPreconnectedOverlap
    hLocalBranches hOpen hOverlapPreconnected
    (hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_pointed_extension
      hPoint hExtend)

/--
Bundled analytic local-isometry consequences plus a selected predata object
with preconnected overlaps give surface real branch-atlas data.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_analyticLocalIsometryConsequences
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hPreData :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapPreDataTheorem X)
    (hAnalytic :
      HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapPreData_and_localChartPreconnectedOverlap
    hPreData
    (hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_analyticLocalIsometryConsequences
      hAnalytic)

/--
Bundled analytic local-isometry consequences plus a concrete selected predata
object with preconnected overlaps give surface real branch-atlas data.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_analyticLocalIsometryConsequences
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hAnalytic :
      HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_localChartPreconnectedOverlap
    hSelection
    (hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_analyticLocalIsometryConsequences
      hAnalytic)

/--
Corrected one-jet analytic local-isometry consequences plus a selected predata
object with preconnected overlaps give surface real branch-atlas data.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_analyticOneJetLocalIsometryConsequences
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hAnalytic :
      HyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_analyticLocalIsometryConsequences
    hSelection
    (hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_oneJet
      hAnalytic)

/--
Selected predata with preconnected overlaps, concrete metric frame data, and
one-jet openness give surface real branch-atlas data.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_analyticOneJetLocalIsometryConsequences
    hSelection
    (hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_oneJetEqualitySetOpen
      hDeriv hPull hChart hOpen hValueFirst)

/--
Selected predata with preconnected overlaps, the Poincare pullback
squared-density formula, chart continuity, and one-jet openness give surface
real branch-atlas data.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_oneJetEqualitySetOpen_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_analyticOneJetLocalIsometryConsequences
    hSelection
    (hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_oneJetEqualitySetOpen_pullbackSquaredDensityFormula
      hPull hChart hOpen hValueFirst)

/--
Selected predata with preconnected overlaps, concrete metric frame data, and
component stability from the actual holomorphic local-isometry fields give
surface real branch-atlas data.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_holomorphicLocalIsometryComponentStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hStability :
      HyperbolicLocalChartHolomorphicLocalIsometryComponentStabilityTheorems
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_analyticOneJetLocalIsometryConsequences
    hSelection
    (hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_holomorphicLocalIsometryComponentStability
      hDeriv hPull hChart hStability hValueFirst)

/--
Selected predata with preconnected overlaps, the Poincare pullback
squared-density formula, and component stability from the actual holomorphic
local-isometry fields give surface real branch-atlas data.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_holomorphicLocalIsometryComponentStability_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hStability :
      HyperbolicLocalChartHolomorphicLocalIsometryComponentStabilityTheorems
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_analyticOneJetLocalIsometryConsequences
    hSelection
    (hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_holomorphicLocalIsometryComponentStability_pullbackSquaredDensityFormula
      hPull hChart hStability hValueFirst)

/--
Selected predata with preconnected overlaps, concrete metric frame data, and
direct one-jet stability from the actual holomorphic local-isometry fields
give surface real branch-atlas data.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_holomorphicLocalIsometryOneJetStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hStability :
      HyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_analyticOneJetLocalIsometryConsequences
    hSelection
    (hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_holomorphicLocalIsometryOneJetStability
      hDeriv hPull hChart hStability hValueFirst)

/--
Selected predata with preconnected overlaps, the Poincare pullback
squared-density formula, and direct one-jet stability from the actual
holomorphic local-isometry fields give surface real branch-atlas data.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_holomorphicLocalIsometryOneJetStability_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hSelection :
      SurfaceRealUpperHalfPlaneBranchAtlasPreconnectedOverlapSelectionTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hStability :
      HyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_preconnectedOverlapSelection_and_analyticOneJetLocalIsometryConsequences
    hSelection
    (hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_holomorphicLocalIsometryOneJetStability_pullbackSquaredDensityFormula
      hPull hChart hStability hValueFirst)

/--
Local real branch existence, restricted-domain openness, selected-overlap
preconnectedness, and bundled analytic local-isometry consequences give
surface real branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_analyticLocalIsometryConsequences
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hAnalytic :
      HyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_localChartPreconnectedOverlap
    hLocalBranches hOpen hOverlapPreconnected
    (hyperbolicLocalChartsOnPreconnectedOverlapHaveRealMobiusTransitionTheorem_of_analyticLocalIsometryConsequences
      hAnalytic)

/--
Local real branches, restricted-domain openness, selected-overlap
preconnectedness, and corrected one-jet analytic local-isometry consequences
give surface real branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_analyticOneJetLocalIsometryConsequences
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpen :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hAnalytic :
      HyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_analyticLocalIsometryConsequences
    hLocalBranches hOpen hOverlapPreconnected
    (hyperbolicLocalChartsHaveAnalyticLocalIsometryConsequencesTheorem_of_oneJet
      hAnalytic)

/--
Local real branches, restricted-domain openness, selected-overlap
preconnectedness, concrete metric frame data, and one-jet openness give
surface real branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_oneJetEqualitySetOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpenDomains :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hOneJetOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_analyticOneJetLocalIsometryConsequences
    hLocalBranches hOpenDomains hOverlapPreconnected
    (hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_oneJetEqualitySetOpen
      hDeriv hPull hChart hOneJetOpen hValueFirst)

/--
Local real branches, restricted-domain openness, selected-overlap
preconnectedness, the Poincare pullback squared-density formula, and one-jet
openness give surface real branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_oneJetEqualitySetOpen_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpenDomains :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hOneJetOpen :
      PointedHyperbolicLocalChartRealMobiusTransitionOneJetEqualitySetIsOpenTheorem
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_analyticOneJetLocalIsometryConsequences
    hLocalBranches hOpenDomains hOverlapPreconnected
    (hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_oneJetEqualitySetOpen_pullbackSquaredDensityFormula
      hPull hChart hOneJetOpen hValueFirst)

/--
Local real branches, restricted-domain openness, selected-overlap
preconnectedness, concrete metric frame data, and component stability from the
actual holomorphic local-isometry fields give surface real branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_holomorphicLocalIsometryComponentStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpenDomains :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hStability :
      HyperbolicLocalChartHolomorphicLocalIsometryComponentStabilityTheorems
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_analyticOneJetLocalIsometryConsequences
    hLocalBranches hOpenDomains hOverlapPreconnected
    (hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_holomorphicLocalIsometryComponentStability
      hDeriv hPull hChart hStability hValueFirst)

/--
Local real branches, restricted-domain openness, selected-overlap
preconnectedness, the Poincare pullback squared-density formula, and
component stability from the actual holomorphic local-isometry fields give
surface real branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_holomorphicLocalIsometryComponentStability_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpenDomains :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hStability :
      HyperbolicLocalChartHolomorphicLocalIsometryComponentStabilityTheorems
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_analyticOneJetLocalIsometryConsequences
    hLocalBranches hOpenDomains hOverlapPreconnected
    (hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_holomorphicLocalIsometryComponentStability_pullbackSquaredDensityFormula
      hPull hChart hStability hValueFirst)

/--
Local real branches, restricted-domain openness, selected-overlap
preconnectedness, concrete metric frame data, and direct one-jet stability
from the actual holomorphic local-isometry fields give surface real
branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_holomorphicLocalIsometryOneJetStability
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpenDomains :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hDeriv :
      HyperbolicLocalChartCoordinateDerivativeNonzeroTheorem X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hStability :
      HyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_analyticOneJetLocalIsometryConsequences
    hLocalBranches hOpenDomains hOverlapPreconnected
    (hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_holomorphicLocalIsometryOneJetStability
      hDeriv hPull hChart hStability hValueFirst)

/--
Local real branches, restricted-domain openness, selected-overlap
preconnectedness, the Poincare pullback squared-density formula, and direct
one-jet stability from the actual holomorphic local-isometry fields give
surface real branch-atlas data.
-/
noncomputable def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_holomorphicLocalIsometryOneJetStability_pullbackSquaredDensityFormula
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocalBranches :
      HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpenDomains :
      SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hOverlapPreconnected :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceOverlapPreconnectedTheorem
        X)
    (hPull :
      HyperbolicLocalChartPullbackSquaredDensityFormulaTheorem X)
    (hChart :
      HyperbolicLocalChartContinuousOnDomainTheorem X)
    (hStability :
      HyperbolicLocalChartHolomorphicLocalIsometryOneJetStabilityTheorems
        X)
    (hValueFirst :
      PointedHyperbolicLocalChartRealMobiusTransitionValueEqualityForcesFirstOrderTheorem
        X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_overlapPreconnected_and_analyticOneJetLocalIsometryConsequences
    hLocalBranches hOpenDomains hOverlapPreconnected
    (hyperbolicLocalChartsHaveAnalyticOneJetLocalIsometryConsequencesTheorem_of_holomorphicLocalIsometryOneJetStability_pullbackSquaredDensityFormula
      hPull hChart hStability hValueFirst)

/--
The Liouville-atlas overlapping surface transition target implies the sharper
curvature-derived version.
-/
def localCurvatureMetricFormulaAtlasOverlappingOffDiagonalSurfaceTransitionTheorem_of_surfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hOverlap :
      SurfaceRealUpperHalfPlaneBranchAtlasOverlappingOffDiagonalSurfaceTransitionTheorem X) :
    LocalCurvatureMetricFormulaAtlasOverlappingOffDiagonalSurfaceTransitionTheorem X := by
  intro g curvatureFormulaAtlas preData x y hxy hne
  exact hOverlap g curvatureFormulaAtlas.toLocalLiouvilleMetricFormulaAtlas preData x y hxy hne

/--
The openness and cross-chart transition targets imply the older monolithic
surface real-branch assembly theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasAssemblyTheorem_of_openness_and_transitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hOpen : SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hTransition : SurfaceRealUpperHalfPlaneBranchAtlasSurfaceTransitionTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasAssemblyTheorem X := by
  intro g metricFormulaAtlas hLocal
  let realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (metricFormulaAtlas.formulaAt x).conformalFactor :=
    fun x ↦ Classical.choice (hLocal x)
  let preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas :=
    { realBranchAtlasAt := realBranchAtlasAt
      restricted_domain_open := hOpen g metricFormulaAtlas realBranchAtlasAt }
  exact ⟨
    { preData := preData
      transition_realMobius := hTransition g metricFormulaAtlas preData }⟩

/--
Pointwise coordinate real branch existence, pointwise surface-domain openness,
and pointwise transition compatibility assemble real branch-atlas data for one
chosen Liouville metric formula atlas.
-/
@[reducible] def surfaceRealUpperHalfPlaneBranchAtlasData_of_localRealBranches_openness_and_transitions_for
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
        metricFormulaAtlas)
    (hTransition :
      SurfaceRealUpperHalfPlaneBranchAtlasSurfaceTransitionFor
        metricFormulaAtlas) :
    Nonempty (SurfaceRealUpperHalfPlaneBranchAtlasData metricFormulaAtlas) := by
  let realBranchAtlasAt :
      ∀ x : X,
        LocalRealUpperHalfPlaneBranchAtlas
          (metricFormulaAtlas.formulaAt x).conformalFactor :=
    fun x ↦ Classical.choice (hLocal x)
  let preData : SurfaceRealUpperHalfPlaneBranchAtlasPreData metricFormulaAtlas :=
    { realBranchAtlasAt := realBranchAtlasAt
      restricted_domain_open := hOpen realBranchAtlasAt }
  exact ⟨
    { preData := preData
      transition_realMobius := hTransition preData }⟩

/--
Coordinate real branch existence, surface-domain openness, and cross-chart
transition compatibility give the surface real-branch data theorem.
-/
def surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_openness_and_transitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal : HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hOpen : SurfaceRealUpperHalfPlaneBranchAtlasRestrictedDomainOpennessTheorem X)
    (hTransition : SurfaceRealUpperHalfPlaneBranchAtlasSurfaceTransitionTheorem X) :
    SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X :=
  surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_and_surfaceAssembly
    hLocal
    (surfaceRealUpperHalfPlaneBranchAtlasAssemblyTheorem_of_openness_and_transitions
      hOpen hTransition)

/--
Coordinate real branch existence plus surface assembly gives pointed
Schwarzian branch data.
-/
def surfaceSchwarzianPointedBranchDataTheorem_of_localRealBranches_and_surfaceAssembly
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal : HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hAssembly : SurfaceRealUpperHalfPlaneBranchAtlasAssemblyTheorem X) :
    SurfaceSchwarzianPointedBranchDataTheorem X :=
  surfaceSchwarzianPointedBranchDataTheorem_of_surfaceRealUpperHalfPlaneBranchAtlasDataTheorem
    (surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_and_surfaceAssembly
      hLocal hAssembly)

/-- Schwarzian local solving forgets to a local developing-solution atlas. -/
def localDevelopingSolutionsFromLiouvilleFormulaAtlasTheorem_of_localSolvingFromSchwarzianBranchDataTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h : LocalSolvingFromSchwarzianBranchDataTheorem X) :
    LocalDevelopingSolutionsFromLiouvilleFormulaAtlasTheorem X :=
  fun g metricFormulaAtlas ↦
    let S := Classical.choice (h g metricFormulaAtlas)
    ⟨S.toLocalLiouvilleDevelopingSolutionAtlas⟩

/--
Pointed Schwarzian local solving forgets to a local developing-solution atlas,
with the required shrinking already built into the branch data.
-/
def localDevelopingSolutionsFromLiouvilleFormulaAtlasTheorem_of_localSolvingFromPointedSchwarzianBranchDataTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h : LocalSolvingFromPointedSchwarzianBranchDataTheorem X) :
    LocalDevelopingSolutionsFromLiouvilleFormulaAtlasTheorem X :=
  fun g metricFormulaAtlas ↦
    let S := Classical.choice (h g metricFormulaAtlas)
    ⟨S.toLocalLiouvilleDevelopingSolutionAtlas⟩

/--
Pointed surface branch data is enough to produce local developing-solution
atlases from Liouville formula atlases.
-/
def localDevelopingSolutionsFromLiouvilleFormulaAtlasTheorem_of_surfaceSchwarzianPointedBranchDataTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h : SurfaceSchwarzianPointedBranchDataTheorem X) :
    LocalDevelopingSolutionsFromLiouvilleFormulaAtlasTheorem X :=
  localDevelopingSolutionsFromLiouvilleFormulaAtlasTheorem_of_localSolvingFromPointedSchwarzianBranchDataTheorem
    (localSolvingFromPointedSchwarzianBranchDataTheorem_of_surfaceSchwarzianPointedBranchDataTheorem h)

/--
Surface real branch-atlas data gives local developing-solution atlases after
forgetting to pointed Schwarzian branch data.
-/
def localDevelopingSolutionsFromLiouvilleFormulaAtlasTheorem_of_surfaceRealUpperHalfPlaneBranchAtlasDataTheorem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h : SurfaceRealUpperHalfPlaneBranchAtlasDataTheorem X) :
    LocalDevelopingSolutionsFromLiouvilleFormulaAtlasTheorem X :=
  localDevelopingSolutionsFromLiouvilleFormulaAtlasTheorem_of_surfaceSchwarzianPointedBranchDataTheorem
    (surfaceSchwarzianPointedBranchDataTheorem_of_surfaceRealUpperHalfPlaneBranchAtlasDataTheorem h)

/--
Coordinate real branch existence plus surface assembly gives local
developing-solution atlases from Liouville formula atlases.
-/
def localDevelopingSolutionsFromLiouvilleFormulaAtlasTheorem_of_localRealBranches_and_surfaceAssembly
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (hLocal : HyperbolicLiouvilleProducesLocalRealUpperHalfPlaneBranchAtlasTheorem)
    (hAssembly : SurfaceRealUpperHalfPlaneBranchAtlasAssemblyTheorem X) :
    LocalDevelopingSolutionsFromLiouvilleFormulaAtlasTheorem X :=
  localDevelopingSolutionsFromLiouvilleFormulaAtlasTheorem_of_surfaceRealUpperHalfPlaneBranchAtlasDataTheorem
    (surfaceRealUpperHalfPlaneBranchAtlasDataTheorem_of_localRealBranches_and_surfaceAssembly
      hLocal hAssembly)

end HyperbolicMetric

end

end JJMath
