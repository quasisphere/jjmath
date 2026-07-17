import JJMath.Uniformization.CoordinateVortexPair
import JJMath.Uniformization.HolomorphicVortexSeam

/-!
# Compact vortex pairs in holomorphic atlas charts

The full-plane smooth charts used for compact-support transport are obtained
by a radial reparametrization and are not holomorphic.  For cancellation at a
shared vortex endpoint we instead retain an actual chart from the Riemann
surface atlas.  The compact affine core of the planar vortex is required to
lie in the chart target; this permits extension by one outside the chart
without changing the holomorphic coordinate near either endpoint.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]

/-- The data needed to place one compact vortex pair in a genuine
holomorphic atlas chart. -/
structure AtlasVortexPairData (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X] (a b : X) where
  /-- The holomorphic surface chart. -/
  chart : OpenPartialHomeomorph X ℂ
  /-- The chart belongs to the Riemann surface atlas. -/
  chart_mem_atlas : chart ∈ atlas ℂ X
  /-- The zero endpoint is in the chart. -/
  left_mem_source : a ∈ chart.source
  /-- The pole endpoint is in the chart. -/
  right_mem_source : b ∈ chart.source
  /-- The endpoints are distinct. -/
  endpoints_ne : a ≠ b
  /-- The entire compact affine core remains in the chart image. -/
  affineCore_subset_target :
    planarVortexAffineCore (by
      intro h
      exact endpoints_ne
        (chart.injOn left_mem_source right_mem_source h)) ⊆ chart.target

/-- A genuine atlas chart carries a compact vortex pair whenever the two
endpoint coordinates are sufficiently close relative to a coordinate ball
contained in the chart target. -/
def AtlasVortexPairData.ofChartBall {a b : X}
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (ha : a ∈ e.source) (hb : b ∈ e.source) (hab : a ≠ b)
    {r : ℝ} (hball : Metric.ball (e a) r ⊆ e.target)
    (hclose : 2 * ‖e b - e a‖ < r) :
    AtlasVortexPairData X a b where
  chart := e
  chart_mem_atlas := he
  left_mem_source := ha
  right_mem_source := hb
  endpoints_ne := hab
  affineCore_subset_target := by
    let hcoord : e a ≠ e b := by
      intro h
      exact hab (e.injOn ha hb h)
    exact (planarVortexAffineCore_subset_ball_left hcoord
      (by simpa [norm_sub_rev] using hclose)).trans hball

/-- Around every point of an atlas chart there is a positive coordinate
radius such that every sufficiently close second endpoint gives valid compact
vortex-pair data in that chart. -/
theorem exists_radius_atlasVortexPairData_of_mem_source
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {a : X} (ha : a ∈ e.source) :
    ∃ r : ℝ, 0 < r ∧
      ∀ b : X, b ∈ e.source → b ≠ a → 2 * ‖e b - e a‖ < r →
        Nonempty (AtlasVortexPairData X a b) := by
  have hea_target : e a ∈ e.target := e.map_source ha
  rcases Metric.isOpen_iff.mp e.open_target (e a) hea_target with
    ⟨r, hr, hball⟩
  refine ⟨r, hr, ?_⟩
  intro b hb hba hclose
  exact ⟨AtlasVortexPairData.ofChartBall e he ha hb hba.symm hball hclose⟩

/-- Every point in a specified atlas chart is the initial endpoint of a
nontrivial compact vortex pair carried by that same chart. -/
theorem exists_atlasVortexPairData_from_chart
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (a : X) (ha : a ∈ e.source) :
    ∃ b : X, ∃ D : AtlasVortexPairData X a b, D.chart = e := by
  have heaTarget : e a ∈ e.target := e.map_source ha
  rcases Metric.isOpen_iff.mp e.open_target (e a) heaTarget with
    ⟨r, hr, hball⟩
  let z : ℂ := e a + (r / 4 : ℝ)
  have hzBall : z ∈ Metric.ball (e a) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hr4 : 0 < r / 4 := by linarith
    simp [z, abs_of_pos hr]
    linarith
  have hzTarget : z ∈ e.target := hball hzBall
  let b : X := e.symm z
  have hb : b ∈ e.source := e.map_target hzTarget
  have heb : e b = z := e.right_inv hzTarget
  have hab : a ≠ b := by
    intro hab
    have heq : e a = z := by simpa [hab] using heb
    have hre := congrArg Complex.re heq
    dsimp [z] at hre
    norm_num at hre
    linarith
  have hclose : 2 * ‖e b - e a‖ < r := by
    rw [heb]
    have hr4 : 0 < r / 4 := by linarith
    simp [z, abs_of_pos hr]
    linarith
  exact ⟨b, AtlasVortexPairData.ofChartBall e he ha hb hab hball hclose,
    rfl⟩

/-- Every point of a Riemann surface is the initial endpoint of a nontrivial
compact vortex pair carried by its atlas chart. -/
theorem exists_atlasVortexPairData_from (a : X) :
    ∃ b : X, Nonempty (AtlasVortexPairData X a b) := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ a
  have ha : a ∈ e.source := mem_chart_source ℂ a
  rcases exists_atlasVortexPairData_from_chart e
      (chart_mem_atlas ℂ a) a ha with ⟨b, D, _⟩
  exact ⟨b, ⟨D⟩⟩

/-- The source of the atlas chart carrying the vortex pair. -/
def AtlasVortexPairData.sourceOpen {a b : X}
    (D : AtlasVortexPairData X a b) : TopologicalSpace.Opens X :=
  ⟨D.chart.source, D.chart.open_source⟩

/-- The two endpoints as points of the chart source. -/
def AtlasVortexPairData.leftPoint {a b : X}
    (D : AtlasVortexPairData X a b) : D.sourceOpen :=
  ⟨a, D.left_mem_source⟩

def AtlasVortexPairData.rightPoint {a b : X}
    (D : AtlasVortexPairData X a b) : D.sourceOpen :=
  ⟨b, D.right_mem_source⟩

/-- The chart coordinates of the endpoints are distinct. -/
theorem AtlasVortexPairData.chart_values_ne {a b : X}
    (D : AtlasVortexPairData X a b) : D.chart a ≠ D.chart b := by
  intro h
  exact D.endpoints_ne
    (D.chart.injOn D.left_mem_source D.right_mem_source h)

/-- A point in the chart part of the twice-punctured surface. -/
def AtlasVortexPairData.chartPatch {a b : X}
    (D : AtlasVortexPairData X a b) :
    TopologicalSpace.Opens (coordinateVortexPairOpen a b) :=
  coordinateVortexChartPatch D.sourceOpen D.leftPoint D.rightPoint

/-- Forget the punctures and regard a chart-patch point as a point of the
chart source. -/
def AtlasVortexPairData.chartPatchToSource {a b : X}
    (D : AtlasVortexPairData X a b) (x : D.chartPatch) : D.sourceOpen :=
  coordinateVortexChartPatchToChart
    D.sourceOpen D.leftPoint D.rightPoint x

private theorem contMDiffCodRestrictOpen
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H G M N : Type*}
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [TopologicalSpace N]
    {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ F G}
    [ChartedSpace H M] [ChartedSpace G N]
    {n : WithTop ℕ∞} {f : M → N}
    (hf : ContMDiff I J n f) (V : TopologicalSpace.Opens N)
    (hmem : ∀ x, f x ∈ V) :
    ContMDiff I J n (fun x ↦ (⟨f x, hmem x⟩ : V)) := by
  classical
  intro x
  let qV : V := ⟨f x, hmem x⟩
  let retract : N → V := fun y ↦
    if hy : y ∈ V then ⟨y, hy⟩ else qV
  have hretract : ContMDiffAt J J n retract (f x) := by
    rw [← contMDiffAt_subtype_iff (U := V) (x := qV)]
    have heq : (fun y : V ↦ retract y) = id := by
      funext y
      simp [retract]
    rw [heq]
    exact contMDiffAt_id
  have hcomp := hretract.comp x (hf x)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [retract, hmem]

/-- The chart-patch point mapped to the arbitrary planar twice-punctured
model. -/
def AtlasVortexPairData.toPlanarPair {a b : X}
    (D : AtlasVortexPairData X a b) (x : D.chartPatch) :
    planarVortexPairOpenAt (D.chart a) (D.chart b) := by
  refine ⟨D.chart (x : X), ?_⟩
  constructor
  · intro h
    exact x.1.2.1 (D.chart.injOn x.2 D.left_mem_source h)
  · intro h
    exact x.1.2.2 (D.chart.injOn x.2 D.right_mem_source h)

theorem AtlasVortexPairData.contMDiff_toPlanarPair {a b : X}
    (D : AtlasVortexPairData X a b) :
    ContMDiff SurfaceRealModel (modelWithCornersSelf ℝ ℂ) ∞
      D.toPlanarPair := by
  have hchartOn : ContMDiffOn SurfaceRealModel SurfaceRealModel ∞
      D.chart D.chart.source :=
    contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas D.chart_mem_atlas)
  have hraw : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun x : D.chartPatch ↦ D.chart (x : X)) := by
    intro x
    have hval : ContMDiffAt SurfaceRealModel SurfaceRealModel ∞
        (fun y : D.chartPatch ↦ (y : X)) x :=
      (contMDiff_subtype_val.comp contMDiff_subtype_val).contMDiffAt
    exact (hchartOn.contMDiffAt
      (D.chart.open_source.mem_nhds x.2)).comp x hval
  exact contMDiffCodRestrictOpen hraw
    (planarVortexPairOpenAt (D.chart a) (D.chart b))
    (fun x ↦ (D.toPlanarPair x).2)

/-- The compact planar phase in the genuine holomorphic chart. -/
def AtlasVortexPairData.chartPhase {a b : X}
    (D : AtlasVortexPairData X a b) (x : D.chartPatch) : ℂ :=
  planarVortexCompactPhaseAt D.chart_values_ne (D.toPlanarPair x)

theorem AtlasVortexPairData.contMDiff_chartPhase {a b : X}
    (D : AtlasVortexPairData X a b) :
    ContMDiff SurfaceRealModel (modelWithCornersSelf ℝ ℂ) ∞
      D.chartPhase :=
  (contMDiff_planarVortexCompactPhaseAt D.chart_values_ne).comp
    D.contMDiff_toPlanarPair

/-- The compact support core, regarded inside the chart source. -/
def AtlasVortexPairData.core {a b : X}
    (D : AtlasVortexPairData X a b) : Set D.sourceOpen :=
  {x | D.chart (x : X) ∈ planarVortexAffineCore D.chart_values_ne}

theorem AtlasVortexPairData.core_isCompact {a b : X}
    (D : AtlasVortexPairData X a b) : IsCompact D.core := by
  let K : Set D.chart.target :=
    {z | (z : ℂ) ∈ planarVortexAffineCore D.chart_values_ne}
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff]
    have himage : ((fun z : D.chart.target ↦ (z : ℂ)) '' K) =
        planarVortexAffineCore D.chart_values_ne := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z, D.affineCore_subset_target hz⟩, hz, rfl⟩
    rw [himage]
    exact planarVortexAffineCore_isCompact D.chart_values_ne
  change IsCompact (D.chart.toHomeomorphSourceTarget ⁻¹' K)
  exact D.chart.toHomeomorphSourceTarget.isCompact_preimage.mpr hK

/-- The ambient compact support core. -/
def AtlasVortexPairData.ambientCore {a b : X}
    (D : AtlasVortexPairData X a b) : Set X :=
  smoothFormCompactCore D.sourceOpen D.core

theorem AtlasVortexPairData.ambientCore_isCompact {a b : X}
    (D : AtlasVortexPairData X a b) : IsCompact D.ambientCore :=
  smoothFormCompactCore_isCompact D.sourceOpen D.core D.core_isCompact

/-- On the affine core near either endpoint, the chart phase is the
normalized holomorphic zero--pole ratio. -/
theorem AtlasVortexPairData.chartPhase_eq_normalized_ratio_of_affine_norm_lt_two
    {a b : X} (D : AtlasVortexPairData X a b) (x : D.chartPatch)
    (hx : ‖planarVortexAffine (D.chart a) (D.chart b)
      (D.chart (x : X))‖ < 2) :
    D.chartPhase x =
      ((D.chart (x : X) - D.chart a) /
        (D.chart (x : X) - D.chart b)) /
      ‖(D.chart (x : X) - D.chart a) /
        (D.chart (x : X) - D.chart b)‖ := by
  exact planarVortexCompactPhaseAt_eq_normalized_ratio_of_affine_norm_lt_two
    D.chart_values_ne (D.toPlanarPair x) hx

/-- The exterior of the compact phase core in the twice-punctured surface. -/
def AtlasVortexPairData.exteriorPatch {a b : X}
    (D : AtlasVortexPairData X a b) :
    TopologicalSpace.Opens (coordinateVortexPairOpen a b) :=
  ⟨{x | ((x : coordinateVortexPairOpen a b) : X) ∉ D.ambientCore},
    D.ambientCore_isCompact.isClosed.isOpen_compl.preimage
      (continuous_subtype_val : Continuous
        (fun x : coordinateVortexPairOpen a b ↦ (x : X)))⟩

/-- The chart phase is one off its compact affine core. -/
theorem AtlasVortexPairData.chartPhase_eq_one_of_mem_exterior
    {a b : X} (D : AtlasVortexPairData X a b) (x : D.chartPatch)
    (hx : ((x : coordinateVortexPairOpen a b) : X) ∉ D.ambientCore) :
    D.chartPhase x = 1 := by
  let xU := D.chartPatchToSource x
  have hxcore : xU ∉ D.core := by
    intro hxK
    exact hx ⟨xU, hxK, rfl⟩
  have hnorm : 3 < ‖planarVortexAffine (D.chart a) (D.chart b)
      (D.chart (x : X))‖ :=
    three_lt_norm_planarVortexAffine_of_not_mem_core
      D.chart_values_ne hxcore
  exact planarVortexCompactPhaseAt_eq_one_of_three_le_affine_norm
    D.chart_values_ne (D.toPlanarPair x) hnorm.le

/-- Extend the compact chart phase by one to the ambient twice-punctured
surface. -/
def AtlasVortexPairData.globalPhaseFun {a b : X}
    (D : AtlasVortexPairData X a b)
    (x : coordinateVortexPairOpen a b) : ℂ := by
  classical
  exact if hx : (x : X) ∈ D.sourceOpen then D.chartPhase ⟨x, hx⟩ else 1

theorem AtlasVortexPairData.globalPhaseFun_eq_chart {a b : X}
    (D : AtlasVortexPairData X a b)
    {x : coordinateVortexPairOpen a b} (hx : (x : X) ∈ D.sourceOpen) :
    D.globalPhaseFun x = D.chartPhase ⟨x, hx⟩ := by
  simp [AtlasVortexPairData.globalPhaseFun, hx]

theorem AtlasVortexPairData.globalPhaseFun_eq_one_of_mem_exterior
    {a b : X} (D : AtlasVortexPairData X a b)
    {x : coordinateVortexPairOpen a b} (hx : x ∈ D.exteriorPatch) :
    D.globalPhaseFun x = 1 := by
  by_cases hxU : (x : X) ∈ D.sourceOpen
  · rw [D.globalPhaseFun_eq_chart hxU]
    exact D.chartPhase_eq_one_of_mem_exterior ⟨x, hxU⟩ hx
  · simp [AtlasVortexPairData.globalPhaseFun, hxU]

theorem AtlasVortexPairData.contMDiff_globalPhaseFun {a b : X}
    (D : AtlasVortexPairData X a b) :
    ContMDiff SurfaceRealModel (modelWithCornersSelf ℝ ℂ) ∞
      D.globalPhaseFun := by
  apply contMDiff_of_contMDiffOn_union_of_isOpen
  · intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    let xU : D.chartPatch := ⟨x, hx⟩
    rw [← contMDiffAt_subtype_iff (U := D.chartPatch) (x := xU)]
    have heq : (fun y : D.chartPatch ↦
        D.globalPhaseFun (y : coordinateVortexPairOpen a b)) =
        D.chartPhase := by
      funext y
      exact D.globalPhaseFun_eq_chart y.2
    rw [heq]
    exact D.contMDiff_chartPhase.contMDiffAt
  · exact contMDiff_const.contMDiffOn.congr (fun x hx ↦
      D.globalPhaseFun_eq_one_of_mem_exterior hx)
  · ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hxU : (x : X) ∈ D.sourceOpen
    · exact Or.inl hxU
    · right
      intro hxcore
      exact hxU (smoothFormCompactCore_subset D.sourceOpen D.core hxcore)
  · exact D.chartPatch.isOpen
  · exact D.exteriorPatch.isOpen

/-- The compact atlas vortex pair as a bundled smooth unit phase. -/
def AtlasVortexPairData.globalPhase {a b : X}
    (D : AtlasVortexPairData X a b) :
    ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      (coordinateVortexPairOpen a b) ℂ ∞ where
  val := D.globalPhaseFun
  property := D.contMDiff_globalPhaseFun

theorem AtlasVortexPairData.norm_globalPhase {a b : X}
    (D : AtlasVortexPairData X a b)
    (x : coordinateVortexPairOpen a b) : ‖D.globalPhase x‖ = 1 := by
  by_cases hxU : (x : X) ∈ D.sourceOpen
  · rw [show D.globalPhase x = D.chartPhase ⟨x, hxU⟩ by
      exact D.globalPhaseFun_eq_chart hxU]
    exact norm_planarVortexCompactPhaseAt D.chart_values_ne
      (D.toPlanarPair ⟨x, hxU⟩)
  · change ‖D.globalPhaseFun x‖ = 1
    simp [AtlasVortexPairData.globalPhaseFun, hxU]

/-- The compact atlas vortex pair, viewed as the circle primitive of its
logarithmic one-form. -/
def AtlasVortexPairData.circlePrimitive {a b : X}
    (D : AtlasVortexPairData X a b) :
    JJMath.Manifold.SmoothCirclePrimitive SurfaceRealModel
      (smoothUnitPhaseOneForm SurfaceRealModel D.globalPhase
        D.norm_globalPhase) :=
  smoothUnitPhaseCirclePrimitive SurfaceRealModel D.globalPhase
    D.norm_globalPhase

/-! ## Cancellation of consecutive atlas vortex pairs -/

/-- Consecutive compact vortex pairs in holomorphic atlas charts have a
smooth unit product across their shared endpoint.  Thus the apparent pole of
the first phase and zero of the second phase cancel even when the two pairs
use different coordinates. -/
theorem AtlasVortexPairData.consecutive_product_local_extension
    {a q b : X} (D₁ : AtlasVortexPairData X a q)
    (D₂ : AtlasVortexPairData X q b) :
    ∃ U : TopologicalSpace.Opens X, q ∈ U ∧ ∃ P : X → ℂ,
      ContMDiffOn SurfaceRealModel (modelWithCornersSelf ℝ ℂ) ∞ P U ∧
      (∀ x ∈ U, ‖P x‖ = 1) ∧
      ∀ (x : X) (_hxU : x ∈ U) (hxa : x ≠ a) (hxq : x ≠ q)
          (hxb : x ≠ b),
        D₁.globalPhase ⟨x, ⟨hxa, hxq⟩⟩ *
          D₂.globalPhase ⟨x, ⟨hxq, hxb⟩⟩ = P x := by
  let F : ℂ → ℂ := fun z ↦ D₁.chart (D₂.chart.symm z)
  let z₀ : ℂ := D₂.chart q
  let α : ℂ := D₁.chart a
  let β : ℂ := D₂.chart b
  have hz₀_target : z₀ ∈ D₂.chart.target :=
    D₂.chart.map_source D₂.left_mem_source
  have hz₀_source₁ : D₂.chart.symm z₀ ∈ D₁.chart.source := by
    simpa [z₀, D₂.chart.left_inv D₂.left_mem_source] using
      D₁.right_mem_source
  have hF_an : AnalyticAt ℂ F z₀ := by
    exact chartTransition_analyticAt D₂.chart D₂.chart_mem_atlas
      D₁.chart D₁.chart_mem_atlas hz₀_target hz₀_source₁
  let χ : PointedSurfaceCoordinate X q :=
    { chart := D₁.chart
      chart_mem_atlas := D₁.chart_mem_atlas
      base_mem_source := D₁.right_mem_source }
  let ψ : PointedSurfaceCoordinate X q :=
    { chart := D₂.chart
      chart_mem_atlas := D₂.chart_mem_atlas
      base_mem_source := D₂.left_mem_source }
  have hderiv : deriv F z₀ ≠ 0 := by
    simpa [F, z₀, χ, ψ] using
      pointedCoordinate_transition_deriv_ne_zero X χ ψ
  have hFz₀ : F z₀ = D₁.chart q := by
    simp [F, z₀, D₂.chart.left_inv D₂.left_mem_source]
  have hα : F z₀ ≠ α := by
    rw [hFz₀]
    exact D₁.chart_values_ne.symm
  have hβ : z₀ ≠ β := D₂.chart_values_ne
  rcases holomorphicVortexSeamPhase_local hF_an hderiv hα hβ with
    ⟨δ, hδ, hseam_smooth, hseam_norm, hseam_eq⟩
  let A₁ : Set ℂ := {z | ‖planarVortexAffine
    (D₁.chart a) (D₁.chart q) z‖ < 2}
  let A₂ : Set ℂ := {z | ‖planarVortexAffine
    (D₂.chart q) (D₂.chart b) z‖ < 2}
  have hA₁_open : IsOpen A₁ := by
    dsimp [A₁]
    apply isOpen_lt _ continuous_const
    unfold planarVortexAffine
    fun_prop
  have hA₂_open : IsOpen A₂ := by
    dsimp [A₂]
    apply isOpen_lt _ continuous_const
    unfold planarVortexAffine
    fun_prop
  let Uset : Set X :=
    (D₁.chart.source ∩ D₁.chart ⁻¹' A₁) ∩
      ((D₂.chart.source ∩ D₂.chart ⁻¹' A₂) ∩
        ((D₂.chart.source ∩ D₂.chart ⁻¹' Metric.ball z₀ δ) ∩
          ({x : X | x ≠ a} ∩ {x : X | x ≠ b})))
  have hU_open : IsOpen Uset := by
    exact (D₁.chart.isOpen_inter_preimage hA₁_open).inter
      ((D₂.chart.isOpen_inter_preimage hA₂_open).inter
        ((D₂.chart.isOpen_inter_preimage Metric.isOpen_ball).inter
          (isOpen_ne.inter isOpen_ne)))
  let U : TopologicalSpace.Opens X := ⟨Uset, hU_open⟩
  have hqU : q ∈ U := by
    refine ⟨⟨D₁.right_mem_source, ?_⟩,
      ⟨⟨D₂.left_mem_source, ?_⟩,
        ⟨⟨D₂.left_mem_source, ?_⟩,
          D₁.endpoints_ne.symm, D₂.endpoints_ne⟩⟩⟩
    · dsimp [A₁]
      rw [planarVortexAffine_apply_right D₁.chart_values_ne]
      norm_num
    · dsimp [A₂]
      rw [planarVortexAffine_apply_left D₂.chart_values_ne]
      norm_num
    · exact Metric.mem_ball_self hδ
  let P : X → ℂ := fun x ↦
    holomorphicVortexSeamPhase F z₀ α β (D₂.chart x)
  have hchart₂ : ContMDiffOn SurfaceRealModel SurfaceRealModel ∞
      D₂.chart D₂.chart.source :=
    contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas D₂.chart_mem_atlas)
  have hseamM : ContMDiffOn (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞
      (holomorphicVortexSeamPhase F z₀ α β) (Metric.ball z₀ δ) :=
    contMDiffOn_iff_contDiffOn.mpr hseam_smooth
  have hP_smooth : ContMDiffOn SurfaceRealModel
      (modelWithCornersSelf ℝ ℂ) ∞ P U := by
    have hcomp := hseamM.comp (hchart₂.mono (by
      intro (x : X) (hx : x ∈ U)
      exact hx.2.1.1)) (by
        intro (x : X) (hx : x ∈ U)
        exact hx.2.2.1.2)
    simpa [P, Function.comp_def] using hcomp
  have hP_norm : ∀ x ∈ U, ‖P x‖ = 1 := by
    intro x hx
    exact hseam_norm (D₂.chart x) hx.2.2.1.2
  refine ⟨U, hqU, P, hP_smooth, hP_norm, ?_⟩
  intro x hxU hxa hxq hxb
  let x₁ : D₁.chartPatch :=
    ⟨⟨x, hxa, hxq⟩, hxU.1.1⟩
  let x₂ : D₂.chartPatch :=
    ⟨⟨x, hxq, hxb⟩, hxU.2.1.1⟩
  have hz_ne : D₂.chart x ≠ z₀ := by
    intro h
    exact hxq (D₂.chart.injOn hxU.2.1.1 D₂.left_mem_source (by
      simpa [z₀] using h))
  have hraw₁ : D₁.chartPhase x₁ =
      ((D₁.chart x - D₁.chart a) / (D₁.chart x - D₁.chart q)) /
        ‖(D₁.chart x - D₁.chart a) /
          (D₁.chart x - D₁.chart q)‖ := by
    exact D₁.chartPhase_eq_normalized_ratio_of_affine_norm_lt_two x₁
      hxU.1.2
  have hraw₂ : D₂.chartPhase x₂ =
      ((D₂.chart x - D₂.chart q) / (D₂.chart x - D₂.chart b)) /
        ‖(D₂.chart x - D₂.chart q) /
          (D₂.chart x - D₂.chart b)‖ := by
    exact D₂.chartPhase_eq_normalized_ratio_of_affine_norm_lt_two x₂
      hxU.2.1.2
  change D₁.globalPhase ⟨x, ⟨hxa, hxq⟩⟩ *
      D₂.globalPhase ⟨x, ⟨hxq, hxb⟩⟩ = P x
  rw [show D₁.globalPhase
        (⟨x, ⟨hxa, hxq⟩⟩ : coordinateVortexPairOpen a q) =
      D₁.chartPhase x₁ by
        exact D₁.globalPhaseFun_eq_chart
          (show x ∈ D₁.sourceOpen from hxU.1.1),
    show D₂.globalPhase
        (⟨x, ⟨hxq, hxb⟩⟩ : coordinateVortexPairOpen q b) =
      D₂.chartPhase x₂ by
        exact D₂.globalPhaseFun_eq_chart
          (show x ∈ D₂.sourceOpen from hxU.2.1.1),
    hraw₁, hraw₂]
  have hseam := hseam_eq (D₂.chart x) hxU.2.2.1.2 hz_ne
  simpa [P, F, z₀, α, β,
    D₂.chart.left_inv hxU.2.1.1,
    D₂.chart.left_inv D₂.left_mem_source] using hseam

/-- Two consecutive compact atlas vortices glue to one smooth unit phase on
the surface with only their two outer endpoints removed. -/
theorem AtlasVortexPairData.exists_combinedPhase
    {a q b : X} (D₁ : AtlasVortexPairData X a q)
    (D₂ : AtlasVortexPairData X q b) :
    ∃ Q : ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
        (coordinateVortexPairOpen a b) ℂ ∞,
      (∀ x : coordinateVortexPairOpen a b, ‖Q x‖ = 1) ∧
      ∀ (x : coordinateVortexPairOpen a b) (hxq : (x : X) ≠ q),
        Q x = D₁.globalPhase ⟨(x : X), ⟨x.2.1, hxq⟩⟩ *
          D₂.globalPhase ⟨(x : X), ⟨hxq, x.2.2⟩⟩ := by
  rcases D₁.consecutive_product_local_extension D₂ with
    ⟨U, hqU, P, hP_smooth, hP_norm, hproduct⟩
  let A : TopologicalSpace.Opens (coordinateVortexPairOpen a b) :=
    ⟨{x | (x : X) ∈ U}, U.isOpen.preimage
      (continuous_subtype_val : Continuous
        (fun x : coordinateVortexPairOpen a b ↦ (x : X)))⟩
  let B : TopologicalSpace.Opens (coordinateVortexPairOpen a b) :=
    ⟨{x | (x : X) ≠ q}, isOpen_ne.preimage
      (continuous_subtype_val : Continuous
        (fun x : coordinateVortexPairOpen a b ↦ (x : X)))⟩
  let Qfun : coordinateVortexPairOpen a b → ℂ := fun x ↦ by
    classical
    exact if hxq : (x : X) ≠ q then
      D₁.globalPhase ⟨(x : X), ⟨x.2.1, hxq⟩⟩ *
        D₂.globalPhase ⟨(x : X), ⟨hxq, x.2.2⟩⟩
    else P x
  have hA_smooth : ContMDiff SurfaceRealModel
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun x : A ↦ P (x : X)) := by
    intro x
    have hval : ContMDiffAt SurfaceRealModel SurfaceRealModel ∞
        (fun y : A ↦ (y : X)) x :=
      (contMDiff_subtype_val.comp contMDiff_subtype_val).contMDiffAt
    exact (hP_smooth.contMDiffAt
      (U.isOpen.mem_nhds x.2)).comp x hval
  have hBto₁ : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun x : B ↦
        (⟨(x : X), ⟨x.1.2.1, x.2⟩⟩ : coordinateVortexPairOpen a q)) := by
    have hval : ContMDiff SurfaceRealModel SurfaceRealModel ∞
        (fun x : B ↦ (x : X)) :=
      contMDiff_subtype_val.comp contMDiff_subtype_val
    exact contMDiffCodRestrictOpen hval (coordinateVortexPairOpen a q)
      (fun x ↦ ⟨x.1.2.1, x.2⟩)
  have hBto₂ : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun x : B ↦
        (⟨(x : X), ⟨x.2, x.1.2.2⟩⟩ : coordinateVortexPairOpen q b)) := by
    have hval : ContMDiff SurfaceRealModel SurfaceRealModel ∞
        (fun x : B ↦ (x : X)) :=
      contMDiff_subtype_val.comp contMDiff_subtype_val
    exact contMDiffCodRestrictOpen hval (coordinateVortexPairOpen q b)
      (fun x ↦ ⟨x.2, x.1.2.2⟩)
  have hB_smooth : ContMDiff SurfaceRealModel
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun x : B ↦
        D₁.globalPhase
            (⟨(x : X), ⟨x.1.2.1, x.2⟩⟩ : coordinateVortexPairOpen a q) *
          D₂.globalPhase
            (⟨(x : X), ⟨x.2, x.1.2.2⟩⟩ : coordinateVortexPairOpen q b)) :=
    ContDiff.comp_contMDiff (by
      fun_prop : ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 * z.2))
      ((D₁.globalPhase.contMDiff.comp hBto₁).prodMk_space
        (D₂.globalPhase.contMDiff.comp hBto₂))
  have hQ_smooth : ContMDiff SurfaceRealModel
      (modelWithCornersSelf ℝ ℂ) ∞ Qfun := by
    apply contMDiff_of_contMDiffOn_union_of_isOpen
    · intro x hx
      apply ContMDiffAt.contMDiffWithinAt
      let xA : A := ⟨x, hx⟩
      rw [← contMDiffAt_subtype_iff (U := A) (x := xA)]
      have heq : (fun y : A ↦ Qfun (y : coordinateVortexPairOpen a b)) =
          fun y : A ↦ P (y : X) := by
        funext y
        by_cases hyq : (y : X) ≠ q
        · rw [show Qfun (y : coordinateVortexPairOpen a b) =
              D₁.globalPhase ⟨(y : X), ⟨y.1.2.1, hyq⟩⟩ *
                D₂.globalPhase ⟨(y : X), ⟨hyq, y.1.2.2⟩⟩ by
              simp [Qfun, hyq]]
          exact hproduct (y : X) y.2 y.1.2.1 hyq y.1.2.2
        · simp [Qfun, hyq]
      rw [heq]
      exact hA_smooth.contMDiffAt
    · intro x hx
      apply ContMDiffAt.contMDiffWithinAt
      let xB : B := ⟨x, hx⟩
      rw [← contMDiffAt_subtype_iff (U := B) (x := xB)]
      have heq : (fun y : B ↦ Qfun (y : coordinateVortexPairOpen a b)) =
          fun y : B ↦
            D₁.globalPhase
                (⟨(y : X), ⟨y.1.2.1, y.2⟩⟩ : coordinateVortexPairOpen a q) *
              D₂.globalPhase
                (⟨(y : X), ⟨y.2, y.1.2.2⟩⟩ : coordinateVortexPairOpen q b) := by
        funext y
        dsimp [Qfun]
        have hyq : (y : X) ≠ q := y.2
        rw [dif_pos hyq]
      rw [heq]
      exact hB_smooth.contMDiffAt
    · ext x
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      by_cases hxq : (x : X) ≠ q
      · exact Or.inr hxq
      · left
        change (x : X) ∈ U
        simpa [not_ne_iff.mp hxq] using hqU
    · exact A.isOpen
    · exact B.isOpen
  let Q : ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      (coordinateVortexPairOpen a b) ℂ ∞ := ⟨Qfun, hQ_smooth⟩
  have hQ_norm : ∀ x : coordinateVortexPairOpen a b, ‖Q x‖ = 1 := by
    intro x
    by_cases hxq : (x : X) ≠ q
    · change ‖Qfun x‖ = 1
      rw [show Qfun x =
          D₁.globalPhase ⟨(x : X), ⟨x.2.1, hxq⟩⟩ *
            D₂.globalPhase ⟨(x : X), ⟨hxq, x.2.2⟩⟩ by
          simp [Qfun, hxq], norm_mul,
        D₁.norm_globalPhase, D₂.norm_globalPhase, one_mul]
    · have hxq' : (x : X) = q := not_ne_iff.mp hxq
      change ‖Qfun x‖ = 1
      rw [show Qfun x = P x by simp [Qfun, hxq]]
      exact hP_norm (x : X) (by simpa [hxq'] using hqU)
  refine ⟨Q, hQ_norm, ?_⟩
  intro x hxq
  change Qfun x = _
  simp [Qfun, hxq]

end

end JJMath.Uniformization
