import JJMath.Uniformization.PlanarVortexPair
import JJMath.Uniformization.CompactSupportTransfer
import JJMath.Uniformization.SmoothUnitPhaseCirclePrimitive

/-!
# Compactly supported vortex pairs in a surface coordinate chart

The planar zero--pole phase is transported through a full-plane surface
chart.  Its nonconstant locus has compact closure in that chart, so extending
the phase by one gives a smooth unit phase on the ambient surface with only
the two marked points removed.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [IsManifold SurfaceRealModel ∞ X] [T2Space X]

/-- The surface with two marked points removed. -/
def coordinateVortexPairOpen (a b : X) : TopologicalSpace.Opens X :=
  ⟨{x : X | x ≠ a ∧ x ≠ b}, isOpen_ne.inter isOpen_ne⟩

/-- The part of a twice-punctured surface lying in a chosen coordinate
chart. -/
def coordinateVortexChartPatch
    (U : TopologicalSpace.Opens X) (a b : U) :
    TopologicalSpace.Opens (coordinateVortexPairOpen (a : X) (b : X)) :=
  ⟨{x | (x : X) ∈ U}, U.isOpen.preimage
    (continuous_subtype_val : Continuous
      (fun x : coordinateVortexPairOpen (a : X) (b : X) ↦ (x : X)))⟩

/-- A chart-patch point, regarded as a point of the original chart. -/
def coordinateVortexChartPatchToChart
    (U : TopologicalSpace.Opens X) (a b : U)
    (x : coordinateVortexChartPatch U a b) : U :=
  ⟨((x : coordinateVortexPairOpen (a : X) (b : X)) : X), x.2⟩

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

theorem contMDiff_coordinateVortexChartPatchToChart
    (U : TopologicalSpace.Opens X) (a b : U) :
    ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (coordinateVortexChartPatchToChart U a b) := by
  have hambient : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun x : coordinateVortexChartPatch U a b ↦
        ((x : coordinateVortexPairOpen (a : X) (b : X)) : X)) :=
    contMDiff_subtype_val.comp contMDiff_subtype_val
  exact contMDiffCodRestrictOpen hambient U (fun x ↦ x.2)

/-- Distinct chart points have distinct complex coordinates. -/
theorem coordinateVortex_chart_values_ne
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X)) :
    (((phi a : complexPlanarModelOpen) : ℂ)) ≠
      (((phi b : complexPlanarModelOpen) : ℂ)) := by
  intro h
  have hphi : phi a = phi b := Subtype.ext h
  exact hab (congrArg (fun x : U ↦ (x : X)) (phi.injective hphi))

/-- The chart patch mapped to the arbitrary planar twice-punctured model. -/
def coordinateVortexChartToPlanarPair
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (_hab : (a : X) ≠ (b : X))
    (x : coordinateVortexChartPatch U a b) :
    planarVortexPairOpenAt
      (((phi a : complexPlanarModelOpen) : ℂ))
      (((phi b : complexPlanarModelOpen) : ℂ)) := by
  let xU := coordinateVortexChartPatchToChart U a b x
  refine ⟨((phi xU : complexPlanarModelOpen) : ℂ), ?_⟩
  constructor
  · intro h
    have hphi : phi xU = phi a := Subtype.ext h
    have hxa : xU = a := phi.injective hphi
    exact x.1.2.1 (congrArg (fun y : U ↦ (y : X)) hxa)
  · intro h
    have hphi : phi xU = phi b := Subtype.ext h
    have hxb : xU = b := phi.injective hphi
    exact x.1.2.2 (congrArg (fun y : U ↦ (y : X)) hxb)

theorem contMDiff_coordinateVortexChartToPlanarPair
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X)) :
    ContMDiff SurfaceRealModel (modelWithCornersSelf ℝ ℂ) ∞
      (coordinateVortexChartToPlanarPair U phi a b hab) := by
  have hraw : ContMDiff SurfaceRealModel (modelWithCornersSelf ℝ ℂ) ∞
      (fun x : coordinateVortexChartPatch U a b ↦
        (((phi (coordinateVortexChartPatchToChart U a b x) :
          complexPlanarModelOpen) : ℂ))) :=
    contMDiff_subtype_val.comp
      (phi.contMDiff.comp
        (contMDiff_coordinateVortexChartPatchToChart U a b))
  exact contMDiffCodRestrictOpen hraw
    (planarVortexPairOpenAt
      (((phi a : complexPlanarModelOpen) : ℂ))
      (((phi b : complexPlanarModelOpen) : ℂ)))
    (fun x ↦ (coordinateVortexChartToPlanarPair U phi a b hab x).2)

/-- The compactly supported vortex-pair phase on the punctured chart. -/
def coordinateVortexChartPhase
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X))
    (x : coordinateVortexChartPatch U a b) : ℂ :=
  planarVortexCompactPhaseAt (coordinateVortex_chart_values_ne U phi a b hab)
    (coordinateVortexChartToPlanarPair U phi a b hab x)

theorem contMDiff_coordinateVortexChartPhase
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X)) :
    ContMDiff SurfaceRealModel (modelWithCornersSelf ℝ ℂ) ∞
      (coordinateVortexChartPhase U phi a b hab) :=
  (contMDiff_planarVortexCompactPhaseAt
    (coordinateVortex_chart_values_ne U phi a b hab)).comp
      (contMDiff_coordinateVortexChartToPlanarPair U phi a b hab)

/-- The preimage in the chart of the affine core supporting the nonconstant
part of the phase. -/
def coordinateVortexCore
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X)) : Set U :=
  {x | (((phi x : complexPlanarModelOpen) : ℂ)) ∈
    planarVortexAffineCore (coordinateVortex_chart_values_ne U phi a b hab)}

theorem coordinateVortexCore_isCompact
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X)) :
    IsCompact (coordinateVortexCore U phi a b hab) := by
  let K : Set complexPlanarModelOpen :=
    {z | (z : ℂ) ∈
      planarVortexAffineCore (coordinateVortex_chart_values_ne U phi a b hab)}
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff]
    have himage : ((fun z : complexPlanarModelOpen ↦ (z : ℂ)) '' K) =
        planarVortexAffineCore
          (coordinateVortex_chart_values_ne U phi a b hab) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z, Set.mem_univ z⟩, hz, rfl⟩
    rw [himage]
    exact planarVortexAffineCore_isCompact
      (coordinateVortex_chart_values_ne U phi a b hab)
  change IsCompact (phi ⁻¹' K)
  exact phi.toHomeomorph.isCompact_preimage.mpr hK

/-- The ambient compact support core of the coordinate vortex pair. -/
def coordinateVortexAmbientCore
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X)) : Set X :=
  smoothFormCompactCore U (coordinateVortexCore U phi a b hab)

theorem coordinateVortexAmbientCore_isCompact
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X)) :
    IsCompact (coordinateVortexAmbientCore U phi a b hab) :=
  smoothFormCompactCore_isCompact U _
    (coordinateVortexCore_isCompact U phi a b hab)

/-- The exterior of the compact phase core, inside the twice-punctured
surface. -/
def coordinateVortexExteriorPatch
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X)) :
    TopologicalSpace.Opens (coordinateVortexPairOpen (a : X) (b : X)) :=
  ⟨{x | ((x : coordinateVortexPairOpen (a : X) (b : X)) : X) ∉
      coordinateVortexAmbientCore U phi a b hab},
    (coordinateVortexAmbientCore_isCompact U phi a b hab).isClosed.isOpen_compl.preimage
      (continuous_subtype_val : Continuous
        (fun x : coordinateVortexPairOpen (a : X) (b : X) ↦ (x : X)))⟩

/-- The chart phase is one off its compact core. -/
theorem coordinateVortexChartPhase_eq_one_of_mem_exterior
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X))
    (x : coordinateVortexChartPatch U a b)
    (hx : ((x : coordinateVortexPairOpen (a : X) (b : X)) : X) ∉
      coordinateVortexAmbientCore U phi a b hab) :
    coordinateVortexChartPhase U phi a b hab x = 1 := by
  let xU := coordinateVortexChartPatchToChart U a b x
  have hxcore : xU ∉ coordinateVortexCore U phi a b hab := by
    intro hxK
    exact hx ⟨xU, hxK, rfl⟩
  have hnorm : 3 < ‖planarVortexAffine
      (((phi a : complexPlanarModelOpen) : ℂ))
      (((phi b : complexPlanarModelOpen) : ℂ))
      (((phi xU : complexPlanarModelOpen) : ℂ))‖ :=
    three_lt_norm_planarVortexAffine_of_not_mem_core
      (coordinateVortex_chart_values_ne U phi a b hab) hxcore
  exact planarVortexCompactPhaseAt_eq_one_of_three_le_affine_norm
    (coordinateVortex_chart_values_ne U phi a b hab)
    (coordinateVortexChartToPlanarPair U phi a b hab x) hnorm.le

/-- Extend the compactly supported chart phase by one to the ambient
twice-punctured surface. -/
def coordinateVortexGlobalPhaseFun
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X))
    (x : coordinateVortexPairOpen (a : X) (b : X)) : ℂ := by
  classical
  exact if hx : (x : X) ∈ U then
    coordinateVortexChartPhase U phi a b hab ⟨x, hx⟩
  else 1

theorem coordinateVortexGlobalPhaseFun_eq_chart
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X))
    {x : coordinateVortexPairOpen (a : X) (b : X)} (hx : (x : X) ∈ U) :
    coordinateVortexGlobalPhaseFun U phi a b hab x =
      coordinateVortexChartPhase U phi a b hab ⟨x, hx⟩ := by
  simp [coordinateVortexGlobalPhaseFun, hx]

theorem coordinateVortexGlobalPhaseFun_eq_one_of_mem_exterior
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X))
    {x : coordinateVortexPairOpen (a : X) (b : X)}
    (hx : x ∈ coordinateVortexExteriorPatch U phi a b hab) :
    coordinateVortexGlobalPhaseFun U phi a b hab x = 1 := by
  by_cases hxU : (x : X) ∈ U
  · rw [coordinateVortexGlobalPhaseFun_eq_chart U phi a b hab hxU]
    exact coordinateVortexChartPhase_eq_one_of_mem_exterior
      U phi a b hab ⟨x, hxU⟩ hx
  · simp [coordinateVortexGlobalPhaseFun, hxU]

theorem contMDiff_coordinateVortexGlobalPhaseFun
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X)) :
    ContMDiff SurfaceRealModel (modelWithCornersSelf ℝ ℂ) ∞
      (coordinateVortexGlobalPhaseFun U phi a b hab) := by
  apply contMDiff_of_contMDiffOn_union_of_isOpen
  · intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    let xU : coordinateVortexChartPatch U a b := ⟨x, hx⟩
    rw [← contMDiffAt_subtype_iff
      (U := coordinateVortexChartPatch U a b) (x := xU)]
    have heq : (fun y : coordinateVortexChartPatch U a b ↦
        coordinateVortexGlobalPhaseFun U phi a b hab
          (y : coordinateVortexPairOpen (a : X) (b : X))) =
        coordinateVortexChartPhase U phi a b hab := by
      funext y
      exact coordinateVortexGlobalPhaseFun_eq_chart U phi a b hab y.2
    rw [heq]
    exact (contMDiff_coordinateVortexChartPhase U phi a b hab).contMDiffAt
  · exact contMDiff_const.contMDiffOn.congr (fun x hx ↦
      coordinateVortexGlobalPhaseFun_eq_one_of_mem_exterior
        U phi a b hab hx)
  · ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hxU : (x : X) ∈ U
    · exact Or.inl hxU
    · right
      intro hxcore
      exact hxU (smoothFormCompactCore_subset U _ hxcore)
  · exact (coordinateVortexChartPatch U a b).isOpen
  · exact (coordinateVortexExteriorPatch U phi a b hab).isOpen

/-- The global compactly supported vortex-pair phase, bundled as a smooth
map. -/
def coordinateVortexGlobalPhase
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X)) :
    ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      (coordinateVortexPairOpen (a : X) (b : X)) ℂ ∞ where
  val := coordinateVortexGlobalPhaseFun U phi a b hab
  property := contMDiff_coordinateVortexGlobalPhaseFun U phi a b hab

theorem norm_coordinateVortexGlobalPhase
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X))
    (x : coordinateVortexPairOpen (a : X) (b : X)) :
    ‖coordinateVortexGlobalPhase U phi a b hab x‖ = 1 := by
  by_cases hxU : (x : X) ∈ U
  · rw [show coordinateVortexGlobalPhase U phi a b hab x =
        coordinateVortexChartPhase U phi a b hab ⟨x, hxU⟩ by
      exact coordinateVortexGlobalPhaseFun_eq_chart U phi a b hab hxU]
    exact norm_planarVortexCompactPhaseAt
      (coordinateVortex_chart_values_ne U phi a b hab)
      (coordinateVortexChartToPlanarPair U phi a b hab ⟨x, hxU⟩)
  · change ‖coordinateVortexGlobalPhaseFun U phi a b hab x‖ = 1
    simp [coordinateVortexGlobalPhaseFun, hxU]

/-- The compactly supported coordinate vortex pair, regarded as the circle
primitive of its logarithmic one-form. -/
def coordinateVortexGlobalCirclePrimitive
    (U : TopologicalSpace.Opens X)
    (phi : U ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
    (a b : U) (hab : (a : X) ≠ (b : X)) :
    SmoothCirclePrimitive SurfaceRealModel
      (smoothUnitPhaseOneForm SurfaceRealModel
        (coordinateVortexGlobalPhase U phi a b hab)
        (norm_coordinateVortexGlobalPhase U phi a b hab)) :=
  smoothUnitPhaseCirclePrimitive SurfaceRealModel
    (coordinateVortexGlobalPhase U phi a b hab)
    (norm_coordinateVortexGlobalPhase U phi a b hab)

end

end JJMath.Uniformization
