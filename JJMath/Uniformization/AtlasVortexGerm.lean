import JJMath.Uniformization.AtlasVortexPair
import JJMath.Uniformization.PlanarVortexGerm

/-!
# The radial germ of an atlas vortex

The planar factorization of a compact vortex pulls back through its genuine
holomorphic surface chart.  On the resulting punctured neighborhood, the
global atlas-vortex phase represents the radial angular form up to an exact
one-form.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]

private theorem contMDiffCodRestrictOpen'
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

/-- The unpunctured planar coordinate neighborhood whose punctured part is
the left radial germ. -/
def AtlasVortexPairData.leftGermCoordinateOpen {a b : X}
    (D : AtlasVortexPairData X a b) : TopologicalSpace.Opens ℂ := by
  let f : ℂ → ℂ := fun z ↦
    planarVortexAffine (D.chart a) (D.chart b) z
  let g : ℂ → ℂ := fun z ↦
    planarVortexNormalizedDenominator (D.chart a) (D.chart b) z
  have hf : Continuous f := by
    dsimp [f, planarVortexAffine]
    fun_prop
  have hg : Continuous g := by
    dsimp [g, planarVortexNormalizedDenominator]
    fun_prop
  exact
    ⟨{z | ‖f z‖ < 2 ∧ g z ∈ Complex.slitPlane},
      (isOpen_lt (continuous_norm.comp hf) continuous_const).inter
        (Complex.isOpen_slitPlane.preimage hg)⟩

/-- An ambient open neighborhood of the zero endpoint whose deletion of the
zero endpoint maps to the left radial germ. -/
def AtlasVortexPairData.leftGermNeighborhood {a b : X}
    (D : AtlasVortexPairData X a b) : TopologicalSpace.Opens X :=
  ⟨D.chart.source ∩ D.chart ⁻¹' D.leftGermCoordinateOpen,
      D.chart.isOpen_inter_preimage D.leftGermCoordinateOpen.isOpen⟩ ⊓
    ⟨{x | x ≠ b}, isOpen_ne⟩

theorem AtlasVortexPairData.left_mem_leftGermNeighborhood {a b : X}
    (D : AtlasVortexPairData X a b) : a ∈ D.leftGermNeighborhood := by
  refine ⟨⟨D.left_mem_source, ?_⟩, D.endpoints_ne⟩
  constructor
  · change ‖planarVortexAffine (D.chart a) (D.chart b) (D.chart a)‖ < 2
    rw [planarVortexAffine_apply_left D.chart_values_ne]
    norm_num
  · change planarVortexNormalizedDenominator
      (D.chart a) (D.chart b) (D.chart a) ∈ Complex.slitPlane
    rw [planarVortexNormalizedDenominator_left D.chart_values_ne]
    exact Complex.one_mem_slitPlane

/-- The part of the atlas chart on which the planar vortex is in its left
radial logarithmic germ. -/
def AtlasVortexPairData.leftGerm {a b : X}
    (D : AtlasVortexPairData X a b) :
    TopologicalSpace.Opens D.chartPatch :=
  ⟨{x | D.toPlanarPair x ∈
      planarVortexLeftGermOpen D.chart_values_ne},
    (planarVortexLeftGermOpen D.chart_values_ne).isOpen.preimage
      D.contMDiff_toPlanarPair.continuous⟩

/-- A nonzero point of the ambient left-germ neighborhood determines a point
of the punctured atlas left germ. -/
def AtlasVortexPairData.toLeftGermOfMemNeighborhood {a b : X}
    (D : AtlasVortexPairData X a b) (x : X)
    (hx : x ∈ D.leftGermNeighborhood) (hxa : x ≠ a) : D.leftGerm :=
  ⟨⟨⟨x, hxa, hx.2⟩, hx.1.1⟩, hx.1.2⟩

/-- The surface left germ mapped into the corresponding planar left germ. -/
def AtlasVortexPairData.leftGermToPlanar {a b : X}
    (D : AtlasVortexPairData X a b)
    (x : D.leftGerm) : planarVortexLeftGermOpen D.chart_values_ne :=
  ⟨D.toPlanarPair x.1, x.2⟩

theorem AtlasVortexPairData.contMDiff_leftGermToPlanar {a b : X}
    (D : AtlasVortexPairData X a b) :
    ContMDiff SurfaceRealModel (modelWithCornersSelf ℝ ℂ) ∞
      D.leftGermToPlanar := by
  exact contMDiffCodRestrictOpen'
    (D.contMDiff_toPlanarPair.comp contMDiff_subtype_val)
    (planarVortexLeftGermOpen D.chart_values_ne) (fun x ↦ x.2)

/-- The surface left germ as a bundled map to the planar left germ. -/
def AtlasVortexPairData.leftGermToPlanarMap {a b : X}
    (D : AtlasVortexPairData X a b) :
    ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      D.leftGerm (planarVortexLeftGermOpen D.chart_values_ne) ∞ where
  val := D.leftGermToPlanar
  property := D.contMDiff_leftGermToPlanar

/-- The global compact atlas-vortex phase restricted to the left germ. -/
def AtlasVortexPairData.leftGermGlobalPhaseMap {a b : X}
    (D : AtlasVortexPairData X a b) :
    ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      D.leftGerm ℂ ∞ where
  val := fun x ↦ D.globalPhase (x.1 : coordinateVortexPairOpen a b)
  property := D.globalPhase.contMDiff.comp
    (contMDiff_subtype_val.comp contMDiff_subtype_val)

/-- The planar compact phase pulled back to the surface left germ. -/
def AtlasVortexPairData.leftGermCompactPhaseMap {a b : X}
    (D : AtlasVortexPairData X a b) :
    ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      D.leftGerm ℂ ∞ :=
  (planarVortexLeftGermCompactPhaseMap D.chart_values_ne).comp
    D.leftGermToPlanarMap

theorem AtlasVortexPairData.leftGermGlobalPhase_eq_compact
    {a b : X} (D : AtlasVortexPairData X a b) (x : D.leftGerm) :
    D.leftGermGlobalPhaseMap x = D.leftGermCompactPhaseMap x := by
  change D.globalPhase (x.1 : coordinateVortexPairOpen a b) =
    planarVortexCompactPhaseAt D.chart_values_ne (D.toPlanarPair x.1)
  rw [show D.globalPhase (x.1 : coordinateVortexPairOpen a b) =
      D.chartPhase x.1 from D.globalPhaseFun_eq_chart x.1.2]
  rfl

theorem AtlasVortexPairData.norm_leftGermGlobalPhaseMap
    {a b : X} (D : AtlasVortexPairData X a b) (x : D.leftGerm) :
    ‖D.leftGermGlobalPhaseMap x‖ = 1 := by
  rw [D.leftGermGlobalPhase_eq_compact]
  exact norm_planarVortexLeftGermCompactPhaseMap
    D.chart_values_ne (D.leftGermToPlanar x)

/-- The rotated radial angular phase pulled back through the atlas chart. -/
def AtlasVortexPairData.leftGermRadialPhaseMap {a b : X}
    (D : AtlasVortexPairData X a b) :
    ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      D.leftGerm ℂ ∞ :=
  (planarVortexLeftRotatedRadialPhaseMap D.chart_values_ne).comp
    D.leftGermToPlanarMap

theorem AtlasVortexPairData.norm_leftGermRadialPhaseMap
    {a b : X} (D : AtlasVortexPairData X a b) (x : D.leftGerm) :
    ‖D.leftGermRadialPhaseMap x‖ = 1 :=
  norm_planarVortexLeftRotatedRadialPhase
    D.chart_values_ne (D.leftGermToPlanar x)

/-- The unrotated coordinate radial phase pulled back through the atlas
chart. -/
def AtlasVortexPairData.leftGermUnrotatedRadialPhaseMap {a b : X}
    (D : AtlasVortexPairData X a b) :
    ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      D.leftGerm ℂ ∞ :=
  (planarVortexLeftRadialPhaseMap D.chart_values_ne).comp
    D.leftGermToPlanarMap

theorem AtlasVortexPairData.norm_leftGermUnrotatedRadialPhaseMap
    {a b : X} (D : AtlasVortexPairData X a b) (x : D.leftGerm) :
    ‖D.leftGermUnrotatedRadialPhaseMap x‖ = 1 :=
  norm_planarVortexLeftRadialPhase
    D.chart_values_ne (D.leftGermToPlanar x)

/-- The smooth exact correction on the surface left germ. -/
def AtlasVortexPairData.leftGermCorrectionSmooth {a b : X}
    (D : AtlasVortexPairData X a b) :
    C^∞⟮SurfaceRealModel, D.leftGerm; ℝ⟯ where
  val := fun x ↦ planarVortexLeftGermCorrection
    D.chart_values_ne (D.leftGermToPlanar x)
  property := (contMDiff_planarVortexLeftGermCorrection
    D.chart_values_ne).comp D.contMDiff_leftGermToPlanar

/-- On the atlas left germ, the transported compact phase is the radial
angular phase multiplied by the exponential of a smooth real correction. -/
theorem AtlasVortexPairData.leftGermGlobalPhase_eq_radial_mul_exp_correction
    {a b : X} (D : AtlasVortexPairData X a b) (x : D.leftGerm) :
    D.leftGermGlobalPhaseMap x = D.leftGermRadialPhaseMap x *
      Complex.exp (((((D.leftGermCorrectionSmooth x : ℝ) : ℂ) *
        Complex.I))) := by
  rw [D.leftGermGlobalPhase_eq_compact]
  exact planarVortexCompactPhaseAt_eq_rotatedRadial_mul_exp_correction
    D.chart_values_ne (D.leftGermToPlanar x)

/-- On a surface atlas germ, the logarithmic form of the compact vortex is
the radial angular form plus the differential of the smooth denominator
correction. -/
theorem AtlasVortexPairData.leftGermGlobalOneForm_eq_radial_addExact
    {a b : X} (D : AtlasVortexPairData X a b) :
    smoothUnitPhaseOneForm SurfaceRealModel
        D.leftGermGlobalPhaseMap D.norm_leftGermGlobalPhaseMap =
      smoothUnitPhaseOneForm SurfaceRealModel
          D.leftGermRadialPhaseMap D.norm_leftGermRadialPhaseMap +
        deRhamDifferential
          (I := SurfaceRealModel) (M := D.leftGerm) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
            D.leftGermCorrectionSmooth) := by
  exact SmoothCirclePrimitive.oneForm_eq_addExact_of_phase_eq
    SurfaceRealModel
    (smoothUnitPhaseCirclePrimitive SurfaceRealModel
      D.leftGermGlobalPhaseMap D.norm_leftGermGlobalPhaseMap)
    (smoothUnitPhaseCirclePrimitive SurfaceRealModel
      D.leftGermRadialPhaseMap D.norm_leftGermRadialPhaseMap)
    D.leftGermCorrectionSmooth
    D.leftGermGlobalPhase_eq_radial_mul_exp_correction

end

end JJMath.Uniformization
