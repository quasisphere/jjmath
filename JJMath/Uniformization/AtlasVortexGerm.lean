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

/--
%%handwave
name:
  Smooth corestriction to an open submanifold
statement:
  A smooth map \(f:M\to N\) whose image lies in an open subset \(V\subseteq N\)
  remains smooth when regarded as a map from \(M\) to \(V\).
proof:
  Near every image point, compose with the local retraction onto \(V\), which
  agrees there with the identity.
-/
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

/--
%%handwave
name:
  The zero endpoint lies in the left vortex-germ neighborhood
statement:
  For an atlas vortex from \(a\) to \(b\), the zero endpoint \(a\) belongs to
  the unpunctured coordinate neighborhood defining its left radial germ.
proof:
  At the left endpoint, the affine vortex coordinate is \(0\), whose norm is
  less than \(2\), and the normalized denominator is \(1\), which lies in the
  slit plane.  The endpoints are distinct, so the additional exclusion of
  \(b\) is satisfied.
-/
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

/--
%%handwave
name:
  Smoothness of the atlas-to-planar left-germ map
statement:
  The map from the left radial germ of an atlas vortex to the corresponding
  planar vortex germ, obtained by applying the surface coordinate and affine
  normalization, is smooth.
proof:
  The ambient atlas-to-planar coordinate map is smooth and takes the surface
  germ into the open planar germ.  Corestrict it to that open target.
-/
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

/--
%%handwave
name:
  The global atlas-vortex phase equals the compact planar phase on the left germ
statement:
  On the left radial germ of an atlas vortex, its globally glued phase equals
  the compact planar vortex phase pulled back through the atlas-to-planar
  coordinate map.
proof:
  The global phase agrees with the chart phase throughout the chart patch,
  and the chart phase is defined by pulling back the compact planar phase.
-/
theorem AtlasVortexPairData.leftGermGlobalPhase_eq_compact
    {a b : X} (D : AtlasVortexPairData X a b) (x : D.leftGerm) :
    D.leftGermGlobalPhaseMap x = D.leftGermCompactPhaseMap x := by
  change D.globalPhase (x.1 : coordinateVortexPairOpen a b) =
    planarVortexCompactPhaseAt D.chart_values_ne (D.toPlanarPair x.1)
  rw [show D.globalPhase (x.1 : coordinateVortexPairOpen a b) =
      D.chartPhase x.1 from D.globalPhaseFun_eq_chart x.1.2]
  rfl

/--
%%handwave
name:
  Unit norm of the global atlas-vortex phase on the left germ
statement:
  The global atlas-vortex phase has complex modulus one at every point of its
  left radial germ.
proof:
  Replace it by the pulled-back compact planar phase, whose modulus is one.
-/
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

/--
%%handwave
name:
  Unit norm of the rotated radial phase on an atlas germ
statement:
  The rotated radial angular phase pulled back to the left germ of an atlas
  vortex has complex modulus one.
proof:
  Apply the unit-norm identity for the planar rotated radial phase at the
  atlas-to-planar image of the point.
-/
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

/--
%%handwave
name:
  Unit norm of the coordinate radial phase on an atlas germ
statement:
  The unrotated coordinate radial phase pulled back to the left germ of an
  atlas vortex has complex modulus one.
proof:
  Apply the planar radial-phase norm identity after the atlas-to-planar map.
-/
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

/--
%%handwave
name:
  Radial factorization of the atlas-vortex phase near its zero
statement:
  On the left germ of an atlas vortex, its global phase factors as
  \[
    P_{\mathrm{vortex}}=P_{\mathrm{radial}}e^{ih},
  \]
  where \(P_{\mathrm{radial}}\) is the rotated radial angular phase and \(h\)
  is the smooth real denominator correction pulled back from the planar germ.
proof:
  Identify the global germ with the compact planar vortex phase and pull back
  the planar radial-times-exponential factorization.
-/
theorem AtlasVortexPairData.leftGermGlobalPhase_eq_radial_mul_exp_correction
    {a b : X} (D : AtlasVortexPairData X a b) (x : D.leftGerm) :
    D.leftGermGlobalPhaseMap x = D.leftGermRadialPhaseMap x *
      Complex.exp (((((D.leftGermCorrectionSmooth x : ℝ) : ℂ) *
        Complex.I))) := by
  rw [D.leftGermGlobalPhase_eq_compact]
  exact planarVortexCompactPhaseAt_eq_rotatedRadial_mul_exp_correction
    D.chart_values_ne (D.leftGermToPlanar x)

/--
%%handwave
name:
  The atlas-vortex one-form is radial up to an exact correction
statement:
  On the left germ of an atlas vortex, the logarithmic one-form of the global
  vortex phase equals the logarithmic one-form of the rotated radial phase
  plus \(dh\), where \(h\) is the smooth real denominator correction.
proof:
  Apply the circle-primitive identity saying that a phase factorization
  \(P=Qe^{ih}\) changes the logarithmic one-form by the exact form \(dh\),
  using the radial factorization of the atlas-vortex phase.
-/
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
