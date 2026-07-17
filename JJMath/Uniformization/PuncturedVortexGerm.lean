import JJMath.Uniformization.AtlasVortexGerm
import JJMath.Uniformization.ExteriorVortexPrimitive

/-!
# The local radial germ of the transported puncture phase

The infinite vortex transport is stationary on a compact coordinate
neighborhood of its initial endpoint.  Intersecting that neighborhood with
the atlas-vortex radial germ identifies the actual global punctured phase
with a radial angular phase times the exponential of a smooth correction.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

private theorem contMDiffCodRestrictOpen''
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

namespace PuncturedAtlasVortexCirclePrimitiveData

/-- An unpunctured open neighborhood of the pole on which both the atlas
radial factorization and the stationary-transport identity hold. -/
def localRadialNeighborhood
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    TopologicalSpace.Opens X :=
  D.vortex.leftGermNeighborhood ⊓
    ⟨interior D.localDisk.carrier, isOpen_interior⟩

theorem pole_mem_localRadialNeighborhood
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    p ∈ D.localRadialNeighborhood :=
  ⟨D.vortex.left_mem_leftGermNeighborhood, D.pole_mem_interior⟩

/-- The stationary radial neighborhood contains a concentric closed
coordinate disk in the original atlas chart, with room for its doubled
punctured collar. -/
theorem exists_localRadialClosedCoordinateDisk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    ∃ K : ClosedCoordinateDisk X,
      K.openDisk.chart = D.vortex.chart ∧
        K.openDisk.center = D.vortex.chart p ∧
          2 * K.closedRadius ≤ K.openDisk.radius ∧
            K.openDisk.carrier ⊆ D.localRadialNeighborhood := by
  classical
  let e : OpenPartialHomeomorph X ℂ := D.vortex.chart
  let c : ℂ := e p
  let N : Set X := D.localRadialNeighborhood
  let S : Set ℂ := e.target ∩ e.symm ⁻¹' N
  have hNopen : IsOpen N := D.localRadialNeighborhood.isOpen
  have hSopen : IsOpen S := by
    simpa [S] using e.isOpen_inter_preimage_symm hNopen
  have hcS : c ∈ S := by
    refine ⟨e.map_source D.vortex.left_mem_source, ?_⟩
    have hleft : e.symm (e p) = p := e.left_inv D.vortex.left_mem_source
    simpa [c, N, hleft] using D.pole_mem_localRadialNeighborhood
  rcases Metric.isOpen_iff.mp hSopen c hcS with
    ⟨R, hRpos, hballS⟩
  let r : ℝ := R / 3
  have hrpos : 0 < r := by
    dsimp [r]
    linarith
  have hrR : r < R := by
    dsimp [r]
    linarith
  have hballTarget : Metric.ball c R ⊆ e.target := fun z hz ↦
    (hballS hz).1
  let K : ClosedCoordinateDisk X :=
    closedCoordinateDiskOfChartBall e D.vortex.chart_mem_atlas c
      hrpos hrR hballTarget
  have hdouble : 2 * K.closedRadius ≤ K.openDisk.radius := by
    change 2 * r ≤ R
    dsimp [r]
    linarith
  have hopenSubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood := by
    intro x hx
    change x ∈ e.source ∩ e ⁻¹' Metric.ball c R at hx
    have hsymm : e.symm (e x) = x := e.left_inv hx.1
    have hxN : e.symm (e x) ∈ N := (hballS hx.2).2
    simpa [N, hsymm] using hxN
  exact ⟨K, rfl, rfl, hdouble, hopenSubset⟩

/-- The stationary radial certificate may be chosen inside any prescribed
open neighborhood of the puncture. -/
theorem exists_localRadialClosedCoordinateDisk_subset_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (O : TopologicalSpace.Opens X) (hpO : p ∈ O) :
    ∃ K : ClosedCoordinateDisk X,
      K.openDisk.chart = D.vortex.chart ∧
        K.openDisk.center = D.vortex.chart p ∧
          2 * K.closedRadius ≤ K.openDisk.radius ∧
            K.openDisk.carrier ⊆ D.localRadialNeighborhood ∧
              K.openDisk.carrier ⊆ O := by
  classical
  let e : OpenPartialHomeomorph X ℂ := D.vortex.chart
  let c : ℂ := e p
  let N : Set X := D.localRadialNeighborhood ∩ O
  have hNopen : IsOpen N :=
    D.localRadialNeighborhood.isOpen.inter O.isOpen
  let S : Set ℂ := e.target ∩ e.symm ⁻¹' N
  have hSopen : IsOpen S := by
    simpa [S] using e.isOpen_inter_preimage_symm hNopen
  have hcS : c ∈ S := by
    refine ⟨e.map_source D.vortex.left_mem_source, ?_⟩
    have hleft : e.symm (e p) = p := e.left_inv D.vortex.left_mem_source
    simpa [c, N, hleft] using
      ⟨D.pole_mem_localRadialNeighborhood, hpO⟩
  rcases Metric.isOpen_iff.mp hSopen c hcS with
    ⟨R, hRpos, hballS⟩
  let r : ℝ := R / 3
  have hrpos : 0 < r := by
    dsimp [r]
    linarith
  have hrR : r < R := by
    dsimp [r]
    linarith
  have hballTarget : Metric.ball c R ⊆ e.target := fun z hz ↦
    (hballS hz).1
  let K : ClosedCoordinateDisk X :=
    closedCoordinateDiskOfChartBall e D.vortex.chart_mem_atlas c
      hrpos hrR hballTarget
  have hdouble : 2 * K.closedRadius ≤ K.openDisk.radius := by
    change 2 * r ≤ R
    dsimp [r]
    linarith
  have hopenSubsetN : K.openDisk.carrier ⊆ N := by
    intro x hx
    change x ∈ e.source ∩ e ⁻¹' Metric.ball c R at hx
    have hsymm : e.symm (e x) = x := e.left_inv hx.1
    have hxN : e.symm (e x) ∈ N := (hballS hx.2).2
    simpa [hsymm] using hxN
  exact ⟨K, rfl, rfl, hdouble,
    fun x hx ↦ (hopenSubsetN hx).1,
    fun x hx ↦ (hopenSubsetN hx).2⟩

/-- The portion of the initial atlas-vortex germ lying in the disk on which
the infinite transport is stationary. -/
def localRadialGerm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    TopologicalSpace.Opens D.vortex.leftGerm :=
  ⟨{x | (x : X) ∈ interior D.localDisk.carrier},
    isOpen_interior.preimage
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_subtype_val))⟩

/-- The local radial germ included into the globally punctured surface. -/
def localRadialGermToPunctured
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (x : D.localRadialGerm) : atlasVortexInitialOpen p :=
  ⟨(x : X), (x.1.1.1 : coordinateVortexPairOpen p D.terminal).2.1⟩

theorem contMDiff_localRadialGermToPunctured
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    ContMDiff SurfaceRealModel SurfaceRealModel ∞
      D.localRadialGermToPunctured := by
  exact contMDiffCodRestrictOpen''
    (contMDiff_subtype_val.comp
      (contMDiff_subtype_val.comp
        (contMDiff_subtype_val.comp contMDiff_subtype_val)))
    (atlasVortexInitialOpen p)
    (fun x ↦ (x.1.1.1 : coordinateVortexPairOpen p D.terminal).2.1)

/-- The transported global phase restricted to its stationary radial germ. -/
def localRadialGermPhaseMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      D.localRadialGerm ℂ ∞ where
  val := fun x ↦ D.phase (D.localRadialGermToPunctured x)
  property := D.phase.contMDiff.comp D.contMDiff_localRadialGermToPunctured

theorem norm_localRadialGermPhaseMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (x : D.localRadialGerm) : ‖D.localRadialGermPhaseMap x‖ = 1 :=
  D.norm_phase (D.localRadialGermToPunctured x)

/-- The atlas radial phase restricted to the stationary local germ. -/
def localRadialGermRadialPhaseMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      D.localRadialGerm ℂ ∞ :=
  D.vortex.leftGermRadialPhaseMap.comp
    { val := fun x : D.localRadialGerm ↦ (x : D.vortex.leftGerm)
      property := contMDiff_subtype_val }

theorem norm_localRadialGermRadialPhaseMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (x : D.localRadialGerm) :
    ‖D.localRadialGermRadialPhaseMap x‖ = 1 :=
  D.vortex.norm_leftGermRadialPhaseMap x.1

/-- The ordinary, unrotated coordinate direction on the stationary local
germ. -/
def localRadialGermUnrotatedPhaseMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      D.localRadialGerm ℂ ∞ :=
  D.vortex.leftGermUnrotatedRadialPhaseMap.comp
    { val := fun x : D.localRadialGerm ↦ (x : D.vortex.leftGerm)
      property := contMDiff_subtype_val }

theorem norm_localRadialGermUnrotatedPhaseMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (x : D.localRadialGerm) :
    ‖D.localRadialGermUnrotatedPhaseMap x‖ = 1 :=
  D.vortex.norm_leftGermUnrotatedRadialPhaseMap x.1

/-- The atlas denominator correction restricted to the stationary local
germ. -/
def localRadialGermCorrectionSmooth
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    C^∞⟮SurfaceRealModel, D.localRadialGerm; ℝ⟯ where
  val := fun x ↦ D.vortex.leftGermCorrectionSmooth x.1
  property := D.vortex.leftGermCorrectionSmooth.contMDiff.comp
    contMDiff_subtype_val

/-- The total smooth correction after absorbing the constant rotation into
the denominator correction. -/
def localRadialGermTotalCorrectionSmooth
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    C^∞⟮SurfaceRealModel, D.localRadialGerm; ℝ⟯ where
  val := fun x ↦
    Complex.arg ((‖D.vortex.chart p - D.vortex.chart D.terminal‖ : ℂ) /
      (D.vortex.chart p - D.vortex.chart D.terminal)) +
        D.localRadialGermCorrectionSmooth x
  property := contMDiff_const.add
    D.localRadialGermCorrectionSmooth.contMDiff

/-- The actual transported puncture phase has the radial angular
factorization on its stationary local germ. -/
theorem localRadialGermPhase_eq_radial_mul_exp_correction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (x : D.localRadialGerm) :
    D.localRadialGermPhaseMap x =
      D.localRadialGermRadialPhaseMap x *
        Complex.exp (((((D.localRadialGermCorrectionSmooth x : ℝ) : ℂ) *
          Complex.I))) := by
  have hstationary := D.phase_eq_vortex
    (x.1.1.1 : coordinateVortexPairOpen p D.terminal)
    (interior_subset x.2)
  calc
    D.localRadialGermPhaseMap x =
        D.vortex.leftGermGlobalPhaseMap x.1 := hstationary
    _ = D.vortex.leftGermRadialPhaseMap x.1 *
        Complex.exp (((((D.vortex.leftGermCorrectionSmooth x.1 : ℝ) : ℂ) *
          Complex.I))) :=
      D.vortex.leftGermGlobalPhase_eq_radial_mul_exp_correction x.1
    _ = D.localRadialGermRadialPhaseMap x *
        Complex.exp (((((D.localRadialGermCorrectionSmooth x : ℝ) : ℂ) *
          Complex.I))) := rfl

/-- After absorbing its constant rotation, the transported puncture phase is
the ordinary coordinate direction times the exponential of one smooth real
function. -/
theorem localRadialGermPhase_eq_unrotated_mul_exp_totalCorrection
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (x : D.localRadialGerm) :
    D.localRadialGermPhaseMap x =
      D.localRadialGermUnrotatedPhaseMap x *
        Complex.exp (((((D.localRadialGermTotalCorrectionSmooth x : ℝ) : ℂ) *
          Complex.I))) := by
  let k : ℂ :=
    (‖D.vortex.chart p - D.vortex.chart D.terminal‖ : ℂ) /
      (D.vortex.chart p - D.vortex.chart D.terminal)
  have hkNorm : ‖k‖ = 1 := by
    simp [k, div_self (norm_ne_zero_iff.mpr
      (sub_ne_zero.mpr D.vortex.chart_values_ne))]
  have hkExp : Complex.exp (((Complex.arg k : ℂ) * Complex.I)) = k := by
    have h := Complex.norm_mul_exp_arg_mul_I k
    rw [hkNorm, Complex.ofReal_one, one_mul] at h
    exact h
  rw [D.localRadialGermPhase_eq_radial_mul_exp_correction]
  change
    (D.localRadialGermUnrotatedPhaseMap x * k) *
        Complex.exp (((D.localRadialGermCorrectionSmooth x : ℂ) *
          Complex.I)) =
      D.localRadialGermUnrotatedPhaseMap x *
        Complex.exp (((((Complex.arg k +
          D.localRadialGermCorrectionSmooth x : ℝ) : ℂ) * Complex.I)))
  let e := Complex.exp
    (((D.localRadialGermCorrectionSmooth x : ℝ) : ℂ) * Complex.I)
  have hprod : k * e =
      Complex.exp (((Complex.arg k : ℂ) * Complex.I)) * e :=
    congrArg (fun z : ℂ => z * e) hkExp.symm
  calc
    (D.localRadialGermUnrotatedPhaseMap x * k) * e =
        D.localRadialGermUnrotatedPhaseMap x * (k * e) := mul_assoc _ _ _
    _ = D.localRadialGermUnrotatedPhaseMap x *
        (Complex.exp (((Complex.arg k : ℂ) * Complex.I)) * e) :=
      congrArg (fun z : ℂ => D.localRadialGermUnrotatedPhaseMap x * z) hprod
    _ = D.localRadialGermUnrotatedPhaseMap x *
        Complex.exp (((Complex.arg k : ℂ) * Complex.I) +
          (((D.localRadialGermCorrectionSmooth x : ℝ) : ℂ) * Complex.I)) := by
      rw [Complex.exp_add]
    _ = D.localRadialGermUnrotatedPhaseMap x *
        Complex.exp (((((Complex.arg k +
          D.localRadialGermCorrectionSmooth x : ℝ) : ℂ) * Complex.I))) := by
      congr 2
      push_cast
      ring

/-- On the stationary puncture germ, the logarithmic one-form of the global
transported phase is the radial angular form plus an exact correction. -/
theorem localRadialGermOneForm_eq_radial_addExact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    smoothUnitPhaseOneForm SurfaceRealModel
        D.localRadialGermPhaseMap D.norm_localRadialGermPhaseMap =
      smoothUnitPhaseOneForm SurfaceRealModel
          D.localRadialGermRadialPhaseMap
          D.norm_localRadialGermRadialPhaseMap +
        deRhamDifferential
          (I := SurfaceRealModel) (M := D.localRadialGerm) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
            D.localRadialGermCorrectionSmooth) := by
  exact SmoothCirclePrimitive.oneForm_eq_addExact_of_phase_eq
    SurfaceRealModel
    (smoothUnitPhaseCirclePrimitive SurfaceRealModel
      D.localRadialGermPhaseMap D.norm_localRadialGermPhaseMap)
    (smoothUnitPhaseCirclePrimitive SurfaceRealModel
      D.localRadialGermRadialPhaseMap
      D.norm_localRadialGermRadialPhaseMap)
    D.localRadialGermCorrectionSmooth
    D.localRadialGermPhase_eq_radial_mul_exp_correction

/-- On the stationary puncture germ, the global logarithmic one-form is the
ordinary coordinate angular form plus an exact term. -/
theorem localRadialGermOneForm_eq_unrotated_addExact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    smoothUnitPhaseOneForm SurfaceRealModel
        D.localRadialGermPhaseMap D.norm_localRadialGermPhaseMap =
      smoothUnitPhaseOneForm SurfaceRealModel
          D.localRadialGermUnrotatedPhaseMap
          D.norm_localRadialGermUnrotatedPhaseMap +
        deRhamDifferential
          (I := SurfaceRealModel) (M := D.localRadialGerm) (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
            D.localRadialGermTotalCorrectionSmooth) := by
  exact SmoothCirclePrimitive.oneForm_eq_addExact_of_phase_eq
    SurfaceRealModel
    (smoothUnitPhaseCirclePrimitive SurfaceRealModel
      D.localRadialGermPhaseMap D.norm_localRadialGermPhaseMap)
    (smoothUnitPhaseCirclePrimitive SurfaceRealModel
      D.localRadialGermUnrotatedPhaseMap
      D.norm_localRadialGermUnrotatedPhaseMap)
    D.localRadialGermTotalCorrectionSmooth
    D.localRadialGermPhase_eq_unrotated_mul_exp_totalCorrection

end PuncturedAtlasVortexCirclePrimitiveData

end

end JJMath.Uniformization
