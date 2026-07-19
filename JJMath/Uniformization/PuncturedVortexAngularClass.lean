import JJMath.Uniformization.PuncturedVortexGerm
import JJMath.Uniformization.PuncturedAngularCirclePrimitive
import JJMath.Uniformization.SmoothUnitPhaseRestriction
import JJMath.Uniformization.AnnularRadialClass

/-!
# The angular class of the transported puncture vortex

The transported vortex phase is first put on the repository's standard
punctured-surface open subtype.  A sufficiently small coordinate disk in the
stationary germ then identifies its restriction with the ordinary coordinate
direction, up to multiplication by the exponential of a smooth real
function.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

attribute [local instance] finrank_real_complex_fact'

namespace PuncturedAtlasVortexCirclePrimitiveData

/-- The transported unit phase, on the standard punctured-surface subtype. -/
def puncturedPhase
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      (puncturedSurfaceOpen p) ℂ ∞ := by
  simpa [puncturedSurfaceOpen, atlasVortexInitialOpen] using D.phase

/--
%%handwave
name:
  Unit modulus of the transported puncture phase
statement:
  The transported puncture phase has modulus one at every point of
  \(X\setminus\{p\}\).
proof:
  This is the unit-modulus property of the global transported vortex phase,
  restricted to the punctured surface.
-/
theorem norm_puncturedPhase
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (x : puncturedSurfaceOpen p) : ‖D.puncturedPhase x‖ = 1 := by
  exact D.norm_phase ⟨(x : X), x.2⟩

/-- The closed logarithmic one-form of the transported phase, on the standard
punctured surface. -/
def puncturedClosedOneForm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    DeRhamClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1 :=
  (smoothUnitPhaseCirclePrimitive SurfaceRealModel
    D.puncturedPhase D.norm_puncturedPhase).toClosedForm SurfaceRealModel

/-- Normalize the transported puncture form so that multiplication by
`2 * pi` recovers the logarithmic form of its unit phase. -/
def puncturedNormalizedClosedOneForm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    DeRhamClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1 :=
  (2 * Real.pi)⁻¹ • D.puncturedClosedOneForm

/-- The normalized transported puncture form has its global unit phase as a
circle primitive. -/
def puncturedNormalizedCirclePrimitive
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    SmoothCirclePrimitive SurfaceRealModel
      ((2 * Real.pi) • D.puncturedNormalizedClosedOneForm.1) := by
  apply SmoothCirclePrimitive.congr SurfaceRealModel
    (smoothUnitPhaseCirclePrimitive SurfaceRealModel
      D.puncturedPhase D.norm_puncturedPhase)
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  change smoothUnitPhaseOneForm SurfaceRealModel
      D.puncturedPhase D.norm_puncturedPhase =
    (2 * Real.pi) • ((2 * Real.pi)⁻¹ •
      smoothUnitPhaseOneForm SurfaceRealModel
        D.puncturedPhase D.norm_puncturedPhase)
  rw [smul_smul, mul_inv_cancel₀ htwoPi, one_smul]

/-- Include a punctured doubled coordinate disk contained in the stationary
radial neighborhood into the local radial germ. -/
def puncturedExpandedOpenDiskToLocalRadialGerm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood)
    (y : K.puncturedExpandedOpenDisk p (2 * K.closedRadius)) :
    D.localRadialGerm := by
  have hyOpen : (y : X) ∈ K.openDisk.carrier := by
    rw [K.openDisk.carrier_eq]
    exact ⟨y.2.2.1, Metric.ball_subset_ball hdouble y.2.2.2⟩
  have hyN : (y : X) ∈ D.localRadialNeighborhood := hsubset hyOpen
  exact ⟨D.vortex.toLeftGermOfMemNeighborhood
    (y : X) hyN.1 y.2.1, hyN.2⟩

/--
%%handwave
name:
  Smooth inclusion of a punctured coordinate disk into the radial germ
statement:
  A punctured doubled coordinate disk contained in the stationary radial
  neighborhood maps smoothly into the local radial vortex germ.
proof:
  The map is the ambient subtype inclusion, successively restricted through
  the chart patch, the left-pole germ, and the radial neighborhood; each is
  an open submanifold restriction of a smooth map.
-/
theorem contMDiff_puncturedExpandedOpenDiskToLocalRadialGerm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (D.puncturedExpandedOpenDiskToLocalRadialGerm K hdouble hsubset) := by
  let W := K.puncturedExpandedOpenDisk p (2 * K.closedRadius)
  have hyN : ∀ y : W, (y : X) ∈ D.localRadialNeighborhood := by
    intro y
    apply hsubset
    rw [K.openDisk.carrier_eq]
    exact ⟨y.2.2.1, Metric.ball_subset_ball hdouble y.2.2.2⟩
  have hval : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun y : W ↦ (y : X)) := contMDiff_subtype_val
  have hpair : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun y : W ↦
        (⟨(y : X), y.2.1, (hyN y).1.2⟩ :
          coordinateVortexPairOpen p D.terminal)) := by
    exact ContMDiff.codRestrict_open hval
      (coordinateVortexPairOpen p D.terminal)
      (fun y ↦ ⟨y.2.1, (hyN y).1.2⟩)
  have hpatch : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun y : W ↦
        (⟨⟨(y : X), y.2.1, (hyN y).1.2⟩, (hyN y).1.1.1⟩ :
          D.vortex.chartPatch)) := by
    exact ContMDiff.codRestrict_open hpair D.vortex.chartPatch
      (fun y ↦ (hyN y).1.1.1)
  have hgerm : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun y : W ↦
        (⟨⟨⟨(y : X), y.2.1, (hyN y).1.2⟩, (hyN y).1.1.1⟩,
          (hyN y).1.1.2⟩ : D.vortex.leftGerm)) := by
    exact ContMDiff.codRestrict_open hpatch D.vortex.leftGerm
      (fun y ↦ (hyN y).1.1.2)
  exact ContMDiff.codRestrict_open hgerm D.localRadialGerm
    (fun y ↦ (hyN y).2)

/-- The punctured-disk inclusion as a bundled smooth map. -/
def puncturedExpandedOpenDiskToLocalRadialGermMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    ContMDiffMap SurfaceRealModel SurfaceRealModel
      (K.puncturedExpandedOpenDisk p (2 * K.closedRadius))
      D.localRadialGerm ∞ where
  val := D.puncturedExpandedOpenDiskToLocalRadialGerm K hdouble hsubset
  property := D.contMDiff_puncturedExpandedOpenDiskToLocalRadialGerm
    K hdouble hsubset

/-- The transported phase restricted to a punctured doubled coordinate
disk in its stationary neighborhood. -/
def puncturedExpandedOpenDiskPhaseMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      (K.puncturedExpandedOpenDisk p (2 * K.closedRadius)) ℂ ∞ :=
  D.localRadialGermPhaseMap.comp
    (D.puncturedExpandedOpenDiskToLocalRadialGermMap K hdouble hsubset)

/--
%%handwave
name:
  Unit modulus of the phase on the punctured coordinate disk
statement:
  The transported phase restricted to the punctured doubled coordinate disk
  has modulus one everywhere.
proof:
  Evaluate the unit-modulus property of the local radial-germ phase at the
  image of the point.
-/
theorem norm_puncturedExpandedOpenDiskPhaseMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood)
    (y : K.puncturedExpandedOpenDisk p (2 * K.closedRadius)) :
    ‖D.puncturedExpandedOpenDiskPhaseMap K hdouble hsubset y‖ = 1 :=
  D.norm_localRadialGermPhaseMap
    (D.puncturedExpandedOpenDiskToLocalRadialGerm K hdouble hsubset y)

/--
%%handwave
name:
  The local radial phase is the restricted global puncture phase
statement:
  On the stationary punctured coordinate disk, the phase obtained through
  the local radial germ equals the restriction of the global transported
  puncture phase.
proof:
  Both sides are definitionally the same global phase evaluated at the
  underlying punctured-surface point.
-/
theorem puncturedExpandedOpenDiskPhaseMap_eq_puncturedPhase
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood)
    (y : K.puncturedExpandedOpenDisk p (2 * K.closedRadius)) :
    D.puncturedExpandedOpenDiskPhaseMap K hdouble hsubset y =
      D.puncturedPhase
        (TopologicalSpace.Opens.inclusion inf_le_left y) := by
  rfl

/--
%%handwave
name:
  Restriction of the global logarithmic vortex form
statement:
  On the stationary punctured coordinate disk, the restriction of the global
  logarithmic one-form equals the logarithmic one-form of the restricted
  phase.
proof:
  Formation of the logarithmic one-form of a smooth unit phase commutes with
  restriction to an open submanifold, and the restricted phases agree.
-/
theorem restrict_puncturedClosedOneForm_eq_puncturedExpandedOpenDisk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
        (W := K.puncturedExpandedOpenDisk p (2 * K.closedRadius))
        (V := puncturedSurfaceOpen p) inf_le_left 1
        D.puncturedClosedOneForm.1 =
      smoothUnitPhaseOneForm SurfaceRealModel
        (D.puncturedExpandedOpenDiskPhaseMap K hdouble hsubset)
        (D.norm_puncturedExpandedOpenDiskPhaseMap K hdouble hsubset) := by
  exact smoothUnitPhaseOneForm_restrictOfLE SurfaceRealModel inf_le_left
    D.puncturedPhase D.norm_puncturedPhase
    (D.puncturedExpandedOpenDiskPhaseMap K hdouble hsubset)
    (D.norm_puncturedExpandedOpenDiskPhaseMap K hdouble hsubset)
    (D.puncturedExpandedOpenDiskPhaseMap_eq_puncturedPhase
      K hdouble hsubset)

/-- The ordinary coordinate direction restricted to the same punctured
doubled disk. -/
def puncturedExpandedOpenDiskUnrotatedPhaseMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      (K.puncturedExpandedOpenDisk p (2 * K.closedRadius)) ℂ ∞ :=
  D.localRadialGermUnrotatedPhaseMap.comp
    (D.puncturedExpandedOpenDiskToLocalRadialGermMap K hdouble hsubset)

/--
%%handwave
name:
  Unit modulus of the unrotated radial phase
statement:
  The unrotated coordinate-direction phase on the punctured doubled disk has
  modulus one everywhere.
proof:
  Restrict the unit-modulus property of the unrotated local radial-germ phase.
-/
theorem norm_puncturedExpandedOpenDiskUnrotatedPhaseMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood)
    (y : K.puncturedExpandedOpenDisk p (2 * K.closedRadius)) :
    ‖D.puncturedExpandedOpenDiskUnrotatedPhaseMap K hdouble hsubset y‖ = 1 :=
  D.norm_localRadialGermUnrotatedPhaseMap
    (D.puncturedExpandedOpenDiskToLocalRadialGerm K hdouble hsubset y)

/-- The smooth local correction restricted to the punctured doubled disk. -/
def puncturedExpandedOpenDiskCorrectionSmooth
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    C^∞⟮SurfaceRealModel,
      K.puncturedExpandedOpenDisk p (2 * K.closedRadius); ℝ⟯ where
  val := fun y ↦ D.localRadialGermTotalCorrectionSmooth
    (D.puncturedExpandedOpenDiskToLocalRadialGerm K hdouble hsubset y)
  property := D.localRadialGermTotalCorrectionSmooth.contMDiff.comp
    (D.contMDiff_puncturedExpandedOpenDiskToLocalRadialGerm
      K hdouble hsubset)

/--
%%handwave
name:
  Local factorization of the transported puncture phase
statement:
  On the punctured doubled disk, the transported phase is
  \[
    u=u_0e^{ih},
  \]
  where \(u_0\) is the unrotated coordinate-direction phase and \(h\) is a
  smooth real correction.
proof:
  Restrict the corresponding stationary radial-germ factorization to the
  punctured coordinate disk.
-/
theorem puncturedExpandedOpenDiskPhase_eq_unrotated_mul_exp_correction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood)
    (y : K.puncturedExpandedOpenDisk p (2 * K.closedRadius)) :
    D.puncturedExpandedOpenDiskPhaseMap K hdouble hsubset y =
      D.puncturedExpandedOpenDiskUnrotatedPhaseMap K hdouble hsubset y *
        Complex.exp (((((D.puncturedExpandedOpenDiskCorrectionSmooth
          K hdouble hsubset y : ℝ) : ℂ) * Complex.I))) :=
  D.localRadialGermPhase_eq_unrotated_mul_exp_totalCorrection
    (D.puncturedExpandedOpenDiskToLocalRadialGerm K hdouble hsubset y)

/--
%%handwave
name:
  The transported logarithmic form differs from the radial form by an exact form
statement:
  If \(u=u_0e^{ih}\) on the punctured doubled disk, then their logarithmic
  one-forms satisfy
  \[
    \alpha_u=\alpha_{u_0}+dh.
  \]
proof:
  Apply the logarithmic differentiation formula for two unit phases related
  by multiplication by the exponential of a smooth real function.
-/
theorem puncturedExpandedOpenDiskOneForm_eq_unrotated_addExact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    smoothUnitPhaseOneForm SurfaceRealModel
        (D.puncturedExpandedOpenDiskPhaseMap K hdouble hsubset)
        (D.norm_puncturedExpandedOpenDiskPhaseMap K hdouble hsubset) =
      smoothUnitPhaseOneForm SurfaceRealModel
          (D.puncturedExpandedOpenDiskUnrotatedPhaseMap K hdouble hsubset)
          (D.norm_puncturedExpandedOpenDiskUnrotatedPhaseMap
            K hdouble hsubset) +
        deRhamDifferential
          (I := SurfaceRealModel)
          (M := K.puncturedExpandedOpenDisk p (2 * K.closedRadius))
          (A := ℝ) 0
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
            (D.puncturedExpandedOpenDiskCorrectionSmooth
              K hdouble hsubset)) := by
  exact SmoothCirclePrimitive.oneForm_eq_addExact_of_phase_eq
    SurfaceRealModel
    (smoothUnitPhaseCirclePrimitive SurfaceRealModel
      (D.puncturedExpandedOpenDiskPhaseMap K hdouble hsubset)
      (D.norm_puncturedExpandedOpenDiskPhaseMap K hdouble hsubset))
    (smoothUnitPhaseCirclePrimitive SurfaceRealModel
      (D.puncturedExpandedOpenDiskUnrotatedPhaseMap K hdouble hsubset)
      (D.norm_puncturedExpandedOpenDiskUnrotatedPhaseMap
        K hdouble hsubset))
    (D.puncturedExpandedOpenDiskCorrectionSmooth K hdouble hsubset)
    (D.puncturedExpandedOpenDiskPhase_eq_unrotated_mul_exp_correction
      K hdouble hsubset)

/-- The normalized closed form of the transported phase on the punctured
doubled disk. -/
def puncturedExpandedOpenDiskNormalizedClosedOneForm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    DeRhamClosedForms (I := SurfaceRealModel)
      (M := K.puncturedExpandedOpenDisk p (2 * K.closedRadius))
      (A := ℝ) 1 :=
  (2 * Real.pi)⁻¹ •
    (smoothUnitPhaseCirclePrimitive SurfaceRealModel
      (D.puncturedExpandedOpenDiskPhaseMap K hdouble hsubset)
      (D.norm_puncturedExpandedOpenDiskPhaseMap K hdouble hsubset)
      |>.toClosedForm SurfaceRealModel)

/--
%%handwave
name:
  Restriction commutes with normalization of the vortex form
statement:
  Restricting the globally normalized puncture form to the stationary
  punctured disk gives the normalized logarithmic form of the restricted
  phase.
proof:
  Restriction is linear, so it commutes with multiplication by
  \((2\pi)^{-1}\); then use the unnormalized restriction identity.
-/
theorem restrict_puncturedNormalizedClosedOneForm_eq_puncturedExpandedOpenDisk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    deRhamClosedFormsRestrictionOfLE
        (I := SurfaceRealModel) (M := X) (A := ℝ)
        (W := K.puncturedExpandedOpenDisk p (2 * K.closedRadius))
        (V := puncturedSurfaceOpen p) inf_le_left 1
        D.puncturedNormalizedClosedOneForm =
      D.puncturedExpandedOpenDiskNormalizedClosedOneForm
        K hdouble hsubset := by
  apply Subtype.ext
  change
    restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
        inf_le_left 1 ((2 * Real.pi)⁻¹ • D.puncturedClosedOneForm.1) =
      (2 * Real.pi)⁻¹ •
        smoothUnitPhaseOneForm SurfaceRealModel
          (D.puncturedExpandedOpenDiskPhaseMap K hdouble hsubset)
          (D.norm_puncturedExpandedOpenDiskPhaseMap K hdouble hsubset)
  rw [map_smul]
  congr 1
  exact D.restrict_puncturedClosedOneForm_eq_puncturedExpandedOpenDisk
    K hdouble hsubset

/-- The normalized closed form of the ordinary coordinate direction on the
punctured doubled disk. -/
def puncturedExpandedOpenDiskRadialNormalizedClosedOneForm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    DeRhamClosedForms (I := SurfaceRealModel)
      (M := K.puncturedExpandedOpenDisk p (2 * K.closedRadius))
      (A := ℝ) 1 :=
  (2 * Real.pi)⁻¹ •
    (smoothUnitPhaseCirclePrimitive SurfaceRealModel
      (D.puncturedExpandedOpenDiskUnrotatedPhaseMap K hdouble hsubset)
      (D.norm_puncturedExpandedOpenDiskUnrotatedPhaseMap
        K hdouble hsubset)
      |>.toClosedForm SurfaceRealModel)

/--
%%handwave
name:
  The transported and radial puncture forms define the same class
statement:
  On the stationary punctured doubled disk, the normalized logarithmic form
  of the transported phase and that of the coordinate-direction phase
  represent the same class in \(H^1_{\mathrm{dR}}\).
proof:
  Their difference is \((2\pi)^{-1}dh\), hence is exact.
-/
theorem puncturedExpandedOpenDiskNormalizedClass_eq_radial
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    (DeRhamExactClosedForms (I := SurfaceRealModel)
        (M := K.puncturedExpandedOpenDisk p (2 * K.closedRadius))
        (A := ℝ) 1).mkQ
        (D.puncturedExpandedOpenDiskNormalizedClosedOneForm
          K hdouble hsubset) =
      (DeRhamExactClosedForms (I := SurfaceRealModel)
        (M := K.puncturedExpandedOpenDisk p (2 * K.closedRadius))
        (A := ℝ) 1).mkQ
        (D.puncturedExpandedOpenDiskRadialNormalizedClosedOneForm
          K hdouble hsubset) := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq]
  change
    ((2 * Real.pi)⁻¹ •
        smoothUnitPhaseOneForm SurfaceRealModel
          (D.puncturedExpandedOpenDiskPhaseMap K hdouble hsubset)
          (D.norm_puncturedExpandedOpenDiskPhaseMap K hdouble hsubset) -
      (2 * Real.pi)⁻¹ •
        smoothUnitPhaseOneForm SurfaceRealModel
          (D.puncturedExpandedOpenDiskUnrotatedPhaseMap K hdouble hsubset)
          (D.norm_puncturedExpandedOpenDiskUnrotatedPhaseMap
            K hdouble hsubset)) ∈
      DeRhamExactForms (I := SurfaceRealModel)
        (M := K.puncturedExpandedOpenDisk p (2 * K.closedRadius))
        (A := ℝ) 1
  rw [DeRhamExactForms]
  refine ⟨(2 * Real.pi)⁻¹ •
    smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
      (D.puncturedExpandedOpenDiskCorrectionSmooth
        K hdouble hsubset), ?_⟩
  rw [map_smul,
    D.puncturedExpandedOpenDiskOneForm_eq_unrotated_addExact]
  module

/--
%%handwave
name:
  The restricted global vortex form has the radial class
statement:
  On a stationary punctured doubled disk, the restriction of the global
  normalized vortex form represents the normalized radial de Rham class.
proof:
  Identify the restriction with the locally normalized transported form and
  use equality of that class with the radial class.
-/
theorem puncturedExpandedOpenDiskGlobalNormalizedClass_eq_radial
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    (DeRhamExactClosedForms (I := SurfaceRealModel)
        (M := K.puncturedExpandedOpenDisk p (2 * K.closedRadius))
        (A := ℝ) 1).mkQ
        (deRhamClosedFormsRestrictionOfLE
          (I := SurfaceRealModel) (M := X) (A := ℝ)
          (W := K.puncturedExpandedOpenDisk p (2 * K.closedRadius))
          (V := puncturedSurfaceOpen p) inf_le_left 1
          D.puncturedNormalizedClosedOneForm) =
      (DeRhamExactClosedForms (I := SurfaceRealModel)
        (M := K.puncturedExpandedOpenDisk p (2 * K.closedRadius))
        (A := ℝ) 1).mkQ
        (D.puncturedExpandedOpenDiskRadialNormalizedClosedOneForm
          K hdouble hsubset) := by
  rw [D.restrict_puncturedNormalizedClosedOneForm_eq_puncturedExpandedOpenDisk]
  exact D.puncturedExpandedOpenDiskNormalizedClass_eq_radial
    K hdouble hsubset

/-- The first circle coordinate of the radial punctured-disk collar, viewed
as a unit-complex smooth phase. -/
def radialPuncturedCollarPhaseMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (K : ClosedCoordinateDisk X) (p : X)
    (hp_source : p ∈ K.openDisk.chart.source)
    (hcenter : K.openDisk.chart p = K.openDisk.center)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius) :
    ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      (K.puncturedExpandedOpenDisk p (2 * K.closedRadius)) ℂ ∞ where
  val := fun y ↦
    ((K.radialPuncturedCollarDiffeomorph
      p hp_source hcenter hdouble y).1 : ℂ)
  property := by
    exact contMDiff_coe_sphere.comp
      (contMDiff_fst.comp
        (K.radialPuncturedCollarDiffeomorph
          p hp_source hcenter hdouble).contMDiff)

/--
%%handwave
name:
  Unit modulus of the radial collar phase
statement:
  The first circle coordinate of the radial punctured-disk collar has modulus
  one.
proof:
  Its value lies on the unit circle by construction.
-/
theorem norm_radialPuncturedCollarPhaseMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (K : ClosedCoordinateDisk X) (p : X)
    (hp_source : p ∈ K.openDisk.chart.source)
    (hcenter : K.openDisk.chart p = K.openDisk.center)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (y : K.puncturedExpandedOpenDisk p (2 * K.closedRadius)) :
    ‖radialPuncturedCollarPhaseMap K p hp_source hcenter hdouble y‖ = 1 :=
  Circle.norm_coe _

/--
%%handwave
name:
  Formula for the radial collar phase
statement:
  The circle coordinate of the radial collar at \(y\) is
  \[
    \frac{z(y)-z(p)}{|z(y)-z(p)|},
  \]
  where \(z\) is the centered coordinate chart.
proof:
  Expand the normalized-vector definition of the radial collar and rewrite
  inverse norm multiplication as division.
-/
theorem radialPuncturedCollarPhaseMap_apply
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (K : ClosedCoordinateDisk X) (p : X)
    (hp_source : p ∈ K.openDisk.chart.source)
    (hcenter : K.openDisk.chart p = K.openDisk.center)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (y : K.puncturedExpandedOpenDisk p (2 * K.closedRadius)) :
    radialPuncturedCollarPhaseMap K p hp_source hcenter hdouble y =
      (K.openDisk.chart (y : X) - K.openDisk.center) /
        ‖K.openDisk.chart (y : X) - K.openDisk.center‖ := by
  change NormedSpace.normalize
      (K.openDisk.chart (y : X) - K.openDisk.center) = _
  change
    ((‖K.openDisk.chart (y : X) - K.openDisk.center‖⁻¹ : ℝ) : ℂ) *
        (K.openDisk.chart (y : X) - K.openDisk.center) =
      (K.openDisk.chart (y : X) - K.openDisk.center) /
        (‖K.openDisk.chart (y : X) - K.openDisk.center‖ : ℂ)
  rw [div_eq_mul_inv, Complex.ofReal_inv]
  ring

/--
%%handwave
name:
  Coordinate formula for the unrotated vortex phase
statement:
  When the stationary disk uses the vortex chart and is centered at \(p\),
  its unrotated phase is
  \[
    \frac{z(y)-z(p)}{|z(y)-z(p)|}.
  \]
proof:
  Substitute the equal chart and center into the defining radial-germ formula.
-/
theorem puncturedExpandedOpenDiskUnrotatedPhaseMap_eq_radial
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hchart : K.openDisk.chart = D.vortex.chart)
    (hcenter : K.openDisk.center = D.vortex.chart p)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood)
    (y : K.puncturedExpandedOpenDisk p (2 * K.closedRadius)) :
    D.puncturedExpandedOpenDiskUnrotatedPhaseMap K hdouble hsubset y =
      (K.openDisk.chart (y : X) - K.openDisk.center) /
        ‖K.openDisk.chart (y : X) - K.openDisk.center‖ := by
  change
    (D.vortex.chart (y : X) - D.vortex.chart p) /
        ‖D.vortex.chart (y : X) - D.vortex.chart p‖ =
      (K.openDisk.chart (y : X) - K.openDisk.center) /
        ‖K.openDisk.chart (y : X) - K.openDisk.center‖
  rw [hchart, hcenter]

/--
%%handwave
name:
  The unrotated vortex phase is the radial collar circle coordinate
statement:
  On a concentric stationary punctured disk, the unrotated vortex phase
  equals the first \(S^1\)-coordinate of the radial annular diffeomorphism.
proof:
  Both quantities equal the normalized coordinate direction from the center.
-/
theorem puncturedExpandedOpenDiskUnrotatedPhaseMap_eq_radialPuncturedCollarPhaseMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hchart : K.openDisk.chart = D.vortex.chart)
    (hcenter : K.openDisk.center = D.vortex.chart p)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood)
    (y : K.puncturedExpandedOpenDisk p (2 * K.closedRadius)) :
    D.puncturedExpandedOpenDiskUnrotatedPhaseMap K hdouble hsubset y =
      radialPuncturedCollarPhaseMap K p
        (by rw [hchart]; exact D.vortex.left_mem_source)
        (by rw [hchart, hcenter]) hdouble y := by
  rw [D.puncturedExpandedOpenDiskUnrotatedPhaseMap_eq_radial
      K hchart hcenter hdouble hsubset y,
    radialPuncturedCollarPhaseMap_apply]

/--
%%handwave
name:
  The radial logarithmic form is pulled back from the annulus
statement:
  The logarithmic one-form of the unrotated puncture phase is the pullback,
  under the radial annular diffeomorphism, of the standard circle-coordinate
  logarithmic form on \(S^1\times\mathbb R\).
proof:
  The two circle primitives agree pointwise because both are the first circle
  coordinate; equality of unit phases gives equality of their logarithmic
  one-forms.
-/
theorem puncturedExpandedOpenDiskRadialOneForm_eq_pullback_annular
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hchart : K.openDisk.chart = D.vortex.chart)
    (hcenter : K.openDisk.center = D.vortex.chart p)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    smoothUnitPhaseOneForm SurfaceRealModel
        (D.puncturedExpandedOpenDiskUnrotatedPhaseMap K hdouble hsubset)
        (D.norm_puncturedExpandedOpenDiskUnrotatedPhaseMap
          K hdouble hsubset) =
      smoothFormsPullbackDiffeomorph SurfaceRealModel AnnularCylinderModel
        (K.radialPuncturedCollarDiffeomorph p
          (by rw [hchart]; exact D.vortex.left_mem_source)
          (by rw [hchart, hcenter]) hdouble) 1
        (annularCutRotationClosedOneForm (circleAntipode 1)).1 := by
  let hp_source : p ∈ K.openDisk.chart.source := by
    rw [hchart]
    exact D.vortex.left_mem_source
  let hp_center : K.openDisk.chart p = K.openDisk.center := by
    rw [hchart, hcenter]
  let phi := K.radialPuncturedCollarDiffeomorph p hp_source hp_center hdouble
  let P :=
    (smoothUnitPhaseCirclePrimitive AnnularCylinderModel
      (annularCutRotationPhase (circleAntipode 1))
      (norm_annularCutRotationPhase (circleAntipode 1))).pullbackDiffeomorph
        AnnularCylinderModel SurfaceRealModel phi
  let Q := smoothUnitPhaseCirclePrimitive SurfaceRealModel
    (D.puncturedExpandedOpenDiskUnrotatedPhaseMap K hdouble hsubset)
    (D.norm_puncturedExpandedOpenDiskUnrotatedPhaseMap K hdouble hsubset)
  symm
  apply SmoothCirclePrimitive.oneForm_eq_of_phase_eq SurfaceRealModel P Q
  intro y
  change
    (annularCutRotation (circleAntipode 1) (phi y).1 : ℂ) =
      D.puncturedExpandedOpenDiskUnrotatedPhaseMap K hdouble hsubset y
  rw [annularCutRotation_antipode_one]
  exact (D.puncturedExpandedOpenDiskUnrotatedPhaseMap_eq_radialPuncturedCollarPhaseMap
    K hchart hcenter hdouble hsubset y).symm

/--
%%handwave
name:
  The normalized radial form is pulled back from the annulus
statement:
  The normalized radial closed one-form on the punctured disk is the pullback
  of the normalized radial form on the annular cylinder.
proof:
  Pullback is linear and therefore commutes with multiplication by
  \((2\pi)^{-1}\); apply the unnormalized pullback identity.
-/
theorem puncturedExpandedOpenDiskRadialNormalizedClosedOneForm_eq_pullback_annular
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hchart : K.openDisk.chart = D.vortex.chart)
    (hcenter : K.openDisk.center = D.vortex.chart p)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    D.puncturedExpandedOpenDiskRadialNormalizedClosedOneForm
        K hdouble hsubset =
      deRhamClosedFormsPullbackDiffeomorph SurfaceRealModel
        AnnularCylinderModel
        (K.radialPuncturedCollarDiffeomorph p
          (by rw [hchart]; exact D.vortex.left_mem_source)
          (by rw [hchart, hcenter]) hdouble) 1
        (annularRadialNormalizedClosedOneForm (circleAntipode 1)) := by
  apply Subtype.ext
  change
    (2 * Real.pi)⁻¹ •
        smoothUnitPhaseOneForm SurfaceRealModel
          (D.puncturedExpandedOpenDiskUnrotatedPhaseMap K hdouble hsubset)
          (D.norm_puncturedExpandedOpenDiskUnrotatedPhaseMap
            K hdouble hsubset) =
      smoothFormsPullbackDiffeomorph SurfaceRealModel AnnularCylinderModel
        (K.radialPuncturedCollarDiffeomorph p
          (by rw [hchart]; exact D.vortex.left_mem_source)
          (by rw [hchart, hcenter]) hdouble) 1
        ((2 * Real.pi)⁻¹ •
          (annularCutRotationClosedOneForm (circleAntipode 1)).1)
  rw [(smoothFormsPullbackDiffeomorph SurfaceRealModel AnnularCylinderModel
      (K.radialPuncturedCollarDiffeomorph p
        (by rw [hchart]; exact D.vortex.left_mem_source)
        (by rw [hchart, hcenter]) hdouble) 1).map_smul]
  congr 1
  exact D.puncturedExpandedOpenDiskRadialOneForm_eq_pullback_annular
    K hchart hcenter hdouble hsubset

/--
%%handwave
name:
  The local radial class is the annular angular class up to orientation
statement:
  Under the radial annular diffeomorphism, the normalized radial vortex class
  equals either the pullback of the standard angular class or its negative.
proof:
  Pull back the annular theorem identifying the normalized radial class with
  the angular class up to sign; linearity of pullback preserves the negative.
-/
theorem puncturedExpandedOpenDiskRadialNormalizedClass_eq_or_neg_angular
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hchart : K.openDisk.chart = D.vortex.chart)
    (hcenter : K.openDisk.center = D.vortex.chart p)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    let phi := K.radialPuncturedCollarDiffeomorph p
      (by rw [hchart]; exact D.vortex.left_mem_source)
      (by rw [hchart, hcenter]) hdouble
    let radialClass :=
      (DeRhamExactClosedForms (I := SurfaceRealModel)
        (M := K.puncturedExpandedOpenDisk p (2 * K.closedRadius))
        (A := ℝ) 1).mkQ
          (D.puncturedExpandedOpenDiskRadialNormalizedClosedOneForm
            K hdouble hsubset)
    let angularClass :=
      deRhamCohomologyPullbackDiffeomorph SurfaceRealModel
        AnnularCylinderModel phi 1
        ((DeRhamExactClosedForms (I := AnnularCylinderModel)
          (M := Circle × ℝ) (A := ℝ) 1).mkQ
            (annularAngularClosedForm (circleAntipode 1)))
    radialClass = angularClass ∨ radialClass = -angularClass := by
  dsimp only
  rw [D.puncturedExpandedOpenDiskRadialNormalizedClosedOneForm_eq_pullback_annular
    K hchart hcenter hdouble hsubset]
  rcases annularRadialNormalizedClosedOneForm_class_eq_or_neg
      (circleAntipode 1) with h | h
  · left
    have hpull := congrArg
      (deRhamCohomologyPullbackDiffeomorph SurfaceRealModel
        AnnularCylinderModel
        (K.radialPuncturedCollarDiffeomorph p
          (by rw [hchart]; exact D.vortex.left_mem_source)
          (by rw [hchart, hcenter]) hdouble) 1) h
    simpa [deRhamCohomologyPullbackDiffeomorph,
      Submodule.mapQ_apply] using hpull
  · right
    have hpull := congrArg
      (deRhamCohomologyPullbackDiffeomorph SurfaceRealModel
        AnnularCylinderModel
        (K.radialPuncturedCollarDiffeomorph p
          (by rw [hchart]; exact D.vortex.left_mem_source)
          (by rw [hchart, hcenter]) hdouble) 1) h
    have hmapneg :
        (deRhamCohomologyPullbackDiffeomorph SurfaceRealModel
          AnnularCylinderModel
          (K.radialPuncturedCollarDiffeomorph p
            (by rw [hchart]; exact D.vortex.left_mem_source)
            (by rw [hchart, hcenter]) hdouble) 1)
            (-(DeRhamExactClosedForms (I := AnnularCylinderModel)
              (M := Circle × ℝ) (A := ℝ) 1).mkQ
                (annularAngularClosedForm (circleAntipode 1))) =
          -(deRhamCohomologyPullbackDiffeomorph SurfaceRealModel
            AnnularCylinderModel
            (K.radialPuncturedCollarDiffeomorph p
              (by rw [hchart]; exact D.vortex.left_mem_source)
              (by rw [hchart, hcenter]) hdouble) 1)
              ((DeRhamExactClosedForms (I := AnnularCylinderModel)
                (M := Circle × ℝ) (A := ℝ) 1).mkQ
                  (annularAngularClosedForm (circleAntipode 1))) :=
      (deRhamCohomologyPullbackDiffeomorph SurfaceRealModel
        AnnularCylinderModel
        (K.radialPuncturedCollarDiffeomorph p
          (by rw [hchart]; exact D.vortex.left_mem_source)
          (by rw [hchart, hcenter]) hdouble) 1).map_neg _
    rw [hmapneg] at hpull
    simpa [deRhamCohomologyPullbackDiffeomorph,
      Submodule.mapQ_apply] using hpull

set_option synthInstance.maxHeartbeats 100000 in
/--
%%handwave
name:
  The global puncture class on the inner disk is angular up to orientation
statement:
  On the inner half of a concentric stationary disk, the restricted global
  normalized vortex form represents either the pullback of the standard
  angular class from the negative half-cylinder or its negative.
proof:
  First identify the global class on the doubled punctured disk with the
  radial class, then with the annular angular class up to sign.  Restrict this
  equality to the inner half and use compatibility of restriction with the
  side-preserving collar pullback.
-/
theorem puncturedInnerDiskGlobalNormalizedClass_eq_or_neg_angular
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p)
    (K : ClosedCoordinateDisk X)
    (hchart : K.openDisk.chart = D.vortex.chart)
    (hcenter : K.openDisk.center = D.vortex.chart p)
    (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
    (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood) :
    let W := K.puncturedExpandedOpenDisk p (2 * K.closedRadius)
    let phi := K.radialPuncturedCollarDiffeomorph p
      (by rw [hchart]; exact D.vortex.left_mem_source)
      (by rw [hchart, hcenter]) hdouble
    let Q := W ⊓
      ⟨K.toSmoothBoundaryDomain.carrier,
        K.toSmoothBoundaryDomain.isOpen⟩
    let hside : ∀ y : W,
        ((y : X) ∈ K.toSmoothBoundaryDomain.carrier ↔
          (phi y).2 < 0) := fun y ↦
      (K.radialPuncturedCollarDiffeomorph_second_lt_zero_iff p
        (by rw [hchart]; exact D.vortex.left_mem_source)
        (by rw [hchart, hcenter]) hdouble y).symm
    let psi := sidePreservingAnnularCollarDomainRestriction
      K.toSmoothBoundaryDomain W phi hside
    let tauQ : DeRhamClosedForms (I := SurfaceRealModel)
        (M := Q) (A := ℝ) 1 :=
      deRhamClosedFormsRestrictionOfLE (I := SurfaceRealModel) (A := ℝ)
        (inf_le_left.trans inf_le_left) 1
        D.puncturedNormalizedClosedOneForm
    let betaQ : DeRhamClosedForms (I := SurfaceRealModel)
        (M := Q) (A := ℝ) 1 :=
      deRhamClosedFormsPullbackDiffeomorph SurfaceRealModel
        AnnularCylinderModel psi 1
        (deRhamClosedFormsRestrictionToOpen
          (I := AnnularCylinderModel) (A := ℝ)
          negativeAnnularCylinderOpen 1
          (annularAngularClosedForm (circleAntipode 1)))
    (DeRhamExactClosedForms (I := SurfaceRealModel)
        (M := Q) (A := ℝ) 1).mkQ tauQ =
        (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := Q) (A := ℝ) 1).mkQ betaQ ∨
      (DeRhamExactClosedForms (I := SurfaceRealModel)
        (M := Q) (A := ℝ) 1).mkQ tauQ =
        -(DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := Q) (A := ℝ) 1).mkQ betaQ := by
  dsimp only
  let W := K.puncturedExpandedOpenDisk p (2 * K.closedRadius)
  let hp_source : p ∈ K.openDisk.chart.source := by
    rw [hchart]
    exact D.vortex.left_mem_source
  let hp_center : K.openDisk.chart p = K.openDisk.center := by
    rw [hchart, hcenter]
  let phi := K.radialPuncturedCollarDiffeomorph p
    hp_source hp_center hdouble
  let Q : TopologicalSpace.Opens X := W ⊓
    ⟨K.toSmoothBoundaryDomain.carrier,
      K.toSmoothBoundaryDomain.isOpen⟩
  let hside : ∀ y : W,
      ((y : X) ∈ K.toSmoothBoundaryDomain.carrier ↔
        (phi y).2 < 0) := fun y ↦
    (K.radialPuncturedCollarDiffeomorph_second_lt_zero_iff p
      hp_source hp_center hdouble y).symm
  let psi := sidePreservingAnnularCollarDomainRestriction
    K.toSmoothBoundaryDomain W phi hside
  let tauW : DeRhamClosedForms (I := SurfaceRealModel)
      (M := W) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionOfLE (I := SurfaceRealModel) (A := ℝ)
      inf_le_left 1 D.puncturedNormalizedClosedOneForm
  let betaW : DeRhamClosedForms (I := SurfaceRealModel)
      (M := W) (A := ℝ) 1 :=
    deRhamClosedFormsPullbackDiffeomorph SurfaceRealModel
      AnnularCylinderModel phi 1
      (annularAngularClosedForm (circleAntipode 1))
  let tauQ : DeRhamClosedForms (I := SurfaceRealModel)
      (M := Q) (A := ℝ) 1 :=
    deRhamClosedFormsRestrictionOfLE (I := SurfaceRealModel) (A := ℝ)
      (inf_le_left.trans inf_le_left) 1
      D.puncturedNormalizedClosedOneForm
  let betaQ : DeRhamClosedForms (I := SurfaceRealModel)
      (M := Q) (A := ℝ) 1 :=
    deRhamClosedFormsPullbackDiffeomorph SurfaceRealModel
      AnnularCylinderModel psi 1
      (deRhamClosedFormsRestrictionToOpen
        (I := AnnularCylinderModel) (A := ℝ)
        negativeAnnularCylinderOpen 1
        (annularAngularClosedForm (circleAntipode 1)))
  have htauRadial :=
    D.puncturedExpandedOpenDiskGlobalNormalizedClass_eq_radial
      K hdouble hsubset
  have hradial :=
    D.puncturedExpandedOpenDiskRadialNormalizedClass_eq_or_neg_angular
      K hchart hcenter hdouble hsubset
  have hW :
      (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := W) (A := ℝ) 1).mkQ tauW =
          (DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := W) (A := ℝ) 1).mkQ betaW ∨
        (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := W) (A := ℝ) 1).mkQ tauW =
          -(DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := W) (A := ℝ) 1).mkQ betaW := by
    have htauRadial' := htauRadial
    have hradial' := hradial
    simpa [W, phi, betaW] using Or.imp
      (fun h ↦ htauRadial'.trans h)
      (fun h ↦ htauRadial'.trans h) hradial'
  have htauRestrict :
      deRhamClosedFormsRestrictionOfLE (I := SurfaceRealModel) (A := ℝ)
          inf_le_left 1 tauW = tauQ := by
    apply Subtype.ext
    change
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          inf_le_left 1
          (restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X)
            (A := ℝ) inf_le_left 1
            D.puncturedNormalizedClosedOneForm.1) =
        restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X)
          (A := ℝ) (inf_le_left.trans inf_le_left) 1
          D.puncturedNormalizedClosedOneForm.1
    exact restrictSmoothFormsOfLE_comp
      (I := SurfaceRealModel) (M := X) (A := ℝ)
      (show W ≤ puncturedSurfaceOpen p from inf_le_left)
      (show Q ≤ W from inf_le_left) 1
      D.puncturedNormalizedClosedOneForm.1
  have hbetaRestrict :
      deRhamClosedFormsRestrictionOfLE (I := SurfaceRealModel) (A := ℝ)
          inf_le_left 1 betaW = betaQ := by
    apply Subtype.ext
    change
      restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X) (A := ℝ)
          inf_le_left 1
          (smoothFormsPullbackDiffeomorph SurfaceRealModel
            AnnularCylinderModel phi 1
            (annularAngularClosedForm (circleAntipode 1)).1) =
        smoothFormsPullbackDiffeomorph SurfaceRealModel
          AnnularCylinderModel psi 1
          (restrictSmoothFormsToOpen (I := AnnularCylinderModel) (A := ℝ)
            negativeAnnularCylinderOpen 1
            (annularAngularClosedForm (circleAntipode 1)).1)
    exact restrict_annularPullback_domain_eq_pullback_negative
      K.toSmoothBoundaryDomain W phi hside
      (annularAngularClosedForm (circleAntipode 1)).1
  let res : DeRhamCohomology (I := SurfaceRealModel)
        (M := W) (A := ℝ) 1 →ₗ[ℝ]
      DeRhamCohomology (I := SurfaceRealModel)
        (M := Q) (A := ℝ) 1 :=
    deRhamCohomologyRestrictionOfLE (I := SurfaceRealModel)
      (A := ℝ) inf_le_left 1
  rcases hW with hW | hW
  · left
    have h := congrArg res hW
    change
      (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := Q) (A := ℝ) 1).mkQ
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tauW) =
        (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := Q) (A := ℝ) 1).mkQ
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 betaW) at h
    rw [htauRestrict, hbetaRestrict] at h
    exact h
  · right
    have h := congrArg res hW
    have hneg := res.map_neg
      ((DeRhamExactClosedForms (I := SurfaceRealModel)
        (M := W) (A := ℝ) 1).mkQ betaW)
    rw [hneg] at h
    change
      (DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := Q) (A := ℝ) 1).mkQ
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tauW) =
        -(DeRhamExactClosedForms (I := SurfaceRealModel)
          (M := Q) (A := ℝ) 1).mkQ
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 betaW) at h
    rw [htauRestrict, hbetaRestrict] at h
    exact h

/--
%%handwave
name:
  Local radial normal form for a transported puncture vortex
statement:
  Every transported puncture vortex admits a concentric coordinate disk whose
  doubled punctured disk lies in the stationary radial neighborhood, on which
  the normalized transported class equals the radial class and the unrotated
  phase is \((z-z(p))/|z-z(p)|\).
proof:
  Choose the stationary radial coordinate disk supplied by the vortex germ.
  Apply the local equality of normalized classes and the coordinate formula
  for the unrotated phase on that disk.
-/
theorem exists_localRadialNormalizedClassCertificate
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    ∃ K : ClosedCoordinateDisk X,
      ∃ (_hchart : K.openDisk.chart = D.vortex.chart)
        (_hcenter : K.openDisk.center = D.vortex.chart p)
        (hdouble : 2 * K.closedRadius ≤ K.openDisk.radius)
        (hsubset : K.openDisk.carrier ⊆ D.localRadialNeighborhood),
        (DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := K.puncturedExpandedOpenDisk p (2 * K.closedRadius))
            (A := ℝ) 1).mkQ
            (D.puncturedExpandedOpenDiskNormalizedClosedOneForm
              K hdouble hsubset) =
          (DeRhamExactClosedForms (I := SurfaceRealModel)
            (M := K.puncturedExpandedOpenDisk p (2 * K.closedRadius))
            (A := ℝ) 1).mkQ
            (D.puncturedExpandedOpenDiskRadialNormalizedClosedOneForm
              K hdouble hsubset) ∧
        ∀ y : K.puncturedExpandedOpenDisk p (2 * K.closedRadius),
          D.puncturedExpandedOpenDiskUnrotatedPhaseMap
              K hdouble hsubset y =
            (K.openDisk.chart (y : X) - K.openDisk.center) /
              ‖K.openDisk.chart (y : X) - K.openDisk.center‖ := by
  rcases D.exists_localRadialClosedCoordinateDisk with
    ⟨K, hchart, hcenter, hdouble, hsubset⟩
  refine ⟨K, hchart, hcenter, hdouble, hsubset,
    D.puncturedExpandedOpenDiskNormalizedClass_eq_radial
      K hdouble hsubset, ?_⟩
  intro y
  exact D.puncturedExpandedOpenDiskUnrotatedPhaseMap_eq_radial
    K hchart hcenter hdouble hsubset y

end PuncturedAtlasVortexCirclePrimitiveData

end

end JJMath.Uniformization
