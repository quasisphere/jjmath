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

/--
%%handwave
name:
  Smooth restriction of the codomain to an open subset
statement:
  Let \(f:M\to N\) be a smooth map whose image lies in an open subset
  \(V\subseteq N\).  Then the same map regarded as
  \[
    M\longrightarrow V,\qquad x\longmapsto f(x),
  \]
  is smooth.
proof:
  Near each \(f(x)\), the inclusion-retract map from \(N\) to \(V\) agrees
  with the identity.  Compose this local smooth retract with \(f\) and use
  local equality.
-/
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

/--
%%handwave
name:
  The pole lies in the stationary radial neighborhood
statement:
  The puncture \(p\) belongs to the intersection of the initial vortex-germ
  neighborhood and the interior of the local coordinate disk.
proof:
  The atlas-vortex data place the initial endpoint in its germ neighborhood
  and the pole in the interior of the local disk.
-/
theorem pole_mem_localRadialNeighborhood
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    p ∈ D.localRadialNeighborhood :=
  ⟨D.vortex.left_mem_leftGermNeighborhood, D.pole_mem_interior⟩

/--
%%handwave
name:
  A closed coordinate disk inside the stationary radial neighborhood
statement:
  There is a closed coordinate disk \(K\), centered at the pole in the
  original vortex chart, such that
  \[
    2r_K\le R_K
    \quad\text{and}\quad
    \operatorname{OpenDisk}(K)\subseteq N,
  \]
  where \(r_K\) is its closed radius, \(R_K\) its chart radius, and \(N\) the
  stationary radial neighborhood.
proof:
  Pull the open neighborhood \(N\) into the vortex chart and choose a
  Euclidean ball of radius \(R\) about the pole inside it.  Taking closed
  radius \(R/3\) leaves the required doubled-radius margin and ensures that
  the resulting coordinate disk lies in \(N\).
-/
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

/--
%%handwave
name:
  A stationary radial disk inside a prescribed neighborhood
statement:
  If \(O\) is an open neighborhood of the puncture, then the disk \(K\) may
  be chosen with
  \[
    2r_K\le R_K,\qquad
    \operatorname{OpenDisk}(K)\subseteq N\cap O,
  \]
  while using the original vortex chart and center.
proof:
  Repeat the coordinate-ball construction inside the open intersection
  \(N\cap O\), again taking one third of the available chart radius.
-/
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

/--
%%handwave
name:
  Smooth inclusion of the stationary germ into the punctured surface
statement:
  The natural map from the stationary local radial germ into the initial
  punctured vortex neighborhood is smooth.
proof:
  Its ambient map is the iterated subtype inclusion, hence smooth, and its
  image lies in the required open punctured neighborhood.  Restricting the
  codomain to that open subset preserves smoothness.
-/
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

/--
%%handwave
name:
  Unit norm of the transported phase on the radial germ
statement:
  For every point \(x\) of the stationary local germ, the transported phase
  satisfies
  \[
    |\Phi(x)|=1.
  \]
proof:
  This is the unit-norm property of the global transported phase, restricted
  along the inclusion of the local germ.
-/
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

/--
%%handwave
name:
  Unit norm of the rotated radial phase
statement:
  The atlas radial phase restricted to the stationary germ has modulus one
  at every point.
proof:
  The unrestricted radial germ phase is circle-valued; restriction does not
  change its values.
-/
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

/--
%%handwave
name:
  Unit norm of the unrotated radial phase
statement:
  The ordinary coordinate-direction phase on the stationary puncture germ
  has modulus one at every point.
proof:
  This is the unit-norm property of the unrotated atlas radial phase after
  restriction to the smaller germ.
-/
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

/--
%%handwave
name:
  Radial factorization of the transported puncture phase
statement:
  On the stationary local germ, the transported phase \(\Phi\) satisfies
  \[
    \Phi(x)=R(x)e^{i h(x)},
  \]
  where \(R\) is the rotated radial phase and \(h\) is a smooth real-valued
  correction.
proof:
  Stationarity of the infinite transport identifies \(\Phi\) with the
  initial atlas-vortex phase on this germ.  Apply the atlas radial
  factorization and restrict its correction function.
-/
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

/--
%%handwave
name:
  Unrotated radial factorization of the transported puncture phase
statement:
  On the stationary local germ,
  \[
    \Phi(x)=U(x)e^{iH(x)},
  \]
  where \(U\) is the unrotated coordinate-direction phase and \(H\) is a
  smooth real-valued total correction.
proof:
  The rotated radial phase is a constant unit complex multiple of \(U\).
  Write that constant as \(e^{i\alpha}\) using its argument, and absorb
  \(\alpha\) into the preceding smooth correction.
-/
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

/--
%%handwave
name:
  The transported phase form differs exactly from the radial phase form
statement:
  If \(\omega_\Phi\) and \(\omega_R\) are the logarithmic real one-forms of
  the transported and rotated radial phases, then on the stationary germ
  \[
    \omega_\Phi=\omega_R+dh.
  \]
proof:
  The phase factorization \(\Phi=R e^{ih}\) implies the logarithmic
  one-form identity by the product rule for circle-valued phases.
-/
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

/--
%%handwave
name:
  The transported phase form differs exactly from the coordinate angular form
statement:
  If \(\omega_U\) is the logarithmic one-form of the unrotated coordinate
  phase, then on the stationary germ
  \[
    \omega_\Phi=\omega_U+dH,
  \]
  where \(H\) is the smooth total correction.
proof:
  Apply the logarithmic one-form product identity to
  \(\Phi=Ue^{iH}\).
-/
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
