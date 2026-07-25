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

/--
%%handwave
name: An unpunctured open neighborhood of the pole on which both the atlas radial factorization and the stationary-transport identity hold
statement:
  Define the stationary radial neighborhood of the puncture $p$ as the
  intersection of the initial atlas vortex-germ neighborhood with the
  interior of the coordinate disk on which the infinite transport is
  stationary.
-/
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
name: The portion of the initial atlas-vortex germ lying in the disk on which the infinite transport is stationary
statement:
  Inside the punctured left atlas germ, define the open subgerm consisting
  of points lying in the interior of the stationary coordinate disk.
-/
def localRadialGerm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    TopologicalSpace.Opens D.vortex.leftGerm :=
  ⟨{x | (x : X) ∈ interior D.localDisk.carrier},
    isOpen_interior.preimage
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_subtype_val))⟩

/--
%%handwave
name: The local radial germ included into the globally punctured surface
statement:
  Define the canonical inclusion of the stationary local radial germ into
  the punctured surface $X\setminus\{p\}$.
-/
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

/--
%%handwave
name: The transported global phase restricted to its stationary radial germ
statement:
  Restrict the transported global phase $\Phi:X\setminus\{p\}\to S^1$ to
  the stationary local radial germ.
-/
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

/--
%%handwave
name: The atlas radial phase restricted to the stationary local germ
statement:
  Restrict the rotated atlas radial phase from the initial left vortex germ
  to the smaller stationary local germ.
-/
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
name: The ordinary, unrotated coordinate direction on the stationary local germ
statement:
  On the stationary local germ, define the unrotated coordinate direction
  \[
    x\longmapsto \frac{e(x)-e(p)}{\lVert e(x)-e(p)\rVert}.
  \]
-/
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

/--
%%handwave
name: The atlas denominator correction restricted to the stationary local germ
statement:
  Restrict the smooth denominator-argument correction from the initial
  atlas vortex germ to the stationary local germ.
-/
def localRadialGermCorrectionSmooth
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]
    {p : X} (D : PuncturedAtlasVortexCirclePrimitiveData X p) :
    C^∞⟮SurfaceRealModel, D.localRadialGerm; ℝ⟯ where
  val := fun x ↦ D.vortex.leftGermCorrectionSmooth x.1
  property := D.vortex.leftGermCorrectionSmooth.contMDiff.comp
    contMDiff_subtype_val

/--
%%handwave
name: The total smooth correction after absorbing the constant rotation into the denominator correction
statement:
  Define
  \[
    H(x)=\arg\!\left(
      \frac{\lVert e(p)-e(q)\rVert}{e(p)-e(q)}
    \right)+h(x),
  \]
  where $q$ is the terminal vortex endpoint and $h$ is the denominator
  correction; this absorbs the constant rotation relating the rotated and
  ordinary radial phases.
-/
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

end PuncturedAtlasVortexCirclePrimitiveData

end

end JJMath.Uniformization
