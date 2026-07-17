import JJMath.Manifold.CirclePrimitive
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A compactly supported planar vortex pair

This file develops the local circle-valued construction used to move one
unit of winding through a coordinate corridor.  The basic rational function
has one zero and one pole.  Its unit phase therefore has opposite angular
germs at the two marked points.  On the exterior of the unit disk the
rational function lies in the slit plane, so its phase has a canonical
smooth real argument; a radial cutoff can consequently flatten the phase to
one at infinity.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

noncomputable section

/-- The plane with the two standard vortex points `-1` and `1` removed. -/
def planarVortexPairOpen : TopologicalSpace.Opens ℂ :=
  ⟨{z : ℂ | z ≠ -1 ∧ z ≠ 1}, isOpen_ne.inter isOpen_ne⟩

@[simp]
theorem mem_planarVortexPairOpen_iff (z : ℂ) :
    z ∈ planarVortexPairOpen ↔ z ≠ -1 ∧ z ≠ 1 := by
  rfl

/-- The standard rational function with a zero at `-1` and a pole at `1`. -/
def planarVortexRatio (z : ℂ) : ℂ := (z + 1) / (z - 1)

theorem planarVortexRatio_ne_zero (z : planarVortexPairOpen) :
    planarVortexRatio z ≠ 0 := by
  rw [planarVortexRatio, div_ne_zero_iff]
  have hz := (mem_planarVortexPairOpen_iff z).mp z.2
  constructor
  · intro h
    exact hz.1 (eq_neg_of_add_eq_zero_left h)
  · intro h
    exact hz.2 (sub_eq_zero.mp h)

/-- The unit phase of the standard zero--pole pair. -/
def planarVortexPairPhase (z : planarVortexPairOpen) : ℂ :=
  planarVortexRatio z / ‖planarVortexRatio z‖

theorem norm_planarVortexPairPhase (z : planarVortexPairOpen) :
    ‖planarVortexPairPhase z‖ = 1 := by
  rw [planarVortexPairPhase, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_norm, div_self]
  exact norm_ne_zero_iff.mpr (planarVortexRatio_ne_zero z)

theorem contDiffAt_planarVortexRatio_of_ne_one
    {z : ℂ} (hz : z ≠ 1) :
    ContDiffAt ℝ ∞ planarVortexRatio z := by
  unfold planarVortexRatio
  have hnum : ContDiffAt ℝ ∞ (fun w : ℂ ↦ w + 1) z :=
    contDiffAt_id.add contDiffAt_const
  have hden : ContDiffAt ℝ ∞ (fun w : ℂ ↦ w - 1) z :=
    contDiffAt_id.sub contDiffAt_const
  exact hnum.mul (hden.inv (sub_ne_zero.mpr hz))

theorem contMDiff_planarVortexRatio :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : planarVortexPairOpen ↦ planarVortexRatio z) := by
  intro z
  rw [contMDiffAt_subtype_iff]
  exact (contDiffAt_planarVortexRatio_of_ne_one
    ((mem_planarVortexPairOpen_iff z).mp z.2).2).contMDiffAt

theorem contMDiff_planarVortexPairPhase :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      planarVortexPairPhase := by
  intro z
  unfold planarVortexPairPhase
  apply (contMDiffAt_subtype_iff
    (f := fun w : ℂ ↦
      planarVortexRatio w / ((‖planarVortexRatio w‖ : ℝ) : ℂ))
    (x := z)).mpr
  have hzmem := (mem_planarVortexPairOpen_iff z).mp z.2
  have hratio : ContDiffAt ℝ ∞ planarVortexRatio (z : ℂ) :=
    contDiffAt_planarVortexRatio_of_ne_one hzmem.2
  have hratioNe : planarVortexRatio (z : ℂ) ≠ 0 :=
    planarVortexRatio_ne_zero z
  have hnorm : ContDiffAt ℝ ∞
      (fun w : ℂ ↦ ‖planarVortexRatio w‖) (z : ℂ) :=
    hratio.norm ℝ hratioNe
  have hnormComplex : ContDiffAt ℝ ∞
      (fun w : ℂ ↦ ((‖planarVortexRatio w‖ : ℝ) : ℂ)) (z : ℂ) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (z : ℂ) hnorm
  exact (hratio.mul (hnormComplex.inv (by
    exact_mod_cast norm_ne_zero_iff.mpr hratioNe))).contMDiffAt

/-- Outside the closed unit disk, the standard vortex ratio is in the slit
plane and hence has its principal smooth logarithm. -/
theorem planarVortexRatio_mem_slitPlane_of_one_lt_norm
    {z : ℂ} (hz : 1 < ‖z‖) :
    planarVortexRatio z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  rw [planarVortexRatio, Complex.div_re]
  have hden : 0 < Complex.normSq (z - 1) :=
    Complex.normSq_pos.mpr (by
      intro h
      have hzone : z = 1 := sub_eq_zero.mp h
      subst z
      norm_num at hz)
  have hnormSq : 1 < Complex.normSq z := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z]
  rw [Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.add_im, Complex.sub_im, Complex.one_im]
  rw [← add_div]
  apply div_pos
  · rw [Complex.normSq_apply] at hnormSq
    nlinarith
  · exact hden

/-- The principal argument of the standard vortex ratio on the exterior of
the unit disk. -/
def planarVortexOuterOpen : TopologicalSpace.Opens ℂ :=
  ⟨{z : ℂ | 1 < ‖z‖}, isOpen_lt continuous_const continuous_norm⟩

/-- The principal argument of the standard vortex ratio on the exterior of
the unit disk. -/
def planarVortexOuterArgument (z : planarVortexOuterOpen) : ℝ :=
  (Complex.log (planarVortexRatio z)).im

theorem contMDiff_planarVortexOuterArgument :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞
      planarVortexOuterArgument := by
  have hratio : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : planarVortexOuterOpen ↦ planarVortexRatio z) := by
    intro z
    rw [contMDiffAt_subtype_iff]
    apply (contDiffAt_planarVortexRatio_of_ne_one ?_).contMDiffAt
    intro h
    have hnorm : ‖(z : ℂ)‖ = 1 := by rw [h]; norm_num
    have hz : 1 < ‖(z : ℂ)‖ := z.2
    exact (ne_of_gt hz) hnorm
  have hlogR : ContDiffOn ℝ ∞ Complex.log Complex.slitPlane := by
    exact @ContDiffOn.restrict_scalars ℝ inferInstance
      ℂ inferInstance inferInstance ℂ inferInstance inferInstance
      Complex.slitPlane Complex.log ∞
      ℂ inferInstance inferInstance inferInstance
      (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ)
      inferInstance (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ)
      ((analyticOnNhd_id.clog (fun z hz ↦ hz)).contDiffOn
        Complex.isOpen_slitPlane.uniqueDiffOn)
  have hlogM : ContMDiffOn (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞ Complex.log Complex.slitPlane :=
    contMDiffOn_iff_contDiffOn.mpr hlogR
  have hlog : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : planarVortexOuterOpen ↦
        Complex.log (planarVortexRatio z)) := by
    rw [← contMDiffOn_univ]
    exact hlogM.comp hratio.contMDiffOn (by
      intro z _
      exact planarVortexRatio_mem_slitPlane_of_one_lt_norm z.2)
  have him : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℝ) ∞ (fun z : ℂ ↦ z.im) :=
    Complex.imCLM.contDiff.contMDiff
  exact him.comp hlog

/-- The imaginary part of a logarithm is an argument for the unit phase. -/
theorem complex_exp_im_log_mul_I_eq_div_norm
    {w : ℂ} (hw : w ≠ 0) :
    Complex.exp ((((Complex.log w).im : ℝ) : ℂ) * Complex.I) =
      w / ‖w‖ := by
  have harg : ((((Complex.log w).im : ℝ) : ℂ) * Complex.I) =
      Complex.log w - (((Complex.log w).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [harg, Complex.exp_sub, Complex.exp_log hw, ← Complex.ofReal_exp,
    Complex.log_re, Real.exp_log (norm_pos_iff.mpr hw)]

/-- Regard a point of the exterior of the unit disk as a point of the
twice-punctured plane. -/
def planarVortexOuterToPair (z : planarVortexOuterOpen) :
    planarVortexPairOpen := by
  refine ⟨z, ?_⟩
  rw [mem_planarVortexPairOpen_iff]
  constructor <;> intro h
  · have hz : ‖(z : ℂ)‖ = 1 := by rw [h]; norm_num
    exact (ne_of_gt z.2) hz
  · have hz : ‖(z : ℂ)‖ = 1 := by rw [h]; norm_num
    exact (ne_of_gt z.2) hz

theorem planarVortexOuterArgument_is_argument
    (z : planarVortexOuterOpen) :
    Complex.exp (((planarVortexOuterArgument z : ℝ) : ℂ) * Complex.I) =
      planarVortexPairPhase (planarVortexOuterToPair z) := by
  exact complex_exp_im_log_mul_I_eq_div_norm
    (planarVortexRatio_ne_zero (planarVortexOuterToPair z))

/-- A radial cutoff which is zero up to radius two and one from radius
three onwards.  It is only used on the exterior of the unit disk, where the
norm is smooth. -/
def planarVortexOuterCutoff (z : planarVortexOuterOpen) : ℝ :=
  Real.smoothTransition (‖(z : ℂ)‖ - 2)

theorem contMDiff_planarVortexOuterNorm :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : planarVortexOuterOpen ↦ ‖(z : ℂ)‖) := by
  intro z
  apply (contMDiffAt_subtype_iff
    (f := fun w : ℂ ↦ ‖w‖) (x := z)).mpr
  apply (contDiffAt_norm ℝ ?_).contMDiffAt
  intro hz
  have hnorm : ‖(z : ℂ)‖ = 0 := by rw [hz]; simp
  have hzpos : 1 < ‖(z : ℂ)‖ := z.2
  linarith

theorem contMDiff_planarVortexOuterCutoff :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞
      planarVortexOuterCutoff := by
  unfold planarVortexOuterCutoff
  exact Real.smoothTransition.contDiff.contMDiff.comp
    (contMDiff_planarVortexOuterNorm.sub contMDiff_const)

theorem planarVortexOuterCutoff_eq_zero_of_norm_lt_two
    (z : planarVortexOuterOpen) (hz : ‖(z : ℂ)‖ < 2) :
    planarVortexOuterCutoff z = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

theorem planarVortexOuterCutoff_eq_one_of_three_le_norm
    (z : planarVortexOuterOpen) (hz : 3 ≤ ‖(z : ℂ)‖) :
    planarVortexOuterCutoff z = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

/-- The exterior logarithmic argument, switched off between radii two and
three. -/
def planarVortexFlattenedOuterArgument
    (z : planarVortexOuterOpen) : ℝ :=
  (1 - planarVortexOuterCutoff z) * planarVortexOuterArgument z

theorem contMDiff_planarVortexFlattenedOuterArgument :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞
      planarVortexFlattenedOuterArgument := by
  unfold planarVortexFlattenedOuterArgument
  exact (contMDiff_const.sub contMDiff_planarVortexOuterCutoff).mul
    contMDiff_planarVortexOuterArgument

/-- The vortex-pair phase on the exterior, flattened to one outside radius
three. -/
def planarVortexFlattenedOuterPhase
    (z : planarVortexOuterOpen) : ℂ :=
  Complex.exp
    (((planarVortexFlattenedOuterArgument z : ℝ) : ℂ) * Complex.I)

theorem contMDiff_planarVortexFlattenedOuterPhase :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      planarVortexFlattenedOuterPhase := by
  unfold planarVortexFlattenedOuterPhase
  have hargComplex : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : planarVortexOuterOpen ↦
        ((planarVortexFlattenedOuterArgument z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.contMDiff.comp
      contMDiff_planarVortexFlattenedOuterArgument
  have hmulI : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞ (fun z : ℂ ↦ z * Complex.I) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  exact Complex.contDiff_exp.contMDiff.comp (hmulI.comp hargComplex)

theorem planarVortexFlattenedOuterPhase_eq_pairPhase_of_norm_lt_two
    (z : planarVortexOuterOpen) (hz : ‖(z : ℂ)‖ < 2) :
    planarVortexFlattenedOuterPhase z =
      planarVortexPairPhase (planarVortexOuterToPair z) := by
  rw [planarVortexFlattenedOuterPhase,
    planarVortexFlattenedOuterArgument,
    planarVortexOuterCutoff_eq_zero_of_norm_lt_two z hz]
  norm_num
  exact planarVortexOuterArgument_is_argument z

theorem planarVortexFlattenedOuterPhase_eq_one_of_three_le_norm
    (z : planarVortexOuterOpen) (hz : 3 ≤ ‖(z : ℂ)‖) :
    planarVortexFlattenedOuterPhase z = 1 := by
  rw [planarVortexFlattenedOuterPhase,
    planarVortexFlattenedOuterArgument,
    planarVortexOuterCutoff_eq_one_of_three_le_norm z hz]
  norm_num

/-! ## Gluing the flattened exterior phase -/

/-- Local version of smooth codomain restriction to an open submanifold.
This is kept private to avoid adding another public copy of the general
manifold helper. -/
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
    (hf : ContMDiff I J n f) (U : TopologicalSpace.Opens N)
    (hmem : ∀ x, f x ∈ U) :
    ContMDiff I J n (fun x ↦ (⟨f x, hmem x⟩ : U)) := by
  classical
  intro x
  let qU : U := ⟨f x, hmem x⟩
  let retract : N → U := fun y ↦
    if hy : y ∈ U then ⟨y, hy⟩ else qU
  have hretract : ContMDiffAt J J n retract (f x) := by
    rw [← contMDiffAt_subtype_iff (U := U) (x := qU)]
    have heq : (fun y : U ↦ retract y) = id := by
      funext y
      simp [retract]
    rw [heq]
    exact contMDiffAt_id
  have hcomp := hretract.comp x (hf x)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [retract, hmem]

/-- The inner patch on which the unflattened rational phase is used. -/
def planarVortexInnerPatch :
    TopologicalSpace.Opens planarVortexPairOpen :=
  ⟨{z | ‖((z : planarVortexPairOpen) : ℂ)‖ < 2}, by
    exact isOpen_lt (by fun_prop) continuous_const⟩

/-- The exterior patch on which the principal logarithm is available. -/
def planarVortexOuterPatch :
    TopologicalSpace.Opens planarVortexPairOpen :=
  ⟨{z | 1 < ‖((z : planarVortexPairOpen) : ℂ)‖}, by
    exact isOpen_lt continuous_const (by fun_prop)⟩

/-- Forget the redundant puncture proof on the exterior patch. -/
def planarVortexOuterPatchToOuter
    (z : planarVortexOuterPatch) : planarVortexOuterOpen :=
  ⟨((z : planarVortexPairOpen) : ℂ), z.2⟩

theorem contMDiff_planarVortexOuterPatchToOuter :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      planarVortexOuterPatchToOuter := by
  have hambient : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : planarVortexOuterPatch ↦
        (((z : planarVortexPairOpen) : ℂ))) :=
    contMDiff_subtype_val.comp contMDiff_subtype_val
  exact contMDiffCodRestrictOpen hambient planarVortexOuterOpen (fun z ↦ z.2)

/-- The compactly supported standard vortex-pair phase. -/
def planarVortexCompactPhase (z : planarVortexPairOpen) : ℂ := by
  classical
  exact if hz : 1 < ‖(z : ℂ)‖ then
    planarVortexFlattenedOuterPhase ⟨(z : ℂ), hz⟩
  else planarVortexPairPhase z

theorem planarVortexCompactPhase_eq_pairPhase_of_norm_lt_two
    (z : planarVortexPairOpen) (hz : ‖(z : ℂ)‖ < 2) :
    planarVortexCompactPhase z = planarVortexPairPhase z := by
  classical
  by_cases hout : 1 < ‖(z : ℂ)‖
  · rw [planarVortexCompactPhase, dif_pos hout,
      planarVortexFlattenedOuterPhase_eq_pairPhase_of_norm_lt_two
        ⟨(z : ℂ), hout⟩ hz]
    congr 1
  · rw [planarVortexCompactPhase, dif_neg hout]

theorem planarVortexCompactPhase_eq_flattened_of_one_lt_norm
    (z : planarVortexPairOpen) (hz : 1 < ‖(z : ℂ)‖) :
    planarVortexCompactPhase z =
      planarVortexFlattenedOuterPhase ⟨(z : ℂ), hz⟩ := by
  simp [planarVortexCompactPhase, hz]

theorem contMDiff_planarVortexCompactPhase :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      planarVortexCompactPhase := by
  apply contMDiff_of_contMDiffOn_union_of_isOpen
  · have hraw : ContMDiff (modelWithCornersSelf ℝ ℂ)
        (modelWithCornersSelf ℝ ℂ) ∞
        (fun z : planarVortexPairOpen ↦ planarVortexPairPhase z) :=
      contMDiff_planarVortexPairPhase
    exact hraw.contMDiffOn.congr (fun z hz ↦
      planarVortexCompactPhase_eq_pairPhase_of_norm_lt_two z hz)
  · have hflat : ContMDiff (modelWithCornersSelf ℝ ℂ)
        (modelWithCornersSelf ℝ ℂ) ∞
        (fun z : planarVortexOuterPatch ↦
          planarVortexFlattenedOuterPhase
            (planarVortexOuterPatchToOuter z)) :=
      contMDiff_planarVortexFlattenedOuterPhase.comp
        contMDiff_planarVortexOuterPatchToOuter
    intro z hz
    apply ContMDiffAt.contMDiffWithinAt
    let zU : planarVortexOuterPatch := ⟨z, hz⟩
    rw [← contMDiffAt_subtype_iff (U := planarVortexOuterPatch) (x := zU)]
    have heq : (fun y : planarVortexOuterPatch ↦
        planarVortexCompactPhase (y : planarVortexPairOpen)) =
        fun y : planarVortexOuterPatch ↦
          planarVortexFlattenedOuterPhase
            (planarVortexOuterPatchToOuter y) := by
      funext y
      exact planarVortexCompactPhase_eq_flattened_of_one_lt_norm
        (y : planarVortexPairOpen) y.2
    rw [heq]
    exact hflat.contMDiffAt
  · ext z
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hz : ‖(z : ℂ)‖ < 2
    · exact Or.inl hz
    · right
      have : 2 ≤ ‖(z : ℂ)‖ := le_of_not_gt hz
      change 1 < ‖(z : ℂ)‖
      linarith
  · exact planarVortexInnerPatch.isOpen
  · exact planarVortexOuterPatch.isOpen

theorem planarVortexCompactPhase_eq_one_of_three_le_norm
    (z : planarVortexPairOpen) (hz : 3 ≤ ‖(z : ℂ)‖) :
    planarVortexCompactPhase z = 1 := by
  have hout : 1 < ‖(z : ℂ)‖ := lt_of_lt_of_le (by norm_num) hz
  rw [planarVortexCompactPhase_eq_flattened_of_one_lt_norm z hout]
  exact planarVortexFlattenedOuterPhase_eq_one_of_three_le_norm
    ⟨(z : ℂ), hout⟩ hz

theorem norm_planarVortexCompactPhase (z : planarVortexPairOpen) :
    ‖planarVortexCompactPhase z‖ = 1 := by
  by_cases hz : ‖(z : ℂ)‖ < 2
  · rw [planarVortexCompactPhase_eq_pairPhase_of_norm_lt_two z hz]
    exact norm_planarVortexPairPhase z
  · have hout : 1 < ‖(z : ℂ)‖ := by
      have : 2 ≤ ‖(z : ℂ)‖ := le_of_not_gt hz
      linarith
    rw [planarVortexCompactPhase_eq_flattened_of_one_lt_norm z hout,
      planarVortexFlattenedOuterPhase, Complex.norm_exp]
    simp

/-! ## Moving the standard pair to arbitrary planar points -/

/-- The twice-punctured plane with arbitrary distinct marked points. -/
def planarVortexPairOpenAt (a b : ℂ) : TopologicalSpace.Opens ℂ :=
  ⟨{z : ℂ | z ≠ a ∧ z ≠ b}, isOpen_ne.inter isOpen_ne⟩

/-- The affine coordinate sending `a` to `-1` and `b` to `1`. -/
def planarVortexAffine (a b z : ℂ) : ℂ :=
  2 * (z - (a + b) / 2) / (b - a)

theorem planarVortexAffine_apply_left {a b : ℂ} (hab : a ≠ b) :
    planarVortexAffine a b a = -1 := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  unfold planarVortexAffine
  field_simp [hba]
  ring

theorem planarVortexAffine_apply_right {a b : ℂ} (hab : a ≠ b) :
    planarVortexAffine a b b = 1 := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  unfold planarVortexAffine
  field_simp [hba]
  ring

/-- After the affine normalization, the standard zero--pole ratio is the
original zero--pole ratio. -/
theorem planarVortexRatio_affine_eq_sub_div_sub
    {a b z : ℂ} (hab : a ≠ b) (hzb : z ≠ b) :
    planarVortexRatio (planarVortexAffine a b z) =
      (z - a) / (z - b) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hzb' : z - b ≠ 0 := sub_ne_zero.mpr hzb
  have haffine_ne : planarVortexAffine a b z - 1 ≠ 0 := by
    intro hz
    apply hzb
    unfold planarVortexAffine at hz
    field_simp [hba] at hz
    linear_combination hz / 2
  unfold planarVortexRatio
  apply (div_eq_div_iff haffine_ne hzb').2
  unfold planarVortexAffine
  field_simp [hba]
  ring

theorem planarVortexAffine_injective {a b : ℂ} (hab : a ≠ b) :
    Function.Injective (planarVortexAffine a b) := by
  intro z w hzw
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  unfold planarVortexAffine at hzw
  field_simp [hba] at hzw
  linear_combination hzw / 2

/-- The inverse affine coordinate. -/
def planarVortexAffineInv (a b w : ℂ) : ℂ :=
  (a + b) / 2 + (b - a) * w / 2

theorem planarVortexAffineInv_apply_affine {a b : ℂ} (hab : a ≠ b)
    (z : ℂ) :
    planarVortexAffineInv a b (planarVortexAffine a b z) = z := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  unfold planarVortexAffineInv planarVortexAffine
  field_simp [hba]
  ring

theorem planarVortexAffine_apply_inv {a b : ℂ} (hab : a ≠ b)
    (w : ℂ) :
    planarVortexAffine a b (planarVortexAffineInv a b w) = w := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  unfold planarVortexAffineInv planarVortexAffine
  field_simp [hba]
  ring

/-- The affine vortex coordinate as a homeomorphism of the plane. -/
def planarVortexAffineHomeomorph {a b : ℂ} (hab : a ≠ b) : ℂ ≃ₜ ℂ where
  toEquiv :=
    { toFun := planarVortexAffine a b
      invFun := planarVortexAffineInv a b
      left_inv := planarVortexAffineInv_apply_affine hab
      right_inv := planarVortexAffine_apply_inv hab }
  continuous_toFun := by
    unfold planarVortexAffine
    fun_prop
  continuous_invFun := by
    unfold planarVortexAffineInv
    fun_prop

/-- The compact coordinate core outside which the affine vortex-pair phase
is identically one. -/
def planarVortexAffineCore {a b : ℂ} (hab : a ≠ b) : Set ℂ :=
  planarVortexAffineHomeomorph hab ⁻¹' Metric.closedBall 0 3

theorem planarVortexAffineCore_isCompact {a b : ℂ} (hab : a ≠ b) :
    IsCompact (planarVortexAffineCore hab) := by
  exact (planarVortexAffineHomeomorph hab).isCompact_preimage.mpr
    (isCompact_closedBall 0 3)

/-- The compact affine core lies in the closed ball of radius twice the
endpoint separation around its zero endpoint. -/
theorem planarVortexAffineCore_subset_closedBall_left
    {a b : ℂ} (hab : a ≠ b) :
    planarVortexAffineCore hab ⊆
      Metric.closedBall a (2 * ‖b - a‖) := by
  intro z hz
  have haff : ‖planarVortexAffine a b z‖ ≤ 3 := by
    simpa [planarVortexAffineCore, Metric.mem_closedBall,
      dist_zero_right] using hz
  have hrepr := planarVortexAffineInv_apply_affine hab z
  have hdiff : z - a =
      (b - a) * (planarVortexAffine a b z + 1) / 2 := by
    calc
      z - a = planarVortexAffineInv a b
          (planarVortexAffine a b z) - a := by rw [hrepr]
      _ = (b - a) * (planarVortexAffine a b z + 1) / 2 := by
        unfold planarVortexAffineInv
        ring
  rw [Metric.mem_closedBall, dist_eq_norm, hdiff, norm_div, norm_mul]
  have hadd : ‖planarVortexAffine a b z + 1‖ ≤ 4 := by
    calc
      ‖planarVortexAffine a b z + 1‖ ≤
          ‖planarVortexAffine a b z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 4 := by norm_num; linarith
  norm_num
  nlinarith [norm_nonneg (b - a)]

/-- If the endpoints are close compared with an ambient coordinate ball,
the entire compact affine core stays in that ball. -/
theorem planarVortexAffineCore_subset_ball_left
    {a b : ℂ} (hab : a ≠ b) {r : ℝ}
    (hclose : 2 * ‖b - a‖ < r) :
    planarVortexAffineCore hab ⊆ Metric.ball a r := by
  intro z hz
  have hclosed := planarVortexAffineCore_subset_closedBall_left hab hz
  exact lt_of_le_of_lt hclosed hclose

theorem three_lt_norm_planarVortexAffine_of_not_mem_core
    {a b z : ℂ} (hab : a ≠ b) (hz : z ∉ planarVortexAffineCore hab) :
    3 < ‖planarVortexAffine a b z‖ := by
  rw [planarVortexAffineCore, Set.mem_preimage,
    Metric.mem_closedBall, dist_zero_right] at hz
  exact lt_of_not_ge hz

/-- The affine coordinate sends the arbitrary twice-punctured plane into
the standard twice-punctured plane. -/
def planarVortexAffineToStandard {a b : ℂ} (hab : a ≠ b)
    (z : planarVortexPairOpenAt a b) : planarVortexPairOpen := by
  refine ⟨planarVortexAffine a b z, ?_⟩
  rw [mem_planarVortexPairOpen_iff]
  constructor
  · intro h
    have hza : (z : ℂ) = a := planarVortexAffine_injective hab
      (h.trans (planarVortexAffine_apply_left hab).symm)
    exact z.2.1 hza
  · intro h
    have hzb : (z : ℂ) = b := planarVortexAffine_injective hab
      (h.trans (planarVortexAffine_apply_right hab).symm)
    exact z.2.2 hzb

theorem contMDiff_planarVortexAffineToStandard {a b : ℂ} (hab : a ≠ b) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (planarVortexAffineToStandard hab) := by
  have hraw : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : planarVortexPairOpenAt a b ↦ planarVortexAffine a b z) := by
    have hambient : ContDiff ℝ ∞ (planarVortexAffine a b) := by
      unfold planarVortexAffine
      fun_prop
    intro z
    rw [contMDiffAt_subtype_iff]
    exact hambient.contMDiff.contMDiffAt
  exact contMDiffCodRestrictOpen hraw planarVortexPairOpen
    (fun z ↦ (planarVortexAffineToStandard hab z).2)

/-- A compactly supported unit phase with degree `+1` at `a` and degree
`-1` at `b`. -/
def planarVortexCompactPhaseAt {a b : ℂ} (hab : a ≠ b)
    (z : planarVortexPairOpenAt a b) : ℂ :=
  planarVortexCompactPhase (planarVortexAffineToStandard hab z)

/-- On the unflattened core, the compact phase is the normalized phase of
the original zero--pole ratio. -/
theorem planarVortexCompactPhaseAt_eq_normalized_ratio_of_affine_norm_lt_two
    {a b : ℂ} (hab : a ≠ b) (z : planarVortexPairOpenAt a b)
    (hz : ‖planarVortexAffine a b z‖ < 2) :
    planarVortexCompactPhaseAt hab z =
      ((z : ℂ) - a) / ((z : ℂ) - b) /
        ‖((z : ℂ) - a) / ((z : ℂ) - b)‖ := by
  rw [planarVortexCompactPhaseAt,
    planarVortexCompactPhase_eq_pairPhase_of_norm_lt_two _ hz,
    planarVortexPairPhase]
  change planarVortexRatio (planarVortexAffine a b (z : ℂ)) /
      ‖planarVortexRatio (planarVortexAffine a b (z : ℂ))‖ = _
  rw [planarVortexRatio_affine_eq_sub_div_sub hab z.2.2]

theorem contMDiff_planarVortexCompactPhaseAt {a b : ℂ} (hab : a ≠ b) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (planarVortexCompactPhaseAt hab) :=
  contMDiff_planarVortexCompactPhase.comp
    (contMDiff_planarVortexAffineToStandard hab)

theorem norm_planarVortexCompactPhaseAt {a b : ℂ} (hab : a ≠ b)
    (z : planarVortexPairOpenAt a b) :
    ‖planarVortexCompactPhaseAt hab z‖ = 1 :=
  norm_planarVortexCompactPhase (planarVortexAffineToStandard hab z)

theorem planarVortexCompactPhaseAt_eq_one_of_three_le_affine_norm
    {a b : ℂ} (hab : a ≠ b) (z : planarVortexPairOpenAt a b)
    (hz : 3 ≤ ‖planarVortexAffine a b z‖) :
    planarVortexCompactPhaseAt hab z = 1 :=
  planarVortexCompactPhase_eq_one_of_three_le_norm
    (planarVortexAffineToStandard hab z) hz

end

end JJMath.Uniformization
