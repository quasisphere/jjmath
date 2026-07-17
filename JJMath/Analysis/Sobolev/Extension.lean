import JJMath.Analysis.Sobolev.Pullback
import JJMath.Analysis.Sobolev.BallTrace
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Sobolev extension operators for Euclidean balls

This file collects the Euclidean Sobolev extension statements and the
translation/dilation reductions used by the local Poincare argument.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal NNReal ContDiff Convolution

namespace Uniformization

noncomputable section

open ContinuousLinearMap

/--
%%handwave
name:
  Radial reflection through the Euclidean unit sphere
statement:
  The radial reflection sends a point \(x\) with \(1<\|x\|<3/2\) to the point
  \(((2-\|x\|)/\|x\|)x\), which lies in the unit ball on the same ray from the
  origin and stays a definite distance away from the origin.
-/
noncomputable def euclideanSobolevUnitBallRadialReflection
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (x : H) : H :=
  (((2 - ‖x‖) / ‖x‖) : ℝ) • x

/--
%%handwave
name:
  Annulus for radial reflection
statement:
  The annulus used by the radial reflection construction is the open region
  \(1<\|x\|<3/2\).
-/
def euclideanSobolevUnitBallReflectionAnnulus
    (H : Type) [NormedAddCommGroup H] : Set H :=
  {x : H | 1 < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)}

/--
%%handwave
name:
  Inner shell for radial reflection
statement:
  The inner shell used by radial reflection is the open region
  \(1/2<\|x\|<1\).
-/
def euclideanSobolevUnitBallPunctured
    (H : Type) [NormedAddCommGroup H] : Set H :=
  {x : H | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 1}

theorem euclideanSobolevUnitBallReflectionAnnulus_isOpen
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    IsOpen (euclideanSobolevUnitBallReflectionAnnulus H) := by
  dsimp [euclideanSobolevUnitBallReflectionAnnulus]
  exact (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

theorem euclideanSobolevUnitBallPunctured_isOpen
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    IsOpen (euclideanSobolevUnitBallPunctured H) := by
  dsimp [euclideanSobolevUnitBallPunctured]
  exact (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

theorem euclideanSobolevUnitBallPunctured_subset_unit_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    euclideanSobolevUnitBallPunctured H ⊆ Metric.ball (0 : H) 1 := by
  intro x hx
  simpa [euclideanSobolevUnitBallPunctured, Metric.mem_ball, dist_eq_norm]
    using hx.2

theorem euclideanSobolevUnitBallRadialReflection_norm_of_norm_pos_of_norm_le_two
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {x : H} (hxpos : 0 < ‖x‖) (hxle : ‖x‖ ≤ 2) :
    ‖euclideanSobolevUnitBallRadialReflection x‖ = 2 - ‖x‖ := by
  have hfactor_nonneg : 0 ≤ ((2 - ‖x‖) / ‖x‖ : ℝ) :=
    div_nonneg (sub_nonneg.mpr hxle) hxpos.le
  rw [euclideanSobolevUnitBallRadialReflection, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hfactor_nonneg]
  field_simp [ne_of_gt hxpos]

theorem euclideanSobolevUnitBallRadialReflection_mem_unit_ball_of_mem_annulus
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {x : H}
    (hx : x ∈ euclideanSobolevUnitBallReflectionAnnulus H) :
    euclideanSobolevUnitBallRadialReflection x ∈
      Metric.ball (0 : H) 1 := by
  have hxpos : 0 < ‖x‖ := lt_trans (by norm_num : (0 : ℝ) < 1) hx.1
  have hnorm :
      ‖euclideanSobolevUnitBallRadialReflection x‖ = 2 - ‖x‖ := by
    exact
      euclideanSobolevUnitBallRadialReflection_norm_of_norm_pos_of_norm_le_two
        hxpos (by linarith [hx.2])
  have hlt : 2 - ‖x‖ < 1 := by
    linarith [hx.1]
  simpa [Metric.mem_ball, dist_eq_norm, hnorm] using hlt

theorem euclideanSobolevUnitBallRadialReflection_mem_punctured_of_mem_annulus
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {x : H}
    (hx : x ∈ euclideanSobolevUnitBallReflectionAnnulus H) :
    euclideanSobolevUnitBallRadialReflection x ∈
      euclideanSobolevUnitBallPunctured H := by
  have hxpos : 0 < ‖x‖ := lt_trans (by norm_num : (0 : ℝ) < 1) hx.1
  have hnorm :
      ‖euclideanSobolevUnitBallRadialReflection x‖ = 2 - ‖x‖ := by
    exact
      euclideanSobolevUnitBallRadialReflection_norm_of_norm_pos_of_norm_le_two
        hxpos (by linarith [hx.2])
  constructor
  · rw [hnorm]
    linarith [hx.2]
  · rw [hnorm]
    linarith [hx.1]

theorem euclideanSobolevUnitBallRadialReflection_mem_annulus_of_mem_punctured
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {x : H}
    (hx : x ∈ euclideanSobolevUnitBallPunctured H) :
    euclideanSobolevUnitBallRadialReflection x ∈
      euclideanSobolevUnitBallReflectionAnnulus H := by
  have hnorm :
      ‖euclideanSobolevUnitBallRadialReflection x‖ = 2 - ‖x‖ := by
    exact
      euclideanSobolevUnitBallRadialReflection_norm_of_norm_pos_of_norm_le_two
        (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hx.1)
        (by linarith [hx.2])
  constructor
  · rw [hnorm]
    linarith [hx.2]
  · rw [hnorm]
    linarith [hx.1]

theorem euclideanSobolevUnitBallRadialReflection_reflection_reflection
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {x : H} (hxpos : 0 < ‖x‖) (hxlt : ‖x‖ < 2) :
    euclideanSobolevUnitBallRadialReflection
        (euclideanSobolevUnitBallRadialReflection x) = x := by
  have hxle : ‖x‖ ≤ 2 := hxlt.le
  have hnorm :
      ‖euclideanSobolevUnitBallRadialReflection x‖ = 2 - ‖x‖ := by
    exact
      euclideanSobolevUnitBallRadialReflection_norm_of_norm_pos_of_norm_le_two
        hxpos hxle
  have hRpos : 0 < ‖euclideanSobolevUnitBallRadialReflection x‖ := by
    rw [hnorm]
    linarith
  rw [euclideanSobolevUnitBallRadialReflection, hnorm,
    euclideanSobolevUnitBallRadialReflection, smul_smul]
  have hxnorm_ne : ‖x‖ ≠ 0 := ne_of_gt hxpos
  have hsub_ne : 2 - ‖x‖ ≠ 0 := ne_of_gt (by linarith : 0 < 2 - ‖x‖)
  have hscalar :
      (((2 - (2 - ‖x‖)) / (2 - ‖x‖)) *
          ((2 - ‖x‖) / ‖x‖) : ℝ) = 1 := by
    field_simp [hxnorm_ne, hsub_ne]
    ring
  rw [hscalar, one_smul]

theorem euclideanSobolevUnitBallRadialReflection_involutive_on_annulus
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {x : H} (hx : x ∈ euclideanSobolevUnitBallReflectionAnnulus H) :
    euclideanSobolevUnitBallRadialReflection
        (euclideanSobolevUnitBallRadialReflection x) = x := by
  exact euclideanSobolevUnitBallRadialReflection_reflection_reflection
    (lt_trans (by norm_num : (0 : ℝ) < 1) hx.1)
    (by linarith [hx.2])

theorem euclideanSobolevUnitBallRadialReflection_involutive_on_punctured
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {x : H} (hx : x ∈ euclideanSobolevUnitBallPunctured H) :
    euclideanSobolevUnitBallRadialReflection
        (euclideanSobolevUnitBallRadialReflection x) = x := by
  exact euclideanSobolevUnitBallRadialReflection_reflection_reflection
    (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hx.1)
    (by linarith [hx.2])

theorem euclideanSobolevUnitBallRadialReflection_mapsTo_annulus_punctured
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    Set.MapsTo (euclideanSobolevUnitBallRadialReflection : H → H)
      (euclideanSobolevUnitBallReflectionAnnulus H)
      (euclideanSobolevUnitBallPunctured H) := by
  intro x hx
  exact euclideanSobolevUnitBallRadialReflection_mem_punctured_of_mem_annulus hx

theorem euclideanSobolevUnitBallRadialReflection_mapsTo_punctured_annulus
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    Set.MapsTo (euclideanSobolevUnitBallRadialReflection : H → H)
      (euclideanSobolevUnitBallPunctured H)
      (euclideanSobolevUnitBallReflectionAnnulus H) := by
  intro x hx
  exact euclideanSobolevUnitBallRadialReflection_mem_annulus_of_mem_punctured hx

/--
%%handwave
name:
  Radial reflection is Lipschitz on the annulus
statement:
  The radial reflection \(x\mapsto ((2-\|x\|)/\|x\|)x\) is Lipschitz on the
  annulus \(1<\|x\|<3/2\).
proof:
  On the annulus the norm is bounded away from zero.  The scalar factor
  \((2-\|x\|)/\|x\|\) is Lipschitz as a function of \(\|x\|\), and
  multiplication by the bounded vector \(x\) preserves a Lipschitz estimate.
-/
theorem euclideanSobolevUnitBallRadialReflection_lipschitzOnWith_annulus
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    LipschitzOnWith (5 : ℝ≥0)
      (euclideanSobolevUnitBallRadialReflection : H → H)
      (euclideanSobolevUnitBallReflectionAnnulus H) := by
  let A : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let R : H → H := euclideanSobolevUnitBallRadialReflection
  let a : H → ℝ := fun x ↦ (2 - ‖x‖) / ‖x‖
  have hLip : LipschitzOnWith (5 : ℝ≥0) R A := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro y hy z hz
    have hy1 : (1 : ℝ) < ‖y‖ := hy.1
    have hy2 : ‖y‖ < (2 : ℝ) := by linarith [hy.2]
    have hz1 : (1 : ℝ) < ‖z‖ := hz.1
    have hz2 : ‖z‖ < (2 : ℝ) := by linarith [hz.2]
    have hypos : 0 < ‖y‖ := lt_trans (by norm_num : (0 : ℝ) < 1) hy1
    have hzpos : 0 < ‖z‖ := lt_trans (by norm_num : (0 : ℝ) < 1) hz1
    have hay_nonneg : 0 ≤ a y :=
      div_nonneg (sub_nonneg.mpr hy2.le) hypos.le
    have hay_abs_le_one : |a y| ≤ 1 := by
      rw [abs_of_nonneg hay_nonneg]
      rw [div_le_iff₀ hypos]
      linarith [hy1]
    have hrec :
        |(‖y‖ : ℝ)⁻¹ - (‖z‖ : ℝ)⁻¹| ≤ |‖y‖ - ‖z‖| := by
      have hden_pos : 0 < ‖y‖ * ‖z‖ := mul_pos hypos hzpos
      have hden_ge_one : (1 : ℝ) ≤ ‖y‖ * ‖z‖ := by
        nlinarith [hy1, hz1]
      have hrec_eq :
          (‖y‖ : ℝ)⁻¹ - (‖z‖ : ℝ)⁻¹ =
            (‖z‖ - ‖y‖) / (‖y‖ * ‖z‖) := by
        field_simp [ne_of_gt hypos, ne_of_gt hzpos]
      rw [hrec_eq, abs_div, abs_mul, abs_of_pos hypos, abs_of_pos hzpos]
      calc
        |‖z‖ - ‖y‖| / (‖y‖ * ‖z‖) ≤ |‖z‖ - ‖y‖| / 1 := by
          exact div_le_div_of_nonneg_left (abs_nonneg _) zero_lt_one hden_ge_one
        _ = |‖z‖ - ‖y‖| := by ring
        _ = |‖y‖ - ‖z‖| := by rw [abs_sub_comm]
    have ha_sub :
        |a y - a z| ≤ 2 * ‖y - z‖ := by
      have ha_sub_eq :
          a y - a z = 2 * ((‖y‖ : ℝ)⁻¹ - (‖z‖ : ℝ)⁻¹) := by
        dsimp [a]
        field_simp [ne_of_gt hypos, ne_of_gt hzpos]
        ring
      rw [ha_sub_eq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc
        2 * |(‖y‖ : ℝ)⁻¹ - (‖z‖ : ℝ)⁻¹|
            ≤ 2 * |‖y‖ - ‖z‖| := by
          exact mul_le_mul_of_nonneg_left hrec (by norm_num)
        _ ≤ 2 * ‖y - z‖ := by
          exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le y z) (by norm_num)
    have hz_norm_le_two : ‖z‖ ≤ 2 := hz2.le
    have hdecomp :
        a y • y - a z • z = a y • (y - z) + (a y - a z) • z := by
      module
    calc
      dist (R y) (R z)
          = ‖a y • y - a z • z‖ := by
            simp [R, a, euclideanSobolevUnitBallRadialReflection, dist_eq_norm]
      _ = ‖a y • (y - z) + (a y - a z) • z‖ := by rw [hdecomp]
      _ ≤ ‖a y • (y - z)‖ + ‖(a y - a z) • z‖ := norm_add_le _ _
      _ = |a y| * ‖y - z‖ + |a y - a z| * ‖z‖ := by
        simp [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * ‖y - z‖ + (2 * ‖y - z‖) * 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hay_abs_le_one (norm_nonneg _))
          (mul_le_mul ha_sub hz_norm_le_two
            (norm_nonneg _) (by positivity))
      _ = (5 : ℝ) * dist y z := by
        rw [dist_eq_norm]
        ring
      _ = (5 : ℝ≥0) * dist y z := by norm_num
  simpa [A, R] using hLip

theorem euclideanSobolevUnitBallRadialReflection_locallyLipschitzOn_annulus
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    LocallyLipschitzOn (euclideanSobolevUnitBallReflectionAnnulus H)
      (euclideanSobolevUnitBallRadialReflection : H → H) := by
  let A : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  intro x hx
  exact
    ⟨5, A, self_mem_nhdsWithin, by
      simpa [A] using
        euclideanSobolevUnitBallRadialReflection_lipschitzOnWith_annulus
          (H := H)⟩

/--
%%handwave
name:
  The annular taper is Lipschitz
statement:
  The scalar taper \(x\mapsto 3-2\|x\|\) is Lipschitz on the radial reflection
  annulus \(1<\|x\|<3/2\), with Lipschitz constant \(2\).
proof:
  The norm is \(1\)-Lipschitz, so multiplying by \(2\) gives the estimate.
-/
theorem euclideanSobolevUnitBallTaper_lipschitzOnWith_annulus
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    LipschitzOnWith (2 : ℝ≥0)
      (fun x : H ↦ (3 : ℝ) - 2 * ‖x‖)
      (euclideanSobolevUnitBallReflectionAnnulus H) := by
  let τ : H → ℝ := fun x : H ↦ (3 : ℝ) - 2 * ‖x‖
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro y _hy z _hz
  change dist (τ y) (τ z) ≤ (2 : ℝ≥0) * dist y z
  have hdiff :
      τ y - τ z = -2 * (‖y‖ - ‖z‖) := by
    dsimp [τ]
    ring
  calc
    dist (τ y) (τ z)
        = |τ y - τ z| := by
          rw [Real.dist_eq]
    _ = 2 * |‖y‖ - ‖z‖| := by
          rw [hdiff, abs_mul, abs_neg,
            abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * ‖y - z‖ :=
          mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le y z)
            (by norm_num : (0 : ℝ) ≤ 2)
    _ = (2 : ℝ≥0) * dist y z := by
          rw [dist_eq_norm]
          norm_num

theorem euclideanSobolevUnitBallTaper_locallyLipschitzOn_annulus
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    LocallyLipschitzOn (euclideanSobolevUnitBallReflectionAnnulus H)
      (fun x : H ↦ (3 : ℝ) - 2 * ‖x‖) := by
  let A : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  intro x hx
  exact
    ⟨2, A, self_mem_nhdsWithin, by
      simpa [A] using
        euclideanSobolevUnitBallTaper_lipschitzOnWith_annulus
          (H := H)⟩

/--
%%handwave
name:
  Radial reflection is Lipschitz on the inner shell
statement:
  The radial reflection \(x\mapsto ((2-\|x\|)/\|x\|)x\) is Lipschitz on the
  inner shell \(1/2<\|x\|<1\).
proof:
  On this shell the norm is bounded away from zero, so the same estimate as
  on annuli applies.
-/
theorem euclideanSobolevUnitBallRadialReflection_lipschitzOnWith_punctured
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    LipschitzOnWith (12 : ℝ≥0)
      (euclideanSobolevUnitBallRadialReflection : H → H)
      (euclideanSobolevUnitBallPunctured H) := by
  let A : Set H := euclideanSobolevUnitBallPunctured H
  let R : H → H := euclideanSobolevUnitBallRadialReflection
  let a : H → ℝ := fun x ↦ (2 - ‖x‖) / ‖x‖
  have hLip : LipschitzOnWith (12 : ℝ≥0) R A := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro y hy z hz
    have hyhalf : (1 / 2 : ℝ) < ‖y‖ := hy.1
    have hzhalf : (1 / 2 : ℝ) < ‖z‖ := hz.1
    have hyone : ‖y‖ < (1 : ℝ) := hy.2
    have hzone : ‖z‖ < (1 : ℝ) := hz.2
    have hypos : 0 < ‖y‖ :=
      lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hyhalf
    have hzpos : 0 < ‖z‖ :=
      lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hzhalf
    have hay_nonneg : 0 ≤ a y :=
      div_nonneg (sub_nonneg.mpr (by linarith [hyone])) hypos.le
    have hay_abs_le_four : |a y| ≤ 4 := by
      rw [abs_of_nonneg hay_nonneg]
      rw [div_le_iff₀ hypos]
      nlinarith [hyhalf]
    have hrec :
        |(‖y‖ : ℝ)⁻¹ - (‖z‖ : ℝ)⁻¹| ≤
          4 * |‖y‖ - ‖z‖| := by
      have hden_pos : 0 < ‖y‖ * ‖z‖ := mul_pos hypos hzpos
      have hden_ge_quarter : (1 / 4 : ℝ) ≤ ‖y‖ * ‖z‖ := by
        nlinarith [hyhalf, hzhalf]
      have hrec_eq :
          (‖y‖ : ℝ)⁻¹ - (‖z‖ : ℝ)⁻¹ =
            (‖z‖ - ‖y‖) / (‖y‖ * ‖z‖) := by
        field_simp [ne_of_gt hypos, ne_of_gt hzpos]
      rw [hrec_eq, abs_div, abs_mul, abs_of_pos hypos,
        abs_of_pos hzpos]
      calc
        |‖z‖ - ‖y‖| / (‖y‖ * ‖z‖) ≤
            |‖z‖ - ‖y‖| / (1 / 4 : ℝ) := by
          exact div_le_div_of_nonneg_left (abs_nonneg _)
            (by norm_num : (0 : ℝ) < 1 / 4) hden_ge_quarter
        _ = 4 * |‖z‖ - ‖y‖| := by ring
        _ = 4 * |‖y‖ - ‖z‖| := by rw [abs_sub_comm]
    have ha_sub :
        |a y - a z| ≤ 8 * ‖y - z‖ := by
      have ha_sub_eq :
          a y - a z = 2 * ((‖y‖ : ℝ)⁻¹ - (‖z‖ : ℝ)⁻¹) := by
        dsimp [a]
        field_simp [ne_of_gt hypos, ne_of_gt hzpos]
        ring
      rw [ha_sub_eq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc
        2 * |(‖y‖ : ℝ)⁻¹ - (‖z‖ : ℝ)⁻¹|
            ≤ 2 * (4 * |‖y‖ - ‖z‖|) := by
          exact mul_le_mul_of_nonneg_left hrec (by norm_num)
        _ = 8 * |‖y‖ - ‖z‖| := by ring
        _ ≤ 8 * ‖y - z‖ := by
          exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le y z)
            (by norm_num)
    have hz_norm_le_one : ‖z‖ ≤ 1 := hzone.le
    have hdecomp :
        a y • y - a z • z = a y • (y - z) + (a y - a z) • z := by
      module
    calc
      dist (R y) (R z)
          = ‖a y • y - a z • z‖ := by
            simp [R, a, euclideanSobolevUnitBallRadialReflection, dist_eq_norm]
      _ = ‖a y • (y - z) + (a y - a z) • z‖ := by rw [hdecomp]
      _ ≤ ‖a y • (y - z)‖ + ‖(a y - a z) • z‖ := norm_add_le _ _
      _ = |a y| * ‖y - z‖ + |a y - a z| * ‖z‖ := by
        simp [norm_smul, Real.norm_eq_abs]
      _ ≤ 4 * ‖y - z‖ + (8 * ‖y - z‖) * 1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hay_abs_le_four (norm_nonneg _))
          (mul_le_mul ha_sub hz_norm_le_one
            (norm_nonneg _) (by positivity))
      _ = (12 : ℝ) * dist y z := by
        rw [dist_eq_norm]
        ring
      _ = (12 : ℝ≥0) * dist y z := by norm_num
  simpa [A, R] using hLip

theorem euclideanSobolevUnitBallRadialReflection_locallyLipschitzOn_punctured
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] :
    LocallyLipschitzOn (euclideanSobolevUnitBallPunctured H)
      (euclideanSobolevUnitBallRadialReflection : H → H) := by
  let A : Set H := euclideanSobolevUnitBallPunctured H
  intro x hx
  exact
    ⟨12, A, self_mem_nhdsWithin, by
      simpa [A] using
        euclideanSobolevUnitBallRadialReflection_lipschitzOnWith_punctured
          (H := H)⟩

theorem euclideanSobolevUnitBallRadialReflection_measurable
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] :
    Measurable (euclideanSobolevUnitBallRadialReflection : H → H) := by
  change Measurable fun x : H ↦ (((2 - ‖x‖) / ‖x‖ : ℝ) • x)
  measurability

private theorem map_restrict_le_smul_of_inverse_lipschitzOnWith
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U Ω : Set H} {T S : H → H} {L : ℝ≥0}
    (hT_meas : Measurable T)
    (hT_maps : Set.MapsTo T U Ω)
    (hS_left : ∀ x ∈ U, S (T x) = x)
    (hS_lip : LipschitzOnWith L S Ω) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      Measure.map T (MeasureTheory.volume.restrict U) ≤
        C • MeasureTheory.volume.restrict Ω := by
  rcases
    lipschitzOnWith_volume_image_le_smul
      (H := H) (A := Ω) (F := S) hS_lip with
    ⟨C, hC_ne_top, hS_image_le⟩
  refine ⟨C, hC_ne_top, ?_⟩
  refine Measure.le_iff.2 ?_
  intro B hB
  rw [Measure.map_apply hT_meas hB, Measure.smul_apply,
    Measure.restrict_apply hB]
  have hpre_meas : MeasurableSet (T ⁻¹' B) :=
    hB.preimage hT_meas
  rw [Measure.restrict_apply hpre_meas]
  calc
    MeasureTheory.volume (T ⁻¹' B ∩ U)
        ≤ MeasureTheory.volume (S '' (B ∩ Ω)) := by
          exact measure_mono (by
            intro x hx
            exact
              ⟨T x, ⟨hx.1, hT_maps hx.2⟩, hS_left x hx.2⟩)
    _ ≤ C * MeasureTheory.volume (B ∩ Ω) :=
          hS_image_le (B ∩ Ω) Set.inter_subset_right

private theorem quasiMeasurePreserving_restrict_of_inverse_lipschitzOnWith
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U Ω : Set H} {T S : H → H} {L : ℝ≥0}
    (hT_meas : Measurable T)
    (hT_maps : Set.MapsTo T U Ω)
    (hS_left : ∀ x ∈ U, S (T x) = x)
    (hS_lip : LipschitzOnWith L S Ω) :
    Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω) := by
  rcases
    lipschitzOnWith_volume_image_le_smul
      (H := H) (A := Ω) (F := S) hS_lip with
    ⟨C, _hC_ne_top, hS_image_le⟩
  refine ⟨hT_meas, ?_⟩
  refine Measure.AbsolutelyContinuous.mk ?_
  intro B hB hB_zero
  rw [Measure.map_apply hT_meas hB]
  have hpre_meas : MeasurableSet (T ⁻¹' B) :=
    hB.preimage hT_meas
  rw [Measure.restrict_apply hpre_meas]
  have hBΩ_zero : MeasureTheory.volume (B ∩ Ω) = 0 := by
    rwa [Measure.restrict_apply hB] at hB_zero
  exact nonpos_iff_eq_zero.1 <| calc
    MeasureTheory.volume (T ⁻¹' B ∩ U)
        ≤ MeasureTheory.volume (S '' (B ∩ Ω)) := by
          exact measure_mono (by
            intro x hx
            exact
              ⟨T x, ⟨hx.1, hT_maps hx.2⟩, hS_left x hx.2⟩)
    _ ≤ C * MeasureTheory.volume (B ∩ Ω) :=
          hS_image_le (B ∩ Ω) Set.inter_subset_right
    _ = 0 := by
          simp [hBΩ_zero]

/--
%%handwave
name:
  Radial reflection preserves null sets from the annulus to the inner shell
statement:
  Restricted from the annulus \(1<\|x\|<3/2\) to the inner shell
  \(1/2<\|x\|<1\), radial reflection is quasi-measure-preserving for Haar
  measure.
proof:
  Use local bi-Lipschitz bounds on compact subannuli and exhaust the annulus
  by such compact sets.  Lipschitz maps in finite-dimensional normed spaces
  send Haar-null sets to Haar-null sets.
-/
theorem euclideanSobolevUnitBallRadialReflection_qmp_annulus_punctured
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    Measure.QuasiMeasurePreserving
      (euclideanSobolevUnitBallRadialReflection : H → H)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H))
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallPunctured H)) := by
  exact
    quasiMeasurePreserving_restrict_of_inverse_lipschitzOnWith
      (U := euclideanSobolevUnitBallReflectionAnnulus H)
      (Ω := euclideanSobolevUnitBallPunctured H)
      (T := euclideanSobolevUnitBallRadialReflection)
      (S := euclideanSobolevUnitBallRadialReflection)
      (L := (12 : ℝ≥0))
      (euclideanSobolevUnitBallRadialReflection_measurable (H := H))
      (euclideanSobolevUnitBallRadialReflection_mapsTo_annulus_punctured
        (H := H))
      (by
        intro x hx
        exact
          euclideanSobolevUnitBallRadialReflection_involutive_on_annulus
            (H := H) (x := x) hx)
      (euclideanSobolevUnitBallRadialReflection_lipschitzOnWith_punctured
        (H := H))

/--
%%handwave
name:
  Radial reflection preserves null sets from the inner shell to the annulus
statement:
  Restricted from the inner shell \(1/2<\|x\|<1\) to the annulus
  \(1<\|x\|<3/2\), radial reflection is quasi-measure-preserving for Haar
  measure.
proof:
  The same local bi-Lipschitz argument applies in the reverse direction,
  since radial reflection is its own inverse between these two regions.
-/
theorem euclideanSobolevUnitBallRadialReflection_qmp_punctured_annulus
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    Measure.QuasiMeasurePreserving
      (euclideanSobolevUnitBallRadialReflection : H → H)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallPunctured H))
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)) := by
  exact
    quasiMeasurePreserving_restrict_of_inverse_lipschitzOnWith
      (U := euclideanSobolevUnitBallPunctured H)
      (Ω := euclideanSobolevUnitBallReflectionAnnulus H)
      (T := euclideanSobolevUnitBallRadialReflection)
      (S := euclideanSobolevUnitBallRadialReflection)
      (L := (5 : ℝ≥0))
      (euclideanSobolevUnitBallRadialReflection_measurable (H := H))
      (euclideanSobolevUnitBallRadialReflection_mapsTo_punctured_annulus
        (H := H))
      (by
        intro x hx
        exact
          euclideanSobolevUnitBallRadialReflection_involutive_on_punctured
            (H := H) (x := x) hx)
      (euclideanSobolevUnitBallRadialReflection_lipschitzOnWith_annulus
        (H := H))

/--
%%handwave
name:
  Radial reflection extension from the Euclidean unit ball
statement:
  The radial reflection extension sends a function on the unit ball to itself
  inside the ball, reflects it through the annulus \(1<\|x\|<3/2\), linearly
  tapers that reflected copy to zero at radius \(3/2\), and sets it to zero
  outside the ball of radius \(3/2\).
-/
noncomputable def euclideanSobolevUnitBallReflectionExtension
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (w : H → ℝ) : H → ℝ :=
  fun x : H ↦
    if ‖x‖ < 1 then
      w x
    else if ‖x‖ < (3 / 2 : ℝ) then
      (3 - 2 * ‖x‖) * w (euclideanSobolevUnitBallRadialReflection x)
    else
      0

/--
%%handwave
name:
  Interior part of the radial reflection extension
statement:
  The interior contribution to the extension is \(w\) on the unit ball and
  zero outside.
-/
noncomputable def euclideanSobolevUnitBallReflectionExtensionUnitPart
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (w : H → ℝ) : H → ℝ :=
  fun x : H ↦ if ‖x‖ < 1 then w x else 0

/--
%%handwave
name:
  Annular part of the radial reflection extension
statement:
  The annular contribution to the extension is the tapered reflected value
  \((3-2\|x\|)w(((2-\|x\|)/\|x\|)x)\), restricted to
  \(1\le \|x\|<3/2\).
-/
noncomputable def euclideanSobolevUnitBallReflectionExtensionAnnulusPart
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (w : H → ℝ) : H → ℝ :=
  fun x : H ↦
    if 1 ≤ ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ) then
      (3 - 2 * ‖x‖) * w (euclideanSobolevUnitBallRadialReflection x)
    else
      0

/--
%%handwave
name:
  Piecewise derivative field for radial reflection
statement:
  The derivative field assigned to the reflected extension is the original
  field in the unit ball, the product-rule derivative of the tapered
  reflected copy in the annulus \(1<\|x\|<3/2\), and zero outside the ball of
  radius \(3/2\).
-/
noncomputable def euclideanSobolevUnitBallRadialReflectionDerivativeExtension
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (w : H → ℝ) (dw : H → H →L[ℝ] ℝ) : H → H →L[ℝ] ℝ :=
  fun x : H ↦
    if ‖x‖ < 1 then
      dw x
    else if ‖x‖ < (3 / 2 : ℝ) then
      (3 - 2 * ‖x‖) •
          (dw (euclideanSobolevUnitBallRadialReflection x)).comp
            (fderiv ℝ (fun y : H ↦
              euclideanSobolevUnitBallRadialReflection y) x) +
        w (euclideanSobolevUnitBallRadialReflection x) •
          fderiv ℝ (fun y : H ↦ (3 : ℝ) - 2 * ‖y‖) x
    else
      0

/--
%%handwave
name:
  Interior part of the derivative field for radial reflection
statement:
  The interior contribution to the assigned derivative field is \(dw\) on
  the unit ball and zero outside.
-/
noncomputable def euclideanSobolevUnitBallRadialReflectionDerivativeUnitPart
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (dw : H → H →L[ℝ] ℝ) : H → H →L[ℝ] ℝ :=
  fun x : H ↦ if ‖x‖ < 1 then dw x else 0

/--
%%handwave
name:
  Annular chain-rule part of the derivative field for radial reflection
statement:
  The first annular contribution to the assigned derivative field is the
  taper \(3-2\|x\|\) times the pullback of \(dw\) by the differential of the
  radial reflection, restricted to \(1\le \|x\|<3/2\).
-/
noncomputable def euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusChainPart
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (dw : H → H →L[ℝ] ℝ) : H → H →L[ℝ] ℝ :=
  fun x : H ↦
    if 1 ≤ ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ) then
      (3 - 2 * ‖x‖) •
        (dw (euclideanSobolevUnitBallRadialReflection x)).comp
          (fderiv ℝ (fun y : H ↦
            euclideanSobolevUnitBallRadialReflection y) x)
    else
      0

/--
%%handwave
name:
  Annular taper-gradient part of the derivative field for radial reflection
statement:
  The second annular contribution to the assigned derivative field is the
  reflected value multiplied by the differential of the taper \(3-2\|x\|\),
  restricted to \(1\le \|x\|<3/2\).
-/
noncomputable def euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusValuePart
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (w : H → ℝ) : H → H →L[ℝ] ℝ :=
  fun x : H ↦
    if 1 ≤ ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ) then
      w (euclideanSobolevUnitBallRadialReflection x) •
        fderiv ℝ (fun y : H ↦ (3 : ℝ) - 2 * ‖y‖) x
    else
      0

theorem euclideanSobolevUnitBallRadialReflectionDerivativeExtension_eq_parts
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (w : H → ℝ) (dw : H → H →L[ℝ] ℝ) :
    euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw =
      fun x : H ↦
        euclideanSobolevUnitBallRadialReflectionDerivativeUnitPart dw x +
          euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusChainPart dw x +
            euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusValuePart w x := by
  funext x
  by_cases hunit : ‖x‖ < 1
  · have hcollar :
        ¬ (1 ≤ ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)) := by
      intro hx
      linarith [hx.1, hunit]
    simp [euclideanSobolevUnitBallRadialReflectionDerivativeExtension,
      euclideanSobolevUnitBallRadialReflectionDerivativeUnitPart,
      euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusChainPart,
      euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusValuePart,
      hunit, hcollar]
  · by_cases houter : ‖x‖ < (3 / 2 : ℝ)
    · have hone : 1 ≤ ‖x‖ := not_lt.mp hunit
      have hcollar : 1 ≤ ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ) :=
        ⟨hone, houter⟩
      simp [euclideanSobolevUnitBallRadialReflectionDerivativeExtension,
        euclideanSobolevUnitBallRadialReflectionDerivativeUnitPart,
        euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusChainPart,
        euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusValuePart,
        hunit, houter, hone]
    · have hcollar :
          ¬ (1 ≤ ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)) := by
        intro hx
        exact houter hx.2
      simp [euclideanSobolevUnitBallRadialReflectionDerivativeExtension,
        euclideanSobolevUnitBallRadialReflectionDerivativeUnitPart,
        euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusChainPart,
        euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusValuePart,
        hunit, houter]

theorem euclideanSobolevUnitBallReflectionExtension_eq_parts
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (w : H → ℝ) :
    euclideanSobolevUnitBallReflectionExtension w =
      fun x : H ↦
        euclideanSobolevUnitBallReflectionExtensionUnitPart w x +
          euclideanSobolevUnitBallReflectionExtensionAnnulusPart w x := by
  funext x
  by_cases hunit : ‖x‖ < 1
  · have hcollar :
        ¬ (1 ≤ ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)) := by
      intro hx
      linarith [hx.1, hunit]
    simp [euclideanSobolevUnitBallReflectionExtension,
      euclideanSobolevUnitBallReflectionExtensionUnitPart,
      euclideanSobolevUnitBallReflectionExtensionAnnulusPart,
      hunit, hcollar]
  · by_cases houter : ‖x‖ < (3 / 2 : ℝ)
    · have hone : 1 ≤ ‖x‖ := not_lt.mp hunit
      simp [euclideanSobolevUnitBallReflectionExtension,
        euclideanSobolevUnitBallReflectionExtensionUnitPart,
        euclideanSobolevUnitBallReflectionExtensionAnnulusPart,
        hunit, houter, hone]
    · have hcollar :
          ¬ (1 ≤ ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)) := by
        intro hx
        exact houter hx.2
      simp [euclideanSobolevUnitBallReflectionExtension,
        euclideanSobolevUnitBallReflectionExtensionUnitPart,
        euclideanSobolevUnitBallReflectionExtensionAnnulusPart,
        hunit, houter]

theorem euclideanSobolevUnitBallReflectionExtension_eq_of_mem_unit_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (w : H → ℝ) {x : H}
    (hx : x ∈ Metric.ball (0 : H) 1) :
    euclideanSobolevUnitBallReflectionExtension w x = w x := by
  have hxnorm : ‖x‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  simp [euclideanSobolevUnitBallReflectionExtension, hxnorm]

theorem euclideanSobolevUnitBallReflectionExtension_ae_eq_on_unit_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    {μ : Measure H} (w : H → ℝ) :
    euclideanSobolevUnitBallReflectionExtension w
      =ᵐ[μ.restrict (Metric.ball (0 : H) 1)] w := by
  exact ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet fun _x hx ↦
    euclideanSobolevUnitBallReflectionExtension_eq_of_mem_unit_ball w hx

theorem euclideanSobolevUnitBallReflectionExtension_eq_reflection_of_one_le_norm_of_norm_lt_two
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (w : H → ℝ) {x : H}
    (h1 : 1 ≤ ‖x‖) (h2 : ‖x‖ < (3 / 2 : ℝ)) :
    euclideanSobolevUnitBallReflectionExtension w x =
      (3 - 2 * ‖x‖) * w (((2 - ‖x‖) / ‖x‖) • x) := by
  have hxnot : ¬ ‖x‖ < 1 := not_lt.mpr h1
  simp [euclideanSobolevUnitBallReflectionExtension,
    euclideanSobolevUnitBallRadialReflection, hxnot, h2]

theorem euclideanSobolevUnitBallReflectionExtension_eq_zero_of_two_le_norm
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (w : H → ℝ) {x : H}
    (hx : (3 / 2 : ℝ) ≤ ‖x‖) :
    euclideanSobolevUnitBallReflectionExtension w x = 0 := by
  have hxnot_one : ¬ ‖x‖ < 1 :=
    not_lt.mpr (le_trans (by norm_num : (1 : ℝ) ≤ 3 / 2) hx)
  have hxnot_two : ¬ ‖x‖ < (3 / 2 : ℝ) := not_lt.mpr hx
  simp [euclideanSobolevUnitBallReflectionExtension, hxnot_one, hxnot_two]

theorem euclideanSobolevUnitBallReflectionExtension_support_subset_closedBall_two
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (w : H → ℝ) :
    Function.support (euclideanSobolevUnitBallReflectionExtension w) ⊆
      Metric.closedBall (0 : H) (3 / 2 : ℝ) := by
  intro x hx
  by_contra hxclosed
  have hxnorm : (3 / 2 : ℝ) ≤ ‖x‖ := by
    refine le_of_not_gt ?_
    intro hxlt
    exact hxclosed (by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxlt.le)
  exact hx (euclideanSobolevUnitBallReflectionExtension_eq_zero_of_two_le_norm
    w hxnorm)

theorem euclideanSobolevUnitBallRadialReflectionDerivativeExtension_eq_of_mem_unit_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (w : H → ℝ) (dw : H → H →L[ℝ] ℝ) {x : H}
    (hx : x ∈ Metric.ball (0 : H) 1) :
    euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw x = dw x := by
  have hxnorm : ‖x‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  simp [euclideanSobolevUnitBallRadialReflectionDerivativeExtension, hxnorm]

theorem euclideanSobolevUnitBallRadialReflectionDerivativeExtension_ae_eq_on_unit_ball
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    {μ : Measure H} (w : H → ℝ) (dw : H → H →L[ℝ] ℝ) :
    euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw
      =ᵐ[μ.restrict (Metric.ball (0 : H) 1)] dw := by
  exact ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet fun _x hx ↦
    euclideanSobolevUnitBallRadialReflectionDerivativeExtension_eq_of_mem_unit_ball
      w dw hx

theorem euclideanSobolevUnitBallRadialReflectionDerivativeExtension_eq_zero_of_two_le_norm
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (w : H → ℝ) (dw : H → H →L[ℝ] ℝ) {x : H}
    (hx : (3 / 2 : ℝ) ≤ ‖x‖) :
    euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw x = 0 := by
  have hxnot_one : ¬ ‖x‖ < 1 :=
    not_lt.mpr (le_trans (by norm_num : (1 : ℝ) ≤ 3 / 2) hx)
  have hxnot_two : ¬ ‖x‖ < (3 / 2 : ℝ) := not_lt.mpr hx
  simp [euclideanSobolevUnitBallRadialReflectionDerivativeExtension,
    hxnot_one, hxnot_two]

theorem euclideanSobolevUnitBallRadialReflectionDerivativeExtension_support_subset_closedBall_two
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (w : H → ℝ) (dw : H → H →L[ℝ] ℝ) :
    Function.support
        (euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw) ⊆
      Metric.closedBall (0 : H) (3 / 2 : ℝ) := by
  intro x hx
  by_contra hxclosed
  have hxnorm : (3 / 2 : ℝ) ≤ ‖x‖ := by
    refine le_of_not_gt ?_
    intro hxlt
    exact hxclosed (by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxlt.le)
  exact hx
    (euclideanSobolevUnitBallRadialReflectionDerivativeExtension_eq_zero_of_two_le_norm
      w dw hxnorm)

/--
%%handwave
name:
  Euclidean spheres have measure zero
statement:
  In a finite-dimensional real normed vector space with Haar measure, every
  sphere of positive radius has measure zero.
proof:
  Apply
  [the theorem that nonzero-radius spheres have zero Haar measure](lean:MeasureTheory.addHaar_sphere_of_ne_zero).
-/
theorem euclidean_volume_sphere_zero
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {c : H} {r : ℝ} (hr : 0 < r) :
    (MeasureTheory.volume : Measure H) (Metric.sphere c r) = 0 := by
  simpa using
    MeasureTheory.Measure.addHaar_sphere_of_ne_zero
      (μ := (MeasureTheory.volume : Measure H)) c (ne_of_gt hr)

/--
%%handwave
name:
  Weak chain rule for the reflected pullback
statement:
  Let \(w\) have weak derivative \(dw\) on the unit ball and be square
  integrable there.  On the annulus \(1<\|x\|<3/2\), the reflected pullback
  \(x\mapsto w(((2-\|x\|)/\|x\|)x)\) has weak derivative obtained by composing
  \(dw\) with the differential of the radial reflection.
proof:
  Restrict the weak derivative identity from the unit ball to the inner
  shell.  Radial reflection maps the annulus to this inner shell and
  is its own inverse between the two regions.  Apply
  [weak derivatives pull back under locally bi-Lipschitz changes of variables](lean:JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues.comp_locallyBiLipschitz),
  using the local Lipschitz and null-set preservation properties of radial
  reflection.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_annulus_pullback_weakDerivative
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H)
      (fun x : H ↦ w (euclideanSobolevUnitBallRadialReflection x))
      (fun x : H ↦
        (dw (euclideanSobolevUnitBallRadialReflection x)).comp
          (fderiv ℝ (fun y : H ↦
            euclideanSobolevUnitBallRadialReflection y) x)) := by
  let U : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let Ω₀ : Set H := euclideanSobolevUnitBallPunctured H
  let R : H → H := euclideanSobolevUnitBallRadialReflection
  have hΩ₀_subset : Ω₀ ⊆ Metric.ball (0 : H) 1 := by
    simpa [Ω₀] using
      euclideanSobolevUnitBallPunctured_subset_unit_ball (H := H)
  have hweak_punct :
      IsWeakDerivativeOnEuclideanRegionWithValues Ω₀ w dw :=
    IsWeakDerivativeOnEuclideanRegionWithValues.mono_set hweak hΩ₀_subset
  have hmeasure_le :
      MeasureTheory.volume.restrict Ω₀ ≤
        MeasureTheory.volume.restrict (Metric.ball (0 : H) 1) :=
    Measure.restrict_mono_set (MeasureTheory.volume : Measure H) hΩ₀_subset
  have hw_punct : MemLp w 2 (MeasureTheory.volume.restrict Ω₀) :=
    _hw.mono_measure hmeasure_le
  have hdw_punct : MemLp dw 2 (MeasureTheory.volume.restrict Ω₀) :=
    _hdw.mono_measure hmeasure_le
  simpa [U, Ω₀, R] using
    IsWeakDerivativeOnEuclideanRegionWithValues.comp_locallyBiLipschitz
      (U := U) (Ω := Ω₀) (T := R) (S := R)
      (euclideanSobolevUnitBallReflectionAnnulus_isOpen (H := H))
      (euclideanSobolevUnitBallPunctured_isOpen (H := H))
      (by
        simpa [U, Ω₀, R] using
          euclideanSobolevUnitBallRadialReflection_mapsTo_annulus_punctured
            (H := H))
      (by
        simpa [U, Ω₀, R] using
          euclideanSobolevUnitBallRadialReflection_mapsTo_punctured_annulus
            (H := H))
      (by
        intro x hx
        simpa [U, R] using
          euclideanSobolevUnitBallRadialReflection_involutive_on_annulus
            (H := H) (x := x) hx)
      (by
        intro y hy
        simpa [Ω₀, R] using
          euclideanSobolevUnitBallRadialReflection_involutive_on_punctured
            (H := H) (x := y) hy)
      (by
        simpa [U, R] using
          euclideanSobolevUnitBallRadialReflection_locallyLipschitzOn_annulus
            (H := H))
      (by
        simpa [Ω₀, R] using
          euclideanSobolevUnitBallRadialReflection_locallyLipschitzOn_punctured
            (H := H))
      (by
        simpa [U, Ω₀, R] using
          euclideanSobolevUnitBallRadialReflection_qmp_annulus_punctured
            (H := H))
      (by
        simpa [U, Ω₀, R] using
          euclideanSobolevUnitBallRadialReflection_qmp_punctured_annulus
            (H := H))
      hweak_punct hw_punct hdw_punct

/--
%%handwave
name:
  Local integrability of the reflected pullback
statement:
  If \(w\) is square integrable on the unit ball, then its reflected pullback
  \(x\mapsto w(((2-\|x\|)/\|x\|)x)\) is locally integrable on the annulus
  \(1<\|x\|<3/2\).
proof:
  The radial reflection maps compact subsets of the annulus into compact
  subsets of the unit ball and has finite multiplicity with locally bounded
  distortion on such compact subsets.  Change variables on each compact
  subset and use that square integrability on a finite-measure set implies
  integrability.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_annulus_pullback_locallyIntegrable
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ}
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    LocallyIntegrableOn
      (fun x : H ↦ w (euclideanSobolevUnitBallRadialReflection x))
      (euclideanSobolevUnitBallReflectionAnnulus H)
      (MeasureTheory.volume : Measure H) := by
  let U : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let Ω₀ : Set H := euclideanSobolevUnitBallPunctured H
  let R : H → H := euclideanSobolevUnitBallRadialReflection
  have hΩ₀_subset : Ω₀ ⊆ Metric.ball (0 : H) 1 := by
    simpa [Ω₀] using
      euclideanSobolevUnitBallPunctured_subset_unit_ball (H := H)
  have hmeasure_le :
      MeasureTheory.volume.restrict Ω₀ ≤
        MeasureTheory.volume.restrict (Metric.ball (0 : H) 1) :=
    Measure.restrict_mono_set (MeasureTheory.volume : Measure H) hΩ₀_subset
  have hw_punct : MemLp w 2 (MeasureTheory.volume.restrict Ω₀) :=
    _hw.mono_measure hmeasure_le
  rw [locallyIntegrableOn_iff
    (euclideanSobolevUnitBallReflectionAnnulus_isOpen (H := H)).isLocallyClosed]
  intro K hKU hK
  have hK_mem :
      MemLp (fun x : H ↦ w (R x)) 2
        (MeasureTheory.volume.restrict K) := by
    simpa [U, Ω₀, R] using
      locallyBiLipschitz_value_pullback_memLp_on_compact
        (U := U) (Ω := Ω₀) (K := K) (T := R) (S := R)
        (euclideanSobolevUnitBallReflectionAnnulus_isOpen (H := H))
        (euclideanSobolevUnitBallPunctured_isOpen (H := H))
        (by
          simpa [U, Ω₀, R] using
            euclideanSobolevUnitBallRadialReflection_mapsTo_annulus_punctured
              (H := H))
        (by
          simpa [U, Ω₀, R] using
            euclideanSobolevUnitBallRadialReflection_mapsTo_punctured_annulus
              (H := H))
        (by
          intro x hx
          simpa [U, R] using
            euclideanSobolevUnitBallRadialReflection_involutive_on_annulus
              (H := H) (x := x) hx)
        (by
          intro y hy
          simpa [Ω₀, R] using
            euclideanSobolevUnitBallRadialReflection_involutive_on_punctured
              (H := H) (x := y) hy)
        (by
          simpa [U, R] using
            euclideanSobolevUnitBallRadialReflection_locallyLipschitzOn_annulus
              (H := H))
        (by
          simpa [Ω₀, R] using
            euclideanSobolevUnitBallRadialReflection_locallyLipschitzOn_punctured
              (H := H))
        (by
          simpa [U, Ω₀, R] using
            euclideanSobolevUnitBallRadialReflection_qmp_annulus_punctured
              (H := H))
        (by
          simpa [U, Ω₀, R] using
            euclideanSobolevUnitBallRadialReflection_qmp_punctured_annulus
              (H := H))
        hK hKU hw_punct
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK.measure_ne_top
  exact hK_mem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)

private theorem locallyIntegrableOn_mul_left_integrable_of_compact_support_bound
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    {Ω K : Set H} {a u : H → ℝ} {C : ℝ}
    (hu_loc : LocallyIntegrableOn u Ω
      (MeasureTheory.volume : Measure H))
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (ha_aesm : AEStronglyMeasurable a (MeasureTheory.volume.restrict K))
    (ha_bound : ∀ᵐ z ∂MeasureTheory.volume.restrict K, ‖a z‖ ≤ C)
    (ha_support : Function.support a ⊆ K) :
    Integrable (fun z : H ↦ a z * u z)
      (MeasureTheory.volume.restrict Ω) := by
  have huK : Integrable u (MeasureTheory.volume.restrict K) :=
    hu_loc.integrableOn_compact_subset hKΩ hK
  have hprodK : Integrable (fun z : H ↦ a z * u z)
      (MeasureTheory.volume.restrict K) :=
    huK.bdd_mul ha_aesm ha_bound
  have hprodK_on : IntegrableOn (fun z : H ↦ a z * u z) K
      (MeasureTheory.volume : Measure H) := by
    simpa [IntegrableOn] using hprodK
  have hprod_support :
      Function.support (fun z : H ↦ a z * u z) ⊆ K := by
    intro z hz
    exact ha_support
      (Function.support_mul_subset_left
        (f := a) (g := u) hz)
  have hprod_global : Integrable (fun z : H ↦ a z * u z)
      (MeasureTheory.volume : Measure H) :=
    (integrableOn_iff_integrable_of_support_subset hprod_support).mp hprodK_on
  exact hprod_global.mono_measure
    (Measure.restrict_le_self (μ := MeasureTheory.volume) (s := Ω))

private theorem locallyIntegrableOn_mul_left_integrable_of_compact_support_continuousOn
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    {Ω K : Set H} {a u : H → ℝ}
    (hu_loc : LocallyIntegrableOn u Ω
      (MeasureTheory.volume : Measure H))
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (ha_cont : ContinuousOn a K)
    (ha_support : Function.support a ⊆ K) :
    Integrable (fun z : H ↦ a z * u z)
      (MeasureTheory.volume.restrict Ω) := by
  let C : ℝ := max 0 (Classical.choose (hK.exists_bound_of_continuousOn ha_cont))
  have hC_bound :
      ∀ z ∈ K, ‖a z‖ ≤ C := by
    intro z hz
    have hbound := Classical.choose_spec (hK.exists_bound_of_continuousOn ha_cont) z hz
    exact le_trans hbound (le_max_right 0 _)
  have ha_aesm : AEStronglyMeasurable a (MeasureTheory.volume.restrict K) :=
    ha_cont.aestronglyMeasurable_of_isCompact hK hK.measurableSet
  exact
    locallyIntegrableOn_mul_left_integrable_of_compact_support_bound
      hu_loc hK hKΩ ha_aesm
      (ae_restrict_of_forall_mem hK.measurableSet hC_bound)
      ha_support

/--
%%handwave
name:
  Test identity for smooth multipliers
statement:
  Let \(u\) have weak derivative \(du\) on a Euclidean region, and let \(a\)
  be smooth.  For every compactly supported smooth test \(\varphi\) and
  constant direction \(v\), assuming the two displayed test pairings are
  integrable,
  \[
    \int D\varphi[v]\,a u
      =
    -\int \varphi\,(a\,du[v]+u\,Da[v]).
  \]
proof:
  Test the weak derivative identity for \(u\) against \(a\varphi\).  The
  classical product rule expands \(D(a\varphi)[v]\); moving the
  \(\varphi\,Da[v]\,u\) term to the other side gives the result.
-/
theorem euclideanSobolev_contDiff_mul_test_integral_eq
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    {Ω : Set H} {a u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (ha_smooth : ContDiff ℝ ∞ a)
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (v : H)
    (hleft_int : Integrable
      (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • (a z * u z))
      (MeasureTheory.volume.restrict Ω))
    (_hright_int : Integrable
      (fun z : H ↦
        φ z • ((a z • du z + u z • fderiv ℝ a z) v))
      (MeasureTheory.volume.restrict Ω)) :
    ∫ z in Ω, (fderiv ℝ (φ : H → ℝ) z v) • (a z * u z)
        ∂MeasureTheory.volume =
      -∫ z in Ω,
        φ z • ((a z • du z + u z • fderiv ℝ a z) v)
        ∂MeasureTheory.volume := by
  let μΩ : Measure H := MeasureTheory.volume.restrict Ω
  let ψ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    { toFun := fun z : H ↦ (φ : H → ℝ) z * a z
      smooth := φ.smooth.mul ha_smooth
      support_subset := by
        exact (tsupport_mul_subset_left).trans φ.support_subset
      compact_support := by
        exact φ.compact_support.of_isClosed_subset
          (isClosed_tsupport _) tsupport_mul_subset_left }
  let A : H → ℝ :=
    fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • (a z * u z)
  let B : H → ℝ :=
    fun z ↦ φ z • (u z * fderiv ℝ a z v)
  let C : H → ℝ :=
    fun z ↦ φ z • (a z * du z v)
  let R : H → ℝ :=
    fun z ↦ φ z • ((a z • du z + u z • fderiv ℝ a z) v)
  have hψ := hweak ψ v
  have hleft_ae :
      (fun z : H ↦ (fderiv ℝ (ψ : H → ℝ) z v) • u z)
        =ᵐ[μΩ] fun z ↦ A z + B z := by
    exact ae_of_all μΩ fun z ↦ by
      have hφdiff : DifferentiableAt ℝ (φ : H → ℝ) z :=
        (φ.smooth.differentiable (by simp)) z
      have hadiff : DifferentiableAt ℝ a z :=
        (ha_smooth.differentiable (by simp)) z
      change
        (fderiv ℝ (fun y : H ↦ (φ : H → ℝ) y * a y) z v) • u z =
          A z + B z
      rw [fderiv_fun_mul hφdiff hadiff]
      simp [A, B, smul_eq_mul]
      ring
  have hright_ae :
      (fun z : H ↦ φ z • ((a z • du z + u z • fderiv ℝ a z) v))
        =ᵐ[μΩ] fun z ↦ C z + B z := by
    exact ae_of_all μΩ fun z ↦ by
      simp [B, C, smul_eq_mul]
      ring
  have hψ_right_ae :
      (fun z : H ↦ ψ z • du z v) =ᵐ[μΩ] C := by
    exact ae_of_all μΩ fun z ↦ by
      simp [ψ, C, smul_eq_mul, mul_assoc]
  have hA_int : Integrable A μΩ := by
    simpa [A, μΩ] using hleft_int
  have hAB_int : Integrable (fun z ↦ A z + B z) μΩ :=
    hψ.1.congr hleft_ae
  have hB_int : Integrable B μΩ := by
    have hdiff : Integrable (fun z ↦ (A z + B z) - A z) μΩ :=
      hAB_int.sub hA_int
    refine hdiff.congr ?_
    exact ae_of_all μΩ fun z ↦ by abel_nf
  have hC_int : Integrable C μΩ :=
    hψ.2.1.congr hψ_right_ae
  have hweak_eq :
      ∫ z, A z + B z ∂μΩ = -∫ z, C z ∂μΩ := by
    calc
      ∫ z, A z + B z ∂μΩ
          = ∫ z, (fderiv ℝ (ψ : H → ℝ) z v) • u z ∂μΩ :=
            integral_congr_ae hleft_ae.symm
      _ = -∫ z, ψ z • du z v ∂μΩ := by
            simpa [μΩ] using hψ.2.2
      _ = -∫ z, C z ∂μΩ := by
            rw [integral_congr_ae hψ_right_ae]
  calc
    ∫ z in Ω, (fderiv ℝ (φ : H → ℝ) z v) • (a z * u z)
        ∂MeasureTheory.volume
        = ∫ z, A z ∂μΩ := by
            rfl
    _ = ∫ z, A z + B z ∂μΩ - ∫ z, B z ∂μΩ := by
          rw [integral_add hA_int hB_int]
          abel_nf
    _ = -∫ z, C z ∂μΩ - ∫ z, B z ∂μΩ := by
          rw [hweak_eq]
    _ = -∫ z, C z + B z ∂μΩ := by
          rw [integral_add hC_int hB_int]
          ring
    _ = -∫ z, R z ∂μΩ := by
          rw [integral_congr_ae hright_ae.symm]
    _ =
      -∫ z in Ω,
        φ z • ((a z • du z + u z • fderiv ℝ a z) v)
        ∂MeasureTheory.volume := by
          rfl

/--
%%handwave
name:
  Weak product rule for smooth multipliers
statement:
  On an open finite-dimensional Euclidean region, if \(u\) has weak derivative
  \(du\), \(u\) is locally integrable, and \(a\) is smooth, then \(a u\) has
  weak derivative \(a\,du+u\,Da\).
proof:
  Compact support of the test function reduces all integrability questions to
  compact subsets of the region.  The test identity is
  [the smooth multiplier identity](lean:JJMath.Uniformization.euclideanSobolev_contDiff_mul_test_integral_eq).
-/
theorem euclideanSobolev_contDiff_mul_weakDerivative
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {a u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hΩ_open : IsOpen Ω)
    (ha_smooth : ContDiff ℝ ∞ a)
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hu_loc : LocallyIntegrableOn u Ω
      (MeasureTheory.volume : Measure H)) :
    IsWeakDerivativeOnEuclideanRegionWithValues Ω
      (fun x : H ↦ a x * u x)
      (fun x : H ↦ a x • du x + u x • fderiv ℝ a x) := by
  intro φ v
  let μΩ : Measure H := MeasureTheory.volume.restrict Ω
  let dφ : H → ℝ := fun z ↦ fderiv ℝ (φ : H → ℝ) z v
  let Kφ : Set H := tsupport (φ : H → ℝ)
  let Kdφ : Set H := tsupport dφ
  have hKφ_compact : IsCompact Kφ := φ.compact_support
  have hKφΩ : Kφ ⊆ Ω := φ.support_subset
  have hKdφ_subset : Kdφ ⊆ Kφ := by
    simpa [Kdφ, Kφ, dφ] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := (φ : H → ℝ)) v)
  have hKdφ_compact : IsCompact Kdφ :=
    hKφ_compact.of_isClosed_subset (isClosed_tsupport _) hKdφ_subset
  have hKdφΩ : Kdφ ⊆ Ω := hKdφ_subset.trans hKφΩ
  have ha_cont_Kφ : ContinuousOn a Kφ :=
    ha_smooth.continuous.continuousOn
  have ha_cont_Kdφ : ContinuousOn a Kdφ :=
    ha_smooth.continuous.continuousOn
  have hdφ_cont : Continuous dφ :=
    ((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hDa_cont : Continuous (fun z : H ↦ fderiv ℝ a z v) :=
    ((ha_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hleft_int : Integrable
      (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • (a z * u z))
      μΩ := by
    let m : H → ℝ := fun z ↦ dφ z * a z
    have hm_cont : ContinuousOn m Kdφ :=
      hdφ_cont.continuousOn.mul ha_cont_Kdφ
    have hm_support : Function.support m ⊆ Kdφ := by
      intro z hz
      exact subset_tsupport dφ
        (Function.support_mul_subset_left (f := dφ) (g := a) hz)
    have hm_int : Integrable (fun z : H ↦ m z * u z)
        (MeasureTheory.volume.restrict Ω) :=
      locallyIntegrableOn_mul_left_integrable_of_compact_support_continuousOn
        hu_loc hKdφ_compact hKdφΩ hm_cont hm_support
    refine hm_int.congr ?_
    exact ae_of_all μΩ fun z ↦ by
      simp [m, dφ, smul_eq_mul, mul_assoc]
  have hweakK : KinnunenWeakDerivativeOnEuclideanRegionScalar Ω u du := by
    simpa [KinnunenWeakDerivativeOnEuclideanRegionScalar,
      IsWeakDerivativeOnEuclideanRegionScalar,
      IsWeakDerivativeOnEuclideanRegionWithValues] using hweak
  have hdu_loc :
      LocallyIntegrableOn (fun z : H ↦ du z v) Ω
        (MeasureTheory.volume : Measure H) :=
    kinnunenWeakDerivative_directionalDerivative_locallyIntegrableOn
      hΩ_open hweakK v
  have hright_du : Integrable
      (fun z : H ↦ ((φ : H → ℝ) z * a z) * du z v)
      (MeasureTheory.volume.restrict Ω) := by
    let m : H → ℝ := fun z ↦ (φ : H → ℝ) z * a z
    have hm_cont : ContinuousOn m Kφ :=
      φ.smooth.continuous.continuousOn.mul ha_cont_Kφ
    have hm_support : Function.support m ⊆ Kφ := by
      intro z hz
      exact subset_tsupport (φ : H → ℝ)
        (Function.support_mul_subset_left
          (f := (φ : H → ℝ)) (g := a) hz)
    simpa [m] using
      locallyIntegrableOn_mul_left_integrable_of_compact_support_continuousOn
        hdu_loc hKφ_compact hKφΩ hm_cont hm_support
  have hright_Da : Integrable
      (fun z : H ↦ ((φ : H → ℝ) z *
          fderiv ℝ a z v) * u z)
      (MeasureTheory.volume.restrict Ω) := by
    let m : H → ℝ := fun z ↦ (φ : H → ℝ) z * fderiv ℝ a z v
    have hm_cont : ContinuousOn m Kφ :=
      φ.smooth.continuous.continuousOn.mul hDa_cont.continuousOn
    have hm_support : Function.support m ⊆ Kφ := by
      intro z hz
      exact subset_tsupport (φ : H → ℝ)
        (Function.support_mul_subset_left
          (f := (φ : H → ℝ))
          (g := fun z : H ↦ fderiv ℝ a z v) hz)
    simpa [m] using
      locallyIntegrableOn_mul_left_integrable_of_compact_support_continuousOn
        hu_loc hKφ_compact hKφΩ hm_cont hm_support
  have hright_int : Integrable
      (fun z : H ↦
        φ z • ((a z • du z + u z • fderiv ℝ a z) v))
      μΩ := by
    have hsum := hright_du.add hright_Da
    refine hsum.congr ?_
    exact ae_of_all μΩ fun z ↦ by
      simp [smul_eq_mul]
      ring
  exact
    ⟨hleft_int, hright_int,
      euclideanSobolev_contDiff_mul_test_integral_eq
        ha_smooth hweak φ v hleft_int hright_int⟩

/--
Smooth approximation data for a locally Lipschitz multiplier, localized to a
fixed weak test pairing.
-/
structure LocallyLipschitzMultiplierSmoothApproxIntegralData
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    {Ω : Set H} (a u : H → ℝ) (du : H → H →L[ℝ] ℝ)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω) (v : H)
    where
  approximants : ℕ → H → ℝ
  smooth : ∀ n : ℕ, ContDiff ℝ ∞ (approximants n)
  left_integrable :
    ∀ n : ℕ,
      Integrable
        (fun z : H ↦
          (fderiv ℝ (φ : H → ℝ) z v) •
            (approximants n z * u z))
        (MeasureTheory.volume.restrict Ω)
  right_integrable :
    ∀ n : ℕ,
      Integrable
        (fun z : H ↦
          φ z •
            ((approximants n z • du z +
                u z • fderiv ℝ (approximants n) z) v))
        (MeasureTheory.volume.restrict Ω)
  left_tendsto :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ z in Ω,
          (fderiv ℝ (φ : H → ℝ) z v) •
            (approximants n z * u z) ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in Ω,
          (fderiv ℝ (φ : H → ℝ) z v) •
            (a z * u z) ∂MeasureTheory.volume))
  right_tendsto :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ z in Ω,
          φ z •
            ((approximants n z • du z +
                u z • fderiv ℝ (approximants n) z) v)
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in Ω,
          φ z • ((a z • du z + u z • fderiv ℝ a z) v)
          ∂MeasureTheory.volume))

/--
Smooth approximation data for a locally Lipschitz multiplier, keeping only the
analytic convergence of the two localized weak test pairings.
-/
structure LocallyLipschitzMultiplierSmoothApproxPairingLimitData
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    {Ω : Set H} (a u : H → ℝ) (du : H → H →L[ℝ] ℝ)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω) (v : H)
    where
  approximants : ℕ → H → ℝ
  smooth : ∀ n : ℕ, ContDiff ℝ ∞ (approximants n)
  left_tendsto :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ z in Ω,
          (fderiv ℝ (φ : H → ℝ) z v) •
            (approximants n z * u z) ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in Ω,
          (fderiv ℝ (φ : H → ℝ) z v) •
            (a z * u z) ∂MeasureTheory.volume))
  right_tendsto :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ z in Ω,
          φ z •
            ((approximants n z • du z +
                u z • fderiv ℝ (approximants n) z) v)
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in Ω,
          φ z • ((a z • du z + u z • fderiv ℝ a z) v)
          ∂MeasureTheory.volume))

/--
Dominated-convergence data for smooth approximation of a locally Lipschitz
multiplier in one localized weak test pairing.
-/
structure LocallyLipschitzMultiplierSmoothApproxDominatedData
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    {Ω : Set H} (a u : H → ℝ) (du : H → H →L[ℝ] ℝ)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω) (v : H)
    where
  approximants : ℕ → H → ℝ
  smooth : ∀ n : ℕ, ContDiff ℝ ∞ (approximants n)
  leftBound : H → ℝ
  rightBound : H → ℝ
  left_aestronglyMeasurable :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun z : H ↦
          (fderiv ℝ (φ : H → ℝ) z v) •
            (approximants n z * u z))
        (MeasureTheory.volume.restrict Ω)
  right_aestronglyMeasurable :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun z : H ↦
          φ z •
            ((approximants n z • du z +
                u z • fderiv ℝ (approximants n) z) v))
        (MeasureTheory.volume.restrict Ω)
  leftBound_integrable :
    Integrable leftBound (MeasureTheory.volume.restrict Ω)
  rightBound_integrable :
    Integrable rightBound (MeasureTheory.volume.restrict Ω)
  left_bound :
    ∀ n : ℕ,
      ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
        ‖(fderiv ℝ (φ : H → ℝ) z v) •
            (approximants n z * u z)‖ ≤ leftBound z
  right_bound :
    ∀ n : ℕ,
      ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
        ‖φ z •
            ((approximants n z • du z +
                u z • fderiv ℝ (approximants n) z) v)‖ ≤
          rightBound z
  left_tendsto_ae :
    ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
      Filter.Tendsto
        (fun n : ℕ ↦
          (fderiv ℝ (φ : H → ℝ) z v) •
            (approximants n z * u z))
        Filter.atTop
        (𝓝
          ((fderiv ℝ (φ : H → ℝ) z v) • (a z * u z)))
  right_tendsto_ae :
    ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
      Filter.Tendsto
        (fun n : ℕ ↦
          φ z •
            ((approximants n z • du z +
                u z • fderiv ℝ (approximants n) z) v))
        Filter.atTop
        (𝓝
          (φ z • ((a z • du z + u z • fderiv ℝ a z) v)))

/--
%%handwave
name:
  Dominated convergence gives multiplier pairing limits
statement:
  Suppose smooth approximants of a locally Lipschitz multiplier have
  pointwise almost-everywhere convergence in the two localized weak test
  integrands, with integrable dominating functions.  Then the two weak test
  pairings converge to the pairings for the original multiplier.
proof:
  Apply dominated convergence separately to the left and right test
  integrands.
-/
theorem euclideanSobolev_locallyLipschitz_mul_smoothApprox_pairingLimitData_of_dominatedData
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    {Ω : Set H} {a u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (v : H)
    (hdom :
      LocallyLipschitzMultiplierSmoothApproxDominatedData
        a u du φ v) :
    Nonempty
      (LocallyLipschitzMultiplierSmoothApproxPairingLimitData
        a u du φ v) := by
  refine
    ⟨{ approximants := hdom.approximants
       smooth := hdom.smooth
       left_tendsto := ?_
       right_tendsto := ?_ }⟩
  · simpa using
      (tendsto_integral_of_dominated_convergence
        (μ := MeasureTheory.volume.restrict Ω)
        (F := fun n (z : H) ↦
          (fderiv ℝ (φ : H → ℝ) z v) •
            (hdom.approximants n z * u z))
        (f := fun z : H ↦
          (fderiv ℝ (φ : H → ℝ) z v) • (a z * u z))
        hdom.leftBound
        hdom.left_aestronglyMeasurable
        hdom.leftBound_integrable
        hdom.left_bound
        hdom.left_tendsto_ae)
  · simpa using
      (tendsto_integral_of_dominated_convergence
        (μ := MeasureTheory.volume.restrict Ω)
        (F := fun n (z : H) ↦
          φ z •
            ((hdom.approximants n z • du z +
                u z • fderiv ℝ (hdom.approximants n) z) v))
        (f := fun z : H ↦
          φ z • ((a z • du z + u z • fderiv ℝ a z) v))
        hdom.rightBound
        hdom.right_aestronglyMeasurable
        hdom.rightBound_integrable
        hdom.right_bound
        hdom.right_tendsto_ae)

/--
%%handwave
name:
  Smooth approximation data gives the locally Lipschitz multiplier identity
statement:
  Suppose a locally Lipschitz multiplier has smooth approximants whose two
  weak test pairings converge to the corresponding pairings for the original
  multiplier.  Then the multiplier identity follows for the original
  multiplier.
proof:
  Apply the smooth multiplier identity to every approximant.  The left-hand
  pairings converge to the desired left-hand side and the negatives of the
  right-hand pairings converge to the negative of the desired right-hand side.
  Uniqueness of limits gives the identity.
-/
theorem euclideanSobolev_locallyLipschitz_mul_test_integral_eq_of_smooth_approx_data
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    {Ω : Set H} {a u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (v : H)
    (happrox :
      LocallyLipschitzMultiplierSmoothApproxIntegralData a u du φ v) :
    ∫ z in Ω, (fderiv ℝ (φ : H → ℝ) z v) • (a z * u z)
        ∂MeasureTheory.volume =
      -∫ z in Ω,
        φ z • ((a z • du z + u z • fderiv ℝ a z) v)
        ∂MeasureTheory.volume := by
  let L : ℕ → ℝ := fun n ↦
    ∫ z in Ω,
      (fderiv ℝ (φ : H → ℝ) z v) •
        (happrox.approximants n z * u z) ∂MeasureTheory.volume
  let R : ℕ → ℝ := fun n ↦
    ∫ z in Ω,
      φ z •
        ((happrox.approximants n z • du z +
            u z • fderiv ℝ (happrox.approximants n) z) v)
        ∂MeasureTheory.volume
  let Llim : ℝ :=
    ∫ z in Ω, (fderiv ℝ (φ : H → ℝ) z v) • (a z * u z)
      ∂MeasureTheory.volume
  let Rlim : ℝ :=
    ∫ z in Ω,
      φ z • ((a z • du z + u z • fderiv ℝ a z) v)
      ∂MeasureTheory.volume
  have hweak_eq : ∀ᶠ n in Filter.atTop, L n = -R n := by
    filter_upwards with n
    simpa [L, R] using
      euclideanSobolev_contDiff_mul_test_integral_eq
        (happrox.smooth n) hweak φ v
        (happrox.left_integrable n)
        (happrox.right_integrable n)
  have hnegR_tendsto_to_Llim :
      Filter.Tendsto (fun n ↦ -R n) Filter.atTop (𝓝 Llim) := by
    exact Filter.Tendsto.congr' hweak_eq
      (by simpa [L, Llim] using happrox.left_tendsto)
  have hnegR_tendsto_to_neg_Rlim :
      Filter.Tendsto (fun n ↦ -R n) Filter.atTop (𝓝 (-Rlim)) := by
    have hR_tendsto : Filter.Tendsto R Filter.atTop (𝓝 Rlim) := by
      simpa [R, Rlim] using happrox.right_tendsto
    exact hR_tendsto.neg
  have hlim_eq : Llim = -Rlim :=
    tendsto_nhds_unique hnegR_tendsto_to_Llim hnegR_tendsto_to_neg_Rlim
  simpa [Llim, Rlim] using hlim_eq

private theorem euclideanSobolevUnitBallReflectionAnnulus_taper_smoothExtension
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    ∃ a : H → ℝ,
      ContDiff ℝ ∞ a ∧
        Set.EqOn a (fun x : H ↦ (3 : ℝ) - 2 * ‖x‖)
          (euclideanSobolevUnitBallReflectionAnnulus H) ∧
        Set.EqOn (fun x : H ↦ fderiv ℝ a x)
          (fun x : H ↦
            fderiv ℝ (fun y : H ↦ (3 : ℝ) - 2 * ‖y‖) x)
          (euclideanSobolevUnitBallReflectionAnnulus H) := by
  classical
  let β : ContDiffBump (0 : H) :=
    { rIn := (1 / 4 : ℝ)
      rOut := (1 / 2 : ℝ)
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let a : H → ℝ :=
    fun x : H ↦ ((1 : ℝ) - β x) * (3 : ℝ) -
      2 * (((1 : ℝ) - β x) * ‖x‖)
  have hmask : ContDiff ℝ ∞ (fun x : H ↦ (1 : ℝ) - β x) :=
    contDiff_const.sub β.contDiff
  have hmask_norm :
      ContDiff ℝ ∞ (fun x : H ↦ ((1 : ℝ) - β x) * ‖x‖) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      have hβ_one :
          (fun y : H ↦ β y) =ᶠ[𝓝 (0 : H)] fun _ : H ↦ (1 : ℝ) :=
        β.eventuallyEq_one
      filter_upwards [hβ_one] with y hy
      simp [hy]
    · exact hmask.contDiffAt.mul (contDiffAt_norm ℝ hx)
  have ha_smooth : ContDiff ℝ ∞ a := by
    have hfirst :
        ContDiff ℝ ∞ (fun x : H ↦ ((1 : ℝ) - β x) * (3 : ℝ)) :=
      hmask.mul contDiff_const
    have hsecond :
        ContDiff ℝ ∞
          (fun x : H ↦ (2 : ℝ) * (((1 : ℝ) - β x) * ‖x‖)) :=
      contDiff_const.mul hmask_norm
    simpa [a] using hfirst.sub hsecond
  have ha_eventually_eq_taper :
      ∀ x ∈ euclideanSobolevUnitBallReflectionAnnulus H,
        a =ᶠ[𝓝 x] fun y : H ↦ (3 : ℝ) - 2 * ‖y‖ := by
    intro x hx
    have hx_norm : (1 / 2 : ℝ) < ‖x‖ := by
      dsimp [euclideanSobolevUnitBallReflectionAnnulus] at hx
      nlinarith [hx.1]
    have hnear :
        {y : H | (1 / 2 : ℝ) < ‖y‖} ∈ 𝓝 x :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hx_norm
    filter_upwards [hnear] with y hy
    have hβ_zero : β y = 0 := by
      exact β.zero_of_le_dist (by
        simpa [β, dist_eq_norm] using (le_of_lt hy))
    simp [a, hβ_zero]
  refine ⟨a, ha_smooth, ?_, ?_⟩
  · intro x hx
    have hx_norm : (1 / 2 : ℝ) < ‖x‖ := by
      dsimp [euclideanSobolevUnitBallReflectionAnnulus] at hx
      nlinarith [hx.1]
    have hβ_zero : β x = 0 := by
      exact β.zero_of_le_dist (by
        simpa [β, dist_eq_norm] using (le_of_lt hx_norm))
    simp [a, hβ_zero]
  · intro x hx
    exact Filter.EventuallyEq.fderiv_eq
      (𝕜 := ℝ) (ha_eventually_eq_taper x hx)

/--
%%handwave
name:
  Weak product rule for the annular taper
statement:
  If \(u\) has weak derivative \(du\) on the annulus \(1<\|x\|<3/2\) and is
  locally integrable there, then \((3-2\|x\|)u\) has weak derivative
  \((3-2\|x\|)du+u\,d(3-2\|x\|)\).
proof:
  Choose a smooth cutoff which is zero near the origin and equal to one on
  the annulus.  Multiplying \(3-2\|x\|\) by this cutoff gives a globally
  smooth function which agrees with the taper, together with its differential,
  on the annulus.  Apply
  [the weak product rule for smooth multipliers](lean:JJMath.Uniformization.euclideanSobolev_contDiff_mul_weakDerivative)
  to that smooth extension and restrict the resulting test identities back to
  the annulus.
-/
theorem euclideanSobolev_annulus_taper_mul_weakDerivative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H) u du)
    (_hu_loc : LocallyIntegrableOn u
      (euclideanSobolevUnitBallReflectionAnnulus H)
      (MeasureTheory.volume : Measure H)) :
    IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H)
      (fun x : H ↦ (3 - 2 * ‖x‖) * u x)
      (fun x : H ↦
        (3 - 2 * ‖x‖) • du x +
          u x • fderiv ℝ (fun y : H ↦ (3 : ℝ) - 2 * ‖y‖) x) := by
  rcases
    euclideanSobolevUnitBallReflectionAnnulus_taper_smoothExtension
      (H := H) with
    ⟨a, ha_smooth, ha_eq, hDa_eq⟩
  let Ω : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let μΩ : Measure H := MeasureTheory.volume.restrict Ω
  have hsmooth :
      IsWeakDerivativeOnEuclideanRegionWithValues Ω
        (fun x : H ↦ a x * u x)
        (fun x : H ↦ a x • du x + u x • fderiv ℝ a x) :=
    euclideanSobolev_contDiff_mul_weakDerivative
      (Ω := Ω) euclideanSobolevUnitBallReflectionAnnulus_isOpen
      ha_smooth hweak _hu_loc
  intro φ v
  rcases hsmooth φ v with ⟨hleft, hright, hpair⟩
  have hΩ_meas : MeasurableSet Ω :=
    euclideanSobolevUnitBallReflectionAnnulus_isOpen.measurableSet
  have hleft_ae :
      (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • (a z * u z))
        =ᵐ[μΩ]
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          (((3 : ℝ) - 2 * ‖z‖) * u z)) :=
    ae_restrict_of_forall_mem hΩ_meas fun z hz ↦ by
      simp [ha_eq hz]
  have hright_ae :
      (fun z : H ↦ φ z • ((a z • du z + u z • fderiv ℝ a z) v))
        =ᵐ[μΩ]
      (fun z : H ↦
        φ z •
          ((((3 : ℝ) - 2 * ‖z‖) • du z +
            u z • fderiv ℝ (fun y : H ↦ (3 : ℝ) - 2 * ‖y‖) z) v)) :=
    ae_restrict_of_forall_mem hΩ_meas fun z hz ↦ by
      simp [ha_eq hz, hDa_eq hz]
  refine ⟨hleft.congr hleft_ae, hright.congr hright_ae, ?_⟩
  calc
    ∫ z in Ω,
        (fderiv ℝ (φ : H → ℝ) z v) •
          (((3 : ℝ) - 2 * ‖z‖) * u z)
        ∂MeasureTheory.volume
        = ∫ z,
            (fderiv ℝ (φ : H → ℝ) z v) • (a z * u z)
            ∂μΩ := by
            rw [integral_congr_ae hleft_ae.symm]
    _ = -∫ z, φ z • ((a z • du z + u z • fderiv ℝ a z) v) ∂μΩ :=
        hpair
    _ = -∫ z in Ω,
        φ z •
          ((((3 : ℝ) - 2 * ‖z‖) • du z +
            u z • fderiv ℝ (fun y : H ↦ (3 : ℝ) - 2 * ‖y‖) z) v)
        ∂MeasureTheory.volume := by
          rw [integral_congr_ae hright_ae]

/--
%%handwave
name:
  Weak chain rule on the reflected annulus
statement:
  Let \(w\) have weak derivative \(dw\) on the unit ball and be square
  integrable there.  On the annulus \(1<\|x\|<3/2\), the tapered pullback
  \(x\mapsto (3-2\|x\|)w(((2-\|x\|)/\|x\|)x)\) has weak derivative given by
  the product rule: the taper times the chain-rule pullback of \(dw\), plus
  the reflected value times the differential of the taper.
proof:
  Apply
  [the weak chain rule for the reflected pullback](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_reflection_annulus_pullback_weakDerivative),
  use
  [local integrability of the reflected pullback](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_reflection_annulus_pullback_locallyIntegrable),
  and then apply
  [the weak product rule for the annular taper](lean:JJMath.Uniformization.euclideanSobolev_annulus_taper_mul_weakDerivative).
-/
theorem euclideanSobolev_unit_ball_radial_reflection_annulus_weakDerivative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H)
      (fun x : H ↦
        (3 - 2 * ‖x‖) * w (euclideanSobolevUnitBallRadialReflection x))
      (fun x : H ↦
        (3 - 2 * ‖x‖) •
            (dw (euclideanSobolevUnitBallRadialReflection x)).comp
              (fderiv ℝ (fun y : H ↦
                euclideanSobolevUnitBallRadialReflection y) x) +
          w (euclideanSobolevUnitBallRadialReflection x) •
            fderiv ℝ (fun y : H ↦ (3 : ℝ) - 2 * ‖y‖) x) := by
  have hpull :
      IsWeakDerivativeOnEuclideanRegionWithValues
        (euclideanSobolevUnitBallReflectionAnnulus H)
        (fun x : H ↦ w (euclideanSobolevUnitBallRadialReflection x))
        (fun x : H ↦
          (dw (euclideanSobolevUnitBallRadialReflection x)).comp
            (fderiv ℝ (fun y : H ↦
              euclideanSobolevUnitBallRadialReflection y) x)) :=
    euclideanSobolev_unit_ball_radial_reflection_annulus_pullback_weakDerivative
      hweak _hw _hdw
  have hpull_loc :
      LocallyIntegrableOn
        (fun x : H ↦ w (euclideanSobolevUnitBallRadialReflection x))
        (euclideanSobolevUnitBallReflectionAnnulus H)
        (MeasureTheory.volume : Measure H) :=
    euclideanSobolev_unit_ball_radial_reflection_annulus_pullback_locallyIntegrable
      _hw
  exact
    euclideanSobolev_annulus_taper_mul_weakDerivative
      (u := fun x : H ↦ w (euclideanSobolevUnitBallRadialReflection x))
      (du := fun x : H ↦
        (dw (euclideanSobolevUnitBallRadialReflection x)).comp
          (fderiv ℝ (fun y : H ↦
            euclideanSobolevUnitBallRadialReflection y) x))
      hpull hpull_loc


/--
%%handwave
name:
  Interior trace scales from the unit sphere to a centered sphere
statement:
  Let \(r>0\).  If the pullback \(z\mapsto w(rz)\) has \(L^1\) trace
  \(\sigma\) on the unit sphere from the inside, and is square-integrable in
  the unit ball, then \(w\) has the inside \(L^1\) trace
  \(y\mapsto \sigma(r^{-1}y)\) on the sphere \(\|y\|=r\).
proof:
  Rescale the inner collar \(r-\varepsilon<\|x\|<r\) by \(x=rz\).  The
  normalized collar integral is bounded by a fixed finite Jacobian constant
  times the corresponding unit-sphere expression with width
  \(\varepsilon/r\).  Since \(\varepsilon/r\downarrow0\), the unit trace
  convergence implies the radius-\(r\) trace convergence.
-/
theorem hasL1TraceFromInsideSphere_centered_smul_of_unit
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {r : ℝ} (hr_pos : 0 < r)
    {w σ : H → ℝ}
    (hw_pull : MemLp (fun z : H ↦ w (r • z)) 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hσ_meas : Measurable σ)
    (htrace : HasL1TraceFromInsideSphere (H := H) 1
      (fun z : H ↦ w (r • z)) σ) :
    HasL1TraceFromInsideSphere (H := H) r w
      (fun y : H ↦ σ (r⁻¹ • y)) := by
  classical
  let μ : Measure H := MeasureTheory.volume
  let T : H → H := fun z ↦ r • z
  let S : H → H := fun x ↦ r⁻¹ • x
  let τ : H → ℝ := fun y ↦ σ (S y)
  let F : H → ℝ≥0∞ := fun x ↦
    ENNReal.ofReal ‖w x - τ (((r / ‖x‖) : ℝ) • x)‖
  let G : H → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal ‖w (T z) - σ (((1 / ‖z‖) : ℝ) • z)‖
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hr_inv_pos : 0 < r⁻¹ := inv_pos.mpr hr_pos
  have hT_lip :
      LipschitzOnWith ‖r‖₊ T (Set.univ : Set H) := by
    simpa [T] using
      ((lipschitzWith_smul (β := H) r).lipschitzOnWith
        (s := (Set.univ : Set H)))
  rcases
    lipschitzOnWith_volume_image_le_smul
      (H := H) (A := (Set.univ : Set H)) (F := T)
      (L := ‖r‖₊) hT_lip with
    ⟨C, hC_ne_top, hT_image_le⟩
  let D : ℝ≥0∞ := C * ENNReal.ofReal (1 / r)
  have hD_ne_top : D ≠ ⊤ := by
    exact ENNReal.mul_ne_top hC_ne_top ENNReal.ofReal_ne_top
  have hδ :
      Filter.Tendsto (fun ε : ℝ ↦ ε / r)
        (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hnhds :
          Filter.Tendsto (fun ε : ℝ ↦ ε / r)
            (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        simpa [div_eq_mul_inv] using
          (Filter.tendsto_id.mul_const r⁻¹ :
            Filter.Tendsto (fun ε : ℝ ↦ ε * r⁻¹)
              (𝓝 (0 : ℝ)) (𝓝 (0 * r⁻¹)))
      exact hnhds.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact div_pos hε hr_pos
  have hunit :
      Filter.Tendsto
        (fun ε : ℝ ↦
          ENNReal.ofReal ((ε / r)⁻¹) *
            ∫⁻ z in {z : H | (1 : ℝ) - ε / r < ‖z‖ ∧ ‖z‖ < 1},
              G z ∂μ)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [HasL1TraceFromInsideSphere, G, T, μ, Function.comp_def] using
      htrace.comp hδ
  have hunit_scaled :
      Filter.Tendsto
        (fun ε : ℝ ↦
          D *
            (ENNReal.ofReal ((ε / r)⁻¹) *
              ∫⁻ z in {z : H | (1 : ℝ) - ε / r < ‖z‖ ∧ ‖z‖ < 1},
                G z ∂μ))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    have hmul := ENNReal.Tendsto.const_mul hunit (Or.inr hD_ne_top)
    simpa [mul_assoc] using hmul
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < r :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr_pos)
  have hbound :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal (1 / ε) *
          ∫⁻ x in {x : H | r - ε < ‖x‖ ∧ ‖x‖ < r}, F x ∂μ ≤
        D *
          (ENNReal.ofReal ((ε / r)⁻¹) *
            ∫⁻ z in {z : H | (1 : ℝ) - ε / r < ‖z‖ ∧ ‖z‖ < 1},
              G z ∂μ) := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε_pos hε_lt
    have hε_pos' : 0 < ε := hε_pos
    let Sx : Set H := {x : H | r - ε < ‖x‖ ∧ ‖x‖ < r}
    let Sz : Set H := {z : H | (1 : ℝ) - ε / r < ‖z‖ ∧ ‖z‖ < 1}
    have hSx_meas : MeasurableSet Sx := by
      dsimp [Sx]
      measurability
    have hSz_meas : MeasurableSet Sz := by
      dsimp [Sz]
      measurability
    have hSz_subset_ball : Sz ⊆ Metric.ball (0 : H) 1 := by
      intro z hz
      dsimp [Sz] at hz
      simpa [Metric.mem_ball, dist_eq_norm] using hz.2
    have hS_meas : Measurable S := by
      dsimp [S]
      measurability
    have hS_maps : Set.MapsTo S Sx Sz := by
      intro x hx
      have hnorm : ‖S x‖ = r⁻¹ * ‖x‖ := by
        simpa [S, Real.norm_of_nonneg hr_inv_pos.le] using
          (norm_smul (r⁻¹ : ℝ) x)
      dsimp [Sx, Sz] at hx ⊢
      constructor
      · have hleft : r⁻¹ * (r - ε) < r⁻¹ * ‖x‖ :=
          mul_lt_mul_of_pos_left hx.1 hr_inv_pos
        have hcoef : r⁻¹ * (r - ε) = 1 - ε / r := by
          field_simp [hr_ne]
        rwa [← hcoef, hnorm]
      · have hright : r⁻¹ * ‖x‖ < r⁻¹ * r :=
          mul_lt_mul_of_pos_left hx.2 hr_inv_pos
        have hright' : r⁻¹ * ‖x‖ < 1 := by
          simpa [inv_mul_cancel₀ hr_ne] using hright
        simpa [hnorm] using hright'
    have hmap_le :
        Measure.map S (μ.restrict Sx) ≤ C • μ.restrict Sz := by
      refine Measure.le_iff.2 ?_
      intro B hB
      rw [Measure.map_apply hS_meas hB, Measure.smul_apply,
        Measure.restrict_apply hB]
      have hpre_meas : MeasurableSet (S ⁻¹' B) :=
        hB.preimage hS_meas
      rw [Measure.restrict_apply hpre_meas]
      calc
        μ (S ⁻¹' B ∩ Sx)
            ≤ μ (T '' (B ∩ Sz)) := by
              exact measure_mono (by
                intro x hx
                refine ⟨S x, ⟨hx.1, hS_maps hx.2⟩, ?_⟩
                simp [T, S, smul_smul, mul_inv_cancel₀ hr_ne])
        _ ≤ C * μ (B ∩ Sz) := by
              simpa [μ] using
                hT_image_le (B ∩ Sz) (Set.subset_univ _)
    have hG_sz : AEMeasurable G (μ.restrict Sz) := by
      have hwpull_sz :
          AEMeasurable (fun z : H ↦ w (r • z)) (μ.restrict Sz) := by
        have hmem : MemLp (fun z : H ↦ w (r • z)) 2 (μ.restrict Sz) :=
          hw_pull.mono_measure
            (by
              simpa [μ] using
                Measure.restrict_mono_set
                  (MeasureTheory.volume : Measure H) hSz_subset_ball)
        exact hmem.aestronglyMeasurable.aemeasurable
      have hπ_meas :
          Measurable (fun z : H ↦ ((1 / ‖z‖) : ℝ) • z) := by
        measurability
      have hσπ :
          AEMeasurable
            (fun z : H ↦ σ (((1 / ‖z‖) : ℝ) • z)) (μ.restrict Sz) :=
        hσ_meas.comp_aemeasurable hπ_meas.aemeasurable
      have hdiff :
          AEMeasurable
            (fun z : H ↦ w (r • z) - σ (((1 / ‖z‖) : ℝ) • z))
            (μ.restrict Sz) :=
        hwpull_sz.sub hσπ
      exact ENNReal.measurable_ofReal.comp_aemeasurable hdiff.norm
    have hG_map :
        AEMeasurable G (Measure.map S (μ.restrict Sx)) :=
      hG_sz.mono_ac (Measure.absolutelyContinuous_of_le_smul hmap_le)
    have hmap_eq :
        ∫⁻ z, G z ∂Measure.map S (μ.restrict Sx) =
          ∫⁻ x in Sx, G (S x) ∂μ := by
      simpa [μ] using
        lintegral_map' (μ := μ.restrict Sx) (f := G) (g := S)
          hG_map hS_meas.aemeasurable
    have hIx_eq :
        (∫⁻ x in Sx, F x ∂μ) =
          ∫⁻ x in Sx, G (S x) ∂μ := by
      refine setLIntegral_congr_fun hSx_meas ?_
      intro x hx
      have hxnorm_pos : 0 < ‖x‖ := by
        dsimp [Sx] at hx
        nlinarith [hx.1, hε_lt]
      have hSnorm : ‖S x‖ = r⁻¹ * ‖x‖ := by
        simpa [S, Real.norm_of_nonneg hr_inv_pos.le] using
          (norm_smul (r⁻¹ : ℝ) x)
      have hTS : T (S x) = x := by
        simp [T, S, smul_smul, mul_inv_cancel₀ hr_ne]
      have hproj :
          ((1 / ‖S x‖) : ℝ) • S x =
            S (((r / ‖x‖) : ℝ) • x) := by
        calc
          ((1 / ‖S x‖) : ℝ) • S x
              = ((1 / (r⁻¹ * ‖x‖)) : ℝ) • (r⁻¹ • x) := by
                  rw [hSnorm]
          _ = ((r / ‖x‖) : ℝ) • (r⁻¹ • x) := by
                  congr 1
                  field_simp [hr_ne, ne_of_gt hxnorm_pos]
          _ = S (((r / ‖x‖) : ℝ) • x) := by
                  simp [S, smul_smul, mul_comm]
      have hproj' :
          ‖S x‖⁻¹ • S x =
            S (((r / ‖x‖) : ℝ) • x) := by
        simpa [one_div] using hproj
      simp [F, G, τ, hTS, hproj']
    have hIx_le :
        (∫⁻ x in Sx, F x ∂μ) ≤
          C * ∫⁻ z in Sz, G z ∂μ := by
      calc
        (∫⁻ x in Sx, F x ∂μ)
            = ∫⁻ x in Sx, G (S x) ∂μ := hIx_eq
        _ = ∫⁻ z, G z ∂Measure.map S (μ.restrict Sx) := hmap_eq.symm
        _ ≤ ∫⁻ z, G z ∂(C • μ.restrict Sz) :=
              lintegral_mono' hmap_le le_rfl
        _ = C * ∫⁻ z in Sz, G z ∂μ := by
              simpa [smul_eq_mul] using
                (lintegral_smul_measure
                  (μ := μ.restrict Sz) (f := G) (c := C))
    have hofReal_scale :
        ENNReal.ofReal (1 / ε) =
          ENNReal.ofReal (1 / r) *
            ENNReal.ofReal ((ε / r)⁻¹) := by
      have hnonneg : 0 ≤ (1 / r : ℝ) :=
        div_nonneg zero_le_one hr_pos.le
      rw [← ENNReal.ofReal_mul hnonneg]
      congr 1
      field_simp [ne_of_gt hε_pos', hr_ne]
    calc
      ENNReal.ofReal (1 / ε) *
          ∫⁻ x in {x : H | r - ε < ‖x‖ ∧ ‖x‖ < r}, F x ∂μ
          = ENNReal.ofReal (1 / ε) *
              ∫⁻ x in Sx, F x ∂μ := rfl
      _ ≤ ENNReal.ofReal (1 / ε) *
            (C * ∫⁻ z in Sz, G z ∂μ) := by
              exact mul_le_mul_right hIx_le _
      _ =
          D *
            (ENNReal.ofReal ((ε / r)⁻¹) *
              ∫⁻ z in Sz, G z ∂μ) := by
            rw [hofReal_scale]
            simp [D, mul_assoc, mul_left_comm, mul_comm]
      _ =
          D *
            (ENNReal.ofReal ((ε / r)⁻¹) *
              ∫⁻ z in {z : H | (1 : ℝ) - ε / r < ‖z‖ ∧ ‖z‖ < 1},
                G z ∂μ) := rfl
  rw [HasL1TraceFromInsideSphere]
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hunit_scaled
      (Filter.Eventually.of_forall fun _ε ↦ zero_le)
      (by
        simpa [F, τ, μ] using hbound)


/--
%%handwave
name:
  Interior \(L^1\) trace for Sobolev functions on centered balls
statement:
  A scalar \(W^{1,2}\) function on a centered ball \(B(0,r)\), with \(r>0\),
  has a measurable \(L^1\) trace representative on the sphere \(\|x\|=r\)
  from the inside.
proof:
  Pull the function back by the dilation \(z\mapsto rz\), apply
  [a scalar \(W^{1,2}\) function on the unit ball has an \(L^1\) trace on the
  unit sphere from the inside](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_has_l1_trace_from_inside_core),
  and push the trace representative forward to the sphere \(\|x\|=r\).
  The collar convergence follows from the dilation change of variables.
-/
theorem euclideanSobolev_centered_ball_has_l1_trace_from_inside
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {r : ℝ} (hr_pos : 0 < r)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) r) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) r)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) r))) :
    ∃ τ : H → ℝ,
      Measurable τ ∧
        HasL1TraceFromInsideSphere (H := H) r w τ := by
  let T : H → H := fun z ↦ r • z
  let wpull : H → ℝ := fun z ↦ w (T z)
  let dwpull : H → H →L[ℝ] ℝ := fun z ↦ r • dw (T z)
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hpre_T :
      T ⁻¹' Metric.ball (0 : H) r = Metric.ball (0 : H) 1 := by
    have hpre :=
      preimage_const_smul_ball_zero_of_pos
        (H := H) (a := r) (R := (1 : ℝ)) hr_pos
    simpa [T, mul_one] using hpre
  have hweak_pull :
      IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.ball (0 : H) 1) wpull dwpull := by
    have hweak_pre :=
      IsWeakDerivativeOnEuclideanRegionWithValues.comp_smul
        _hweak hr_ne
    simpa [wpull, dwpull, T, hpre_T] using hweak_pre
  have hw_pull : MemLp wpull 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
    have hw' : MemLp (fun z : H ↦ w (r • z)) 2
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
      simpa [mul_one] using
        memLp_comp_const_smul_of_memLp_restrict_ball_zero
          (H := H) (E := ℝ) (a := r) (R := (1 : ℝ)) hr_pos
          (by simpa [mul_one] using _hw)
    simpa [wpull, T] using hw'
  have hdw_pull : MemLp dwpull 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
    have hdw_comp : MemLp (fun z : H ↦ dw (r • z)) 2
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
      simpa [mul_one] using
        memLp_comp_const_smul_of_memLp_restrict_ball_zero
          (H := H) (E := H →L[ℝ] ℝ) (a := r) (R := (1 : ℝ)) hr_pos
          (by simpa [mul_one] using _hdw)
    have hdw_scaled : MemLp (fun z : H ↦ r • dw (r • z)) 2
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
      simpa using hdw_comp.const_smul r
    simpa [dwpull, T] using hdw_scaled
  rcases
    euclideanSobolev_unit_ball_has_l1_trace_from_inside_core
      hweak_pull hw_pull hdw_pull with
    ⟨σ, hσ_meas, hσ_trace⟩
  refine ⟨fun y : H ↦ σ (r⁻¹ • y), ?_, ?_⟩
  · exact hσ_meas.comp (by measurability)
  · simpa [wpull, T] using
      hasL1TraceFromInsideSphere_centered_smul_of_unit
        (H := H) (r := r) hr_pos
        (w := w) (σ := σ)
        (by simpa [wpull, T] using hw_pull)
        hσ_meas
        (by simpa [wpull, T] using hσ_trace)


/--
%%handwave
name:
  Collar distortion estimate for unit radial reflection
statement:
  For radial reflection across the unit sphere, the normalized exterior
  collar trace integral of the reflected function is bounded, for all
  sufficiently small collar widths, by a fixed finite multiple of the
  corresponding normalized interior collar trace integral.
proof:
  The reflection sends \(1<\|x\|<1+\varepsilon\) bijectively to
  \(1-\varepsilon<\|y\|<1\), preserves radial projection to the unit sphere,
  and is bi-Lipschitz with constants independent of
  \(0<\varepsilon<1/2\).  Apply the finite-dimensional Haar-measure distortion
  bound for the inverse Lipschitz map.
-/
theorem unit_radial_reflection_exterior_trace_integral_le_interior
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w τ : H → ℝ}
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hτ_meas : Measurable τ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal (1 / ε) *
          ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
            ENNReal.ofReal
              ‖w (euclideanSobolevUnitBallRadialReflection x) -
                τ (((1 / ‖x‖) : ℝ) • x)‖
              ∂MeasureTheory.volume ≤
          C *
            (ENNReal.ofReal (1 / ε) *
              ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
                ENNReal.ofReal
                  ‖w y - τ (((1 / ‖y‖) : ℝ) • y)‖
                  ∂MeasureTheory.volume) := by
  let Ω₀ : Set H := euclideanSobolevUnitBallPunctured H
  let R : H → H := euclideanSobolevUnitBallRadialReflection
  let μ : Measure H := MeasureTheory.volume
  let F : H → ℝ≥0∞ := fun y : H ↦
    ENNReal.ofReal ‖w y - τ (((1 / ‖y‖) : ℝ) • y)‖
  rcases
    lipschitzOnWith_volume_image_le_smul
      (H := H) (A := Ω₀) (F := R) (L := (12 : ℝ≥0))
      (by
        simpa [Ω₀, R] using
          euclideanSobolevUnitBallRadialReflection_lipschitzOnWith_punctured
            (H := H)) with
    ⟨C, hC_ne_top, hR_image_le⟩
  refine ⟨C, hC_ne_top, ?_⟩
  have hR_meas : Measurable R := by
    simpa [R] using euclideanSobolevUnitBallRadialReflection_measurable
      (H := H)
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < (1 / 2 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε_pos hε_lt
  let S : Set H := {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε}
  let T : Set H := {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1}
  have hS_meas : MeasurableSet S := by
    dsimp [S]
    measurability
  have hT_meas : MeasurableSet T := by
    dsimp [T]
    measurability
  have hT_subset_Ω₀ : T ⊆ Ω₀ := by
    intro y hy
    dsimp [T, Ω₀, euclideanSobolevUnitBallPunctured] at hy ⊢
    exact ⟨by nlinarith [hy.1, hε_lt], hy.2⟩
  have hT_subset_ball : T ⊆ Metric.ball (0 : H) 1 := by
    intro y hy
    dsimp [T] at hy
    simpa [Metric.mem_ball, dist_eq_norm] using hy.2
  have hS_subset_annulus : S ⊆ euclideanSobolevUnitBallReflectionAnnulus H := by
    intro x hx
    dsimp [S, euclideanSobolevUnitBallReflectionAnnulus] at hx ⊢
    exact ⟨hx.1, by nlinarith [hx.2, hε_lt]⟩
  have hR_maps : Set.MapsTo R S T := by
    intro x hx
    have hxpos : 0 < ‖x‖ := by nlinarith [hx.1]
    have hxle : ‖x‖ ≤ 2 := by nlinarith [hx.2, hε_lt]
    have hnorm :
        ‖R x‖ = 2 - ‖x‖ := by
      simpa [R] using
        euclideanSobolevUnitBallRadialReflection_norm_of_norm_pos_of_norm_le_two
          (H := H) (x := x) hxpos hxle
    dsimp [T]
    constructor <;> rw [hnorm] <;> nlinarith [hx.1, hx.2]
  have hR_involutive_S : ∀ x ∈ S, R (R x) = x := by
    intro x hx
    simpa [R] using
      euclideanSobolevUnitBallRadialReflection_involutive_on_annulus
        (H := H) (x := x) (hS_subset_annulus hx)
  have hprojection : ∀ x ∈ S,
      ((1 / ‖R x‖) : ℝ) • R x = ((1 / ‖x‖) : ℝ) • x := by
    intro x hx
    have hxpos : 0 < ‖x‖ := by nlinarith [hx.1]
    have hxle : ‖x‖ ≤ 2 := by nlinarith [hx.2, hε_lt]
    have hcoef_pos : 0 < 2 - ‖x‖ := by nlinarith [hx.2, hε_lt]
    have hnorm :
        ‖R x‖ = 2 - ‖x‖ := by
      simpa [R] using
        euclideanSobolevUnitBallRadialReflection_norm_of_norm_pos_of_norm_le_two
          (H := H) (x := x) hxpos hxle
    simp only [R, euclideanSobolevUnitBallRadialReflection] at hnorm ⊢
    rw [hnorm, smul_smul]
    congr 1
    field_simp [ne_of_gt hxpos, ne_of_gt hcoef_pos]
  have hmap_le :
      Measure.map R (μ.restrict S) ≤ C • μ.restrict T := by
    refine Measure.le_iff.2 ?_
    intro B hB
    rw [Measure.map_apply hR_meas hB, Measure.smul_apply,
      Measure.restrict_apply hB]
    have hpre_meas : MeasurableSet (R ⁻¹' B) := hB.preimage hR_meas
    rw [Measure.restrict_apply hpre_meas]
    calc
      μ (R ⁻¹' B ∩ S)
          ≤ μ (R '' (B ∩ T)) := by
            exact measure_mono (by
              intro x hx
              exact
                ⟨R x, ⟨hx.1, hR_maps hx.2⟩,
                  hR_involutive_S x hx.2⟩)
      _ ≤ C * μ (B ∩ T) :=
            hR_image_le (B ∩ T)
              (Set.inter_subset_right.trans hT_subset_Ω₀)
  have hF_T : AEMeasurable F (μ.restrict T) := by
    have hwT_mem : MemLp w 2 (μ.restrict T) :=
      _hw.mono_measure
        (by
          simpa [μ] using
            Measure.restrict_mono_set
              (MeasureTheory.volume : Measure H) hT_subset_ball)
    have hwT : AEMeasurable w (μ.restrict T) :=
      hwT_mem.aestronglyMeasurable.aemeasurable
    have hπ_meas :
        Measurable (fun y : H ↦ ((1 / ‖y‖) : ℝ) • y) := by
      measurability
    have hτπ : AEMeasurable
        (fun y : H ↦ τ (((1 / ‖y‖) : ℝ) • y)) (μ.restrict T) :=
      hτ_meas.comp_aemeasurable hπ_meas.aemeasurable
    have hdiff :
        AEMeasurable
          (fun y : H ↦ w y - τ (((1 / ‖y‖) : ℝ) • y))
          (μ.restrict T) :=
      hwT.sub hτπ
    exact ENNReal.measurable_ofReal.comp_aemeasurable hdiff.norm
  have hF_map : AEMeasurable F (Measure.map R (μ.restrict S)) :=
    hF_T.mono_ac (Measure.absolutelyContinuous_of_le_smul hmap_le)
  have hmap_eq :
      ∫⁻ y, F y ∂Measure.map R (μ.restrict S) =
        ∫⁻ x in S, F (R x) ∂μ := by
    simpa [μ] using
      lintegral_map' (μ := μ.restrict S) (f := F) (g := R)
        hF_map hR_meas.aemeasurable
  have hext_eq :
      (∫⁻ x in S,
        ENNReal.ofReal
          ‖w (R x) - τ (((1 / ‖x‖) : ℝ) • x)‖ ∂μ) =
        ∫⁻ x in S, F (R x) ∂μ := by
    refine setLIntegral_congr_fun hS_meas ?_
    intro x hx
    change
      ENNReal.ofReal ‖w (R x) - τ (((1 / ‖x‖) : ℝ) • x)‖ =
        ENNReal.ofReal
          ‖w (R x) - τ (((1 / ‖R x‖) : ℝ) • R x)‖
    rw [← hprojection x hx]
  have hlin_le :
      (∫⁻ x in S,
        ENNReal.ofReal
          ‖w (R x) - τ (((1 / ‖x‖) : ℝ) • x)‖ ∂μ) ≤
        C * ∫⁻ y in T, F y ∂μ := by
    calc
      (∫⁻ x in S,
        ENNReal.ofReal
          ‖w (R x) - τ (((1 / ‖x‖) : ℝ) • x)‖ ∂μ)
          = ∫⁻ x in S, F (R x) ∂μ := hext_eq
      _ = ∫⁻ y, F y ∂Measure.map R (μ.restrict S) := hmap_eq.symm
      _ ≤ ∫⁻ y, F y ∂(C • μ.restrict T) :=
            lintegral_mono' hmap_le le_rfl
      _ = C * ∫⁻ y in T, F y ∂μ := by
            simpa [smul_eq_mul] using
              (lintegral_smul_measure
                (μ := μ.restrict T) (f := F) (c := C))
  calc
    ENNReal.ofReal (1 / ε) *
        ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
          ENNReal.ofReal
            ‖w (euclideanSobolevUnitBallRadialReflection x) -
              τ (((1 / ‖x‖) : ℝ) • x)‖
          ∂MeasureTheory.volume
        = ENNReal.ofReal (1 / ε) *
          (∫⁻ x in S,
            ENNReal.ofReal
              ‖w (R x) - τ (((1 / ‖x‖) : ℝ) • x)‖ ∂μ) := by
            rfl
    _ ≤ ENNReal.ofReal (1 / ε) *
          (C * ∫⁻ y in T, F y ∂μ) := by
            exact mul_le_mul_right hlin_le _
    _ = C *
          (ENNReal.ofReal (1 / ε) *
            ∫⁻ y in T, F y ∂μ) := by
            ac_rfl
    _ =
        C *
          (ENNReal.ofReal (1 / ε) *
            ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
              ENNReal.ofReal
                ‖w y - τ (((1 / ‖y‖) : ℝ) • y)‖
              ∂MeasureTheory.volume) := by
            rfl

/--
%%handwave
name:
  Reflected copy has the exterior unit trace
statement:
  If \(w\) has an \(L^1\) trace \(\tau\) on the unit sphere from inside the
  unit ball, and \(w\) is square-integrable on the unit ball, then the radial
  reflection \(x\mapsto w(((2-\|x\|)/\|x\|)x)\) has the same \(L^1\) trace on
  the unit sphere from the outside.
proof:
  The radial reflection sends the exterior collar
  \(1<\|x\|<1+\varepsilon\) to the interior collar
  \(1-\varepsilon<\|y\|<1\) on each ray.  On collars with
  \(\varepsilon<1/2\) the map is bi-Lipschitz with uniformly bounded
  distortion, so the normalized exterior trace integral is bounded by a fixed
  multiple of the normalized interior trace integral, which tends to zero.
-/
theorem hasL1TraceFromOutsideSphere_unit_radial_reflection_of_inside
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w τ : H → ℝ}
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hτ_meas : Measurable τ)
    (_htrace : HasL1TraceFromInsideSphere (H := H) 1 w τ) :
    HasL1TraceFromOutsideSphere (H := H) 1
      (fun x : H ↦ w (euclideanSobolevUnitBallRadialReflection x))
      τ := by
  rcases
    unit_radial_reflection_exterior_trace_integral_le_interior
      (H := H) (w := w) (τ := τ) _hw hτ_meas with
    ⟨C, hC_ne_top, hbound⟩
  have hinner_scaled :
      Filter.Tendsto
        (fun ε : ℝ ↦
          C *
            (ENNReal.ofReal (1 / ε) *
              ∫⁻ y in {y : H | (1 : ℝ) - ε < ‖y‖ ∧ ‖y‖ < 1},
                ENNReal.ofReal
                  ‖w y - τ (((1 / ‖y‖) : ℝ) • y)‖
                  ∂MeasureTheory.volume))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    have hmul :=
      ENNReal.Tendsto.const_mul _htrace (Or.inr hC_ne_top)
    simpa [HasL1TraceFromInsideSphere, mul_assoc] using hmul
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hinner_scaled
      (Filter.Eventually.of_forall fun _ε ↦ zero_le)
      hbound

/--
%%handwave
name:
  Tapered reflection trace integral is controlled by raw trace plus taper error
statement:
  In the exterior unit collar, the normalized \(L^1\) trace expression for
  the tapered reflected function is bounded by the corresponding expression
  for the untapered reflected function plus the normalized \(L^1\)-mass of
  the taper error \((3-2\|x\|-1)w(Rx)\).
proof:
  Apply the triangle inequality pointwise:
  \[
    |(3-2\|x\|)w(Rx)-\tau(\pi x)|
      \le |w(Rx)-\tau(\pi x)|
        + |(3-2\|x\|-1)w(Rx)|.
  \]
  Then use monotonicity and additivity of the nonnegative integral.
-/
theorem unit_radial_reflection_taper_trace_integral_le_raw_add_error
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H]
    {w τ : H → ℝ}
    (hraw_meas :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        AEMeasurable
          (fun x : H ↦
            ENNReal.ofReal
              ‖w (euclideanSobolevUnitBallRadialReflection x) -
                τ (((1 / ‖x‖) : ℝ) • x)‖)
          (MeasureTheory.volume.restrict
            {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε})) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (1 / ε) *
        ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
          ENNReal.ofReal
            ‖(3 - 2 * ‖x‖) *
                w (euclideanSobolevUnitBallRadialReflection x) -
              τ (((1 / ‖x‖) : ℝ) • x)‖
            ∂MeasureTheory.volume ≤
        (ENNReal.ofReal (1 / ε) *
          ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
            ENNReal.ofReal
              ‖w (euclideanSobolevUnitBallRadialReflection x) -
                τ (((1 / ‖x‖) : ℝ) • x)‖
              ∂MeasureTheory.volume) +
          (ENNReal.ofReal (1 / ε) *
            ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
              ENNReal.ofReal
                ‖((3 - 2 * ‖x‖) - 1) *
                    w (euclideanSobolevUnitBallRadialReflection x)‖
                ∂MeasureTheory.volume) := by
  filter_upwards [hraw_meas] with ε hraw
  let S : Set H := {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε}
  let a : H → ℝ := fun x : H ↦ 3 - 2 * ‖x‖
  let R : H → H := euclideanSobolevUnitBallRadialReflection
  let π : H → H := fun x : H ↦ ((1 / ‖x‖) : ℝ) • x
  let raw : H → ℝ≥0∞ := fun x : H ↦
    ENNReal.ofReal ‖w (R x) - τ (π x)‖
  let err : H → ℝ≥0∞ := fun x : H ↦
    ENNReal.ofReal ‖(a x - 1) * w (R x)‖
  let tapered : H → ℝ≥0∞ := fun x : H ↦
    ENNReal.ofReal ‖a x * w (R x) - τ (π x)‖
  have hpoint : ∀ x : H, tapered x ≤ raw x + err x := by
    intro x
    have hdecomp :
        a x * w (R x) - τ (π x) =
          (w (R x) - τ (π x)) + (a x - 1) * w (R x) := by
      ring
    change
      ENNReal.ofReal ‖a x * w (R x) - τ (π x)‖ ≤
        ENNReal.ofReal ‖w (R x) - τ (π x)‖ +
          ENNReal.ofReal ‖(a x - 1) * w (R x)‖
    calc
      ENNReal.ofReal ‖a x * w (R x) - τ (π x)‖
          ≤ ENNReal.ofReal
              (‖w (R x) - τ (π x)‖ +
                ‖(a x - 1) * w (R x)‖) := by
              exact ENNReal.ofReal_le_ofReal
                (by
                  rw [hdecomp]
                  exact norm_add_le _ _)
      _ = ENNReal.ofReal ‖w (R x) - τ (π x)‖ +
            ENNReal.ofReal ‖(a x - 1) * w (R x)‖ := by
              rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  have hlin_mono :
      ∫⁻ x in S, tapered x ∂MeasureTheory.volume ≤
        ∫⁻ x in S, raw x + err x ∂MeasureTheory.volume :=
    lintegral_mono hpoint
  have hraw' : AEMeasurable raw (MeasureTheory.volume.restrict S) := by
    simpa [raw, R, π, S] using hraw
  have hsplit :
      ∫⁻ x in S, raw x + err x ∂MeasureTheory.volume =
        (∫⁻ x in S, raw x ∂MeasureTheory.volume) +
          ∫⁻ x in S, err x ∂MeasureTheory.volume := by
    exact lintegral_add_left' (μ := MeasureTheory.volume.restrict S) hraw' err
  calc
    ENNReal.ofReal (1 / ε) *
        ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
          ENNReal.ofReal
            ‖(3 - 2 * ‖x‖) *
                w (euclideanSobolevUnitBallRadialReflection x) -
              τ (((1 / ‖x‖) : ℝ) • x)‖
            ∂MeasureTheory.volume
        = ENNReal.ofReal (1 / ε) *
          ∫⁻ x in S, tapered x ∂MeasureTheory.volume := rfl
    _ ≤ ENNReal.ofReal (1 / ε) *
          ∫⁻ x in S, raw x + err x ∂MeasureTheory.volume := by
            exact mul_le_mul_right hlin_mono _
    _ = ENNReal.ofReal (1 / ε) *
          ((∫⁻ x in S, raw x ∂MeasureTheory.volume) +
            ∫⁻ x in S, err x ∂MeasureTheory.volume) := by
            rw [hsplit]
    _ =
        (ENNReal.ofReal (1 / ε) *
          ∫⁻ x in S, raw x ∂MeasureTheory.volume) +
          (ENNReal.ofReal (1 / ε) *
            ∫⁻ x in S, err x ∂MeasureTheory.volume) := by
            rw [mul_add]
    _ =
        (ENNReal.ofReal (1 / ε) *
          ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
            ENNReal.ofReal
              ‖w (euclideanSobolevUnitBallRadialReflection x) -
                τ (((1 / ‖x‖) : ℝ) • x)‖
              ∂MeasureTheory.volume) +
          (ENNReal.ofReal (1 / ε) *
            ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
              ENNReal.ofReal
                ‖((3 - 2 * ‖x‖) - 1) *
                    w (euclideanSobolevUnitBallRadialReflection x)‖
                ∂MeasureTheory.volume) := by
            rfl

/--
%%handwave
name:
  Unit exterior taper error is controlled by collar mass
statement:
  In the collar \(1<\|x\|<1+\varepsilon\), the normalized \(L^1\)-mass of
  the error \((3-2\|x\|-1)g(x)\) is bounded, for sufficiently small positive
  \(\varepsilon\), by twice the \(L^1\)-mass of \(g\) on that collar.
proof:
  On the collar, \(|3-2\|x\|-1|\le 2\varepsilon\).  The factor
  \(1/\varepsilon\) in the normalized trace expression cancels the
  \(\varepsilon\), and monotonicity of the nonnegative integral gives the
  estimate.
-/
theorem unit_outer_taper_error_trace_integral_le_two_collar_mass
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    {g : H → ℝ} :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (1 / ε) *
        ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
          ENNReal.ofReal ‖((3 - 2 * ‖x‖) - 1) * g x‖
            ∂MeasureTheory.volume ≤
        (2 : ℝ≥0∞) *
          ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
            ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε_pos : 0 < ε := hε
  let S : Set H := {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε}
  have hS_meas : MeasurableSet S := by
    dsimp [S]
    measurability
  have hpoint : ∀ x ∈ S,
      ENNReal.ofReal ‖((3 - 2 * ‖x‖) - 1) * g x‖ ≤
        ENNReal.ofReal (2 * ε) * ENNReal.ofReal ‖g x‖ := by
    intro x hx
    have htaper_nonpos : ((3 : ℝ) - 2 * ‖x‖) - 1 ≤ 0 := by
      nlinarith [hx.1]
    have htaper_le : |((3 : ℝ) - 2 * ‖x‖) - 1| ≤ 2 * ε := by
      rw [abs_of_nonpos htaper_nonpos]
      nlinarith [hx.2]
    calc
      ENNReal.ofReal ‖((3 - 2 * ‖x‖) - 1) * g x‖
          = ENNReal.ofReal (|((3 : ℝ) - 2 * ‖x‖) - 1| * ‖g x‖) := by
              simp [norm_mul, Real.norm_eq_abs]
      _ ≤ ENNReal.ofReal ((2 * ε) * ‖g x‖) := by
              exact ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right htaper_le (norm_nonneg _))
      _ = ENNReal.ofReal (2 * ε) * ENNReal.ofReal ‖g x‖ := by
              rw [ENNReal.ofReal_mul]
              nlinarith [hε_pos]
  have hlin :
      ∫⁻ x in S, ENNReal.ofReal ‖((3 - 2 * ‖x‖) - 1) * g x‖
          ∂MeasureTheory.volume ≤
        ∫⁻ x in S,
          ENNReal.ofReal (2 * ε) * ENNReal.ofReal ‖g x‖
          ∂MeasureTheory.volume :=
    setLIntegral_mono' hS_meas hpoint
  have hconst_ne_top : ENNReal.ofReal (2 * ε) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hprod :
      ENNReal.ofReal (1 / ε) * ENNReal.ofReal (2 * ε) =
        (2 : ℝ≥0∞) := by
    have hinv_nonneg : 0 ≤ (1 / ε : ℝ) :=
      div_nonneg zero_le_one hε_pos.le
    rw [← ENNReal.ofReal_mul hinv_nonneg]
    have hmul : (1 / ε) * (2 * ε) = (2 : ℝ) := by
      field_simp [ne_of_gt hε_pos]
    rw [hmul]
    norm_num
  calc
    ENNReal.ofReal (1 / ε) *
        ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
          ENNReal.ofReal ‖((3 - 2 * ‖x‖) - 1) * g x‖
            ∂MeasureTheory.volume
        = ENNReal.ofReal (1 / ε) *
          ∫⁻ x in S,
            ENNReal.ofReal ‖((3 - 2 * ‖x‖) - 1) * g x‖
              ∂MeasureTheory.volume := rfl
    _ ≤ ENNReal.ofReal (1 / ε) *
          ∫⁻ x in S,
            ENNReal.ofReal (2 * ε) * ENNReal.ofReal ‖g x‖
              ∂MeasureTheory.volume := by
            exact mul_le_mul_right hlin _
    _ = ENNReal.ofReal (1 / ε) *
          (ENNReal.ofReal (2 * ε) *
            ∫⁻ x in S, ENNReal.ofReal ‖g x‖
              ∂MeasureTheory.volume) := by
            rw [lintegral_const_mul' (μ := MeasureTheory.volume.restrict S)
              (r := ENNReal.ofReal (2 * ε))
              (f := fun x : H ↦ ENNReal.ofReal ‖g x‖) hconst_ne_top]
    _ = (2 : ℝ≥0∞) *
          ∫⁻ x in S, ENNReal.ofReal ‖g x‖
            ∂MeasureTheory.volume := by
            rw [← mul_assoc, hprod]
    _ = (2 : ℝ≥0∞) *
          ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
            ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume := rfl

private theorem unit_radial_reflection_taper_error_pullback_memLp
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ}
    (hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    MemLp (fun x : H ↦ w (euclideanSobolevUnitBallRadialReflection x))
      2
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)) := by
  let U : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let Ω₀ : Set H := euclideanSobolevUnitBallPunctured H
  let B : Set H := Metric.ball (0 : H) 1
  let R : H → H := euclideanSobolevUnitBallRadialReflection
  let μ : Measure H := MeasureTheory.volume
  have hR_meas : Measurable R := by
    simpa [R] using euclideanSobolevUnitBallRadialReflection_measurable
      (H := H)
  rcases
    map_restrict_le_smul_of_inverse_lipschitzOnWith
      (U := U) (Ω := Ω₀) (T := R) (S := R)
      (L := (12 : ℝ≥0))
      hR_meas
      (by
        simpa [U, Ω₀, R] using
          euclideanSobolevUnitBallRadialReflection_mapsTo_annulus_punctured
            (H := H))
      (by
        intro x hx
        simpa [U, R] using
          euclideanSobolevUnitBallRadialReflection_involutive_on_annulus
            (H := H) (x := x) hx)
      (by
        simpa [Ω₀, R] using
          euclideanSobolevUnitBallRadialReflection_lipschitzOnWith_punctured
            (H := H)) with
    ⟨D, hD_ne_top, hmap_le⟩
  have hΩ₀_subset : Ω₀ ⊆ B := by
    simpa [Ω₀, B] using
      euclideanSobolevUnitBallPunctured_subset_unit_ball (H := H)
  have hmeasure_le : μ.restrict Ω₀ ≤ μ.restrict B :=
    Measure.restrict_mono_set μ hΩ₀_subset
  have hwΩ₀ : MemLp w 2 (μ.restrict Ω₀) :=
    hw.mono_measure (by simpa [μ, B] using hmeasure_le)
  have hmap_le' :
      Measure.map R (μ.restrict U) ≤ D • μ.restrict Ω₀ := by
    simpa [μ] using hmap_le
  have hw_map : MemLp w 2 (Measure.map R (μ.restrict U)) :=
    hwΩ₀.of_measure_le_smul hD_ne_top hmap_le'
  have hR_aemeas_U : AEMeasurable R (μ.restrict U) :=
    hR_meas.aemeasurable
  simpa [U, R, μ, Function.comp_def] using
    hw_map.comp_of_map hR_aemeas_U

private theorem annulus_l1_lintegral_indicator_lt_top_of_memLp_for_taper
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {g : H → ℝ}
    (_hg : MemLp g 2
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H))) :
    ∫⁻ x,
      (euclideanSobolevUnitBallReflectionAnnulus H).indicator
        (fun y : H ↦ ENNReal.ofReal ‖g y‖) x
      ∂MeasureTheory.volume < ⊤ := by
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let A : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  have hA_meas : MeasurableSet A := by
    dsimp [A, euclideanSobolevUnitBallReflectionAnnulus]
    measurability
  have hA_subset : A ⊆ Metric.closedBall (0 : H) (3 / 2 : ℝ) := by
    intro x hx
    simp [A, euclideanSobolevUnitBallReflectionAnnulus,
      Metric.mem_closedBall, dist_eq_norm] at hx ⊢
    exact hx.2.le
  have hclosed_ne_top :
      (MeasureTheory.volume : Measure H)
        (Metric.closedBall (0 : H) (3 / 2 : ℝ)) ≠ ⊤ :=
    (isCompact_closedBall (0 : H) (3 / 2 : ℝ)).measure_ne_top
  have hA_ne_top : (MeasureTheory.volume : Measure H) A ≠ ⊤ :=
    ne_top_of_le_ne_top hclosed_ne_top (measure_mono hA_subset)
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict A) :=
    isFiniteMeasure_restrict.2 hA_ne_top
  have hg_int : Integrable g (MeasureTheory.volume.restrict A) := by
    simpa [A] using _hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hnorm_lt :
      (∫⁻ x, ENNReal.ofReal ‖g x‖
          ∂MeasureTheory.volume.restrict A) < ⊤ :=
    hg_int.norm.lintegral_lt_top
  simpa [A] using
    (by
      rw [lintegral_indicator hA_meas]
      exact hnorm_lt)

private theorem unit_outer_collar_measure_tendsto_zero_for_taper
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    Filter.Tendsto
      (fun ε : ℝ ↦
        (MeasureTheory.volume : Measure H)
          {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε})
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let R : ℝ := 1
  let S : ℝ → Set H := fun ε : ℝ ↦
    {x : H | R < ‖x‖ ∧ ‖x‖ < R + ε}
  have hmeas : ∀ ε > (0 : ℝ),
      NullMeasurableSet (S ε) (MeasureTheory.volume : Measure H) := by
    intro ε _hε
    dsimp [S]
    exact (by measurability : MeasurableSet
      {x : H | R < ‖x‖ ∧ ‖x‖ < R + ε}).nullMeasurableSet
  have hmono : ∀ i j : ℝ, (0 : ℝ) < i → i ≤ j → S i ⊆ S j := by
    intro i j _hi hij x hx
    dsimp [S] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2, hij]⟩
  have hfinite : ∃ ε > (0 : ℝ),
      (MeasureTheory.volume : Measure H) (S ε) ≠ ⊤ := by
    refine ⟨1, by norm_num, ?_⟩
    have hS_subset : S 1 ⊆ Metric.closedBall (0 : H) (R + 1) := by
      intro x hx
      dsimp [S] at hx
      simp [Metric.mem_closedBall, dist_eq_norm]
      exact hx.2.le
    have hclosed_ne_top :
        (MeasureTheory.volume : Measure H)
          (Metric.closedBall (0 : H) (R + 1)) ≠ ⊤ :=
      (isCompact_closedBall (0 : H) (R + 1)).measure_ne_top
    exact ne_top_of_le_ne_top hclosed_ne_top (measure_mono hS_subset)
  have hS_empty : (⋂ ε > (0 : ℝ), S ε) = (∅ : Set H) := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    have hx_all : ∀ ε : ℝ, 0 < ε → x ∈ S ε := by
      intro ε hε
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hx ε) hε
    have hx_lower : R < ‖x‖ := (hx_all 1 (by norm_num)).1
    let δ : ℝ := (‖x‖ - R) / 2
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      exact half_pos (sub_pos.mpr hx_lower)
    have hx_upper : ‖x‖ < R + δ := (hx_all δ hδ_pos).2
    dsimp [δ] at hx_upper
    have hnorm_lt_R : ‖x‖ < R := by
      have htwice :
          2 * ‖x‖ < 2 * (R + (‖x‖ - R) / 2) := by
        exact mul_lt_mul_of_pos_left hx_upper (by norm_num : (0 : ℝ) < 2)
      ring_nf at htwice
      linarith [htwice]
    exact (not_lt_of_ge hx_lower.le) hnorm_lt_R
  have htendsto :=
    tendsto_measure_biInter_gt
      (μ := (MeasureTheory.volume : Measure H))
      (s := S) (a := (0 : ℝ)) hmeas hmono hfinite
  have htarget :
      Filter.Tendsto ((MeasureTheory.volume : Measure H) ∘ S)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [hS_empty] using htendsto
  simpa [Function.comp_def, S, R] using htarget

private theorem annulus_l1_outer_unit_collar_mass_tendsto_zero_for_taper
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {g : H → ℝ}
    (_hg : MemLp g 2
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H))) :
    Filter.Tendsto
      (fun ε : ℝ ↦
        ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
          ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  let A : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let F : H → ℝ≥0∞ :=
    fun x : H ↦ A.indicator (fun y : H ↦ ENNReal.ofReal ‖g y‖) x
  have hF_finite : ∫⁻ x, F x ∂MeasureTheory.volume ≠ ⊤ := by
    exact ne_of_lt
      (by
        simpa [F, A] using
          annulus_l1_lintegral_indicator_lt_top_of_memLp_for_taper _hg)
  have hmeasure :
      Filter.Tendsto
        ((MeasureTheory.volume : Measure H) ∘
          (fun ε : ℝ ↦ {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε}))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [Function.comp_def] using
      unit_outer_collar_measure_tendsto_zero_for_taper (H := H)
  have hF_tendsto :
      Filter.Tendsto
        (fun ε : ℝ ↦
          ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
            F x ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) :=
    tendsto_setLIntegral_zero hF_finite hmeasure
  have heq_eventually :
      (fun ε : ℝ ↦
        ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
          F x ∂MeasureTheory.volume)
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε : ℝ ↦
        ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
          ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume) := by
    have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < (1 / 2 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hsmall] with ε hε_lt
    refine (setLIntegral_congr_fun ?_ ?_).symm
    · measurability
    intro x hx
    have hxA : x ∈ A := by
      dsimp [A, euclideanSobolevUnitBallReflectionAnnulus]
      constructor
      · exact hx.1
      · nlinarith [hx.2, hε_lt]
    simp [F, hxA]
  exact hF_tendsto.congr' heq_eventually

/--
%%handwave
name:
  Unit taper error has vanishing exterior trace mass
statement:
  If \(w\) is square-integrable in the unit ball, then the normalized
  \(L^1\)-mass of the exterior collar error
  \((3-2\|x\|-1)w(Rx)\) tends to zero as the collar shrinks to the unit
  sphere.
proof:
  On \(1<\|x\|<1+\varepsilon\), the factor
  \(|3-2\|x\|-1|\) is bounded by \(2\varepsilon\).  After dividing by
  \(\varepsilon\), the error is controlled by the reflected \(L^1\)-mass in
  the collar.  Square-integrability of \(w\) and the bounded distortion of
  the radial reflection give a uniform \(L^1\)-bound for these collar masses.
-/
theorem unit_radial_reflection_taper_error_tendsto_zero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ}
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    Filter.Tendsto
      (fun ε : ℝ ↦
        ENNReal.ofReal (1 / ε) *
          ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
            ENNReal.ofReal
              ‖((3 - 2 * ‖x‖) - 1) *
                  w (euclideanSobolevUnitBallRadialReflection x)‖
              ∂MeasureTheory.volume)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  let g : H → ℝ :=
    fun x : H ↦ w (euclideanSobolevUnitBallRadialReflection x)
  have hg :
      MemLp g 2
        (MeasureTheory.volume.restrict
          (euclideanSobolevUnitBallReflectionAnnulus H)) := by
    simpa [g] using
      unit_radial_reflection_taper_error_pullback_memLp
        _hw
  have hmass :
      Filter.Tendsto
        (fun ε : ℝ ↦
          ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
            ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) :=
    annulus_l1_outer_unit_collar_mass_tendsto_zero_for_taper hg
  have hscaled :
      Filter.Tendsto
        (fun ε : ℝ ↦
          (2 : ℝ≥0∞) *
            ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
              ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    have htwo_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have hmul := ENNReal.Tendsto.const_mul hmass (Or.inr htwo_ne_top)
    simpa [mul_assoc] using hmul
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hscaled
      (Filter.Eventually.of_forall fun _ε ↦ zero_le)
      (unit_outer_taper_error_trace_integral_le_two_collar_mass
        (H := H) (g := g))

/--
%%handwave
name:
  Measurability of the raw reflected trace integrand
statement:
  If \(w\) is square-integrable on the unit ball and the boundary trace
  representative is measurable, then the raw reflected exterior trace
  integrand is a.e. measurable on all sufficiently thin exterior collars.
proof:
  The reflected pullback of \(w\) is square-integrable on the annulus, hence
  a.e. measurable on each small collar.  The radial projection is measurable,
  so composing it with a measurable trace representative is measurable on the
  collar.  The conclusion follows by closure of a.e. measurable functions
  under subtraction, norm, and the map \(t\mapsto \max(t,0)\).
-/
private theorem unit_radial_reflection_raw_trace_integrand_aemeasurable
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w τ : H → ℝ}
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hτ_meas : Measurable τ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      AEMeasurable
        (fun x : H ↦
          ENNReal.ofReal
            ‖w (euclideanSobolevUnitBallRadialReflection x) -
              τ (((1 / ‖x‖) : ℝ) • x)‖)
        (MeasureTheory.volume.restrict
          {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε}) := by
  let A : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let g : H → ℝ :=
    fun x : H ↦ w (euclideanSobolevUnitBallRadialReflection x)
  have hgA :
      MemLp g 2 (MeasureTheory.volume.restrict A) := by
    simpa [g, A] using
      unit_radial_reflection_taper_error_pullback_memLp
        _hw
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < (1 / 2 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall] with ε hε_lt
  let S : Set H := {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε}
  have hSA : S ⊆ A := by
    intro x hx
    dsimp [S, A, euclideanSobolevUnitBallReflectionAnnulus] at hx ⊢
    exact ⟨hx.1, by nlinarith [hx.2, hε_lt]⟩
  have hmeasure_le :
      MeasureTheory.volume.restrict S ≤
        MeasureTheory.volume.restrict A :=
    Measure.restrict_mono_set (MeasureTheory.volume : Measure H) hSA
  have hgS : AEMeasurable g (MeasureTheory.volume.restrict S) :=
    (hgA.mono_measure hmeasure_le).aestronglyMeasurable.aemeasurable
  have hπ_meas :
      Measurable (fun x : H ↦ ((1 / ‖x‖) : ℝ) • x) := by
    measurability
  have hτπ :
      AEMeasurable
        (fun x : H ↦ τ (((1 / ‖x‖) : ℝ) • x))
        (MeasureTheory.volume.restrict S) :=
    hτ_meas.comp_aemeasurable hπ_meas.aemeasurable
  have hdiff :
      AEMeasurable
        (fun x : H ↦ g x - τ (((1 / ‖x‖) : ℝ) • x))
        (MeasureTheory.volume.restrict S) :=
    hgS.sub hτπ
  exact ENNReal.measurable_ofReal.comp_aemeasurable hdiff.norm

/--
%%handwave
name:
  Unit trace is unchanged by the reflection taper
statement:
  If the radial reflected copy of a square-integrable function has exterior
  \(L^1\) trace \(\tau\) on the unit sphere, then multiplying that reflected
  copy by the taper \(3-2\|x\|\) leaves the exterior unit trace equal to
  \(\tau\).
proof:
  In the exterior collar \(1<\|x\|<1+\varepsilon\), the taper differs from
  \(1\) by at most \(2\varepsilon\).  The normalized \(L^1\)-error is therefore
  controlled by the ordinary \(L^1\)-mass of the reflected pullback in the
  collar.  This mass is uniformly bounded for small collars by the
  square-integrability of \(w\) in the unit ball and the bounded distortion of
  radial reflection.
-/
theorem hasL1TraceFromOutsideSphere_unit_radial_reflection_taper_of_untapered
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w τ : H → ℝ}
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hτ_meas : Measurable τ)
    (_htrace : HasL1TraceFromOutsideSphere (H := H) 1
      (fun x : H ↦ w (euclideanSobolevUnitBallRadialReflection x))
      τ) :
    HasL1TraceFromOutsideSphere (H := H) 1
      (fun x : H ↦
        (3 - 2 * ‖x‖) *
          w (euclideanSobolevUnitBallRadialReflection x))
      τ := by
  have herror :
      Filter.Tendsto
        (fun ε : ℝ ↦
          ENNReal.ofReal (1 / ε) *
            ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
              ENNReal.ofReal
                ‖((3 - 2 * ‖x‖) - 1) *
                    w (euclideanSobolevUnitBallRadialReflection x)‖
                ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) :=
    unit_radial_reflection_taper_error_tendsto_zero _hw
  have hsum :
      Filter.Tendsto
        (fun ε : ℝ ↦
          (ENNReal.ofReal (1 / ε) *
            ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
              ENNReal.ofReal
                ‖w (euclideanSobolevUnitBallRadialReflection x) -
                  τ (((1 / ‖x‖) : ℝ) • x)‖
                ∂MeasureTheory.volume) +
            (ENNReal.ofReal (1 / ε) *
              ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
                ENNReal.ofReal
                  ‖((3 - 2 * ‖x‖) - 1) *
                      w (euclideanSobolevUnitBallRadialReflection x)‖
                  ∂MeasureTheory.volume))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    have h := _htrace.add herror
    simpa [HasL1TraceFromOutsideSphere] using h
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hsum
      (Filter.Eventually.of_forall fun _ε ↦ zero_le)
      (unit_radial_reflection_taper_trace_integral_le_raw_add_error
        (H := H) (w := w) (τ := τ)
        (unit_radial_reflection_raw_trace_integrand_aemeasurable
          _hw hτ_meas))

/--
%%handwave
name:
  Reflected tapered copy has the exterior unit trace
statement:
  If \(w\) has an \(L^1\) trace \(\tau\) on the unit sphere from inside the
  unit ball, and \(w\) is square-integrable on the unit ball, then the
  tapered radial reflection
  \(x\mapsto (3-2\|x\|)w(((2-\|x\|)/\|x\|)x)\) has the same \(L^1\) trace
  on the unit sphere from the outside.
proof:
  First use
  [the radial reflected copy has the same exterior trace as the original
  interior trace](lean:JJMath.Uniformization.hasL1TraceFromOutsideSphere_unit_radial_reflection_of_inside).
  Then apply
  [multiplication by the taper does not change the exterior unit
  trace](lean:JJMath.Uniformization.hasL1TraceFromOutsideSphere_unit_radial_reflection_taper_of_untapered).
-/
theorem hasL1TraceFromOutsideSphere_unit_radial_reflection_taper_of_inside
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w τ : H → ℝ}
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hτ_meas : Measurable τ)
    (_htrace : HasL1TraceFromInsideSphere (H := H) 1 w τ) :
    HasL1TraceFromOutsideSphere (H := H) 1
      (fun x : H ↦
        (3 - 2 * ‖x‖) *
          w (euclideanSobolevUnitBallRadialReflection x))
      τ := by
  have hraw :
    HasL1TraceFromOutsideSphere (H := H) 1
        (fun x : H ↦ w (euclideanSobolevUnitBallRadialReflection x))
        τ :=
    hasL1TraceFromOutsideSphere_unit_radial_reflection_of_inside
      _hw hτ_meas _htrace
  exact
    hasL1TraceFromOutsideSphere_unit_radial_reflection_taper_of_untapered
      _hw hτ_meas hraw

/--
%%handwave
name:
  Matching trace for the reflected copy at the unit sphere
statement:
  If \(w\) is a \(W^{1,2}\) function on the unit ball, then \(w\) and its
  tapered radial reflected copy have a common \(L^1\) trace on the unit
  sphere.
proof:
  First apply
  [a scalar \(W^{1,2}\) function on the unit ball has an \(L^1\) trace on the
  unit sphere from the inside](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_has_l1_trace_from_inside).
  Then apply
  [the tapered radial reflection has the same \(L^1\) trace on the unit
  sphere from the outside](lean:JJMath.Uniformization.hasL1TraceFromOutsideSphere_unit_radial_reflection_taper_of_inside).
-/
theorem euclideanSobolev_unit_ball_radial_reflection_inner_trace
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      HasL1TraceFromInsideSphere (H := H) 1 w τ ∧
        HasL1TraceFromOutsideSphere (H := H) 1
          (fun x : H ↦
            (3 - 2 * ‖x‖) *
              w (euclideanSobolevUnitBallRadialReflection x))
          τ := by
  rcases
    euclideanSobolev_unit_ball_has_l1_trace_from_inside
      _hweak _hw _hdw with
    ⟨τ, hτ_meas, hτ⟩
  exact
    ⟨τ, hτ,
      hasL1TraceFromOutsideSphere_unit_radial_reflection_taper_of_inside
        _hw hτ_meas hτ⟩

/--
%%handwave
name:
  Reflected pullbacks are square-integrable on the annulus
statement:
  If \(w\) is square-integrable on the unit ball, then the radial reflected
  pullback \(x\mapsto w(((2-\|x\|)/\|x\|)x)\) is square-integrable on the
  annulus \(1<\|x\|<3/2\).
proof:
  Radial reflection maps the annulus into the inner shell
  \(1/2<\|x\|<1\).  The inverse map on this shell is Lipschitz, so the image
  measure of annular sets is controlled by Haar measure on the shell.  Pull
  the \(L^2\)-bound for \(w\) back through this quasi-measure-preserving map.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_annulus_pullback_memLp
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ}
    (hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    MemLp (fun x : H ↦ w (euclideanSobolevUnitBallRadialReflection x))
      2
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)) := by
  let U : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let Ω₀ : Set H := euclideanSobolevUnitBallPunctured H
  let B : Set H := Metric.ball (0 : H) 1
  let R : H → H := euclideanSobolevUnitBallRadialReflection
  let μ : Measure H := MeasureTheory.volume
  have hR_meas : Measurable R := by
    simpa [R] using euclideanSobolevUnitBallRadialReflection_measurable
      (H := H)
  rcases
    map_restrict_le_smul_of_inverse_lipschitzOnWith
      (U := U) (Ω := Ω₀) (T := R) (S := R)
      (L := (12 : ℝ≥0))
      hR_meas
      (by
        simpa [U, Ω₀, R] using
          euclideanSobolevUnitBallRadialReflection_mapsTo_annulus_punctured
            (H := H))
      (by
        intro x hx
        simpa [U, R] using
          euclideanSobolevUnitBallRadialReflection_involutive_on_annulus
            (H := H) (x := x) hx)
      (by
        simpa [Ω₀, R] using
          euclideanSobolevUnitBallRadialReflection_lipschitzOnWith_punctured
            (H := H)) with
    ⟨D, hD_ne_top, hmap_le⟩
  have hΩ₀_subset : Ω₀ ⊆ B := by
    simpa [Ω₀, B] using
      euclideanSobolevUnitBallPunctured_subset_unit_ball (H := H)
  have hmeasure_le : μ.restrict Ω₀ ≤ μ.restrict B :=
    Measure.restrict_mono_set μ hΩ₀_subset
  have hwΩ₀ : MemLp w 2 (μ.restrict Ω₀) :=
    hw.mono_measure (by simpa [μ, B] using hmeasure_le)
  have hmap_le' :
      Measure.map R (μ.restrict U) ≤ D • μ.restrict Ω₀ := by
    simpa [μ] using hmap_le
  have hw_map : MemLp w 2 (Measure.map R (μ.restrict U)) :=
    hwΩ₀.of_measure_le_smul hD_ne_top hmap_le'
  have hR_aemeas_U : AEMeasurable R (μ.restrict U) :=
    hR_meas.aemeasurable
  simpa [U, R, μ, Function.comp_def] using
    hw_map.comp_of_map hR_aemeas_U

/--
%%handwave
name:
  Outer taper trace integral is controlled by annular collar mass
statement:
  In the collar \(3/2-\varepsilon<\|x\|<3/2\), the normalized \(L^1\) trace
  expression for \((3-2\|x\|)g(x)\) is bounded, for sufficiently small
  \(\varepsilon>0\), by twice the \(L^1\)-mass of \(g\) on the same collar.
proof:
  The inequality \(|3-2\|x\||\le 2\varepsilon\) holds throughout the collar.
  Multiplying by \(1/\varepsilon\) leaves the factor \(2\), and monotonicity
  of the nonnegative integral gives the result.
-/
theorem three_halves_taper_trace_integral_le_two_collar_mass
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    {g : H → ℝ} :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (1 / ε) *
        ∫⁻ x in {x : H | (3 / 2 : ℝ) - ε < ‖x‖ ∧
            ‖x‖ < (3 / 2 : ℝ)},
          ENNReal.ofReal ‖(3 - 2 * ‖x‖) * g x - 0‖
            ∂MeasureTheory.volume ≤
        (2 : ℝ≥0∞) *
          ∫⁻ x in {x : H | (3 / 2 : ℝ) - ε < ‖x‖ ∧
              ‖x‖ < (3 / 2 : ℝ)},
            ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε_pos : 0 < ε := hε
  let S : Set H := {x : H | (3 / 2 : ℝ) - ε < ‖x‖ ∧
    ‖x‖ < (3 / 2 : ℝ)}
  have hS_meas : MeasurableSet S := by
    dsimp [S]
    measurability
  have hpoint : ∀ x ∈ S,
      ENNReal.ofReal ‖(3 - 2 * ‖x‖) * g x - 0‖ ≤
        ENNReal.ofReal (2 * ε) * ENNReal.ofReal ‖g x‖ := by
    intro x hx
    have htaper_nonneg : 0 ≤ (3 : ℝ) - 2 * ‖x‖ := by
      nlinarith [hx.2]
    have htaper_le : |(3 : ℝ) - 2 * ‖x‖| ≤ 2 * ε := by
      rw [abs_of_nonneg htaper_nonneg]
      nlinarith [hx.1]
    calc
      ENNReal.ofReal ‖(3 - 2 * ‖x‖) * g x - 0‖
          = ENNReal.ofReal (|(3 : ℝ) - 2 * ‖x‖| * ‖g x‖) := by
              simp [norm_mul, Real.norm_eq_abs]
      _ ≤ ENNReal.ofReal ((2 * ε) * ‖g x‖) := by
              exact ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right htaper_le (norm_nonneg _))
      _ = ENNReal.ofReal (2 * ε) * ENNReal.ofReal ‖g x‖ := by
              rw [ENNReal.ofReal_mul]
              nlinarith [hε_pos]
  have hlin :
      ∫⁻ x in S, ENNReal.ofReal ‖(3 - 2 * ‖x‖) * g x - 0‖
          ∂MeasureTheory.volume ≤
        ∫⁻ x in S,
          ENNReal.ofReal (2 * ε) * ENNReal.ofReal ‖g x‖
          ∂MeasureTheory.volume :=
    setLIntegral_mono' hS_meas hpoint
  have hconst_ne_top : ENNReal.ofReal (2 * ε) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hprod :
      ENNReal.ofReal (1 / ε) * ENNReal.ofReal (2 * ε) =
        (2 : ℝ≥0∞) := by
    have hinv_nonneg : 0 ≤ (1 / ε : ℝ) :=
      div_nonneg zero_le_one hε_pos.le
    rw [← ENNReal.ofReal_mul hinv_nonneg]
    have hmul : (1 / ε) * (2 * ε) = (2 : ℝ) := by
      field_simp [ne_of_gt hε_pos]
    rw [hmul]
    norm_num
  calc
    ENNReal.ofReal (1 / ε) *
        ∫⁻ x in {x : H | (3 / 2 : ℝ) - ε < ‖x‖ ∧
            ‖x‖ < (3 / 2 : ℝ)},
          ENNReal.ofReal ‖(3 - 2 * ‖x‖) * g x - 0‖
            ∂MeasureTheory.volume
        = ENNReal.ofReal (1 / ε) *
          ∫⁻ x in S,
            ENNReal.ofReal ‖(3 - 2 * ‖x‖) * g x - 0‖
              ∂MeasureTheory.volume := rfl
    _ ≤ ENNReal.ofReal (1 / ε) *
          ∫⁻ x in S,
            ENNReal.ofReal (2 * ε) * ENNReal.ofReal ‖g x‖
              ∂MeasureTheory.volume := by
            exact mul_le_mul_right hlin _
    _ = ENNReal.ofReal (1 / ε) *
          (ENNReal.ofReal (2 * ε) *
            ∫⁻ x in S, ENNReal.ofReal ‖g x‖
              ∂MeasureTheory.volume) := by
            rw [lintegral_const_mul' (μ := MeasureTheory.volume.restrict S)
              (r := ENNReal.ofReal (2 * ε))
              (f := fun x : H ↦ ENNReal.ofReal ‖g x‖) hconst_ne_top]
    _ = (2 : ℝ≥0∞) *
          ∫⁻ x in S, ENNReal.ofReal ‖g x‖
            ∂MeasureTheory.volume := by
            rw [← mul_assoc, hprod]
    _ = (2 : ℝ≥0∞) *
          ∫⁻ x in {x : H | (3 / 2 : ℝ) - ε < ‖x‖ ∧
              ‖x‖ < (3 / 2 : ℝ)},
            ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume := rfl

/--
%%handwave
name:
  Annular \(L^1\)-mass is finite for square-integrable functions
statement:
  If \(g\) is square-integrable on the annulus \(1<\|x\|<3/2\), then the
  nonnegative function \(|g|\), extended by zero outside the annulus, has
  finite integral.
proof:
  The annulus has finite Haar measure in a finite-dimensional normed vector
  space because it is contained in a compact ball.  On a finite-measure set,
  \(L^2\)-integrability implies \(L^1\)-integrability.
-/
theorem annulus_l1_lintegral_indicator_lt_top_of_memLp
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {g : H → ℝ}
    (_hg : MemLp g 2
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H))) :
    ∫⁻ x,
      (euclideanSobolevUnitBallReflectionAnnulus H).indicator
        (fun y : H ↦ ENNReal.ofReal ‖g y‖) x
      ∂MeasureTheory.volume < ⊤ := by
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let A : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  have hA_meas : MeasurableSet A := by
    dsimp [A, euclideanSobolevUnitBallReflectionAnnulus]
    measurability
  have hA_subset : A ⊆ Metric.closedBall (0 : H) (3 / 2 : ℝ) := by
    intro x hx
    simp [A, euclideanSobolevUnitBallReflectionAnnulus,
      Metric.mem_closedBall, dist_eq_norm] at hx ⊢
    exact hx.2.le
  have hclosed_ne_top :
      (MeasureTheory.volume : Measure H)
        (Metric.closedBall (0 : H) (3 / 2 : ℝ)) ≠ ⊤ :=
    (isCompact_closedBall (0 : H) (3 / 2 : ℝ)).measure_ne_top
  have hA_ne_top : (MeasureTheory.volume : Measure H) A ≠ ⊤ :=
    ne_top_of_le_ne_top hclosed_ne_top (measure_mono hA_subset)
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict A) :=
    isFiniteMeasure_restrict.2 hA_ne_top
  have hg_int : Integrable g (MeasureTheory.volume.restrict A) := by
    simpa [A] using _hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hnorm_lt :
      (∫⁻ x, ENNReal.ofReal ‖g x‖
          ∂MeasureTheory.volume.restrict A) < ⊤ :=
    hg_int.norm.lintegral_lt_top
  simpa [A] using
    (by
      rw [lintegral_indicator hA_meas]
      exact hnorm_lt)

/--
%%handwave
name:
  Unit exterior annular collars shrink to measure zero
statement:
  The Haar measure of the collars
  \(1<\|x\|<1+\varepsilon\) tends to zero as
  \(\varepsilon\downarrow0\).
proof:
  The collars are increasing with respect to the width \(\varepsilon\), have
  finite measure for one positive width, and their intersection over all
  positive widths is empty.  Continuity of measure from above gives the
  claimed convergence.
-/
theorem unit_outer_collar_measure_tendsto_zero
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    Filter.Tendsto
      (fun ε : ℝ ↦
        (MeasureTheory.volume : Measure H)
          {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε})
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let R : ℝ := 1
  let S : ℝ → Set H := fun ε : ℝ ↦
    {x : H | R < ‖x‖ ∧ ‖x‖ < R + ε}
  have hmeas : ∀ ε > (0 : ℝ),
      NullMeasurableSet (S ε) (MeasureTheory.volume : Measure H) := by
    intro ε _hε
    dsimp [S]
    exact (by measurability : MeasurableSet
      {x : H | R < ‖x‖ ∧ ‖x‖ < R + ε}).nullMeasurableSet
  have hmono : ∀ i j : ℝ, (0 : ℝ) < i → i ≤ j → S i ⊆ S j := by
    intro i j _hi hij x hx
    dsimp [S] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2, hij]⟩
  have hfinite : ∃ ε > (0 : ℝ),
      (MeasureTheory.volume : Measure H) (S ε) ≠ ⊤ := by
    refine ⟨1, by norm_num, ?_⟩
    have hS_subset : S 1 ⊆ Metric.closedBall (0 : H) (R + 1) := by
      intro x hx
      dsimp [S] at hx
      simp [Metric.mem_closedBall, dist_eq_norm]
      exact hx.2.le
    have hclosed_ne_top :
        (MeasureTheory.volume : Measure H)
          (Metric.closedBall (0 : H) (R + 1)) ≠ ⊤ :=
      (isCompact_closedBall (0 : H) (R + 1)).measure_ne_top
    exact ne_top_of_le_ne_top hclosed_ne_top (measure_mono hS_subset)
  have hS_empty : (⋂ ε > (0 : ℝ), S ε) = (∅ : Set H) := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    have hx_all : ∀ ε : ℝ, 0 < ε → x ∈ S ε := by
      intro ε hε
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hx ε) hε
    have hx_lower : R < ‖x‖ := (hx_all 1 (by norm_num)).1
    let δ : ℝ := (‖x‖ - R) / 2
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      exact half_pos (sub_pos.mpr hx_lower)
    have hx_upper : ‖x‖ < R + δ := (hx_all δ hδ_pos).2
    dsimp [δ] at hx_upper
    have hnorm_lt_R : ‖x‖ < R := by
      have htwice :
          2 * ‖x‖ < 2 * (R + (‖x‖ - R) / 2) := by
        exact mul_lt_mul_of_pos_left hx_upper (by norm_num : (0 : ℝ) < 2)
      ring_nf at htwice
      linarith [htwice]
    exact (not_lt_of_ge hx_lower.le) hnorm_lt_R
  have htendsto :=
    tendsto_measure_biInter_gt
      (μ := (MeasureTheory.volume : Measure H))
      (s := S) (a := (0 : ℝ)) hmeas hmono hfinite
  have htarget :
      Filter.Tendsto ((MeasureTheory.volume : Measure H) ∘ S)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [hS_empty] using htendsto
  simpa [Function.comp_def, S, R] using htarget

/--
%%handwave
name:
  Annular \(L^1\)-mass vanishes in shrinking unit exterior collars
statement:
  If \(g\) is square-integrable on the annulus \(1<\|x\|<3/2\), then its
  \(L^1\)-mass on the shrinking collars \(1<\|x\|<1+\varepsilon\)
  tends to zero.
proof:
  Extend \(|g|\) by zero outside the annulus.  This extended nonnegative
  function has finite integral.  Since the unit exterior collars shrink to a
  set of Haar measure zero, absolute continuity of the integral gives the
  result; for all sufficiently small widths the collars lie inside the
  annulus.
-/
theorem annulus_l1_outer_unit_collar_mass_tendsto_zero
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {g : H → ℝ}
    (_hg : MemLp g 2
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H))) :
    Filter.Tendsto
      (fun ε : ℝ ↦
        ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
          ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  let A : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let F : H → ℝ≥0∞ :=
    fun x : H ↦ A.indicator (fun y : H ↦ ENNReal.ofReal ‖g y‖) x
  have hF_finite : ∫⁻ x, F x ∂MeasureTheory.volume ≠ ⊤ := by
    exact ne_of_lt
      (by
        simpa [F, A] using
          annulus_l1_lintegral_indicator_lt_top_of_memLp _hg)
  have hmeasure :
      Filter.Tendsto
        ((MeasureTheory.volume : Measure H) ∘
          (fun ε : ℝ ↦ {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε}))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [Function.comp_def] using
      unit_outer_collar_measure_tendsto_zero (H := H)
  have hF_tendsto :
      Filter.Tendsto
        (fun ε : ℝ ↦
          ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
            F x ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) :=
    tendsto_setLIntegral_zero hF_finite hmeasure
  have heq_eventually :
      (fun ε : ℝ ↦
        ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
          F x ∂MeasureTheory.volume)
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε : ℝ ↦
        ∫⁻ x in {x : H | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 + ε},
          ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume) := by
    have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < (1 / 2 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hsmall] with ε hε_lt
    refine (setLIntegral_congr_fun ?_ ?_).symm
    · measurability
    intro x hx
    have hxA : x ∈ A := by
      dsimp [A, euclideanSobolevUnitBallReflectionAnnulus]
      constructor
      · exact hx.1
      · nlinarith [hx.2, hε_lt]
    simp [F, hxA]
  exact hF_tendsto.congr' heq_eventually

/--
%%handwave
name:
  Outer annular collars shrink to measure zero
statement:
  The Haar measure of the collars
  \(3/2-\varepsilon<\|x\|<3/2\) tends to zero as
  \(\varepsilon\downarrow0\).
proof:
  These collars increase with \(\varepsilon\), and their intersection over all
  positive \(\varepsilon\) is contained in the sphere \(\|x\|=3/2\), which has
  Haar measure zero.  Continuity of measure from above at finite measure sets
  gives the limit.
-/
theorem three_halves_outer_collar_measure_tendsto_zero
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    Filter.Tendsto
      (fun ε : ℝ ↦
        (MeasureTheory.volume : Measure H)
          {x : H | (3 / 2 : ℝ) - ε < ‖x‖ ∧
            ‖x‖ < (3 / 2 : ℝ)})
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let R : ℝ := 3 / 2
  let S : ℝ → Set H := fun ε : ℝ ↦
    {x : H | R - ε < ‖x‖ ∧ ‖x‖ < R}
  have hmeas : ∀ ε > (0 : ℝ),
      NullMeasurableSet (S ε) (MeasureTheory.volume : Measure H) := by
    intro ε _hε
    dsimp [S]
    exact (by measurability : MeasurableSet
      {x : H | R - ε < ‖x‖ ∧ ‖x‖ < R}).nullMeasurableSet
  have hmono : ∀ i j : ℝ, (0 : ℝ) < i → i ≤ j → S i ⊆ S j := by
    intro i j _hi hij x hx
    dsimp [S] at hx ⊢
    exact ⟨by linarith [hx.1, hij], hx.2⟩
  have hfinite : ∃ ε > (0 : ℝ),
      (MeasureTheory.volume : Measure H) (S ε) ≠ ⊤ := by
    refine ⟨1, by norm_num, ?_⟩
    have hS_subset : S 1 ⊆ Metric.closedBall (0 : H) R := by
      intro x hx
      dsimp [S] at hx
      simp [Metric.mem_closedBall, dist_eq_norm]
      exact hx.2.le
    have hclosed_ne_top :
        (MeasureTheory.volume : Measure H)
          (Metric.closedBall (0 : H) R) ≠ ⊤ :=
      (isCompact_closedBall (0 : H) R).measure_ne_top
    exact ne_top_of_le_ne_top hclosed_ne_top (measure_mono hS_subset)
  have hS_empty : (⋂ ε > (0 : ℝ), S ε) = (∅ : Set H) := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    have hx_all : ∀ ε : ℝ, 0 < ε → x ∈ S ε := by
      intro ε hε
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hx ε) hε
    have hx_upper : ‖x‖ < R := (hx_all 1 (by norm_num)).2
    let δ : ℝ := (R - ‖x‖) / 2
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      exact half_pos (sub_pos.mpr hx_upper)
    have hx_lower : R - δ < ‖x‖ := (hx_all δ hδ_pos).1
    dsimp [δ] at hx_lower
    have hR_lt_norm : R < ‖x‖ := by
      have htwice :
          2 * (R - (R - ‖x‖) / 2) < 2 * ‖x‖ := by
        exact mul_lt_mul_of_pos_left hx_lower (by norm_num : (0 : ℝ) < 2)
      ring_nf at htwice
      linarith [htwice]
    exact (not_lt_of_ge hx_upper.le) hR_lt_norm
  have htendsto :=
    tendsto_measure_biInter_gt
      (μ := (MeasureTheory.volume : Measure H))
      (s := S) (a := (0 : ℝ)) hmeas hmono hfinite
  have htarget :
      Filter.Tendsto ((MeasureTheory.volume : Measure H) ∘ S)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [hS_empty] using htendsto
  simpa [Function.comp_def, S, R] using htarget

/--
%%handwave
name:
  Annular \(L^1\)-mass vanishes in shrinking outer collars
statement:
  If \(g\) is square-integrable on the annulus \(1<\|x\|<3/2\), then its
  \(L^1\)-mass on the shrinking collars
  \(3/2-\varepsilon<\|x\|<3/2\) tends to zero.
proof:
  Square-integrability on the finite-measure annulus implies \(L^1\)
  integrability there.  The collars decrease to the empty set, up to the
  boundary sphere, and the boundary sphere has Haar measure zero.  Absolute
  continuity of the integral gives convergence of the collar masses to zero.
-/
theorem annulus_l1_collar_mass_tendsto_zero_at_three_halves
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {g : H → ℝ}
    (_hg : MemLp g 2
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H))) :
    Filter.Tendsto
      (fun ε : ℝ ↦
        ∫⁻ x in {x : H | (3 / 2 : ℝ) - ε < ‖x‖ ∧
            ‖x‖ < (3 / 2 : ℝ)},
          ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  let A : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let F : H → ℝ≥0∞ :=
    fun x : H ↦ A.indicator (fun y : H ↦ ENNReal.ofReal ‖g y‖) x
  have hF_finite : ∫⁻ x, F x ∂MeasureTheory.volume ≠ ⊤ := by
    exact ne_of_lt
      (by
        simpa [F, A] using
          annulus_l1_lintegral_indicator_lt_top_of_memLp _hg)
  have hmeasure :
      Filter.Tendsto
        ((MeasureTheory.volume : Measure H) ∘
          (fun ε : ℝ ↦ {x : H | (3 / 2 : ℝ) - ε < ‖x‖ ∧
            ‖x‖ < (3 / 2 : ℝ)}))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [Function.comp_def] using
      three_halves_outer_collar_measure_tendsto_zero (H := H)
  have hF_tendsto :
      Filter.Tendsto
        (fun ε : ℝ ↦
          ∫⁻ x in {x : H | (3 / 2 : ℝ) - ε < ‖x‖ ∧
              ‖x‖ < (3 / 2 : ℝ)}, F x ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) :=
    tendsto_setLIntegral_zero hF_finite hmeasure
  have heq_eventually :
      (fun ε : ℝ ↦
        ∫⁻ x in {x : H | (3 / 2 : ℝ) - ε < ‖x‖ ∧
            ‖x‖ < (3 / 2 : ℝ)}, F x ∂MeasureTheory.volume)
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε : ℝ ↦
        ∫⁻ x in {x : H | (3 / 2 : ℝ) - ε < ‖x‖ ∧
            ‖x‖ < (3 / 2 : ℝ)},
          ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume) := by
    have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < (1 / 2 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε_pos hε_lt
    refine (setLIntegral_congr_fun ?_ ?_).symm
    · measurability
    intro x hx
    have hxA : x ∈ A := by
      dsimp [A, euclideanSobolevUnitBallReflectionAnnulus]
      constructor
      · nlinarith [hx.1, hε_lt]
      · exact hx.2
    simp [F, hxA]
  exact hF_tendsto.congr' heq_eventually

/--
%%handwave
name:
  Vanishing linear taper gives zero \(L^1\) trace
statement:
  If a function is square-integrable on the annulus \(1<\|x\|<3/2\), then
  multiplying it by the linear taper \(3-2\|x\|\) gives a function whose
  interior \(L^1\) trace on the sphere \(\|x\|=3/2\) is zero.
proof:
  In the collar \(3/2-\varepsilon<\|x\|<3/2\), the taper is bounded by
  \(2\varepsilon\).  After normalization by \(1/\varepsilon\), the trace
  expression is controlled by the ordinary \(L^1\)-mass of the function on a
  shrinking annular collar, which tends to zero by absolute continuity of the
  integral.
-/
theorem hasL1TraceFromInsideSphere_three_halves_zero_of_annulus_taper
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {g : H → ℝ}
    (_hg : MemLp g 2
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H))) :
    HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      (fun x : H ↦ (3 - 2 * ‖x‖) * g x)
      (fun _x : H ↦ 0) := by
  have hmass :
      Filter.Tendsto
        (fun ε : ℝ ↦
          ∫⁻ x in {x : H | (3 / 2 : ℝ) - ε < ‖x‖ ∧
              ‖x‖ < (3 / 2 : ℝ)},
            ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) :=
    annulus_l1_collar_mass_tendsto_zero_at_three_halves _hg
  have hscaled :
      Filter.Tendsto
        (fun ε : ℝ ↦
          (2 : ℝ≥0∞) *
            ∫⁻ x in {x : H | (3 / 2 : ℝ) - ε < ‖x‖ ∧
                ‖x‖ < (3 / 2 : ℝ)},
              ENNReal.ofReal ‖g x‖ ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    have htwo_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have hmul := ENNReal.Tendsto.const_mul hmass (Or.inr htwo_ne_top)
    simpa [mul_assoc] using hmul
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hscaled
      (Filter.Eventually.of_forall fun _ε ↦ zero_le)
      (three_halves_taper_trace_integral_le_two_collar_mass
        (H := H) (g := g))

/--
%%handwave
name:
  Zero trace of the tapered reflected copy on the outer sphere
statement:
  If \(w\) is square integrable on the unit ball, then the tapered reflected
  copy \((3-2\|x\|)w(((2-\|x\|)/\|x\|)x)\) has zero \(L^1\) trace on the
  sphere of radius \(3/2\) from the inside.
proof:
  Near radius \(3/2\) the radial reflection remains in a compact subannulus
  of the unit ball, while the taper \(3-2\|x\|\) tends to zero uniformly.
  Use square-integrability of the reflected pullback on the annulus, then apply
  [the zero-trace statement for a square-integrable annular function
  multiplied by the vanishing taper](lean:JJMath.Uniformization.hasL1TraceFromInsideSphere_three_halves_zero_of_annulus_taper).
-/
theorem euclideanSobolev_unit_ball_radial_reflection_outer_trace_zero
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ}
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      (fun x : H ↦
        (3 - 2 * ‖x‖) *
          w (euclideanSobolevUnitBallRadialReflection x))
      (fun _x : H ↦ 0) := by
  have hpull :
      MemLp
        (fun x : H ↦ w (euclideanSobolevUnitBallRadialReflection x))
        2
        (MeasureTheory.volume.restrict
          (euclideanSobolevUnitBallReflectionAnnulus H)) :=
    euclideanSobolev_unit_ball_radial_reflection_annulus_pullback_memLp
      _hw
  exact
    hasL1TraceFromInsideSphere_three_halves_zero_of_annulus_taper
      hpull

/--
Collar-cutoff approximation data for gluing across the unit sphere and the
sphere of radius \(3/2\), localized to one test function and one direction.
-/
structure EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffLimitData
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    (u₀ u₁ : H → ℝ) (du₀ du₁ : H → H →L[ℝ] ℝ)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H) where
  leftApprox : ℕ → ℝ
  rightApprox : ℕ → ℝ
  local_identity :
    ∀ n : ℕ, leftApprox n = -rightApprox n
  left_tendsto :
    Filter.Tendsto leftApprox Filter.atTop
      (𝓝
        (∫ z in Set.univ,
          (fderiv ℝ (φ : H → ℝ) z v) •
            (if ‖z‖ < 1 then
              u₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              u₁ z
            else
              0) ∂MeasureTheory.volume))
  right_tendsto :
    Filter.Tendsto rightApprox Filter.atTop
      (𝓝
        (∫ z in Set.univ,
          φ z •
            ((if ‖z‖ < 1 then
              du₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              du₁ z
            else
              0) v) ∂MeasureTheory.volume))

/--
Smooth cutoff test functions for gluing across the unit sphere and the sphere
of radius `3 / 2`, localized to one ambient test function.
-/
structure EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestFunctions
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    where
  unitTest :
    ℕ → SmoothCompactlySupportedManifoldCoordinateFunction
      (Metric.ball (0 : H) 1)
  annulusTest :
    ℕ → SmoothCompactlySupportedManifoldCoordinateFunction
      (euclideanSobolevUnitBallReflectionAnnulus H)

/--
%%handwave
name:
  Smooth cutoff tests exist on shrinking ball and annulus cores
statement:
  For every smooth compactly supported ambient test function there are
  sequences of smooth compactly supported tests on the unit ball and on the
  annulus \(1<\|x\|<3/2\).  They are obtained by multiplying the ambient test
  by smooth cutoffs supported in the corresponding open regions.
proof:
  For the unit ball use compact cores
  \(\overline B(0,1-\varepsilon_n)\).  For the annulus use compact cores
  \(1+\varepsilon_n\le\|x\|\le 3/2-\varepsilon_n\), with
  \(\varepsilon_n=(n+4)^{-1}\).  The smooth cutoff theorem for compact
  subsets of open sets gives cutoff functions on each core.  Multiplying the
  ambient test by each cutoff gives the desired compactly supported smooth
  tests.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_cutoffTestFunctions
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H)) :
    Nonempty
      (EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestFunctions φ) := by
  classical
  let ε : ℕ → ℝ := fun n : ℕ ↦ ((n : ℝ) + 4)⁻¹
  let Qunit : ℕ → Set H := fun n : ℕ ↦
    Metric.closedBall (0 : H) (1 - ε n)
  let Qannulus : ℕ → Set H := fun n : ℕ ↦
    {x : H | 1 + ε n ≤ ‖x‖ ∧ ‖x‖ ≤ (3 / 2 : ℝ) - ε n}
  have hε_pos : ∀ n : ℕ, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hQunit_compact : ∀ n : ℕ, IsCompact (Qunit n) := by
    intro n
    dsimp [Qunit]
    exact isCompact_closedBall (0 : H) (1 - ε n)
  have hQunit_subset : ∀ n : ℕ, Qunit n ⊆ Metric.ball (0 : H) 1 := by
    intro n x hx
    have hxle : dist x (0 : H) ≤ 1 - ε n := by
      simpa [Qunit, Metric.mem_closedBall] using hx
    have hxlt : dist x (0 : H) < 1 := by
      nlinarith [hε_pos n, hxle]
    simpa [Metric.mem_ball] using hxlt
  have hQannulus_closed : ∀ n : ℕ, IsClosed (Qannulus n) := by
    intro n
    dsimp [Qannulus]
    exact
      (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
  have hQannulus_subset_closedBall :
      ∀ n : ℕ, Qannulus n ⊆ Metric.closedBall (0 : H) (3 / 2 : ℝ) := by
    intro n x hx
    have hxle : ‖x‖ ≤ (3 / 2 : ℝ) := by
      nlinarith [hε_pos n, hx.2]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxle
  have hQannulus_compact : ∀ n : ℕ, IsCompact (Qannulus n) := by
    intro n
    exact
      (isCompact_closedBall (0 : H) (3 / 2 : ℝ)).of_isClosed_subset
        (hQannulus_closed n) (hQannulus_subset_closedBall n)
  have hQannulus_subset :
      ∀ n : ℕ, Qannulus n ⊆ euclideanSobolevUnitBallReflectionAnnulus H := by
    intro n x hx
    dsimp [Qannulus, euclideanSobolevUnitBallReflectionAnnulus] at hx ⊢
    constructor
    · nlinarith [hε_pos n, hx.1]
    · nlinarith [hε_pos n, hx.2]
  let χunit :
      (n : ℕ) →
        ScalarWeakSobolevCutoff (Qunit n) (Metric.ball (0 : H) 1) :=
    fun n ↦
      Classical.choice
        (exists_scalarWeakSobolevCutoff
          (hQunit_compact n) (hQunit_subset n) Metric.isOpen_ball)
  let χannulus :
      (n : ℕ) →
        ScalarWeakSobolevCutoff (Qannulus n)
          (euclideanSobolevUnitBallReflectionAnnulus H) :=
    fun n ↦
      Classical.choice
        (exists_scalarWeakSobolevCutoff
          (hQannulus_compact n) (hQannulus_subset n)
          (by
            dsimp [euclideanSobolevUnitBallReflectionAnnulus]
            exact
              (isOpen_lt continuous_const continuous_norm).inter
                (isOpen_lt continuous_norm continuous_const)))
  let unitTest :
      ℕ → SmoothCompactlySupportedManifoldCoordinateFunction
        (Metric.ball (0 : H) 1) := fun n ↦
    { toFun := fun z : H ↦ (χunit n : H → ℝ) z * (φ : H → ℝ) z
      smooth := (χunit n).smooth.mul φ.smooth
      support_subset := by
        exact (tsupport_mul_subset_left).trans (χunit n).support_subset
      compact_support := by
        exact (χunit n).compact_support.of_isClosed_subset
          (isClosed_tsupport _) tsupport_mul_subset_left }
  let annulusTest :
      ℕ → SmoothCompactlySupportedManifoldCoordinateFunction
        (euclideanSobolevUnitBallReflectionAnnulus H) := fun n ↦
    { toFun := fun z : H ↦ (χannulus n : H → ℝ) z * (φ : H → ℝ) z
      smooth := (χannulus n).smooth.mul φ.smooth
      support_subset := by
        exact (tsupport_mul_subset_left).trans (χannulus n).support_subset
      compact_support := by
        exact (χannulus n).compact_support.of_isClosed_subset
          (isClosed_tsupport _) tsupport_mul_subset_left }
  exact ⟨{ unitTest := unitTest, annulusTest := annulusTest }⟩

/--
Convergence data for a chosen pair of cutoff test sequences.
-/
structure EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestConvergence
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    (u₀ u₁ : H → ℝ) (du₀ du₁ : H → H →L[ℝ] ℝ)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (tests : EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestFunctions φ)
    where
  left_tendsto :
    Filter.Tendsto
      (fun n : ℕ ↦
        (∫ z in Metric.ball (0 : H) 1,
          (fderiv ℝ (tests.unitTest n : H → ℝ) z v) • u₀ z
          ∂MeasureTheory.volume) +
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          (fderiv ℝ (tests.annulusTest n : H → ℝ) z v) • u₁ z
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in Set.univ,
          (fderiv ℝ (φ : H → ℝ) z v) •
            (if ‖z‖ < 1 then
              u₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              u₁ z
            else
              0) ∂MeasureTheory.volume))
  right_tendsto :
    Filter.Tendsto
      (fun n : ℕ ↦
        (∫ z in Metric.ball (0 : H) 1,
          (tests.unitTest n : H → ℝ) z • du₀ z v
          ∂MeasureTheory.volume) +
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          (tests.annulusTest n : H → ℝ) z • du₁ z v
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in Set.univ,
          φ z •
            ((if ‖z‖ < 1 then
              du₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              du₁ z
            else
                  0) v) ∂MeasureTheory.volume))

/--
Smooth collar cutoff tests with a recorded collar width.
-/
structure EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    extends EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestFunctions φ
    where
  unitCutoff : ℕ → H → ℝ
  annulusCutoff : ℕ → H → ℝ
  unitCutoff_smooth : ∀ n : ℕ, ContDiff ℝ ∞ (unitCutoff n)
  annulusCutoff_smooth : ∀ n : ℕ, ContDiff ℝ ∞ (annulusCutoff n)
  unitTest_eq :
    ∀ n : ℕ, ∀ x : H,
      (unitTest n : H → ℝ) x = unitCutoff n x * φ x
  annulusTest_eq :
    ∀ n : ℕ, ∀ x : H,
      (annulusTest n : H → ℝ) x = annulusCutoff n x * φ x
  unitCutoff_norm_le_one :
    ∀ n : ℕ, ∀ x : H, ‖unitCutoff n x‖ ≤ (1 : ℝ)
  annulusCutoff_norm_le_one :
    ∀ n : ℕ, ∀ x : H, ‖annulusCutoff n x‖ ≤ (1 : ℝ)
  width : ℕ → ℝ
  width_pos : ∀ n : ℕ, 0 < width n
  width_tendsto_zero :
    Filter.Tendsto width Filter.atTop (𝓝 (0 : ℝ))
  unitCutoff_eq_one_on_core :
    ∀ n : ℕ, ∀ x : H, ‖x‖ ≤ 1 - width n →
      unitCutoff n x = 1
  annulusCutoff_eq_one_on_core :
    ∀ n : ℕ, ∀ x : H,
      1 + width n ≤ ‖x‖ → ‖x‖ ≤ (3 / 2 : ℝ) - width n →
        annulusCutoff n x = 1
  unitCutoff_fderiv_eq_zero_on_core :
    ∀ n : ℕ, ∀ x : H, ‖x‖ ≤ 1 - width n →
      fderiv ℝ (unitCutoff n) x = 0
  annulusCutoff_fderiv_eq_zero_on_core :
    ∀ n : ℕ, ∀ x : H,
      1 + width n ≤ ‖x‖ → ‖x‖ ≤ (3 / 2 : ℝ) - width n →
        fderiv ℝ (annulusCutoff n) x = 0
  unit_eq_on_core :
    ∀ n : ℕ, ∀ x : H, ‖x‖ ≤ 1 - width n →
      (unitTest n : H → ℝ) x = φ x
  annulus_eq_on_core :
    ∀ n : ℕ, ∀ x : H,
      1 + width n ≤ ‖x‖ → ‖x‖ ≤ (3 / 2 : ℝ) - width n →
        (annulusTest n : H → ℝ) x = φ x
  unit_norm_le :
    ∀ n : ℕ, ∀ x : H, ‖(unitTest n : H → ℝ) x‖ ≤ ‖φ x‖
  annulus_norm_le :
    ∀ n : ℕ, ∀ x : H, ‖(annulusTest n : H → ℝ) x‖ ≤ ‖φ x‖

/--
Smooth collar cutoff tests whose cutoff-derivative collar terms have the
trace cancellation needed for gluing.
-/
structure EuclideanSobolevUnitBallAnnulusL1TraceGlueTraceControlledSmoothCollarCutoffTests
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    {u₀ u₁ τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    extends EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests φ
    where
  trace_collar_terms_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ ↦
        (∫ z in Metric.ball (0 : H) 1,
          ((fderiv ℝ (unitCutoff n) z v) * φ z) • u₀ z
          ∂MeasureTheory.volume) +
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          ((fderiv ℝ (annulusCutoff n) z v) * φ z) • u₁ z
          ∂MeasureTheory.volume)
      Filter.atTop (𝓝 (0 : ℝ))

/--
Scalar smooth collar cutoffs with the geometric support, core, and boundedness
properties needed before trace cancellation is imposed.
-/
structure EuclideanSobolevUnitBallAnnulusL1TraceGlueScalarCutoffGeometry
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    where
  unitCutoff : ℕ → H → ℝ
  annulusCutoff : ℕ → H → ℝ
  unitCutoff_smooth : ∀ n : ℕ, ContDiff ℝ ∞ (unitCutoff n)
  annulusCutoff_smooth : ∀ n : ℕ, ContDiff ℝ ∞ (annulusCutoff n)
  unitCutoff_tsupport_subset :
    ∀ n : ℕ, tsupport (unitCutoff n) ⊆ Metric.ball (0 : H) 1
  annulusCutoff_tsupport_subset :
    ∀ n : ℕ,
      tsupport (annulusCutoff n) ⊆
        euclideanSobolevUnitBallReflectionAnnulus H
  unitCutoff_compact_support :
    ∀ n : ℕ, IsCompact (tsupport (unitCutoff n))
  annulusCutoff_compact_support :
    ∀ n : ℕ, IsCompact (tsupport (annulusCutoff n))
  unitCutoff_norm_le_one :
    ∀ n : ℕ, ∀ x : H, ‖unitCutoff n x‖ ≤ (1 : ℝ)
  annulusCutoff_norm_le_one :
    ∀ n : ℕ, ∀ x : H, ‖annulusCutoff n x‖ ≤ (1 : ℝ)
  width : ℕ → ℝ
  width_pos : ∀ n : ℕ, 0 < width n
  width_tendsto_zero :
    Filter.Tendsto width Filter.atTop (𝓝 (0 : ℝ))
  unitCutoff_eq_one_on_core :
    ∀ n : ℕ, ∀ x : H, ‖x‖ ≤ 1 - width n →
      unitCutoff n x = 1
  annulusCutoff_eq_one_on_core :
    ∀ n : ℕ, ∀ x : H,
      1 + width n ≤ ‖x‖ → ‖x‖ ≤ (3 / 2 : ℝ) - width n →
        annulusCutoff n x = 1
  unitCutoff_fderiv_eq_zero_on_core :
    ∀ n : ℕ, ∀ x : H, ‖x‖ ≤ 1 - width n →
      fderiv ℝ (unitCutoff n) x = 0
  annulusCutoff_fderiv_eq_zero_on_core :
    ∀ n : ℕ, ∀ x : H,
      1 + width n ≤ ‖x‖ → ‖x‖ ≤ (3 / 2 : ℝ) - width n →
        fderiv ℝ (annulusCutoff n) x = 0

/--
Scalar smooth collar cutoffs with the trace cancellation needed for gluing.
This is the analytic part of the cutoff construction, before multiplying by
the ambient test function.
-/
structure EuclideanSobolevUnitBallAnnulusL1TraceGlueTraceControlledScalarCutoffData
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    {u₀ u₁ τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    extends EuclideanSobolevUnitBallAnnulusL1TraceGlueScalarCutoffGeometry
      (H := H)
    where
  trace_collar_terms_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ ↦
        (∫ z in Metric.ball (0 : H) 1,
          ((fderiv ℝ (unitCutoff n) z v) * φ z) • u₀ z
          ∂MeasureTheory.volume) +
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          ((fderiv ℝ (annulusCutoff n) z v) * φ z) • u₁ z
          ∂MeasureTheory.volume)
      Filter.atTop (𝓝 (0 : ℝ))

private theorem exists_scalarWeakSobolevCutoff_range_Icc
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H]
    {Q Ω : Set H} (hQ : IsCompact Q)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω) :
    ∃ χ : ScalarWeakSobolevCutoff Q Ω,
      ∀ x : H, (χ : H → ℝ) x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨δ, hδ_pos, hδΩ⟩ :=
    hQ.exists_cthickening_subset_open hΩ_open hQΩ
  let η : ℝ := δ / 2
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  have hη_ltδ : η < δ := by
    dsimp [η]
    linarith
  have hclosed_eta : IsClosed (Metric.cthickening η Q) :=
    Metric.isClosed_cthickening
  have heta_subset_thickening :
      Metric.cthickening η Q ⊆ Metric.thickening δ Q :=
    Metric.cthickening_subset_thickening' hδ_pos hη_ltδ Q
  obtain ⟨χ, hχ_smooth, hχ_range, hχ_support, hχ_one⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := 𝓘(ℝ, H)) (n := ⊤)
      (Metric.isOpen_thickening) hclosed_eta heta_subset_thickening
  have hχ_tsupport_subset_cthickening :
      tsupport χ ⊆ Metric.cthickening δ Q := by
    rw [tsupport, hχ_support]
    exact Metric.closure_thickening_subset_cthickening δ Q
  have hχ_deriv_zero :
      ∀ z ∈ Q, fderiv ℝ χ z = 0 := by
    intro z hzQ
    have hz_thick : z ∈ Metric.thickening η Q :=
      Metric.self_subset_thickening hη_pos Q hzQ
    have hnhds : Metric.thickening η Q ∈ 𝓝 z :=
      Metric.isOpen_thickening.mem_nhds hz_thick
    have hχ_eventually :
        χ =ᶠ[𝓝 z] fun _ : H ↦ (1 : ℝ) := by
      filter_upwards [hnhds] with y hy
      exact (hχ_one y).1 ((Metric.thickening_subset_cthickening η Q) hy)
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hχ_eventually]
    simp
  refine
    ⟨{ toFun := χ
       smooth := hχ_smooth.contDiff
       support_subset := hχ_tsupport_subset_cthickening.trans hδΩ
       compact_support := by
        exact IsCompact.of_isClosed_subset (hQ.cthickening)
          (isClosed_tsupport χ) hχ_tsupport_subset_cthickening
       eq_one_on := by
        intro z hzQ
        exact (hχ_one z).1 (Metric.self_subset_cthickening Q hzQ)
       fderiv_eq_zero_on := hχ_deriv_zero }, ?_⟩
  intro x
  exact hχ_range ⟨x, rfl⟩

/--
%%handwave
name:
  Smooth collar cutoff families exist
statement:
  For every compactly supported smooth ambient test function there are smooth
  tests on the unit ball and on the annulus \(1<\|x\|<3/2\), obtained from
  smooth radial collar cutoffs with widths tending to zero.  The tests agree
  with the ambient test on the compact cores away from the boundary spheres
  and are pointwise bounded in absolute value by the ambient test.
proof:
  Choose smooth one-dimensional radial cutoff profiles on the intervals
  \((-\infty,1)\) and \((1,3/2)\), with transition layers of width
  \(\varepsilon_n\downarrow0\).  Compose these profiles with the norm and
  multiply by the ambient test.  The bounds follow from choosing profiles
  with values in \([0,1]\).
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_smooth_collar_cutoff_tests
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H)) :
    Nonempty
      (EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests φ) := by
  classical
  let ε : ℕ → ℝ := fun n : ℕ ↦ ((n : ℝ) + 4)⁻¹
  let Qunit : ℕ → Set H := fun n : ℕ ↦
    Metric.closedBall (0 : H) (1 - ε n)
  let Qannulus : ℕ → Set H := fun n : ℕ ↦
    {x : H | 1 + ε n ≤ ‖x‖ ∧ ‖x‖ ≤ (3 / 2 : ℝ) - ε n}
  have hε_pos : ∀ n : ℕ, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hε_tendsto :
      Filter.Tendsto ε Filter.atTop (𝓝 (0 : ℝ)) := by
    have hbase :
        Filter.Tendsto
          (fun n : ℕ ↦ 1 / (((n + 3 : ℕ) : ℝ) + 1))
          Filter.atTop (𝓝 (0 : ℝ)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (Filter.tendsto_add_atTop_nat 3)
    exact Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n : ℕ ↦ by
        dsimp [ε]
        norm_num [one_div, Nat.cast_add]
        ring)
      hbase
  have hQunit_compact : ∀ n : ℕ, IsCompact (Qunit n) := by
    intro n
    dsimp [Qunit]
    exact isCompact_closedBall (0 : H) (1 - ε n)
  have hQunit_subset : ∀ n : ℕ, Qunit n ⊆ Metric.ball (0 : H) 1 := by
    intro n x hx
    have hxle : dist x (0 : H) ≤ 1 - ε n := by
      simpa [Qunit, Metric.mem_closedBall] using hx
    have hxlt : dist x (0 : H) < 1 := by
      nlinarith [hε_pos n, hxle]
    simpa [Metric.mem_ball] using hxlt
  have hQannulus_closed : ∀ n : ℕ, IsClosed (Qannulus n) := by
    intro n
    dsimp [Qannulus]
    exact
      (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
  have hQannulus_subset_closedBall :
      ∀ n : ℕ, Qannulus n ⊆ Metric.closedBall (0 : H) (3 / 2 : ℝ) := by
    intro n x hx
    have hxle : ‖x‖ ≤ (3 / 2 : ℝ) := by
      nlinarith [hε_pos n, hx.2]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxle
  have hQannulus_compact : ∀ n : ℕ, IsCompact (Qannulus n) := by
    intro n
    exact
      (isCompact_closedBall (0 : H) (3 / 2 : ℝ)).of_isClosed_subset
        (hQannulus_closed n) (hQannulus_subset_closedBall n)
  have hQannulus_subset :
      ∀ n : ℕ, Qannulus n ⊆ euclideanSobolevUnitBallReflectionAnnulus H := by
    intro n x hx
    dsimp [Qannulus, euclideanSobolevUnitBallReflectionAnnulus] at hx ⊢
    constructor
    · nlinarith [hε_pos n, hx.1]
    · nlinarith [hε_pos n, hx.2]
  let χunit :
      (n : ℕ) →
        ScalarWeakSobolevCutoff (Qunit n) (Metric.ball (0 : H) 1) :=
    fun n ↦
      Classical.choose
        (exists_scalarWeakSobolevCutoff_range_Icc
          (hQunit_compact n) (hQunit_subset n) Metric.isOpen_ball)
  let χannulus :
      (n : ℕ) →
        ScalarWeakSobolevCutoff (Qannulus n)
          (euclideanSobolevUnitBallReflectionAnnulus H) :=
    fun n ↦
      Classical.choose
        (exists_scalarWeakSobolevCutoff_range_Icc
          (hQannulus_compact n) (hQannulus_subset n)
          (by
            dsimp [euclideanSobolevUnitBallReflectionAnnulus]
            exact
              (isOpen_lt continuous_const continuous_norm).inter
                (isOpen_lt continuous_norm continuous_const)))
  have hχunit_range :
      ∀ n : ℕ, ∀ x : H,
        (χunit n : H → ℝ) x ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    exact
      Classical.choose_spec
        (exists_scalarWeakSobolevCutoff_range_Icc
          (hQunit_compact n) (hQunit_subset n) Metric.isOpen_ball)
  have hχannulus_range :
      ∀ n : ℕ, ∀ x : H,
        (χannulus n : H → ℝ) x ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    exact
      Classical.choose_spec
        (exists_scalarWeakSobolevCutoff_range_Icc
          (hQannulus_compact n) (hQannulus_subset n)
          (by
            dsimp [euclideanSobolevUnitBallReflectionAnnulus]
            exact
              (isOpen_lt continuous_const continuous_norm).inter
                (isOpen_lt continuous_norm continuous_const)))
  let unitTest :
      ℕ → SmoothCompactlySupportedManifoldCoordinateFunction
        (Metric.ball (0 : H) 1) := fun n ↦
    { toFun := fun z : H ↦ (χunit n : H → ℝ) z * (φ : H → ℝ) z
      smooth := (χunit n).smooth.mul φ.smooth
      support_subset := by
        exact (tsupport_mul_subset_left).trans (χunit n).support_subset
      compact_support := by
        exact (χunit n).compact_support.of_isClosed_subset
          (isClosed_tsupport _) tsupport_mul_subset_left }
  let annulusTest :
      ℕ → SmoothCompactlySupportedManifoldCoordinateFunction
        (euclideanSobolevUnitBallReflectionAnnulus H) := fun n ↦
    { toFun := fun z : H ↦ (χannulus n : H → ℝ) z * (φ : H → ℝ) z
      smooth := (χannulus n).smooth.mul φ.smooth
      support_subset := by
        exact (tsupport_mul_subset_left).trans (χannulus n).support_subset
      compact_support := by
        exact (χannulus n).compact_support.of_isClosed_subset
          (isClosed_tsupport _) tsupport_mul_subset_left }
  refine
    ⟨{ toEuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestFunctions :=
          { unitTest := unitTest
            annulusTest := annulusTest }
       unitCutoff := fun n ↦ (χunit n : H → ℝ)
       annulusCutoff := fun n ↦ (χannulus n : H → ℝ)
       unitCutoff_smooth := fun n ↦ (χunit n).smooth
       annulusCutoff_smooth := fun n ↦ (χannulus n).smooth
       unitTest_eq := by
        intro n x
        rfl
       annulusTest_eq := by
        intro n x
        rfl
       unitCutoff_norm_le_one := ?_
       annulusCutoff_norm_le_one := ?_
       width := ε
       width_pos := hε_pos
       width_tendsto_zero := hε_tendsto
       unitCutoff_eq_one_on_core := ?_
       annulusCutoff_eq_one_on_core := ?_
       unitCutoff_fderiv_eq_zero_on_core := ?_
       annulusCutoff_fderiv_eq_zero_on_core := ?_
       unit_eq_on_core := ?_
       annulus_eq_on_core := ?_
       unit_norm_le := ?_
       annulus_norm_le := ?_ }⟩
  · intro n x
    rcases hχunit_range n x with ⟨hχ_nonneg, hχ_le⟩
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, hχ_le⟩
  · intro n x
    rcases hχannulus_range n x with ⟨hχ_nonneg, hχ_le⟩
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, hχ_le⟩
  · intro n x hx
    have hxQ : x ∈ Qunit n := by
      dsimp [Qunit]
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    exact (χunit n).eq_one_on x hxQ
  · intro n x hx₁ hx₂
    have hxQ : x ∈ Qannulus n := by
      dsimp [Qannulus]
      exact ⟨hx₁, hx₂⟩
    exact (χannulus n).eq_one_on x hxQ
  · intro n x hx
    have hxQ : x ∈ Qunit n := by
      dsimp [Qunit]
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    exact (χunit n).fderiv_eq_zero_on x hxQ
  · intro n x hx₁ hx₂
    have hxQ : x ∈ Qannulus n := by
      dsimp [Qannulus]
      exact ⟨hx₁, hx₂⟩
    exact (χannulus n).fderiv_eq_zero_on x hxQ
  · intro n x hx
    have hxQ : x ∈ Qunit n := by
      dsimp [Qunit]
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    simp [unitTest, (χunit n).eq_one_on x hxQ]
  · intro n x hx₁ hx₂
    have hxQ : x ∈ Qannulus n := by
      dsimp [Qannulus]
      exact ⟨hx₁, hx₂⟩
    simp [annulusTest, (χannulus n).eq_one_on x hxQ]
  · intro n x
    have hχ_abs : ‖(χunit n : H → ℝ) x‖ ≤ (1 : ℝ) := by
      rcases hχunit_range n x with ⟨hχ_nonneg, hχ_le⟩
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, hχ_le⟩
    calc
      ‖(unitTest n : H → ℝ) x‖
          = ‖(χunit n : H → ℝ) x‖ * ‖φ x‖ := by
            simp [unitTest, norm_mul]
      _ ≤ 1 * ‖φ x‖ :=
            mul_le_mul_of_nonneg_right hχ_abs (norm_nonneg _)
      _ = ‖φ x‖ := one_mul _
  · intro n x
    have hχ_abs : ‖(χannulus n : H → ℝ) x‖ ≤ (1 : ℝ) := by
      rcases hχannulus_range n x with ⟨hχ_nonneg, hχ_le⟩
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, hχ_le⟩
    calc
      ‖(annulusTest n : H → ℝ) x‖
          = ‖(χannulus n : H → ℝ) x‖ * ‖φ x‖ := by
            simp [annulusTest, norm_mul]
      _ ≤ 1 * ‖φ x‖ :=
            mul_le_mul_of_nonneg_right hχ_abs (norm_nonneg _)
      _ = ‖φ x‖ := one_mul _

/--
Boundary integrability of the trace itself, and of the trace against the
fixed smooth weight and normal component associated to a test direction.
-/
def EuclideanSobolevUnitSphereWeightedTraceIntegrable
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H]
    (τ : H → ℝ)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H) : Prop :=
  Integrable
      (fun θ : Metric.sphere (0 : H) 1 ↦ τ (θ : H))
      ((MeasureTheory.volume : Measure H).toSphere) ∧
    Integrable
      (fun θ : Metric.sphere (0 : H) 1 ↦
        τ (θ : H) * φ (θ : H) * inner ℝ (θ : H) v)
      ((MeasureTheory.volume : Measure H).toSphere)

/--
If the trace itself is integrable on the unit sphere, then its product with a
fixed smooth ambient test function and a fixed normal component is integrable.
-/
theorem euclideanSobolev_unit_sphere_weighted_trace_integrable_of_trace_integrable
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hτ : Integrable
      (fun θ : Metric.sphere (0 : H) 1 ↦ τ (θ : H))
      ((MeasureTheory.volume : Measure H).toSphere)) :
    EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v := by
  classical
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let weight : Metric.sphere (0 : H) 1 → ℝ := fun θ ↦
    φ (θ : H) * inner ℝ (θ : H) v
  have hweight_cont : Continuous weight := by
    have hφ_cont : Continuous (fun θ : Metric.sphere (0 : H) 1 ↦
        φ (θ : H)) :=
      φ.smooth.continuous.comp continuous_subtype_val
    have hinner_cont : Continuous (fun θ : Metric.sphere (0 : H) 1 ↦
        inner ℝ (θ : H) v) :=
      continuous_subtype_val.inner continuous_const
    simpa [weight] using hφ_cont.mul hinner_cont
  have hweight_aesm : AEStronglyMeasurable weight μS :=
    hweight_cont.aestronglyMeasurable
  rcases
      (isCompact_univ.exists_bound_of_continuousOn
        hweight_cont.continuousOn) with
    ⟨C, hC⟩
  have hweight_bound : ∀ᵐ θ ∂μS, ‖weight θ‖ ≤ C :=
    Filter.Eventually.of_forall fun θ ↦ hC θ (Set.mem_univ θ)
  have hmul :
      Integrable
        (fun θ : Metric.sphere (0 : H) 1 ↦
          (τ (θ : H)) * weight θ) μS :=
    hτ.mul_bdd hweight_aesm hweight_bound
  exact
    ⟨by simpa [μS] using hτ,
      by
        simpa [EuclideanSobolevUnitSphereWeightedTraceIntegrable, weight, μS,
          mul_assoc] using hmul⟩

/--
%%handwave
name:
  An integrable sphere function has an integrable radial extension on bounded
  collars
statement:
  If a boundary function on the unit sphere is integrable, then its radial
  extension \(x\mapsto \tau(x/\|x\|)\) is integrable on every bounded annulus
  \(a<\|x\|<b\) with \(0<a<b\).
proof:
  Use polar coordinates on the punctured space.  The annulus becomes the
  product of the unit sphere with the finite radial interval \(a<r<b\), and
  the radial extension becomes the pullback of the sphere function by the
  first projection.  Since the radial interval has finite measure, product
  integrability follows from integrability on the sphere, and the
  measure-preserving polar map transfers it back to the annulus.
-/
private theorem euclideanSobolev_unit_sphere_integrable_radial_extension_on_annulus
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {τ : H → ℝ} {a b : ℝ}
    (ha_pos : 0 < a) (_hab : a < b)
    (hτ : Integrable
      (fun θ : Metric.sphere (0 : H) 1 ↦ τ (θ : H))
      ((MeasureTheory.volume : Measure H).toSphere)) :
    Integrable
      (fun x : H ↦ τ (((1 / ‖x‖) : ℝ) • x))
      (MeasureTheory.volume.restrict {x : H | a < ‖x‖ ∧ ‖x‖ < b}) := by
  classical
  by_cases hsub : Subsingleton H
  · haveI : Subsingleton H := hsub
    have hset_empty :
        {x : H | a < ‖x‖ ∧ ‖x‖ < b} = ∅ := by
      ext x
      have hx0 : x = 0 := Subsingleton.elim x 0
      simp [hx0, ha_pos.not_gt]
    simp [hset_empty]
  · haveI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hsub
    let μH : Measure H := MeasureTheory.volume
    let μS : Measure (Metric.sphere (0 : H) 1) := μH.toSphere
    let μR : Measure (Set.Ioi (0 : ℝ)) :=
      MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
    let I : Set (Set.Ioi (0 : ℝ)) :=
      {r : Set.Ioi (0 : ℝ) | a < (r : ℝ) ∧ (r : ℝ) < b}
    let P : Set (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
      Set.univ ×ˢ I
    let C : Set H := {x : H | a < ‖x‖ ∧ ‖x‖ < b}
    let NZ : Set H := {0}ᶜ
    let T : Set ({0}ᶜ : Set H) := ((↑) : ({0}ᶜ : Set H) → H) ⁻¹' C
    let e : ({0}ᶜ : Set H) ≃ₜ
        (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
      homeomorphUnitSphereProd H
    let μNZ : Measure ({0}ᶜ : Set H) :=
      μH.comap ((↑) : ({0}ᶜ : Set H) → H)
    let ν : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
      μS.prod μR
    let F : H → ℝ := fun x : H ↦ τ (((1 / ‖x‖) : ℝ) • x)
    let G : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) → ℝ :=
      fun p ↦ τ (p.1 : H)
    have hNZ_meas : MeasurableSet NZ := by
      dsimp [NZ]
      exact (measurableSet_singleton (0 : H)).compl
    have hC_subset_NZ : C ⊆ NZ := by
      intro x hx
      dsimp [C, NZ] at hx ⊢
      exact norm_pos_iff.mp (ha_pos.trans hx.1)
    let R : Set.Ioi (0 : ℝ) :=
      ⟨max b 1, lt_of_lt_of_le zero_lt_one (le_max_right b 1)⟩
    have hI_subset : I ⊆ Set.Iio R := by
      intro r hr
      dsimp [I, R] at hr ⊢
      exact hr.2.trans_le (le_max_left b 1)
    have hμR_I_ne_top : μR I ≠ (∞ : ℝ≥0∞) := by
      have hIio_ne_top : μR (Set.Iio R) ≠ (∞ : ℝ≥0∞) := by
        simp [μR, MeasureTheory.Measure.volumeIoiPow_apply_Iio]
      exact ne_top_of_le_ne_top hIio_ne_top (measure_mono hI_subset)
    haveI : IsFiniteMeasure (μR.restrict I) :=
      isFiniteMeasure_restrict.2 hμR_I_ne_top
    have hprod_int :
        Integrable G (μS.prod (μR.restrict I)) := by
      simpa [G, μS] using
        (by
          have hτ' :
              Integrable
                (fun θ : Metric.sphere (0 : H) 1 ↦ τ (θ : H)) μS := by
            simpa [μS, μH] using hτ
          exact hτ'.comp_fst (μR.restrict I))
    have hν_restrict :
        ν.restrict P = μS.prod (μR.restrict I) := by
      have hprod :=
        Measure.prod_restrict (μ := μS) (ν := μR) Set.univ I
      simpa [ν, P] using hprod.symm
    have hprod_on : IntegrableOn G P ν := by
      rw [IntegrableOn, hν_restrict]
      exact hprod_int
    have hmp : MeasurePreserving e μNZ ν := by
      simpa [e, μNZ, ν, μS, μR, μH] using
        (MeasureTheory.volume : Measure H).measurePreserving_homeomorphUnitSphereProd
    have hcomp_on : IntegrableOn (G ∘ e) (e ⁻¹' P) μNZ :=
      (hmp.integrableOn_comp_preimage e.measurableEmbedding).2 hprod_on
    have hpre : e ⁻¹' P = T := by
      ext x
      simp [P, T, C, I, e, homeomorphUnitSphereProd_apply_snd_coe]
    have hsubtype_int :
        Integrable (fun x : ({0}ᶜ : Set H) ↦ F (x : H)) (μNZ.restrict T) := by
      rw [IntegrableOn, hpre] at hcomp_on
      refine hcomp_on.congr ?_
      filter_upwards with x
      have hdir :
          ((e x).1 : H) =
            (((1 / ‖(x : H)‖) : ℝ) • (x : H)) := by
        simp [e, homeomorphUnitSphereProd_apply_fst_coe, div_eq_mul_inv]
      simp [F, G, hdir]
    have hcomap :
        (μH.restrict C).comap ((↑) : ({0}ᶜ : Set H) → H) =
          μNZ.restrict T := by
      have hraw :=
        (MeasurableEmbedding.subtype_coe hNZ_meas).comap_restrict
          μH C
      simpa [μNZ, T] using hraw
    have hraw :
        Integrable (F ∘ ((↑) : ({0}ᶜ : Set H) → H))
          ((μH.restrict C).comap ((↑) : ({0}ᶜ : Set H) → H)) := by
      simpa [hcomap, Function.comp_def] using hsubtype_int
    have hOn : IntegrableOn F NZ (μH.restrict C) :=
      (integrableOn_iff_comap_subtypeVal hNZ_meas).2 hraw
    rw [IntegrableOn] at hOn
    have hrestrict_eq :
        (μH.restrict C).restrict NZ = μH.restrict C := by
      rw [Measure.restrict_restrict hNZ_meas]
      have hinter : NZ ∩ C = C := Set.inter_eq_right.mpr hC_subset_NZ
      rw [hinter]
    simpa [F, C, μH, hrestrict_eq]
      using hOn

/--
%%handwave
name:
  A finite collar integral of a radial boundary extension gives sphere
  integrability
statement:
  Suppose \(0<\varepsilon<1\).  If the radial extension
  \(x\mapsto \tau(x/\|x\|)\) is integrable on the inner collar
  \(1-\varepsilon<\|x\|<1\), then \(\tau\) is integrable on the unit sphere.
proof:
  Remove the origin and use the polar-coordinate homeomorphism.  The collar
  becomes the product of the unit sphere with the radial interval
  \(1-\varepsilon<r<1\), and the radial extension becomes the pullback of
  \(\tau\) by the first projection.  Since this radial interval has positive
  finite measure, product-measure integrability of the pullback is equivalent
  to integrability of \(\tau\) on the sphere.
-/
theorem euclideanSobolev_unit_ball_integrable_sphere_trace_of_radial_extension_integrable_on_collar
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {τ : H → ℝ} {ε : ℝ}
    (_hε_pos : 0 < ε) (_hε_lt : ε < 1)
    (_hτ_meas : Measurable τ)
    (_hcollar :
      Integrable
        (fun x : H ↦ τ (((1 / ‖x‖) : ℝ) • x))
        (MeasureTheory.volume.restrict
          {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1})) :
    Integrable
      (fun θ : Metric.sphere (0 : H) 1 ↦ τ (θ : H))
      ((MeasureTheory.volume : Measure H).toSphere) := by
  classical
  by_cases hsub : Subsingleton H
  · haveI : Subsingleton H := hsub
    have hμS_zero :
        (MeasureTheory.volume : Measure H).toSphere = 0 := by
      rw [MeasureTheory.Measure.toSphere_eq_zero_iff]
      infer_instance
    simp [hμS_zero]
  · haveI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hsub
    let μH : Measure H := MeasureTheory.volume
    let μS : Measure (Metric.sphere (0 : H) 1) := μH.toSphere
    let μR : Measure (Set.Ioi (0 : ℝ)) :=
      MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
    let a : Set.Ioi (0 : ℝ) :=
      ⟨(1 : ℝ) - ε, sub_pos.mpr _hε_lt⟩
    let b : Set.Ioi (0 : ℝ) :=
      ⟨(1 : ℝ), by norm_num⟩
    let I : Set (Set.Ioi (0 : ℝ)) := Set.Ioo a b
    let P : Set (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
      Set.univ ×ˢ I
    let C : Set H :=
      {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1}
    let NZ : Set H := {0}ᶜ
    let T : Set ({0}ᶜ : Set H) := ((↑) : ({0}ᶜ : Set H) → H) ⁻¹' C
    let e : ({0}ᶜ : Set H) ≃ₜ
        (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
      homeomorphUnitSphereProd H
    let μNZ : Measure ({0}ᶜ : Set H) :=
      μH.comap ((↑) : ({0}ᶜ : Set H) → H)
    let ν : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
      μS.prod μR
    let F : H → ℝ := fun x : H ↦ τ (((1 / ‖x‖) : ℝ) • x)
    have hNZ_meas : MeasurableSet NZ := by
      dsimp [NZ]
      exact (measurableSet_singleton (0 : H)).compl
    have hC_subset_NZ : C ⊆ NZ := by
      intro x hx
      dsimp [C, NZ] at hx ⊢
      have hx_pos : 0 < ‖x‖ := by linarith
      exact norm_pos_iff.mp hx_pos
    have hF_on_NZ : IntegrableOn F NZ (μH.restrict C) := by
      rw [IntegrableOn, Measure.restrict_restrict hNZ_meas]
      have hinter : NZ ∩ C = C := Set.inter_eq_right.mpr hC_subset_NZ
      simpa [F, C, μH, hinter] using _hcollar
    have hsubtype_int :
        Integrable (fun x : ({0}ᶜ : Set H) ↦ F (x : H))
          (μNZ.restrict T) := by
      have hraw :
          Integrable (F ∘ ((↑) : ({0}ᶜ : Set H) → H))
            ((μH.restrict C).comap
              ((↑) : ({0}ᶜ : Set H) → H)) :=
        (integrableOn_iff_comap_subtypeVal hNZ_meas).1 hF_on_NZ
      have hcomap :
          (μH.restrict C).comap
              ((↑) : ({0}ᶜ : Set H) → H) =
            μNZ.restrict T := by
        simpa [μNZ, T] using
          (MeasurableEmbedding.subtype_coe hNZ_meas).comap_restrict
            μH C
      rw [hcomap] at hraw
      simpa [Function.comp_def] using hraw
    have hmp : MeasurePreserving e μNZ ν := by
      simpa [e, μNZ, ν, μS, μR, μH] using
        (MeasureTheory.volume : Measure H).measurePreserving_homeomorphUnitSphereProd
    have hpre : e ⁻¹' P = T := by
      ext x
      have hsnd :
          ((e x).2 : ℝ) = ‖(x : H)‖ := by
        simp [e, homeomorphUnitSphereProd_apply_snd_coe]
      simp only [P, T, C, I, Set.mem_preimage, Set.mem_prod,
        Set.mem_univ, true_and, Set.mem_Ioo]
      change
        ((1 : ℝ) - ε < ((e x).2 : ℝ) ∧ ((e x).2 : ℝ) < 1) ↔
          (1 : ℝ) - ε < ‖(x : H)‖ ∧ ‖(x : H)‖ < 1
      rw [hsnd]
    have hcomp_int :
        IntegrableOn
          ((fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
            τ (p.1 : H)) ∘ e)
          (e ⁻¹' P) μNZ := by
      rw [IntegrableOn, hpre]
      refine hsubtype_int.congr ?_
      filter_upwards with x
      have hdir :
          ((e x).1 : H) =
            (((1 / ‖(x : H)‖) : ℝ) • (x : H)) := by
        simp [e, homeomorphUnitSphereProd_apply_fst_coe, div_eq_mul_inv]
      simp [F, hdir]
    have hprod_on :
        IntegrableOn
          (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
            τ (p.1 : H))
          P ν :=
      (hmp.integrableOn_comp_preimage e.measurableEmbedding).1 hcomp_int
    have hν_restrict :
        ν.restrict P = μS.prod (μR.restrict I) := by
      have hprod :=
        Measure.prod_restrict (μ := μS) (ν := μR) Set.univ I
      simpa [ν, P] using hprod.symm
    have hprod_int :
        Integrable
          (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
            τ (p.1 : H))
          (μS.prod (μR.restrict I)) := by
      rw [IntegrableOn] at hprod_on
      simpa [hν_restrict] using hprod_on
    have hμR_I_pos : 0 < μR I := by
      let density : Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun r ↦
        ENNReal.ofReal ((r : ℝ) ^ (Module.finrank ℝ H - 1))
      have hdensity_meas : Measurable density := by
        dsimp [density]
        measurability
      have hI_meas : MeasurableSet I := by
        dsimp [I]
        exact measurableSet_Ioo
      have hbase_pos :
          0 <
            (Measure.comap ((↑) : Set.Ioi (0 : ℝ) → ℝ)
              (MeasureTheory.volume : Measure ℝ)) I := by
        rw [comap_subtype_coe_apply
          (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))
          (MeasureTheory.volume : Measure ℝ) I]
        have himage :
            ((↑) : Set.Ioi (0 : ℝ) → ℝ) '' I =
              Set.Ioo ((1 : ℝ) - ε) 1 := by
          simp [I, a, b]
        rw [himage, Real.volume_Ioo]
        exact ENNReal.ofReal_pos.mpr (by linarith)
      have hsupp_inter : Function.support density ∩ I = I := by
        ext r
        constructor
        · intro hr
          exact hr.2
        · intro hr
          refine ⟨?_, hr⟩
          dsimp [density, Function.support]
          exact ne_of_gt <|
            ENNReal.ofReal_pos.mpr
              (pow_pos r.2 (Module.finrank ℝ H - 1))
      change
        0 <
          (Measure.withDensity
            (Measure.comap ((↑) : Set.Ioi (0 : ℝ) → ℝ)
              (MeasureTheory.volume : Measure ℝ)) density) I
      rw [withDensity_apply density hI_meas]
      rw [setLIntegral_pos_iff hdensity_meas]
      simpa [density, hsupp_inter] using hbase_pos
    have hμR_restrict_ne_zero : μR.restrict I ≠ 0 := by
      intro hzero
      have hmeasure_zero :
          (μR.restrict I) Set.univ = 0 := by
        rw [hzero]
        simp
      have hI_zero : μR I = 0 := by
        simpa using hmeasure_zero
      exact hμR_I_pos.ne' hI_zero
    have hsphere_int :
        Integrable
          (fun θ : Metric.sphere (0 : H) 1 ↦ τ (θ : H))
          μS :=
      Integrable.of_comp_fst hprod_int hμR_restrict_ne_zero
    simpa [μS, μH] using hsphere_int

/--
%%handwave
name:
  An inside \(L^1\) trace has finite radial extension mass on some collar
statement:
  Let \(w\) be square-integrable in the unit ball and let \(\tau\) be a
  measurable inside \(L^1\)-trace of \(w\) on the unit sphere.  Then for some
  \(0<\varepsilon<1\), the radial extension
  \(x\mapsto \tau(x/\|x\|)\) is integrable on the collar
  \(1-\varepsilon<\|x\|<1\).
proof:
  The trace convergence gives a sufficiently thin collar where the normalized
  \(L^1\)-error between \(w\) and the radial extension of \(\tau\) is finite.
  Since \(w\in L^2\) on the finite-measure unit ball, \(w\) is \(L^1\) on the
  same collar.  The radial extension is the difference of \(w\) and this
  finite \(L^1\)-error, hence is integrable on that collar.
-/
theorem euclideanSobolev_unit_ball_radial_trace_extension_integrable_on_some_collar
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w τ : H → ℝ}
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hτ_meas : Measurable τ)
    (_htrace : HasL1TraceFromInsideSphere (H := H) 1 w τ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      Integrable
        (fun x : H ↦ τ (((1 / ‖x‖) : ℝ) • x))
        (MeasureTheory.volume.restrict
          {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1}) := by
  classical
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let B : Set H := Metric.ball (0 : H) 1
  have hB_subset : B ⊆ Metric.closedBall (0 : H) 1 :=
    Metric.ball_subset_closedBall
  have hclosed_ne_top :
      (MeasureTheory.volume : Measure H)
        (Metric.closedBall (0 : H) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : H) 1).measure_ne_top
  have hB_ne_top : (MeasureTheory.volume : Measure H) B ≠ ⊤ :=
    ne_top_of_le_ne_top hclosed_ne_top (measure_mono hB_subset)
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict B) :=
    isFiniteMeasure_restrict.2 hB_ne_top
  have hw_int_B : Integrable w (MeasureTheory.volume.restrict B) := by
    simpa [B] using
      _hw.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [HasL1TraceFromInsideSphere] at _htrace
  have hfinite :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal (1 / ε) *
          ∫⁻ x in {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1},
            ENNReal.ofReal
              ‖w x - τ (((1 / ‖x‖) : ℝ) • x)‖
              ∂MeasureTheory.volume < (⊤ : ℝ≥0∞) :=
    _htrace.eventually
      (gt_mem_nhds (by simp : (0 : ℝ≥0∞) < (⊤ : ℝ≥0∞)))
  have hpos_eventual : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := by
    exact self_mem_nhdsWithin
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  rcases (hfinite.and (hpos_eventual.and hsmall)).exists with
    ⟨ε, hε_finite, hε_pos, hε_lt⟩
  let S : Set H := {x : H | (1 : ℝ) - ε < ‖x‖ ∧ ‖x‖ < 1}
  let μS : Measure H := MeasureTheory.volume.restrict S
  have hS_subset_B : S ⊆ B := by
    intro x hx
    dsimp [S, B] at hx ⊢
    simpa [Metric.mem_ball, dist_eq_norm] using hx.2
  have hw_int_S : Integrable w μS := by
    exact hw_int_B.mono_measure
      (by
        simpa [μS, B, S] using
          Measure.restrict_mono_set
            (MeasureTheory.volume : Measure H) hS_subset_B)
  let π : H → H := fun x : H ↦ ((1 / ‖x‖) : ℝ) • x
  have hπ_meas : Measurable π := by
    dsimp [π]
    measurability
  have hτπ_aemeas : AEMeasurable (fun x : H ↦ τ (π x)) μS :=
    _hτ_meas.comp_aemeasurable hπ_meas.aemeasurable
  have hdiff_aemeas :
      AEStronglyMeasurable (fun x : H ↦ w x - τ (π x)) μS :=
    hw_int_S.aestronglyMeasurable.sub hτπ_aemeas.aestronglyMeasurable
  have herror_ne_top :
      (∫⁻ x in S,
          ENNReal.ofReal ‖w x - τ (π x)‖
          ∂MeasureTheory.volume) ≠ (⊤ : ℝ≥0∞) := by
    have hscaled_ne_top :
        ENNReal.ofReal (1 / ε) *
          (∫⁻ x in S,
            ENNReal.ofReal ‖w x - τ (π x)‖
            ∂MeasureTheory.volume) ≠ (⊤ : ℝ≥0∞) := by
      simpa [S, π] using ne_of_lt hε_finite
    have hcoef_ne_zero : ENNReal.ofReal (1 / ε) ≠ 0 := by
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (one_div_pos.mpr hε_pos))
    exact
      ne_of_lt
        (ENNReal.lt_top_of_mul_ne_top_right
          hscaled_ne_top hcoef_ne_zero)
  have hdiff_int : Integrable (fun x : H ↦ w x - τ (π x)) μS := by
    refine ⟨hdiff_aemeas, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa [μS] using lt_top_iff_ne_top.2 herror_ne_top
  have hτπ_int :
      Integrable (fun x : H ↦ w x - (w x - τ (π x))) μS :=
    hw_int_S.sub hdiff_int
  refine ⟨ε, hε_pos, hε_lt, ?_⟩
  simpa [π, S, μS, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using hτπ_int

/--
%%handwave
name:
  An interior \(L^1\) trace is integrable on the sphere
statement:
  Let \(w\) be square-integrable in the unit ball and let \(\tau\) be a
  measurable inside \(L^1\)-trace of \(w\) on the unit sphere.  Then
  \(\tau\) is integrable with respect to spherical measure.
proof:
  Choose a sufficiently thin collar for which the normalized trace error is
  finite.  The square-integrability of \(w\) on the finite-measure unit ball
  gives finite \(L^1\)-mass of \(w\) on that collar, so the radial extension
  \(x\mapsto \tau(x/\|x\|)\) also has finite \(L^1\)-mass there.  Polar
  coordinates identify this collar integral with the product of the spherical
  \(L^1\)-mass of \(\tau\) and the positive finite radial measure of the
  collar; hence the spherical \(L^1\)-mass is finite.
-/
theorem euclideanSobolev_unit_ball_integrable_sphere_trace_of_l1_trace_from_inside
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w τ : H → ℝ}
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hτ_meas : Measurable τ)
    (_htrace : HasL1TraceFromInsideSphere (H := H) 1 w τ) :
    Integrable
      (fun θ : Metric.sphere (0 : H) 1 ↦ τ (θ : H))
      ((MeasureTheory.volume : Measure H).toSphere) := by
  rcases
    euclideanSobolev_unit_ball_radial_trace_extension_integrable_on_some_collar
      _hw _hτ_meas _htrace with
    ⟨ε, hε_pos, hε_lt, hcollar⟩
  exact
    euclideanSobolev_unit_ball_integrable_sphere_trace_of_radial_extension_integrable_on_collar
      (H := H) (τ := τ) hε_pos hε_lt _hτ_meas hcollar

/--
%%handwave
name:
  Unit-ball Sobolev functions have an integrable sphere trace
statement:
  A scalar \(W^{1,2}\) function on the unit ball has a measurable
  \(L^1\)-trace representative on the unit sphere that is integrable with
  respect to the spherical measure.
proof:
  First use
  [a scalar \(W^{1,2}\) function on the unit ball has an inside \(L^1\)
  trace](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_has_l1_trace_from_inside_core).
  Then apply
  [an inside \(L^1\) trace of a square-integrable function is integrable on
  the unit sphere](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_integrable_sphere_trace_of_l1_trace_from_inside).
-/
theorem euclideanSobolev_unit_ball_has_integrable_l1_trace_from_inside
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      Integrable
        (fun θ : Metric.sphere (0 : H) 1 ↦ τ (θ : H))
        ((MeasureTheory.volume : Measure H).toSphere) ∧
        Measurable τ ∧
          HasL1TraceFromInsideSphere (H := H) 1 w τ := by
  rcases
    euclideanSobolev_unit_ball_has_l1_trace_from_inside_core
      _hweak _hw _hdw with
    ⟨τ, hτ_meas, htrace⟩
  exact
    ⟨τ,
      euclideanSobolev_unit_ball_integrable_sphere_trace_of_l1_trace_from_inside
        _hw hτ_meas htrace,
      hτ_meas, htrace⟩

/--
%%handwave
name:
  The reflected unit-ball trace has integrable weighted pairings
statement:
  For a scalar Sobolev function on the unit ball, the common \(L^1\) trace of
  the function and its tapered radial reflection has integrable pairing
  against every fixed smooth ambient test function and every normal component
  on the unit sphere.
proof:
  The unit-ball trace is \(L^1\) on the sphere.  A fixed smooth ambient test
  function and a fixed normal component are bounded on the compact unit
  sphere, so multiplying the trace by this bounded weight preserves
  integrability.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_inner_trace_weighted_integrable
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (_hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ τ : H → ℝ,
      (∀
        (φ : SmoothCompactlySupportedManifoldCoordinateFunction
          (Set.univ : Set H))
        (v : H),
        EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) ∧
        HasL1TraceFromInsideSphere (H := H) 1 w τ ∧
          HasL1TraceFromOutsideSphere (H := H) 1
            (fun x : H ↦
              (3 - 2 * ‖x‖) *
                w (euclideanSobolevUnitBallRadialReflection x))
            τ := by
  rcases
    euclideanSobolev_unit_ball_has_integrable_l1_trace_from_inside
      _hweak _hw _hdw with
    ⟨τ, hτ_int, hτ_meas, htrace_inner⟩
  have htrace_outer :
      HasL1TraceFromOutsideSphere (H := H) 1
        (fun x : H ↦
          (3 - 2 * ‖x‖) *
            w (euclideanSobolevUnitBallRadialReflection x))
        τ :=
    hasL1TraceFromOutsideSphere_unit_radial_reflection_taper_of_inside
      _hw hτ_meas htrace_inner
  refine ⟨τ, ?_, htrace_inner, htrace_outer⟩
  intro φ v
  exact
    euclideanSobolev_unit_sphere_weighted_trace_integrable_of_trace_integrable
      (τ := τ) φ v hτ_int

private def sphereInnerL1TraceError
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (r : ℝ) (u τ : H → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / ε) *
    ∫⁻ x in {x : H | r - ε < ‖x‖ ∧ ‖x‖ < r},
      ENNReal.ofReal ‖u x - τ (((r / ‖x‖) : ℝ) • x)‖
        ∂MeasureTheory.volume

private def sphereOuterL1TraceError
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (r : ℝ) (u τ : H → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / ε) *
    ∫⁻ x in {x : H | r < ‖x‖ ∧ ‖x‖ < r + ε},
      ENNReal.ofReal ‖u x - τ (((r / ‖x‖) : ℝ) • x)‖
        ∂MeasureTheory.volume

private theorem radialProjection_mem_sphere_of_pos
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {r : ℝ} (hr_pos : 0 < r) {z : H} (hz : z ≠ 0) :
    (((r / ‖z‖) : ℝ) • z) ∈ Metric.sphere (0 : H) r := by
  have hz_norm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hcoef_nonneg : 0 ≤ r / ‖z‖ :=
    div_nonneg hr_pos.le hz_norm_pos.le
  have hnorm :
      ‖((r / ‖z‖ : ℝ) • z)‖ = r := by
    calc
      ‖((r / ‖z‖ : ℝ) • z)‖
          = ‖(r / ‖z‖ : ℝ)‖ * ‖z‖ := norm_smul _ _
      _ = (r / ‖z‖) * ‖z‖ := by rw [Real.norm_of_nonneg hcoef_nonneg]
      _ = r := by field_simp [hz_norm_pos.ne']
  rw [Metric.mem_sphere, dist_eq_norm]
  simp [hnorm]

private theorem radialUnitProjection_mem_unit_sphere
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {z : H} (hz : z ≠ 0) :
    (((1 / ‖z‖) : ℝ) • z) ∈ Metric.sphere (0 : H) 1 := by
  simpa using
    (radialProjection_mem_sphere_of_pos
      (H := H) (r := (1 : ℝ)) (by norm_num) hz)

private theorem invNorm_smul_mem_unit_sphere
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {z : H} (hz : z ≠ 0) :
    ((‖z‖)⁻¹ • z) ∈ Metric.sphere (0 : H) 1 := by
  simpa [one_div] using
    (radialUnitProjection_mem_unit_sphere (H := H) hz)

/--
%%handwave
name:
  A small collar width has small total trace error
statement:
  If the two functions have matching \(L^1\)-traces on the unit sphere and
  the annular function has zero \(L^1\)-trace on the sphere of radius
  \(3/2\), then for every positive tolerance there is a positive collar width
  below that tolerance for which the sum of the three normalized trace errors
  is below the tolerance.
proof:
  The three normalized trace errors tend to zero by hypothesis, so their sum
  also tends to zero.  Intersect the resulting eventual smallness with the
  punctured neighborhood condition \(0<\varepsilon<\eta\) and choose one
  admissible width.
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_exists_width_trace_errors_small
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    {η : ℝ} (hη_pos : 0 < η) :
    ∃ width : ℝ,
      0 < width ∧
      width ≤ η ∧
      width ≤ (1 / 4 : ℝ) ∧
      sphereInnerL1TraceError (H := H) 1 u₀ τ width +
          sphereOuterL1TraceError (H := H) 1 u₁ τ width +
            sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
              u₁ (fun _x : H ↦ 0) width ≤
        ENNReal.ofReal η := by
  have hinner₀' :
      Filter.Tendsto
        (fun ε : ℝ ↦ sphereInnerL1TraceError (H := H) 1 u₀ τ ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [sphereInnerL1TraceError, HasL1TraceFromInsideSphere] using hinner₀
  have hinner₁' :
      Filter.Tendsto
        (fun ε : ℝ ↦ sphereOuterL1TraceError (H := H) 1 u₁ τ ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [sphereOuterL1TraceError, HasL1TraceFromOutsideSphere] using hinner₁
  have houter' :
      Filter.Tendsto
        (fun ε : ℝ ↦
          sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
            u₁ (fun _x : H ↦ 0) ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [sphereInnerL1TraceError, HasL1TraceFromInsideSphere] using houter
  have hsum :
      Filter.Tendsto
        (fun ε : ℝ ↦
          sphereInnerL1TraceError (H := H) 1 u₀ τ ε +
            sphereOuterL1TraceError (H := H) 1 u₁ τ ε +
              sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                u₁ (fun _x : H ↦ 0) ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa [zero_add] using (hinner₀'.add hinner₁').add houter'
  have hη_enn_pos : (0 : ℝ≥0∞) < ENNReal.ofReal η :=
    ENNReal.ofReal_pos.mpr hη_pos
  have hsmall_error :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        sphereInnerL1TraceError (H := H) 1 u₀ τ ε +
            sphereOuterL1TraceError (H := H) 1 u₁ τ ε +
              sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                u₁ (fun _x : H ↦ 0) ε <
          ENNReal.ofReal η :=
    hsum.eventually (Iio_mem_nhds hη_enn_pos)
  have hsmall_width : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < η :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hη_pos)
  have hsmall_width_quarter : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < (1 / 4 : ℝ) := by
    exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hchoose :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        0 < ε ∧
          ε ≤ η ∧
            ε ≤ (1 / 4 : ℝ) ∧
              sphereInnerL1TraceError (H := H) 1 u₀ τ ε +
                sphereOuterL1TraceError (H := H) 1 u₁ τ ε +
                  sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                    u₁ (fun _x : H ↦ 0) ε ≤
              ENNReal.ofReal η := by
    filter_upwards [self_mem_nhdsWithin, hsmall_width, hsmall_width_quarter,
      hsmall_error] with ε hε_pos hε_lt hε_quarter hε_error
    exact ⟨hε_pos, hε_lt.le, hε_quarter.le, hε_error.le⟩
  rcases hchoose.exists with
    ⟨width, hwidth_pos, hwidth_le, hwidth_quarter, htrace⟩
  exact ⟨width, hwidth_pos, hwidth_le, hwidth_quarter, htrace⟩

/--
The standard fixed-width pair of smooth collar cutoffs for the unit ball and
the reflection annulus.
-/
structure EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (width : ℝ) where
  unitCutoff : H → ℝ
  annulusCutoff : H → ℝ
  radial_profiles :
    ∃ unitProfile annulusProfile : ℝ → ℝ,
      ContDiff ℝ ∞ unitProfile ∧
        ContDiff ℝ ∞ annulusProfile ∧
          (∀ x : H, unitCutoff x = unitProfile ‖x‖) ∧
            (∀ x : H, annulusCutoff x = annulusProfile ‖x‖)
  unitCutoff_eq_standard :
    ∀ x : H,
      unitCutoff x =
        Real.smoothTransition (((1 : ℝ) - width / 2 - ‖x‖) / (width / 4))
  annulusCutoff_eq_standard :
    ∀ x : H,
      annulusCutoff x =
        Real.smoothTransition ((‖x‖ - ((1 : ℝ) + width / 2)) / (width / 4)) *
          Real.smoothTransition
            ((((3 / 2 : ℝ) - width / 2) - ‖x‖) / (width / 4))
  unitCutoff_smooth : ContDiff ℝ ∞ unitCutoff
  annulusCutoff_smooth : ContDiff ℝ ∞ annulusCutoff
  unitCutoff_tsupport_subset :
    tsupport unitCutoff ⊆ Metric.ball (0 : H) 1
  annulusCutoff_tsupport_subset :
    tsupport annulusCutoff ⊆
      euclideanSobolevUnitBallReflectionAnnulus H
  unitCutoff_compact_support : IsCompact (tsupport unitCutoff)
  annulusCutoff_compact_support : IsCompact (tsupport annulusCutoff)
  unitCutoff_norm_le_one : ∀ x : H, ‖unitCutoff x‖ ≤ (1 : ℝ)
  annulusCutoff_norm_le_one : ∀ x : H, ‖annulusCutoff x‖ ≤ (1 : ℝ)
  unitCutoff_eq_one_on_core :
    ∀ x : H, ‖x‖ ≤ 1 - width → unitCutoff x = 1
  annulusCutoff_eq_one_on_core :
    ∀ x : H, 1 + width ≤ ‖x‖ →
      ‖x‖ ≤ (3 / 2 : ℝ) - width → annulusCutoff x = 1
  unitCutoff_fderiv_eq_zero_on_core :
    ∀ x : H, ‖x‖ ≤ 1 - width → fderiv ℝ unitCutoff x = 0
  annulusCutoff_fderiv_eq_zero_on_core :
    ∀ x : H, 1 + width ≤ ‖x‖ →
      ‖x‖ ≤ (3 / 2 : ℝ) - width → fderiv ℝ annulusCutoff x = 0

private def euclideanSobolevUnitBallInnerTransitionCollar
    (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (width : ℝ) : Set H :=
  {z : H | 1 - width < ‖z‖ ∧ ‖z‖ < 1}

private def euclideanSobolevUnitBallAnnulusInnerTransitionCollar
    (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (width : ℝ) : Set H :=
  {z : H | 1 < ‖z‖ ∧ ‖z‖ < 1 + width}

private def euclideanSobolevUnitBallAnnulusOuterTransitionCollar
    (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (width : ℝ) : Set H :=
  {z : H | (3 / 2 : ℝ) - width < ‖z‖ ∧ ‖z‖ < (3 / 2 : ℝ)}

private theorem euclideanSobolevUnitBallInnerTransitionCollar_isOpen
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (width : ℝ) :
    IsOpen (euclideanSobolevUnitBallInnerTransitionCollar H width) := by
  dsimp [euclideanSobolevUnitBallInnerTransitionCollar]
  exact
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)

private theorem euclideanSobolevUnitBallAnnulusInnerTransitionCollar_isOpen
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (width : ℝ) :
    IsOpen (euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width) := by
  dsimp [euclideanSobolevUnitBallAnnulusInnerTransitionCollar]
  exact
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)

private theorem euclideanSobolevUnitBallAnnulusOuterTransitionCollar_isOpen
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (width : ℝ) :
    IsOpen (euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width) := by
  dsimp [euclideanSobolevUnitBallAnnulusOuterTransitionCollar]
  exact
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)

private theorem euclideanSobolevUnitBallAnnulusTransitionCollars_disjoint
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {width : ℝ} (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) :
    Disjoint
      (euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width)
      (euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width) := by
  rw [Set.disjoint_left]
  intro z hinner houter
  nlinarith [hwidth_le_quarter, hinner.2, houter.1]

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.unit_fderiv_eq_zero_of_notMem_inner_transition_collar
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {width : ℝ}
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    {z : H}
    (hz : z ∉ euclideanSobolevUnitBallInnerTransitionCollar H width) :
    fderiv ℝ χ.unitCutoff z = 0 := by
  classical
  by_cases hcore : ‖z‖ ≤ 1 - width
  · exact χ.unitCutoff_fderiv_eq_zero_on_core z hcore
  · have hgt : 1 - width < ‖z‖ := lt_of_not_ge hcore
    have hnot_lt_one : ¬ ‖z‖ < (1 : ℝ) := by
      intro hlt
      exact hz ⟨hgt, hlt⟩
    have hnot_tsupport : z ∉ tsupport χ.unitCutoff := by
      intro hzts
      have hzball := χ.unitCutoff_tsupport_subset hzts
      have hlt : ‖z‖ < (1 : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm] using hzball
      exact hnot_lt_one hlt
    exact fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := χ.unitCutoff) hnot_tsupport

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.annulus_fderiv_eq_zero_of_notMem_transition_collars
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {width : ℝ}
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    {z : H}
    (hz :
      z ∉
        euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
          euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width) :
    fderiv ℝ χ.annulusCutoff z = 0 := by
  classical
  by_cases hA : 1 < ‖z‖ ∧ ‖z‖ < (3 / 2 : ℝ)
  · have hnot_inner :
        z ∉ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width := by
      intro hinner
      exact hz (Or.inl hinner)
    have hnot_outer :
        z ∉ euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width := by
      intro houter
      exact hz (Or.inr houter)
    have hge : 1 + width ≤ ‖z‖ := by
      by_contra hnot
      have hlt : ‖z‖ < 1 + width := lt_of_not_ge hnot
      exact hnot_inner ⟨hA.1, hlt⟩
    have hle : ‖z‖ ≤ (3 / 2 : ℝ) - width := by
      by_contra hnot
      have hgt : (3 / 2 : ℝ) - width < ‖z‖ := lt_of_not_ge hnot
      exact hnot_outer ⟨hgt, hA.2⟩
    exact χ.annulusCutoff_fderiv_eq_zero_on_core z hge hle
  · have hnot_tsupport : z ∉ tsupport χ.annulusCutoff := by
      intro hzts
      have hzann := χ.annulusCutoff_tsupport_subset hzts
      have hA' : 1 < ‖z‖ ∧ ‖z‖ < (3 / 2 : ℝ) := by
        simpa [euclideanSobolevUnitBallReflectionAnnulus] using hzann
      exact hA hA'
    exact fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := χ.annulusCutoff) hnot_tsupport

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.unit_derivative_pairing_eq_inner_transition_collar
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    {width : ℝ}
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    (u φ : H → ℝ) (v : H) :
    (∫ z in Metric.ball (0 : H) 1,
        ((fderiv ℝ χ.unitCutoff z v) * φ z) • u z
        ∂MeasureTheory.volume) =
      ∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
        ((fderiv ℝ χ.unitCutoff z v) * φ z) • u z
        ∂MeasureTheory.volume := by
  let F : H → ℝ :=
    fun z ↦ ((fderiv ℝ χ.unitCutoff z v) * φ z) • u z
  have hzero_ball : ∀ z ∉ Metric.ball (0 : H) 1, F z = 0 := by
    intro z hzball
    have hnot_collar :
        z ∉ euclideanSobolevUnitBallInnerTransitionCollar H width := by
      intro hzcollar
      exact hzball (by
        simpa [Metric.mem_ball, dist_eq_norm] using hzcollar.2)
    have hD :
        fderiv ℝ χ.unitCutoff z = 0 :=
      χ.unit_fderiv_eq_zero_of_notMem_inner_transition_collar hnot_collar
    simp [F, hD]
  have hzero_collar :
      ∀ z ∉ euclideanSobolevUnitBallInnerTransitionCollar H width,
        F z = 0 := by
    intro z hzcollar
    have hD :
        fderiv ℝ χ.unitCutoff z = 0 :=
      χ.unit_fderiv_eq_zero_of_notMem_inner_transition_collar hzcollar
    simp [F, hD]
  change
    (∫ z in Metric.ball (0 : H) 1, F z ∂MeasureTheory.volume) =
      ∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
        F z ∂MeasureTheory.volume
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero_ball,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero_collar]

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.annulus_derivative_pairing_eq_transition_collars
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    {width : ℝ}
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    (u φ : H → ℝ) (v : H) :
    (∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
        ((fderiv ℝ χ.annulusCutoff z v) * φ z) • u z
        ∂MeasureTheory.volume) =
      ∫ z in
        euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
          euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
        ((fderiv ℝ χ.annulusCutoff z v) * φ z) • u z
        ∂MeasureTheory.volume := by
  let F : H → ℝ :=
    fun z ↦ ((fderiv ℝ χ.annulusCutoff z v) * φ z) • u z
  have hzero_annulus :
      ∀ z ∉ euclideanSobolevUnitBallReflectionAnnulus H, F z = 0 := by
    intro z hzann
    have hnot_tsupport : z ∉ tsupport χ.annulusCutoff := by
      intro hzts
      exact hzann (χ.annulusCutoff_tsupport_subset hzts)
    have hD :
        fderiv ℝ χ.annulusCutoff z = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := χ.annulusCutoff)
        hnot_tsupport
    simp [F, hD]
  have hzero_collars :
      ∀ z ∉
        euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
          euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
        F z = 0 := by
    intro z hzcollars
    have hD :
        fderiv ℝ χ.annulusCutoff z = 0 :=
      χ.annulus_fderiv_eq_zero_of_notMem_transition_collars hzcollars
    simp [F, hD]
  change
    (∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
        F z ∂MeasureTheory.volume) =
      ∫ z in
        euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
          euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
        F z ∂MeasureTheory.volume
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero_annulus,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero_collars]

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.derivative_pairing_sum_eq_transition_collar_pairing_sum
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H]
    {width : ℝ}
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    (u₀ u₁ φ : H → ℝ) (v : H) :
    (∫ z in Metric.ball (0 : H) 1,
        ((fderiv ℝ χ.unitCutoff z v) * φ z) • u₀ z
        ∂MeasureTheory.volume) +
      ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
        ((fderiv ℝ χ.annulusCutoff z v) * φ z) • u₁ z
        ∂MeasureTheory.volume =
    (∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
        ((fderiv ℝ χ.unitCutoff z v) * φ z) • u₀ z
        ∂MeasureTheory.volume) +
      ∫ z in
        euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
          euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
        ((fderiv ℝ χ.annulusCutoff z v) * φ z) • u₁ z
        ∂MeasureTheory.volume := by
  rw [χ.unit_derivative_pairing_eq_inner_transition_collar u₀ φ v,
    χ.annulus_derivative_pairing_eq_transition_collars u₁ φ v]

private theorem exists_smoothTransition_deriv_bound_Icc_neg_two_two :
    ∃ C : ℝ,
      1 ≤ C ∧
        ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
          ‖deriv Real.smoothTransition t‖ ≤ C := by
  have hsmooth : ContDiff ℝ ∞ Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have hcont :
      Continuous (fun t : ℝ ↦ deriv Real.smoothTransition t) :=
    hsmooth.continuous_deriv (by simp)
  rcases
      (isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn) with
    ⟨C₀, hC₀⟩
  refine ⟨max C₀ 1, le_max_right C₀ 1, ?_⟩
  intro t ht
  exact (hC₀ t ht).trans (le_max_left C₀ 1)

private theorem deriv_smoothTransition_eq_zero_of_lt_zero {x : ℝ}
    (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ ↦ (0 : ℝ) :=
    Filter.Eventually.mono (Iio_mem_nhds hx) fun y hy ↦
      Real.smoothTransition.zero_of_nonpos hy.le
  rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]

private theorem deriv_smoothTransition_eq_zero_of_one_lt {x : ℝ}
    (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ ↦ (1 : ℝ) :=
    Filter.Eventually.mono (Ioi_mem_nhds hx) fun y hy ↦
      Real.smoothTransition.one_of_one_le hy.le
  rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]

private theorem unit_inner_transition_arg_mem_Icc_neg_two_two
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {width : ℝ} (hwidth_pos : 0 < width) {z : H}
    (hz : z ∈ euclideanSobolevUnitBallInnerTransitionCollar H width) :
    (((1 : ℝ) - width / 2 - ‖z‖) / (width / 4)) ∈
      Set.Icc (-(2 : ℝ)) 2 := by
  have hden : 0 < width / 4 := by linarith
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith [hz.2.le]
  · rw [div_le_iff₀ hden]
    nlinarith [hz.1.le]

private theorem annulus_inner_transition_arg_mem_Icc_neg_two_two
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {width : ℝ} (hwidth_pos : 0 < width) {z : H}
    (hz :
      z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width) :
    ((‖z‖ - ((1 : ℝ) + width / 2)) / (width / 4)) ∈
      Set.Icc (-(2 : ℝ)) 2 := by
  have hden : 0 < width / 4 := by linarith
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith [hz.1.le]
  · rw [div_le_iff₀ hden]
    nlinarith [hz.2.le]

private theorem annulus_outer_transition_arg_mem_Icc_neg_two_two
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {width : ℝ} (hwidth_pos : 0 < width) {z : H}
    (hz :
      z ∈ euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width) :
    ((((3 / 2 : ℝ) - width / 2) - ‖z‖) / (width / 4)) ∈
      Set.Icc (-(2 : ℝ)) 2 := by
  have hden : 0 < width / 4 := by linarith
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith [hz.2.le]
  · rw [div_le_iff₀ hden]
    nlinarith [hz.1.le]

private theorem annulus_outer_transition_arg_gt_one_of_inner_transition
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {width : ℝ} (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) {z : H}
    (hz :
      z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width) :
    1 <
      ((((3 / 2 : ℝ) - width / 2) - ‖z‖) / (width / 4)) := by
  have hden : 0 < width / 4 := by linarith
  rw [one_lt_div hden]
  nlinarith [hz.2, hwidth_le_quarter]

private theorem annulus_inner_transition_arg_gt_one_of_outer_transition
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {width : ℝ} (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) {z : H}
    (hz :
      z ∈ euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width) :
    1 <
      ((‖z‖ - ((1 : ℝ) + width / 2)) / (width / 4)) := by
  have hden : 0 < width / 4 := by linarith
  rw [one_lt_div hden]
  nlinarith [hz.1, hwidth_le_quarter]

private theorem unit_inner_transition_profile_deriv_eq
    {width r : ℝ} :
    deriv
        (fun s : ℝ ↦
          Real.smoothTransition (((1 : ℝ) - width / 2 - s) / (width / 4)))
        r =
      deriv Real.smoothTransition
          (((1 : ℝ) - width / 2 - r) / (width / 4)) *
        (-(1 : ℝ) / (width / 4)) := by
  have harg_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦ (((1 : ℝ) - width / 2 - s) / (width / 4))) r := by
    fun_prop
  have hs_diff :
      DifferentiableAt ℝ Real.smoothTransition
        (((1 : ℝ) - width / 2 - r) / (width / 4)) :=
    ((Real.smoothTransition.contDiff :
        ContDiff ℝ (1 : WithTop ℕ∞) Real.smoothTransition).differentiable
      (by norm_num)) _
  have hderiv_arg :
      deriv (fun s : ℝ ↦ (((1 : ℝ) - width / 2 - s) / (width / 4))) r =
        -(1 : ℝ) / (width / 4) := by
    rw [deriv_div_const, deriv_const_sub]
    simp
  simpa [Function.comp_def, hderiv_arg] using
    deriv_comp r hs_diff harg_diff

private theorem annulus_inner_transition_profile_deriv_eq
    {width r : ℝ} :
    deriv
        (fun s : ℝ ↦
          Real.smoothTransition ((s - ((1 : ℝ) + width / 2)) / (width / 4)))
        r =
      deriv Real.smoothTransition
          ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
        ((1 : ℝ) / (width / 4)) := by
  have harg_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦ ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r := by
    fun_prop
  have hs_diff :
      DifferentiableAt ℝ Real.smoothTransition
        ((r - ((1 : ℝ) + width / 2)) / (width / 4)) :=
    ((Real.smoothTransition.contDiff :
        ContDiff ℝ (1 : WithTop ℕ∞) Real.smoothTransition).differentiable
      (by norm_num)) _
  have hderiv_arg :
      deriv
          (fun s : ℝ ↦ ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r =
        (1 : ℝ) / (width / 4) := by
    rw [deriv_div_const]
    simp
  simpa [Function.comp_def, hderiv_arg] using
    deriv_comp r hs_diff harg_diff

private theorem annulus_outer_transition_profile_deriv_eq
    {width r : ℝ} :
    deriv
        (fun s : ℝ ↦
          Real.smoothTransition
            ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4)))
        r =
      deriv Real.smoothTransition
          ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)) *
        (-(1 : ℝ) / (width / 4)) := by
  have harg_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦
          ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r := by
    fun_prop
  have hs_diff :
      DifferentiableAt ℝ Real.smoothTransition
        ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)) :=
    ((Real.smoothTransition.contDiff :
        ContDiff ℝ (1 : WithTop ℕ∞) Real.smoothTransition).differentiable
      (by norm_num)) _
  have hderiv_arg :
      deriv
          (fun s : ℝ ↦
            ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r =
        -(1 : ℝ) / (width / 4) := by
    rw [deriv_div_const, deriv_const_sub]
    simp
  simpa [Function.comp_def, hderiv_arg] using
    deriv_comp r hs_diff harg_diff

private theorem annulus_transition_product_profile_deriv_eq_of_inner_collar
    {width r : ℝ} (_hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    (hr : 1 < r ∧ r < 1 + width) :
    deriv
        (fun s : ℝ ↦
          Real.smoothTransition ((s - ((1 : ℝ) + width / 2)) / (width / 4)) *
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4)))
        r =
      deriv Real.smoothTransition
          ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
        ((1 : ℝ) / (width / 4)) := by
  have hden : 0 < width / 4 := by linarith
  have houter_arg_gt :
      1 < ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)) := by
    rw [one_lt_div hden]
    nlinarith [hr.2, hwidth_le_quarter]
  have houter_one :
      Real.smoothTransition
        ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)) = 1 :=
    Real.smoothTransition.one_of_one_le houter_arg_gt.le
  have houter_zero :
      deriv
          (fun s : ℝ ↦
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r = 0 := by
    rw [annulus_outer_transition_profile_deriv_eq,
      deriv_smoothTransition_eq_zero_of_one_lt houter_arg_gt]
    simp
  have hinner_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦
          Real.smoothTransition
            ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r := by
    fun_prop
  have houter_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦
          Real.smoothTransition
            ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r := by
    fun_prop
  have hprod := deriv_mul hinner_diff houter_diff
  have hinner_deriv :=
    annulus_inner_transition_profile_deriv_eq (width := width) (r := r)
  change
    deriv
        ((fun s : ℝ ↦
          Real.smoothTransition ((s - ((1 : ℝ) + width / 2)) / (width / 4))) *
          fun s : ℝ ↦
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4)))
        r =
      deriv Real.smoothTransition
          ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
        ((1 : ℝ) / (width / 4))
  rw [hprod, houter_one, houter_zero, hinner_deriv]
  ring

private theorem annulus_transition_product_profile_deriv_eq_of_outer_collar
    {width r : ℝ} (_hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    (hr : (3 / 2 : ℝ) - width < r ∧ r < (3 / 2 : ℝ)) :
    deriv
        (fun s : ℝ ↦
          Real.smoothTransition ((s - ((1 : ℝ) + width / 2)) / (width / 4)) *
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4)))
        r =
      deriv Real.smoothTransition
          ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)) *
        (-(1 : ℝ) / (width / 4)) := by
  have hden : 0 < width / 4 := by linarith
  have hinner_arg_gt :
      1 < ((r - ((1 : ℝ) + width / 2)) / (width / 4)) := by
    rw [one_lt_div hden]
    nlinarith [hr.1, hwidth_le_quarter]
  have hinner_one :
      Real.smoothTransition
        ((r - ((1 : ℝ) + width / 2)) / (width / 4)) = 1 :=
    Real.smoothTransition.one_of_one_le hinner_arg_gt.le
  have hinner_zero :
      deriv
          (fun s : ℝ ↦
            Real.smoothTransition
              ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r = 0 := by
    rw [annulus_inner_transition_profile_deriv_eq,
      deriv_smoothTransition_eq_zero_of_one_lt hinner_arg_gt]
    simp
  have hinner_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦
          Real.smoothTransition
            ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r := by
    fun_prop
  have houter_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦
          Real.smoothTransition
            ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r := by
    fun_prop
  have hprod := deriv_mul hinner_diff houter_diff
  have houter_deriv :=
    annulus_outer_transition_profile_deriv_eq (width := width) (r := r)
  change
    deriv
        ((fun s : ℝ ↦
          Real.smoothTransition ((s - ((1 : ℝ) + width / 2)) / (width / 4))) *
          fun s : ℝ ↦
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4)))
        r =
      deriv Real.smoothTransition
          ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)) *
        (-(1 : ℝ) / (width / 4))
  rw [hprod, hinner_zero, hinner_one, houter_deriv]
  ring

private theorem unit_inner_transition_profile_deriv_norm_le
    {width C r : ℝ} (hwidth_pos : 0 < width)
    (hC : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ C)
    (hr :
      (((1 : ℝ) - width / 2 - r) / (width / 4)) ∈
        Set.Icc (-(2 : ℝ)) 2) :
    ‖deriv
        (fun s : ℝ ↦
          Real.smoothTransition (((1 : ℝ) - width / 2 - s) / (width / 4)))
        r‖ ≤ C * (4 / width) := by
  have harg_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦ (((1 : ℝ) - width / 2 - s) / (width / 4))) r := by
    fun_prop
  have hs_diff :
      DifferentiableAt ℝ Real.smoothTransition
        (((1 : ℝ) - width / 2 - r) / (width / 4)) :=
    ((Real.smoothTransition.contDiff :
        ContDiff ℝ (1 : WithTop ℕ∞) Real.smoothTransition).differentiable
      (by norm_num)) _
  have hderiv_arg :
      deriv (fun s : ℝ ↦ (((1 : ℝ) - width / 2 - s) / (width / 4))) r =
        -(1 : ℝ) / (width / 4) := by
    rw [deriv_div_const, deriv_const_sub]
    simp
  have hderiv :
      deriv
          (fun s : ℝ ↦
            Real.smoothTransition
              (((1 : ℝ) - width / 2 - s) / (width / 4))) r =
        deriv Real.smoothTransition
            (((1 : ℝ) - width / 2 - r) / (width / 4)) *
          (-(1 : ℝ) / (width / 4)) := by
    simpa [Function.comp_def, hderiv_arg] using
      deriv_comp r hs_diff harg_diff
  have hscale : ‖-(1 : ℝ) / (width / 4)‖ = 4 / width := by
    rw [norm_div, norm_neg, norm_one,
      Real.norm_of_nonneg (by linarith : 0 ≤ width / 4)]
    field_simp [hwidth_pos.ne']
  calc
    ‖deriv
        (fun s : ℝ ↦
          Real.smoothTransition (((1 : ℝ) - width / 2 - s) / (width / 4)))
        r‖
        =
          ‖deriv Real.smoothTransition
              (((1 : ℝ) - width / 2 - r) / (width / 4)) *
            (-(1 : ℝ) / (width / 4))‖ := by
            rw [hderiv]
    _ =
          ‖deriv Real.smoothTransition
              (((1 : ℝ) - width / 2 - r) / (width / 4))‖ *
            ‖-(1 : ℝ) / (width / 4)‖ := norm_mul _ _
    _ ≤ C * ‖-(1 : ℝ) / (width / 4)‖ :=
          mul_le_mul_of_nonneg_right (hC _ hr) (norm_nonneg _)
    _ = C * (4 / width) := by rw [hscale]

private theorem annulus_inner_transition_profile_deriv_norm_le
    {width C r : ℝ} (hwidth_pos : 0 < width)
    (hC : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ C)
    (hr :
      ((r - ((1 : ℝ) + width / 2)) / (width / 4)) ∈
        Set.Icc (-(2 : ℝ)) 2) :
    ‖deriv
        (fun s : ℝ ↦
          Real.smoothTransition ((s - ((1 : ℝ) + width / 2)) / (width / 4)))
        r‖ ≤ C * (4 / width) := by
  have harg_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦ ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r := by
    fun_prop
  have hs_diff :
      DifferentiableAt ℝ Real.smoothTransition
        ((r - ((1 : ℝ) + width / 2)) / (width / 4)) :=
    ((Real.smoothTransition.contDiff :
        ContDiff ℝ (1 : WithTop ℕ∞) Real.smoothTransition).differentiable
      (by norm_num)) _
  have hderiv_arg :
      deriv
          (fun s : ℝ ↦ ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r =
        (1 : ℝ) / (width / 4) := by
    rw [deriv_div_const]
    simp
  have hderiv :
      deriv
          (fun s : ℝ ↦
            Real.smoothTransition
              ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r =
        deriv Real.smoothTransition
            ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
          ((1 : ℝ) / (width / 4)) := by
    simpa [Function.comp_def, hderiv_arg] using
      deriv_comp r hs_diff harg_diff
  have hscale : ‖(1 : ℝ) / (width / 4)‖ = 4 / width := by
    rw [norm_div, norm_one,
      Real.norm_of_nonneg (by linarith : 0 ≤ width / 4)]
    field_simp [hwidth_pos.ne']
  calc
    ‖deriv
        (fun s : ℝ ↦
          Real.smoothTransition ((s - ((1 : ℝ) + width / 2)) / (width / 4)))
        r‖
        =
          ‖deriv Real.smoothTransition
              ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
            ((1 : ℝ) / (width / 4))‖ := by
            rw [hderiv]
    _ =
          ‖deriv Real.smoothTransition
              ((r - ((1 : ℝ) + width / 2)) / (width / 4))‖ *
            ‖(1 : ℝ) / (width / 4)‖ := norm_mul _ _
    _ ≤ C * ‖(1 : ℝ) / (width / 4)‖ :=
          mul_le_mul_of_nonneg_right (hC _ hr) (norm_nonneg _)
    _ = C * (4 / width) := by rw [hscale]

private theorem annulus_outer_transition_profile_deriv_norm_le
    {width C r : ℝ} (hwidth_pos : 0 < width)
    (hC : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ C)
    (hr :
      ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)) ∈
        Set.Icc (-(2 : ℝ)) 2) :
    ‖deriv
        (fun s : ℝ ↦
          Real.smoothTransition
            ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4)))
        r‖ ≤ C * (4 / width) := by
  have harg_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦
          ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r := by
    fun_prop
  have hs_diff :
      DifferentiableAt ℝ Real.smoothTransition
        ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)) :=
    ((Real.smoothTransition.contDiff :
        ContDiff ℝ (1 : WithTop ℕ∞) Real.smoothTransition).differentiable
      (by norm_num)) _
  have hderiv_arg :
      deriv
          (fun s : ℝ ↦
            ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r =
        -(1 : ℝ) / (width / 4) := by
    rw [deriv_div_const, deriv_const_sub]
    simp
  have hderiv :
      deriv
          (fun s : ℝ ↦
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r =
        deriv Real.smoothTransition
            ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)) *
          (-(1 : ℝ) / (width / 4)) := by
    simpa [Function.comp_def, hderiv_arg] using
      deriv_comp r hs_diff harg_diff
  have hscale : ‖-(1 : ℝ) / (width / 4)‖ = 4 / width := by
    rw [norm_div, norm_neg, norm_one,
      Real.norm_of_nonneg (by linarith : 0 ≤ width / 4)]
    field_simp [hwidth_pos.ne']
  calc
    ‖deriv
        (fun s : ℝ ↦
          Real.smoothTransition
            ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4)))
        r‖
        =
          ‖deriv Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)) *
            (-(1 : ℝ) / (width / 4))‖ := by
            rw [hderiv]
    _ =
          ‖deriv Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4))‖ *
            ‖-(1 : ℝ) / (width / 4)‖ := norm_mul _ _
    _ ≤ C * ‖-(1 : ℝ) / (width / 4)‖ :=
          mul_le_mul_of_nonneg_right (hC _ hr) (norm_nonneg _)
    _ = C * (4 / width) := by rw [hscale]

private theorem annulus_transition_product_profile_deriv_norm_le_of_inner_collar
    {width C r : ℝ} (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    (hC_ge_one : 1 ≤ C)
    (hC : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ C)
    (hr : 1 < r ∧ r < 1 + width) :
    ‖deriv
        (fun s : ℝ ↦
          Real.smoothTransition ((s - ((1 : ℝ) + width / 2)) / (width / 4)) *
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4)))
        r‖ ≤ C * (4 / width) := by
  have hden : 0 < width / 4 := by linarith
  have hinner_arg :
      ((r - ((1 : ℝ) + width / 2)) / (width / 4)) ∈
        Set.Icc (-(2 : ℝ)) 2 := by
    constructor
    · rw [le_div_iff₀ hden]
      nlinarith [hr.1.le]
    · rw [div_le_iff₀ hden]
      nlinarith [hr.2.le]
  have houter_arg_gt :
      1 < ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)) := by
    rw [one_lt_div hden]
    nlinarith [hr.2, hwidth_le_quarter]
  have hinner_bound :
      ‖deriv
          (fun s : ℝ ↦
            Real.smoothTransition
              ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r‖ ≤
        C * (4 / width) :=
    annulus_inner_transition_profile_deriv_norm_le hwidth_pos hC hinner_arg
  have houter_arg_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦
          ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r := by
    fun_prop
  have hs_diff :
      DifferentiableAt ℝ Real.smoothTransition
        ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)) :=
    ((Real.smoothTransition.contDiff :
        ContDiff ℝ (1 : WithTop ℕ∞) Real.smoothTransition).differentiable
      (by norm_num)) _
  have houter_deriv_arg :
      deriv
          (fun s : ℝ ↦
            ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r =
        -(1 : ℝ) / (width / 4) := by
    rw [deriv_div_const, deriv_const_sub]
    simp
  have houter_deriv :
      deriv
          (fun s : ℝ ↦
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r =
        deriv Real.smoothTransition
            ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)) *
          (-(1 : ℝ) / (width / 4)) := by
    simpa [Function.comp_def, houter_deriv_arg] using
      deriv_comp r hs_diff houter_arg_diff
  have houter_zero :
      deriv
          (fun s : ℝ ↦
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r = 0 := by
    rw [houter_deriv,
      deriv_smoothTransition_eq_zero_of_one_lt houter_arg_gt]
    simp
  have hinner_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦
          Real.smoothTransition
            ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r := by
    fun_prop
  have houter_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦
          Real.smoothTransition
            ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r := by
    fun_prop
  have hprod := deriv_mul hinner_diff houter_diff
  have houter_norm :
      ‖Real.smoothTransition
        ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4))‖ ≤
        (1 : ℝ) := by
    rw [Real.norm_eq_abs]
    exact
      abs_le.mpr
        ⟨by
          have hnonneg :
              0 ≤
                Real.smoothTransition
                  ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)) :=
            Real.smoothTransition.nonneg _
          linarith,
        Real.smoothTransition.le_one _⟩
  have hscale_nonneg : 0 ≤ C * (4 / width) := by
    exact
      mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hC_ge_one)
        (div_nonneg (by norm_num) hwidth_pos.le)
  calc
    ‖deriv
        (fun s : ℝ ↦
          Real.smoothTransition ((s - ((1 : ℝ) + width / 2)) / (width / 4)) *
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4)))
        r‖
        =
          ‖deriv
              (fun s : ℝ ↦
                Real.smoothTransition
                  ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r *
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4))‖ := by
            change
              ‖deriv
                  ((fun s : ℝ ↦
                      Real.smoothTransition
                        ((s - ((1 : ℝ) + width / 2)) / (width / 4))) *
                    fun s : ℝ ↦
                      Real.smoothTransition
                        ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4)))
                  r‖ =
                ‖deriv
                    (fun s : ℝ ↦
                      Real.smoothTransition
                        ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r *
                  Real.smoothTransition
                    ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4))‖
            rw [hprod, houter_zero]
            simp
    _ =
          ‖deriv
              (fun s : ℝ ↦
                Real.smoothTransition
                  ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r‖ *
            ‖Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4))‖ :=
        norm_mul _ _
    _ ≤ (C * (4 / width)) * 1 :=
        mul_le_mul hinner_bound houter_norm (norm_nonneg _) hscale_nonneg
    _ = C * (4 / width) := by ring

private theorem annulus_transition_product_profile_deriv_norm_le_of_outer_collar
    {width C r : ℝ} (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    (hC_ge_one : 1 ≤ C)
    (hC : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ C)
    (hr : (3 / 2 : ℝ) - width < r ∧ r < (3 / 2 : ℝ)) :
    ‖deriv
        (fun s : ℝ ↦
          Real.smoothTransition ((s - ((1 : ℝ) + width / 2)) / (width / 4)) *
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4)))
        r‖ ≤ C * (4 / width) := by
  have hden : 0 < width / 4 := by linarith
  have houter_arg :
      ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)) ∈
        Set.Icc (-(2 : ℝ)) 2 := by
    constructor
    · rw [le_div_iff₀ hden]
      nlinarith [hr.2.le]
    · rw [div_le_iff₀ hden]
      nlinarith [hr.1.le]
  have hinner_arg_gt :
      1 < ((r - ((1 : ℝ) + width / 2)) / (width / 4)) := by
    rw [one_lt_div hden]
    nlinarith [hr.1, hwidth_le_quarter]
  have houter_bound :
      ‖deriv
          (fun s : ℝ ↦
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r‖ ≤
        C * (4 / width) :=
    annulus_outer_transition_profile_deriv_norm_le hwidth_pos hC houter_arg
  have hinner_arg_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦ ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r := by
    fun_prop
  have hs_diff :
      DifferentiableAt ℝ Real.smoothTransition
        ((r - ((1 : ℝ) + width / 2)) / (width / 4)) :=
    ((Real.smoothTransition.contDiff :
        ContDiff ℝ (1 : WithTop ℕ∞) Real.smoothTransition).differentiable
      (by norm_num)) _
  have hinner_deriv_arg :
      deriv
          (fun s : ℝ ↦ ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r =
        (1 : ℝ) / (width / 4) := by
    rw [deriv_div_const]
    simp
  have hinner_deriv :
      deriv
          (fun s : ℝ ↦
            Real.smoothTransition
              ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r =
        deriv Real.smoothTransition
            ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
          ((1 : ℝ) / (width / 4)) := by
    simpa [Function.comp_def, hinner_deriv_arg] using
      deriv_comp r hs_diff hinner_arg_diff
  have hinner_zero :
      deriv
          (fun s : ℝ ↦
            Real.smoothTransition
              ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r = 0 := by
    rw [hinner_deriv,
      deriv_smoothTransition_eq_zero_of_one_lt hinner_arg_gt]
    simp
  have hinner_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦
          Real.smoothTransition
            ((s - ((1 : ℝ) + width / 2)) / (width / 4))) r := by
    fun_prop
  have houter_diff :
      DifferentiableAt ℝ
        (fun s : ℝ ↦
          Real.smoothTransition
            ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r := by
    fun_prop
  have hprod := deriv_mul hinner_diff houter_diff
  have hinner_norm :
      ‖Real.smoothTransition
        ((r - ((1 : ℝ) + width / 2)) / (width / 4))‖ ≤
        (1 : ℝ) := by
    rw [Real.norm_eq_abs]
    exact
      abs_le.mpr
        ⟨by
          have hnonneg :
              0 ≤
                Real.smoothTransition
                  ((r - ((1 : ℝ) + width / 2)) / (width / 4)) :=
            Real.smoothTransition.nonneg _
          linarith,
        Real.smoothTransition.le_one _⟩
  have hscale_nonneg : 0 ≤ C * (4 / width) := by
    exact
      mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hC_ge_one)
        (div_nonneg (by norm_num) hwidth_pos.le)
  calc
    ‖deriv
        (fun s : ℝ ↦
          Real.smoothTransition ((s - ((1 : ℝ) + width / 2)) / (width / 4)) *
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4)))
        r‖
        =
          ‖Real.smoothTransition
              ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
            deriv
              (fun s : ℝ ↦
                Real.smoothTransition
                  ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r‖ := by
            change
              ‖deriv
                  ((fun s : ℝ ↦
                      Real.smoothTransition
                        ((s - ((1 : ℝ) + width / 2)) / (width / 4))) *
                    fun s : ℝ ↦
                      Real.smoothTransition
                        ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4)))
                  r‖ =
                ‖Real.smoothTransition
                    ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
                  deriv
                    (fun s : ℝ ↦
                      Real.smoothTransition
                        ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r‖
            rw [hprod, hinner_zero]
            ring_nf
    _ =
          ‖Real.smoothTransition
              ((r - ((1 : ℝ) + width / 2)) / (width / 4))‖ *
            ‖deriv
              (fun s : ℝ ↦
                Real.smoothTransition
                  ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4))) r‖ :=
        norm_mul _ _
    _ ≤ 1 * (C * (4 / width)) :=
        mul_le_mul hinner_norm houter_bound (norm_nonneg _) (by norm_num)
    _ = C * (4 / width) := by ring

/--
%%handwave
name:
  Fixed-width smooth collar cutoff pair exists
statement:
  For every sufficiently small positive collar width there is a pair of
  smooth scalar radial cutoffs: one supported in the unit ball and one
  supported in the annulus \(1<\|x\|<3/2\).  They are bounded by one, equal to
  one on the corresponding cores of width \(\delta\), and have zero derivative
  on those cores.
proof:
  Choose one-dimensional smooth transition functions of the radius.  The
  inner profile is one on a neighborhood of radius \(1-\delta\) and vanishes
  before radius \(1-\delta/2\).  The annular profile is the product of an
  increasing transition from \(0\) to \(1\) in the collar
  \(1+\delta/2<r<1+3\delta/4\) and a decreasing transition from \(1\) to \(0\)
  in the collar \(3/2-3\delta/4<r<3/2-\delta/2\).  Since the profiles are
  locally constant at the origin and on the cores, their radial pullbacks are
  smooth and have zero derivative on the cores.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_exists_radial_collar_cutoff_pair
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {width : ℝ} (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) :
    Nonempty
      (EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
        (H := H) width) := by
  classical
  let unitProfile : ℝ → ℝ :=
    fun r ↦ Real.smoothTransition (((1 : ℝ) - width / 2 - r) / (width / 4))
  let annulusProfile : ℝ → ℝ :=
    fun r ↦
      Real.smoothTransition ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
        Real.smoothTransition
          ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4))
  let unitCutoff : H → ℝ := fun x ↦ unitProfile ‖x‖
  let annulusCutoff : H → ℝ := fun x ↦ annulusProfile ‖x‖
  have hwidth_half_pos : 0 < width / 2 := by linarith
  have hwidth_quarter_pos : 0 < width / 4 := by linarith
  have hunitProfile_smooth : ContDiff ℝ ∞ unitProfile := by
    dsimp [unitProfile]
    fun_prop
  have hannulusProfile_smooth : ContDiff ℝ ∞ annulusProfile := by
    dsimp [annulusProfile]
    fun_prop
  have hunit_smooth : ContDiff ℝ ∞ unitCutoff := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx0 : x = 0
    · subst x
      have h0_lt : ‖(0 : H)‖ < (1 : ℝ) - 3 * width / 4 := by
        simp
        nlinarith [hwidth_le_quarter]
      have hnorm_eventually :
          ∀ᶠ y in 𝓝 (0 : H), ‖y‖ < (1 : ℝ) - 3 * width / 4 :=
        continuous_norm.continuousAt.eventually (Iio_mem_nhds h0_lt)
      have hone : unitCutoff =ᶠ[𝓝 (0 : H)] fun _ : H ↦ (1 : ℝ) :=
        hnorm_eventually.mono fun y hy ↦ by
          have harg :
              1 ≤ (((1 : ℝ) - width / 2 - ‖y‖) / (width / 4)) :=
            (one_le_div hwidth_quarter_pos).2 (by nlinarith [hy])
          simpa [unitCutoff, unitProfile] using
            Real.smoothTransition.one_of_one_le harg
      exact (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq hone
    · have hnorm : ContDiffAt ℝ ∞ (fun y : H ↦ ‖y‖) x :=
        contDiffAt_norm ℝ hx0
      have harg :
          ContDiffAt ℝ ∞
            (fun y : H ↦ (((1 : ℝ) - width / 2 - ‖y‖) / (width / 4))) x :=
        (contDiffAt_const.sub hnorm).div_const (width / 4)
      exact Real.smoothTransition.contDiff.contDiffAt.comp x harg
  have hannulus_smooth : ContDiff ℝ ∞ annulusCutoff := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx0 : x = 0
    · subst x
      have h0_lt : ‖(0 : H)‖ < (1 : ℝ) + width / 2 := by
        simp
        linarith
      have hnorm_eventually :
          ∀ᶠ y in 𝓝 (0 : H), ‖y‖ < (1 : ℝ) + width / 2 :=
        continuous_norm.continuousAt.eventually (Iio_mem_nhds h0_lt)
      have hzero : annulusCutoff =ᶠ[𝓝 (0 : H)] fun _ : H ↦ (0 : ℝ) :=
        hnorm_eventually.mono fun y hy ↦ by
          have harg :
              ((‖y‖ - ((1 : ℝ) + width / 2)) / (width / 4)) ≤ 0 := by
            exact div_nonpos_of_nonpos_of_nonneg (by linarith) hwidth_quarter_pos.le
          simp [annulusCutoff, annulusProfile,
            Real.smoothTransition.zero_of_nonpos harg]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hzero
    · have hnorm : ContDiffAt ℝ ∞ (fun y : H ↦ ‖y‖) x :=
        contDiffAt_norm ℝ hx0
      have hinner_arg :
          ContDiffAt ℝ ∞
            (fun y : H ↦ ((‖y‖ - ((1 : ℝ) + width / 2)) / (width / 4))) x :=
        (hnorm.sub contDiffAt_const).div_const (width / 4)
      have houter_arg :
          ContDiffAt ℝ ∞
            (fun y : H ↦ ((((3 / 2 : ℝ) - width / 2) - ‖y‖) / (width / 4))) x :=
        (contDiffAt_const.sub hnorm).div_const (width / 4)
      have hinner :
          ContDiffAt ℝ ∞
            (fun y : H ↦
              Real.smoothTransition
                ((‖y‖ - ((1 : ℝ) + width / 2)) / (width / 4))) x :=
        Real.smoothTransition.contDiff.contDiffAt.comp x hinner_arg
      have houter :
          ContDiffAt ℝ ∞
            (fun y : H ↦
              Real.smoothTransition
                ((((3 / 2 : ℝ) - width / 2) - ‖y‖) / (width / 4))) x :=
        Real.smoothTransition.contDiff.contDiffAt.comp x houter_arg
      simpa [annulusCutoff, annulusProfile] using hinner.mul houter
  have hunit_support :
      tsupport unitCutoff ⊆ Metric.ball (0 : H) 1 := by
    intro x hx
    by_contra hnot
    have hx_ge : (1 : ℝ) ≤ ‖x‖ := by
      have hnot_norm : ¬ ‖x‖ < (1 : ℝ) := by
        intro hlt
        exact hnot (by simpa [Metric.mem_ball, dist_eq_norm] using hlt)
      exact le_of_not_gt hnot_norm
    have hx_gt : (1 : ℝ) - width / 2 < ‖x‖ := by
      linarith
    have hnorm_eventually :
        ∀ᶠ y in 𝓝 x, (1 : ℝ) - width / 2 < ‖y‖ :=
      continuous_norm.continuousAt.eventually (Ioi_mem_nhds hx_gt)
    have hzero : unitCutoff =ᶠ[𝓝 x] 0 :=
      hnorm_eventually.mono fun y hy ↦ by
        have harg :
            (((1 : ℝ) - width / 2 - ‖y‖) / (width / 4)) ≤ 0 := by
          exact div_nonpos_of_nonpos_of_nonneg (by linarith) hwidth_quarter_pos.le
        simpa [unitCutoff, unitProfile] using
          Real.smoothTransition.zero_of_nonpos harg
    exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hx
  have hannulus_support :
      tsupport annulusCutoff ⊆
        euclideanSobolevUnitBallReflectionAnnulus H := by
    intro x hx
    dsimp [euclideanSobolevUnitBallReflectionAnnulus]
    constructor
    · by_contra hnot
      have hx_le : ‖x‖ ≤ (1 : ℝ) := le_of_not_gt hnot
      have hx_lt : ‖x‖ < (1 : ℝ) + width / 2 := by
        linarith
      have hnorm_eventually :
          ∀ᶠ y in 𝓝 x, ‖y‖ < (1 : ℝ) + width / 2 :=
        continuous_norm.continuousAt.eventually (Iio_mem_nhds hx_lt)
      have hzero : annulusCutoff =ᶠ[𝓝 x] 0 :=
        hnorm_eventually.mono fun y hy ↦ by
          have harg :
              ((‖y‖ - ((1 : ℝ) + width / 2)) / (width / 4)) ≤ 0 := by
            exact div_nonpos_of_nonpos_of_nonneg (by linarith) hwidth_quarter_pos.le
          simp [annulusCutoff, annulusProfile,
            Real.smoothTransition.zero_of_nonpos harg]
      exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hx
    · by_contra hnot
      have hx_ge : (3 / 2 : ℝ) ≤ ‖x‖ := le_of_not_gt hnot
      have hx_gt : (3 / 2 : ℝ) - width / 2 < ‖x‖ := by
        linarith
      have hnorm_eventually :
          ∀ᶠ y in 𝓝 x, (3 / 2 : ℝ) - width / 2 < ‖y‖ :=
        continuous_norm.continuousAt.eventually (Ioi_mem_nhds hx_gt)
      have hzero : annulusCutoff =ᶠ[𝓝 x] 0 :=
        hnorm_eventually.mono fun y hy ↦ by
          have harg :
              ((((3 / 2 : ℝ) - width / 2) - ‖y‖) / (width / 4)) ≤ 0 := by
            exact div_nonpos_of_nonpos_of_nonneg (by linarith) hwidth_quarter_pos.le
          simp [annulusCutoff, annulusProfile,
            Real.smoothTransition.zero_of_nonpos harg]
      exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hx
  have hunit_compact : IsCompact (tsupport unitCutoff) := by
    have hsubset_closedBall :
        tsupport unitCutoff ⊆ Metric.closedBall (0 : H) 1 := by
      intro x hx
      have hxball := hunit_support hx
      have hdist : dist x (0 : H) < (1 : ℝ) := by
        simpa [Metric.mem_ball] using hxball
      exact by
        simpa [Metric.mem_closedBall] using le_of_lt hdist
    exact
      (isCompact_closedBall (0 : H) (1 : ℝ)).of_isClosed_subset
        (isClosed_tsupport _) hsubset_closedBall
  have hannulus_compact : IsCompact (tsupport annulusCutoff) := by
    have hsubset_closedBall :
        tsupport annulusCutoff ⊆ Metric.closedBall (0 : H) (3 / 2 : ℝ) := by
      intro x hx
      have hxann := hannulus_support hx
      have hxlt : ‖x‖ < (3 / 2 : ℝ) := by
        simpa [euclideanSobolevUnitBallReflectionAnnulus] using hxann.2
      exact by
        simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_lt hxlt
    exact
      (isCompact_closedBall (0 : H) (3 / 2 : ℝ)).of_isClosed_subset
        (isClosed_tsupport _) hsubset_closedBall
  have hunit_norm : ∀ x : H, ‖unitCutoff x‖ ≤ (1 : ℝ) := by
    intro x
    dsimp [unitCutoff, unitProfile]
    exact
      abs_le.mpr
        ⟨by
          have hnonneg :
              0 ≤
                Real.smoothTransition
                  (((1 : ℝ) - width / 2 - ‖x‖) / (width / 4)) :=
            Real.smoothTransition.nonneg _
          linarith,
        Real.smoothTransition.le_one _⟩
  have hannulus_norm : ∀ x : H, ‖annulusCutoff x‖ ≤ (1 : ℝ) := by
    intro x
    dsimp [annulusCutoff, annulusProfile]
    let a : ℝ :=
      Real.smoothTransition ((‖x‖ - ((1 : ℝ) + width / 2)) / (width / 4))
    let b : ℝ :=
      Real.smoothTransition
        ((((3 / 2 : ℝ) - width / 2) - ‖x‖) / (width / 4))
    have ha_nonneg : 0 ≤ a := Real.smoothTransition.nonneg _
    have ha_le : a ≤ 1 := Real.smoothTransition.le_one _
    have hb_nonneg : 0 ≤ b := Real.smoothTransition.nonneg _
    have hb_le : b ≤ 1 := Real.smoothTransition.le_one _
    have hab_nonneg : 0 ≤ a * b := mul_nonneg ha_nonneg hb_nonneg
    have hab_le : a * b ≤ 1 := by
      calc
        a * b ≤ 1 * b := mul_le_mul_of_nonneg_right ha_le hb_nonneg
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hb_le (by norm_num)
        _ = 1 := by norm_num
    simpa [a, b] using abs_le.mpr ⟨by linarith, hab_le⟩
  refine
    ⟨{ unitCutoff := unitCutoff
       annulusCutoff := annulusCutoff
       radial_profiles :=
        ⟨unitProfile, annulusProfile, hunitProfile_smooth,
          hannulusProfile_smooth, by intro x; rfl, by intro x; rfl⟩
       unitCutoff_eq_standard := by intro x; rfl
       annulusCutoff_eq_standard := by intro x; rfl
       unitCutoff_smooth := hunit_smooth
       annulusCutoff_smooth := hannulus_smooth
       unitCutoff_tsupport_subset := hunit_support
       annulusCutoff_tsupport_subset := hannulus_support
       unitCutoff_compact_support := hunit_compact
       annulusCutoff_compact_support := hannulus_compact
       unitCutoff_norm_le_one := hunit_norm
       annulusCutoff_norm_le_one := hannulus_norm
       unitCutoff_eq_one_on_core := ?_
       annulusCutoff_eq_one_on_core := ?_
       unitCutoff_fderiv_eq_zero_on_core := ?_
       annulusCutoff_fderiv_eq_zero_on_core := ?_ }⟩
  · intro x hx
    have harg :
        1 ≤ (((1 : ℝ) - width / 2 - ‖x‖) / (width / 4)) :=
      (one_le_div hwidth_quarter_pos).2 (by nlinarith [hx])
    simpa [unitCutoff, unitProfile] using
      Real.smoothTransition.one_of_one_le harg
  · intro x hx₁ hx₂
    have harg₁ :
        1 ≤ ((‖x‖ - ((1 : ℝ) + width / 2)) / (width / 4)) :=
      (one_le_div hwidth_quarter_pos).2 (by nlinarith [hx₁])
    have harg₂ :
        1 ≤ ((((3 / 2 : ℝ) - width / 2) - ‖x‖) / (width / 4)) :=
      (one_le_div hwidth_quarter_pos).2 (by nlinarith [hx₂])
    simp [annulusCutoff, annulusProfile,
      Real.smoothTransition.one_of_one_le harg₁,
      Real.smoothTransition.one_of_one_le harg₂]
  · intro x hx
    have hx_lt : ‖x‖ < (1 : ℝ) - 3 * width / 4 := by
      nlinarith [hwidth_pos, hx]
    have hnorm_eventually :
        ∀ᶠ y in 𝓝 x, ‖y‖ < (1 : ℝ) - 3 * width / 4 :=
      continuous_norm.continuousAt.eventually (Iio_mem_nhds hx_lt)
    have hone : unitCutoff =ᶠ[𝓝 x] fun _ : H ↦ (1 : ℝ) :=
      hnorm_eventually.mono fun y hy ↦ by
        have harg :
            1 ≤ (((1 : ℝ) - width / 2 - ‖y‖) / (width / 4)) :=
          (one_le_div hwidth_quarter_pos).2 (by nlinarith [hy])
        simpa [unitCutoff, unitProfile] using
          Real.smoothTransition.one_of_one_le harg
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hone]
    simp
  · intro x hx₁ hx₂
    have hx_lower : (1 : ℝ) + 3 * width / 4 < ‖x‖ := by
      nlinarith [hwidth_pos, hx₁]
    have hx_upper : ‖x‖ < (3 / 2 : ℝ) - 3 * width / 4 := by
      nlinarith [hwidth_pos, hx₂]
    have hlower_eventually :
        ∀ᶠ y in 𝓝 x, (1 : ℝ) + 3 * width / 4 < ‖y‖ :=
      continuous_norm.continuousAt.eventually (Ioi_mem_nhds hx_lower)
    have hupper_eventually :
        ∀ᶠ y in 𝓝 x, ‖y‖ < (3 / 2 : ℝ) - 3 * width / 4 :=
      continuous_norm.continuousAt.eventually (Iio_mem_nhds hx_upper)
    have hone : annulusCutoff =ᶠ[𝓝 x] fun _ : H ↦ (1 : ℝ) := by
      filter_upwards [hlower_eventually, hupper_eventually] with y hy_lower hy_upper
      have harg₁ :
          1 ≤ ((‖y‖ - ((1 : ℝ) + width / 2)) / (width / 4)) :=
        (one_le_div hwidth_quarter_pos).2 (by nlinarith [hy_lower])
      have harg₂ :
          1 ≤ ((((3 / 2 : ℝ) - width / 2) - ‖y‖) / (width / 4)) :=
        (one_le_div hwidth_quarter_pos).2 (by nlinarith [hy_upper])
      simp [annulusCutoff, annulusProfile,
        Real.smoothTransition.one_of_one_le harg₁,
        Real.smoothTransition.one_of_one_le harg₂]
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hone]
    simp

private theorem fderiv_norm_apply_eq_inner_inv_norm_smul
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {z v : H} (hz : z ≠ 0) :
    fderiv ℝ (fun y : H ↦ ‖y‖) z v =
      inner ℝ ((‖z‖)⁻¹ • z) v := by
  have hnorm_cd : ContDiffAt ℝ ∞ (fun y : H ↦ ‖y‖) z :=
    contDiffAt_norm ℝ hz
  have hnorm : DifferentiableAt ℝ (fun y : H ↦ ‖y‖) z :=
    hnorm_cd.differentiableAt (by simp)
  have hsq_chain :
      fderiv ℝ (fun y : H ↦ ‖y‖ ^ 2) z v =
        (2 * ‖z‖) * fderiv ℝ (fun y : H ↦ ‖y‖) z v := by
    have h :=
      fderiv_fun_pow (𝕜 := ℝ) (f := fun y : H ↦ ‖y‖) (x := z) 2 hnorm
    rw [h]
    simp [pow_one, mul_assoc]
  have hsq_inner :
      fderiv ℝ (fun y : H ↦ ‖y‖ ^ 2) z v =
        2 * inner ℝ z v := by
    rw [fderiv_norm_sq_apply]
    simp [innerSL_apply_apply, two_smul]
    ring
  have hmain :
      (2 * ‖z‖) * fderiv ℝ (fun y : H ↦ ‖y‖) z v =
        2 * inner ℝ z v := by
    rw [← hsq_chain, hsq_inner]
  have hnorm_ne : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  calc
    fderiv ℝ (fun y : H ↦ ‖y‖) z v
        = (‖z‖)⁻¹ * inner ℝ z v := by
          have htwo : (2 : ℝ) ≠ 0 := by norm_num
          field_simp [hnorm_ne, htwo] at hmain ⊢
          linarith
    _ = inner ℝ ((‖z‖)⁻¹ • z) v := by
          rw [inner_smul_left]
          simp

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.unitCutoff_fderiv_apply_eq
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width : ℝ}
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    {z v : H} (hz : z ≠ 0) :
    fderiv ℝ χ.unitCutoff z v =
      deriv
        (fun r : ℝ ↦
          Real.smoothTransition (((1 : ℝ) - width / 2 - r) / (width / 4)))
        ‖z‖ *
        fderiv ℝ (fun y : H ↦ ‖y‖) z v := by
  let g : ℝ → ℝ := fun r : ℝ ↦
    Real.smoothTransition (((1 : ℝ) - width / 2 - r) / (width / 4))
  have hχ : χ.unitCutoff = fun y : H ↦ g ‖y‖ := by
    funext y
    simpa [g] using χ.unitCutoff_eq_standard y
  have hg : DifferentiableAt ℝ g ‖z‖ := by
    dsimp [g]
    fun_prop
  have hnorm_cd : ContDiffAt ℝ ∞ (fun y : H ↦ ‖y‖) z :=
    contDiffAt_norm ℝ hz
  have hnorm : DifferentiableAt ℝ (fun y : H ↦ ‖y‖) z :=
    hnorm_cd.differentiableAt (by simp)
  have hcomp :
      fderiv ℝ (fun y : H ↦ g ‖y‖) z =
        (fderiv ℝ g ‖z‖).comp
          (fderiv ℝ (fun y : H ↦ ‖y‖) z) :=
    fderiv_comp' (x := z) (g := g) (f := fun y : H ↦ ‖y‖) hg hnorm
  rw [hχ, hcomp]
  simp [g, ContinuousLinearMap.comp_apply, mul_comm]

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.unitCutoff_fderiv_apply_eq_radial
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width : ℝ}
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    {z v : H} (hz : z ≠ 0) :
    fderiv ℝ χ.unitCutoff z v =
      deriv
        (fun r : ℝ ↦
          Real.smoothTransition (((1 : ℝ) - width / 2 - r) / (width / 4)))
        ‖z‖ *
        inner ℝ ((‖z‖)⁻¹ • z) v := by
  rw [χ.unitCutoff_fderiv_apply_eq hz,
    fderiv_norm_apply_eq_inner_inv_norm_smul hz]

private theorem euclideanSobolevUnitBallInnerTransitionCollar_ne_zero
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {width : ℝ} (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) {z : H}
    (hz : z ∈ euclideanSobolevUnitBallInnerTransitionCollar H width) :
    z ≠ 0 := by
  intro hz_eq
  subst z
  have hlt : (1 : ℝ) - width < 0 := by
    simpa [euclideanSobolevUnitBallInnerTransitionCollar] using hz.1
  nlinarith [hwidth_le_quarter, hlt]

private theorem euclideanSobolevUnitBallAnnulusInnerTransitionCollar_ne_zero
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {width : ℝ} {z : H}
    (hz : z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width) :
    z ≠ 0 := by
  intro hz_eq
  subst z
  have hlt : (1 : ℝ) < 0 := by
    simpa [euclideanSobolevUnitBallAnnulusInnerTransitionCollar] using hz.1
  linarith

private theorem euclideanSobolevUnitBallAnnulusOuterTransitionCollar_ne_zero
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {width : ℝ} (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) {z : H}
    (hz : z ∈ euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width) :
    z ≠ 0 := by
  intro hz_eq
  subst z
  have hlt : (3 / 2 : ℝ) - width < 0 := by
    simpa [euclideanSobolevUnitBallAnnulusOuterTransitionCollar] using hz.1
  nlinarith [hwidth_le_quarter, hlt]

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.unitCutoff_fderiv_apply_eq_radial_of_inner_transition
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width : ℝ}
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) {z v : H}
    (hz : z ∈ euclideanSobolevUnitBallInnerTransitionCollar H width) :
    fderiv ℝ χ.unitCutoff z v =
      deriv
        (fun r : ℝ ↦
          Real.smoothTransition (((1 : ℝ) - width / 2 - r) / (width / 4)))
        ‖z‖ *
        inner ℝ ((‖z‖)⁻¹ • z) v := by
  exact
    χ.unitCutoff_fderiv_apply_eq_radial
      (euclideanSobolevUnitBallInnerTransitionCollar_ne_zero
        hwidth_le_quarter hz)

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.unitCutoff_fderiv_apply_eq_oriented_profile_of_inner_transition
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width : ℝ}
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) {z v : H}
    (hz : z ∈ euclideanSobolevUnitBallInnerTransitionCollar H width) :
    fderiv ℝ χ.unitCutoff z v =
      (deriv Real.smoothTransition
          (((1 : ℝ) - width / 2 - ‖z‖) / (width / 4)) *
        (-(1 : ℝ) / (width / 4))) *
        inner ℝ ((‖z‖)⁻¹ • z) v := by
  rw [χ.unitCutoff_fderiv_apply_eq_radial_of_inner_transition
      hwidth_le_quarter hz,
    unit_inner_transition_profile_deriv_eq]

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.unitCutoff_fderiv_apply_norm_le_of_inner_transition
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width C : ℝ}
    (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    (hC_ge_one : 1 ≤ C)
    (hC : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ C)
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    {z v : H}
    (hz : z ∈ euclideanSobolevUnitBallInnerTransitionCollar H width) :
    ‖fderiv ℝ χ.unitCutoff z v‖ ≤ C * (4 / width) * ‖v‖ := by
  have hz0 : z ≠ 0 := by
    intro hz_eq
    subst z
    have hlt : (1 : ℝ) - width < 0 := by
      simpa [euclideanSobolevUnitBallInnerTransitionCollar] using hz.1
    nlinarith [hwidth_le_quarter, hlt]
  have hprofile :
      ‖deriv
          (fun s : ℝ ↦
            Real.smoothTransition (((1 : ℝ) - width / 2 - s) / (width / 4)))
          ‖z‖‖ ≤ C * (4 / width) :=
    unit_inner_transition_profile_deriv_norm_le hwidth_pos hC
      (unit_inner_transition_arg_mem_Icc_neg_two_two hwidth_pos hz)
  have hnorm_op :
      ‖fderiv ℝ (fun y : H ↦ ‖y‖) z‖ ≤ (1 : ℝ) := by
    simpa using
      (norm_fderiv_le_of_lipschitz (𝕜 := ℝ)
        (f := fun y : H ↦ ‖y‖) (x₀ := z) lipschitzWith_one_norm)
  have hnorm_apply :
      ‖fderiv ℝ (fun y : H ↦ ‖y‖) z v‖ ≤ ‖v‖ := by
    calc
      ‖fderiv ℝ (fun y : H ↦ ‖y‖) z v‖
          ≤ ‖fderiv ℝ (fun y : H ↦ ‖y‖) z‖ * ‖v‖ :=
            le_opNorm _ _
      _ ≤ 1 * ‖v‖ :=
            mul_le_mul_of_nonneg_right hnorm_op (norm_nonneg _)
      _ = ‖v‖ := one_mul _
  have hscale_nonneg : 0 ≤ C * (4 / width) := by
    exact
      mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hC_ge_one)
        (div_nonneg (by norm_num) hwidth_pos.le)
  rw [χ.unitCutoff_fderiv_apply_eq hz0]
  calc
    ‖deriv
        (fun r : ℝ ↦
          Real.smoothTransition (((1 : ℝ) - width / 2 - r) / (width / 4)))
        ‖z‖ *
        fderiv ℝ (fun y : H ↦ ‖y‖) z v‖
        =
          ‖deriv
            (fun r : ℝ ↦
              Real.smoothTransition (((1 : ℝ) - width / 2 - r) / (width / 4)))
            ‖z‖‖ *
            ‖fderiv ℝ (fun y : H ↦ ‖y‖) z v‖ := norm_mul _ _
    _ ≤ (C * (4 / width)) * ‖v‖ :=
        mul_le_mul hprofile hnorm_apply (norm_nonneg _) hscale_nonneg

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.annulusCutoff_fderiv_apply_eq
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width : ℝ}
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    {z v : H} (hz : z ≠ 0) :
    fderiv ℝ χ.annulusCutoff z v =
      deriv
        (fun r : ℝ ↦
          Real.smoothTransition ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)))
        ‖z‖ *
        fderiv ℝ (fun y : H ↦ ‖y‖) z v := by
  let g : ℝ → ℝ := fun r : ℝ ↦
    Real.smoothTransition ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
      Real.smoothTransition
        ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4))
  have hχ : χ.annulusCutoff = fun y : H ↦ g ‖y‖ := by
    funext y
    simpa [g] using χ.annulusCutoff_eq_standard y
  have hg : DifferentiableAt ℝ g ‖z‖ := by
    dsimp [g]
    fun_prop
  have hnorm_cd : ContDiffAt ℝ ∞ (fun y : H ↦ ‖y‖) z :=
    contDiffAt_norm ℝ hz
  have hnorm : DifferentiableAt ℝ (fun y : H ↦ ‖y‖) z :=
    hnorm_cd.differentiableAt (by simp)
  have hcomp :
      fderiv ℝ (fun y : H ↦ g ‖y‖) z =
        (fderiv ℝ g ‖z‖).comp
          (fderiv ℝ (fun y : H ↦ ‖y‖) z) :=
    fderiv_comp' (x := z) (g := g) (f := fun y : H ↦ ‖y‖) hg hnorm
  rw [hχ, hcomp]
  simp [g, ContinuousLinearMap.comp_apply, mul_comm]

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.annulusCutoff_fderiv_apply_eq_radial
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width : ℝ}
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    {z v : H} (hz : z ≠ 0) :
    fderiv ℝ χ.annulusCutoff z v =
      deriv
        (fun r : ℝ ↦
          Real.smoothTransition ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)))
        ‖z‖ *
        inner ℝ ((‖z‖)⁻¹ • z) v := by
  rw [χ.annulusCutoff_fderiv_apply_eq hz,
    fderiv_norm_apply_eq_inner_inv_norm_smul hz]

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.annulusCutoff_fderiv_apply_eq_radial_of_inner_transition
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width : ℝ}
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    {z v : H}
    (hz : z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width) :
    fderiv ℝ χ.annulusCutoff z v =
      deriv
        (fun r : ℝ ↦
          Real.smoothTransition ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)))
        ‖z‖ *
        inner ℝ ((‖z‖)⁻¹ • z) v := by
  exact
    χ.annulusCutoff_fderiv_apply_eq_radial
      (euclideanSobolevUnitBallAnnulusInnerTransitionCollar_ne_zero hz)

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.annulusCutoff_fderiv_apply_eq_radial_of_outer_transition
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width : ℝ}
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) {z v : H}
    (hz : z ∈ euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width) :
    fderiv ℝ χ.annulusCutoff z v =
      deriv
        (fun r : ℝ ↦
          Real.smoothTransition ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)))
        ‖z‖ *
        inner ℝ ((‖z‖)⁻¹ • z) v := by
  exact
    χ.annulusCutoff_fderiv_apply_eq_radial
      (euclideanSobolevUnitBallAnnulusOuterTransitionCollar_ne_zero
        hwidth_le_quarter hz)

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.annulusCutoff_fderiv_apply_eq_oriented_profile_of_inner_transition
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width : ℝ}
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) {z v : H}
    (hz : z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width) :
    fderiv ℝ χ.annulusCutoff z v =
      (deriv Real.smoothTransition
          ((‖z‖ - ((1 : ℝ) + width / 2)) / (width / 4)) *
        ((1 : ℝ) / (width / 4))) *
        inner ℝ ((‖z‖)⁻¹ • z) v := by
  rw [χ.annulusCutoff_fderiv_apply_eq_radial_of_inner_transition hz,
    annulus_transition_product_profile_deriv_eq_of_inner_collar
      hwidth_pos hwidth_le_quarter hz]

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.annulusCutoff_fderiv_apply_eq_oriented_profile_of_outer_transition
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width : ℝ}
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) {z v : H}
    (hz : z ∈ euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width) :
    fderiv ℝ χ.annulusCutoff z v =
      (deriv Real.smoothTransition
          ((((3 / 2 : ℝ) - width / 2) - ‖z‖) / (width / 4)) *
        (-(1 : ℝ) / (width / 4))) *
        inner ℝ ((‖z‖)⁻¹ • z) v := by
  rw [χ.annulusCutoff_fderiv_apply_eq_radial_of_outer_transition
      hwidth_le_quarter hz,
    annulus_transition_product_profile_deriv_eq_of_outer_collar
      hwidth_pos hwidth_le_quarter hz]

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.annulusCutoff_fderiv_apply_norm_le_of_inner_transition
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width C : ℝ}
    (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    (hC_ge_one : 1 ≤ C)
    (hC : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ C)
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    {z v : H}
    (hz : z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width) :
    ‖fderiv ℝ χ.annulusCutoff z v‖ ≤ C * (4 / width) * ‖v‖ := by
  have hz0 : z ≠ 0 := by
    intro hz_eq
    subst z
    have hlt : (1 : ℝ) < 0 := by
      simpa [euclideanSobolevUnitBallAnnulusInnerTransitionCollar] using hz.1
    linarith
  have hprofile :
      ‖deriv
          (fun s : ℝ ↦
            Real.smoothTransition ((s - ((1 : ℝ) + width / 2)) / (width / 4)) *
              Real.smoothTransition
                ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4)))
          ‖z‖‖ ≤ C * (4 / width) :=
    annulus_transition_product_profile_deriv_norm_le_of_inner_collar
      hwidth_pos hwidth_le_quarter hC_ge_one hC hz
  have hnorm_op :
      ‖fderiv ℝ (fun y : H ↦ ‖y‖) z‖ ≤ (1 : ℝ) := by
    simpa using
      (norm_fderiv_le_of_lipschitz (𝕜 := ℝ)
        (f := fun y : H ↦ ‖y‖) (x₀ := z) lipschitzWith_one_norm)
  have hnorm_apply :
      ‖fderiv ℝ (fun y : H ↦ ‖y‖) z v‖ ≤ ‖v‖ := by
    calc
      ‖fderiv ℝ (fun y : H ↦ ‖y‖) z v‖
          ≤ ‖fderiv ℝ (fun y : H ↦ ‖y‖) z‖ * ‖v‖ :=
            le_opNorm _ _
      _ ≤ 1 * ‖v‖ :=
            mul_le_mul_of_nonneg_right hnorm_op (norm_nonneg _)
      _ = ‖v‖ := one_mul _
  have hscale_nonneg : 0 ≤ C * (4 / width) := by
    exact
      mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hC_ge_one)
        (div_nonneg (by norm_num) hwidth_pos.le)
  rw [χ.annulusCutoff_fderiv_apply_eq hz0]
  calc
    ‖deriv
        (fun r : ℝ ↦
          Real.smoothTransition ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)))
        ‖z‖ *
        fderiv ℝ (fun y : H ↦ ‖y‖) z v‖
        =
          ‖deriv
            (fun r : ℝ ↦
              Real.smoothTransition ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
                Real.smoothTransition
                  ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)))
            ‖z‖‖ *
            ‖fderiv ℝ (fun y : H ↦ ‖y‖) z v‖ := norm_mul _ _
    _ ≤ (C * (4 / width)) * ‖v‖ :=
        mul_le_mul hprofile hnorm_apply (norm_nonneg _) hscale_nonneg

private theorem EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair.annulusCutoff_fderiv_apply_norm_le_of_outer_transition
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width C : ℝ}
    (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    (hC_ge_one : 1 ≤ C)
    (hC : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ C)
    (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
      (H := H) width)
    {z v : H}
    (hz : z ∈ euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width) :
    ‖fderiv ℝ χ.annulusCutoff z v‖ ≤ C * (4 / width) * ‖v‖ := by
  have hz0 : z ≠ 0 := by
    intro hz_eq
    subst z
    have hlt : (3 / 2 : ℝ) - width < 0 := by
      simpa [euclideanSobolevUnitBallAnnulusOuterTransitionCollar] using hz.1
    nlinarith [hwidth_le_quarter, hlt]
  have hprofile :
      ‖deriv
          (fun s : ℝ ↦
            Real.smoothTransition ((s - ((1 : ℝ) + width / 2)) / (width / 4)) *
              Real.smoothTransition
                ((((3 / 2 : ℝ) - width / 2) - s) / (width / 4)))
          ‖z‖‖ ≤ C * (4 / width) :=
    annulus_transition_product_profile_deriv_norm_le_of_outer_collar
      hwidth_pos hwidth_le_quarter hC_ge_one hC hz
  have hnorm_op :
      ‖fderiv ℝ (fun y : H ↦ ‖y‖) z‖ ≤ (1 : ℝ) := by
    simpa using
      (norm_fderiv_le_of_lipschitz (𝕜 := ℝ)
        (f := fun y : H ↦ ‖y‖) (x₀ := z) lipschitzWith_one_norm)
  have hnorm_apply :
      ‖fderiv ℝ (fun y : H ↦ ‖y‖) z v‖ ≤ ‖v‖ := by
    calc
      ‖fderiv ℝ (fun y : H ↦ ‖y‖) z v‖
          ≤ ‖fderiv ℝ (fun y : H ↦ ‖y‖) z‖ * ‖v‖ :=
            le_opNorm _ _
      _ ≤ 1 * ‖v‖ :=
            mul_le_mul_of_nonneg_right hnorm_op (norm_nonneg _)
      _ = ‖v‖ := one_mul _
  have hscale_nonneg : 0 ≤ C * (4 / width) := by
    exact
      mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hC_ge_one)
        (div_nonneg (by norm_num) hwidth_pos.le)
  rw [χ.annulusCutoff_fderiv_apply_eq hz0]
  calc
    ‖deriv
        (fun r : ℝ ↦
          Real.smoothTransition ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
            Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)))
        ‖z‖ *
        fderiv ℝ (fun y : H ↦ ‖y‖) z v‖
        =
          ‖deriv
            (fun r : ℝ ↦
              Real.smoothTransition ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
                Real.smoothTransition
                  ((((3 / 2 : ℝ) - width / 2) - r) / (width / 4)))
            ‖z‖‖ *
            ‖fderiv ℝ (fun y : H ↦ ‖y‖) z v‖ := norm_mul _ _
    _ ≤ (C * (4 / width)) * ‖v‖ :=
        mul_le_mul hprofile hnorm_apply (norm_nonneg _) hscale_nonneg

private def euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (width : ℝ) (φ : H → ℝ) (v : H) (z : H) : ℝ :=
  (deriv Real.smoothTransition
      (((1 : ℝ) - width / 2 - ‖z‖) / (width / 4)) *
    (-(1 : ℝ) / (width / 4))) *
    inner ℝ ((‖z‖)⁻¹ • z) v * φ z

private def euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (width : ℝ) (φ : H → ℝ) (v : H) (z : H) : ℝ :=
  (deriv Real.smoothTransition
      ((‖z‖ - ((1 : ℝ) + width / 2)) / (width / 4)) *
    ((1 : ℝ) / (width / 4))) *
    inner ℝ ((‖z‖)⁻¹ • z) v * φ z

private def euclideanSobolevUnitBallAnnulusOuterOrientedRadialPairingWeight
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (width : ℝ) (φ : H → ℝ) (v : H) (z : H) : ℝ :=
  (deriv Real.smoothTransition
      ((((3 / 2 : ℝ) - width / 2) - ‖z‖) / (width / 4)) *
    (-(1 : ℝ) / (width / 4))) *
    inner ℝ ((‖z‖)⁻¹ • z) v * φ z

private noncomputable def euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (width : ℝ) (φ : H → ℝ) (v : H) (z : H) : ℝ :=
  by
    classical
    exact
      if z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width then
        euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
          width φ v z
      else
        euclideanSobolevUnitBallAnnulusOuterOrientedRadialPairingWeight
          width φ v z

private theorem norm_inner_invNorm_smul_le_norm
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {z v : H} (hz : z ≠ 0) :
    ‖inner ℝ ((‖z‖)⁻¹ • z) v‖ ≤ ‖v‖ := by
  have hrad_norm :
      ‖((‖z‖)⁻¹ • z)‖ = (1 : ℝ) := by
    have hmem := invNorm_smul_mem_unit_sphere (H := H) hz
    simpa [Metric.mem_sphere, dist_eq_norm] using hmem
  calc
    ‖inner ℝ ((‖z‖)⁻¹ • z) v‖
        ≤ ‖((‖z‖)⁻¹ • z)‖ * ‖v‖ :=
          norm_inner_le_norm (𝕜 := ℝ) _ _
    _ = ‖v‖ := by rw [hrad_norm, one_mul]

private theorem euclideanSobolevUnitBallInnerOrientedRadialPairingWeight_norm_le
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width C : ℝ}
    (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    (hC_ge_one : 1 ≤ C)
    (hC : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ C)
    {φ : H → ℝ} {v z : H}
    (hz : z ∈ euclideanSobolevUnitBallInnerTransitionCollar H width) :
    ‖euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
        width φ v z‖ ≤
      (C * (4 / width) * ‖v‖) * ‖φ z‖ := by
  have hz0 : z ≠ 0 := by
    exact euclideanSobolevUnitBallInnerTransitionCollar_ne_zero
      hwidth_le_quarter hz
  have hprof :
      ‖deriv Real.smoothTransition
          (((1 : ℝ) - width / 2 - ‖z‖) / (width / 4)) *
        (-(1 : ℝ) / (width / 4))‖ ≤
        C * (4 / width) := by
    have hderiv :=
      unit_inner_transition_profile_deriv_norm_le
        hwidth_pos hC
        (unit_inner_transition_arg_mem_Icc_neg_two_two hwidth_pos hz)
    simpa [unit_inner_transition_profile_deriv_eq] using hderiv
  have hinner : ‖inner ℝ ((‖z‖)⁻¹ • z) v‖ ≤ ‖v‖ :=
    norm_inner_invNorm_smul_le_norm hz0
  have hscale_nonneg : 0 ≤ C * (4 / width) := by
    exact
      mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hC_ge_one)
        (div_nonneg (by norm_num) hwidth_pos.le)
  calc
    ‖euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
        width φ v z‖
        =
          ‖deriv Real.smoothTransition
              (((1 : ℝ) - width / 2 - ‖z‖) / (width / 4)) *
            (-(1 : ℝ) / (width / 4))‖ *
            ‖inner ℝ ((‖z‖)⁻¹ • z) v‖ * ‖φ z‖ := by
          simp [euclideanSobolevUnitBallInnerOrientedRadialPairingWeight,
            norm_mul, mul_assoc]
    _ ≤ (C * (4 / width) * ‖v‖) * ‖φ z‖ := by
          exact
            mul_le_mul_of_nonneg_right
              (mul_le_mul hprof hinner (norm_nonneg _) hscale_nonneg)
              (norm_nonneg _)

private theorem euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight_norm_le
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width C : ℝ}
    (hwidth_pos : 0 < width)
    (hC_ge_one : 1 ≤ C)
    (hC : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ C)
    {φ : H → ℝ} {v z : H}
    (hz : z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width) :
    ‖euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
        width φ v z‖ ≤
      (C * (4 / width) * ‖v‖) * ‖φ z‖ := by
  have hz0 : z ≠ 0 :=
    euclideanSobolevUnitBallAnnulusInnerTransitionCollar_ne_zero hz
  have hprof :
      ‖deriv Real.smoothTransition
          ((‖z‖ - ((1 : ℝ) + width / 2)) / (width / 4)) *
        ((1 : ℝ) / (width / 4))‖ ≤
        C * (4 / width) := by
    have hderiv :=
      annulus_inner_transition_profile_deriv_norm_le
        hwidth_pos hC
        (annulus_inner_transition_arg_mem_Icc_neg_two_two hwidth_pos hz)
    simpa [annulus_inner_transition_profile_deriv_eq] using hderiv
  have hinner : ‖inner ℝ ((‖z‖)⁻¹ • z) v‖ ≤ ‖v‖ :=
    norm_inner_invNorm_smul_le_norm hz0
  have hscale_nonneg : 0 ≤ C * (4 / width) := by
    exact
      mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hC_ge_one)
        (div_nonneg (by norm_num) hwidth_pos.le)
  calc
    ‖euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
        width φ v z‖
        =
          ‖deriv Real.smoothTransition
              ((‖z‖ - ((1 : ℝ) + width / 2)) / (width / 4)) *
            ((1 : ℝ) / (width / 4))‖ *
            ‖inner ℝ ((‖z‖)⁻¹ • z) v‖ * ‖φ z‖ := by
          simp [euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight,
            norm_mul, mul_assoc]
    _ ≤ (C * (4 / width) * ‖v‖) * ‖φ z‖ := by
          exact
            mul_le_mul_of_nonneg_right
              (mul_le_mul hprof hinner (norm_nonneg _) hscale_nonneg)
              (norm_nonneg _)

private theorem euclideanSobolevUnitBallAnnulusOuterOrientedRadialPairingWeight_norm_le
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width C : ℝ}
    (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    (hC_ge_one : 1 ≤ C)
    (hC : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ C)
    {φ : H → ℝ} {v z : H}
    (hz : z ∈ euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width) :
    ‖euclideanSobolevUnitBallAnnulusOuterOrientedRadialPairingWeight
        width φ v z‖ ≤
      (C * (4 / width) * ‖v‖) * ‖φ z‖ := by
  have hz0 : z ≠ 0 :=
    euclideanSobolevUnitBallAnnulusOuterTransitionCollar_ne_zero
      hwidth_le_quarter hz
  have hprof :
      ‖deriv Real.smoothTransition
          ((((3 / 2 : ℝ) - width / 2) - ‖z‖) / (width / 4)) *
        (-(1 : ℝ) / (width / 4))‖ ≤
        C * (4 / width) := by
    have hderiv :=
      annulus_outer_transition_profile_deriv_norm_le
        hwidth_pos hC
        (annulus_outer_transition_arg_mem_Icc_neg_two_two hwidth_pos hz)
    simpa [annulus_outer_transition_profile_deriv_eq] using hderiv
  have hinner : ‖inner ℝ ((‖z‖)⁻¹ • z) v‖ ≤ ‖v‖ :=
    norm_inner_invNorm_smul_le_norm hz0
  have hscale_nonneg : 0 ≤ C * (4 / width) := by
    exact
      mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hC_ge_one)
        (div_nonneg (by norm_num) hwidth_pos.le)
  calc
    ‖euclideanSobolevUnitBallAnnulusOuterOrientedRadialPairingWeight
        width φ v z‖
        =
          ‖deriv Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - ‖z‖) / (width / 4)) *
            (-(1 : ℝ) / (width / 4))‖ *
            ‖inner ℝ ((‖z‖)⁻¹ • z) v‖ * ‖φ z‖ := by
          simp [euclideanSobolevUnitBallAnnulusOuterOrientedRadialPairingWeight,
            norm_mul, mul_assoc]
    _ ≤ (C * (4 / width) * ‖v‖) * ‖φ z‖ := by
          exact
            mul_le_mul_of_nonneg_right
              (mul_le_mul hprof hinner (norm_nonneg _) hscale_nonneg)
              (norm_nonneg _)

private theorem euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight_norm_le
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {width C : ℝ}
    (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    (hC_ge_one : 1 ≤ C)
    (hC : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ C)
    {φ : H → ℝ} {v z : H}
    (hz :
      z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
        euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width) :
    ‖euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
        width φ v z‖ ≤
      (C * (4 / width) * ‖v‖) * ‖φ z‖ := by
  classical
  by_cases hz_inner :
      z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width
  · have hbound :=
      euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight_norm_le
        (φ := φ) (v := v) hwidth_pos hC_ge_one hC hz_inner
    simpa [euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight,
      hz_inner] using hbound
  · have hz_outer :
        z ∈ euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width := by
      rcases hz with hz_inner' | hz_outer
      · exact False.elim (hz_inner hz_inner')
      · exact hz_outer
    have hbound :=
      euclideanSobolevUnitBallAnnulusOuterOrientedRadialPairingWeight_norm_le
        (φ := φ) (v := v) hwidth_pos hwidth_le_quarter
        hC_ge_one hC hz_outer
    simpa [euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight,
      hz_inner] using hbound

private def euclideanSobolevUnitSphereRadialTrace
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (τ : H → ℝ) (z : H) : ℝ :=
  τ (((1 / ‖z‖) : ℝ) • z)

private noncomputable def euclideanSobolevUnitBallAnnulusGlueRadialTrace
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (width : ℝ) (τ : H → ℝ) (z : H) : ℝ :=
  by
    classical
    exact
      if z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width then
        euclideanSobolevUnitSphereRadialTrace τ z
      else
        0

private noncomputable def euclideanSobolevUnitBallAnnulusExplicitOrientedPairing
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H]
    (width : ℝ)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H) (u₀ u₁ : H → ℝ) : ℝ :=
  (∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
      euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
        width (φ : H → ℝ) v z • u₀ z
      ∂MeasureTheory.volume) +
    ∫ z in
      euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
        euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
      euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
        width (φ : H → ℝ) v z • u₁ z
      ∂MeasureTheory.volume

private noncomputable def euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H]
    (width : ℝ)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H) (τ : H → ℝ) : ℝ :=
  (∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
      euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
        width (φ : H → ℝ) v z •
          euclideanSobolevUnitSphereRadialTrace τ z
      ∂MeasureTheory.volume) +
    ∫ z in
      euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
        euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
      euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
        width (φ : H → ℝ) v z •
          euclideanSobolevUnitBallAnnulusGlueRadialTrace width τ z
      ∂MeasureTheory.volume

/--
Bochner integrability of the explicit oriented collar pairings.
-/
private structure EuclideanSobolevUnitBallAnnulusExplicitOrientedPairingIntegrable
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H]
    (width : ℝ)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H) (u₀ u₁ : H → ℝ) : Prop where
  unit :
    Integrable
      (fun z : H ↦
        euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
          width (φ : H → ℝ) v z • u₀ z)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallInnerTransitionCollar H width))
  annulus :
    Integrable
      (fun z : H ↦
        euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
          width (φ : H → ℝ) v z • u₁ z)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
          euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width))

/--
Bochner integrability of the trace-inserted oriented collar pairings.
-/
private structure EuclideanSobolevUnitBallAnnulusExactTraceOrientedPairingIntegrable
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H]
    (width : ℝ)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H) (τ : H → ℝ) : Prop where
  unit :
    Integrable
      (fun z : H ↦
        euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
          width (φ : H → ℝ) v z •
            euclideanSobolevUnitSphereRadialTrace τ z)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallInnerTransitionCollar H width))
  annulus :
    Integrable
      (fun z : H ↦
        euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
          width (φ : H → ℝ) v z •
            euclideanSobolevUnitBallAnnulusGlueRadialTrace width τ z)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
          euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width))

/--
%%handwave
name:
  Integrable sphere traces give integrable trace-inserted collar pairings
statement:
  If the common unit-sphere trace is integrable on the sphere, then for every
  fixed smooth test function, direction, and standard collar width, the
  oriented collar pairings obtained by inserting the radial trace are Bochner
  integrable.
proof:
  The trace integrability on the sphere gives integrability of the radial
  extension on each transition collar by polar coordinates.  The oriented
  radial weights are bounded on the collars by the fixed profile bound, the
  test-function bound, and the fixed direction.  Multiplication by these
  bounded measurable weights preserves integrability.  On the outer annular
  collar the inserted trace is zero, so the contribution is integrable
  trivially; the inner and outer annular pieces are then combined over their
  union.
-/
private theorem euclideanSobolev_unit_ball_annulus_exact_oriented_pairing_integrable_of_weighted_trace
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v)
    {width : ℝ} (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) :
    EuclideanSobolevUnitBallAnnulusExactTraceOrientedPairingIntegrable
      (H := H) width φ v τ := by
  classical
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let S₀ : Set H := euclideanSobolevUnitBallInnerTransitionCollar H width
  let Sinner : Set H :=
    euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width
  let Souter : Set H :=
    euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width
  let S₁ : Set H := Sinner ∪ Souter
  obtain ⟨Cprofile, hCprofile_ge_one, hCprofile⟩ :=
    exists_smoothTransition_deriv_bound_Icc_neg_two_two
  rcases
      φ.compact_support.exists_bound_of_continuousOn
        φ.smooth.continuous.continuousOn with
    ⟨B₀, hB₀⟩
  let B : ℝ := max B₀ 0
  have hB_nonneg : 0 ≤ B := le_max_right B₀ 0
  have hφ_bound : ∀ z : H, ‖(φ : H → ℝ) z‖ ≤ B := by
    intro z
    by_cases hz : z ∈ tsupport (φ : H → ℝ)
    · exact (hB₀ z hz).trans (le_max_left B₀ 0)
    · have hzero : (φ : H → ℝ) z = 0 :=
        image_eq_zero_of_notMem_tsupport hz
      simp [B, hzero, hB_nonneg]
  have hS₀_meas : MeasurableSet S₀ :=
    (euclideanSobolevUnitBallInnerTransitionCollar_isOpen
      (H := H) width).measurableSet
  have hSinner_meas : MeasurableSet Sinner :=
    (euclideanSobolevUnitBallAnnulusInnerTransitionCollar_isOpen
      (H := H) width).measurableSet
  have hSouter_meas : MeasurableSet Souter :=
    (euclideanSobolevUnitBallAnnulusOuterTransitionCollar_isOpen
      (H := H) width).measurableSet
  have hS₁_meas : MeasurableSet S₁ := hSinner_meas.union hSouter_meas
  have hτ_sphere :
      Integrable
        (fun θ : Metric.sphere (0 : H) 1 ↦ τ (θ : H))
        ((MeasureTheory.volume : Measure H).toSphere) :=
    hτ_weight.1
  have htrace_unit :
      Integrable
        (fun z : H ↦ euclideanSobolevUnitSphereRadialTrace τ z)
        (MeasureTheory.volume.restrict S₀) := by
    have hpos : 0 < (1 : ℝ) - width := by
      nlinarith [hwidth_le_quarter]
    have hlt : (1 : ℝ) - width < 1 := by
      linarith
    simpa [S₀, euclideanSobolevUnitSphereRadialTrace,
      euclideanSobolevUnitBallInnerTransitionCollar] using
      euclideanSobolev_unit_sphere_integrable_radial_extension_on_annulus
        (H := H) (τ := τ) (a := (1 : ℝ) - width) (b := 1)
        hpos hlt hτ_sphere
  have htrace_inner :
      Integrable
        (fun z : H ↦ euclideanSobolevUnitSphereRadialTrace τ z)
        (MeasureTheory.volume.restrict Sinner) := by
    have hlt : (1 : ℝ) < 1 + width := by
      linarith
    simpa [Sinner, euclideanSobolevUnitSphereRadialTrace,
      euclideanSobolevUnitBallAnnulusInnerTransitionCollar] using
      euclideanSobolev_unit_sphere_integrable_radial_extension_on_annulus
        (H := H) (τ := τ) (a := (1 : ℝ)) (b := 1 + width)
        (by norm_num) hlt hτ_sphere
  let K : ℝ := (Cprofile * (4 / width) * ‖v‖) * B
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hderiv_meas :
      Measurable (fun t : ℝ ↦ deriv Real.smoothTransition t) := by
    have hsmooth : ContDiff ℝ ∞ Real.smoothTransition :=
      Real.smoothTransition.contDiff
    exact (hsmooth.continuous_deriv (by simp)).measurable
  have hnorm_inv_meas :
      Measurable (fun z : H ↦ (‖z‖ : ℝ)⁻¹) :=
    (continuous_norm.measurable).inv
  have hinner_meas :
      Measurable (fun z : H ↦ inner ℝ (((‖z‖)⁻¹ : ℝ) • z) v) := by
    have hinner_base :
        Measurable (fun z : H ↦ inner ℝ z v) :=
      (continuous_id.inner continuous_const).measurable
    have hmul :
        Measurable (fun z : H ↦ (‖z‖ : ℝ)⁻¹ * inner ℝ z v) :=
      hnorm_inv_meas.mul hinner_base
    convert hmul using 1
    ext z
    simp [inner_smul_left]
  have hφ_meas : Measurable (φ : H → ℝ) :=
    φ.smooth.continuous.measurable
  have hunit_weight_meas :
      Measurable
        (fun z : H ↦
          euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
            width (φ : H → ℝ) v z) := by
    have harg :
        Measurable
          (fun z : H ↦
            (((1 : ℝ) - width / 2 - ‖z‖) / (width / 4))) := by
      fun_prop
    have hprof :
        Measurable
          (fun z : H ↦
            deriv Real.smoothTransition
              (((1 : ℝ) - width / 2 - ‖z‖) / (width / 4))) :=
      hderiv_meas.comp harg
    simpa [euclideanSobolevUnitBallInnerOrientedRadialPairingWeight,
      mul_assoc] using
      (((hprof.mul measurable_const).mul hinner_meas).mul hφ_meas)
  have hannulus_inner_weight_meas :
      Measurable
        (fun z : H ↦
          euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
            width (φ : H → ℝ) v z) := by
    have harg :
        Measurable
          (fun z : H ↦
            ((‖z‖ - ((1 : ℝ) + width / 2)) / (width / 4))) := by
      fun_prop
    have hprof :
        Measurable
          (fun z : H ↦
            deriv Real.smoothTransition
              ((‖z‖ - ((1 : ℝ) + width / 2)) / (width / 4))) :=
      hderiv_meas.comp harg
    simpa [euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight,
      mul_assoc] using
      (((hprof.mul measurable_const).mul hinner_meas).mul hφ_meas)
  have hannulus_outer_weight_meas :
      Measurable
        (fun z : H ↦
          euclideanSobolevUnitBallAnnulusOuterOrientedRadialPairingWeight
            width (φ : H → ℝ) v z) := by
    have harg :
        Measurable
          (fun z : H ↦
            ((((3 / 2 : ℝ) - width / 2) - ‖z‖) /
              (width / 4))) := by
      fun_prop
    have hprof :
        Measurable
          (fun z : H ↦
            deriv Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - ‖z‖) /
                (width / 4))) :=
      hderiv_meas.comp harg
    simpa [euclideanSobolevUnitBallAnnulusOuterOrientedRadialPairingWeight,
      mul_assoc] using
      (((hprof.mul measurable_const).mul hinner_meas).mul hφ_meas)
  have hannulus_weight_meas :
      Measurable
        (fun z : H ↦
          euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
            width (φ : H → ℝ) v z) := by
    simpa [euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight]
      using
        Measurable.ite
          (p := fun z : H ↦
            z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width)
          hSinner_meas hannulus_inner_weight_meas
          hannulus_outer_weight_meas
  have hunit_weight_aesm :
      AEStronglyMeasurable
        (fun z : H ↦
          euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
            width (φ : H → ℝ) v z)
        (MeasureTheory.volume.restrict S₀) := by
    exact hunit_weight_meas.aestronglyMeasurable
  have hunit_weight_bound :
      ∀ᵐ z ∂MeasureTheory.volume.restrict S₀,
        ‖euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
            width (φ : H → ℝ) v z‖ ≤ K := by
    refine ae_restrict_of_forall_mem hS₀_meas ?_
    intro z hz
    have hbound :=
      euclideanSobolevUnitBallInnerOrientedRadialPairingWeight_norm_le
        (φ := (φ : H → ℝ)) (v := v)
        hwidth_pos hwidth_le_quarter hCprofile_ge_one hCprofile
        (by simpa [S₀] using hz)
    calc
      ‖euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
          width (φ : H → ℝ) v z‖
          ≤ (Cprofile * (4 / width) * ‖v‖) * ‖(φ : H → ℝ) z‖ := hbound
      _ ≤ (Cprofile * (4 / width) * ‖v‖) * B := by
        exact mul_le_mul_of_nonneg_left (hφ_bound z)
          (by positivity)
      _ = K := rfl
  have hunit_int :
      Integrable
        (fun z : H ↦
          euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
            width (φ : H → ℝ) v z •
            euclideanSobolevUnitSphereRadialTrace τ z)
        (MeasureTheory.volume.restrict S₀) := by
    exact htrace_unit.bdd_smul K hunit_weight_aesm hunit_weight_bound
  have hinner_weight_aesm :
      AEStronglyMeasurable
        (fun z : H ↦
          euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
            width (φ : H → ℝ) v z)
        (MeasureTheory.volume.restrict Sinner) := by
    exact hannulus_weight_meas.aestronglyMeasurable
  have hinner_weight_bound :
      ∀ᵐ z ∂MeasureTheory.volume.restrict Sinner,
        ‖euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
            width (φ : H → ℝ) v z‖ ≤ K := by
    refine ae_restrict_of_forall_mem hSinner_meas ?_
    intro z hz
    have hz_union :
        z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
          euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width :=
      Or.inl (by simpa [Sinner] using hz)
    have hbound :=
      euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight_norm_le
        (φ := (φ : H → ℝ)) (v := v)
        hwidth_pos hwidth_le_quarter hCprofile_ge_one hCprofile hz_union
    calc
      ‖euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
          width (φ : H → ℝ) v z‖
          ≤ (Cprofile * (4 / width) * ‖v‖) * ‖(φ : H → ℝ) z‖ := hbound
      _ ≤ (Cprofile * (4 / width) * ‖v‖) * B := by
        exact mul_le_mul_of_nonneg_left (hφ_bound z)
          (by positivity)
      _ = K := rfl
  have hinner_int :
      Integrable
        (fun z : H ↦
          euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
            width (φ : H → ℝ) v z •
            euclideanSobolevUnitBallAnnulusGlueRadialTrace width τ z)
        (MeasureTheory.volume.restrict Sinner) := by
    have hraw :
        Integrable
          (fun z : H ↦
            euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
              width (φ : H → ℝ) v z •
              euclideanSobolevUnitSphereRadialTrace τ z)
          (MeasureTheory.volume.restrict Sinner) :=
      htrace_inner.bdd_smul K hinner_weight_aesm hinner_weight_bound
    refine hraw.congr ?_
    refine ae_restrict_of_forall_mem hSinner_meas ?_
    intro z hz
    have hz_inner :
        z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width := by
      simpa [Sinner] using hz
    simp [euclideanSobolevUnitBallAnnulusGlueRadialTrace, hz_inner]
  have houter_int :
      Integrable
        (fun z : H ↦
          euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
            width (φ : H → ℝ) v z •
            euclideanSobolevUnitBallAnnulusGlueRadialTrace width τ z)
        (MeasureTheory.volume.restrict Souter) := by
    refine
      (integrable_zero H ℝ (MeasureTheory.volume.restrict Souter) :
        Integrable (fun _ : H ↦ (0 : ℝ))
          (MeasureTheory.volume.restrict Souter)).congr ?_
    refine ae_restrict_of_forall_mem hSouter_meas ?_
    intro z hz
    have hz_not_inner :
        z ∉ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width := by
      intro hz_inner
      exact
        (euclideanSobolevUnitBallAnnulusTransitionCollars_disjoint
          (H := H) hwidth_le_quarter).le_bot
          ⟨hz_inner, by simpa [Souter] using hz⟩
    simp [euclideanSobolevUnitBallAnnulusGlueRadialTrace, hz_not_inner]
  have hannulus_int :
      Integrable
        (fun z : H ↦
          euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
            width (φ : H → ℝ) v z •
            euclideanSobolevUnitBallAnnulusGlueRadialTrace width τ z)
        (MeasureTheory.volume.restrict S₁) := by
    have hinner_on :
        IntegrableOn
          (fun z : H ↦
            euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
              width (φ : H → ℝ) v z •
              euclideanSobolevUnitBallAnnulusGlueRadialTrace width τ z)
          Sinner MeasureTheory.volume := by
      simpa [IntegrableOn, Sinner] using hinner_int
    have houter_on :
        IntegrableOn
          (fun z : H ↦
            euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
              width (φ : H → ℝ) v z •
              euclideanSobolevUnitBallAnnulusGlueRadialTrace width τ z)
          Souter MeasureTheory.volume := by
      simpa [IntegrableOn, Souter] using houter_int
    have hunion_on := hinner_on.union houter_on
    simpa [IntegrableOn, S₁] using hunion_on
  exact ⟨by simpa [S₀] using hunit_int, by simpa [S₁, Sinner, Souter] using hannulus_int⟩

/--
%%handwave
name:
  Weak derivative identities give integrability of the explicit collar terms
statement:
  Suppose the two local functions satisfy the weak derivative identity on the
  unit ball and on the annulus, and suppose the ambient glued left pairing is
  integrable for a fixed test function and direction.  Then, for every
  standard radial collar width, the two explicit oriented transition-collar
  pairings are Bochner integrable.
proof:
  Build the standard radial collar cutoffs of the given width and multiply
  them by the fixed ambient test.  The weak derivative identities give
  integrability of the derivatives of these products against the two local
  functions.  The assumed glued left-pairing integrability gives integrability
  of the main product terms, after restriction to the ball and annulus and
  multiplication by the bounded cutoffs.  Subtracting the main terms leaves
  exactly the derivative-of-cutoff collar terms, and the standard radial
  formulas identify them with the explicit oriented weights on the transition
  collars.
-/
private theorem euclideanSobolev_unit_ball_annulus_explicit_oriented_pairing_integrable_of_weakDerivative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ} {du₀ du₁ : H → H →L[ℝ] ℝ}
    (hunit : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u₀ du₀)
    (hannulus : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H) u₁ du₁)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hleft_int : Integrable
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0))
      (MeasureTheory.volume.restrict Set.univ))
    {width : ℝ} (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) :
    EuclideanSobolevUnitBallAnnulusExplicitOrientedPairingIntegrable
      (H := H) width φ v u₀ u₁ := by
  classical
  obtain ⟨χ⟩ :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_exists_radial_collar_cutoff_pair
      (H := H) hwidth_pos hwidth_le_quarter
  let B : Set H := Metric.ball (0 : H) 1
  let A : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let S₀ : Set H := euclideanSobolevUnitBallInnerTransitionCollar H width
  let S₁ : Set H :=
    euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
      euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width
  let μB : Measure H := MeasureTheory.volume.restrict B
  let μA : Measure H := MeasureTheory.volume.restrict A
  let unitTest :
      SmoothCompactlySupportedManifoldCoordinateFunction B :=
    { toFun := fun z : H ↦ χ.unitCutoff z * (φ : H → ℝ) z
      smooth := χ.unitCutoff_smooth.mul φ.smooth
      support_subset := by
        exact (tsupport_mul_subset_left).trans χ.unitCutoff_tsupport_subset
      compact_support := by
        exact χ.unitCutoff_compact_support.of_isClosed_subset
          (isClosed_tsupport _) tsupport_mul_subset_left }
  let annulusTest :
      SmoothCompactlySupportedManifoldCoordinateFunction A :=
    { toFun := fun z : H ↦ χ.annulusCutoff z * (φ : H → ℝ) z
      smooth := χ.annulusCutoff_smooth.mul φ.smooth
      support_subset := by
        exact (tsupport_mul_subset_left).trans χ.annulusCutoff_tsupport_subset
      compact_support := by
        exact χ.annulusCutoff_compact_support.of_isClosed_subset
          (isClosed_tsupport _) tsupport_mul_subset_left }
  have hB_meas : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hA_meas : MeasurableSet A :=
    (euclideanSobolevUnitBallReflectionAnnulus_isOpen (H := H)).measurableSet
  have hS₀_meas : MeasurableSet S₀ :=
    (euclideanSobolevUnitBallInnerTransitionCollar_isOpen
      (H := H) width).measurableSet
  have hS₁_meas : MeasurableSet S₁ :=
    (euclideanSobolevUnitBallAnnulusInnerTransitionCollar_isOpen
        (H := H) width).measurableSet.union
      (euclideanSobolevUnitBallAnnulusOuterTransitionCollar_isOpen
        (H := H) width).measurableSet
  have hunit_target_int :
      Integrable
        (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • u₀ z) μB := by
    have hμ_le : μB ≤ MeasureTheory.volume.restrict Set.univ :=
      Measure.restrict_mono (Set.subset_univ _) le_rfl
    have hglobal_local := _hleft_int.mono_measure hμ_le
    refine hglobal_local.congr ?_
    refine ae_restrict_of_forall_mem hB_meas ?_
    intro z hz
    have hz_norm : ‖z‖ < 1 := by
      simpa [B, Metric.mem_ball, dist_eq_norm] using hz
    simp [hz_norm]
  have hannulus_target_int :
      Integrable
        (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • u₁ z) μA := by
    have hμ_le : μA ≤ MeasureTheory.volume.restrict Set.univ :=
      Measure.restrict_mono (Set.subset_univ _) le_rfl
    have hglobal_local := _hleft_int.mono_measure hμ_le
    refine hglobal_local.congr ?_
    refine ae_restrict_of_forall_mem hA_meas ?_
    intro z hz
    have hz_inner : 1 < ‖z‖ := by
      simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hz.1
    have hz_not_unit : ¬ ‖z‖ < 1 := by
      linarith
    have hz_outer : ‖z‖ < (3 / 2 : ℝ) := by
      simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hz.2
    simp [hz_not_unit, hz_outer]
  let Umain : H → ℝ := fun z ↦
    χ.unitCutoff z • ((fderiv ℝ (φ : H → ℝ) z v) • u₀ z)
  let Uerr : H → ℝ := fun z ↦
    ((fderiv ℝ χ.unitCutoff z v) * φ z) • u₀ z
  let Afull : H → ℝ := fun z ↦
    (fderiv ℝ (annulusTest : H → ℝ) z v) • u₁ z
  let Amain : H → ℝ := fun z ↦
    χ.annulusCutoff z • ((fderiv ℝ (φ : H → ℝ) z v) • u₁ z)
  let Aerr : H → ℝ := fun z ↦
    ((fderiv ℝ χ.annulusCutoff z v) * φ z) • u₁ z
  have hunit_main_int : Integrable Umain μB := by
    have hcut :
        AEStronglyMeasurable χ.unitCutoff μB :=
      χ.unitCutoff_smooth.continuous.aestronglyMeasurable
    have hmain_meas : AEStronglyMeasurable Umain μB := by
      exact hcut.smul hunit_target_int.aestronglyMeasurable
    refine hunit_target_int.mono hmain_meas ?_
    refine ae_restrict_of_forall_mem hB_meas ?_
    intro z _hz
    calc
      ‖Umain z‖ =
          ‖χ.unitCutoff z‖ *
            ‖(fderiv ℝ (φ : H → ℝ) z v) • u₀ z‖ := by
          simp [Umain]
      _ ≤ 1 * ‖(fderiv ℝ (φ : H → ℝ) z v) • u₀ z‖ :=
          mul_le_mul_of_nonneg_right
            (χ.unitCutoff_norm_le_one z) (norm_nonneg _)
      _ = ‖(fderiv ℝ (φ : H → ℝ) z v) • u₀ z‖ := one_mul _
  have hannulus_main_int : Integrable Amain μA := by
    have hcut :
        AEStronglyMeasurable χ.annulusCutoff μA :=
      χ.annulusCutoff_smooth.continuous.aestronglyMeasurable
    have hmain_meas : AEStronglyMeasurable Amain μA := by
      exact hcut.smul hannulus_target_int.aestronglyMeasurable
    refine hannulus_target_int.mono hmain_meas ?_
    refine ae_restrict_of_forall_mem hA_meas ?_
    intro z _hz
    calc
      ‖Amain z‖ =
          ‖χ.annulusCutoff z‖ *
            ‖(fderiv ℝ (φ : H → ℝ) z v) • u₁ z‖ := by
          simp [Amain]
      _ ≤ 1 * ‖(fderiv ℝ (φ : H → ℝ) z v) • u₁ z‖ :=
          mul_le_mul_of_nonneg_right
            (χ.annulusCutoff_norm_le_one z) (norm_nonneg _)
      _ = ‖(fderiv ℝ (φ : H → ℝ) z v) • u₁ z‖ := one_mul _
  have hunit_full_int :
      Integrable
        (fun z : H ↦ (fderiv ℝ (unitTest : H → ℝ) z v) • u₀ z) μB := by
    simpa [B, μB, unitTest] using (hunit unitTest v).1
  have hannulus_full_int : Integrable Afull μA := by
    simpa [A, μA, Afull, annulusTest] using (hannulus annulusTest v).1
  have hunit_sum_ae :
      (fun z : H ↦ (fderiv ℝ (unitTest : H → ℝ) z v) • u₀ z)
        =ᵐ[μB] fun z : H ↦ Umain z + Uerr z := by
    exact ae_of_all μB fun z ↦ by
      have hcutdiff : DifferentiableAt ℝ χ.unitCutoff z :=
        χ.unitCutoff_smooth.differentiable (by simp) z
      have hφdiff : DifferentiableAt ℝ (φ : H → ℝ) z :=
        (φ.smooth.differentiable (by simp)) z
      change
        (fderiv ℝ
            (fun y : H ↦ χ.unitCutoff y * (φ : H → ℝ) y) z v) •
            u₀ z =
          Umain z + Uerr z
      rw [fderiv_fun_mul hcutdiff hφdiff]
      simp [Umain, Uerr, smul_eq_mul]
      ring
  have hannulus_sum_ae :
      Afull =ᵐ[μA] fun z : H ↦ Amain z + Aerr z := by
    exact ae_of_all μA fun z ↦ by
      have hcutdiff : DifferentiableAt ℝ χ.annulusCutoff z :=
        χ.annulusCutoff_smooth.differentiable (by simp) z
      have hφdiff : DifferentiableAt ℝ (φ : H → ℝ) z :=
        (φ.smooth.differentiable (by simp)) z
      dsimp [Afull]
      change
        (fderiv ℝ
            (fun y : H ↦ χ.annulusCutoff y * (φ : H → ℝ) y) z v) •
            u₁ z =
          Amain z + Aerr z
      rw [fderiv_fun_mul hcutdiff hφdiff]
      simp [Amain, Aerr, smul_eq_mul]
      ring
  have hunit_err_int_B : Integrable Uerr μB := by
    have hsum_int : Integrable (fun z : H ↦ Umain z + Uerr z) μB :=
      hunit_full_int.congr hunit_sum_ae
    have hdiff_int :
        Integrable (fun z : H ↦ (Umain z + Uerr z) - Umain z) μB :=
      hsum_int.sub hunit_main_int
    refine hdiff_int.congr ?_
    exact ae_of_all μB fun z ↦ by simp
  have hannulus_err_int_A : Integrable Aerr μA := by
    have hsum_int : Integrable (fun z : H ↦ Amain z + Aerr z) μA :=
      hannulus_full_int.congr hannulus_sum_ae
    have hdiff_int :
        Integrable (fun z : H ↦ (Amain z + Aerr z) - Amain z) μA :=
      hsum_int.sub hannulus_main_int
    refine hdiff_int.congr ?_
    exact ae_of_all μA fun z ↦ by simp
  have hS₀_subset_B : S₀ ⊆ B := by
    intro z hz
    simpa [S₀, B, Metric.mem_ball, dist_eq_norm] using hz.2
  have hS₁_subset_A : S₁ ⊆ A := by
    intro z hz
    rcases hz with hz_inner | hz_outer
    · have hlt : ‖z‖ < (3 / 2 : ℝ) := by
        nlinarith [hz_inner.2, hwidth_le_quarter]
      exact ⟨by simpa [S₁] using hz_inner.1, by
        simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hlt⟩
    · have hgt : 1 < ‖z‖ := by
        nlinarith [hz_outer.1, hwidth_le_quarter]
      exact ⟨by simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hgt,
        by simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hz_outer.2⟩
  have hunit_err_int_S₀ : Integrable Uerr (MeasureTheory.volume.restrict S₀) :=
    hunit_err_int_B.mono_measure
      (by
        simpa [μB, B, S₀] using
          Measure.restrict_mono hS₀_subset_B le_rfl)
  have hannulus_err_int_S₁ : Integrable Aerr (MeasureTheory.volume.restrict S₁) :=
    hannulus_err_int_A.mono_measure
      (by
        simpa [μA, A, S₁] using
          Measure.restrict_mono hS₁_subset_A le_rfl)
  refine ⟨?_, ?_⟩
  · refine hunit_err_int_S₀.congr ?_
    refine ae_restrict_of_forall_mem hS₀_meas ?_
    intro z hz
    dsimp [Uerr]
    rw [χ.unitCutoff_fderiv_apply_eq_oriented_profile_of_inner_transition
      hwidth_le_quarter hz]
    simp [euclideanSobolevUnitBallInnerOrientedRadialPairingWeight,
      mul_assoc]
  · refine hannulus_err_int_S₁.congr ?_
    refine ae_restrict_of_forall_mem hS₁_meas ?_
    intro z hz
    rcases hz with hz_inner | hz_outer
    · dsimp [Aerr]
      rw [χ.annulusCutoff_fderiv_apply_eq_oriented_profile_of_inner_transition
        hwidth_pos hwidth_le_quarter hz_inner]
      simp [euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight,
        euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight,
        hz_inner, mul_assoc]
    · have hz_not_inner :
          z ∉ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width := by
        intro hz_inner
        exact
          (euclideanSobolevUnitBallAnnulusTransitionCollars_disjoint
            (H := H) hwidth_le_quarter).le_bot ⟨hz_inner, hz_outer⟩
      dsimp [Aerr]
      rw [χ.annulusCutoff_fderiv_apply_eq_oriented_profile_of_outer_transition
        hwidth_pos hwidth_le_quarter hz_outer]
      simp [euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight,
        euclideanSobolevUnitBallAnnulusOuterOrientedRadialPairingWeight,
        hz_not_inner, mul_assoc]

/--
%%handwave
name:
  Bochner comparison for weighted scalar integrals
statement:
  If two weighted scalar functions are Bochner integrable on a region, then
  the distance between their integrals is bounded by the integral of the
  weight times the pointwise scalar error.
proof:
  Apply the standard Bochner estimate bounding the distance of two integrals
  by the lower integral of the pointwise extended distance.  For scalar
  multiples, the pointwise distance is exactly the absolute value of the
  weight times the absolute value of the scalar difference.
-/
private theorem dist_setIntegral_smul_le_lintegral_weight_error
    {α : Type} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {a u t : α → ℝ}
    (hu : Integrable (fun x ↦ a x • u x) (μ.restrict s))
    (ht : Integrable (fun x ↦ a x • t x) (μ.restrict s)) :
    dist (∫ x in s, a x • u x ∂μ) (∫ x in s, a x • t x ∂μ) ≤
      (∫⁻ x in s, ENNReal.ofReal (‖a x‖ * ‖u x - t x‖) ∂μ).toReal := by
  have h :=
    dist_integral_le_lintegral_edist
      (μ := μ.restrict s)
      (f := fun x ↦ a x • u x)
      (g := fun x ↦ a x • t x)
      hu ht
  have hlin :
      (∫⁻ x in s, edist (a x • u x) (a x • t x) ∂μ) =
        ∫⁻ x in s, ENNReal.ofReal (‖a x‖ * ‖u x - t x‖) ∂μ := by
    refine lintegral_congr fun x ↦ ?_
    rw [edist_eq_enorm_sub, ← ofReal_norm]
    congr 1
    rw [← smul_sub, norm_smul]
  rw [hlin] at h
  exact h

private theorem integrable_weighted_scalar_of_integrable_trace_and_error
    {α : Type} [MeasurableSpace α] {μ : Measure α}
    {a u t : α → ℝ}
    (ha : Measurable a) (hu : AEStronglyMeasurable u μ)
    (htrace : Integrable (fun x ↦ a x • t x) μ)
    (herror :
      (∫⁻ x, ENNReal.ofReal (‖a x‖ * ‖u x - t x‖) ∂μ) ≠
        (∞ : ℝ≥0∞)) :
    Integrable (fun x ↦ a x • u x) μ := by
  have hau_aesm :
      AEStronglyMeasurable (fun x ↦ a x • u x) μ := by
    simpa [smul_eq_mul] using ha.aestronglyMeasurable.mul hu
  have herror_aesm :
      AEStronglyMeasurable (fun x ↦ a x • (u x - t x)) μ := by
    have hsub := hau_aesm.sub htrace.aestronglyMeasurable
    convert hsub using 1
    ext x
    simp [smul_eq_mul]
    ring
  have herror_hfi :
      HasFiniteIntegral (fun x ↦ a x • (u x - t x)) μ := by
    have hlt :
        (∫⁻ x, ENNReal.ofReal (‖a x‖ * ‖u x - t x‖) ∂μ) <
          (∞ : ℝ≥0∞) :=
      lt_top_iff_ne_top.mpr herror
    have hnorm :
        (∫⁻ x, ‖a x • (u x - t x)‖ₑ ∂μ) =
          ∫⁻ x, ENNReal.ofReal (‖a x‖ * ‖u x - t x‖) ∂μ := by
      refine lintegral_congr fun x ↦ ?_
      rw [← ofReal_norm]
      simp
    rw [hasFiniteIntegral_iff_enorm, hnorm]
    exact hlt
  have herror_int :
      Integrable (fun x ↦ a x • (u x - t x)) μ :=
    ⟨herror_aesm, herror_hfi⟩
  have hsum := htrace.add herror_int
  convert hsum using 1
  ext x
  simp [smul_eq_mul]
  ring

/--
%%handwave
name:
  Bochner comparison for the two oriented collar pairings
statement:
  If the explicit and trace-inserted oriented collar integrands are Bochner
  integrable, then the distance between the explicit pairing and the
  trace-inserted pairing is bounded by the sum of the two weighted
  pointwise-error integrals, one over the unit collar and one over the
  annular collars.
proof:
  Split the distance between the two sums by the triangle inequality.  On
  each collar apply the weighted scalar Bochner comparison.
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_oriented_radial_trace_error_dist_le_lintegrals
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (width : ℝ)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hunit_u : Integrable
      (fun z : H ↦
        euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
          width (φ : H → ℝ) v z • u₀ z)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallInnerTransitionCollar H width)))
    (hunit_trace : Integrable
      (fun z : H ↦
        euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
          width (φ : H → ℝ) v z •
            euclideanSobolevUnitSphereRadialTrace τ z)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallInnerTransitionCollar H width)))
    (hannulus_u : Integrable
      (fun z : H ↦
        euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
          width (φ : H → ℝ) v z • u₁ z)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
          euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width)))
    (hannulus_trace : Integrable
      (fun z : H ↦
        euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
          width (φ : H → ℝ) v z •
            euclideanSobolevUnitBallAnnulusGlueRadialTrace width τ z)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
          euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width))) :
    dist
      (euclideanSobolevUnitBallAnnulusExplicitOrientedPairing
        (H := H) width φ v u₀ u₁)
      (euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing
        (H := H) width φ v τ) ≤
      (∫⁻ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
        ENNReal.ofReal
          (‖euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
              width (φ : H → ℝ) v z‖ *
            ‖u₀ z - euclideanSobolevUnitSphereRadialTrace τ z‖)
        ∂MeasureTheory.volume).toReal +
      (∫⁻ z in
          euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
            euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
        ENNReal.ofReal
          (‖euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
              width (φ : H → ℝ) v z‖ *
            ‖u₁ z -
              euclideanSobolevUnitBallAnnulusGlueRadialTrace width τ z‖)
        ∂MeasureTheory.volume).toReal := by
  let μ : Measure H := MeasureTheory.volume
  let S₀ : Set H := euclideanSobolevUnitBallInnerTransitionCollar H width
  let S₁ : Set H :=
    euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
      euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width
  let a₀ : H → ℝ :=
    fun z ↦ euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
      width (φ : H → ℝ) v z
  let a₁ : H → ℝ :=
    fun z ↦ euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
      width (φ : H → ℝ) v z
  let t₀ : H → ℝ := euclideanSobolevUnitSphereRadialTrace τ
  let t₁ : H → ℝ :=
    euclideanSobolevUnitBallAnnulusGlueRadialTrace width τ
  have hunit :
      dist (∫ z in S₀, a₀ z • u₀ z ∂μ)
          (∫ z in S₀, a₀ z • t₀ z ∂μ) ≤
        (∫⁻ z in S₀, ENNReal.ofReal (‖a₀ z‖ * ‖u₀ z - t₀ z‖)
          ∂μ).toReal := by
    exact
      dist_setIntegral_smul_le_lintegral_weight_error
        (μ := μ) (s := S₀) (a := a₀) (u := u₀) (t := t₀)
        (by simpa [μ, S₀, a₀] using hunit_u)
        (by simpa [μ, S₀, a₀, t₀] using hunit_trace)
  have hannulus :
      dist (∫ z in S₁, a₁ z • u₁ z ∂μ)
          (∫ z in S₁, a₁ z • t₁ z ∂μ) ≤
        (∫⁻ z in S₁, ENNReal.ofReal (‖a₁ z‖ * ‖u₁ z - t₁ z‖)
          ∂μ).toReal := by
    exact
      dist_setIntegral_smul_le_lintegral_weight_error
        (μ := μ) (s := S₁) (a := a₁) (u := u₁) (t := t₁)
        (by simpa [μ, S₁, a₁] using hannulus_u)
        (by simpa [μ, S₁, a₁, t₁] using hannulus_trace)
  calc
    dist
      (euclideanSobolevUnitBallAnnulusExplicitOrientedPairing
        (H := H) width φ v u₀ u₁)
      (euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing
        (H := H) width φ v τ)
        =
      dist ((∫ z in S₀, a₀ z • u₀ z ∂μ) +
          ∫ z in S₁, a₁ z • u₁ z ∂μ)
        ((∫ z in S₀, a₀ z • t₀ z ∂μ) +
          ∫ z in S₁, a₁ z • t₁ z ∂μ) := by
          rfl
    _ ≤ dist (∫ z in S₀, a₀ z • u₀ z ∂μ)
          (∫ z in S₀, a₀ z • t₀ z ∂μ) +
        dist (∫ z in S₁, a₁ z • u₁ z ∂μ)
          (∫ z in S₁, a₁ z • t₁ z ∂μ) :=
          dist_add_add_le _ _ _ _
    _ ≤
        (∫⁻ z in S₀, ENNReal.ofReal (‖a₀ z‖ * ‖u₀ z - t₀ z‖)
          ∂μ).toReal +
        (∫⁻ z in S₁, ENNReal.ofReal (‖a₁ z‖ * ‖u₁ z - t₁ z‖)
          ∂μ).toReal :=
          add_le_add hunit hannulus
    _ =
      (∫⁻ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
        ENNReal.ofReal
          (‖euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
              width (φ : H → ℝ) v z‖ *
            ‖u₀ z - euclideanSobolevUnitSphereRadialTrace τ z‖)
        ∂MeasureTheory.volume).toReal +
      (∫⁻ z in
          euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
            euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
        ENNReal.ofReal
          (‖euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
              width (φ : H → ℝ) v z‖ *
            ‖u₁ z -
              euclideanSobolevUnitBallAnnulusGlueRadialTrace width τ z‖)
        ∂MeasureTheory.volume).toReal := by
          rfl

/--
%%handwave
name:
  Downstream Sobolev and trace hypotheses supply the Bochner comparison
statement:
  Under the local weak derivative hypotheses and the integrability of the
  glued left pairing for a fixed test function and direction, together with
  integrability of the common boundary trace on the sphere, the Bochner
  comparison applies to the explicit and trace-inserted oriented collar
  pairings.
proof:
  The weak derivative identities and the glued left-pairing integrability
  give Bochner integrability of the two explicit collar terms.  The sphere
  trace integrability gives Bochner integrability of the two trace-inserted
  collar terms by polar coordinates and boundedness of the radial weights.
  Apply the Bochner comparison for the two oriented collar pairings.
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_oriented_radial_trace_error_dist_le_lintegrals_of_weakDerivative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ} {du₀ du₁ : H → H →L[ℝ] ℝ}
    {τ : H → ℝ}
    (hunit : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u₀ du₀)
    (hannulus : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H) u₁ du₁)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hleft_int : Integrable
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0))
      (MeasureTheory.volume.restrict Set.univ))
    {width : ℝ} (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    dist
      (euclideanSobolevUnitBallAnnulusExplicitOrientedPairing
        (H := H) width φ v u₀ u₁)
      (euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing
        (H := H) width φ v τ) ≤
      (∫⁻ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
        ENNReal.ofReal
          (‖euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
              width (φ : H → ℝ) v z‖ *
            ‖u₀ z - euclideanSobolevUnitSphereRadialTrace τ z‖)
        ∂MeasureTheory.volume).toReal +
      (∫⁻ z in
          euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
            euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
        ENNReal.ofReal
          (‖euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
              width (φ : H → ℝ) v z‖ *
            ‖u₁ z -
              euclideanSobolevUnitBallAnnulusGlueRadialTrace width τ z‖)
        ∂MeasureTheory.volume).toReal := by
  have hexplicit :
      EuclideanSobolevUnitBallAnnulusExplicitOrientedPairingIntegrable
        (H := H) width φ v u₀ u₁ :=
    euclideanSobolev_unit_ball_annulus_explicit_oriented_pairing_integrable_of_weakDerivative
      hunit hannulus φ v _hleft_int hwidth_pos hwidth_le_quarter
  have htrace_int :
      EuclideanSobolevUnitBallAnnulusExactTraceOrientedPairingIntegrable
        (H := H) width φ v τ :=
    euclideanSobolev_unit_ball_annulus_exact_oriented_pairing_integrable_of_weighted_trace
      φ v hτ_weight hwidth_pos hwidth_le_quarter
  exact
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_oriented_radial_trace_error_dist_le_lintegrals
      (u₀ := u₀) (u₁ := u₁) (τ := τ) width φ v
      hexplicit.unit htrace_int.unit hexplicit.annulus htrace_int.annulus

/--
%%handwave
name:
  Uniformly bounded tests give the raw trace-error estimate
statement:
  Assume the fixed smooth test function is bounded in absolute value by a
  constant \(B\).  Then the difference between the explicit oriented collar
  pairing and the same pairing with radial traces inserted is bounded by a
  constant depending only on \(B\), the profile derivative bound, and the
  fixed direction, times the total normalized \(L^1\)-trace error, whenever
  that total error is finite.
proof:
  On each of the three collars, subtract the inserted trace inside the
  integral.  The radial component of the normal has norm one and the test is
  bounded by \(B\), so the oriented radial weights are bounded by a fixed
  multiple of \(1/\delta\).  The three resulting integrals are therefore
  bounded by the corresponding normalized \(L^1\)-trace errors.  Summing the
  unit inner collar, the unit outer collar, and the outer \(3/2\)-collar gives
  the estimate.
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_oriented_radial_trace_error_dist_le_trace_errors_of_test_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (Cprofile : ℝ) (hCprofile_ge_one : 1 ≤ Cprofile)
    (hCprofile : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ Cprofile)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v)
    (B : ℝ) (_hB_nonneg : 0 ≤ B)
    (_hφ_bound : ∀ z : H, ‖(φ : H → ℝ) z‖ ≤ B) :
    ∃ K : ℝ,
      0 ≤ K ∧
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
          (sphereInnerL1TraceError (H := H) 1 u₀ τ width +
                sphereOuterL1TraceError (H := H) 1 u₁ τ width +
                  sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                    u₁ (fun _x : H ↦ 0) width) ≠ (∞ : ℝ≥0∞) →
          dist
            (euclideanSobolevUnitBallAnnulusExplicitOrientedPairing
              (H := H) width φ v u₀ u₁)
            (euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing
              (H := H) width φ v τ) ≤
            K *
              (sphereInnerL1TraceError (H := H) 1 u₀ τ width +
                  sphereOuterL1TraceError (H := H) 1 u₁ τ width +
                    sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                      u₁ (fun _x : H ↦ 0) width).toReal := by
  classical
  let K : ℝ := (Cprofile * 4 * ‖v‖) * B
  have hCprofile_nonneg : 0 ≤ Cprofile :=
    le_trans zero_le_one hCprofile_ge_one
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK_nonneg, ?_⟩
  intro width hwidth_pos hwidth_le_quarter htotal_ne_top
  let μ : Measure H := MeasureTheory.volume
  let S₀ : Set H := euclideanSobolevUnitBallInnerTransitionCollar H width
  let Sinner : Set H :=
    euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width
  let Souter : Set H :=
    euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width
  let S₁ : Set H := Sinner ∪ Souter
  let a₀ : H → ℝ := fun z ↦
    euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
      width (φ : H → ℝ) v z
  let a₁ : H → ℝ := fun z ↦
    euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
      width (φ : H → ℝ) v z
  let t₀ : H → ℝ := euclideanSobolevUnitSphereRadialTrace τ
  let t₁ : H → ℝ :=
    euclideanSobolevUnitBallAnnulusGlueRadialTrace width τ
  let E₀ : ℝ≥0∞ := sphereInnerL1TraceError (H := H) 1 u₀ τ width
  let E₁ : ℝ≥0∞ := sphereOuterL1TraceError (H := H) 1 u₁ τ width
  let E₂ : ℝ≥0∞ :=
    sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0) width
  let T : ℝ≥0∞ := E₀ + E₁ + E₂
  let L₀ : ℝ≥0∞ :=
    ∫⁻ z in S₀, ENNReal.ofReal (‖a₀ z‖ * ‖u₀ z - t₀ z‖) ∂μ
  let L₁ : ℝ≥0∞ :=
    ∫⁻ z in S₁, ENNReal.ofReal (‖a₁ z‖ * ‖u₁ z - t₁ z‖) ∂μ
  have hS₀_meas : MeasurableSet S₀ :=
    (euclideanSobolevUnitBallInnerTransitionCollar_isOpen
      (H := H) width).measurableSet
  have hSinner_meas : MeasurableSet Sinner :=
    (euclideanSobolevUnitBallAnnulusInnerTransitionCollar_isOpen
      (H := H) width).measurableSet
  have hSouter_meas : MeasurableSet Souter :=
    (euclideanSobolevUnitBallAnnulusOuterTransitionCollar_isOpen
      (H := H) width).measurableSet
  have hS₁_meas : MeasurableSet S₁ := hSinner_meas.union hSouter_meas
  have hS₀_subset_ball : S₀ ⊆ Metric.ball (0 : H) 1 := by
    intro z hz
    exact by
      simpa [S₀, euclideanSobolevUnitBallInnerTransitionCollar,
        Metric.mem_ball, dist_eq_norm] using hz.2
  have hSinner_subset_annulus :
      Sinner ⊆ euclideanSobolevUnitBallReflectionAnnulus H := by
    intro z hz
    have hlt : ‖z‖ < (3 / 2 : ℝ) := by
      nlinarith [hz.2, hwidth_le_quarter]
    exact by
      simpa [Sinner, euclideanSobolevUnitBallReflectionAnnulus] using
        And.intro hz.1 hlt
  have hSouter_subset_annulus :
      Souter ⊆ euclideanSobolevUnitBallReflectionAnnulus H := by
    intro z hz
    have hgt : (1 : ℝ) < ‖z‖ := by
      nlinarith [hz.1, hwidth_le_quarter]
    exact by
      simpa [Souter, euclideanSobolevUnitBallReflectionAnnulus] using
        And.intro hgt hz.2
  have hS₁_subset_annulus :
      S₁ ⊆ euclideanSobolevUnitBallReflectionAnnulus H := by
    intro z hz
    rcases hz with hz | hz
    · exact hSinner_subset_annulus hz
    · exact hSouter_subset_annulus hz
  have hu₀_aesm_S₀ : AEStronglyMeasurable u₀ (μ.restrict S₀) := by
    simpa [μ] using hu₀_aesm.mono_set hS₀_subset_ball
  have hu₁_aesm_S₁ : AEStronglyMeasurable u₁ (μ.restrict S₁) := by
    simpa [μ] using hu₁_aesm.mono_set hS₁_subset_annulus
  have hT_ne_top : T ≠ (∞ : ℝ≥0∞) := by
    simpa [T, E₀, E₁, E₂] using htotal_ne_top
  have hE₀_ne_top : E₀ ≠ (∞ : ℝ≥0∞) := by
    refine ne_top_of_le_ne_top hT_ne_top ?_
    dsimp [T]
    calc
      E₀ ≤ E₀ + E₁ := le_self_add
      _ ≤ E₀ + E₁ + E₂ := le_self_add
  have hE₁_ne_top : E₁ ≠ (∞ : ℝ≥0∞) := by
    refine ne_top_of_le_ne_top hT_ne_top ?_
    dsimp [T]
    calc
      E₁ ≤ E₀ + E₁ := le_add_self
      _ ≤ E₀ + E₁ + E₂ := le_self_add
  have hE₂_ne_top : E₂ ≠ (∞ : ℝ≥0∞) := by
    refine ne_top_of_le_ne_top hT_ne_top ?_
    dsimp [T]
    simpa [add_assoc] using (le_add_self : E₂ ≤ (E₀ + E₁) + E₂)
  have htrace_int :
      EuclideanSobolevUnitBallAnnulusExactTraceOrientedPairingIntegrable
        (H := H) width φ v τ :=
    euclideanSobolev_unit_ball_annulus_exact_oriented_pairing_integrable_of_weighted_trace
      φ v _hτ_weight hwidth_pos hwidth_le_quarter
  have hderiv_meas :
      Measurable (fun t : ℝ ↦ deriv Real.smoothTransition t) := by
    have hsmooth : ContDiff ℝ ∞ Real.smoothTransition :=
      Real.smoothTransition.contDiff
    exact (hsmooth.continuous_deriv (by simp)).measurable
  have hnorm_inv_meas :
      Measurable (fun z : H ↦ (‖z‖ : ℝ)⁻¹) :=
    (continuous_norm.measurable).inv
  have hinner_meas :
      Measurable (fun z : H ↦ inner ℝ (((‖z‖)⁻¹ : ℝ) • z) v) := by
    have hinner_base :
        Measurable (fun z : H ↦ inner ℝ z v) :=
      (continuous_id.inner continuous_const).measurable
    have hmul :
        Measurable (fun z : H ↦ (‖z‖ : ℝ)⁻¹ * inner ℝ z v) :=
      hnorm_inv_meas.mul hinner_base
    convert hmul using 1
    ext z
    simp [inner_smul_left]
  have hφ_meas : Measurable (φ : H → ℝ) :=
    φ.smooth.continuous.measurable
  have ha₀_meas : Measurable a₀ := by
    have harg :
        Measurable
          (fun z : H ↦
            (((1 : ℝ) - width / 2 - ‖z‖) / (width / 4))) := by
      fun_prop
    have hprof :
        Measurable
          (fun z : H ↦
            deriv Real.smoothTransition
              (((1 : ℝ) - width / 2 - ‖z‖) / (width / 4))) :=
      hderiv_meas.comp harg
    simpa [a₀, euclideanSobolevUnitBallInnerOrientedRadialPairingWeight,
      mul_assoc] using
      (((hprof.mul measurable_const).mul hinner_meas).mul hφ_meas)
  have hannulus_inner_weight_meas :
      Measurable
        (fun z : H ↦
          euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
            width (φ : H → ℝ) v z) := by
    have harg :
        Measurable
          (fun z : H ↦
            ((‖z‖ - ((1 : ℝ) + width / 2)) / (width / 4))) := by
      fun_prop
    have hprof :
        Measurable
          (fun z : H ↦
            deriv Real.smoothTransition
              ((‖z‖ - ((1 : ℝ) + width / 2)) / (width / 4))) :=
      hderiv_meas.comp harg
    simpa [euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight,
      mul_assoc] using
      (((hprof.mul measurable_const).mul hinner_meas).mul hφ_meas)
  have hannulus_outer_weight_meas :
      Measurable
        (fun z : H ↦
          euclideanSobolevUnitBallAnnulusOuterOrientedRadialPairingWeight
            width (φ : H → ℝ) v z) := by
    have harg :
        Measurable
          (fun z : H ↦
            ((((3 / 2 : ℝ) - width / 2) - ‖z‖) /
              (width / 4))) := by
      fun_prop
    have hprof :
        Measurable
          (fun z : H ↦
            deriv Real.smoothTransition
              ((((3 / 2 : ℝ) - width / 2) - ‖z‖) /
                (width / 4))) :=
      hderiv_meas.comp harg
    simpa [euclideanSobolevUnitBallAnnulusOuterOrientedRadialPairingWeight,
      mul_assoc] using
      (((hprof.mul measurable_const).mul hinner_meas).mul hφ_meas)
  have ha₁_meas : Measurable a₁ := by
    simpa [a₁, euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight]
      using
        Measurable.ite
          (p := fun z : H ↦
            z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width)
          hSinner_meas hannulus_inner_weight_meas
          hannulus_outer_weight_meas
  have hunit_weight_bound :
      ∀ z ∈ S₀, ‖a₀ z‖ ≤ (Cprofile * (4 / width) * ‖v‖) * B := by
    intro z hz
    have hbound :=
      euclideanSobolevUnitBallInnerOrientedRadialPairingWeight_norm_le
        (φ := (φ : H → ℝ)) (v := v)
        hwidth_pos hwidth_le_quarter hCprofile_ge_one hCprofile
        (by simpa [S₀] using hz)
    calc
      ‖a₀ z‖ ≤
          (Cprofile * (4 / width) * ‖v‖) * ‖(φ : H → ℝ) z‖ := by
            simpa [a₀] using hbound
      _ ≤ (Cprofile * (4 / width) * ‖v‖) * B := by
            exact mul_le_mul_of_nonneg_left (_hφ_bound z) (by positivity)
  have hannulus_weight_bound :
      ∀ z ∈ S₁, ‖a₁ z‖ ≤ (Cprofile * (4 / width) * ‖v‖) * B := by
    intro z hz
    have hbound :=
      euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight_norm_le
        (φ := (φ : H → ℝ)) (v := v)
        hwidth_pos hwidth_le_quarter hCprofile_ge_one hCprofile
        (by simpa [S₁, Sinner, Souter] using hz)
    calc
      ‖a₁ z‖ ≤
          (Cprofile * (4 / width) * ‖v‖) * ‖(φ : H → ℝ) z‖ := by
            simpa [a₁] using hbound
      _ ≤ (Cprofile * (4 / width) * ‖v‖) * B := by
            exact mul_le_mul_of_nonneg_left (_hφ_bound z) (by positivity)
  have hscale_nonneg :
      0 ≤ (Cprofile * (4 / width) * ‖v‖) * B := by
    positivity
  have hK_scale :
      (Cprofile * (4 / width) * ‖v‖) * B = K * (1 / width) := by
    field_simp [hwidth_pos.ne']
    ring
  have hL₀_le : L₀ ≤ ENNReal.ofReal K * E₀ := by
    calc
      L₀ ≤
          ∫⁻ z in S₀,
            ENNReal.ofReal
              (((Cprofile * (4 / width) * ‖v‖) * B) *
                ‖u₀ z - t₀ z‖) ∂μ := by
            refine setLIntegral_mono' hS₀_meas ?_
            intro z hz
            exact ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right
                (hunit_weight_bound z hz) (norm_nonneg _))
      _ =
          ∫⁻ z in S₀,
            ENNReal.ofReal ((Cprofile * (4 / width) * ‖v‖) * B) *
              ENNReal.ofReal ‖u₀ z - t₀ z‖ ∂μ := by
            refine lintegral_congr fun z ↦ ?_
            rw [ENNReal.ofReal_mul hscale_nonneg]
      _ =
          ENNReal.ofReal ((Cprofile * (4 / width) * ‖v‖) * B) *
            ∫⁻ z in S₀, ENNReal.ofReal ‖u₀ z - t₀ z‖ ∂μ := by
            rw [lintegral_const_mul']
            exact ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal K * E₀ := by
            have hK_scale_ofReal :
                ENNReal.ofReal ((Cprofile * (4 / width) * ‖v‖) * B) =
                  ENNReal.ofReal K * ENNReal.ofReal (1 / width) := by
              rw [hK_scale, ENNReal.ofReal_mul hK_nonneg]
            rw [hK_scale_ofReal]
            simp [E₀, S₀, t₀, μ, sphereInnerL1TraceError,
              euclideanSobolevUnitBallInnerTransitionCollar,
              euclideanSobolevUnitSphereRadialTrace, one_div, mul_assoc]
  let Linner : ℝ≥0∞ :=
    ∫⁻ z in Sinner, ENNReal.ofReal (‖a₁ z‖ * ‖u₁ z - t₁ z‖) ∂μ
  let Louter : ℝ≥0∞ :=
    ∫⁻ z in Souter, ENNReal.ofReal (‖a₁ z‖ * ‖u₁ z - t₁ z‖) ∂μ
  have hL₁_eq : L₁ = Linner + Louter := by
    have hdisj :
        Disjoint Sinner Souter := by
      simpa [Sinner, Souter] using
        euclideanSobolevUnitBallAnnulusTransitionCollars_disjoint
          (H := H) hwidth_le_quarter
    simpa [L₁, Linner, Louter, S₁] using
      lintegral_union (μ := μ)
        (f := fun z : H ↦ ENNReal.ofReal (‖a₁ z‖ * ‖u₁ z - t₁ z‖))
        hSouter_meas hdisj
  have hLinner_le : Linner ≤ ENNReal.ofReal K * E₁ := by
    calc
      Linner ≤
          ∫⁻ z in Sinner,
            ENNReal.ofReal
              (((Cprofile * (4 / width) * ‖v‖) * B) *
                ‖u₁ z - euclideanSobolevUnitSphereRadialTrace τ z‖) ∂μ := by
            refine setLIntegral_mono' hSinner_meas ?_
            intro z hz
            have hzS₁ : z ∈ S₁ := Or.inl hz
            have ht₁ :
                t₁ z = euclideanSobolevUnitSphereRadialTrace τ z := by
              simp [t₁, euclideanSobolevUnitBallAnnulusGlueRadialTrace,
                Sinner, hz]
            rw [ht₁]
            exact ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right
                (hannulus_weight_bound z hzS₁) (norm_nonneg _))
      _ =
          ∫⁻ z in Sinner,
            ENNReal.ofReal ((Cprofile * (4 / width) * ‖v‖) * B) *
              ENNReal.ofReal
                ‖u₁ z - euclideanSobolevUnitSphereRadialTrace τ z‖ ∂μ := by
            refine lintegral_congr fun z ↦ ?_
            rw [ENNReal.ofReal_mul hscale_nonneg]
      _ =
          ENNReal.ofReal ((Cprofile * (4 / width) * ‖v‖) * B) *
            ∫⁻ z in Sinner,
              ENNReal.ofReal
                ‖u₁ z - euclideanSobolevUnitSphereRadialTrace τ z‖ ∂μ := by
            rw [lintegral_const_mul']
            exact ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal K * E₁ := by
            have hK_scale_ofReal :
                ENNReal.ofReal ((Cprofile * (4 / width) * ‖v‖) * B) =
                  ENNReal.ofReal K * ENNReal.ofReal (1 / width) := by
              rw [hK_scale, ENNReal.ofReal_mul hK_nonneg]
            rw [hK_scale_ofReal]
            simp [E₁, Sinner, μ, sphereOuterL1TraceError,
              euclideanSobolevUnitBallAnnulusInnerTransitionCollar,
              euclideanSobolevUnitSphereRadialTrace, one_div, mul_assoc]
  have hLouter_le : Louter ≤ ENNReal.ofReal K * E₂ := by
    calc
      Louter ≤
          ∫⁻ z in Souter,
            ENNReal.ofReal
              (((Cprofile * (4 / width) * ‖v‖) * B) *
                ‖u₁ z‖) ∂μ := by
            refine setLIntegral_mono' hSouter_meas ?_
            intro z hz
            have hzS₁ : z ∈ S₁ := Or.inr hz
            have hz_not_inner :
                z ∉ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width := by
              intro hz_inner
              exact
                (euclideanSobolevUnitBallAnnulusTransitionCollars_disjoint
                  (H := H) hwidth_le_quarter).le_bot
                  ⟨hz_inner, by simpa [Souter] using hz⟩
            have ht₁ : t₁ z = 0 := by
              simp [t₁, euclideanSobolevUnitBallAnnulusGlueRadialTrace,
                hz_not_inner]
            rw [ht₁, sub_zero]
            exact ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right
                (hannulus_weight_bound z hzS₁) (norm_nonneg _))
      _ =
          ∫⁻ z in Souter,
            ENNReal.ofReal ((Cprofile * (4 / width) * ‖v‖) * B) *
              ENNReal.ofReal ‖u₁ z‖ ∂μ := by
            refine lintegral_congr fun z ↦ ?_
            rw [ENNReal.ofReal_mul hscale_nonneg]
      _ =
          ENNReal.ofReal ((Cprofile * (4 / width) * ‖v‖) * B) *
            ∫⁻ z in Souter, ENNReal.ofReal ‖u₁ z‖ ∂μ := by
            rw [lintegral_const_mul']
            exact ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal K * E₂ := by
            have hK_scale_ofReal :
                ENNReal.ofReal ((Cprofile * (4 / width) * ‖v‖) * B) =
                  ENNReal.ofReal K * ENNReal.ofReal (1 / width) := by
              rw [hK_scale, ENNReal.ofReal_mul hK_nonneg]
            rw [hK_scale_ofReal]
            simp [E₂, Souter, μ, sphereInnerL1TraceError,
              euclideanSobolevUnitBallAnnulusOuterTransitionCollar,
              one_div, mul_assoc]
  have hL₁_le : L₁ ≤ ENNReal.ofReal K * (E₁ + E₂) := by
    calc
      L₁ = Linner + Louter := hL₁_eq
      _ ≤ ENNReal.ofReal K * E₁ + ENNReal.ofReal K * E₂ :=
            add_le_add hLinner_le hLouter_le
      _ = ENNReal.ofReal K * (E₁ + E₂) := by
            rw [mul_add]
  have hLsum_le : L₀ + L₁ ≤ ENNReal.ofReal K * T := by
    calc
      L₀ + L₁ ≤ ENNReal.ofReal K * E₀ +
          ENNReal.ofReal K * (E₁ + E₂) :=
            add_le_add hL₀_le hL₁_le
      _ = ENNReal.ofReal K * T := by
            simp [T, mul_add, add_assoc]
  have hLsum_ne_top : L₀ + L₁ ≠ (∞ : ℝ≥0∞) := by
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT_ne_top) hLsum_le
  have hL₀_ne_top : L₀ ≠ (∞ : ℝ≥0∞) := by
    refine ne_top_of_le_ne_top hLsum_ne_top ?_
    exact le_self_add
  have hL₁_ne_top : L₁ ≠ (∞ : ℝ≥0∞) := by
    refine ne_top_of_le_ne_top hLsum_ne_top ?_
    exact le_add_self
  have hunit_u_int :
      Integrable (fun z : H ↦ a₀ z • u₀ z) (μ.restrict S₀) := by
    refine
      integrable_weighted_scalar_of_integrable_trace_and_error
        (μ := μ.restrict S₀) (a := a₀) (u := u₀) (t := t₀)
        ha₀_meas hu₀_aesm_S₀ ?_ ?_
    · simpa [μ, S₀, a₀, t₀] using htrace_int.unit
    · simpa [L₀, μ, S₀, a₀, t₀] using hL₀_ne_top
  have hannulus_u_int :
      Integrable (fun z : H ↦ a₁ z • u₁ z) (μ.restrict S₁) := by
    refine
      integrable_weighted_scalar_of_integrable_trace_and_error
        (μ := μ.restrict S₁) (a := a₁) (u := u₁) (t := t₁)
        ha₁_meas hu₁_aesm_S₁ ?_ ?_
    · simpa [μ, S₁, a₁, t₁] using htrace_int.annulus
    · simpa [L₁, μ, S₁, a₁, t₁] using hL₁_ne_top
  have hdist_lintegrals :
      dist
        (euclideanSobolevUnitBallAnnulusExplicitOrientedPairing
          (H := H) width φ v u₀ u₁)
        (euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing
          (H := H) width φ v τ) ≤
        L₀.toReal + L₁.toReal := by
    have h :=
      euclideanSobolev_unit_ball_annulus_l1_trace_glue_oriented_radial_trace_error_dist_le_lintegrals
        (u₀ := u₀) (u₁ := u₁) (τ := τ) width φ v
        (by simpa [μ, S₀, a₀] using hunit_u_int)
        htrace_int.unit
        (by simpa [μ, S₁, a₁] using hannulus_u_int)
        htrace_int.annulus
    simpa [L₀, L₁, μ, S₀, S₁, a₀, a₁, t₀, t₁] using h
  have htoReal_bound : L₀.toReal + L₁.toReal ≤ K * T.toReal := by
    calc
      L₀.toReal + L₁.toReal = (L₀ + L₁).toReal := by
        rw [ENNReal.toReal_add hL₀_ne_top hL₁_ne_top]
      _ ≤ (ENNReal.ofReal K * T).toReal := by
        exact ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT_ne_top) hLsum_le
      _ = K * T.toReal := by
        simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK_nonneg]
  exact hdist_lintegrals.trans (by simpa [T, E₀, E₁, E₂] using htoReal_bound)

/--
%%handwave
name:
  The trace-error part is bounded by the normalized trace errors
statement:
  For fixed profile bound, test function, and direction, there is a finite
  constant \(K\) such that the distance between the explicit oriented collar
  pairing and the same pairing with the radial traces inserted is bounded by
  \(K\) times the sum of the three normalized \(L^1\)-trace errors whenever
  that total error is finite.
proof:
  Apply the pointwise bounds for the three explicit radial weights.  The
  smooth test function is bounded, and the radial normal component is bounded
  by the norm of the fixed direction.  Thus each collar contribution is
  bounded by a fixed multiple of the corresponding normalized trace error;
  summing the unit collar, the outer unit collar, and the \(3/2\)-collar gives
  the claimed estimate.
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_oriented_radial_trace_error_dist_le_trace_errors
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (Cprofile : ℝ) (hCprofile_ge_one : 1 ≤ Cprofile)
    (hCprofile : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ Cprofile)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ K : ℝ,
      0 ≤ K ∧
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
          (sphereInnerL1TraceError (H := H) 1 u₀ τ width +
                sphereOuterL1TraceError (H := H) 1 u₁ τ width +
                  sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                    u₁ (fun _x : H ↦ 0) width) ≠ (∞ : ℝ≥0∞) →
          dist
            (euclideanSobolevUnitBallAnnulusExplicitOrientedPairing
              (H := H) width φ v u₀ u₁)
            (euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing
              (H := H) width φ v τ) ≤
            K *
              (sphereInnerL1TraceError (H := H) 1 u₀ τ width +
                  sphereOuterL1TraceError (H := H) 1 u₁ τ width +
                    sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                      u₁ (fun _x : H ↦ 0) width).toReal := by
  classical
  rcases
      φ.compact_support.exists_bound_of_continuousOn
        φ.smooth.continuous.continuousOn with
    ⟨B₀, hB₀⟩
  let B : ℝ := max B₀ 0
  have hB_nonneg : 0 ≤ B := le_max_right B₀ 0
  have hφ_bound : ∀ z : H, ‖(φ : H → ℝ) z‖ ≤ B := by
    intro z
    by_cases hz : z ∈ tsupport (φ : H → ℝ)
    · exact (hB₀ z hz).trans (le_max_left B₀ 0)
    · have hzero : (φ : H → ℝ) z = 0 :=
        image_eq_zero_of_notMem_tsupport hz
      simp [B, hzero, hB_nonneg]
  exact
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_oriented_radial_trace_error_dist_le_trace_errors_of_test_bound
      (u₀ := u₀) (u₁ := u₁) (τ := τ)
      hu₀_aesm hu₁_aesm
      Cprofile hCprofile_ge_one hCprofile φ v _hτ_weight
      B hB_nonneg hφ_bound

/--
%%handwave
name:
  Trace errors control the distance to the exact radial-trace pairing
statement:
  If the three normalized collar trace errors are small, then the explicit
  oriented collar pairing differs from the same pairing with the radial traces
  inserted by at most half the prescribed tolerance.
proof:
  Use the pointwise bounds for the explicit oriented radial weights.  On the
  unit collar and on the inner annular collar, insert the common unit-sphere
  trace; on the outer annular collar insert the zero trace.  The normalized
  \(L^1\)-trace errors absorb the factor \(1/\delta\) from the transition
  derivatives after enlarging the constant.
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_oriented_radial_trace_error_dist_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (Cprofile : ℝ) (hCprofile_ge_one : 1 ≤ Cprofile)
    (hCprofile : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ Cprofile)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ C : ℝ,
      Cprofile ≤ C ∧
        1 ≤ C ∧
          ∀ {η width : ℝ}
            (_hη_pos : 0 < η)
            (_hwidth_pos : 0 < width)
            (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
            sphereInnerL1TraceError (H := H) 1 u₀ τ width +
                sphereOuterL1TraceError (H := H) 1 u₁ τ width +
                  sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                    u₁ (fun _x : H ↦ 0) width ≤
              ENNReal.ofReal (η / C) →
            dist
              (euclideanSobolevUnitBallAnnulusExplicitOrientedPairing
                (H := H) width φ v u₀ u₁)
              (euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing
                (H := H) width φ v τ) ≤
              η / 2 := by
  obtain ⟨K, hK_nonneg, hK_bound⟩ :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_oriented_radial_trace_error_dist_le_trace_errors
      (u₀ := u₀) (u₁ := u₁) (τ := τ)
      hu₀_aesm hu₁_aesm
      Cprofile hCprofile_ge_one hCprofile φ v _hτ_weight
  let C : ℝ := max Cprofile (max (1 : ℝ) (2 * K))
  refine ⟨C, ?_, ?_, ?_⟩
  · exact le_max_left Cprofile (max (1 : ℝ) (2 * K))
  · exact (le_max_left (1 : ℝ) (2 * K)).trans
      (le_max_right Cprofile (max (1 : ℝ) (2 * K)))
  · intro η width hη_pos hwidth_pos hwidth_le_quarter htrace
    let T : ℝ≥0∞ :=
      sphereInnerL1TraceError (H := H) 1 u₀ τ width +
        sphereOuterL1TraceError (H := H) 1 u₁ τ width +
          sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
            u₁ (fun _x : H ↦ 0) width
    have hC_ge_one : 1 ≤ C :=
      (le_max_left (1 : ℝ) (2 * K)).trans
        (le_max_right Cprofile (max (1 : ℝ) (2 * K)))
    have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC_ge_one
    have hT_toReal_le : T.toReal ≤ η / C := by
      have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top htrace
      have hη_div_nonneg : 0 ≤ η / C :=
        div_nonneg hη_pos.le hC_pos.le
      simpa [T, ENNReal.toReal_ofReal hη_div_nonneg] using hmono
    have hdist_le :
        dist
          (euclideanSobolevUnitBallAnnulusExplicitOrientedPairing
            (H := H) width φ v u₀ u₁)
          (euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing
            (H := H) width φ v τ) ≤ K * T.toReal := by
      have hT_ne_top : T ≠ (∞ : ℝ≥0∞) := by
        exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          (by simpa [T] using htrace)
      simpa [T] using hK_bound hwidth_pos hwidth_le_quarter hT_ne_top
    have hK_le_halfC : K / C ≤ (1 / 2 : ℝ) := by
      have htwoK_le_C : 2 * K ≤ C :=
        (le_max_right (1 : ℝ) (2 * K)).trans
          (le_max_right Cprofile (max (1 : ℝ) (2 * K)))
      rw [div_le_iff₀ hC_pos]
      nlinarith
    calc
      dist
          (euclideanSobolevUnitBallAnnulusExplicitOrientedPairing
            (H := H) width φ v u₀ u₁)
          (euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing
            (H := H) width φ v τ)
          ≤ K * T.toReal := hdist_le
      _ ≤ K * (η / C) :=
          mul_le_mul_of_nonneg_left hT_toReal_le hK_nonneg
      _ = η * (K / C) := by ring
      _ ≤ η * (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hK_le_halfC hη_pos.le
      _ = η / 2 := by ring

private theorem euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing_eq_two_unit_collars
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    (width : ℝ)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H) (τ : H → ℝ) :
    euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing
        (H := H) width φ v τ =
      (∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
          euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
            width (φ : H → ℝ) v z •
            euclideanSobolevUnitSphereRadialTrace τ z
          ∂MeasureTheory.volume) +
        ∫ z in euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width,
          euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
            width (φ : H → ℝ) v z •
            euclideanSobolevUnitSphereRadialTrace τ z
          ∂MeasureTheory.volume := by
  classical
  let Sinner : Set H :=
    euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width
  let Souter : Set H :=
    euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width
  let F : H → ℝ := fun z ↦
    euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
      width (φ : H → ℝ) v z •
      euclideanSobolevUnitBallAnnulusGlueRadialTrace width τ z
  let G : H → ℝ := fun z ↦
    euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
      width (φ : H → ℝ) v z •
      euclideanSobolevUnitSphereRadialTrace τ z
  have hF_zero_inner_compl : ∀ z : H, z ∉ Sinner → F z = 0 := by
    intro z hz
    simp [F, euclideanSobolevUnitBallAnnulusGlueRadialTrace, Sinner, hz]
  have hF_zero_union_compl : ∀ z : H, z ∉ Sinner ∪ Souter → F z = 0 := by
    intro z hz
    exact hF_zero_inner_compl z (fun hz_inner ↦ hz (Or.inl hz_inner))
  have hannulus :
      (∫ z in Sinner ∪ Souter, F z ∂MeasureTheory.volume) =
        ∫ z in Sinner, G z ∂MeasureTheory.volume := by
    calc
      (∫ z in Sinner ∪ Souter, F z ∂MeasureTheory.volume)
          = ∫ z, F z ∂MeasureTheory.volume := by
            rw [setIntegral_eq_integral_of_forall_compl_eq_zero
              hF_zero_union_compl]
      _ = ∫ z in Sinner, F z ∂MeasureTheory.volume := by
            rw [setIntegral_eq_integral_of_forall_compl_eq_zero
              hF_zero_inner_compl]
      _ = ∫ z in Sinner, G z ∂MeasureTheory.volume := by
            refine setIntegral_congr_fun
              (euclideanSobolevUnitBallAnnulusInnerTransitionCollar_isOpen
                (H := H) width).measurableSet ?_
            intro z hz
            simp [F, G, Sinner,
              euclideanSobolevUnitBallAnnulusGlueRadialTrace,
              euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight,
              hz]
  simpa [euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing,
    Sinner, Souter, F, G] using congrArg
      (fun x ↦
        (∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
          euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
            width (φ : H → ℝ) v z •
            euclideanSobolevUnitSphereRadialTrace τ z
          ∂MeasureTheory.volume) + x)
      hannulus

private theorem euclideanSobolev_setIntegral_annulus_eq_polar
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [Nontrivial H]
    {F : H → ℝ} {a b : ℝ} (ha_pos : 0 < a) :
    (∫ x in {x : H | a < ‖x‖ ∧ ‖x‖ < b},
        F x ∂MeasureTheory.volume) =
      ∫ p in
        (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
          {r : Set.Ioi (0 : ℝ) | a < (r : ℝ) ∧ (r : ℝ) < b},
        F (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))
        ∂(((MeasureTheory.volume : Measure H).toSphere).prod
          (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1))) := by
  classical
  let μH : Measure H := MeasureTheory.volume
  let μS : Measure (Metric.sphere (0 : H) 1) := μH.toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let C : Set H := {x : H | a < ‖x‖ ∧ ‖x‖ < b}
  let NZ : Set H := {0}ᶜ
  let T : Set ({0}ᶜ : Set H) := ((↑) : ({0}ᶜ : Set H) → H) ⁻¹' C
  let I : Set (Set.Ioi (0 : ℝ)) :=
    {r : Set.Ioi (0 : ℝ) | a < (r : ℝ) ∧ (r : ℝ) < b}
  let P : Set (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    Set.univ ×ˢ I
  let e : ({0}ᶜ : Set H) ≃ₜ
      (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    homeomorphUnitSphereProd H
  let μNZ : Measure ({0}ᶜ : Set H) :=
    μH.comap ((↑) : ({0}ᶜ : Set H) → H)
  let ν : Measure (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    μS.prod μR
  let G : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    fun p ↦ F ((p.2 : ℝ) • (p.1 : H))
  have hNZ_meas : MeasurableSet NZ := by
    dsimp [NZ]
    exact (measurableSet_singleton (0 : H)).compl
  have hC_meas : MeasurableSet C := by
    dsimp [C]
    exact
      (isOpen_lt continuous_const continuous_norm).measurableSet.inter
        (isOpen_lt continuous_norm continuous_const).measurableSet
  have hC_subset_NZ : C ⊆ NZ := by
    intro x hx
    dsimp [C, NZ] at hx ⊢
    exact norm_pos_iff.mp (ha_pos.trans hx.1)
  have hmap_subtype :
      Measure.map ((↑) : ({0}ᶜ : Set H) → H) μNZ = μH.restrict NZ := by
    simpa [μNZ, NZ] using map_comap_subtype_coe hNZ_meas μH
  have hleft_subtype :
      (∫ x in C, F x ∂μH) =
        ∫ x in T, F (x : H) ∂μNZ := by
    have hrestrict :
        (μH.restrict NZ).restrict C = μH.restrict C := by
      rw [Measure.restrict_restrict hC_meas]
      have hinter : C ∩ NZ = C := Set.inter_eq_left.mpr hC_subset_NZ
      rw [hinter]
    calc
      (∫ x in C, F x ∂μH)
          = ∫ x in C, F x ∂(μH.restrict NZ) := by
            rw [hrestrict]
      _ = ∫ x in T, F (x : H) ∂μNZ := by
            rw [← hmap_subtype]
            simpa [T] using
              (MeasurableEmbedding.subtype_coe hNZ_meas).setIntegral_map
                (μ := μNZ) F C
  have hmp : MeasurePreserving e μNZ ν := by
    simpa [e, μNZ, ν, μS, μR, μH] using
      (MeasureTheory.volume : Measure H).measurePreserving_homeomorphUnitSphereProd
  have hpre : e ⁻¹' P = T := by
    ext x
    simp [P, T, C, I, e, homeomorphUnitSphereProd_apply_snd_coe]
  have hT_meas : MeasurableSet T := by
    dsimp [T]
    exact hC_meas.preimage measurable_subtype_coe
  have hpolar :
      (∫ x in T, F (x : H) ∂μNZ) =
        ∫ p in P, G p ∂ν := by
    calc
      (∫ x in T, F (x : H) ∂μNZ)
          = ∫ x in e ⁻¹' P, G (e x) ∂μNZ := by
            rw [hpre]
            refine setIntegral_congr_fun hT_meas ?_
            intro x _hx
            have hx_ne : (x : H) ≠ 0 := by
              intro hx_zero
              exact x.2 (by simp [hx_zero])
            have hx_norm_ne : ‖(x : H)‖ ≠ 0 := norm_ne_zero_iff.mpr hx_ne
            have hdir :
                ((e x).1 : H) =
                  (((1 / ‖(x : H)‖) : ℝ) • (x : H)) := by
              simp [e, homeomorphUnitSphereProd_apply_fst_coe, div_eq_mul_inv]
            have hr :
                ((e x).2 : ℝ) = ‖(x : H)‖ := by
              simp [e, homeomorphUnitSphereProd_apply_snd_coe]
            have hpoint :
                ((e x).2 : ℝ) • ((e x).1 : H) = (x : H) := by
              rw [hr, hdir, smul_smul]
              have hcoef : ‖(x : H)‖ * (1 / ‖(x : H)‖) = (1 : ℝ) := by
                field_simp [hx_norm_ne]
              rw [hcoef, one_smul]
            simp [G, hpoint]
      _ = ∫ p in P, G p ∂ν :=
            hmp.setIntegral_preimage_emb e.measurableEmbedding G P
  simpa [μH, μS, μR, C, I, P, ν, G] using hleft_subtype.trans hpolar

private theorem euclideanSobolev_two_unit_collar_exact_trace_pairing_eq_polar
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [Nontrivial H]
    {τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H) {width : ℝ}
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) :
    (∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
        euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
          width (φ : H → ℝ) v z •
          euclideanSobolevUnitSphereRadialTrace τ z
        ∂MeasureTheory.volume) +
      ∫ z in euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width,
        euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
          width (φ : H → ℝ) v z •
          euclideanSobolevUnitSphereRadialTrace τ z
        ∂MeasureTheory.volume =
    (∫ p in
        (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
          {r : Set.Ioi (0 : ℝ) |
            (1 : ℝ) - width < (r : ℝ) ∧ (r : ℝ) < 1},
        euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
          width (φ : H → ℝ) v
          (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) •
          euclideanSobolevUnitSphereRadialTrace τ
            (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))
        ∂(((MeasureTheory.volume : Measure H).toSphere).prod
          (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)))) +
      ∫ p in
        (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
          {r : Set.Ioi (0 : ℝ) |
            (1 : ℝ) < (r : ℝ) ∧ (r : ℝ) < 1 + width},
        euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
          width (φ : H → ℝ) v
          (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) •
          euclideanSobolevUnitSphereRadialTrace τ
            (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))
        ∂(((MeasureTheory.volume : Measure H).toSphere).prod
          (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1))) := by
  have hunit_a_pos : 0 < (1 : ℝ) - width := by
    nlinarith [hwidth_le_quarter]
  have hunit :=
    euclideanSobolev_setIntegral_annulus_eq_polar
      (H := H)
      (F := fun z : H ↦
        euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
          width (φ : H → ℝ) v z •
          euclideanSobolevUnitSphereRadialTrace τ z)
      (a := (1 : ℝ) - width) (b := 1) hunit_a_pos
  have hannulus :=
    euclideanSobolev_setIntegral_annulus_eq_polar
      (H := H)
      (F := fun z : H ↦
        euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
          width (φ : H → ℝ) v z •
          euclideanSobolevUnitSphereRadialTrace τ z)
      (a := (1 : ℝ)) (b := 1 + width) (by norm_num)
  simpa [euclideanSobolevUnitBallInnerTransitionCollar,
    euclideanSobolevUnitBallAnnulusInnerTransitionCollar] using
    congrArg₂ HAdd.hAdd hunit hannulus

private theorem norm_polar_smul_unit_sphere
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :
    ‖((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)‖ =
      ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) := by
  have hθ_norm : ‖(p.1 : H)‖ = (1 : ℝ) := by
    simpa [Metric.mem_sphere, dist_eq_norm] using p.1.2
  have hr_nonneg : 0 ≤ ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) := p.2.2.le
  simp [norm_smul, Real.norm_of_nonneg hr_nonneg, hθ_norm]

private theorem invNorm_smul_polar_smul_unit_sphere
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :
    (‖((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)‖)⁻¹ •
        (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) =
      (p.1 : H) := by
  have hr_ne : ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) ≠ 0 :=
    ne_of_gt p.2.2
  rw [norm_polar_smul_unit_sphere p, smul_smul]
  have hcoef :
      ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)⁻¹ *
          ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) = 1 := by
    exact inv_mul_cancel₀ hr_ne
  simp [hcoef]

private theorem euclideanSobolevUnitSphereRadialTrace_polar
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {τ : H → ℝ}
    (p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :
    euclideanSobolevUnitSphereRadialTrace τ
        (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) =
      τ (p.1 : H) := by
  simpa [euclideanSobolevUnitSphereRadialTrace, one_div] using
    congrArg τ (invNorm_smul_polar_smul_unit_sphere (H := H) p)

private theorem inner_invNorm_smul_polar_smul_unit_sphere
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) (v : H) :
    inner ℝ
        ((‖((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)‖)⁻¹ •
          (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))) v =
      inner ℝ (p.1 : H) v := by
  rw [invNorm_smul_polar_smul_unit_sphere p]

/--
%%handwave
name:
  Compactly supported smooth coordinate tests have bounded differential
statement:
  The operator norm of the differential of a smooth compactly supported
  coordinate test is bounded on the whole model vector space.
proof:
  The differential depends continuously on the base point, hence its norm is
  bounded on the compact closed support.  Away from the closed support the test
  vanishes in a neighbourhood, so its differential is zero.
-/
private theorem smoothCompactlySupportedCoordinateFunction_exists_fderiv_norm_bound
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Ω : Set H}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω) :
    ∃ C : NNReal, ∀ z : H, ‖fderiv ℝ (φ : H → ℝ) z‖ ≤ C := by
  have hcont :
      Continuous (fun z : H ↦ fderiv ℝ (φ : H → ℝ) z) :=
    φ.smooth.continuous_fderiv (by simp)
  have hnorm_cont :
      Continuous (fun z : H ↦ ‖fderiv ℝ (φ : H → ℝ) z‖) :=
    continuous_norm.comp hcont
  rcases
      φ.compact_support.exists_bound_of_continuousOn
        hnorm_cont.continuousOn with
    ⟨C₀, hC₀⟩
  let C : ℝ := max C₀ 0
  have hC_nonneg : 0 ≤ C := le_max_right C₀ 0
  refine ⟨⟨C, hC_nonneg⟩, ?_⟩
  intro z
  by_cases hz : z ∈ tsupport (φ : H → ℝ)
  · have hz_bound :
        ‖(‖fderiv ℝ (φ : H → ℝ) z‖ : ℝ)‖ ≤ C :=
      (hC₀ z hz).trans (le_max_left C₀ 0)
    change ‖fderiv ℝ (φ : H → ℝ) z‖ ≤ C
    simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hz_bound
  · have hz_deriv : fderiv ℝ (φ : H → ℝ) z = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := (φ : H → ℝ)) hz
    simp [hz_deriv, C]

/--
%%handwave
name:
  Smooth coordinate tests vary Lipschitzly along unit rays
statement:
  A smooth compactly supported coordinate test has a constant \(L\) such that
  \(|\varphi(r\theta)-\varphi(\theta)|\le L |r-1|\) for every unit vector
  \(\theta\) and every real radius \(r\).
proof:
  Use the global bound for the operator norm of the differential and apply the
  mean value inequality on the convex model vector space to the two points
  \(r\theta\) and \(\theta\).
-/
private theorem smoothCompactlySupportedCoordinateFunction_exists_radial_lipschitz_bound
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Ω : Set H}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω) :
    ∃ L : ℝ,
      0 ≤ L ∧
        ∀ (θ : Metric.sphere (0 : H) 1) (r : ℝ),
          ‖(φ : H → ℝ) (r • (θ : H)) - (φ : H → ℝ) (θ : H)‖ ≤
            L * ‖r - 1‖ := by
  obtain ⟨C, hC⟩ :=
    smoothCompactlySupportedCoordinateFunction_exists_fderiv_norm_bound φ
  refine ⟨C, C.2, ?_⟩
  intro θ r
  have hdiff :
      ∀ z ∈ (Set.univ : Set H),
        DifferentiableAt ℝ (φ : H → ℝ) z := by
    intro z _hz
    exact (φ.smooth.differentiable (by simp)) z
  have hbound :
      ∀ z ∈ (Set.univ : Set H),
        ‖fderiv ℝ (φ : H → ℝ) z‖ ≤ (C : ℝ) := by
    intro z _hz
    exact hC z
  have hmv :
      ‖(φ : H → ℝ) (r • (θ : H)) - (φ : H → ℝ) (θ : H)‖ ≤
        (C : ℝ) * ‖r • (θ : H) - (θ : H)‖ := by
    apply
      (convex_univ : Convex ℝ (Set.univ : Set H)).norm_image_sub_le_of_norm_fderiv_le
        (𝕜 := ℝ)
    · exact hdiff
    · exact hbound
    · simp
    · simp
  have hθ_norm : ‖(θ : H)‖ = (1 : ℝ) := by
    simpa [Metric.mem_sphere, dist_eq_norm] using θ.2
  have hsub :
      r • (θ : H) - (θ : H) = (r - 1) • (θ : H) := by
    simpa using (sub_smul r (1 : ℝ) (θ : H)).symm
  have hdist :
      ‖r • (θ : H) - (θ : H)‖ = ‖r - 1‖ := by
    rw [hsub, norm_smul, hθ_norm, mul_one]
  simpa [hdist] using hmv

/--
%%handwave
name:
  Weighted trace integrability controls the normal trace factor
statement:
  If the trace is integrable on the unit sphere, then its product with a fixed
  normal component \(\langle\theta,v\rangle\) is also integrable.
proof:
  The normal component is continuous on the compact unit sphere and bounded by
  \(\|v\|\).  Multiplication of an integrable function by a bounded measurable
  function preserves integrability.
-/
private theorem euclideanSobolev_unit_sphere_trace_inner_integrable_of_weighted
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    Integrable
      (fun θ : Metric.sphere (0 : H) 1 ↦
        τ (θ : H) * inner ℝ (θ : H) v)
      ((MeasureTheory.volume : Measure H).toSphere) := by
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  have hinner_cont : Continuous (fun θ : Metric.sphere (0 : H) 1 ↦
      inner ℝ (θ : H) v) :=
    continuous_subtype_val.inner continuous_const
  have hinner_aesm :
      AEStronglyMeasurable
        (fun θ : Metric.sphere (0 : H) 1 ↦ inner ℝ (θ : H) v) μS :=
    hinner_cont.aestronglyMeasurable
  have hinner_bound :
      ∀ᵐ θ ∂μS,
        ‖(fun θ : Metric.sphere (0 : H) 1 ↦
          inner ℝ (θ : H) v) θ‖ ≤ ‖v‖ :=
    Filter.Eventually.of_forall fun (θ : Metric.sphere (0 : H) 1) ↦ by
      have hθ_norm : ‖(θ : H)‖ = (1 : ℝ) := by
        simpa [Metric.mem_sphere, dist_eq_norm] using θ.2
      calc
        ‖inner ℝ (θ : H) v‖ ≤ ‖(θ : H)‖ * ‖v‖ :=
          norm_inner_le_norm (𝕜 := ℝ) (θ : H) v
        _ = ‖v‖ := by rw [hθ_norm, one_mul]
  have hmul := hτ_weight.1.mul_bdd hinner_aesm hinner_bound
  simpa [μS] using hmul

/--
%%handwave
name:
  The polar exact trace integrands have the simplified radial form
statement:
  On polar points \((\theta,r)\), the radial trace is \(\tau(\theta)\), the
  radial normal is \(\theta\), and the two exact trace collar weights reduce
  to the transition-profile derivative times
  \(\tau(\theta)\langle\theta,v\rangle\varphi(r\theta)\).
proof:
  Since \(\theta\) lies on the unit sphere and \(r>0\), one has
  \(\|r\theta\|=r\) and \(\|r\theta\|^{-1}r\theta=\theta\).  Substitute these
  identities in the definitions of the radial trace and oriented weights.
-/
private theorem euclideanSobolev_two_unit_collar_exact_trace_pairing_polar_integrands_simplify
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {τ : H → ℝ} (φ : H → ℝ) (v : H) {width : ℝ}
    (p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :
    euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
        width φ v (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) •
        euclideanSobolevUnitSphereRadialTrace τ
          (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) =
      ((deriv Real.smoothTransition
          (((1 : ℝ) - width / 2 - ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) /
            (width / 4)) *
        (-(1 : ℝ) / (width / 4))) *
        inner ℝ (p.1 : H) v *
        φ (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))) *
        τ (p.1 : H) ∧
    euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
        width φ v (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) •
        euclideanSobolevUnitSphereRadialTrace τ
          (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) =
      ((deriv Real.smoothTransition
          ((((p.2 : Set.Ioi (0 : ℝ)) : ℝ) - ((1 : ℝ) + width / 2)) /
            (width / 4)) *
        ((1 : ℝ) / (width / 4))) *
        inner ℝ (p.1 : H) v *
        φ (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))) *
        τ (p.1 : H) := by
  let z : H := ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)
  have hnorm : ‖z‖ = ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) := by
    simpa [z] using norm_polar_smul_unit_sphere (H := H) p
  have hradial :
      (‖z‖)⁻¹ • z = (p.1 : H) := by
    simpa [z] using invNorm_smul_polar_smul_unit_sphere (H := H) p
  have hinner : inner ℝ ((‖z‖)⁻¹ • z) v = inner ℝ (p.1 : H) v := by
    rw [hradial]
  have hinner_polar :
      inner ℝ
          ((((p.2 : Set.Ioi (0 : ℝ)) : ℝ)⁻¹ •
            (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)))) v =
        inner ℝ (p.1 : H) v := by
    simpa [z, hnorm] using hinner
  have htrace :
      euclideanSobolevUnitSphereRadialTrace τ z = τ (p.1 : H) := by
    simpa [z] using euclideanSobolevUnitSphereRadialTrace_polar
      (H := H) (τ := τ) p
  constructor
  · change
      euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
          width φ v z *
          euclideanSobolevUnitSphereRadialTrace τ z =
        ((deriv Real.smoothTransition
            (((1 : ℝ) - width / 2 - ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) /
              (width / 4)) *
          (-(1 : ℝ) / (width / 4))) *
          inner ℝ (p.1 : H) v * φ z) *
          τ (p.1 : H)
    rw [htrace]
    simp [euclideanSobolevUnitBallInnerOrientedRadialPairingWeight,
      hnorm, hinner_polar, z, mul_assoc]
  · change
      euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
          width φ v z *
          euclideanSobolevUnitSphereRadialTrace τ z =
        ((deriv Real.smoothTransition
            ((((p.2 : Set.Ioi (0 : ℝ)) : ℝ) - ((1 : ℝ) + width / 2)) /
              (width / 4)) *
          ((1 : ℝ) / (width / 4))) *
          inner ℝ (p.1 : H) v * φ z) *
          τ (p.1 : H)
    rw [htrace]
    simp [euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight,
      hnorm, hinner_polar, z, mul_assoc]

private def euclideanSobolevTwoUnitInnerRadialCollar
    (width : ℝ) : Set (Set.Ioi (0 : ℝ)) :=
  {r : Set.Ioi (0 : ℝ) |
    (1 : ℝ) - width < (r : ℝ) ∧ (r : ℝ) < 1}

private def euclideanSobolevTwoUnitOuterRadialCollar
    (width : ℝ) : Set (Set.Ioi (0 : ℝ)) :=
  {r : Set.Ioi (0 : ℝ) |
    (1 : ℝ) < (r : ℝ) ∧ (r : ℝ) < 1 + width}

private def euclideanSobolevTwoUnitInnerRadialProfileDeriv
    (width r : ℝ) : ℝ :=
  deriv Real.smoothTransition
      (((1 : ℝ) - width / 2 - r) / (width / 4)) *
    (-(1 : ℝ) / (width / 4))

private def euclideanSobolevTwoUnitOuterRadialProfileDeriv
    (width r : ℝ) : ℝ :=
  deriv Real.smoothTransition
      ((r - ((1 : ℝ) + width / 2)) / (width / 4)) *
    ((1 : ℝ) / (width / 4))

private theorem euclideanSobolevTwoUnitInnerRadialCollar_measurableSet
    (width : ℝ) :
    MeasurableSet (euclideanSobolevTwoUnitInnerRadialCollar width) := by
  unfold euclideanSobolevTwoUnitInnerRadialCollar
  exact
    (isOpen_lt continuous_const continuous_subtype_val).measurableSet.inter
      (isOpen_lt continuous_subtype_val continuous_const).measurableSet

private theorem euclideanSobolevTwoUnitOuterRadialCollar_measurableSet
    (width : ℝ) :
    MeasurableSet (euclideanSobolevTwoUnitOuterRadialCollar width) := by
  unfold euclideanSobolevTwoUnitOuterRadialCollar
  exact
    (isOpen_lt continuous_const continuous_subtype_val).measurableSet.inter
      (isOpen_lt continuous_subtype_val continuous_const).measurableSet

private theorem euclideanSobolevTwoUnitInnerRadialCollar_measure_lt_top
    (n : ℕ) {width : ℝ} :
    MeasureTheory.Measure.volumeIoiPow n
        (euclideanSobolevTwoUnitInnerRadialCollar width) < (∞ : ℝ≥0∞) := by
  have hsubset :
      euclideanSobolevTwoUnitInnerRadialCollar width ⊆
        Set.Iio (⟨(2 : ℝ), by norm_num⟩ : Set.Ioi (0 : ℝ)) := by
    intro r hr
    change ((r : Set.Ioi (0 : ℝ)) : ℝ) < 2
    exact lt_trans hr.2 (by norm_num)
  exact (measure_mono hsubset).trans_lt (by
    rw [MeasureTheory.Measure.volumeIoiPow_apply_Iio]
    exact ENNReal.ofReal_lt_top)

private theorem euclideanSobolevTwoUnitOuterRadialCollar_measure_lt_top
    (n : ℕ) {width : ℝ} (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) :
    MeasureTheory.Measure.volumeIoiPow n
        (euclideanSobolevTwoUnitOuterRadialCollar width) < (∞ : ℝ≥0∞) := by
  have hsubset :
      euclideanSobolevTwoUnitOuterRadialCollar width ⊆
        Set.Iio (⟨(2 : ℝ), by norm_num⟩ : Set.Ioi (0 : ℝ)) := by
    intro r hr
    change ((r : Set.Ioi (0 : ℝ)) : ℝ) < 2
    linarith [hr.2, hwidth_le_quarter]
  exact (measure_mono hsubset).trans_lt (by
    rw [MeasureTheory.Measure.volumeIoiPow_apply_Iio]
    exact ENNReal.ofReal_lt_top)

private theorem volumeIoiPow_apply_le_of_pow_le_on_set
    (n : ℕ) {s : Set (Set.Ioi (0 : ℝ))} (hs : MeasurableSet s)
    {M : ℝ} (_hM_nonneg : 0 ≤ M)
    (hpow : ∀ r ∈ s, (((r : Set.Ioi (0 : ℝ)) : ℝ) ^ n) ≤ M) :
    MeasureTheory.Measure.volumeIoiPow n s ≤
      ENNReal.ofReal M *
        (Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ)) s := by
  rw [MeasureTheory.Measure.volumeIoiPow, withDensity_apply _ hs]
  calc
    ∫⁻ r in s, ENNReal.ofReal (((r : Set.Ioi (0 : ℝ)) : ℝ) ^ n)
        ∂(Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ))
        ≤ ∫⁻ _r in s, ENNReal.ofReal M
            ∂(Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ)) := by
          exact setLIntegral_mono' hs
            (fun r hr ↦ ENNReal.ofReal_le_ofReal (hpow r hr))
    _ = ENNReal.ofReal M *
        (Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ)) s := by
          rw [setLIntegral_const]

private theorem euclideanSobolevTwoUnitInnerRadialCollar_comap_volume_le_width
    {width : ℝ} :
    (Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ))
        (euclideanSobolevTwoUnitInnerRadialCollar width) ≤
      ENNReal.ofReal width := by
  rw [comap_subtype_coe_apply measurableSet_Ioi
    (MeasureTheory.volume : Measure ℝ)
    (euclideanSobolevTwoUnitInnerRadialCollar width)]
  calc
    (MeasureTheory.volume : Measure ℝ)
        (((↑) : Set.Ioi (0 : ℝ) → ℝ) ''
          euclideanSobolevTwoUnitInnerRadialCollar width)
        ≤ (MeasureTheory.volume : Measure ℝ)
            (Set.Ioo ((1 : ℝ) - width) 1) := by
          refine measure_mono ?_
          intro x hx
          rcases hx with ⟨r, hr, rfl⟩
          exact hr
    _ = ENNReal.ofReal width := by
          rw [Real.volume_Ioo]
          ring_nf

private theorem euclideanSobolevTwoUnitOuterRadialCollar_comap_volume_le_width
    {width : ℝ} :
    (Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ))
        (euclideanSobolevTwoUnitOuterRadialCollar width) ≤
      ENNReal.ofReal width := by
  rw [comap_subtype_coe_apply measurableSet_Ioi
    (MeasureTheory.volume : Measure ℝ)
    (euclideanSobolevTwoUnitOuterRadialCollar width)]
  calc
    (MeasureTheory.volume : Measure ℝ)
        (((↑) : Set.Ioi (0 : ℝ) → ℝ) ''
          euclideanSobolevTwoUnitOuterRadialCollar width)
        ≤ (MeasureTheory.volume : Measure ℝ)
            (Set.Ioo (1 : ℝ) (1 + width)) := by
          refine measure_mono ?_
          intro x hx
          rcases hx with ⟨r, hr, rfl⟩
          exact hr
    _ = ENNReal.ofReal width := by
          rw [Real.volume_Ioo]
          ring_nf

private theorem euclideanSobolevTwoUnitInnerRadialCollar_volumeIoiPow_real_le_width
    (n : ℕ) {width : ℝ} (hwidth_pos : 0 < width) :
    (MeasureTheory.Measure.volumeIoiPow n).real
        (euclideanSobolevTwoUnitInnerRadialCollar width) ≤
      ((2 : ℝ) ^ n) * width := by
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) n
  have hμ_le_density :
      MeasureTheory.Measure.volumeIoiPow n
          (euclideanSobolevTwoUnitInnerRadialCollar width) ≤
        ENNReal.ofReal ((2 : ℝ) ^ n) *
          (Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ))
            (euclideanSobolevTwoUnitInnerRadialCollar width) := by
    refine
      volumeIoiPow_apply_le_of_pow_le_on_set n
        (euclideanSobolevTwoUnitInnerRadialCollar_measurableSet width)
        hpow_nonneg ?_
    intro r hr
    have hr_nonneg : 0 ≤ ((r : Set.Ioi (0 : ℝ)) : ℝ) := le_of_lt r.2
    have hr_le_two : ((r : Set.Ioi (0 : ℝ)) : ℝ) ≤ 2 :=
      le_of_lt (lt_trans hr.2 (by norm_num))
    exact pow_le_pow_left₀ hr_nonneg hr_le_two n
  have hbase :
      (Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ))
          (euclideanSobolevTwoUnitInnerRadialCollar width) ≤
        ENNReal.ofReal width :=
    euclideanSobolevTwoUnitInnerRadialCollar_comap_volume_le_width
  have hμ_le :
      MeasureTheory.Measure.volumeIoiPow n
          (euclideanSobolevTwoUnitInnerRadialCollar width) ≤
        ENNReal.ofReal (((2 : ℝ) ^ n) * width) := by
    calc
      MeasureTheory.Measure.volumeIoiPow n
          (euclideanSobolevTwoUnitInnerRadialCollar width)
          ≤ ENNReal.ofReal ((2 : ℝ) ^ n) *
            (Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ))
              (euclideanSobolevTwoUnitInnerRadialCollar width) :=
            hμ_le_density
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal width := by
            gcongr
      _ = ENNReal.ofReal (((2 : ℝ) ^ n) * width) := by
            exact (ENNReal.ofReal_mul hpow_nonneg).symm
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg hpow_nonneg hwidth_pos.le) hμ_le

private theorem euclideanSobolevTwoUnitOuterRadialCollar_volumeIoiPow_real_le_width
    (n : ℕ) {width : ℝ} (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) :
    (MeasureTheory.Measure.volumeIoiPow n).real
        (euclideanSobolevTwoUnitOuterRadialCollar width) ≤
      ((2 : ℝ) ^ n) * width := by
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) n
  have hμ_le_density :
      MeasureTheory.Measure.volumeIoiPow n
          (euclideanSobolevTwoUnitOuterRadialCollar width) ≤
        ENNReal.ofReal ((2 : ℝ) ^ n) *
          (Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ))
            (euclideanSobolevTwoUnitOuterRadialCollar width) := by
    refine
      volumeIoiPow_apply_le_of_pow_le_on_set n
        (euclideanSobolevTwoUnitOuterRadialCollar_measurableSet width)
        hpow_nonneg ?_
    intro r hr
    have hr_nonneg : 0 ≤ ((r : Set.Ioi (0 : ℝ)) : ℝ) := le_of_lt r.2
    have hr_le_two : ((r : Set.Ioi (0 : ℝ)) : ℝ) ≤ 2 := by
      linarith [hr.2, hwidth_le_quarter]
    exact pow_le_pow_left₀ hr_nonneg hr_le_two n
  have hbase :
      (Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ))
          (euclideanSobolevTwoUnitOuterRadialCollar width) ≤
        ENNReal.ofReal width :=
    euclideanSobolevTwoUnitOuterRadialCollar_comap_volume_le_width
  have hμ_le :
      MeasureTheory.Measure.volumeIoiPow n
          (euclideanSobolevTwoUnitOuterRadialCollar width) ≤
        ENNReal.ofReal (((2 : ℝ) ^ n) * width) := by
    calc
      MeasureTheory.Measure.volumeIoiPow n
          (euclideanSobolevTwoUnitOuterRadialCollar width)
          ≤ ENNReal.ofReal ((2 : ℝ) ^ n) *
            (Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ))
              (euclideanSobolevTwoUnitOuterRadialCollar width) :=
            hμ_le_density
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal width := by
            gcongr
      _ = ENNReal.ofReal (((2 : ℝ) ^ n) * width) := by
            exact (ENNReal.ofReal_mul hpow_nonneg).symm
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg hpow_nonneg hwidth_pos.le) hμ_le

private theorem euclideanSobolevTwoUnitInnerRadialProfile_arg_mem_Icc
    {width : ℝ} (hwidth_pos : 0 < width)
    {r : Set.Ioi (0 : ℝ)}
    (hr : r ∈ euclideanSobolevTwoUnitInnerRadialCollar width) :
    (((1 : ℝ) - width / 2 - ((r : Set.Ioi (0 : ℝ)) : ℝ)) /
        (width / 4)) ∈ Set.Icc (-(2 : ℝ)) 2 := by
  have hden : 0 < width / 4 := by linarith
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith [hr.2]
  · rw [div_le_iff₀ hden]
    nlinarith [hr.1]

private theorem euclideanSobolevTwoUnitOuterRadialProfile_arg_mem_Icc
    {width : ℝ} (hwidth_pos : 0 < width)
    {r : Set.Ioi (0 : ℝ)}
    (hr : r ∈ euclideanSobolevTwoUnitOuterRadialCollar width) :
    ((((r : Set.Ioi (0 : ℝ)) : ℝ) - ((1 : ℝ) + width / 2)) /
        (width / 4)) ∈ Set.Icc (-(2 : ℝ)) 2 := by
  have hden : 0 < width / 4 := by linarith
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith [hr.1]
  · rw [div_le_iff₀ hden]
    nlinarith [hr.2]

private theorem euclideanSobolevTwoUnitInnerRadialProfileDeriv_measurable
    (width : ℝ) :
    Measurable
      (fun r : Set.Ioi (0 : ℝ) ↦
        euclideanSobolevTwoUnitInnerRadialProfileDeriv
          width ((r : Set.Ioi (0 : ℝ)) : ℝ)) := by
  have hderiv_cont :
      Continuous (fun t : ℝ ↦ deriv Real.smoothTransition t) := by
    have hsmooth : ContDiff ℝ ∞ Real.smoothTransition :=
      Real.smoothTransition.contDiff
    exact hsmooth.continuous_deriv (by simp)
  have harg_cont :
      Continuous
        (fun r : Set.Ioi (0 : ℝ) ↦
          (((1 : ℝ) - width / 2 - ((r : Set.Ioi (0 : ℝ)) : ℝ)) /
            (width / 4))) := by
    fun_prop
  simpa [euclideanSobolevTwoUnitInnerRadialProfileDeriv] using
    ((hderiv_cont.comp harg_cont).measurable).mul measurable_const

private theorem euclideanSobolevTwoUnitOuterRadialProfileDeriv_measurable
    (width : ℝ) :
    Measurable
      (fun r : Set.Ioi (0 : ℝ) ↦
        euclideanSobolevTwoUnitOuterRadialProfileDeriv
          width ((r : Set.Ioi (0 : ℝ)) : ℝ)) := by
  have hderiv_cont :
      Continuous (fun t : ℝ ↦ deriv Real.smoothTransition t) := by
    have hsmooth : ContDiff ℝ ∞ Real.smoothTransition :=
      Real.smoothTransition.contDiff
    exact hsmooth.continuous_deriv (by simp)
  have harg_cont :
      Continuous
        (fun r : Set.Ioi (0 : ℝ) ↦
          ((((r : Set.Ioi (0 : ℝ)) : ℝ) - ((1 : ℝ) + width / 2)) /
            (width / 4))) := by
    fun_prop
  simpa [euclideanSobolevTwoUnitOuterRadialProfileDeriv] using
    ((hderiv_cont.comp harg_cont).measurable).mul measurable_const

private theorem euclideanSobolevTwoUnitInnerRadialProfileDeriv_norm_le
    {width C : ℝ} (hwidth_pos : 0 < width)
    (hC : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ C)
    {r : Set.Ioi (0 : ℝ)}
    (hr : r ∈ euclideanSobolevTwoUnitInnerRadialCollar width) :
    ‖euclideanSobolevTwoUnitInnerRadialProfileDeriv
        width ((r : Set.Ioi (0 : ℝ)) : ℝ)‖ ≤ C * (4 / width) := by
  have harg :=
    euclideanSobolevTwoUnitInnerRadialProfile_arg_mem_Icc hwidth_pos hr
  simpa [euclideanSobolevTwoUnitInnerRadialProfileDeriv,
    unit_inner_transition_profile_deriv_eq] using
    unit_inner_transition_profile_deriv_norm_le
      (width := width) (C := C) (r := ((r : Set.Ioi (0 : ℝ)) : ℝ))
      hwidth_pos hC harg

private theorem euclideanSobolevTwoUnitOuterRadialProfileDeriv_norm_le
    {width C : ℝ} (hwidth_pos : 0 < width)
    (hC : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ C)
    {r : Set.Ioi (0 : ℝ)}
    (hr : r ∈ euclideanSobolevTwoUnitOuterRadialCollar width) :
    ‖euclideanSobolevTwoUnitOuterRadialProfileDeriv
        width ((r : Set.Ioi (0 : ℝ)) : ℝ)‖ ≤ C * (4 / width) := by
  have harg :=
    euclideanSobolevTwoUnitOuterRadialProfile_arg_mem_Icc hwidth_pos hr
  simpa [euclideanSobolevTwoUnitOuterRadialProfileDeriv,
    annulus_inner_transition_profile_deriv_eq] using
    annulus_inner_transition_profile_deriv_norm_le
      (width := width) (C := C) (r := ((r : Set.Ioi (0 : ℝ)) : ℝ))
      hwidth_pos hC harg

private theorem euclideanSobolevTwoUnitInnerRadialCollar_dist_one_le_one
    {width : ℝ} (hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    {r : Set.Ioi (0 : ℝ)}
    (hr : r ∈ euclideanSobolevTwoUnitInnerRadialCollar width) :
    ‖((r : Set.Ioi (0 : ℝ)) : ℝ) - 1‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [hr.1, hwidth_pos, hwidth_le_quarter]
  · linarith [hr.2]

private theorem euclideanSobolevTwoUnitInnerRadialCollar_dist_one_le_width
    {width : ℝ} (hwidth_pos : 0 < width)
    {r : Set.Ioi (0 : ℝ)}
    (hr : r ∈ euclideanSobolevTwoUnitInnerRadialCollar width) :
    ‖((r : Set.Ioi (0 : ℝ)) : ℝ) - 1‖ ≤ width := by
  rw [Real.norm_eq_abs]
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [hr.1]
  · linarith [hr.2, hwidth_pos]

private theorem euclideanSobolevTwoUnitOuterRadialCollar_dist_one_le_one
    {width : ℝ} (_hwidth_pos : 0 < width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    {r : Set.Ioi (0 : ℝ)}
    (hr : r ∈ euclideanSobolevTwoUnitOuterRadialCollar width) :
    ‖((r : Set.Ioi (0 : ℝ)) : ℝ) - 1‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [hr.1]
  · linarith [hr.2, hwidth_le_quarter]

private theorem euclideanSobolevTwoUnitOuterRadialCollar_dist_one_le_width
    {width : ℝ} (hwidth_pos : 0 < width)
    {r : Set.Ioi (0 : ℝ)}
    (hr : r ∈ euclideanSobolevTwoUnitOuterRadialCollar width) :
    ‖((r : Set.Ioi (0 : ℝ)) : ℝ) - 1‖ ≤ width := by
  rw [Real.norm_eq_abs]
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [hr.1, hwidth_pos]
  · linarith [hr.2]

private theorem integrableOn_volumeIoiPow_of_measurable_bounded
    {n : ℕ} {s : Set (Set.Ioi (0 : ℝ))}
    (hs_meas : MeasurableSet s)
    (hs_finite : MeasureTheory.Measure.volumeIoiPow n s < (∞ : ℝ≥0∞))
    {f : Set.Ioi (0 : ℝ) → ℝ} (hf_meas : Measurable f)
    (C : ℝ) (hf_bound : ∀ r ∈ s, ‖f r‖ ≤ C) :
    IntegrableOn f s (MeasureTheory.Measure.volumeIoiPow n) := by
  refine IntegrableOn.of_bound hs_finite
    hf_meas.aestronglyMeasurable.restrict C ?_
  filter_upwards [ae_restrict_mem hs_meas] with r hr
  exact hf_bound r hr

private noncomputable def euclideanSobolevTwoUnitScalarRadialPairing
    (n : ℕ) (width a : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  (∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
      (euclideanSobolevTwoUnitInnerRadialProfileDeriv
          width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
        a * Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ))
      ∂(MeasureTheory.Measure.volumeIoiPow n)) +
    ∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
      (euclideanSobolevTwoUnitOuterRadialProfileDeriv
          width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
        a * Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ))
      ∂(MeasureTheory.Measure.volumeIoiPow n)

private noncomputable def euclideanSobolevTwoUnitScalarRadialVariationPairing
    (n : ℕ) (width a : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  (∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
      (euclideanSobolevTwoUnitInnerRadialProfileDeriv
          width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
        a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1))
      ∂(MeasureTheory.Measure.volumeIoiPow n)) +
    ∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
      (euclideanSobolevTwoUnitOuterRadialProfileDeriv
          width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
        a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1))
      ∂(MeasureTheory.Measure.volumeIoiPow n)

private noncomputable def euclideanSobolevTwoUnitScalarRadialFrozenPairing
    (n : ℕ) (width c : ℝ) : ℝ :=
  (∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
      euclideanSobolevTwoUnitInnerRadialProfileDeriv
        width ((r : Set.Ioi (0 : ℝ)) : ℝ) * c
      ∂(MeasureTheory.Measure.volumeIoiPow n)) +
    ∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
      euclideanSobolevTwoUnitOuterRadialProfileDeriv
        width ((r : Set.Ioi (0 : ℝ)) : ℝ) * c
      ∂(MeasureTheory.Measure.volumeIoiPow n)

/--
%%handwave
name:
  The scalar two-collar summands are integrable
statement:
  On the two finite radial collars, the transition derivative times either
  \(\Psi(r)-\Psi(1)\) or the frozen coefficient \(a\Psi(1)\) is integrable
  with respect to the polar radial measure.
proof:
  The collars lie in a fixed compact subinterval of \((0,\infty)\).  The
  transition derivative is bounded there, and the Lipschitz bound on
  \(\Psi\) gives a uniform bound for the variation term.
-/
private theorem euclideanSobolevTwoUnitScalarRadialPairing_split_integrability
    (n : ℕ) {width : ℝ} (_hwidth_pos : 0 < width)
    (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    (a : ℝ) (Ψ : ℝ → ℝ) (_hΨ_meas : Measurable Ψ)
    (_hΨ_lipschitz : ∃ L : ℝ,
      0 ≤ L ∧ ∀ r : ℝ, ‖Ψ r - Ψ 1‖ ≤ L * ‖r - 1‖) :
    IntegrableOn
        (fun r : Set.Ioi (0 : ℝ) ↦
          euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1))
        (euclideanSobolevTwoUnitInnerRadialCollar width)
        (MeasureTheory.Measure.volumeIoiPow n) ∧
      IntegrableOn
        (fun r : Set.Ioi (0 : ℝ) ↦
          euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            (a * Ψ 1))
        (euclideanSobolevTwoUnitInnerRadialCollar width)
        (MeasureTheory.Measure.volumeIoiPow n) ∧
      IntegrableOn
        (fun r : Set.Ioi (0 : ℝ) ↦
          euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1))
        (euclideanSobolevTwoUnitOuterRadialCollar width)
        (MeasureTheory.Measure.volumeIoiPow n) ∧
      IntegrableOn
        (fun r : Set.Ioi (0 : ℝ) ↦
          euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            (a * Ψ 1))
        (euclideanSobolevTwoUnitOuterRadialCollar width)
        (MeasureTheory.Measure.volumeIoiPow n) := by
  rcases exists_smoothTransition_deriv_bound_Icc_neg_two_two with
    ⟨Cprofile, hCprofile_ge_one, hCprofile⟩
  rcases _hΨ_lipschitz with ⟨L, hL_nonneg, hΨ_lipschitz⟩
  have hCprofile_nonneg : 0 ≤ Cprofile :=
    le_trans zero_le_one hCprofile_ge_one
  have hscale_nonneg : 0 ≤ Cprofile * (4 / width) := by
    exact mul_nonneg hCprofile_nonneg (by positivity)
  have hinner_meas :=
    euclideanSobolevTwoUnitInnerRadialCollar_measurableSet width
  have houter_meas :=
    euclideanSobolevTwoUnitOuterRadialCollar_measurableSet width
  have hinner_finite :
      MeasureTheory.Measure.volumeIoiPow n
          (euclideanSobolevTwoUnitInnerRadialCollar width) < (∞ : ℝ≥0∞) :=
    euclideanSobolevTwoUnitInnerRadialCollar_measure_lt_top n
  have houter_finite :
      MeasureTheory.Measure.volumeIoiPow n
          (euclideanSobolevTwoUnitOuterRadialCollar width) < (∞ : ℝ≥0∞) :=
    euclideanSobolevTwoUnitOuterRadialCollar_measure_lt_top
      n _hwidth_le_quarter
  have hΨ_sub_meas :
      Measurable
        (fun r : Set.Ioi (0 : ℝ) ↦
          Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1) :=
    (_hΨ_meas.comp measurable_subtype_coe).sub measurable_const
  have hinner_profile_meas :=
    euclideanSobolevTwoUnitInnerRadialProfileDeriv_measurable width
  have houter_profile_meas :=
    euclideanSobolevTwoUnitOuterRadialProfileDeriv_measurable width
  have hinner_var_meas :
      Measurable
        (fun r : Set.Ioi (0 : ℝ) ↦
          euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)) :=
    (hinner_profile_meas.mul measurable_const).mul hΨ_sub_meas
  have hinner_frozen_meas :
      Measurable
        (fun r : Set.Ioi (0 : ℝ) ↦
          euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            (a * Ψ 1)) :=
    hinner_profile_meas.mul measurable_const
  have houter_var_meas :
      Measurable
        (fun r : Set.Ioi (0 : ℝ) ↦
          euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)) :=
    (houter_profile_meas.mul measurable_const).mul hΨ_sub_meas
  have houter_frozen_meas :
      Measurable
        (fun r : Set.Ioi (0 : ℝ) ↦
          euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            (a * Ψ 1)) :=
    houter_profile_meas.mul measurable_const
  have hinner_var_bound :
      ∀ r ∈ euclideanSobolevTwoUnitInnerRadialCollar width,
        ‖euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)‖ ≤
          (Cprofile * (4 / width) * ‖a‖) * L := by
    intro r hr
    have hprofile :=
      euclideanSobolevTwoUnitInnerRadialProfileDeriv_norm_le
        _hwidth_pos hCprofile hr
    have hdist :=
      euclideanSobolevTwoUnitInnerRadialCollar_dist_one_le_one
        _hwidth_pos _hwidth_le_quarter hr
    have hΨ_bound :
        ‖Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1‖ ≤ L := by
      calc
        ‖Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1‖
            ≤ L * ‖((r : Set.Ioi (0 : ℝ)) : ℝ) - 1‖ :=
              hΨ_lipschitz ((r : Set.Ioi (0 : ℝ)) : ℝ)
        _ ≤ L * 1 := mul_le_mul_of_nonneg_left hdist hL_nonneg
        _ = L := by ring
    calc
      ‖euclideanSobolevTwoUnitInnerRadialProfileDeriv
            width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
          a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)‖
          =
            (‖euclideanSobolevTwoUnitInnerRadialProfileDeriv
                width ((r : Set.Ioi (0 : ℝ)) : ℝ)‖ * ‖a‖) *
              ‖Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1‖ := by
              rw [norm_mul, norm_mul]
      _ ≤ (Cprofile * (4 / width) * ‖a‖) * L := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hprofile (norm_nonneg a))
          hΨ_bound
          (norm_nonneg _)
          (mul_nonneg hscale_nonneg (norm_nonneg a))
  have houter_var_bound :
      ∀ r ∈ euclideanSobolevTwoUnitOuterRadialCollar width,
        ‖euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)‖ ≤
          (Cprofile * (4 / width) * ‖a‖) * L := by
    intro r hr
    have hprofile :=
      euclideanSobolevTwoUnitOuterRadialProfileDeriv_norm_le
        _hwidth_pos hCprofile hr
    have hdist :=
      euclideanSobolevTwoUnitOuterRadialCollar_dist_one_le_one
        _hwidth_pos _hwidth_le_quarter hr
    have hΨ_bound :
        ‖Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1‖ ≤ L := by
      calc
        ‖Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1‖
            ≤ L * ‖((r : Set.Ioi (0 : ℝ)) : ℝ) - 1‖ :=
              hΨ_lipschitz ((r : Set.Ioi (0 : ℝ)) : ℝ)
        _ ≤ L * 1 := mul_le_mul_of_nonneg_left hdist hL_nonneg
        _ = L := by ring
    calc
      ‖euclideanSobolevTwoUnitOuterRadialProfileDeriv
            width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
          a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)‖
          =
            (‖euclideanSobolevTwoUnitOuterRadialProfileDeriv
                width ((r : Set.Ioi (0 : ℝ)) : ℝ)‖ * ‖a‖) *
              ‖Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1‖ := by
              rw [norm_mul, norm_mul]
      _ ≤ (Cprofile * (4 / width) * ‖a‖) * L := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hprofile (norm_nonneg a))
          hΨ_bound
          (norm_nonneg _)
          (mul_nonneg hscale_nonneg (norm_nonneg a))
  have hinner_frozen_bound :
      ∀ r ∈ euclideanSobolevTwoUnitInnerRadialCollar width,
        ‖euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            (a * Ψ 1)‖ ≤
          Cprofile * (4 / width) * ‖a * Ψ 1‖ := by
    intro r hr
    have hprofile :=
      euclideanSobolevTwoUnitInnerRadialProfileDeriv_norm_le
        _hwidth_pos hCprofile hr
    calc
      ‖euclideanSobolevTwoUnitInnerRadialProfileDeriv
            width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
          (a * Ψ 1)‖
          =
            ‖euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ)‖ * ‖a * Ψ 1‖ := by
            rw [norm_mul]
      _ ≤ Cprofile * (4 / width) * ‖a * Ψ 1‖ :=
        mul_le_mul_of_nonneg_right hprofile (norm_nonneg _)
  have houter_frozen_bound :
      ∀ r ∈ euclideanSobolevTwoUnitOuterRadialCollar width,
        ‖euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            (a * Ψ 1)‖ ≤
          Cprofile * (4 / width) * ‖a * Ψ 1‖ := by
    intro r hr
    have hprofile :=
      euclideanSobolevTwoUnitOuterRadialProfileDeriv_norm_le
        _hwidth_pos hCprofile hr
    calc
      ‖euclideanSobolevTwoUnitOuterRadialProfileDeriv
            width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
          (a * Ψ 1)‖
          =
            ‖euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ)‖ * ‖a * Ψ 1‖ := by
            rw [norm_mul]
      _ ≤ Cprofile * (4 / width) * ‖a * Ψ 1‖ :=
        mul_le_mul_of_nonneg_right hprofile (norm_nonneg _)
  exact
    ⟨integrableOn_volumeIoiPow_of_measurable_bounded
        hinner_meas hinner_finite hinner_var_meas
        ((Cprofile * (4 / width) * ‖a‖) * L) hinner_var_bound,
      integrableOn_volumeIoiPow_of_measurable_bounded
        hinner_meas hinner_finite hinner_frozen_meas
        (Cprofile * (4 / width) * ‖a * Ψ 1‖) hinner_frozen_bound,
      integrableOn_volumeIoiPow_of_measurable_bounded
        houter_meas houter_finite houter_var_meas
        ((Cprofile * (4 / width) * ‖a‖) * L) houter_var_bound,
      integrableOn_volumeIoiPow_of_measurable_bounded
        houter_meas houter_finite houter_frozen_meas
        (Cprofile * (4 / width) * ‖a * Ψ 1‖) houter_frozen_bound⟩

/--
%%handwave
name:
  Scalar radial pairing splits into variation and frozen parts
statement:
  The scalar two-collar radial pairing equals the sum of the pairing with
  \(\Psi(r)-\Psi(1)\) and the frozen pairing with coefficient \(a\Psi(1)\).
proof:
  Pointwise, \(a\Psi(r)=a(\Psi(r)-\Psi(1))+a\Psi(1)\).  Apply linearity of the
  Bochner integral on the two compact radial collars.
-/
private theorem euclideanSobolevTwoUnitScalarRadialPairing_eq_variation_add_frozen
    (n : ℕ) {width : ℝ} (_hwidth_pos : 0 < width)
    (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    (a : ℝ) (Ψ : ℝ → ℝ) (_hΨ_meas : Measurable Ψ)
    (_hΨ_lipschitz : ∃ L : ℝ,
      0 ≤ L ∧ ∀ r : ℝ, ‖Ψ r - Ψ 1‖ ≤ L * ‖r - 1‖) :
    euclideanSobolevTwoUnitScalarRadialPairing n width a Ψ =
      euclideanSobolevTwoUnitScalarRadialVariationPairing n width a Ψ +
        euclideanSobolevTwoUnitScalarRadialFrozenPairing n width (a * Ψ 1) := by
  obtain ⟨hinner_var, hinner_frozen, houter_var, houter_frozen⟩ :=
    euclideanSobolevTwoUnitScalarRadialPairing_split_integrability
      n _hwidth_pos _hwidth_le_quarter a Ψ _hΨ_meas _hΨ_lipschitz
  dsimp [euclideanSobolevTwoUnitScalarRadialPairing,
    euclideanSobolevTwoUnitScalarRadialVariationPairing,
    euclideanSobolevTwoUnitScalarRadialFrozenPairing]
  have hinner :
      (∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
          euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ)
          ∂(MeasureTheory.Measure.volumeIoiPow n)) =
        (∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
          euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)
          ∂(MeasureTheory.Measure.volumeIoiPow n)) +
        ∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
          euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            (a * Ψ 1)
          ∂(MeasureTheory.Measure.volumeIoiPow n) := by
    rw [← integral_add
      (μ := (MeasureTheory.Measure.volumeIoiPow n).restrict
        (euclideanSobolevTwoUnitInnerRadialCollar width))
      hinner_var hinner_frozen]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro r
    ring
  have houter :
      (∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
          euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ)
          ∂(MeasureTheory.Measure.volumeIoiPow n)) =
        (∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
          euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)
          ∂(MeasureTheory.Measure.volumeIoiPow n)) +
        ∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
          euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            (a * Ψ 1)
          ∂(MeasureTheory.Measure.volumeIoiPow n) := by
    rw [← integral_add
      (μ := (MeasureTheory.Measure.volumeIoiPow n).restrict
        (euclideanSobolevTwoUnitOuterRadialCollar width))
      houter_var houter_frozen]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro r
    ring
  rw [hinner, houter]
  ring

/--
%%handwave
name:
  The radial variation part is linear in the collar width
statement:
  If \(\Psi\) varies Lipschitzly from radius one, then the variation part of the
  scalar two-collar radial pairing is bounded by \(A|a|\delta\).
proof:
  On both active collars \(|r-1|\le\delta\), while the profile derivative has
  size \(O(1/\delta)\) and the radial collar has measure \(O(\delta)\).  The
  weighted density \(r^n\) is uniformly bounded on \(3/4\le r\le5/4\).
-/
private theorem euclideanSobolevTwoUnitScalarRadialVariationPairing_norm_le_width
    (n : ℕ) (Cprofile LΦ : ℝ)
    (_hCprofile_ge_one : 1 ≤ Cprofile)
    (_hCprofile : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ Cprofile)
    (_hLΦ_nonneg : 0 ≤ LΦ) :
    ∃ A : ℝ,
      0 ≤ A ∧
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
          (a : ℝ) (Ψ : ℝ → ℝ),
          Measurable Ψ →
          (∀ r : ℝ, ‖Ψ r - Ψ 1‖ ≤ LΦ * ‖r - 1‖) →
          ‖euclideanSobolevTwoUnitScalarRadialVariationPairing
              n width a Ψ‖ ≤ A * ‖a‖ * width := by
  refine ⟨8 * Cprofile * LΦ * ((2 : ℝ) ^ n), ?_, ?_⟩
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (le_trans zero_le_one _hCprofile_ge_one))
        _hLΦ_nonneg)
      (pow_nonneg (by norm_num) n)
  intro width hwidth_pos hwidth_le_quarter a Ψ _hΨ_meas hΨ
  have hCprofile_nonneg : 0 ≤ Cprofile :=
    le_trans zero_le_one _hCprofile_ge_one
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) n
  have hscale_nonneg : 0 ≤ Cprofile * (4 / width) := by
    exact mul_nonneg hCprofile_nonneg (by positivity)
  have hvar_bound_nonneg :
      0 ≤ (Cprofile * (4 / width) * ‖a‖) * (LΦ * width) := by
    exact mul_nonneg
      (mul_nonneg hscale_nonneg (norm_nonneg a))
      (mul_nonneg _hLΦ_nonneg hwidth_pos.le)
  have hinner_pointwise :
      ∀ r ∈ euclideanSobolevTwoUnitInnerRadialCollar width,
        ‖euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)‖ ≤
          (Cprofile * (4 / width) * ‖a‖) * (LΦ * width) := by
    intro r hr
    have hprofile :=
      euclideanSobolevTwoUnitInnerRadialProfileDeriv_norm_le
        hwidth_pos _hCprofile hr
    have hdist :=
      euclideanSobolevTwoUnitInnerRadialCollar_dist_one_le_width
        hwidth_pos hr
    have hΨ_bound :
        ‖Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1‖ ≤ LΦ * width :=
      (hΨ ((r : Set.Ioi (0 : ℝ)) : ℝ)).trans
        (mul_le_mul_of_nonneg_left hdist _hLΦ_nonneg)
    calc
      ‖euclideanSobolevTwoUnitInnerRadialProfileDeriv
            width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
          a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)‖
          =
            (‖euclideanSobolevTwoUnitInnerRadialProfileDeriv
                width ((r : Set.Ioi (0 : ℝ)) : ℝ)‖ * ‖a‖) *
              ‖Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1‖ := by
              rw [norm_mul, norm_mul]
      _ ≤ (Cprofile * (4 / width) * ‖a‖) * (LΦ * width) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hprofile (norm_nonneg a))
          hΨ_bound
          (norm_nonneg _)
          (mul_nonneg hscale_nonneg (norm_nonneg a))
  have houter_pointwise :
      ∀ r ∈ euclideanSobolevTwoUnitOuterRadialCollar width,
        ‖euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)‖ ≤
          (Cprofile * (4 / width) * ‖a‖) * (LΦ * width) := by
    intro r hr
    have hprofile :=
      euclideanSobolevTwoUnitOuterRadialProfileDeriv_norm_le
        hwidth_pos _hCprofile hr
    have hdist :=
      euclideanSobolevTwoUnitOuterRadialCollar_dist_one_le_width
        hwidth_pos hr
    have hΨ_bound :
        ‖Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1‖ ≤ LΦ * width :=
      (hΨ ((r : Set.Ioi (0 : ℝ)) : ℝ)).trans
        (mul_le_mul_of_nonneg_left hdist _hLΦ_nonneg)
    calc
      ‖euclideanSobolevTwoUnitOuterRadialProfileDeriv
            width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
          a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)‖
          =
            (‖euclideanSobolevTwoUnitOuterRadialProfileDeriv
                width ((r : Set.Ioi (0 : ℝ)) : ℝ)‖ * ‖a‖) *
              ‖Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1‖ := by
              rw [norm_mul, norm_mul]
      _ ≤ (Cprofile * (4 / width) * ‖a‖) * (LΦ * width) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hprofile (norm_nonneg a))
          hΨ_bound
          (norm_nonneg _)
          (mul_nonneg hscale_nonneg (norm_nonneg a))
  have hinner_measure :
      (MeasureTheory.Measure.volumeIoiPow n).real
          (euclideanSobolevTwoUnitInnerRadialCollar width) ≤
        ((2 : ℝ) ^ n) * width :=
    euclideanSobolevTwoUnitInnerRadialCollar_volumeIoiPow_real_le_width
      n hwidth_pos
  have houter_measure :
      (MeasureTheory.Measure.volumeIoiPow n).real
          (euclideanSobolevTwoUnitOuterRadialCollar width) ≤
        ((2 : ℝ) ^ n) * width :=
    euclideanSobolevTwoUnitOuterRadialCollar_volumeIoiPow_real_le_width
      n hwidth_pos hwidth_le_quarter
  have hinner_int :
      ‖∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
          euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)
          ∂(MeasureTheory.Measure.volumeIoiPow n)‖ ≤
        (4 * Cprofile * LΦ * ((2 : ℝ) ^ n)) * ‖a‖ * width := by
    have hnorm :=
      norm_setIntegral_le_of_norm_le_const
        (μ := MeasureTheory.Measure.volumeIoiPow n)
        (s := euclideanSobolevTwoUnitInnerRadialCollar width)
        (f := fun r : Set.Ioi (0 : ℝ) ↦
          euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1))
        (euclideanSobolevTwoUnitInnerRadialCollar_measure_lt_top n)
        hinner_pointwise
    calc
      ‖∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
          euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)
          ∂(MeasureTheory.Measure.volumeIoiPow n)‖
          ≤ (Cprofile * (4 / width) * ‖a‖) * (LΦ * width) *
            (MeasureTheory.Measure.volumeIoiPow n).real
              (euclideanSobolevTwoUnitInnerRadialCollar width) := hnorm
      _ ≤ (Cprofile * (4 / width) * ‖a‖) * (LΦ * width) *
            (((2 : ℝ) ^ n) * width) := by
            exact mul_le_mul_of_nonneg_left hinner_measure hvar_bound_nonneg
      _ = (4 * Cprofile * LΦ * ((2 : ℝ) ^ n)) * ‖a‖ * width := by
            field_simp [hwidth_pos.ne']
  have houter_int :
      ‖∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
          euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)
          ∂(MeasureTheory.Measure.volumeIoiPow n)‖ ≤
        (4 * Cprofile * LΦ * ((2 : ℝ) ^ n)) * ‖a‖ * width := by
    have hnorm :=
      norm_setIntegral_le_of_norm_le_const
        (μ := MeasureTheory.Measure.volumeIoiPow n)
        (s := euclideanSobolevTwoUnitOuterRadialCollar width)
        (f := fun r : Set.Ioi (0 : ℝ) ↦
          euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1))
        (euclideanSobolevTwoUnitOuterRadialCollar_measure_lt_top
          n hwidth_le_quarter)
        houter_pointwise
    calc
      ‖∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
          euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
            a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)
          ∂(MeasureTheory.Measure.volumeIoiPow n)‖
          ≤ (Cprofile * (4 / width) * ‖a‖) * (LΦ * width) *
            (MeasureTheory.Measure.volumeIoiPow n).real
              (euclideanSobolevTwoUnitOuterRadialCollar width) := hnorm
      _ ≤ (Cprofile * (4 / width) * ‖a‖) * (LΦ * width) *
            (((2 : ℝ) ^ n) * width) := by
            exact mul_le_mul_of_nonneg_left houter_measure hvar_bound_nonneg
      _ = (4 * Cprofile * LΦ * ((2 : ℝ) ^ n)) * ‖a‖ * width := by
            field_simp [hwidth_pos.ne']
  dsimp [euclideanSobolevTwoUnitScalarRadialVariationPairing]
  calc
    ‖(∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
        euclideanSobolevTwoUnitInnerRadialProfileDeriv
            width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
          a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)
        ∂(MeasureTheory.Measure.volumeIoiPow n)) +
      ∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
        euclideanSobolevTwoUnitOuterRadialProfileDeriv
            width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
          a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)
        ∂(MeasureTheory.Measure.volumeIoiPow n)‖
        ≤ ‖∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
            euclideanSobolevTwoUnitInnerRadialProfileDeriv
                width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
              a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)
            ∂(MeasureTheory.Measure.volumeIoiPow n)‖ +
          ‖∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
            euclideanSobolevTwoUnitOuterRadialProfileDeriv
                width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
              a * (Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ) - Ψ 1)
            ∂(MeasureTheory.Measure.volumeIoiPow n)‖ := norm_add_le _ _
    _ ≤ (4 * Cprofile * LΦ * ((2 : ℝ) ^ n)) * ‖a‖ * width +
          (4 * Cprofile * LΦ * ((2 : ℝ) ^ n)) * ‖a‖ * width :=
        add_le_add hinner_int houter_int
    _ = (8 * Cprofile * LΦ * ((2 : ℝ) ^ n)) * ‖a‖ * width := by
        ring

/--
%%handwave
name:
  Frozen scalar radial pairing is linear in the coefficient
statement:
  The frozen two-collar scalar pairing with coefficient \(c\) is \(c\) times
  the same pairing with coefficient \(1\).
proof:
  Pull the constant coefficient through each Bochner integral and factor it
  out of the sum.
-/
private theorem euclideanSobolevTwoUnitScalarRadialFrozenPairing_eq_unit_mul
    (n : ℕ) (width c : ℝ) :
    euclideanSobolevTwoUnitScalarRadialFrozenPairing n width c =
      euclideanSobolevTwoUnitScalarRadialFrozenPairing n width 1 * c := by
  simp [euclideanSobolevTwoUnitScalarRadialFrozenPairing,
    integral_mul_const, add_mul]

private theorem setIntegral_volumeIoiPow_Ioo_eq_interval
    (n : ℕ) {a b : ℝ} (ha_pos : 0 < a) (hab : a ≤ b)
    (F : ℝ → ℝ) :
    (∫ r in {r : Set.Ioi (0 : ℝ) | a < (r : ℝ) ∧ (r : ℝ) < b},
        F (r : ℝ) ∂MeasureTheory.Measure.volumeIoiPow n) =
      ∫ x in a..b, F x * x ^ n := by
  let s : Set (Set.Ioi (0 : ℝ)) :=
    {r : Set.Ioi (0 : ℝ) | a < (r : ℝ) ∧ (r : ℝ) < b}
  let μ0 : Measure (Set.Ioi (0 : ℝ)) :=
    Measure.comap Subtype.val (MeasureTheory.volume : Measure ℝ)
  have hs : MeasurableSet s := by
    dsimp [s]
    exact
      (isOpen_lt continuous_const continuous_subtype_val).measurableSet.inter
        (isOpen_lt continuous_subtype_val continuous_const).measurableSet
  have hρ_meas :
      Measurable
        (fun r : Set.Ioi (0 : ℝ) ↦
          ENNReal.ofReal (((r : Set.Ioi (0 : ℝ)) : ℝ) ^ n)) :=
    (measurable_subtype_coe.pow_const n).ennreal_ofReal
  have hρ_top :
      ∀ᵐ r ∂μ0.restrict s,
        ENNReal.ofReal (((r : Set.Ioi (0 : ℝ)) : ℝ) ^ n) <
          (∞ : ℝ≥0∞) :=
    Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hwithDensity :
      (∫ r in s, F ((r : Set.Ioi (0 : ℝ)) : ℝ)
          ∂MeasureTheory.Measure.volumeIoiPow n) =
        ∫ r in s,
          (((r : Set.Ioi (0 : ℝ)) : ℝ) ^ n) *
            F ((r : Set.Ioi (0 : ℝ)) : ℝ) ∂μ0 := by
    rw [MeasureTheory.Measure.volumeIoiPow]
    have h :=
      setIntegral_withDensity_eq_setIntegral_toReal_smul
        (μ := μ0)
        (f := fun r : Set.Ioi (0 : ℝ) ↦
          ENNReal.ofReal (((r : Set.Ioi (0 : ℝ)) : ℝ) ^ n))
        hρ_meas hρ_top
        (fun r : Set.Ioi (0 : ℝ) ↦
          F ((r : Set.Ioi (0 : ℝ)) : ℝ)) hs
    rw [h]
    refine setIntegral_congr_fun hs ?_
    intro r _hr
    have hpow_nonneg : 0 ≤ (((r : Set.Ioi (0 : ℝ)) : ℝ) ^ n) :=
      pow_nonneg (le_of_lt r.2) n
    simp [ENNReal.toReal_ofReal hpow_nonneg, smul_eq_mul, mul_comm]
  have hmap :
      Measure.map Subtype.val μ0 =
        (MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)) := by
    simpa [μ0] using
      map_comap_subtype_coe measurableSet_Ioi
        (MeasureTheory.volume : Measure ℝ)
  have hpre :
      ((Subtype.val : Set.Ioi (0 : ℝ) → ℝ) ⁻¹' Set.Ioo a b) = s := by
    rfl
  have hsubset : Set.Ioo a b ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact ha_pos.trans hx.1
  have hmapInt :
      (∫ r in s,
          (((r : Set.Ioi (0 : ℝ)) : ℝ) ^ n) *
            F ((r : Set.Ioi (0 : ℝ)) : ℝ) ∂μ0) =
        ∫ x in Set.Ioo a b, x ^ n * F x := by
    have hraw :=
      (MeasurableEmbedding.subtype_coe measurableSet_Ioi).setIntegral_map
        (μ := μ0)
        (g := fun x : ℝ ↦ x ^ n * F x)
        (s := Set.Ioo a b)
    rw [hmap, hpre] at hraw
    rw [← hraw]
    change
      ∫ x, x ^ n * F x
          ∂(((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))).restrict
            (Set.Ioo a b)) =
        ∫ x, x ^ n * F x
          ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo a b))
    rw [Measure.restrict_restrict_of_subset hsubset]
  calc
    (∫ r in {r : Set.Ioi (0 : ℝ) | a < (r : ℝ) ∧ (r : ℝ) < b},
        F (r : ℝ) ∂MeasureTheory.Measure.volumeIoiPow n)
        = ∫ r in s, F ((r : Set.Ioi (0 : ℝ)) : ℝ)
            ∂MeasureTheory.Measure.volumeIoiPow n := rfl
    _ = ∫ r in s,
          (((r : Set.Ioi (0 : ℝ)) : ℝ) ^ n) *
            F ((r : Set.Ioi (0 : ℝ)) : ℝ) ∂μ0 := hwithDensity
    _ = ∫ x in Set.Ioo a b, x ^ n * F x := hmapInt
    _ = ∫ x in a..b, F x * x ^ n := by
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hab]
      refine intervalIntegral.integral_congr ?_
      intro x _hx
      ring

/--
%%handwave
name:
  Frozen two-collar pairing after the radial transition change of variables
statement:
  For sufficiently small positive collar width, the unit-coefficient frozen
  pairing equals the integral over the transition parameter of the derivative
  of the transition profile times the difference between the outer and inner
  radial densities.
proof:
  Write the polar radial measure as \(r^n\,dr\).  In the inner collar use
  \(r=1-\delta/2-\delta t/4\), and in the outer collar use
  \(r=1+\delta/2+\delta t/4\).  The two profile derivatives exactly cancel
  the Jacobians, with opposite orientation on the inner collar.
-/
private theorem euclideanSobolevTwoUnitScalarRadialFrozenPairing_unit_eq_transition_density_difference
    (n : ℕ) {width : ℝ} (_hwidth_pos : 0 < width)
    (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) :
    euclideanSobolevTwoUnitScalarRadialFrozenPairing n width 1 =
      ∫ t in Set.Icc (-(2 : ℝ)) 2,
        deriv Real.smoothTransition t *
          (((1 : ℝ) + width / 2 + width * t / 4) ^ n -
            ((1 : ℝ) - width / 2 - width * t / 4) ^ n) := by
  have hwidth_lt_one : width < 1 := by
    linarith
  have hinner_lower_pos : 0 < (1 : ℝ) - width := by
    linarith
  have hinner_le : (1 : ℝ) - width ≤ 1 := by
    linarith
  have houter_le : (1 : ℝ) ≤ 1 + width := by
    linarith
  have hc_pos : 0 < width / 4 := by
    linarith
  have hc_ne : width / 4 ≠ 0 := ne_of_gt hc_pos
  let Ginner : ℝ → ℝ := fun r ↦
    euclideanSobolevTwoUnitInnerRadialProfileDeriv width r * r ^ n
  let Gouter : ℝ → ℝ := fun r ↦
    euclideanSobolevTwoUnitOuterRadialProfileDeriv width r * r ^ n
  let Iinner : ℝ → ℝ := fun t ↦
    deriv Real.smoothTransition t *
      ((1 : ℝ) - width / 2 - width * t / 4) ^ n
  let Iouter : ℝ → ℝ := fun t ↦
    deriv Real.smoothTransition t *
      ((1 : ℝ) + width / 2 + width * t / 4) ^ n
  have hinner_weighted :
      (∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
          euclideanSobolevTwoUnitInnerRadialProfileDeriv
            width ((r : Set.Ioi (0 : ℝ)) : ℝ) * 1
          ∂MeasureTheory.Measure.volumeIoiPow n) =
        ∫ r in ((1 : ℝ) - width)..1, Ginner r := by
    have h :=
      setIntegral_volumeIoiPow_Ioo_eq_interval
        n hinner_lower_pos hinner_le
        (fun r : ℝ ↦
          euclideanSobolevTwoUnitInnerRadialProfileDeriv width r * 1)
    simpa [euclideanSobolevTwoUnitInnerRadialCollar, Ginner,
      mul_assoc] using h
  have houter_weighted :
      (∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
          euclideanSobolevTwoUnitOuterRadialProfileDeriv
            width ((r : Set.Ioi (0 : ℝ)) : ℝ) * 1
          ∂MeasureTheory.Measure.volumeIoiPow n) =
        ∫ r in (1 : ℝ)..(1 + width), Gouter r := by
    have h :=
      setIntegral_volumeIoiPow_Ioo_eq_interval
        n (by norm_num : (0 : ℝ) < 1) houter_le
        (fun r : ℝ ↦
          euclideanSobolevTwoUnitOuterRadialProfileDeriv width r * 1)
    simpa [euclideanSobolevTwoUnitOuterRadialCollar, Gouter,
      mul_assoc] using h
  have hinner_subst :
      (∫ r in ((1 : ℝ) - width)..1, Ginner r) =
        ∫ t in (-(2 : ℝ))..2, - Iinner t := by
    have hraw :=
      intervalIntegral.smul_integral_comp_sub_mul
        (f := Ginner) (a := (-(2 : ℝ))) (b := (2 : ℝ))
        (c := width / 4) (d := (1 : ℝ) - width / 2)
    calc
      (∫ r in ((1 : ℝ) - width)..1, Ginner r)
          = (width / 4) *
              ∫ t in (-(2 : ℝ))..2,
                Ginner (((1 : ℝ) - width / 2) - (width / 4) * t) := by
            convert hraw.symm using 1 <;> ring
      _ = ∫ t in (-(2 : ℝ))..2, - Iinner t := by
            rw [← intervalIntegral.integral_const_mul]
            refine intervalIntegral.integral_congr ?_
            intro t _ht
            have harg :
                (((1 : ℝ) - width / 2 -
                    (((1 : ℝ) - width / 2) - (width / 4) * t)) /
                  (width / 4)) = t := by
              field_simp [hc_ne]
              ring
            have hr :
                ((1 : ℝ) - width / 2) - (width / 4) * t =
                  (1 : ℝ) - width / 2 - width * t / 4 := by
              ring
            dsimp [Ginner, Iinner,
              euclideanSobolevTwoUnitInnerRadialProfileDeriv]
            rw [harg, hr]
            field_simp [hc_ne]
  have houter_subst :
      (∫ r in (1 : ℝ)..(1 + width), Gouter r) =
        ∫ t in (-(2 : ℝ))..2, Iouter t := by
    have hraw :=
      intervalIntegral.smul_integral_comp_add_mul
        (f := Gouter) (a := (-(2 : ℝ))) (b := (2 : ℝ))
        (c := width / 4) (d := (1 : ℝ) + width / 2)
    calc
      (∫ r in (1 : ℝ)..(1 + width), Gouter r)
          = (width / 4) *
              ∫ t in (-(2 : ℝ))..2,
                Gouter (((1 : ℝ) + width / 2) + (width / 4) * t) := by
            convert hraw.symm using 1 <;> ring
      _ = ∫ t in (-(2 : ℝ))..2, Iouter t := by
            rw [← intervalIntegral.integral_const_mul]
            refine intervalIntegral.integral_congr ?_
            intro t _ht
            have harg :
                ((((1 : ℝ) + width / 2 + (width / 4) * t) -
                    ((1 : ℝ) + width / 2)) /
                  (width / 4)) = t := by
              field_simp [hc_ne]
              ring
            have hr :
                ((1 : ℝ) + width / 2) + (width / 4) * t =
                  (1 : ℝ) + width / 2 + width * t / 4 := by
              ring
            dsimp [Gouter, Iouter,
              euclideanSobolevTwoUnitOuterRadialProfileDeriv]
            rw [harg, hr]
            field_simp [hc_ne]
  have hderiv_cont :
      Continuous (fun t : ℝ ↦ deriv Real.smoothTransition t) := by
    have hsmooth : ContDiff ℝ ∞ Real.smoothTransition :=
      Real.smoothTransition.contDiff
    exact hsmooth.continuous_deriv (by simp)
  have hinner_intervalIntegrable :
      IntervalIntegrable Iinner MeasureTheory.volume (-(2 : ℝ)) 2 := by
    dsimp [Iinner]
    exact (hderiv_cont.mul (by fun_prop)).intervalIntegrable _ _
  have houter_intervalIntegrable :
      IntervalIntegrable Iouter MeasureTheory.volume (-(2 : ℝ)) 2 := by
    dsimp [Iouter]
    exact (hderiv_cont.mul (by fun_prop)).intervalIntegrable _ _
  have hsum_interval :
      (∫ t in (-(2 : ℝ))..2, - Iinner t) +
          ∫ t in (-(2 : ℝ))..2, Iouter t =
        ∫ t in (-(2 : ℝ))..2,
          deriv Real.smoothTransition t *
            (((1 : ℝ) + width / 2 + width * t / 4) ^ n -
              ((1 : ℝ) - width / 2 - width * t / 4) ^ n) := by
    change
      (∫ t in (-(2 : ℝ))..2, (-Iinner) t) +
          ∫ t in (-(2 : ℝ))..2, Iouter t =
        ∫ t in (-(2 : ℝ))..2,
          deriv Real.smoothTransition t *
            (((1 : ℝ) + width / 2 + width * t / 4) ^ n -
              ((1 : ℝ) - width / 2 - width * t / 4) ^ n)
    rw [← intervalIntegral.integral_add
      hinner_intervalIntegrable.neg houter_intervalIntegrable]
    refine intervalIntegral.integral_congr ?_
    intro t _ht
    dsimp [Iinner, Iouter]
    ring
  have hset_eq_interval :
      (∫ t in Set.Icc (-(2 : ℝ)) 2,
        deriv Real.smoothTransition t *
          (((1 : ℝ) + width / 2 + width * t / 4) ^ n -
            ((1 : ℝ) - width / 2 - width * t / 4) ^ n)) =
        ∫ t in (-(2 : ℝ))..2,
        deriv Real.smoothTransition t *
          (((1 : ℝ) + width / 2 + width * t / 4) ^ n -
            ((1 : ℝ) - width / 2 - width * t / 4) ^ n) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-(2 : ℝ)) ≤ 2),
      ← integral_Icc_eq_integral_Ioc]
  dsimp [euclideanSobolevTwoUnitScalarRadialFrozenPairing]
  rw [hinner_weighted, houter_weighted, hinner_subst, houter_subst]
  rw [hset_eq_interval]
  exact hsum_interval

private theorem euclideanSobolevTwoUnitTransitionDensityDifference_abs_le
    (n : ℕ) {width t : ℝ} (hwidth_nonneg : 0 ≤ width)
    (hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
    (ht : t ∈ Set.Icc (-(2 : ℝ)) 2) :
    |((1 : ℝ) + width / 2 + width * t / 4) ^ n -
        ((1 : ℝ) - width / 2 - width * t / 4) ^ n| ≤
      (2 * width) * (n : ℝ) * (2 : ℝ) ^ (n - 1) := by
  let rout : ℝ := (1 : ℝ) + width / 2 + width * t / 4
  let rin : ℝ := (1 : ℝ) - width / 2 - width * t / 4
  have hwt_le : width * t / 4 ≤ width / 2 := by
    have hmul : width * t ≤ width * (2 : ℝ) :=
      mul_le_mul_of_nonneg_left ht.2 hwidth_nonneg
    linarith
  have hwt_ge : -(width / 2) ≤ width * t / 4 := by
    have hmul : width * (-(2 : ℝ)) ≤ width * t :=
      mul_le_mul_of_nonneg_left ht.1 hwidth_nonneg
    linarith
  have hrout_abs_le_two : |rout| ≤ (2 : ℝ) := by
    rw [abs_le]
    constructor <;> dsimp [rout] <;> linarith [hwt_le, hwt_ge, hwidth_le_quarter]
  have hrin_abs_le_two : |rin| ≤ (2 : ℝ) := by
    rw [abs_le]
    constructor <;> dsimp [rin] <;> linarith [hwt_le, hwt_ge, hwidth_le_quarter]
  have hmax_nonneg : 0 ≤ max |rout| |rin| :=
    (abs_nonneg rout).trans (le_max_left |rout| |rin|)
  have hmax_le_two : max |rout| |rin| ≤ (2 : ℝ) :=
    max_le hrout_abs_le_two hrin_abs_le_two
  have hpow_le :
      max |rout| |rin| ^ (n - 1) ≤ (2 : ℝ) ^ (n - 1) :=
    pow_le_pow_left₀ hmax_nonneg hmax_le_two (n - 1)
  have hfactor_abs : |1 + t / 2| ≤ (2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hdiff_abs : |rout - rin| ≤ 2 * width := by
    calc
      |rout - rin| = |width * (1 + t / 2)| := by
          congr 1
          dsimp [rout, rin]
          ring
      _ = width * |1 + t / 2| := by
          rw [abs_mul, abs_of_nonneg hwidth_nonneg]
      _ ≤ width * 2 := mul_le_mul_of_nonneg_left hfactor_abs hwidth_nonneg
      _ = 2 * width := by ring
  have hpow_sub :=
    abs_pow_sub_pow_le (a := rout) (b := rin) (n := n)
  calc
    |((1 : ℝ) + width / 2 + width * t / 4) ^ n -
        ((1 : ℝ) - width / 2 - width * t / 4) ^ n|
        = |rout ^ n - rin ^ n| := by rfl
    _ ≤ |rout - rin| * (n : ℝ) * max |rout| |rin| ^ (n - 1) :=
        hpow_sub
    _ ≤ (2 * width) * (n : ℝ) * (2 : ℝ) ^ (n - 1) := by
        gcongr

/--
%%handwave
name:
  Unit-coefficient frozen radial cancellation is linear in the collar width
statement:
  The frozen two-collar radial pairing with coefficient \(1\) is bounded by
  \(B\delta\).
proof:
  Change variables in the two radial integrals to the common transition
  parameter.  The two oriented profile derivatives have opposite total mass,
  so the constant-density contributions cancel.  The remaining contribution is
  controlled by the variation of \(r^n\) across the two width-\(\delta\)
  collars.
-/
private theorem euclideanSobolevTwoUnitScalarRadialFrozenPairing_unit_norm_le_width
    (n : ℕ) (Cprofile : ℝ)
    (_hCprofile_ge_one : 1 ≤ Cprofile)
    (_hCprofile : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ Cprofile) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
          ‖euclideanSobolevTwoUnitScalarRadialFrozenPairing n width 1‖ ≤
            B * width := by
  refine ⟨8 * Cprofile * (n : ℝ) * (2 : ℝ) ^ (n - 1), ?_, ?_⟩
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (le_trans zero_le_one _hCprofile_ge_one))
        (Nat.cast_nonneg n))
      (pow_nonneg (by norm_num) (n - 1))
  intro width hwidth_pos hwidth_le_quarter
  have hwidth_nonneg : 0 ≤ width := hwidth_pos.le
  have hCprofile_nonneg : 0 ≤ Cprofile :=
    le_trans zero_le_one _hCprofile_ge_one
  rw [euclideanSobolevTwoUnitScalarRadialFrozenPairing_unit_eq_transition_density_difference
    n hwidth_pos hwidth_le_quarter]
  let M : ℝ :=
    Cprofile * ((2 * width) * (n : ℝ) * (2 : ℝ) ^ (n - 1))
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg hCprofile_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hwidth_nonneg)
          (Nat.cast_nonneg n))
        (pow_nonneg (by norm_num) (n - 1)))
  have hpointwise :
      ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
        ‖deriv Real.smoothTransition t *
          (((1 : ℝ) + width / 2 + width * t / 4) ^ n -
            ((1 : ℝ) - width / 2 - width * t / 4) ^ n)‖ ≤ M := by
    intro t ht
    have hdensity :=
      euclideanSobolevTwoUnitTransitionDensityDifference_abs_le
        n hwidth_nonneg hwidth_le_quarter ht
    calc
      ‖deriv Real.smoothTransition t *
          (((1 : ℝ) + width / 2 + width * t / 4) ^ n -
            ((1 : ℝ) - width / 2 - width * t / 4) ^ n)‖
          =
            ‖deriv Real.smoothTransition t‖ *
              |((1 : ℝ) + width / 2 + width * t / 4) ^ n -
                ((1 : ℝ) - width / 2 - width * t / 4) ^ n| := by
            rw [norm_mul]
            simp [Real.norm_eq_abs]
      _ ≤ Cprofile *
            ((2 * width) * (n : ℝ) * (2 : ℝ) ^ (n - 1)) :=
          mul_le_mul (_hCprofile t ht) hdensity (abs_nonneg _)
            hCprofile_nonneg
      _ = M := rfl
  have hnorm :=
    norm_setIntegral_le_of_norm_le_const
      (μ := MeasureTheory.volume)
      (s := Set.Icc (-(2 : ℝ)) 2)
      (f := fun t : ℝ ↦
        deriv Real.smoothTransition t *
          (((1 : ℝ) + width / 2 + width * t / 4) ^ n -
            ((1 : ℝ) - width / 2 - width * t / 4) ^ n))
      isCompact_Icc.measure_lt_top
      hpointwise
  calc
    ‖∫ t in Set.Icc (-(2 : ℝ)) 2,
        deriv Real.smoothTransition t *
          (((1 : ℝ) + width / 2 + width * t / 4) ^ n -
            ((1 : ℝ) - width / 2 - width * t / 4) ^ n)‖
        ≤ M * (MeasureTheory.volume : Measure ℝ).real
            (Set.Icc (-(2 : ℝ)) 2) := hnorm
    _ = M * 4 := by
        rw [Real.volume_real_Icc_of_le]
        · norm_num
        · norm_num
    _ = (8 * Cprofile * (n : ℝ) * (2 : ℝ) ^ (n - 1)) * width := by
        dsimp [M]
        ring

/--
%%handwave
name:
  The frozen scalar radial part is linear in the collar width
statement:
  The frozen two-collar radial pairing with constant coefficient \(c\) is
  bounded by \(B|c|\delta\).
proof:
  The constant-density frozen terms cancel because the two oriented profile
  derivatives have opposite total mass.  The only remaining contribution comes
  from the variation of the radial density \(r^n\), which is \(O(\delta)\) on
  the two collars.
-/
private theorem euclideanSobolevTwoUnitScalarRadialFrozenPairing_norm_le_width
    (n : ℕ) (Cprofile : ℝ)
    (_hCprofile_ge_one : 1 ≤ Cprofile)
    (_hCprofile : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ Cprofile) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
          (c : ℝ),
          ‖euclideanSobolevTwoUnitScalarRadialFrozenPairing n width c‖ ≤
            B * ‖c‖ * width := by
  obtain ⟨B, hB_nonneg, hunit⟩ :=
    euclideanSobolevTwoUnitScalarRadialFrozenPairing_unit_norm_le_width
      n Cprofile _hCprofile_ge_one _hCprofile
  refine ⟨B, hB_nonneg, ?_⟩
  intro width hwidth_pos hwidth_le_quarter c
  rw [euclideanSobolevTwoUnitScalarRadialFrozenPairing_eq_unit_mul]
  calc
    ‖euclideanSobolevTwoUnitScalarRadialFrozenPairing n width 1 * c‖
        = ‖euclideanSobolevTwoUnitScalarRadialFrozenPairing n width 1‖ *
            ‖c‖ := norm_mul _ _
    _ ≤ (B * width) * ‖c‖ :=
        mul_le_mul_of_nonneg_right
          (hunit hwidth_pos hwidth_le_quarter) (norm_nonneg c)
    _ = B * ‖c‖ * width := by ring

/--
%%handwave
name:
  Scalar radial cancellation for the two unit collars
statement:
  Uniform bounds for the transition-profile derivative and for the radial
  variation of a scalar weight give constants \(A,B\) such that, for every
  scalar boundary coefficient \(a\) and every radial weight \(\Psi\), the two
  one-dimensional collar integrals are bounded by
  \((A|a|+B|a\Psi(1)|)\delta\).
proof:
  Decompose \(a\Psi(r)=a\Psi(1)+a(\Psi(r)-\Psi(1))\).  The two oriented
  transition derivatives have opposite unit mass, so the constant-density
  frozen part cancels.  The remaining frozen contribution is controlled by
  \(|r^n-1|\le C\delta\) on the two collars, and the non-frozen contribution is
  controlled by \(|\Psi(r)-\Psi(1)|\le L|r-1|\).
-/
private theorem euclideanSobolev_two_unit_collar_scalar_radial_profile_cancellation_norm_le_width
    (n : ℕ) (Cprofile LΦ : ℝ)
    (_hCprofile_ge_one : 1 ≤ Cprofile)
    (_hCprofile : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ Cprofile)
    (_hLΦ_nonneg : 0 ≤ LΦ) :
    ∃ A B : ℝ,
      0 ≤ A ∧ 0 ≤ B ∧
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
          (a : ℝ) (Ψ : ℝ → ℝ),
          Measurable Ψ →
          (∀ r : ℝ, ‖Ψ r - Ψ 1‖ ≤ LΦ * ‖r - 1‖) →
          ‖(∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
              (euclideanSobolevTwoUnitInnerRadialProfileDeriv
                  width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
                a * Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ))
              ∂(MeasureTheory.Measure.volumeIoiPow n)) +
            ∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
              (euclideanSobolevTwoUnitOuterRadialProfileDeriv
                  width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
                a * Ψ ((r : Set.Ioi (0 : ℝ)) : ℝ))
              ∂(MeasureTheory.Measure.volumeIoiPow n)‖ ≤
            (A * ‖a‖ + B * ‖a * Ψ 1‖) * width := by
  obtain ⟨A, hA_nonneg, hvariation⟩ :=
    euclideanSobolevTwoUnitScalarRadialVariationPairing_norm_le_width
      n Cprofile LΦ _hCprofile_ge_one _hCprofile _hLΦ_nonneg
  obtain ⟨B, hB_nonneg, hfrozen⟩ :=
    euclideanSobolevTwoUnitScalarRadialFrozenPairing_norm_le_width
      n Cprofile _hCprofile_ge_one _hCprofile
  refine ⟨A, B, hA_nonneg, hB_nonneg, ?_⟩
  intro width hwidth_pos hwidth_le_quarter a Ψ hΨ_meas hΨ
  change
    ‖euclideanSobolevTwoUnitScalarRadialPairing n width a Ψ‖ ≤
      (A * ‖a‖ + B * ‖a * Ψ 1‖) * width
  rw [euclideanSobolevTwoUnitScalarRadialPairing_eq_variation_add_frozen
    n hwidth_pos hwidth_le_quarter a Ψ hΨ_meas
    ⟨LΦ, _hLΦ_nonneg, hΨ⟩]
  have hvar :
      ‖euclideanSobolevTwoUnitScalarRadialVariationPairing n width a Ψ‖ ≤
        A * ‖a‖ * width :=
    hvariation hwidth_pos hwidth_le_quarter a Ψ hΨ_meas hΨ
  have hfro :
      ‖euclideanSobolevTwoUnitScalarRadialFrozenPairing n width (a * Ψ 1)‖ ≤
        B * ‖a * Ψ 1‖ * width :=
    hfrozen hwidth_pos hwidth_le_quarter (a * Ψ 1)
  calc
    ‖euclideanSobolevTwoUnitScalarRadialVariationPairing n width a Ψ +
        euclideanSobolevTwoUnitScalarRadialFrozenPairing n width (a * Ψ 1)‖
        ≤ ‖euclideanSobolevTwoUnitScalarRadialVariationPairing n width a Ψ‖ +
            ‖euclideanSobolevTwoUnitScalarRadialFrozenPairing n width (a * Ψ 1)‖ :=
          by exact norm_add_le _ _
    _ ≤ A * ‖a‖ * width + B * ‖a * Ψ 1‖ * width :=
          add_le_add hvar hfro
    _ = (A * ‖a‖ + B * ‖a * Ψ 1‖) * width := by ring

private noncomputable def euclideanSobolevTwoUnitAbstractRadialSum
    {S : Type} [MeasurableSpace S]
    (n : ℕ) (normal trace : S → ℝ) (Φ : S → ℝ → ℝ)
    (width : ℝ) (θ : S) : ℝ :=
  (∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
      (euclideanSobolevTwoUnitInnerRadialProfileDeriv
          width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
        normal θ * Φ θ ((r : Set.Ioi (0 : ℝ)) : ℝ)) *
        trace θ
      ∂(MeasureTheory.Measure.volumeIoiPow n)) +
    ∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
      (euclideanSobolevTwoUnitOuterRadialProfileDeriv
          width ((r : Set.Ioi (0 : ℝ)) : ℝ) *
        normal θ * Φ θ ((r : Set.Ioi (0 : ℝ)) : ℝ)) *
        trace θ
      ∂(MeasureTheory.Measure.volumeIoiPow n)

private noncomputable def euclideanSobolevTwoUnitAbstractProductSum
    {S : Type} [MeasurableSpace S]
    (μS : Measure S) (n : ℕ) (normal trace : S → ℝ)
    (Φ : S → ℝ → ℝ) (width : ℝ) : ℝ :=
  (∫ p in
      (Set.univ : Set S) ×ˢ
        euclideanSobolevTwoUnitInnerRadialCollar width,
      ((euclideanSobolevTwoUnitInnerRadialProfileDeriv
          width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
        normal p.1 *
        Φ p.1 ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
        trace p.1
      ∂(μS.prod (MeasureTheory.Measure.volumeIoiPow n))) +
    ∫ p in
      (Set.univ : Set S) ×ˢ
        euclideanSobolevTwoUnitOuterRadialCollar width,
      ((euclideanSobolevTwoUnitOuterRadialProfileDeriv
          width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
        normal p.1 *
        Φ p.1 ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
        trace p.1
      ∂(μS.prod (MeasureTheory.Measure.volumeIoiPow n))

/--
%%handwave
name:
  Pointwise radial bounds integrate over the sphere variable
statement:
  If each sphere direction satisfies the scalar radial collar estimate with
  bounds depending on two integrable boundary factors, then the corresponding
  product-measure collar integral is bounded by a constant times the collar
  width.
proof:
  Apply Fubini on the two product collars.  The pointwise radial estimate gives
  an \(L^1\)-majorant
  \(A|\mathrm{trace}\cdot\mathrm{normal}|+
  B|\mathrm{trace}\cdot\Phi(1)\cdot\mathrm{normal}|\), which is integrable by
  the hypotheses.  Integrating the majorant gives the required constant.
-/
private theorem euclideanSobolev_two_unit_collar_abstract_radial_cancellation_norm_le_width_of_pointwise_radial_bound
    {S : Type} [MeasurableSpace S]
    (μS : Measure S) (n : ℕ)
    (normal trace : S → ℝ) (Φ : S → ℝ → ℝ)
    (A B : ℝ) (_hA_nonneg : 0 ≤ A) (_hB_nonneg : 0 ≤ B)
    (_htrace_normal :
      Integrable (fun θ : S ↦ trace θ * normal θ) μS)
    (_htrace_frozen_weight :
      Integrable (fun θ : S ↦ trace θ * Φ θ 1 * normal θ) μS)
    (_hpointwise :
      ∀ {width : ℝ}
        (_hwidth_pos : 0 < width)
        (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
        (θ : S),
        ‖euclideanSobolevTwoUnitAbstractRadialSum
          n normal trace Φ width θ‖ ≤
          (A * ‖trace θ * normal θ‖ +
            B * ‖trace θ * Φ θ 1 * normal θ‖) * width)
    (_hproduct_to_radial :
      ∀ {width : ℝ}
        (_hwidth_pos : 0 < width)
        (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
        euclideanSobolevTwoUnitAbstractProductSum
          μS n normal trace Φ width =
          ∫ θ, euclideanSobolevTwoUnitAbstractRadialSum
            n normal trace Φ width θ ∂μS) :
    ∃ K : ℝ,
      0 ≤ K ∧
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
          ‖euclideanSobolevTwoUnitAbstractProductSum
            μS n normal trace Φ width‖ ≤ K * width := by
    let K : ℝ :=
      A * ∫ θ, ‖trace θ * normal θ‖ ∂μS +
        B * ∫ θ, ‖trace θ * Φ θ 1 * normal θ‖ ∂μS
    refine ⟨K, ?_, ?_⟩
    · dsimp [K]
      exact add_nonneg
        (mul_nonneg _hA_nonneg
          (integral_nonneg fun θ ↦ norm_nonneg (trace θ * normal θ)))
        (mul_nonneg _hB_nonneg
          (integral_nonneg fun θ ↦
            norm_nonneg (trace θ * Φ θ 1 * normal θ)))
    · intro width hwidth_pos hwidth_le_quarter
      let majorant : S → ℝ := fun θ ↦
        (A * ‖trace θ * normal θ‖ +
          B * ‖trace θ * Φ θ 1 * normal θ‖) * width
      have hmajorant_int : Integrable majorant μS := by
        dsimp [majorant]
        exact
          (((_htrace_normal.norm.const_mul A).add
            (_htrace_frozen_weight.norm.const_mul B)).mul_const width)
      have hbound :
          ∀ᵐ θ ∂μS,
            ‖euclideanSobolevTwoUnitAbstractRadialSum
              n normal trace Φ width θ‖ ≤ majorant θ :=
        Filter.Eventually.of_forall fun θ ↦
          _hpointwise hwidth_pos hwidth_le_quarter θ
      calc
        ‖euclideanSobolevTwoUnitAbstractProductSum
            μS n normal trace Φ width‖
            = ‖∫ θ, euclideanSobolevTwoUnitAbstractRadialSum
                n normal trace Φ width θ ∂μS‖ := by
              rw [_hproduct_to_radial hwidth_pos hwidth_le_quarter]
        _ ≤ ∫ θ, majorant θ ∂μS :=
              norm_integral_le_of_norm_le hmajorant_int hbound
        _ = K * width := by
                dsimp [majorant, K]
                rw [integral_mul_const]
                change
                  (∫ θ,
                    A * ‖trace θ * normal θ‖ +
                      B * ‖trace θ * Φ θ 1 * normal θ‖ ∂μS) *
                      width =
                    (A * ∫ θ, ‖trace θ * normal θ‖ ∂μS +
                      B * ∫ θ, ‖trace θ * Φ θ 1 * normal θ‖ ∂μS) *
                      width
                rw [integral_add
                  (_htrace_normal.norm.const_mul A)
                  (_htrace_frozen_weight.norm.const_mul B)]
                rw [integral_const_mul, integral_const_mul]

/--
%%handwave
name:
  Abstract radial cancellation for two unit collars
statement:
  Let a sphere variable carry an integrable trace-normal factor and an
  integrable frozen weighted factor.  If the radial weight varies Lipschitzly
  from radius one and the transition-profile derivative is uniformly bounded,
  then the two oriented radial collar integrals adjacent to radius one are
  bounded by a constant times the collar width.
proof:
  This is the one-dimensional cancellation argument.  In each direction,
  change both collar integrals to the transition variable.  The frozen radius
  one terms cancel because the two oriented profile derivatives have opposite
  total mass.  The remainder is bounded by the radial variation of the weight
  and by the variation of the density \(r^n\) on a fixed compact interval.
-/
private theorem euclideanSobolev_two_unit_collar_abstract_radial_cancellation_norm_le_width
    {S : Type} [MeasurableSpace S]
    (μS : Measure S) (n : ℕ)
    (normal trace : S → ℝ) (Φ : S → ℝ → ℝ)
    (Cprofile LΦ : ℝ)
    (_hCprofile_ge_one : 1 ≤ Cprofile)
    (_hCprofile : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ Cprofile)
    (_hLΦ_nonneg : 0 ≤ LΦ)
    (_hΦ_lipschitz :
      ∀ (θ : S) (r : ℝ), ‖Φ θ r - Φ θ 1‖ ≤ LΦ * ‖r - 1‖)
    (_hΦ_radial_measurable : ∀ θ : S, Measurable (Φ θ))
      (_htrace_normal :
        Integrable (fun θ : S ↦ trace θ * normal θ) μS)
      (_htrace_frozen_weight :
        Integrable (fun θ : S ↦ trace θ * Φ θ 1 * normal θ) μS)
      (_hproduct_to_radial :
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
          euclideanSobolevTwoUnitAbstractProductSum
            μS n normal trace Φ width =
            ∫ θ, euclideanSobolevTwoUnitAbstractRadialSum
              n normal trace Φ width θ ∂μS) :
    ∃ K : ℝ,
      0 ≤ K ∧
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
          ‖(∫ p in
              (Set.univ : Set S) ×ˢ
                {r : Set.Ioi (0 : ℝ) |
                  (1 : ℝ) - width < (r : ℝ) ∧ (r : ℝ) < 1},
              ((deriv Real.smoothTransition
                  (((1 : ℝ) - width / 2 -
                      ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) / (width / 4)) *
                (-(1 : ℝ) / (width / 4))) *
                normal p.1 *
                Φ p.1 ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
                trace p.1
              ∂(μS.prod
                (MeasureTheory.Measure.volumeIoiPow n)) +
            ∫ p in
              (Set.univ : Set S) ×ˢ
                {r : Set.Ioi (0 : ℝ) |
                  (1 : ℝ) < (r : ℝ) ∧ (r : ℝ) < 1 + width},
              ((deriv Real.smoothTransition
                  ((((p.2 : Set.Ioi (0 : ℝ)) : ℝ) -
                      ((1 : ℝ) + width / 2)) / (width / 4)) *
                ((1 : ℝ) / (width / 4))) *
                normal p.1 *
                Φ p.1 ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
                trace p.1
              ∂(μS.prod
                (MeasureTheory.Measure.volumeIoiPow n)))‖ ≤ K * width := by
  obtain ⟨A, B, hA_nonneg, hB_nonneg, hscalar⟩ :=
    euclideanSobolev_two_unit_collar_scalar_radial_profile_cancellation_norm_le_width
      n Cprofile LΦ _hCprofile_ge_one _hCprofile _hLΦ_nonneg
  have hpointwise :
      ∀ {width : ℝ}
        (_hwidth_pos : 0 < width)
        (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
        (θ : S),
        ‖euclideanSobolevTwoUnitAbstractRadialSum
          n normal trace Φ width θ‖ ≤
          (A * ‖trace θ * normal θ‖ +
            B * ‖trace θ * Φ θ 1 * normal θ‖) * width := by
    intro width hwidth_pos hwidth_le_quarter θ
    have hscalarθ :=
      hscalar hwidth_pos hwidth_le_quarter (trace θ * normal θ)
        (Φ θ) (_hΦ_radial_measurable θ) (_hΦ_lipschitz θ)
    simpa [euclideanSobolevTwoUnitAbstractRadialSum,
      mul_assoc, mul_left_comm, mul_comm] using hscalarθ
  obtain ⟨K, hK_nonneg, hK_bound⟩ :=
    euclideanSobolev_two_unit_collar_abstract_radial_cancellation_norm_le_width_of_pointwise_radial_bound
      μS n normal trace Φ A B hA_nonneg hB_nonneg
      _htrace_normal _htrace_frozen_weight hpointwise _hproduct_to_radial
  refine ⟨K, hK_nonneg, ?_⟩
  intro width hwidth_pos hwidth_le_quarter
  simpa [euclideanSobolevTwoUnitInnerRadialCollar,
    euclideanSobolevTwoUnitOuterRadialCollar,
    euclideanSobolevTwoUnitInnerRadialProfileDeriv,
    euclideanSobolevTwoUnitOuterRadialProfileDeriv,
    euclideanSobolevTwoUnitAbstractProductSum] using
    hK_bound hwidth_pos hwidth_le_quarter

/--
%%handwave
name:
  Inner smooth polar collar integrability
statement:
  The inner product-collar integrand formed from the transition profile, the
  normal factor, a smooth test function evaluated at \(r\theta\), and an
  integrable boundary trace-normal factor is integrable on the inner product
  collar.
proof:
  The radial profile is bounded on the collar and the smooth test function is
  globally bounded because it has compact support.  The integrand is therefore
  dominated by a fixed multiple of
  \(|\tau(\theta)\langle\theta,v\rangle|\), pulled back to the product collar.
  This pullback is integrable since the radial collar has finite measure.
-/
private theorem euclideanSobolev_two_unit_collar_exact_trace_pairing_simplified_polar_inner_integrableOn
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [Nontrivial H]
    {τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_inner :
      Integrable
        (fun θ : Metric.sphere (0 : H) 1 ↦
          τ (θ : H) * inner ℝ (θ : H) v)
        ((MeasureTheory.volume : Measure H).toSphere))
    {width : ℝ} (_hwidth_pos : 0 < width)
    (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) :
    IntegrableOn
      (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
        ((euclideanSobolevTwoUnitInnerRadialProfileDeriv
            width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
          inner ℝ (p.1 : H) v *
          (φ : H → ℝ) (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))) *
          τ (p.1 : H))
      ((Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
        euclideanSobolevTwoUnitInnerRadialCollar width)
      (((MeasureTheory.volume : Measure H).toSphere).prod
        (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1))) := by
  classical
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let R : Set (Set.Ioi (0 : ℝ)) :=
    euclideanSobolevTwoUnitInnerRadialCollar width
  let boundary : Metric.sphere (0 : H) 1 → ℝ :=
    fun θ ↦ τ (θ : H) * inner ℝ (θ : H) v
  let weight : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    fun p ↦
      euclideanSobolevTwoUnitInnerRadialProfileDeriv
          width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) *
        (φ : H → ℝ) (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))
  have hR_meas : MeasurableSet R := by
    simpa [R] using euclideanSobolevTwoUnitInnerRadialCollar_measurableSet width
  have hR_lt_top : μR R < (∞ : ℝ≥0∞) := by
    simpa [μR, R] using
      euclideanSobolevTwoUnitInnerRadialCollar_measure_lt_top
        (Module.finrank ℝ H - 1) (width := width)
  haveI : IsFiniteMeasure (μR.restrict R) :=
    isFiniteMeasure_restrict.2 (ne_of_lt hR_lt_top)
  have hboundary_int : Integrable boundary μS := by
    simpa [boundary, μS] using _hτ_inner
  have hboundary_prod :
      Integrable
        (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
          boundary p.1)
        (μS.prod (μR.restrict R)) :=
    hboundary_int.comp_fst (μR.restrict R)
  have hpoint_cont :
      Continuous
        (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
          ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) := by
    fun_prop
  have hφ_meas :
      Measurable
        (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
          (φ : H → ℝ) (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))) :=
    (φ.smooth.continuous.comp hpoint_cont).measurable
  have hprofile_meas :
      Measurable
        (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
          euclideanSobolevTwoUnitInnerRadialProfileDeriv
            width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) :=
    (euclideanSobolevTwoUnitInnerRadialProfileDeriv_measurable width).comp
      measurable_snd
  have hweight_aesm : AEStronglyMeasurable weight (μS.prod (μR.restrict R)) := by
    simpa [weight] using
      (hprofile_meas.mul hφ_meas).aestronglyMeasurable
  obtain ⟨Cprofile, hCprofile_ge_one, hCprofile⟩ :=
    exists_smoothTransition_deriv_bound_Icc_neg_two_two
  have hCprofile_nonneg : 0 ≤ Cprofile :=
    le_trans zero_le_one hCprofile_ge_one
  rcases
      φ.compact_support.exists_bound_of_continuousOn
        φ.smooth.continuous.continuousOn with
    ⟨B₀, hB₀⟩
  let B : ℝ := max B₀ 0
  have hB_nonneg : 0 ≤ B := le_max_right B₀ 0
  have hφ_bound : ∀ z : H, ‖(φ : H → ℝ) z‖ ≤ B := by
    intro z
    by_cases hz : z ∈ tsupport (φ : H → ℝ)
    · exact (hB₀ z hz).trans (le_max_left B₀ 0)
    · have hzero : (φ : H → ℝ) z = 0 :=
        image_eq_zero_of_notMem_tsupport hz
      simp [B, hzero, hB_nonneg]
  let C : ℝ := (Cprofile * (4 / width)) * B
  have hfactor_nonneg : 0 ≤ Cprofile * (4 / width) := by
    exact mul_nonneg hCprofile_nonneg
      (div_nonneg (by norm_num) _hwidth_pos.le)
  have hR_ae : ∀ᵐ r ∂μR.restrict R, r ∈ R :=
    ae_restrict_mem hR_meas
  have hpred_meas :
      MeasurableSet
        {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) | p.2 ∈ R} :=
    hR_meas.preimage measurable_snd
  have hprod_mem :
      ∀ᵐ p ∂μS.prod (μR.restrict R), p.2 ∈ R := by
    rw [Measure.ae_prod_iff_ae_ae hpred_meas]
    exact Filter.Eventually.of_forall fun _θ ↦ hR_ae
  have hweight_bound :
      ∀ᵐ p ∂μS.prod (μR.restrict R), ‖weight p‖ ≤ C := by
    filter_upwards [hprod_mem] with p hpR
    have hprofile :
        ‖euclideanSobolevTwoUnitInnerRadialProfileDeriv
            width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)‖ ≤
          Cprofile * (4 / width) :=
      euclideanSobolevTwoUnitInnerRadialProfileDeriv_norm_le
        _hwidth_pos hCprofile hpR
    have hφ :
        ‖(φ : H → ℝ) (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))‖ ≤ B :=
      hφ_bound (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))
    calc
      ‖weight p‖ =
          ‖euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)‖ *
            ‖(φ : H → ℝ) (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))‖ := by
            simp [weight, norm_mul]
      _ ≤ C := by
            simpa [C] using
              mul_le_mul hprofile hφ (norm_nonneg _) hfactor_nonneg
  have hprod_int :
      Integrable
        (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
          boundary p.1 * weight p)
        (μS.prod (μR.restrict R)) :=
    hboundary_prod.mul_bdd hweight_aesm hweight_bound
  rw [IntegrableOn, ← Measure.prod_restrict]
  simpa [Measure.restrict_univ, μS, μR, R, boundary, weight,
    mul_assoc, mul_left_comm, mul_comm] using hprod_int

/--
%%handwave
name:
  Outer smooth polar collar integrability
statement:
  The outer product-collar integrand formed from the transition profile, the
  normal factor, a smooth test function evaluated at \(r\theta\), and an
  integrable boundary trace-normal factor is integrable on the outer product
  collar.
proof:
  The proof is the same as for the inner collar: the radial profile and smooth
  test function are bounded on the collar, and the finite radial measure turns
  the integrable boundary trace-normal factor into an integrable product
  majorant.
-/
private theorem euclideanSobolev_two_unit_collar_exact_trace_pairing_simplified_polar_outer_integrableOn
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [Nontrivial H]
    {τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_inner :
      Integrable
        (fun θ : Metric.sphere (0 : H) 1 ↦
          τ (θ : H) * inner ℝ (θ : H) v)
        ((MeasureTheory.volume : Measure H).toSphere))
    {width : ℝ} (_hwidth_pos : 0 < width)
    (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)) :
    IntegrableOn
      (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
        ((euclideanSobolevTwoUnitOuterRadialProfileDeriv
            width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
          inner ℝ (p.1 : H) v *
          (φ : H → ℝ) (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))) *
          τ (p.1 : H))
      ((Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
        euclideanSobolevTwoUnitOuterRadialCollar width)
      (((MeasureTheory.volume : Measure H).toSphere).prod
        (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1))) := by
  classical
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let R : Set (Set.Ioi (0 : ℝ)) :=
    euclideanSobolevTwoUnitOuterRadialCollar width
  let boundary : Metric.sphere (0 : H) 1 → ℝ :=
    fun θ ↦ τ (θ : H) * inner ℝ (θ : H) v
  let weight : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    fun p ↦
      euclideanSobolevTwoUnitOuterRadialProfileDeriv
          width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) *
        (φ : H → ℝ) (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))
  have hR_meas : MeasurableSet R := by
    simpa [R] using euclideanSobolevTwoUnitOuterRadialCollar_measurableSet width
  have hR_lt_top : μR R < (∞ : ℝ≥0∞) := by
    simpa [μR, R] using
      euclideanSobolevTwoUnitOuterRadialCollar_measure_lt_top
        (Module.finrank ℝ H - 1) (width := width) _hwidth_le_quarter
  haveI : IsFiniteMeasure (μR.restrict R) :=
    isFiniteMeasure_restrict.2 (ne_of_lt hR_lt_top)
  have hboundary_int : Integrable boundary μS := by
    simpa [boundary, μS] using _hτ_inner
  have hboundary_prod :
      Integrable
        (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
          boundary p.1)
        (μS.prod (μR.restrict R)) :=
    hboundary_int.comp_fst (μR.restrict R)
  have hpoint_cont :
      Continuous
        (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
          ((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) := by
    fun_prop
  have hφ_meas :
      Measurable
        (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
          (φ : H → ℝ) (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))) :=
    (φ.smooth.continuous.comp hpoint_cont).measurable
  have hprofile_meas :
      Measurable
        (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
          euclideanSobolevTwoUnitOuterRadialProfileDeriv
            width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) :=
    (euclideanSobolevTwoUnitOuterRadialProfileDeriv_measurable width).comp
      measurable_snd
  have hweight_aesm : AEStronglyMeasurable weight (μS.prod (μR.restrict R)) := by
    simpa [weight] using
      (hprofile_meas.mul hφ_meas).aestronglyMeasurable
  obtain ⟨Cprofile, hCprofile_ge_one, hCprofile⟩ :=
    exists_smoothTransition_deriv_bound_Icc_neg_two_two
  have hCprofile_nonneg : 0 ≤ Cprofile :=
    le_trans zero_le_one hCprofile_ge_one
  rcases
      φ.compact_support.exists_bound_of_continuousOn
        φ.smooth.continuous.continuousOn with
    ⟨B₀, hB₀⟩
  let B : ℝ := max B₀ 0
  have hB_nonneg : 0 ≤ B := le_max_right B₀ 0
  have hφ_bound : ∀ z : H, ‖(φ : H → ℝ) z‖ ≤ B := by
    intro z
    by_cases hz : z ∈ tsupport (φ : H → ℝ)
    · exact (hB₀ z hz).trans (le_max_left B₀ 0)
    · have hzero : (φ : H → ℝ) z = 0 :=
        image_eq_zero_of_notMem_tsupport hz
      simp [B, hzero, hB_nonneg]
  let C : ℝ := (Cprofile * (4 / width)) * B
  have hfactor_nonneg : 0 ≤ Cprofile * (4 / width) := by
    exact mul_nonneg hCprofile_nonneg
      (div_nonneg (by norm_num) _hwidth_pos.le)
  have hR_ae : ∀ᵐ r ∂μR.restrict R, r ∈ R :=
    ae_restrict_mem hR_meas
  have hpred_meas :
      MeasurableSet
        {p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) | p.2 ∈ R} :=
    hR_meas.preimage measurable_snd
  have hprod_mem :
      ∀ᵐ p ∂μS.prod (μR.restrict R), p.2 ∈ R := by
    rw [Measure.ae_prod_iff_ae_ae hpred_meas]
    exact Filter.Eventually.of_forall fun _θ ↦ hR_ae
  have hweight_bound :
      ∀ᵐ p ∂μS.prod (μR.restrict R), ‖weight p‖ ≤ C := by
    filter_upwards [hprod_mem] with p hpR
    have hprofile :
        ‖euclideanSobolevTwoUnitOuterRadialProfileDeriv
            width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)‖ ≤
          Cprofile * (4 / width) :=
      euclideanSobolevTwoUnitOuterRadialProfileDeriv_norm_le
        _hwidth_pos hCprofile hpR
    have hφ :
        ‖(φ : H → ℝ) (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))‖ ≤ B :=
      hφ_bound (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))
    calc
      ‖weight p‖ =
          ‖euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)‖ *
            ‖(φ : H → ℝ) (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))‖ := by
            simp [weight, norm_mul]
      _ ≤ C := by
            simpa [C] using
              mul_le_mul hprofile hφ (norm_nonneg _) hfactor_nonneg
  have hprod_int :
      Integrable
        (fun p : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) ↦
          boundary p.1 * weight p)
        (μS.prod (μR.restrict R)) :=
    hboundary_prod.mul_bdd hweight_aesm hweight_bound
  rw [IntegrableOn, ← Measure.prod_restrict]
  simpa [Measure.restrict_univ, μS, μR, R, boundary, weight,
    mul_assoc, mul_left_comm, mul_comm] using hprod_int

/--
%%handwave
name:
  Fubini for the two smooth polar collars
statement:
  For a smooth compactly supported test function and an integrable boundary
  trace factor, the sum of the two product collar integrals equals the integral
  over the sphere of the corresponding one-dimensional radial collar sum.
proof:
  The two collar integrands are measurable on the product collars.  Their
  absolute values are dominated by a finite radial profile bound times the sum
  of the two integrable boundary factors
  \(|\tau(\theta)\langle\theta,v\rangle|\) and
  \(|\tau(\theta)\varphi(\theta)\langle\theta,v\rangle|\).  Hence the
  product integrands are integrable, and Fubini's theorem applies on each
  collar.
-/
private theorem euclideanSobolev_two_unit_collar_exact_trace_pairing_simplified_polar_product_eq_iterated
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [Nontrivial H]
    {τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_inner :
      Integrable
        (fun θ : Metric.sphere (0 : H) 1 ↦
          τ (θ : H) * inner ℝ (θ : H) v)
        ((MeasureTheory.volume : Measure H).toSphere))
    (_hτ_weighted :
      Integrable
        (fun θ : Metric.sphere (0 : H) 1 ↦
          τ (θ : H) * (φ : H → ℝ) (θ : H) * inner ℝ (θ : H) v)
        ((MeasureTheory.volume : Measure H).toSphere)) :
    ∀ {width : ℝ}
      (_hwidth_pos : 0 < width)
      (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
      euclideanSobolevTwoUnitAbstractProductSum
        ((MeasureTheory.volume : Measure H).toSphere)
        (Module.finrank ℝ H - 1)
        (fun θ : Metric.sphere (0 : H) 1 ↦ inner ℝ (θ : H) v)
        (fun θ : Metric.sphere (0 : H) 1 ↦ τ (θ : H))
        (fun θ : Metric.sphere (0 : H) 1 ↦
          fun r : ℝ ↦ (φ : H → ℝ) (r • (θ : H)))
        width =
        ∫ θ,
            euclideanSobolevTwoUnitAbstractRadialSum
              (Module.finrank ℝ H - 1)
              (fun θ : Metric.sphere (0 : H) 1 ↦ inner ℝ (θ : H) v)
              (fun θ : Metric.sphere (0 : H) 1 ↦ τ (θ : H))
              (fun θ : Metric.sphere (0 : H) 1 ↦
                fun r : ℝ ↦ (φ : H → ℝ) (r • (θ : H)))
              width θ
            ∂((MeasureTheory.volume : Measure H).toSphere) := by
  intro width hwidth_pos hwidth_le_quarter
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let μR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)
  let n : ℕ := Module.finrank ℝ H - 1
  let normal : Metric.sphere (0 : H) 1 → ℝ :=
    fun θ ↦ inner ℝ (θ : H) v
  let trace : Metric.sphere (0 : H) 1 → ℝ :=
    fun θ ↦ τ (θ : H)
  let Φ : Metric.sphere (0 : H) 1 → ℝ → ℝ :=
    fun θ r ↦ (φ : H → ℝ) (r • (θ : H))
  let Finner : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    fun p ↦
      ((euclideanSobolevTwoUnitInnerRadialProfileDeriv
          width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
        normal p.1 * Φ p.1 ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
        trace p.1
  let Fouter : Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    fun p ↦
      ((euclideanSobolevTwoUnitOuterRadialProfileDeriv
          width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
        normal p.1 * Φ p.1 ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
        trace p.1
  have hinner_int :
      IntegrableOn Finner
        ((Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
          euclideanSobolevTwoUnitInnerRadialCollar width)
        (μS.prod μR) := by
    simpa [Finner, μS, μR, n, normal, trace, Φ, mul_assoc] using
      euclideanSobolev_two_unit_collar_exact_trace_pairing_simplified_polar_inner_integrableOn
        (τ := τ) φ v _hτ_inner hwidth_pos hwidth_le_quarter
  have houter_int :
      IntegrableOn Fouter
        ((Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
          euclideanSobolevTwoUnitOuterRadialCollar width)
        (μS.prod μR) := by
    simpa [Fouter, μS, μR, n, normal, trace, Φ, mul_assoc] using
      euclideanSobolev_two_unit_collar_exact_trace_pairing_simplified_polar_outer_integrableOn
        (τ := τ) φ v _hτ_inner hwidth_pos hwidth_le_quarter
  have hinner_prod :
      (∫ p in
          (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
            euclideanSobolevTwoUnitInnerRadialCollar width,
          Finner p ∂(μS.prod μR)) =
        ∫ θ in (Set.univ : Set (Metric.sphere (0 : H) 1)),
          ∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
            Finner (θ, r) ∂μR ∂μS := by
    exact MeasureTheory.setIntegral_prod Finner hinner_int
  have houter_prod :
      (∫ p in
          (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
            euclideanSobolevTwoUnitOuterRadialCollar width,
          Fouter p ∂(μS.prod μR)) =
        ∫ θ in (Set.univ : Set (Metric.sphere (0 : H) 1)),
          ∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
            Fouter (θ, r) ∂μR ∂μS := by
    exact MeasureTheory.setIntegral_prod Fouter houter_int
  have hinner_iter_int :
      Integrable
        (fun θ : Metric.sphere (0 : H) 1 ↦
          ∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
            Finner (θ, r) ∂μR) μS := by
    rw [IntegrableOn, ← Measure.prod_restrict] at hinner_int
    have h := hinner_int.integral_prod_left
    simpa [Measure.restrict_univ] using h
  have houter_iter_int :
      Integrable
        (fun θ : Metric.sphere (0 : H) 1 ↦
          ∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
            Fouter (θ, r) ∂μR) μS := by
    rw [IntegrableOn, ← Measure.prod_restrict] at houter_int
    have h := houter_int.integral_prod_left
    simpa [Measure.restrict_univ] using h
  dsimp [euclideanSobolevTwoUnitAbstractProductSum,
    euclideanSobolevTwoUnitAbstractRadialSum]
  rw [show
      (∫ p in
          (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
            euclideanSobolevTwoUnitInnerRadialCollar width,
          ((euclideanSobolevTwoUnitInnerRadialProfileDeriv
              width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
            normal p.1 *
            Φ p.1 ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
            trace p.1 ∂(μS.prod μR)) =
        ∫ θ in (Set.univ : Set (Metric.sphere (0 : H) 1)),
          ∫ r in euclideanSobolevTwoUnitInnerRadialCollar width,
            Finner (θ, r) ∂μR ∂μS by
        simpa [Finner, normal, trace, Φ, mul_assoc] using hinner_prod]
  rw [show
      (∫ p in
          (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
            euclideanSobolevTwoUnitOuterRadialCollar width,
          ((euclideanSobolevTwoUnitOuterRadialProfileDeriv
              width ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
            normal p.1 *
            Φ p.1 ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) *
            trace p.1 ∂(μS.prod μR)) =
          ∫ θ in (Set.univ : Set (Metric.sphere (0 : H) 1)),
            ∫ r in euclideanSobolevTwoUnitOuterRadialCollar width,
              Fouter (θ, r) ∂μR ∂μS by
    simpa [Fouter, normal, trace, Φ, mul_assoc] using houter_prod]
  simp only [Measure.restrict_univ]
  rw [← integral_add hinner_iter_int houter_iter_int]

/--
%%handwave
name:
  Radial cancellation with integrable boundary factors
statement:
  Assume that both boundary factors
  \(\tau(\theta)\langle\theta,v\rangle\) and
  \(\tau(\theta)\varphi(\theta)\langle\theta,v\rangle\) are integrable on the
  unit sphere.  If the transition-profile derivative is uniformly bounded and
  \(\varphi\) varies Lipschitzly along unit rays, then the sum of the two
  simplified polar collar pairings is bounded by a constant times the collar
  width.
proof:
  Rewrite both radial collars using the common transition parameter.  The
  frozen term at radius one has opposite oriented mass in the two collars and
  cancels exactly.  The remaining terms are controlled by the ray-Lipschitz
  variation of \(\varphi\) and by the Lipschitz variation of the polar density
  \(r^{n-1}\) on \(3/4\le r\le5/4\).  These bounds are multiplied by the two
  integrable boundary factors.
-/
private theorem euclideanSobolev_two_unit_collar_exact_trace_pairing_simplified_polar_norm_le_width_of_integrable_boundary_factors
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [Nontrivial H]
    {τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (Cprofile Lφ : ℝ)
    (_hCprofile_ge_one : 1 ≤ Cprofile)
    (_hCprofile : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ Cprofile)
    (_hLφ_nonneg : 0 ≤ Lφ)
    (_hφ_radial_lipschitz :
      ∀ (θ : Metric.sphere (0 : H) 1) (r : ℝ),
        ‖(φ : H → ℝ) (r • (θ : H)) - (φ : H → ℝ) (θ : H)‖ ≤
          Lφ * ‖r - 1‖)
    (_hτ_inner :
      Integrable
        (fun θ : Metric.sphere (0 : H) 1 ↦
          τ (θ : H) * inner ℝ (θ : H) v)
        ((MeasureTheory.volume : Measure H).toSphere))
    (_hτ_weighted :
      Integrable
        (fun θ : Metric.sphere (0 : H) 1 ↦
          τ (θ : H) * (φ : H → ℝ) (θ : H) * inner ℝ (θ : H) v)
        ((MeasureTheory.volume : Measure H).toSphere)) :
    ∃ K : ℝ,
      0 ≤ K ∧
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
          ‖(∫ p in
              (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
                {r : Set.Ioi (0 : ℝ) |
                  (1 : ℝ) - width < (r : ℝ) ∧ (r : ℝ) < 1},
              ((deriv Real.smoothTransition
                  (((1 : ℝ) - width / 2 -
                      ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) / (width / 4)) *
                (-(1 : ℝ) / (width / 4))) *
                inner ℝ (p.1 : H) v *
                (φ : H → ℝ)
                  (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))) *
                τ (p.1 : H)
              ∂(((MeasureTheory.volume : Measure H).toSphere).prod
                (MeasureTheory.Measure.volumeIoiPow
                  (Module.finrank ℝ H - 1)))) +
            ∫ p in
              (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
                {r : Set.Ioi (0 : ℝ) |
                  (1 : ℝ) < (r : ℝ) ∧ (r : ℝ) < 1 + width},
              ((deriv Real.smoothTransition
                  ((((p.2 : Set.Ioi (0 : ℝ)) : ℝ) -
                      ((1 : ℝ) + width / 2)) / (width / 4)) *
                ((1 : ℝ) / (width / 4))) *
                inner ℝ (p.1 : H) v *
                (φ : H → ℝ)
                  (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))) *
                τ (p.1 : H)
              ∂(((MeasureTheory.volume : Measure H).toSphere).prod
                (MeasureTheory.Measure.volumeIoiPow
                  (Module.finrank ℝ H - 1)))‖ ≤ K * width := by
  let μS : Measure (Metric.sphere (0 : H) 1) :=
    (MeasureTheory.volume : Measure H).toSphere
  let n : ℕ := Module.finrank ℝ H - 1
  let normal : Metric.sphere (0 : H) 1 → ℝ := fun θ ↦ inner ℝ (θ : H) v
  let trace : Metric.sphere (0 : H) 1 → ℝ := fun θ ↦ τ (θ : H)
  let Φ : Metric.sphere (0 : H) 1 → ℝ → ℝ :=
    fun θ r ↦ (φ : H → ℝ) (r • (θ : H))
  have hΦ_lipschitz :
      ∀ (θ : Metric.sphere (0 : H) 1) (r : ℝ),
        ‖Φ θ r - Φ θ 1‖ ≤ Lφ * ‖r - 1‖ := by
    intro θ r
    simpa [Φ] using _hφ_radial_lipschitz θ r
  have hΦ_radial_measurable :
      ∀ θ : Metric.sphere (0 : H) 1, Measurable (Φ θ) := by
    intro θ
    have hcont : Continuous (fun r : ℝ ↦
        (φ : H → ℝ) (r • (θ : H))) := by
      exact φ.smooth.continuous.comp
        (continuous_id.smul continuous_const)
    simpa [Φ] using hcont.measurable
  have htrace_normal :
      Integrable (fun θ : Metric.sphere (0 : H) 1 ↦
        trace θ * normal θ) μS := by
    simpa [trace, normal, μS] using _hτ_inner
  have htrace_frozen_weight :
      Integrable (fun θ : Metric.sphere (0 : H) 1 ↦
        trace θ * Φ θ 1 * normal θ) μS := by
    simpa [trace, normal, Φ, μS] using _hτ_weighted
  have hproduct_to_radial :
      ∀ {width : ℝ}
        (_hwidth_pos : 0 < width)
        (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
        euclideanSobolevTwoUnitAbstractProductSum
          μS n normal trace Φ width =
          ∫ θ, euclideanSobolevTwoUnitAbstractRadialSum
            n normal trace Φ width θ ∂μS := by
    intro width hwidth_pos hwidth_le_quarter
    simpa [μS, n, normal, trace, Φ] using
      euclideanSobolev_two_unit_collar_exact_trace_pairing_simplified_polar_product_eq_iterated
        (τ := τ) φ v _hτ_inner _hτ_weighted
        hwidth_pos hwidth_le_quarter
  obtain ⟨K, hK_nonneg, hK_bound⟩ :=
    euclideanSobolev_two_unit_collar_abstract_radial_cancellation_norm_le_width
      μS n normal trace Φ Cprofile Lφ
      _hCprofile_ge_one _hCprofile _hLφ_nonneg hΦ_lipschitz
      hΦ_radial_measurable htrace_normal htrace_frozen_weight
      hproduct_to_radial
  refine ⟨K, hK_nonneg, ?_⟩
  intro width hwidth_pos hwidth_le_quarter
  simpa [μS, n, normal, trace, Φ] using
    hK_bound hwidth_pos hwidth_le_quarter

/--
%%handwave
name:
  Radial cancellation from uniform profile and ray-variation bounds
statement:
  Suppose the transition-profile derivative is uniformly bounded and the smooth
  test function varies Lipschitzly along every unit ray.  Then the two
  polar-coordinate collar integrals adjacent to the unit sphere are bounded by
  a constant times the collar width.
proof:
  Change variables in the two radial collars to the common parameter
  \(t\in[0,1]\).  The inner radius is \(1-\delta/2-\delta t/4\), while the
  outer radius is \(1+\delta/2+\delta t/4\), and the two profile derivatives
  enter with opposite signs.  The frozen term at radius one cancels.  The
  difference of the remaining factors is \(O(\delta)\): the test function is
  controlled by the ray-Lipschitz bound, and the polar density is Lipschitz on
  the fixed annulus \(3/4\le r\le5/4\).  The sphere factor is integrable, so the
  product estimate gives the claimed bound.
-/
private theorem euclideanSobolev_two_unit_collar_exact_trace_pairing_simplified_polar_norm_le_width_of_profile_bound_and_radial_lipschitz
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [Nontrivial H]
    {τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (Cprofile Lφ : ℝ)
    (_hCprofile_ge_one : 1 ≤ Cprofile)
    (_hCprofile : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ Cprofile)
    (_hLφ_nonneg : 0 ≤ Lφ)
    (_hφ_radial_lipschitz :
      ∀ (θ : Metric.sphere (0 : H) 1) (r : ℝ),
        ‖(φ : H → ℝ) (r • (θ : H)) - (φ : H → ℝ) (θ : H)‖ ≤
          Lφ * ‖r - 1‖)
    (_hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ K : ℝ,
      0 ≤ K ∧
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
          ‖(∫ p in
              (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
                {r : Set.Ioi (0 : ℝ) |
                  (1 : ℝ) - width < (r : ℝ) ∧ (r : ℝ) < 1},
              ((deriv Real.smoothTransition
                  (((1 : ℝ) - width / 2 -
                      ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) / (width / 4)) *
                (-(1 : ℝ) / (width / 4))) *
                inner ℝ (p.1 : H) v *
                (φ : H → ℝ)
                  (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))) *
                τ (p.1 : H)
              ∂(((MeasureTheory.volume : Measure H).toSphere).prod
                (MeasureTheory.Measure.volumeIoiPow
                  (Module.finrank ℝ H - 1)))) +
            ∫ p in
              (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
                {r : Set.Ioi (0 : ℝ) |
                  (1 : ℝ) < (r : ℝ) ∧ (r : ℝ) < 1 + width},
              ((deriv Real.smoothTransition
                  ((((p.2 : Set.Ioi (0 : ℝ)) : ℝ) -
                      ((1 : ℝ) + width / 2)) / (width / 4)) *
                ((1 : ℝ) / (width / 4))) *
                inner ℝ (p.1 : H) v *
                (φ : H → ℝ)
                  (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))) *
                τ (p.1 : H)
              ∂(((MeasureTheory.volume : Measure H).toSphere).prod
                (MeasureTheory.Measure.volumeIoiPow
                  (Module.finrank ℝ H - 1)))‖ ≤ K * width := by
  have hτ_inner :
      Integrable
        (fun θ : Metric.sphere (0 : H) 1 ↦
          τ (θ : H) * inner ℝ (θ : H) v)
        ((MeasureTheory.volume : Measure H).toSphere) :=
    euclideanSobolev_unit_sphere_trace_inner_integrable_of_weighted
      (H := H) (τ := τ) φ v _hτ_weight
  have hτ_weighted :
      Integrable
        (fun θ : Metric.sphere (0 : H) 1 ↦
          τ (θ : H) * (φ : H → ℝ) (θ : H) * inner ℝ (θ : H) v)
        ((MeasureTheory.volume : Measure H).toSphere) :=
    _hτ_weight.2
  exact
    euclideanSobolev_two_unit_collar_exact_trace_pairing_simplified_polar_norm_le_width_of_integrable_boundary_factors
      (τ := τ) φ v Cprofile Lφ _hCprofile_ge_one _hCprofile
      _hLφ_nonneg _hφ_radial_lipschitz hτ_inner hτ_weighted

/--
%%handwave
name:
  Simplified polar exact trace collar pairing is linear in the width
statement:
  After substituting the polar identities \(\|r\theta\|=r\),
  \(\|r\theta\|^{-1}r\theta=\theta\), and
  \(\tau((r\theta)/\|r\theta\|)=\tau(\theta)\), the two unit-sphere collar
  contributions are bounded by a constant times the collar width.
proof:
  The two profile derivatives are the same compactly supported
  one-dimensional derivative with opposite orientation.  The frozen boundary
  contribution therefore cancels exactly.  The residual is the product of the
  integrable sphere factor with the radial variation of the smooth test
  factor and the polar density, which is uniformly \(O(\delta)\).
-/
private theorem euclideanSobolev_two_unit_collar_exact_trace_pairing_simplified_polar_norm_le_width_nontrivial
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [Nontrivial H]
    {τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ K : ℝ,
      0 ≤ K ∧
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
          ‖(∫ p in
              (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
                {r : Set.Ioi (0 : ℝ) |
                  (1 : ℝ) - width < (r : ℝ) ∧ (r : ℝ) < 1},
              ((deriv Real.smoothTransition
                  (((1 : ℝ) - width / 2 -
                      ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) / (width / 4)) *
                (-(1 : ℝ) / (width / 4))) *
                inner ℝ (p.1 : H) v *
                (φ : H → ℝ)
                  (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))) *
                τ (p.1 : H)
              ∂(((MeasureTheory.volume : Measure H).toSphere).prod
                (MeasureTheory.Measure.volumeIoiPow
                  (Module.finrank ℝ H - 1)))) +
            ∫ p in
              (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
                {r : Set.Ioi (0 : ℝ) |
                  (1 : ℝ) < (r : ℝ) ∧ (r : ℝ) < 1 + width},
              ((deriv Real.smoothTransition
                  ((((p.2 : Set.Ioi (0 : ℝ)) : ℝ) -
                      ((1 : ℝ) + width / 2)) / (width / 4)) *
                ((1 : ℝ) / (width / 4))) *
                inner ℝ (p.1 : H) v *
                (φ : H → ℝ)
                  (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))) *
                τ (p.1 : H)
              ∂(((MeasureTheory.volume : Measure H).toSphere).prod
                (MeasureTheory.Measure.volumeIoiPow
                  (Module.finrank ℝ H - 1)))‖ ≤ K * width := by
  obtain ⟨Cprofile, hCprofile_ge_one, hCprofile⟩ :=
    exists_smoothTransition_deriv_bound_Icc_neg_two_two
  obtain ⟨Lφ, hLφ_nonneg, hφ_radial_lipschitz⟩ :=
    smoothCompactlySupportedCoordinateFunction_exists_radial_lipschitz_bound φ
  exact
    euclideanSobolev_two_unit_collar_exact_trace_pairing_simplified_polar_norm_le_width_of_profile_bound_and_radial_lipschitz
      (τ := τ) φ v Cprofile Lφ hCprofile_ge_one hCprofile
      hLφ_nonneg hφ_radial_lipschitz _hτ_weight

/--
%%handwave
name:
  The polar-product exact trace collar pairing is linear in the width
statement:
  In a nontrivial finite-dimensional Euclidean space, the two polar-product
  integrals obtained from the inner and outer unit-sphere collars are bounded
  by a constant times the collar width.
proof:
  For each fixed direction on the unit sphere, subtract the frozen value at
  radius one from the smooth test factor and the polar density.  The two
  one-dimensional profile derivative integrals of the frozen term have
  opposite signs and cancel.  The residual is bounded by the collar width
  times an integrable multiple of the boundary trace, uniformly in the sphere
  variable.
-/
private theorem euclideanSobolev_two_unit_collar_exact_trace_pairing_polar_norm_le_width_nontrivial
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [Nontrivial H]
    {τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ K : ℝ,
      0 ≤ K ∧
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
          ‖(∫ p in
              (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
                {r : Set.Ioi (0 : ℝ) |
                  (1 : ℝ) - width < (r : ℝ) ∧ (r : ℝ) < 1},
              euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
                width (φ : H → ℝ) v
                (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) •
                euclideanSobolevUnitSphereRadialTrace τ
                  (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))
              ∂(((MeasureTheory.volume : Measure H).toSphere).prod
                (MeasureTheory.Measure.volumeIoiPow
                  (Module.finrank ℝ H - 1)))) +
            ∫ p in
              (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
                {r : Set.Ioi (0 : ℝ) |
                  (1 : ℝ) < (r : ℝ) ∧ (r : ℝ) < 1 + width},
              euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
                width (φ : H → ℝ) v
                (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) •
                euclideanSobolevUnitSphereRadialTrace τ
                  (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))
              ∂(((MeasureTheory.volume : Measure H).toSphere).prod
                (MeasureTheory.Measure.volumeIoiPow
                  (Module.finrank ℝ H - 1)))‖ ≤ K * width := by
  obtain ⟨K, hK_nonneg, hK_bound⟩ :=
    euclideanSobolev_two_unit_collar_exact_trace_pairing_simplified_polar_norm_le_width_nontrivial
      (τ := τ) φ v _hτ_weight
  refine ⟨K, hK_nonneg, ?_⟩
  intro width hwidth_pos hwidth_le_quarter
  let Sminus : Set (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
      {r : Set.Ioi (0 : ℝ) |
        (1 : ℝ) - width < (r : ℝ) ∧ (r : ℝ) < 1}
  let Splus : Set (Metric.sphere (0 : H) 1 × Set.Ioi (0 : ℝ)) :=
    (Set.univ : Set (Metric.sphere (0 : H) 1)) ×ˢ
      {r : Set.Ioi (0 : ℝ) |
        (1 : ℝ) < (r : ℝ) ∧ (r : ℝ) < 1 + width}
  have hRminus :
      MeasurableSet
        {r : Set.Ioi (0 : ℝ) |
          (1 : ℝ) - width < (r : ℝ) ∧ (r : ℝ) < 1} := by
    exact
      (isOpen_lt continuous_const continuous_subtype_val).measurableSet.inter
        (isOpen_lt continuous_subtype_val continuous_const).measurableSet
  have hRplus :
      MeasurableSet
        {r : Set.Ioi (0 : ℝ) |
          (1 : ℝ) < (r : ℝ) ∧ (r : ℝ) < 1 + width} := by
    exact
      (isOpen_lt continuous_const continuous_subtype_val).measurableSet.inter
        (isOpen_lt continuous_subtype_val continuous_const).measurableSet
  have hSminus : MeasurableSet Sminus := by
    dsimp [Sminus]
    exact MeasurableSet.univ.prod hRminus
  have hSplus : MeasurableSet Splus := by
    dsimp [Splus]
    exact MeasurableSet.univ.prod hRplus
  have hinner_eq :
      (∫ p in Sminus,
        euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
          width (φ : H → ℝ) v
          (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) •
          euclideanSobolevUnitSphereRadialTrace τ
            (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))
        ∂(((MeasureTheory.volume : Measure H).toSphere).prod
          (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)))) =
      ∫ p in Sminus,
        ((deriv Real.smoothTransition
            (((1 : ℝ) - width / 2 -
                ((p.2 : Set.Ioi (0 : ℝ)) : ℝ)) / (width / 4)) *
          (-(1 : ℝ) / (width / 4))) *
          inner ℝ (p.1 : H) v *
          (φ : H → ℝ)
            (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))) *
          τ (p.1 : H)
        ∂(((MeasureTheory.volume : Measure H).toSphere).prod
          (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1))) := by
    refine setIntegral_congr_fun hSminus ?_
    intro p _hp
    exact
      (euclideanSobolev_two_unit_collar_exact_trace_pairing_polar_integrands_simplify
        (τ := τ) (φ := (φ : H → ℝ)) (v := v) (width := width) p).1
  have houter_eq :
      (∫ p in Splus,
        euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
          width (φ : H → ℝ) v
          (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H)) •
          euclideanSobolevUnitSphereRadialTrace τ
            (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))
        ∂(((MeasureTheory.volume : Measure H).toSphere).prod
          (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1)))) =
      ∫ p in Splus,
        ((deriv Real.smoothTransition
            ((((p.2 : Set.Ioi (0 : ℝ)) : ℝ) -
                ((1 : ℝ) + width / 2)) / (width / 4)) *
          ((1 : ℝ) / (width / 4))) *
          inner ℝ (p.1 : H) v *
          (φ : H → ℝ)
            (((p.2 : Set.Ioi (0 : ℝ)) : ℝ) • (p.1 : H))) *
          τ (p.1 : H)
        ∂(((MeasureTheory.volume : Measure H).toSphere).prod
          (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ H - 1))) := by
    refine setIntegral_congr_fun hSplus ?_
    intro p _hp
    exact
      (euclideanSobolev_two_unit_collar_exact_trace_pairing_polar_integrands_simplify
        (τ := τ) (φ := (φ : H → ℝ)) (v := v) (width := width) p).2
  have hbound := hK_bound hwidth_pos hwidth_le_quarter
  rw [← hinner_eq, ← houter_eq] at hbound
  simpa [Sminus, Splus] using hbound

/--
%%handwave
name:
  Polar cancellation for the two unit collars in positive dimension
statement:
  In a nontrivial finite-dimensional Euclidean space, an integrable trace on
  the unit sphere gives a linear-in-width bound for the sum of the exact
  trace contributions in the two collars adjacent to the unit sphere.
proof:
  Use the polar-coordinate homeomorphism on the punctured space.  The two
  collars become products of the unit sphere with two short radial intervals.
  After subtracting the frozen boundary value, the two radial profile
  integrals cancel and the residual is bounded by the radial Lipschitz
  constant of the smooth test factor and the polar density.
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_two_unit_collar_exact_trace_pairing_norm_le_width_nontrivial
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [Nontrivial H]
    {τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ K : ℝ,
      0 ≤ K ∧
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
          ‖(∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
              euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
                width (φ : H → ℝ) v z •
                euclideanSobolevUnitSphereRadialTrace τ z
              ∂MeasureTheory.volume) +
            ∫ z in euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width,
              euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
                width (φ : H → ℝ) v z •
                euclideanSobolevUnitSphereRadialTrace τ z
              ∂MeasureTheory.volume‖ ≤ K * width := by
  obtain ⟨K, hK_nonneg, hK_bound⟩ :=
    euclideanSobolev_two_unit_collar_exact_trace_pairing_polar_norm_le_width_nontrivial
      (τ := τ) φ v _hτ_weight
  refine ⟨K, hK_nonneg, ?_⟩
  intro width hwidth_pos hwidth_le_quarter
  rw [euclideanSobolev_two_unit_collar_exact_trace_pairing_eq_polar
    (τ := τ) φ v hwidth_le_quarter]
  exact hK_bound hwidth_pos hwidth_le_quarter

/--
%%handwave
name:
  Polar cancellation for the two unit-sphere exact trace collars
statement:
  For an integrable trace on the unit sphere, the sum of the exact trace
  contributions in the inner unit-ball collar and the outer annular collar
  adjacent to the unit sphere is bounded by a fixed constant times the collar
  width.
proof:
  Transport both collar integrals to polar coordinates.  In the radial
  variable the two transition derivatives are translates of the same
  one-dimensional profile with opposite signs.  Subtract the frozen boundary
  factor \(\tau(\theta)\varphi(\theta)\langle\theta,v\rangle\); its two
  profile integrals cancel.  The remaining radial variation of the smooth
  factor and the polar density is uniformly \(O(\delta)\), and the sphere
  trace is integrable.
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_two_unit_collar_exact_trace_pairing_norm_le_width
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ K : ℝ,
      0 ≤ K ∧
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
          ‖(∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
              euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
                width (φ : H → ℝ) v z •
                euclideanSobolevUnitSphereRadialTrace τ z
              ∂MeasureTheory.volume) +
            ∫ z in euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width,
              euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight
                width (φ : H → ℝ) v z •
                euclideanSobolevUnitSphereRadialTrace τ z
              ∂MeasureTheory.volume‖ ≤ K * width := by
  classical
  by_cases hsub : Subsingleton H
  · haveI : Subsingleton H := hsub
    refine ⟨0, le_rfl, ?_⟩
    intro width _hwidth_pos hwidth_le_quarter
    have hunit_empty :
        euclideanSobolevUnitBallInnerTransitionCollar H width = ∅ := by
      ext z
      constructor
      · intro hz
        have hz0 : z = (0 : H) := Subsingleton.elim z 0
        have hlt : (1 : ℝ) - width < 0 := by
          simpa [euclideanSobolevUnitBallInnerTransitionCollar, hz0] using hz.1
        nlinarith [hwidth_le_quarter]
      · intro hz
        cases hz
    have hannulus_empty :
        euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width = ∅ := by
      ext z
      constructor
      · intro hz
        have hz0 : z = (0 : H) := Subsingleton.elim z 0
        have hlt : (1 : ℝ) < 0 := by
          simpa [euclideanSobolevUnitBallAnnulusInnerTransitionCollar, hz0] using hz.1
        nlinarith
      · intro hz
        cases hz
    simp [hunit_empty, hannulus_empty]
  · haveI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hsub
    exact
      euclideanSobolev_unit_ball_annulus_l1_trace_glue_two_unit_collar_exact_trace_pairing_norm_le_width_nontrivial
        (τ := τ) φ v _hτ_weight

/--
%%handwave
name:
  The exact radial-trace oriented pairing is linear in the collar width
statement:
  For an integrable trace on the unit sphere, the exact radial-trace
  contribution of the two unit-sphere collars and the zero outer trace is
  bounded by a fixed constant times the collar width.
proof:
  Write the two unit collars in polar coordinates.  The inner and outer unit
  collar profiles have opposite oriented total mass, so their frozen
  boundary terms cancel.  The remaining terms contain only the radial
  variation of the smooth test factor and the polar Jacobian.  These
  variations are uniformly Lipschitz on the fixed compact annulus, while the
  boundary trace is integrable on the sphere.  The outer \(3/2\)-sphere term
  is zero by construction.
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_exact_oriented_radial_trace_pairing_norm_le_width
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {τ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ K : ℝ,
      0 ≤ K ∧
        ∀ {width : ℝ}
          (_hwidth_pos : 0 < width)
          (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ)),
          ‖euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing
            (H := H) width φ v τ‖ ≤ K * width := by
  obtain ⟨K, hK_nonneg, hK_bound⟩ :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_two_unit_collar_exact_trace_pairing_norm_le_width
      (τ := τ) φ v _hτ_weight
  refine ⟨K, hK_nonneg, ?_⟩
  intro width hwidth_pos hwidth_le_quarter
  rw [euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing_eq_two_unit_collars]
  exact hK_bound hwidth_pos hwidth_le_quarter

/--
%%handwave
name:
  The exact radial-trace oriented pairing is small on thin collars
statement:
  For an integrable trace, the exact radial-trace contribution of the two
  unit-sphere collars and the zero outer trace is \(O(\delta)\) after the
  leading opposite oriented unit-sphere contributions cancel.
proof:
  Write the two unit collars in polar coordinates.  The radial derivatives of
  the two transition profiles have opposite total mass, so the frozen
  boundary term
  \(\int_{\mathbb S} \tau(\theta)\varphi(\theta)\langle\theta,v\rangle\)
  cancels.  The remaining terms contain the radial variation of the smooth
  factor and of the polar Jacobian, both uniformly \(O(\delta)\); the
  integrability of \(\tau\) on the sphere gives the required absolute
  continuity.  The outer \(3/2\)-sphere exact trace term is identically zero.
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_exact_oriented_radial_trace_pairing_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {τ : H → ℝ}
    (Cprofile : ℝ) (_hCprofile_ge_one : 1 ≤ Cprofile)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ C : ℝ,
      Cprofile ≤ C ∧
        1 ≤ C ∧
          ∀ {η width : ℝ}
            (_hη_pos : 0 < η)
            (_hwidth_pos : 0 < width)
            (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
            (_hwidth_le : width ≤ η / C),
            ‖euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing
              (H := H) width φ v τ‖ ≤ η / 2 := by
  obtain ⟨K, hK_nonneg, hK_bound⟩ :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_exact_oriented_radial_trace_pairing_norm_le_width
      (τ := τ) φ v _hτ_weight
  let C : ℝ := max Cprofile (max (1 : ℝ) (2 * K))
  refine ⟨C, ?_, ?_, ?_⟩
  · exact le_max_left Cprofile (max (1 : ℝ) (2 * K))
  · exact (le_max_left (1 : ℝ) (2 * K)).trans
      (le_max_right Cprofile (max (1 : ℝ) (2 * K)))
  · intro η width hη_pos hwidth_pos hwidth_le_quarter hwidth_le
    have hC_ge_one : 1 ≤ C :=
      (le_max_left (1 : ℝ) (2 * K)).trans
        (le_max_right Cprofile (max (1 : ℝ) (2 * K)))
    have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC_ge_one
    have hK_le_halfC : K / C ≤ (1 / 2 : ℝ) := by
      have htwoK_le_C : 2 * K ≤ C :=
        (le_max_right (1 : ℝ) (2 * K)).trans
          (le_max_right Cprofile (max (1 : ℝ) (2 * K)))
      rw [div_le_iff₀ hC_pos]
      nlinarith
    calc
      ‖euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing
          (H := H) width φ v τ‖
          ≤ K * width := hK_bound hwidth_pos hwidth_le_quarter
      _ ≤ K * (η / C) :=
          mul_le_mul_of_nonneg_left hwidth_le hK_nonneg
      _ = η * (K / C) := by ring
      _ ≤ η * (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hK_le_halfC hη_pos.le
      _ = η / 2 := by ring

/--
%%handwave
name:
  The polar estimate for the explicit oriented radial collar weights
statement:
  Fix a bound for the one-dimensional transition-profile derivatives.  For
  the explicit inward, outward, and outer radial collar weights, there is a
  finite constant \(C\) such that the sum of the unit-collar and annulus-collar
  pairings is bounded by \(\eta\), provided the collar width and the normalized
  \(L^1\)-trace errors are both at most \(\eta/C\).
proof:
  Insert and subtract the radial traces in each collar.  The trace-error
  pieces are controlled by the normalized \(L^1\)-trace errors and the
  derivative-profile bound.  In polar coordinates the two unit-sphere exact
  trace terms carry opposite oriented radial weights and cancel to first
  order.  The outer \(3/2\)-sphere exact trace term vanishes because the trace
  there is zero.  The remaining radial variation of the fixed smooth weight
  and the polar Jacobian is \(O(\delta)\), and absolute continuity for the
  integrable weighted trace absorbs it after enlarging \(C\).
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_explicit_oriented_radial_pairing_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (Cprofile : ℝ) (hCprofile_ge_one : 1 ≤ Cprofile)
    (hCprofile : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ Cprofile)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ C : ℝ,
      Cprofile ≤ C ∧
        1 ≤ C ∧
          ∀ {η width : ℝ}
            (_hη_pos : 0 < η)
            (_hwidth_pos : 0 < width)
            (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
            (_hwidth_le : width ≤ η / C),
            sphereInnerL1TraceError (H := H) 1 u₀ τ width +
                sphereOuterL1TraceError (H := H) 1 u₁ τ width +
                  sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                    u₁ (fun _x : H ↦ 0) width ≤
              ENNReal.ofReal (η / C) →
              ‖(∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
                  euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
                    width (φ : H → ℝ) v z • u₀ z
                  ∂MeasureTheory.volume) +
                ∫ z in
                  euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
                    euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
                  euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
                    width (φ : H → ℝ) v z • u₁ z
                  ∂MeasureTheory.volume‖ ≤ η := by
  obtain ⟨Cerror, hCprofile_le_error, hCerror_ge_one, herror⟩ :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_oriented_radial_trace_error_dist_bound
      (u₀ := u₀) (u₁ := u₁) (τ := τ)
      hu₀_aesm hu₁_aesm
      Cprofile hCprofile_ge_one hCprofile φ v _hτ_weight
  obtain ⟨Ctrace, hCprofile_le_trace, hCtrace_ge_one, htrace_exact⟩ :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_exact_oriented_radial_trace_pairing_bound
      (τ := τ) Cprofile hCprofile_ge_one φ v _hτ_weight
  let C : ℝ := max Cerror Ctrace
  refine ⟨C, ?_, ?_, ?_⟩
  · exact hCprofile_le_error.trans (le_max_left Cerror Ctrace)
  · exact hCerror_ge_one.trans (le_max_left Cerror Ctrace)
  · intro η width hη_pos hwidth_pos hwidth_le_quarter hwidth_le htrace
    let original : ℝ :=
      euclideanSobolevUnitBallAnnulusExplicitOrientedPairing
        (H := H) width φ v u₀ u₁
    let exactTrace : ℝ :=
      euclideanSobolevUnitBallAnnulusExactTraceOrientedPairing
        (H := H) width φ v τ
    have hCerror_le_C : Cerror ≤ C := le_max_left Cerror Ctrace
    have hCtrace_le_C : Ctrace ≤ C := le_max_right Cerror Ctrace
    have hCerror_pos : 0 < Cerror :=
      lt_of_lt_of_le zero_lt_one hCerror_ge_one
    have hCtrace_pos : 0 < Ctrace :=
      lt_of_lt_of_le zero_lt_one hCtrace_ge_one
    have htrace_mono :
        ENNReal.ofReal (η / C) ≤ ENNReal.ofReal (η / Cerror) := by
      exact
        ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_left hη_pos.le hCerror_pos hCerror_le_C)
    have htrace_for_error :
        sphereInnerL1TraceError (H := H) 1 u₀ τ width +
            sphereOuterL1TraceError (H := H) 1 u₁ τ width +
              sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                u₁ (fun _x : H ↦ 0) width ≤
          ENNReal.ofReal (η / Cerror) :=
      htrace.trans htrace_mono
    have hdist :
        dist original exactTrace ≤ η / 2 := by
      simpa [original, exactTrace] using
        herror (η := η) (width := width) hη_pos hwidth_pos
          hwidth_le_quarter htrace_for_error
    have hwidth_for_trace : width ≤ η / Ctrace := by
      exact hwidth_le.trans
        (div_le_div_of_nonneg_left hη_pos.le hCtrace_pos hCtrace_le_C)
    have hexact :
        ‖exactTrace‖ ≤ η / 2 := by
      simpa [exactTrace] using
        htrace_exact (η := η) (width := width) hη_pos hwidth_pos
          hwidth_le_quarter hwidth_for_trace
    change ‖original‖ ≤ η
    calc
      ‖original‖ = dist original 0 := by
        simp [dist_eq_norm]
      _ ≤ dist original exactTrace + dist exactTrace 0 :=
        dist_triangle original exactTrace 0
      _ = dist original exactTrace + ‖exactTrace‖ := by
        simp [dist_eq_norm]
      _ ≤ η / 2 + η / 2 := add_le_add hdist hexact
      _ = η := by ring

/--
%%handwave
name:
  The radial-profile polar estimate for weighted trace collar pairings
statement:
  Fix a bound for the one-dimensional transition-profile derivatives.  If
  the cutoff derivatives on the three collars are given by the corresponding
  radial profile derivative times the radial normal component, and if they
  satisfy the stated \(C/\delta\) bounds, then a finite constant controls the
  sum of the three collar pairings by the normalized \(L^1\)-trace errors and
  by the collar width.
proof:
  Insert and subtract the radial trace on each collar.  The error terms are
  bounded by the normalized \(L^1\)-trace errors and the \(C/\delta\)
  derivative bounds.  For the exact trace terms, use polar coordinates.  The
  inner and outer unit-sphere collar contributions have opposite radial
  orientations and the same one-dimensional transition profile, hence their
  leading boundary terms cancel.  The radius-\(3/2\) trace term is zero.  The
  remaining variation of the smooth weight and the polar Jacobian is bounded
  by a constant times the collar width; absolute continuity of the integrable
  weighted trace absorbs this after enlarging the constant.
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_polar_weighted_trace_estimate_of_radial_profile_bounds
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (Cprofile : ℝ) (hCprofile_ge_one : 1 ≤ Cprofile)
    (hCprofile : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ Cprofile)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ C : ℝ,
      Cprofile ≤ C ∧
        1 ≤ C ∧
          ∀ {η width : ℝ}
            (_hη_pos : 0 < η)
            (_hwidth_pos : 0 < width)
            (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
            (_hwidth_le : width ≤ η / C)
            (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
                (H := H) width),
            (∀ z : H,
              z ∈ euclideanSobolevUnitBallInnerTransitionCollar H width →
                fderiv ℝ χ.unitCutoff z v =
                  (deriv Real.smoothTransition
                      (((1 : ℝ) - width / 2 - ‖z‖) / (width / 4)) *
                    (-(1 : ℝ) / (width / 4))) *
                    inner ℝ ((‖z‖)⁻¹ • z) v) →
            (∀ z : H,
              z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width →
                fderiv ℝ χ.annulusCutoff z v =
                  (deriv Real.smoothTransition
                      ((‖z‖ - ((1 : ℝ) + width / 2)) / (width / 4)) *
                    ((1 : ℝ) / (width / 4))) *
                    inner ℝ ((‖z‖)⁻¹ • z) v) →
            (∀ z : H,
              z ∈ euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width →
                fderiv ℝ χ.annulusCutoff z v =
                  (deriv Real.smoothTransition
                      ((((3 / 2 : ℝ) - width / 2) - ‖z‖) /
                        (width / 4)) *
                    (-(1 : ℝ) / (width / 4))) *
                    inner ℝ ((‖z‖)⁻¹ • z) v) →
            (∀ z : H,
              z ∈ euclideanSobolevUnitBallInnerTransitionCollar H width →
                ‖fderiv ℝ χ.unitCutoff z v‖ ≤
                  Cprofile * (4 / width) * ‖v‖) →
            (∀ z : H,
              z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width →
                ‖fderiv ℝ χ.annulusCutoff z v‖ ≤
                  Cprofile * (4 / width) * ‖v‖) →
            (∀ z : H,
              z ∈ euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width →
                ‖fderiv ℝ χ.annulusCutoff z v‖ ≤
                  Cprofile * (4 / width) * ‖v‖) →
            sphereInnerL1TraceError (H := H) 1 u₀ τ width +
                sphereOuterL1TraceError (H := H) 1 u₁ τ width +
                  sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                    u₁ (fun _x : H ↦ 0) width ≤
              ENNReal.ofReal (η / C) →
              ‖(∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
                  ((fderiv ℝ χ.unitCutoff z v) * φ z) • u₀ z
                  ∂MeasureTheory.volume) +
                ∫ z in
                  euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
                    euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
                  ((fderiv ℝ χ.annulusCutoff z v) * φ z) • u₁ z
                  ∂MeasureTheory.volume‖ ≤ η := by
  obtain ⟨C, hCprofile_le, hC_ge_one, horiented⟩ :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_explicit_oriented_radial_pairing_bound
      (u₀ := u₀) (u₁ := u₁) (τ := τ)
      hu₀_aesm hu₁_aesm
      Cprofile hCprofile_ge_one hCprofile φ v _hτ_weight
  refine ⟨C, hCprofile_le, hC_ge_one, ?_⟩
  intro η width hη_pos hwidth_pos hwidth_le_quarter hwidth_le χ
    hunit_formula hannulus_inner_formula hannulus_outer_formula
    _hunit_bound _hannulus_inner_bound _hannulus_outer_bound htrace
  have hunit_eq :
      (∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
          ((fderiv ℝ χ.unitCutoff z v) * φ z) • u₀ z
          ∂MeasureTheory.volume) =
        ∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
          euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
            width (φ : H → ℝ) v z • u₀ z
          ∂MeasureTheory.volume := by
    refine setIntegral_congr_fun
      (euclideanSobolevUnitBallInnerTransitionCollar_isOpen
        (H := H) width).measurableSet ?_
    intro z hz
    change (((fderiv ℝ χ.unitCutoff z) v * φ z) • u₀ z) =
      euclideanSobolevUnitBallInnerOrientedRadialPairingWeight
        width (φ : H → ℝ) v z • u₀ z
    rw [hunit_formula z hz]
    simp [euclideanSobolevUnitBallInnerOrientedRadialPairingWeight,
      mul_assoc]
  have hannulus_eq :
      (∫ z in
          euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
            euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
          ((fderiv ℝ χ.annulusCutoff z v) * φ z) • u₁ z
          ∂MeasureTheory.volume) =
        ∫ z in
          euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
            euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
          euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
            width (φ : H → ℝ) v z • u₁ z
          ∂MeasureTheory.volume := by
    refine setIntegral_congr_fun
      ((euclideanSobolevUnitBallAnnulusInnerTransitionCollar_isOpen
          (H := H) width).measurableSet.union
        (euclideanSobolevUnitBallAnnulusOuterTransitionCollar_isOpen
          (H := H) width).measurableSet) ?_
    intro z hz
    rcases hz with hz_inner | hz_outer
    · change (((fderiv ℝ χ.annulusCutoff z) v * φ z) • u₁ z) =
        euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
          width (φ : H → ℝ) v z • u₁ z
      rw [hannulus_inner_formula z hz_inner]
      simp [euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight,
        euclideanSobolevUnitBallAnnulusInnerOrientedRadialPairingWeight,
        hz_inner, mul_assoc]
    · have hz_not_inner :
          z ∉ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width := by
        intro hz_inner
        exact
          (euclideanSobolevUnitBallAnnulusTransitionCollars_disjoint
            (H := H) hwidth_le_quarter).le_bot ⟨hz_inner, hz_outer⟩
      change (((fderiv ℝ χ.annulusCutoff z) v * φ z) • u₁ z) =
        euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight
          width (φ : H → ℝ) v z • u₁ z
      rw [hannulus_outer_formula z hz_outer]
      simp [euclideanSobolevUnitBallAnnulusOrientedRadialPairingWeight,
        euclideanSobolevUnitBallAnnulusOuterOrientedRadialPairingWeight,
        hz_not_inner, mul_assoc]
  rw [hunit_eq, hannulus_eq]
  exact
    horiented (η := η) (width := width) hη_pos hwidth_pos
      hwidth_le_quarter hwidth_le htrace

/--
%%handwave
name:
  The polar weighted trace estimate for radial collar pairings
statement:
  Fix a bound for the one-dimensional profile derivatives.  If a standard
  radial collar pair has cutoff derivatives bounded by this profile bound
  times \(1/\delta\) on each of the three transition collars, then a finite
  constant \(C\) controls its transition-collar pairing by the normalized
  \(L^1\)-trace errors and the collar width.
proof:
  Estimate the parts containing \(u-\tau\) by the three normalized trace
  errors and the assumed derivative bounds.  For the exact trace pieces, pass
  to polar coordinates.  The two unit-sphere pieces have opposite orientation
  and cancel in the limit, while the radius-\(3/2\) piece has zero trace.  The
  fixed smooth weight and the polar Jacobian vary continuously in the radial
  variable, and the weighted trace is integrable on the unit sphere, so
  absolute continuity and dominated convergence give an \(O(\delta)\) bound
  after increasing \(C\).
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_polar_weighted_trace_estimate_with_profile_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (Cprofile : ℝ) (hCprofile_ge_one : 1 ≤ Cprofile)
    (hCprofile : ∀ t ∈ Set.Icc (-(2 : ℝ)) 2,
      ‖deriv Real.smoothTransition t‖ ≤ Cprofile)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ C : ℝ,
      Cprofile ≤ C ∧
        1 ≤ C ∧
          ∀ {η width : ℝ}
            (_hη_pos : 0 < η)
            (_hwidth_pos : 0 < width)
            (_hwidth_le_quarter : width ≤ (1 / 4 : ℝ))
            (_hwidth_le : width ≤ η / C)
            (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
                (H := H) width),
            (∀ z : H,
              z ∈ euclideanSobolevUnitBallInnerTransitionCollar H width →
                ‖fderiv ℝ χ.unitCutoff z v‖ ≤
                  Cprofile * (4 / width) * ‖v‖) →
            (∀ z : H,
              z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width →
                ‖fderiv ℝ χ.annulusCutoff z v‖ ≤
                  Cprofile * (4 / width) * ‖v‖) →
            (∀ z : H,
              z ∈ euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width →
                ‖fderiv ℝ χ.annulusCutoff z v‖ ≤
                  Cprofile * (4 / width) * ‖v‖) →
            sphereInnerL1TraceError (H := H) 1 u₀ τ width +
                sphereOuterL1TraceError (H := H) 1 u₁ τ width +
                  sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                    u₁ (fun _x : H ↦ 0) width ≤
              ENNReal.ofReal (η / C) →
              ‖(∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
                  ((fderiv ℝ χ.unitCutoff z v) * φ z) • u₀ z
                  ∂MeasureTheory.volume) +
                ∫ z in
                  euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
                    euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
                  ((fderiv ℝ χ.annulusCutoff z v) * φ z) • u₁ z
                  ∂MeasureTheory.volume‖ ≤ η := by
  obtain ⟨C, hCprofile_le, hC_ge_one, hpolar⟩ :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_polar_weighted_trace_estimate_of_radial_profile_bounds
      (u₀ := u₀) (u₁ := u₁) (τ := τ)
      hu₀_aesm hu₁_aesm
      Cprofile hCprofile_ge_one hCprofile φ v _hτ_weight
  refine ⟨C, hCprofile_le, hC_ge_one, ?_⟩
  intro η width hη_pos hwidth_pos hwidth_le_quarter hwidth_le χ
    hunit_bound hannulus_inner_bound hannulus_outer_bound htrace
  exact
    hpolar (η := η) (width := width) hη_pos hwidth_pos
      hwidth_le_quarter hwidth_le χ
      (fun z hz ↦
        χ.unitCutoff_fderiv_apply_eq_oriented_profile_of_inner_transition
          hwidth_le_quarter hz)
      (fun z hz ↦
        χ.annulusCutoff_fderiv_apply_eq_oriented_profile_of_inner_transition
          hwidth_pos hwidth_le_quarter hz)
      (fun z hz ↦
        χ.annulusCutoff_fderiv_apply_eq_oriented_profile_of_outer_transition
          hwidth_pos hwidth_le_quarter hz)
      hunit_bound hannulus_inner_bound hannulus_outer_bound htrace

/--
%%handwave
name:
  Standard radial collars satisfy the weighted trace estimate
statement:
  For a fixed smooth test function and fixed direction, there is a finite
  constant \(C\ge 1\) such that every standard smooth radial collar pair of
  width \(\delta\le 1/4\) has transition-collar pairing bounded by \(\eta\),
  provided \(\delta\le\eta/C\) and the sum of the three normalized
  \(L^1\)-trace errors is at most \(\eta/C\).
proof:
  Use the explicit one-dimensional formulas for the standard collar profiles.
  On each transition collar, the radial derivative is the derivative of the
  basic smooth transition profile multiplied by \(1/\delta\) and by the radial
  normal component.  Insert and subtract the prescribed traces.  The resulting
  error terms are controlled by the three normalized trace errors.  The exact
  trace terms cancel after writing the collars in polar coordinates: the
  inside and outside unit-sphere terms have opposite orientations, and the
  radius-\(3/2\) term has zero trace.  The remaining variation of the fixed
  smooth weight and of the polar Jacobian is bounded by a constant times
  \(\delta\), and is absorbed by the small-width hypothesis.
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_standard_radial_collar_pairing_bound_with_constant
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ C : ℝ,
      1 ≤ C ∧
        ∀ {η width : ℝ},
          0 < η →
          0 < width →
          width ≤ (1 / 4 : ℝ) →
          width ≤ η / C →
          ∀ (χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
              (H := H) width),
          sphereInnerL1TraceError (H := H) 1 u₀ τ width +
              sphereOuterL1TraceError (H := H) 1 u₁ τ width +
                sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                  u₁ (fun _x : H ↦ 0) width ≤
            ENNReal.ofReal (η / C) →
            ‖(∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
                ((fderiv ℝ χ.unitCutoff z v) * φ z) • u₀ z
                ∂MeasureTheory.volume) +
              ∫ z in
                euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
                  euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
                ((fderiv ℝ χ.annulusCutoff z v) * φ z) • u₁ z
                ∂MeasureTheory.volume‖ ≤ η := by
  obtain ⟨Cprofile, hCprofile_ge_one, hCprofile⟩ :=
    exists_smoothTransition_deriv_bound_Icc_neg_two_two
  obtain ⟨C, _hCprofile_le, hC_ge_one, hpolar⟩ :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_polar_weighted_trace_estimate_with_profile_bound
      (u₀ := u₀) (u₁ := u₁) (τ := τ)
      hu₀_aesm hu₁_aesm
      Cprofile hCprofile_ge_one hCprofile φ v _hτ_weight
  refine ⟨C, hC_ge_one, ?_⟩
  intro η width hη_pos hwidth_pos hwidth_le_quarter hwidth_le χ htrace
  have hunit_bound :
      ∀ z : H,
        z ∈ euclideanSobolevUnitBallInnerTransitionCollar H width →
          ‖fderiv ℝ χ.unitCutoff z v‖ ≤
            Cprofile * (4 / width) * ‖v‖ := by
    intro z hz
    exact
      χ.unitCutoff_fderiv_apply_norm_le_of_inner_transition
        hwidth_pos hwidth_le_quarter hCprofile_ge_one hCprofile hz
  have hannulus_inner_bound :
      ∀ z : H,
        z ∈ euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width →
          ‖fderiv ℝ χ.annulusCutoff z v‖ ≤
            Cprofile * (4 / width) * ‖v‖ := by
    intro z hz
    exact
      χ.annulusCutoff_fderiv_apply_norm_le_of_inner_transition
        hwidth_pos hwidth_le_quarter hCprofile_ge_one hCprofile hz
  have hannulus_outer_bound :
      ∀ z : H,
        z ∈ euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width →
          ‖fderiv ℝ χ.annulusCutoff z v‖ ≤
            Cprofile * (4 / width) * ‖v‖ := by
    intro z hz
    exact
      χ.annulusCutoff_fderiv_apply_norm_le_of_outer_transition
        hwidth_pos hwidth_le_quarter hCprofile_ge_one hCprofile hz
  exact
    hpolar (η := η) (width := width) hη_pos hwidth_pos
      hwidth_le_quarter hwidth_le χ hunit_bound
      hannulus_inner_bound hannulus_outer_bound htrace

/--
%%handwave
name:
  Radial collars satisfying the weighted trace estimate exist
statement:
  For a fixed smooth test function and fixed direction, there is a finite
  constant \(C\ge 1\) such that, whenever the sum of the three normalized
  \(L^1\)-trace errors is at most \(\eta/C\) and the collar width is at most
  \(\eta/C\), there is a smooth radial collar pair of that width whose
  transition-collar pairing is bounded by \(\eta\).
proof:
  Use the standard one-dimensional smooth transition profiles to build the
  collars.  Their derivatives are supported in the three boundary collars and
  are bounded by a fixed compact bound for the derivative of the basic
  transition function, scaled by \(1/\delta\).  Insert and subtract the common
  trace on the unit sphere and the zero trace on the sphere of radius \(3/2\).
  The normalized \(L^1\)-trace errors control the resulting error terms.  The
  exact trace terms cancel in polar coordinates: the two unit-sphere
  contributions have opposite orientations, and the outer \(3/2\)-sphere
  contribution has zero trace.  The variation of the fixed smooth weight and
  the radial volume factor across a collar is \(O(\delta)\), which is absorbed
  by the small-width hypothesis after increasing \(C\).
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_exists_radial_collar_pairing_bound_with_constant
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ C : ℝ,
      1 ≤ C ∧
        ∀ {η width : ℝ},
          0 < η →
          0 < width →
          width ≤ (1 / 4 : ℝ) →
          width ≤ η / C →
          sphereInnerL1TraceError (H := H) 1 u₀ τ width +
              sphereOuterL1TraceError (H := H) 1 u₁ τ width +
                sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                  u₁ (fun _x : H ↦ 0) width ≤
            ENNReal.ofReal (η / C) →
          ∃ χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
              (H := H) width,
            ‖(∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
                ((fderiv ℝ χ.unitCutoff z v) * φ z) • u₀ z
                ∂MeasureTheory.volume) +
              ∫ z in
                euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
                  euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
                ((fderiv ℝ χ.annulusCutoff z v) * φ z) • u₁ z
                ∂MeasureTheory.volume‖ ≤ η := by
  obtain ⟨C, hC_ge_one, hC_pairing⟩ :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_standard_radial_collar_pairing_bound_with_constant
      (u₀ := u₀) (u₁ := u₁) (τ := τ)
      hu₀_aesm hu₁_aesm φ v _hτ_weight
  refine ⟨C, hC_ge_one, ?_⟩
  intro η width hη_pos hwidth_pos hwidth_le_quarter hwidth_le htrace
  obtain ⟨χ⟩ :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_exists_radial_collar_cutoff_pair
      (H := H) hwidth_pos hwidth_le_quarter
  refine ⟨χ, ?_⟩
  exact
    hC_pairing (η := η) (width := width) hη_pos hwidth_pos
      hwidth_le_quarter hwidth_le χ htrace

/--
%%handwave
name:
  A localized weighted trace constant controls radial collar pairings
statement:
  For a fixed smooth test function and fixed direction, there is a finite
  constant \(C\ge 1\) such that, whenever the sum of the three normalized
  \(L^1\)-trace errors is at most \(\eta/C\) and the collar width is at most
  \(\eta/C\), the radial transition-collar part of the cutoff-derivative
  pairing is bounded by \(\eta\).
proof:
  Apply
  [the existence of radial collars satisfying the weighted trace
  estimate](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_annulus_l1_trace_glue_exists_radial_collar_pairing_bound_with_constant).
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_localized_radial_collar_pairing_bound_with_constant
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ C : ℝ,
      1 ≤ C ∧
        ∀ {η width : ℝ},
          0 < η →
          0 < width →
          width ≤ (1 / 4 : ℝ) →
          width ≤ η / C →
          sphereInnerL1TraceError (H := H) 1 u₀ τ width +
              sphereOuterL1TraceError (H := H) 1 u₁ τ width +
                sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                  u₁ (fun _x : H ↦ 0) width ≤
            ENNReal.ofReal (η / C) →
          ∃ χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
              (H := H) width,
            ‖(∫ z in euclideanSobolevUnitBallInnerTransitionCollar H width,
                ((fderiv ℝ χ.unitCutoff z v) * φ z) • u₀ z
                ∂MeasureTheory.volume) +
              ∫ z in
                euclideanSobolevUnitBallAnnulusInnerTransitionCollar H width ∪
                  euclideanSobolevUnitBallAnnulusOuterTransitionCollar H width,
                ((fderiv ℝ χ.annulusCutoff z v) * φ z) • u₁ z
                ∂MeasureTheory.volume‖ ≤ η := by
  exact
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_exists_radial_collar_pairing_bound_with_constant
      (u₀ := u₀) (u₁ := u₁) (τ := τ)
      hu₀_aesm hu₁_aesm φ v hτ_weight

/--
%%handwave
name:
  A finite weighted trace constant controls radial collar pairings
statement:
  For a fixed smooth test function and fixed direction, there is a finite
  constant \(C\ge 1\) such that, whenever the sum of the three normalized
  \(L^1\)-trace errors is at most \(\eta/C\) and the collar width is at most
  \(\eta/C\), the concrete radial collar cutoffs of the corresponding width
  have cutoff-derivative pairing bounded by \(\eta\).
proof:
  Apply
  [the transition-collar pairing bound under the same trace-error
  hypothesis](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_annulus_l1_trace_glue_localized_radial_collar_pairing_bound_with_constant).
  The cutoff derivatives vanish outside the three transition collars, so the
  full ball and annulus integrals are exactly the localized collar integrals.
-/
private theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_radial_collar_pairing_bound_with_constant
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ C : ℝ,
      1 ≤ C ∧
        ∀ {η width : ℝ},
          0 < η →
          0 < width →
          width ≤ (1 / 4 : ℝ) →
          width ≤ η / C →
          sphereInnerL1TraceError (H := H) 1 u₀ τ width +
              sphereOuterL1TraceError (H := H) 1 u₁ τ width +
                sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                  u₁ (fun _x : H ↦ 0) width ≤
            ENNReal.ofReal (η / C) →
          ∃ χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
              (H := H) width,
            ‖(∫ z in Metric.ball (0 : H) 1,
                ((fderiv ℝ χ.unitCutoff z v) * φ z) • u₀ z
                ∂MeasureTheory.volume) +
              ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
                ((fderiv ℝ χ.annulusCutoff z v) * φ z) • u₁ z
                ∂MeasureTheory.volume‖ ≤ η := by
  obtain ⟨C, hC_ge_one, hC_pairing⟩ :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_localized_radial_collar_pairing_bound_with_constant
      (u₀ := u₀) (u₁ := u₁) (τ := τ)
      hu₀_aesm hu₁_aesm φ v hτ_weight
  refine ⟨C, hC_ge_one, ?_⟩
  intro η width hη_pos hwidth_pos hwidth_le_quarter hwidth_le htrace
  obtain ⟨χ, hχ⟩ :=
    hC_pairing hη_pos hwidth_pos hwidth_le_quarter hwidth_le htrace
  refine ⟨χ, ?_⟩
  have hlocalize :=
    χ.derivative_pairing_sum_eq_transition_collar_pairing_sum
      u₀ u₁ (φ : H → ℝ) v
  rw [hlocalize]
  exact hχ

/--
%%handwave
name:
  Small trace errors control the derivative pairing for radial collar cutoffs
statement:
  For every positive tolerance \(\eta\), fixed smooth test function, and fixed
  direction, there is a smaller positive trace tolerance \(\eta'\le\eta\) such
  that if the total normalized \(L^1\)-trace error in the three boundary
  collars is at most \(\eta'\), then the concrete radial collar cutoffs of that
  width have cutoff-derivative pairing bounded by \(\eta\).
proof:
  Bound the smooth test and the fixed direction on the compact collars.  Use
  the one-dimensional radial profile formulas for the derivatives.  Insert and
  subtract the common trace on the unit sphere and the zero trace at radius
  \(3/2\).  The unit-sphere trace terms cancel because the inner and outer
  radial profiles have opposite orientations and matching total variation.  The
  remaining terms are bounded by the three normalized trace errors, multiplied
  by the fixed bound.  The nonconstant radial variation of the smooth test is
  bounded by the same constant times the collar width; choose \(\eta'\) small
  enough to absorb both effects.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_radial_collar_pairing_bound_of_trace_errors_small
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v)
    {η : ℝ} (hη_pos : 0 < η) :
    ∃ ηtrace : ℝ,
      0 < ηtrace ∧
        ηtrace ≤ η ∧
          ∀ {width : ℝ},
            0 < width →
            width ≤ ηtrace →
            width ≤ (1 / 4 : ℝ) →
            sphereInnerL1TraceError (H := H) 1 u₀ τ width +
                sphereOuterL1TraceError (H := H) 1 u₁ τ width +
                  sphereInnerL1TraceError (H := H) (3 / 2 : ℝ)
                    u₁ (fun _x : H ↦ 0) width ≤
              ENNReal.ofReal ηtrace →
            ∃ χ : EuclideanSobolevUnitBallAnnulusRadialCollarCutoffPair
                (H := H) width,
              ‖(∫ z in Metric.ball (0 : H) 1,
                  ((fderiv ℝ χ.unitCutoff z v) * φ z) • u₀ z
                  ∂MeasureTheory.volume) +
                ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
                  ((fderiv ℝ χ.annulusCutoff z v) * φ z) • u₁ z
                  ∂MeasureTheory.volume‖ ≤ η := by
  obtain ⟨C, hC_ge_one, hC_pairing⟩ :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_radial_collar_pairing_bound_with_constant
      (u₀ := u₀) (u₁ := u₁) (τ := τ)
      hu₀_aesm hu₁_aesm φ v hτ_weight
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC_ge_one
  refine ⟨η / C, ?_, ?_, ?_⟩
  · exact div_pos hη_pos hC_pos
  · have hmul : η ≤ η * C := by
      calc
        η = η * 1 := by ring
        _ ≤ η * C := mul_le_mul_of_nonneg_left hC_ge_one hη_pos.le
    exact (div_le_iff₀ hC_pos).2 hmul
  · intro width hwidth_pos hwidth_le_trace hwidth_le_quarter htrace
    exact hC_pairing hη_pos hwidth_pos hwidth_le_quarter
      (η := η) (width := width) hwidth_le_trace htrace

/--
%%handwave
name:
  Radial trace-controlled scalar collar cutoffs exist
statement:
  Given a positive tolerance \(\eta\), matching \(L^1\)-traces on the unit
  sphere, and zero \(L^1\)-trace on the sphere of radius \(3/2\), there are a
  width \(0<\delta\le\eta\) and smooth scalar cutoffs supported in the unit
  ball and in the annulus \(1<\|x\|<3/2\).  The cutoffs are bounded by one,
  equal to one away from the boundary collars of width \(\delta\), have zero
  derivative on those cores, and the sum of their derivative-collar pairings
  against the two functions is bounded by \(\eta\).
proof:
  Choose \(\delta\) so that the normalized \(L^1\)-trace errors in the inner,
  outer-unit, and radius-\(3/2\) collars are small after multiplication by the
  bounded smooth test and the fixed direction.  Take one-dimensional smooth
  radial profiles with derivative supported in these collars and total
  variation one.  The two unit-sphere collar contributions approach the same
  boundary pairing with opposite signs, while the radius-\(3/2\) contribution
  is small because the annular function has zero trace there.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_trace_controlled_radial_collar_cutoffs
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v)
    {η : ℝ} (_hη_pos : 0 < η) :
    ∃ (width : ℝ) (unitCutoff annulusCutoff : H → ℝ),
      0 < width ∧
      width ≤ η ∧
      ContDiff ℝ ∞ unitCutoff ∧
      ContDiff ℝ ∞ annulusCutoff ∧
      tsupport unitCutoff ⊆ Metric.ball (0 : H) 1 ∧
      tsupport annulusCutoff ⊆
        euclideanSobolevUnitBallReflectionAnnulus H ∧
      IsCompact (tsupport unitCutoff) ∧
      IsCompact (tsupport annulusCutoff) ∧
      (∀ x : H, ‖unitCutoff x‖ ≤ (1 : ℝ)) ∧
      (∀ x : H, ‖annulusCutoff x‖ ≤ (1 : ℝ)) ∧
      (∀ x : H, ‖x‖ ≤ 1 - width →
        unitCutoff x = 1) ∧
      (∀ x : H,
        1 + width ≤ ‖x‖ → ‖x‖ ≤ (3 / 2 : ℝ) - width →
          annulusCutoff x = 1) ∧
      (∀ x : H, ‖x‖ ≤ 1 - width →
        fderiv ℝ unitCutoff x = 0) ∧
      (∀ x : H,
        1 + width ≤ ‖x‖ → ‖x‖ ≤ (3 / 2 : ℝ) - width →
          fderiv ℝ annulusCutoff x = 0) ∧
      ‖(∫ z in Metric.ball (0 : H) 1,
          ((fderiv ℝ unitCutoff z v) * φ z) • u₀ z
          ∂MeasureTheory.volume) +
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          ((fderiv ℝ annulusCutoff z v) * φ z) • u₁ z
          ∂MeasureTheory.volume‖ ≤ η := by
  obtain ⟨ηtrace, hηtrace_pos, hηtrace_le_eta, hpairing_of_trace⟩ :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_radial_collar_pairing_bound_of_trace_errors_small
      (u₀ := u₀) (u₁ := u₁) (τ := τ)
      hu₀_aesm hu₁_aesm φ v hτ_weight _hη_pos
  obtain
      ⟨width, hwidth_pos, hwidth_le_trace, hwidth_le_quarter,
        htrace_error⟩ :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_exists_width_trace_errors_small
      _hinner₀ _hinner₁ _houter hηtrace_pos
  obtain ⟨χ, hpairing⟩ :=
    hpairing_of_trace hwidth_pos hwidth_le_trace hwidth_le_quarter htrace_error
  have hwidth_le_eta : width ≤ η :=
    hwidth_le_trace.trans hηtrace_le_eta
  exact
    ⟨width, χ.unitCutoff, χ.annulusCutoff,
      hwidth_pos, hwidth_le_eta, χ.unitCutoff_smooth,
      χ.annulusCutoff_smooth, χ.unitCutoff_tsupport_subset,
      χ.annulusCutoff_tsupport_subset, χ.unitCutoff_compact_support,
      χ.annulusCutoff_compact_support, χ.unitCutoff_norm_le_one,
      χ.annulusCutoff_norm_le_one, χ.unitCutoff_eq_one_on_core,
      χ.annulusCutoff_eq_one_on_core, χ.unitCutoff_fderiv_eq_zero_on_core,
      χ.annulusCutoff_fderiv_eq_zero_on_core, hpairing⟩

/--
%%handwave
name:
  One trace-adapted scalar collar cutoff pair of functions exists
statement:
  Given a positive tolerance \(\eta\), matching \(L^1\)-traces on the unit
  sphere, and zero \(L^1\)-trace on the sphere of radius \(3/2\), there are a
  positive width \(\delta\le\eta\) and two smooth scalar cutoff functions,
  supported in the unit ball and in the annulus, equal to one on the compact
  cores of width \(\delta\), bounded by one, and with cutoff-derivative
  collar term bounded in absolute value by \(\eta\).
proof:
  Apply [the radial collar cutoff construction with trace-controlled
  derivative pairing](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_annulus_l1_trace_glue_trace_controlled_radial_collar_cutoffs).
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_trace_controlled_scalar_collar_cutoff_step_functions
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v)
    {η : ℝ} (_hη_pos : 0 < η) :
    ∃ (width : ℝ) (unitCutoff annulusCutoff : H → ℝ),
      0 < width ∧
      width ≤ η ∧
      ContDiff ℝ ∞ unitCutoff ∧
      ContDiff ℝ ∞ annulusCutoff ∧
      tsupport unitCutoff ⊆ Metric.ball (0 : H) 1 ∧
      tsupport annulusCutoff ⊆
        euclideanSobolevUnitBallReflectionAnnulus H ∧
      IsCompact (tsupport unitCutoff) ∧
      IsCompact (tsupport annulusCutoff) ∧
      (∀ x : H, ‖unitCutoff x‖ ≤ (1 : ℝ)) ∧
      (∀ x : H, ‖annulusCutoff x‖ ≤ (1 : ℝ)) ∧
      (∀ x : H, ‖x‖ ≤ 1 - width →
        unitCutoff x = 1) ∧
      (∀ x : H,
        1 + width ≤ ‖x‖ → ‖x‖ ≤ (3 / 2 : ℝ) - width →
          annulusCutoff x = 1) ∧
      (∀ x : H, ‖x‖ ≤ 1 - width →
        fderiv ℝ unitCutoff x = 0) ∧
      (∀ x : H,
        1 + width ≤ ‖x‖ → ‖x‖ ≤ (3 / 2 : ℝ) - width →
          fderiv ℝ annulusCutoff x = 0) ∧
      ‖(∫ z in Metric.ball (0 : H) 1,
          ((fderiv ℝ unitCutoff z v) * φ z) • u₀ z
          ∂MeasureTheory.volume) +
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          ((fderiv ℝ annulusCutoff z v) * φ z) • u₁ z
          ∂MeasureTheory.volume‖ ≤ η := by
  exact
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_trace_controlled_radial_collar_cutoffs
      hu₀_aesm hu₁_aesm _hinner₀ _hinner₁ _houter φ v hτ_weight _hη_pos

/--
%%handwave
name:
  Scalar collar cutoff geometry with trace cancellation exists
statement:
  Suppose the two local functions have matching \(L^1\)-traces on the unit
  sphere and the annular function has zero \(L^1\)-trace on the sphere of
  radius \(3/2\).  For every smooth compactly supported ambient test function
  and constant direction, there are scalar smooth collar cutoffs satisfying
  the usual support, core, and boundedness conditions, and their
  cutoff-derivative collar terms tend to zero.
proof:
  Construct radial one-dimensional transition profiles in collars of widths
  \(\varepsilon_n\downarrow0\), with normalized derivatives.  The matching
  \(L^1\)-traces cancel the two unit-sphere terms, and the zero trace at
  radius \(3/2\) kills the outer collar term.  The profiles are then smoothed
  within the collars without changing the normalized limits.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_trace_controlled_scalar_collar_cutoff_geometry
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ χ : EuclideanSobolevUnitBallAnnulusL1TraceGlueScalarCutoffGeometry
        (H := H),
      Filter.Tendsto
        (fun n : ℕ ↦
          (∫ z in Metric.ball (0 : H) 1,
            ((fderiv ℝ (χ.unitCutoff n) z v) * φ z) • u₀ z
            ∂MeasureTheory.volume) +
          ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
            ((fderiv ℝ (χ.annulusCutoff n) z v) * φ z) • u₁ z
            ∂MeasureTheory.volume)
        Filter.atTop (𝓝 (0 : ℝ)) := by
  classical
  let η : ℕ → ℝ := fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹
  have hη_pos : ∀ n : ℕ, 0 < η n := by
    intro n
    dsimp [η]
    positivity
  have hstep_exists :
      ∀ n : ℕ, ∃ (width : ℝ) (unitCutoff annulusCutoff : H → ℝ),
        0 < width ∧
        width ≤ η n ∧
        ContDiff ℝ ∞ unitCutoff ∧
        ContDiff ℝ ∞ annulusCutoff ∧
        tsupport unitCutoff ⊆ Metric.ball (0 : H) 1 ∧
        tsupport annulusCutoff ⊆
          euclideanSobolevUnitBallReflectionAnnulus H ∧
        IsCompact (tsupport unitCutoff) ∧
        IsCompact (tsupport annulusCutoff) ∧
        (∀ x : H, ‖unitCutoff x‖ ≤ (1 : ℝ)) ∧
        (∀ x : H, ‖annulusCutoff x‖ ≤ (1 : ℝ)) ∧
        (∀ x : H, ‖x‖ ≤ 1 - width →
          unitCutoff x = 1) ∧
        (∀ x : H,
          1 + width ≤ ‖x‖ → ‖x‖ ≤ (3 / 2 : ℝ) - width →
            annulusCutoff x = 1) ∧
        (∀ x : H, ‖x‖ ≤ 1 - width →
          fderiv ℝ unitCutoff x = 0) ∧
        (∀ x : H,
          1 + width ≤ ‖x‖ → ‖x‖ ≤ (3 / 2 : ℝ) - width →
            fderiv ℝ annulusCutoff x = 0) ∧
        ‖(∫ z in Metric.ball (0 : H) 1,
            ((fderiv ℝ unitCutoff z v) * φ z) • u₀ z
            ∂MeasureTheory.volume) +
          ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
            ((fderiv ℝ annulusCutoff z v) * φ z) • u₁ z
            ∂MeasureTheory.volume‖ ≤ η n := by
    intro n
    exact
      euclideanSobolev_unit_ball_annulus_l1_trace_glue_trace_controlled_scalar_collar_cutoff_step_functions
        hu₀_aesm hu₁_aesm _hinner₀ _hinner₁ _houter φ v hτ_weight (hη_pos n)
  choose width unitCutoff annulusCutoff hstep_spec using hstep_exists
  have hstep_width_pos : ∀ n : ℕ, 0 < width n := by
    intro n
    rcases hstep_spec n with ⟨h, _⟩
    exact h
  have hstep_width_le : ∀ n : ℕ, width n ≤ η n := by
    intro n
    rcases hstep_spec n with ⟨_, h, _⟩
    exact h
  have hstep_unit_smooth :
      ∀ n : ℕ, ContDiff ℝ ∞ (unitCutoff n) := by
    intro n
    rcases hstep_spec n with ⟨_, _, h, _⟩
    exact h
  have hstep_annulus_smooth :
      ∀ n : ℕ, ContDiff ℝ ∞ (annulusCutoff n) := by
    intro n
    rcases hstep_spec n with ⟨_, _, _, h, _⟩
    exact h
  have hstep_unit_support :
      ∀ n : ℕ, tsupport (unitCutoff n) ⊆ Metric.ball (0 : H) 1 := by
    intro n
    rcases hstep_spec n with ⟨_, _, _, _, h, _⟩
    exact h
  have hstep_annulus_support :
      ∀ n : ℕ, tsupport (annulusCutoff n) ⊆
        euclideanSobolevUnitBallReflectionAnnulus H := by
    intro n
    rcases hstep_spec n with ⟨_, _, _, _, _, h, _⟩
    exact h
  have hstep_unit_compact :
      ∀ n : ℕ, IsCompact (tsupport (unitCutoff n)) := by
    intro n
    rcases hstep_spec n with ⟨_, _, _, _, _, _, h, _⟩
    exact h
  have hstep_annulus_compact :
      ∀ n : ℕ, IsCompact (tsupport (annulusCutoff n)) := by
    intro n
    rcases hstep_spec n with ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  have hstep_unit_norm :
      ∀ n : ℕ, ∀ x : H, ‖unitCutoff n x‖ ≤ (1 : ℝ) := by
    intro n
    rcases hstep_spec n with ⟨_, _, _, _, _, _, _, _, h, _⟩
    exact h
  have hstep_annulus_norm :
      ∀ n : ℕ, ∀ x : H, ‖annulusCutoff n x‖ ≤ (1 : ℝ) := by
    intro n
    rcases hstep_spec n with ⟨_, _, _, _, _, _, _, _, _, h, _⟩
    exact h
  have hstep_unit_core :
      ∀ n : ℕ, ∀ x : H, ‖x‖ ≤ 1 - width n →
        unitCutoff n x = 1 := by
    intro n
    rcases hstep_spec n with ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩
    exact h
  have hstep_annulus_core :
      ∀ n : ℕ, ∀ x : H,
        1 + width n ≤ ‖x‖ → ‖x‖ ≤ (3 / 2 : ℝ) - width n →
          annulusCutoff n x = 1 := by
    intro n
    rcases hstep_spec n with
      ⟨_, _, _, _, _, _, _, _, _, _, _, h, _⟩
    exact h
  have hstep_unit_fderiv :
      ∀ n : ℕ, ∀ x : H, ‖x‖ ≤ 1 - width n →
        fderiv ℝ (unitCutoff n) x = 0 := by
    intro n
    rcases hstep_spec n with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
    exact h
  have hstep_annulus_fderiv :
      ∀ n : ℕ, ∀ x : H,
        1 + width n ≤ ‖x‖ → ‖x‖ ≤ (3 / 2 : ℝ) - width n →
          fderiv ℝ (annulusCutoff n) x = 0 := by
    intro n
    rcases hstep_spec n with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
    exact h
  have hstep_trace :
      ∀ n : ℕ,
        ‖(∫ z in Metric.ball (0 : H) 1,
            ((fderiv ℝ (unitCutoff n) z v) * φ z) • u₀ z
            ∂MeasureTheory.volume) +
          ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
            ((fderiv ℝ (annulusCutoff n) z v) * φ z) • u₁ z
            ∂MeasureTheory.volume‖ ≤ η n := by
    intro n
    rcases hstep_spec n with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩
    exact h
  let χ : EuclideanSobolevUnitBallAnnulusL1TraceGlueScalarCutoffGeometry
      (H := H) :=
    { unitCutoff := unitCutoff
      annulusCutoff := annulusCutoff
      unitCutoff_smooth := hstep_unit_smooth
      annulusCutoff_smooth := hstep_annulus_smooth
      unitCutoff_tsupport_subset := hstep_unit_support
      annulusCutoff_tsupport_subset := hstep_annulus_support
      unitCutoff_compact_support := hstep_unit_compact
      annulusCutoff_compact_support := hstep_annulus_compact
      unitCutoff_norm_le_one := hstep_unit_norm
      annulusCutoff_norm_le_one := hstep_annulus_norm
      width := width
      width_pos := hstep_width_pos
      width_tendsto_zero := by
        have hη_tendsto :
            Filter.Tendsto η Filter.atTop (𝓝 (0 : ℝ)) := by
          simpa [η, one_div] using
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        exact
          squeeze_zero
            (fun n : ℕ ↦ (hstep_width_pos n).le)
            hstep_width_le
            hη_tendsto
      unitCutoff_eq_one_on_core := hstep_unit_core
      annulusCutoff_eq_one_on_core := hstep_annulus_core
      unitCutoff_fderiv_eq_zero_on_core := hstep_unit_fderiv
      annulusCutoff_fderiv_eq_zero_on_core := hstep_annulus_fderiv }
  refine ⟨χ, ?_⟩
  let T : ℕ → ℝ := fun n : ℕ ↦
    (∫ z in Metric.ball (0 : H) 1,
      ((fderiv ℝ (unitCutoff n) z v) * φ z) • u₀ z
      ∂MeasureTheory.volume) +
    ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
      ((fderiv ℝ (annulusCutoff n) z v) * φ z) • u₁ z
      ∂MeasureTheory.volume
  have hη_tendsto :
      Filter.Tendsto η Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [η, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hnorm_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ ‖T n‖) Filter.atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero
      (fun n : ℕ ↦ norm_nonneg (T n))
      (fun n : ℕ ↦ by
        simpa [T] using hstep_trace n)
      hη_tendsto
  have hT_tendsto :
      Filter.Tendsto T Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_tendsto
  simpa [χ, T] using hT_tendsto

/--
%%handwave
name:
  Scalar collar cutoffs with trace cancellation exist
statement:
  Suppose the two local functions have matching \(L^1\)-traces on the unit
  sphere and the annular function has zero \(L^1\)-trace on the sphere of
  radius \(3/2\).  For every smooth compactly supported ambient test function
  and constant direction, there are scalar smooth collar cutoffs, supported
  in the unit ball and annulus, equal to one on compact cores and bounded by
  one, whose cutoff-derivative collar terms tend to zero.
proof:
  Construct one-dimensional transition profiles on the three collars, with
  widths tending to zero and normalized derivatives.  Pull them back to the
  Euclidean regions by a smooth collar coordinate.  The normalized
  \(L^1\)-trace convergence gives cancellation of the two unit-sphere
  contributions and vanishing of the outer contribution.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_trace_controlled_scalar_collar_cutoff_data
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    Nonempty
      (EuclideanSobolevUnitBallAnnulusL1TraceGlueTraceControlledScalarCutoffData
        (u₀ := u₀) (u₁ := u₁) (τ := τ) φ v) := by
  rcases
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_trace_controlled_scalar_collar_cutoff_geometry
      hu₀_aesm hu₁_aesm _hinner₀ _hinner₁ _houter φ v hτ_weight with
    ⟨χ, hχ_trace⟩
  exact
    ⟨{ toEuclideanSobolevUnitBallAnnulusL1TraceGlueScalarCutoffGeometry :=
          χ
       trace_collar_terms_tendsto_zero := hχ_trace }⟩

/--
%%handwave
name:
  Smooth collar cutoff data with trace cancellation exists
statement:
  Suppose the two local functions have matching \(L^1\)-traces on the unit
  sphere and the annular function has zero \(L^1\)-trace on the sphere of
  radius \(3/2\).  For every smooth compactly supported ambient test function
  and constant direction, there is a smooth collar cutoff family for which
  the sum of the cutoff-derivative collar terms tends to zero.
proof:
  Choose radial cutoff profiles with transition width
  \(\varepsilon_n\downarrow0\), equal to one on the compact cores and with
  normalized radial derivative in the collars.  The matching \(L^1\)-traces
  make the two unit-sphere contributions converge to opposite copies of the
  same boundary integral.  The zero outer trace makes the contribution from
  the sphere of radius \(3/2\) vanish.  Smooth the profiles while preserving
  these collar limits.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_trace_controlled_smooth_collar_cutoff_data
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    ∃ tests : EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests φ,
      Filter.Tendsto
        (fun n : ℕ ↦
          (∫ z in Metric.ball (0 : H) 1,
            ((fderiv ℝ (tests.unitCutoff n) z v) * φ z) • u₀ z
            ∂MeasureTheory.volume) +
          ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
            ((fderiv ℝ (tests.annulusCutoff n) z v) * φ z) • u₁ z
            ∂MeasureTheory.volume)
        Filter.atTop (𝓝 (0 : ℝ)) := by
  rcases
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_trace_controlled_scalar_collar_cutoff_data
      hu₀_aesm hu₁_aesm _hinner₀ _hinner₁ _houter φ v hτ_weight with
    ⟨χ⟩
  let unitTest :
      ℕ → SmoothCompactlySupportedManifoldCoordinateFunction
        (Metric.ball (0 : H) 1) := fun n ↦
    { toFun := fun z : H ↦ χ.unitCutoff n z * (φ : H → ℝ) z
      smooth := (χ.unitCutoff_smooth n).mul φ.smooth
      support_subset := by
        exact (tsupport_mul_subset_left).trans
          (χ.unitCutoff_tsupport_subset n)
      compact_support := by
        exact (χ.unitCutoff_compact_support n).of_isClosed_subset
          (isClosed_tsupport _) tsupport_mul_subset_left }
  let annulusTest :
      ℕ → SmoothCompactlySupportedManifoldCoordinateFunction
        (euclideanSobolevUnitBallReflectionAnnulus H) := fun n ↦
    { toFun := fun z : H ↦ χ.annulusCutoff n z * (φ : H → ℝ) z
      smooth := (χ.annulusCutoff_smooth n).mul φ.smooth
      support_subset := by
        exact (tsupport_mul_subset_left).trans
          (χ.annulusCutoff_tsupport_subset n)
      compact_support := by
        exact (χ.annulusCutoff_compact_support n).of_isClosed_subset
          (isClosed_tsupport _) tsupport_mul_subset_left }
  refine
    ⟨{ toEuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestFunctions :=
          { unitTest := unitTest
            annulusTest := annulusTest }
       unitCutoff := χ.unitCutoff
       annulusCutoff := χ.annulusCutoff
       unitCutoff_smooth := χ.unitCutoff_smooth
       annulusCutoff_smooth := χ.annulusCutoff_smooth
       unitTest_eq := by
        intro n x
        rfl
       annulusTest_eq := by
        intro n x
        rfl
       unitCutoff_norm_le_one := χ.unitCutoff_norm_le_one
       annulusCutoff_norm_le_one := χ.annulusCutoff_norm_le_one
       width := χ.width
       width_pos := χ.width_pos
       width_tendsto_zero := χ.width_tendsto_zero
       unitCutoff_eq_one_on_core := χ.unitCutoff_eq_one_on_core
       annulusCutoff_eq_one_on_core := χ.annulusCutoff_eq_one_on_core
       unitCutoff_fderiv_eq_zero_on_core :=
          χ.unitCutoff_fderiv_eq_zero_on_core
       annulusCutoff_fderiv_eq_zero_on_core :=
          χ.annulusCutoff_fderiv_eq_zero_on_core
       unit_eq_on_core := ?_
       annulus_eq_on_core := ?_
       unit_norm_le := ?_
       annulus_norm_le := ?_ }, ?_⟩
  · intro n x hx
    simp [unitTest, χ.unitCutoff_eq_one_on_core n x hx]
  · intro n x hx₁ hx₂
    simp [annulusTest, χ.annulusCutoff_eq_one_on_core n x hx₁ hx₂]
  · intro n x
    calc
      ‖(unitTest n : H → ℝ) x‖
          = ‖χ.unitCutoff n x‖ * ‖φ x‖ := by
            simp [unitTest, norm_mul]
      _ ≤ 1 * ‖φ x‖ :=
            mul_le_mul_of_nonneg_right
              (χ.unitCutoff_norm_le_one n x) (norm_nonneg _)
      _ = ‖φ x‖ := one_mul _
  · intro n x
    calc
      ‖(annulusTest n : H → ℝ) x‖
          = ‖χ.annulusCutoff n x‖ * ‖φ x‖ := by
            simp [annulusTest, norm_mul]
      _ ≤ 1 * ‖φ x‖ :=
            mul_le_mul_of_nonneg_right
              (χ.annulusCutoff_norm_le_one n x) (norm_nonneg _)
      _ = ‖φ x‖ := one_mul _
  · exact χ.trace_collar_terms_tendsto_zero

/--
%%handwave
name:
  Trace-controlled smooth collar cutoff families exist
statement:
  Suppose the two local functions have matching \(L^1\)-traces on the unit
  sphere and the annular function has zero \(L^1\)-trace on the sphere of
  radius \(3/2\).  For every smooth compactly supported ambient test function
  and constant direction, there are smooth collar cutoffs whose
  cutoff-derivative collar terms tend to zero.
proof:
  Choose radial cutoffs which are equal to one on the compact cores and which
  transition across collars of width \(\varepsilon_n\downarrow0\) with
  normalized radial derivative.  The \(L^1\)-trace convergence identifies the
  two unit-sphere collar limits and gives opposite signs, while the zero
  outer trace makes the \(3/2\)-sphere collar contribution vanish.  Smooth the
  one-dimensional profiles without changing these limits.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_trace_controlled_smooth_collar_cutoff_tests
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v) :
    Nonempty
      (EuclideanSobolevUnitBallAnnulusL1TraceGlueTraceControlledSmoothCollarCutoffTests
        (u₀ := u₀) (u₁ := u₁) (τ := τ) φ v) := by
  rcases
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_trace_controlled_smooth_collar_cutoff_data
      hu₀_aesm hu₁_aesm _hinner₀ _hinner₁ _houter φ v hτ_weight with
    ⟨tests, htrace⟩
  exact
    ⟨{ toEuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests :=
          tests
       trace_collar_terms_tendsto_zero := htrace }⟩

private theorem euclideanSobolev_smooth_collar_unitTest_tendsto_at_point
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H]
    {φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H)}
    (tests : EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests φ)
    {x : H} (hx : ‖x‖ < 1) :
    Filter.Tendsto
      (fun n : ℕ ↦ (tests.unitTest n : H → ℝ) x)
      Filter.atTop (𝓝 (φ x)) := by
  have hδ : 0 < 1 - ‖x‖ := by
    linarith
  have hevent :
      ∀ᶠ n in Filter.atTop, tests.width n < 1 - ‖x‖ :=
    (tendsto_order.mp tests.width_tendsto_zero).2 (1 - ‖x‖) hδ
  exact
    tendsto_nhds_of_eventually_eq
      (hevent.mono fun n hn ↦ by
        exact tests.unit_eq_on_core n x (by linarith))

private theorem euclideanSobolev_smooth_collar_annulusTest_tendsto_at_point
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H]
    {φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H)}
    (tests : EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests φ)
    {x : H} (hx_inner : 1 < ‖x‖) (hx_outer : ‖x‖ < (3 / 2 : ℝ)) :
    Filter.Tendsto
      (fun n : ℕ ↦ (tests.annulusTest n : H → ℝ) x)
      Filter.atTop (𝓝 (φ x)) := by
  have hδ_inner : 0 < ‖x‖ - 1 := by
    linarith
  have hδ_outer : 0 < (3 / 2 : ℝ) - ‖x‖ := by
    linarith
  have hevent_inner :
      ∀ᶠ n in Filter.atTop, tests.width n < ‖x‖ - 1 :=
    (tendsto_order.mp tests.width_tendsto_zero).2 (‖x‖ - 1) hδ_inner
  have hevent_outer :
      ∀ᶠ n in Filter.atTop, tests.width n < (3 / 2 : ℝ) - ‖x‖ :=
    (tendsto_order.mp tests.width_tendsto_zero).2
      ((3 / 2 : ℝ) - ‖x‖) hδ_outer
  exact
    tendsto_nhds_of_eventually_eq
      ((hevent_inner.and hevent_outer).mono fun n hn ↦ by
        exact tests.annulus_eq_on_core n x (by linarith) (by linarith))

private theorem euclideanSobolev_smooth_collar_unitCutoff_tendsto_one_at_point
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H]
    {φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H)}
    (tests : EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests φ)
    {x : H} (hx : ‖x‖ < 1) :
    Filter.Tendsto
      (fun n : ℕ ↦ tests.unitCutoff n x)
      Filter.atTop (𝓝 (1 : ℝ)) := by
  have hδ : 0 < 1 - ‖x‖ := by
    linarith
  have hevent :
      ∀ᶠ n in Filter.atTop, tests.width n < 1 - ‖x‖ :=
    (tendsto_order.mp tests.width_tendsto_zero).2 (1 - ‖x‖) hδ
  exact
    tendsto_nhds_of_eventually_eq
      (hevent.mono fun n hn ↦ by
        exact tests.unitCutoff_eq_one_on_core n x (by linarith))

private theorem euclideanSobolev_smooth_collar_annulusCutoff_tendsto_one_at_point
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H]
    {φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H)}
    (tests : EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests φ)
    {x : H} (hx_inner : 1 < ‖x‖) (hx_outer : ‖x‖ < (3 / 2 : ℝ)) :
    Filter.Tendsto
      (fun n : ℕ ↦ tests.annulusCutoff n x)
      Filter.atTop (𝓝 (1 : ℝ)) := by
  have hδ_inner : 0 < ‖x‖ - 1 := by
    linarith
  have hδ_outer : 0 < (3 / 2 : ℝ) - ‖x‖ := by
    linarith
  have hevent_inner :
      ∀ᶠ n in Filter.atTop, tests.width n < ‖x‖ - 1 :=
    (tendsto_order.mp tests.width_tendsto_zero).2 (‖x‖ - 1) hδ_inner
  have hevent_outer :
      ∀ᶠ n in Filter.atTop, tests.width n < (3 / 2 : ℝ) - ‖x‖ :=
    (tendsto_order.mp tests.width_tendsto_zero).2
      ((3 / 2 : ℝ) - ‖x‖) hδ_outer
  exact
    tendsto_nhds_of_eventually_eq
      ((hevent_inner.and hevent_outer).mono fun n hn ↦ by
        exact tests.annulusCutoff_eq_one_on_core n x (by linarith) (by linarith))

private theorem euclideanSobolev_smooth_collar_unit_left_main_pairing_tendsto
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    {u₀ : H → ℝ}
    {φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H)}
    (tests : EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests φ)
    (v : H)
    (htarget_int : Integrable
      (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • u₀ z)
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ z in Metric.ball (0 : H) 1,
          tests.unitCutoff n z •
            ((fderiv ℝ (φ : H → ℝ) z v) • u₀ z)
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in Metric.ball (0 : H) 1,
          (fderiv ℝ (φ : H → ℝ) z v) • u₀ z
          ∂MeasureTheory.volume)) := by
  let μ : Measure H := MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)
  let base : H → ℝ := fun z : H ↦
    (fderiv ℝ (φ : H → ℝ) z v) • u₀ z
  have hF_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun z : H ↦ tests.unitCutoff n z • base z) μ := by
    intro n
    have hcut :
        AEStronglyMeasurable (tests.unitCutoff n) μ :=
      (tests.unitCutoff_smooth n).continuous.aestronglyMeasurable
    exact hcut.smul htarget_int.aestronglyMeasurable
  have hbound_int : Integrable (fun z : H ↦ ‖base z‖) μ := by
    simpa [base, μ] using htarget_int.norm
  have hbound :
      ∀ n : ℕ, ∀ᵐ z ∂μ,
        ‖tests.unitCutoff n z • base z‖ ≤ ‖base z‖ := by
    intro n
    refine ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet ?_
    intro z _hz
    calc
      ‖tests.unitCutoff n z • base z‖
          = ‖tests.unitCutoff n z‖ * ‖base z‖ := by
            rw [norm_smul]
      _ ≤ 1 * ‖base z‖ :=
            mul_le_mul_of_nonneg_right
              (tests.unitCutoff_norm_le_one n z) (norm_nonneg _)
      _ = ‖base z‖ := one_mul _
  have hlim :
      ∀ᵐ z ∂μ,
        Filter.Tendsto
          (fun n : ℕ ↦ tests.unitCutoff n z • base z)
          Filter.atTop
          (𝓝 ((1 : ℝ) • base z)) := by
    refine ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet ?_
    intro z hz
    have hz_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact
      (euclideanSobolev_smooth_collar_unitCutoff_tendsto_one_at_point
        tests hz_norm).smul_const (base z)
  simpa [base, μ] using
    (tendsto_integral_of_dominated_convergence
      (μ := μ)
      (F := fun n (z : H) ↦ tests.unitCutoff n z • base z)
      (f := fun z : H ↦ (1 : ℝ) • base z)
      (fun z : H ↦ ‖base z‖)
      hF_meas hbound_int hbound hlim)

private theorem euclideanSobolev_smooth_collar_annulus_left_main_pairing_tendsto
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₁ : H → ℝ}
    {φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H)}
    (tests : EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests φ)
    (v : H)
    (htarget_int : Integrable
      (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • u₁ z)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H))) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          tests.annulusCutoff n z •
            ((fderiv ℝ (φ : H → ℝ) z v) • u₁ z)
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          (fderiv ℝ (φ : H → ℝ) z v) • u₁ z
          ∂MeasureTheory.volume)) := by
  let A : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let μ : Measure H := MeasureTheory.volume.restrict A
  let base : H → ℝ := fun z : H ↦
    (fderiv ℝ (φ : H → ℝ) z v) • u₁ z
  have hA_meas : MeasurableSet A :=
    (euclideanSobolevUnitBallReflectionAnnulus_isOpen (H := H)).measurableSet
  have hF_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun z : H ↦ tests.annulusCutoff n z • base z) μ := by
    intro n
    have hcut :
        AEStronglyMeasurable (tests.annulusCutoff n) μ :=
      (tests.annulusCutoff_smooth n).continuous.aestronglyMeasurable
    exact hcut.smul htarget_int.aestronglyMeasurable
  have hbound_int : Integrable (fun z : H ↦ ‖base z‖) μ := by
    simpa [A, base, μ] using htarget_int.norm
  have hbound :
      ∀ n : ℕ, ∀ᵐ z ∂μ,
        ‖tests.annulusCutoff n z • base z‖ ≤ ‖base z‖ := by
    intro n
    refine ae_restrict_of_forall_mem hA_meas ?_
    intro z _hz
    calc
      ‖tests.annulusCutoff n z • base z‖
          = ‖tests.annulusCutoff n z‖ * ‖base z‖ := by
            rw [norm_smul]
      _ ≤ 1 * ‖base z‖ :=
            mul_le_mul_of_nonneg_right
              (tests.annulusCutoff_norm_le_one n z) (norm_nonneg _)
      _ = ‖base z‖ := one_mul _
  have hlim :
      ∀ᵐ z ∂μ,
        Filter.Tendsto
          (fun n : ℕ ↦ tests.annulusCutoff n z • base z)
          Filter.atTop
          (𝓝 ((1 : ℝ) • base z)) := by
    refine ae_restrict_of_forall_mem hA_meas ?_
    intro z hz
    have hz_inner : 1 < ‖z‖ := by
      simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hz.1
    have hz_outer : ‖z‖ < (3 / 2 : ℝ) := by
      simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hz.2
    exact
      (euclideanSobolev_smooth_collar_annulusCutoff_tendsto_one_at_point
        tests hz_inner hz_outer).smul_const (base z)
  simpa [A, base, μ] using
    (tendsto_integral_of_dominated_convergence
      (μ := μ)
      (F := fun n (z : H) ↦ tests.annulusCutoff n z • base z)
      (f := fun z : H ↦ (1 : ℝ) • base z)
      (fun z : H ↦ ‖base z‖)
      hF_meas hbound_int hbound hlim)

private theorem euclideanSobolev_smooth_collar_unit_right_pairing_tendsto
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    {φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H)}
    (tests : EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests φ)
    {du₀ : H → H →L[ℝ] ℝ} (v : H)
    (htarget_int : Integrable
      (fun z : H ↦ φ z • du₀ z v)
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hunit_right_int : ∀ n : ℕ, Integrable
      (fun z : H ↦ (tests.unitTest n : H → ℝ) z • du₀ z v)
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ z in Metric.ball (0 : H) 1,
          (tests.unitTest n : H → ℝ) z • du₀ z v
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in Metric.ball (0 : H) 1,
          φ z • du₀ z v ∂MeasureTheory.volume)) := by
  let μ : Measure H := MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)
  have hF_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun z : H ↦ (tests.unitTest n : H → ℝ) z • du₀ z v) μ := by
    intro n
    simpa [μ] using (hunit_right_int n).aestronglyMeasurable
  have hbound_int :
      Integrable (fun z : H ↦ ‖φ z • du₀ z v‖) μ := by
    simpa [μ] using htarget_int.norm
  have hbound :
      ∀ n : ℕ, ∀ᵐ z ∂μ,
        ‖(tests.unitTest n : H → ℝ) z • du₀ z v‖ ≤
          ‖φ z • du₀ z v‖ := by
    intro n
    refine ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet ?_
    intro z _hz
    calc
      ‖(tests.unitTest n : H → ℝ) z • du₀ z v‖
          = ‖(tests.unitTest n : H → ℝ) z‖ * ‖du₀ z v‖ := by
            rw [norm_smul]
      _ ≤ ‖φ z‖ * ‖du₀ z v‖ :=
            mul_le_mul_of_nonneg_right (tests.unit_norm_le n z)
              (norm_nonneg _)
      _ = ‖φ z • du₀ z v‖ := by
            rw [norm_smul]
  have hlim :
      ∀ᵐ z ∂μ,
        Filter.Tendsto
          (fun n : ℕ ↦ (tests.unitTest n : H → ℝ) z • du₀ z v)
          Filter.atTop
          (𝓝 (φ z • du₀ z v)) := by
    refine ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet ?_
    intro z hz
    have hz_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact
      (euclideanSobolev_smooth_collar_unitTest_tendsto_at_point
        tests hz_norm).smul_const (du₀ z v)
  simpa [μ] using
    (tendsto_integral_of_dominated_convergence
      (μ := μ)
      (F := fun n (z : H) ↦ (tests.unitTest n : H → ℝ) z • du₀ z v)
      (f := fun z : H ↦ φ z • du₀ z v)
      (fun z : H ↦ ‖φ z • du₀ z v‖)
      hF_meas hbound_int hbound hlim)

private theorem euclideanSobolev_smooth_collar_annulus_right_pairing_tendsto
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H)}
    (tests : EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests φ)
    {du₁ : H → H →L[ℝ] ℝ} (v : H)
    (htarget_int : Integrable
      (fun z : H ↦ φ z • du₁ z v)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (hannulus_right_int : ∀ n : ℕ, Integrable
      (fun z : H ↦ (tests.annulusTest n : H → ℝ) z • du₁ z v)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H))) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          (tests.annulusTest n : H → ℝ) z • du₁ z v
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          φ z • du₁ z v ∂MeasureTheory.volume)) := by
  let A : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let μ : Measure H := MeasureTheory.volume.restrict A
  have hA_meas : MeasurableSet A :=
    (euclideanSobolevUnitBallReflectionAnnulus_isOpen (H := H)).measurableSet
  have hF_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun z : H ↦ (tests.annulusTest n : H → ℝ) z • du₁ z v) μ := by
    intro n
    simpa [A, μ] using (hannulus_right_int n).aestronglyMeasurable
  have hbound_int :
      Integrable (fun z : H ↦ ‖φ z • du₁ z v‖) μ := by
    simpa [A, μ] using htarget_int.norm
  have hbound :
      ∀ n : ℕ, ∀ᵐ z ∂μ,
        ‖(tests.annulusTest n : H → ℝ) z • du₁ z v‖ ≤
          ‖φ z • du₁ z v‖ := by
    intro n
    refine ae_restrict_of_forall_mem hA_meas ?_
    intro z _hz
    calc
      ‖(tests.annulusTest n : H → ℝ) z • du₁ z v‖
          = ‖(tests.annulusTest n : H → ℝ) z‖ * ‖du₁ z v‖ := by
            rw [norm_smul]
      _ ≤ ‖φ z‖ * ‖du₁ z v‖ :=
            mul_le_mul_of_nonneg_right (tests.annulus_norm_le n z)
              (norm_nonneg _)
      _ = ‖φ z • du₁ z v‖ := by
            rw [norm_smul]
  have hlim :
      ∀ᵐ z ∂μ,
        Filter.Tendsto
          (fun n : ℕ ↦ (tests.annulusTest n : H → ℝ) z • du₁ z v)
          Filter.atTop
          (𝓝 (φ z • du₁ z v)) := by
    refine ae_restrict_of_forall_mem hA_meas ?_
    intro z hz
    have hz_inner : 1 < ‖z‖ := by
      simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hz.1
    have hz_outer : ‖z‖ < (3 / 2 : ℝ) := by
      simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hz.2
    exact
      (euclideanSobolev_smooth_collar_annulusTest_tendsto_at_point
        tests hz_inner hz_outer).smul_const (du₁ z v)
  simpa [A, μ] using
    (tendsto_integral_of_dominated_convergence
      (μ := μ)
      (F := fun n (z : H) ↦
        (tests.annulusTest n : H → ℝ) z • du₁ z v)
      (f := fun z : H ↦ φ z • du₁ z v)
      (fun z : H ↦ ‖φ z • du₁ z v‖)
      hF_meas hbound_int hbound hlim)

/--
%%handwave
name:
  The glued right pairing splits into the ball and annulus pairings
statement:
  The integral of the glued derivative pairing over the ambient space is the
  sum of the corresponding integral over the unit ball and the integral over
  the annulus \(1<\|x\|<3/2\).  The only boundary contribution is on spheres,
  which have Haar measure zero.
proof:
  Split the ambient space into the unit ball, the annulus, and the complement.
  On the two open pieces the glued integrand is exactly the local integrand,
  and it vanishes on the complement except possibly on boundary spheres.  The
  boundary spheres have zero Haar measure, so the boundary contribution does
  not change the Bochner integral.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_right_pairing_setIntegral_identity
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {du₀ du₁ : H → H →L[ℝ] ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hunit_int : Integrable
      (fun z : H ↦ φ z • du₀ z v)
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hannulus_int : Integrable
      (fun z : H ↦ φ z • du₁ z v)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (_hglobal_int : Integrable
      (fun z : H ↦
        φ z •
          ((if ‖z‖ < 1 then
            du₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            du₁ z
          else
            0) v))
      (MeasureTheory.volume.restrict Set.univ)) :
    (∫ z in Metric.ball (0 : H) 1,
        φ z • du₀ z v ∂MeasureTheory.volume) +
      ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
        φ z • du₁ z v ∂MeasureTheory.volume =
        ∫ z in Set.univ,
          φ z •
            ((if ‖z‖ < 1 then
              du₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              du₁ z
            else
              0) v) ∂MeasureTheory.volume := by
  classical
  let μ : Measure H := MeasureTheory.volume
  let B : Set H := Metric.ball (0 : H) 1
  let A : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let S : Set H := B ∪ A
  let G : H → ℝ := fun z ↦
    φ z •
      ((if ‖z‖ < 1 then
        du₀ z
      else if ‖z‖ < (3 / 2 : ℝ) then
        du₁ z
      else
        0) v)
  let G₀ : H → ℝ := fun z ↦ φ z • du₀ z v
  let G₁ : H → ℝ := fun z ↦ φ z • du₁ z v
  have hB_meas : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hA_meas : MeasurableSet A :=
    (euclideanSobolevUnitBallReflectionAnnulus_isOpen (H := H)).measurableSet
  have hS_meas : MeasurableSet S := hB_meas.union hA_meas
  have hG_int : Integrable G μ := by
    simpa [G, μ] using _hglobal_int
  have hB_int : IntegrableOn G B μ :=
    hG_int.integrableOn
  have hA_int : IntegrableOn G A μ :=
    hG_int.integrableOn
  have hBA_disjoint : Disjoint B A := by
    rw [Set.disjoint_left]
    intro z hzB hzA
    have hzB_norm : ‖z‖ < 1 := by
      simpa [B, Metric.mem_ball, dist_eq_norm] using hzB
    have hzA_inner : 1 < ‖z‖ := by
      simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hzA.1
    linarith
  have hS_split :
      ∫ z in S, G z ∂μ =
        (∫ z in B, G z ∂μ) + ∫ z in A, G z ∂μ := by
    simpa [S] using
      (setIntegral_union (μ := μ) (f := G) hBA_disjoint hA_meas
        hB_int hA_int)
  have hB_eq :
      ∫ z in B, G z ∂μ = ∫ z in B, G₀ z ∂μ := by
    refine setIntegral_congr_fun hB_meas ?_
    intro z hzB
    have hz_norm : ‖z‖ < 1 := by
      simpa [B, Metric.mem_ball, dist_eq_norm] using hzB
    simp [G, G₀, hz_norm]
  have hA_eq :
      ∫ z in A, G z ∂μ = ∫ z in A, G₁ z ∂μ := by
    refine setIntegral_congr_fun hA_meas ?_
    intro z hzA
    have hz_inner : 1 < ‖z‖ := by
      simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hzA.1
    have hz_not_ball : ¬ ‖z‖ < 1 := by
      linarith
    have hz_outer : ‖z‖ < (3 / 2 : ℝ) := by
      simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hzA.2
    simp [G, G₁, hz_not_ball, hz_outer]
  have hsphere_zero : μ {z : H | ‖z‖ = 1} = 0 := by
    simpa [μ, Metric.sphere, dist_eq_norm] using
      euclidean_volume_sphere_zero (H := H) (c := (0 : H)) (r := (1 : ℝ))
        (by norm_num)
  have hG_zero_compl :
      ∀ᵐ z ∂μ, z ∈ Sᶜ → G z = 0 := by
    filter_upwards [compl_mem_ae_iff.mpr hsphere_zero] with z hz_not_sphere hzS
    have hz_not_ball : ¬ ‖z‖ < 1 := by
      intro hz
      exact hzS (Or.inl (by
        simpa [B, Metric.mem_ball, dist_eq_norm] using hz))
    by_cases hz_outer : ‖z‖ < (3 / 2 : ℝ)
    · have hz_le_one : 1 ≤ ‖z‖ := le_of_not_gt hz_not_ball
      have hz_ne_one : ‖z‖ ≠ 1 := by
        intro hz_eq
        exact hz_not_sphere (by simpa using hz_eq)
      have hz_inner : 1 < ‖z‖ := lt_of_le_of_ne hz_le_one (Ne.symm hz_ne_one)
      exact False.elim <| hzS (Or.inr (by
        exact ⟨hz_inner, hz_outer⟩))
    · simp [G, hz_not_ball, hz_outer]
  have hcompl_zero :
      ∫ z in Sᶜ, G z ∂μ = 0 := by
    calc
      ∫ z in Sᶜ, G z ∂μ = ∫ z in Sᶜ, (0 : ℝ) ∂μ := by
        exact setIntegral_congr_ae hS_meas.compl hG_zero_compl
      _ = 0 := by simp
  have hS_eq_global :
      ∫ z in S, G z ∂μ = ∫ z in Set.univ, G z ∂μ := by
    have hadd := integral_add_compl hS_meas hG_int
    rw [hcompl_zero, add_zero] at hadd
    simpa [setIntegral_univ] using hadd
  calc
    (∫ z in Metric.ball (0 : H) 1,
        φ z • du₀ z v ∂MeasureTheory.volume) +
      ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
        φ z • du₁ z v ∂MeasureTheory.volume
        = (∫ z in B, G₀ z ∂μ) + ∫ z in A, G₁ z ∂μ := by
          rfl
    _ = (∫ z in B, G z ∂μ) + ∫ z in A, G z ∂μ := by
          rw [hB_eq, hA_eq]
    _ = ∫ z in S, G z ∂μ := hS_split.symm
    _ = ∫ z in Set.univ, G z ∂μ := hS_eq_global
    _ = ∫ z in Set.univ,
          φ z •
            ((if ‖z‖ < 1 then
              du₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              du₁ z
            else
              0) v) ∂MeasureTheory.volume := by
          rfl

/--
%%handwave
name:
  The glued left main pairing splits into the ball and annulus pairings
statement:
  The integral of the ambient-test derivative against the glued function
  equals the sum of the corresponding unit-ball and annulus integrals.  The
  only possible mismatch is on the unit sphere, which has Haar measure zero.
proof:
  Split the ambient integral over the union of the unit ball and annulus and
  its complement.  On the two open regions the glued integrand is exactly the
  corresponding local integrand.  On the complement it vanishes away from the
  unit sphere, and that sphere has zero Haar measure.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_left_main_setIntegral_identity
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hunit_int : Integrable
      (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • u₀ z)
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hannulus_int : Integrable
      (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • u₁ z)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (_hglobal_int : Integrable
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0))
      (MeasureTheory.volume.restrict Set.univ)) :
    (∫ z in Metric.ball (0 : H) 1,
        (fderiv ℝ (φ : H → ℝ) z v) • u₀ z ∂MeasureTheory.volume) +
      ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
        (fderiv ℝ (φ : H → ℝ) z v) • u₁ z ∂MeasureTheory.volume =
        ∫ z in Set.univ,
          (fderiv ℝ (φ : H → ℝ) z v) •
            (if ‖z‖ < 1 then
              u₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              u₁ z
            else
              0) ∂MeasureTheory.volume := by
  classical
  let μ : Measure H := MeasureTheory.volume
  let B : Set H := Metric.ball (0 : H) 1
  let A : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let S : Set H := B ∪ A
  let G : H → ℝ := fun z ↦
    (fderiv ℝ (φ : H → ℝ) z v) •
      (if ‖z‖ < 1 then
        u₀ z
      else if ‖z‖ < (3 / 2 : ℝ) then
        u₁ z
      else
        0)
  let G₀ : H → ℝ := fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • u₀ z
  let G₁ : H → ℝ := fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • u₁ z
  have hB_meas : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hA_meas : MeasurableSet A :=
    (euclideanSobolevUnitBallReflectionAnnulus_isOpen (H := H)).measurableSet
  have hS_meas : MeasurableSet S := hB_meas.union hA_meas
  have hG_int : Integrable G μ := by
    simpa [G, μ] using _hglobal_int
  have hB_int : IntegrableOn G B μ :=
    hG_int.integrableOn
  have hA_int : IntegrableOn G A μ :=
    hG_int.integrableOn
  have hBA_disjoint : Disjoint B A := by
    rw [Set.disjoint_left]
    intro z hzB hzA
    have hzB_norm : ‖z‖ < 1 := by
      simpa [B, Metric.mem_ball, dist_eq_norm] using hzB
    have hzA_inner : 1 < ‖z‖ := by
      simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hzA.1
    linarith
  have hS_split :
      ∫ z in S, G z ∂μ =
        (∫ z in B, G z ∂μ) + ∫ z in A, G z ∂μ := by
    simpa [S] using
      (setIntegral_union (μ := μ) (f := G) hBA_disjoint hA_meas
        hB_int hA_int)
  have hB_eq :
      ∫ z in B, G z ∂μ = ∫ z in B, G₀ z ∂μ := by
    refine setIntegral_congr_fun hB_meas ?_
    intro z hzB
    have hz_norm : ‖z‖ < 1 := by
      simpa [B, Metric.mem_ball, dist_eq_norm] using hzB
    simp [G, G₀, hz_norm]
  have hA_eq :
      ∫ z in A, G z ∂μ = ∫ z in A, G₁ z ∂μ := by
    refine setIntegral_congr_fun hA_meas ?_
    intro z hzA
    have hz_inner : 1 < ‖z‖ := by
      simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hzA.1
    have hz_not_ball : ¬ ‖z‖ < 1 := by
      linarith
    have hz_outer : ‖z‖ < (3 / 2 : ℝ) := by
      simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hzA.2
    simp [G, G₁, hz_not_ball, hz_outer]
  have hsphere_zero : μ {z : H | ‖z‖ = 1} = 0 := by
    simpa [μ, Metric.sphere, dist_eq_norm] using
      euclidean_volume_sphere_zero (H := H) (c := (0 : H)) (r := (1 : ℝ))
        (by norm_num)
  have hG_zero_compl :
      ∀ᵐ z ∂μ, z ∈ Sᶜ → G z = 0 := by
    filter_upwards [compl_mem_ae_iff.mpr hsphere_zero] with z hz_not_sphere hzS
    have hz_not_ball : ¬ ‖z‖ < 1 := by
      intro hz
      exact hzS (Or.inl (by
        simpa [B, Metric.mem_ball, dist_eq_norm] using hz))
    by_cases hz_outer : ‖z‖ < (3 / 2 : ℝ)
    · have hz_le_one : 1 ≤ ‖z‖ := le_of_not_gt hz_not_ball
      have hz_ne_one : ‖z‖ ≠ 1 := by
        intro hz_eq
        exact hz_not_sphere (by simpa using hz_eq)
      have hz_inner : 1 < ‖z‖ := lt_of_le_of_ne hz_le_one (Ne.symm hz_ne_one)
      exact False.elim <| hzS (Or.inr (by
        exact ⟨hz_inner, hz_outer⟩))
    · simp [G, hz_not_ball, hz_outer]
  have hcompl_zero :
      ∫ z in Sᶜ, G z ∂μ = 0 := by
    calc
      ∫ z in Sᶜ, G z ∂μ = ∫ z in Sᶜ, (0 : ℝ) ∂μ := by
        exact setIntegral_congr_ae hS_meas.compl hG_zero_compl
      _ = 0 := by simp
  have hS_eq_global :
      ∫ z in S, G z ∂μ = ∫ z in Set.univ, G z ∂μ := by
    have hadd := integral_add_compl hS_meas hG_int
    rw [hcompl_zero, add_zero] at hadd
    simpa [setIntegral_univ] using hadd
  calc
    (∫ z in Metric.ball (0 : H) 1,
        (fderiv ℝ (φ : H → ℝ) z v) • u₀ z ∂MeasureTheory.volume) +
      ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
        (fderiv ℝ (φ : H → ℝ) z v) • u₁ z ∂MeasureTheory.volume
        = (∫ z in B, G₀ z ∂μ) + ∫ z in A, G₁ z ∂μ := by
          rfl
    _ = (∫ z in B, G z ∂μ) + ∫ z in A, G z ∂μ := by
          rw [hB_eq, hA_eq]
    _ = ∫ z in S, G z ∂μ := hS_split.symm
    _ = ∫ z in Set.univ, G z ∂μ := hS_eq_global
    _ = ∫ z in Set.univ,
          (fderiv ℝ (φ : H → ℝ) z v) •
            (if ‖z‖ < 1 then
              u₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              u₁ z
            else
              0) ∂MeasureTheory.volume := by
          rfl

/--
%%handwave
name:
  Trace cancellation for cutoff-derivative collars
statement:
  For smooth collar cutoffs adapted to the unit sphere and the sphere of
  radius \(3/2\), the sum of the integrals containing the derivatives of the
  scalar cutoffs tends to zero.
proof:
  The cutoff derivatives are supported in shrinking collars.  The two
  unit-sphere collar terms converge to the same boundary integral with
  opposite signs, because the inside and outside \(L^1\)-traces agree.  The
  outer collar term tends to zero because the annular function has zero
  \(L^1\)-trace at radius \(3/2\).
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_smooth_collar_cutoff_left_trace_collar_terms_tendsto_zero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (tests :
      EuclideanSobolevUnitBallAnnulusL1TraceGlueTraceControlledSmoothCollarCutoffTests
        (u₀ := u₀) (u₁ := u₁) (τ := τ) φ v) :
    Filter.Tendsto
      (fun n : ℕ ↦
        (∫ z in Metric.ball (0 : H) 1,
          ((fderiv ℝ (tests.unitCutoff n) z v) * φ z) • u₀ z
          ∂MeasureTheory.volume) +
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          ((fderiv ℝ (tests.annulusCutoff n) z v) * φ z) • u₁ z
          ∂MeasureTheory.volume)
      Filter.atTop (𝓝 (0 : ℝ)) := by
  exact tests.trace_collar_terms_tendsto_zero

/--
%%handwave
name:
  The derivative-collar error tends to zero
statement:
  For smooth collar cutoffs adapted to the unit sphere and the sphere of
  radius \(3/2\), the difference between the local left pairings and their
  main parts, where only the ambient test derivative is retained, tends to
  zero.
proof:
  Apply the product rule to each cutoff test.  The error is exactly the sum
  of the terms containing the derivatives of the scalar cutoffs, and these
  terms vanish in the limit by the trace cancellation for the shrinking
  collars.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_smooth_collar_cutoff_left_derivative_collar_error_tendsto_zero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (tests :
      EuclideanSobolevUnitBallAnnulusL1TraceGlueTraceControlledSmoothCollarCutoffTests
        (u₀ := u₀) (u₁ := u₁) (τ := τ) φ v)
    (_hunit_left_int : ∀ n : ℕ, Integrable
      (fun z : H ↦
        (fderiv ℝ (tests.unitTest n : H → ℝ) z v) • u₀ z)
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hannulus_left_int : ∀ n : ℕ, Integrable
      (fun z : H ↦
        (fderiv ℝ (tests.annulusTest n : H → ℝ) z v) • u₁ z)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (_hleft_int : Integrable
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0))
      (MeasureTheory.volume.restrict Set.univ)) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ((∫ z in Metric.ball (0 : H) 1,
            (fderiv ℝ (tests.unitTest n : H → ℝ) z v) • u₀ z
            ∂MeasureTheory.volume) +
          ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
            (fderiv ℝ (tests.annulusTest n : H → ℝ) z v) • u₁ z
            ∂MeasureTheory.volume) -
          ((∫ z in Metric.ball (0 : H) 1,
              tests.unitCutoff n z •
                ((fderiv ℝ (φ : H → ℝ) z v) • u₀ z)
              ∂MeasureTheory.volume) +
            ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
                tests.annulusCutoff n z •
                  ((fderiv ℝ (φ : H → ℝ) z v) • u₁ z)
                ∂MeasureTheory.volume))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  classical
  let B : Set H := Metric.ball (0 : H) 1
  let A : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let μB : Measure H := MeasureTheory.volume.restrict B
  let μA : Measure H := MeasureTheory.volume.restrict A
  let Ufull : ℕ → H → ℝ := fun n z ↦
    (fderiv ℝ (tests.unitTest n : H → ℝ) z v) • u₀ z
  let Umain : ℕ → H → ℝ := fun n z ↦
    tests.unitCutoff n z • ((fderiv ℝ (φ : H → ℝ) z v) • u₀ z)
  let Uerr : ℕ → H → ℝ := fun n z ↦
    ((fderiv ℝ (tests.unitCutoff n) z v) * φ z) • u₀ z
  let Afull : ℕ → H → ℝ := fun n z ↦
    (fderiv ℝ (tests.annulusTest n : H → ℝ) z v) • u₁ z
  let Amain : ℕ → H → ℝ := fun n z ↦
    tests.annulusCutoff n z •
      ((fderiv ℝ (φ : H → ℝ) z v) • u₁ z)
  let Aerr : ℕ → H → ℝ := fun n z ↦
    ((fderiv ℝ (tests.annulusCutoff n) z v) * φ z) • u₁ z
  have hB_meas : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hA_meas : MeasurableSet A :=
    (euclideanSobolevUnitBallReflectionAnnulus_isOpen (H := H)).measurableSet
  have hunit_target_int :
      Integrable
        (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • u₀ z) μB := by
    have hμ_le : μB ≤ MeasureTheory.volume.restrict Set.univ :=
      Measure.restrict_mono (Set.subset_univ _) le_rfl
    have hglobal_local := _hleft_int.mono_measure hμ_le
    refine hglobal_local.congr ?_
    refine ae_restrict_of_forall_mem hB_meas ?_
    intro z hz
    have hz_norm : ‖z‖ < 1 := by
      simpa [B, Metric.mem_ball, dist_eq_norm] using hz
    simp [hz_norm]
  have hannulus_target_int :
      Integrable
        (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • u₁ z) μA := by
    have hμ_le : μA ≤ MeasureTheory.volume.restrict Set.univ :=
      Measure.restrict_mono (Set.subset_univ _) le_rfl
    have hglobal_local := _hleft_int.mono_measure hμ_le
    refine hglobal_local.congr ?_
    refine ae_restrict_of_forall_mem hA_meas ?_
    intro z hz
    have hz_inner : 1 < ‖z‖ := by
      simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hz.1
    have hz_not_unit : ¬ ‖z‖ < 1 := by
      linarith
    have hz_outer : ‖z‖ < (3 / 2 : ℝ) := by
      simpa [A, euclideanSobolevUnitBallReflectionAnnulus] using hz.2
    simp [hz_not_unit, hz_outer]
  have hunit_main_int : ∀ n : ℕ, Integrable (Umain n) μB := by
    intro n
    have hcut :
        AEStronglyMeasurable (tests.unitCutoff n) μB :=
      (tests.unitCutoff_smooth n).continuous.aestronglyMeasurable
    have hmain_meas :
        AEStronglyMeasurable (Umain n) μB := by
      exact hcut.smul hunit_target_int.aestronglyMeasurable
    refine hunit_target_int.mono hmain_meas ?_
    refine ae_restrict_of_forall_mem hB_meas ?_
    intro z _hz
    calc
      ‖Umain n z‖
          = ‖tests.unitCutoff n z‖ *
              ‖(fderiv ℝ (φ : H → ℝ) z v) • u₀ z‖ := by
            simp [Umain]
      _ ≤ 1 * ‖(fderiv ℝ (φ : H → ℝ) z v) • u₀ z‖ :=
            mul_le_mul_of_nonneg_right
              (tests.unitCutoff_norm_le_one n z) (norm_nonneg _)
      _ = ‖(fderiv ℝ (φ : H → ℝ) z v) • u₀ z‖ := one_mul _
  have hannulus_main_int : ∀ n : ℕ, Integrable (Amain n) μA := by
    intro n
    have hcut :
        AEStronglyMeasurable (tests.annulusCutoff n) μA :=
      (tests.annulusCutoff_smooth n).continuous.aestronglyMeasurable
    have hmain_meas :
        AEStronglyMeasurable (Amain n) μA := by
      exact hcut.smul hannulus_target_int.aestronglyMeasurable
    refine hannulus_target_int.mono hmain_meas ?_
    refine ae_restrict_of_forall_mem hA_meas ?_
    intro z _hz
    calc
      ‖Amain n z‖
          = ‖tests.annulusCutoff n z‖ *
              ‖(fderiv ℝ (φ : H → ℝ) z v) • u₁ z‖ := by
            simp [Amain]
      _ ≤ 1 * ‖(fderiv ℝ (φ : H → ℝ) z v) • u₁ z‖ :=
            mul_le_mul_of_nonneg_right
              (tests.annulusCutoff_norm_le_one n z) (norm_nonneg _)
      _ = ‖(fderiv ℝ (φ : H → ℝ) z v) • u₁ z‖ := one_mul _
  have hunit_sum_ae :
      ∀ n : ℕ, Ufull n =ᵐ[μB] fun z : H ↦ Umain n z + Uerr n z := by
    intro n
    exact ae_of_all μB fun z ↦ by
      have htest_fun :
          (tests.unitTest n : H → ℝ) =
            fun y : H ↦ tests.unitCutoff n y * (φ : H → ℝ) y := by
        funext y
        exact tests.unitTest_eq n y
      have hcutdiff : DifferentiableAt ℝ (tests.unitCutoff n) z :=
        (tests.unitCutoff_smooth n).differentiable (by simp) z
      have hφdiff : DifferentiableAt ℝ (φ : H → ℝ) z :=
        (φ.smooth.differentiable (by simp)) z
      dsimp [Ufull, Umain, Uerr]
      rw [htest_fun, fderiv_fun_mul hcutdiff hφdiff]
      simp [smul_eq_mul]
      ring
  have hannulus_sum_ae :
      ∀ n : ℕ, Afull n =ᵐ[μA] fun z : H ↦ Amain n z + Aerr n z := by
    intro n
    exact ae_of_all μA fun z ↦ by
      have htest_fun :
          (tests.annulusTest n : H → ℝ) =
            fun y : H ↦ tests.annulusCutoff n y * (φ : H → ℝ) y := by
        funext y
        exact tests.annulusTest_eq n y
      have hcutdiff : DifferentiableAt ℝ (tests.annulusCutoff n) z :=
        (tests.annulusCutoff_smooth n).differentiable (by simp) z
      have hφdiff : DifferentiableAt ℝ (φ : H → ℝ) z :=
        (φ.smooth.differentiable (by simp)) z
      dsimp [Afull, Amain, Aerr]
      rw [htest_fun, fderiv_fun_mul hcutdiff hφdiff]
      simp [smul_eq_mul]
      ring
  have hunit_err_int : ∀ n : ℕ, Integrable (Uerr n) μB := by
    intro n
    have hfull_int : Integrable (Ufull n) μB := by
      simpa [B, μB, Ufull] using _hunit_left_int n
    have hsum_int : Integrable (fun z : H ↦ Umain n z + Uerr n z) μB :=
      hfull_int.congr (hunit_sum_ae n)
    have hdiff_int :
        Integrable (fun z : H ↦ (Umain n z + Uerr n z) - Umain n z) μB :=
      hsum_int.sub (hunit_main_int n)
    refine hdiff_int.congr ?_
    exact ae_of_all μB fun z ↦ by
      simp
  have hannulus_err_int : ∀ n : ℕ, Integrable (Aerr n) μA := by
    intro n
    have hfull_int : Integrable (Afull n) μA := by
      simpa [A, μA, Afull] using _hannulus_left_int n
    have hsum_int : Integrable (fun z : H ↦ Amain n z + Aerr n z) μA :=
      hfull_int.congr (hannulus_sum_ae n)
    have hdiff_int :
        Integrable (fun z : H ↦ (Amain n z + Aerr n z) - Amain n z) μA :=
      hsum_int.sub (hannulus_main_int n)
    refine hdiff_int.congr ?_
    exact ae_of_all μA fun z ↦ by
      simp
  have hunit_integral :
      ∀ n : ℕ,
        ∫ z, Ufull n z ∂μB =
          (∫ z, Umain n z ∂μB) + ∫ z, Uerr n z ∂μB := by
    intro n
    calc
      ∫ z, Ufull n z ∂μB
          = ∫ z, Umain n z + Uerr n z ∂μB := by
            exact integral_congr_ae (hunit_sum_ae n)
      _ = (∫ z, Umain n z ∂μB) + ∫ z, Uerr n z ∂μB := by
            exact integral_add (hunit_main_int n) (hunit_err_int n)
  have hannulus_integral :
      ∀ n : ℕ,
        ∫ z, Afull n z ∂μA =
          (∫ z, Amain n z ∂μA) + ∫ z, Aerr n z ∂μA := by
    intro n
    calc
      ∫ z, Afull n z ∂μA
          = ∫ z, Amain n z + Aerr n z ∂μA := by
            exact integral_congr_ae (hannulus_sum_ae n)
      _ = (∫ z, Amain n z ∂μA) + ∫ z, Aerr n z ∂μA := by
            exact integral_add (hannulus_main_int n) (hannulus_err_int n)
  have htrace_terms :
      Filter.Tendsto
        (fun n : ℕ ↦
          (∫ z, Uerr n z ∂μB) + ∫ z, Aerr n z ∂μA)
        Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [B, A, μB, μA, Uerr, Aerr] using
      euclideanSobolev_unit_ball_annulus_l1_trace_glue_smooth_collar_cutoff_left_trace_collar_terms_tendsto_zero
        _hinner₀ _hinner₁ _houter φ v tests
  refine Filter.Tendsto.congr' ?_ htrace_terms
  exact Filter.Eventually.of_forall fun n ↦ by
    change
      (∫ z, Uerr n z ∂μB) + ∫ z, Aerr n z ∂μA =
        ((∫ z, Ufull n z ∂μB) + ∫ z, Afull n z ∂μA) -
          ((∫ z, Umain n z ∂μB) + ∫ z, Amain n z ∂μA)
    rw [hunit_integral n, hannulus_integral n]
    ring

/--
%%handwave
name:
  Trace collar control gives the left pairing limit
statement:
  Let smooth collar tests be products of a fixed ambient test with scalar
  cutoffs which shrink to the boundary spheres.  If the two functions have
  matching \(L^1\)-traces on the unit sphere and the annular function has
  zero \(L^1\)-trace on the outer sphere, then the sum of the two local left
  pairings converges to the left pairing of the glued function.
proof:
  Expand the derivatives of the products by the classical product rule.  The
  terms where the cutoffs multiply the ambient derivative converge by
  dominated convergence and absolute continuity on the shrinking collars.  The
  derivative-of-cutoff terms are supported in the three thin collars; the two
  contributions at the unit sphere cancel in the limit by the common
  \(L^1\)-trace, and the outer contribution tends to zero by the zero
  \(L^1\)-trace at radius \(3/2\).
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_smooth_collar_cutoff_left_pairing_limit_of_trace_collar_control
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ}
    {τ : H → ℝ}
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (tests :
      EuclideanSobolevUnitBallAnnulusL1TraceGlueTraceControlledSmoothCollarCutoffTests
        (u₀ := u₀) (u₁ := u₁) (τ := τ) φ v)
    (_hunit_left_int : ∀ n : ℕ, Integrable
      (fun z : H ↦
        (fderiv ℝ (tests.unitTest n : H → ℝ) z v) • u₀ z)
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hannulus_left_int : ∀ n : ℕ, Integrable
      (fun z : H ↦
        (fderiv ℝ (tests.annulusTest n : H → ℝ) z v) • u₁ z)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (_hleft_int : Integrable
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0))
      (MeasureTheory.volume.restrict Set.univ))
    :
    Filter.Tendsto
      (fun n : ℕ ↦
        (∫ z in Metric.ball (0 : H) 1,
          (fderiv ℝ (tests.unitTest n : H → ℝ) z v) • u₀ z
          ∂MeasureTheory.volume) +
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          (fderiv ℝ (tests.annulusTest n : H → ℝ) z v) • u₁ z
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in Set.univ,
          (fderiv ℝ (φ : H → ℝ) z v) •
            (if ‖z‖ < 1 then
              u₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              u₁ z
            else
              0) ∂MeasureTheory.volume)) := by
  have hunit_target_int :
      Integrable
        (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • u₀ z)
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
    have hμ_le :
        MeasureTheory.volume.restrict (Metric.ball (0 : H) 1) ≤
          MeasureTheory.volume.restrict Set.univ :=
      Measure.restrict_mono (Set.subset_univ _) le_rfl
    have hglobal_local := _hleft_int.mono_measure hμ_le
    refine hglobal_local.congr ?_
    refine ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet ?_
    intro z hz
    have hz_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    simp [hz_norm]
  have hannulus_target_int :
      Integrable
        (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • u₁ z)
        (MeasureTheory.volume.restrict
          (euclideanSobolevUnitBallReflectionAnnulus H)) := by
    have hμ_le :
        MeasureTheory.volume.restrict
            (euclideanSobolevUnitBallReflectionAnnulus H) ≤
          MeasureTheory.volume.restrict Set.univ :=
      Measure.restrict_mono (Set.subset_univ _) le_rfl
    have hglobal_local := _hleft_int.mono_measure hμ_le
    refine hglobal_local.congr ?_
    refine ae_restrict_of_forall_mem
      (euclideanSobolevUnitBallReflectionAnnulus_isOpen (H := H)).measurableSet ?_
    intro z hz
    have hz_inner : 1 < ‖z‖ := by
      simpa [euclideanSobolevUnitBallReflectionAnnulus] using hz.1
    have hz_not_unit : ¬ ‖z‖ < 1 := by
      linarith
    have hz_outer : ‖z‖ < (3 / 2 : ℝ) := by
      simpa [euclideanSobolevUnitBallReflectionAnnulus] using hz.2
    simp [hz_not_unit, hz_outer]
  let smoothTests :
      EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests φ :=
    tests.toEuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests
  have hunit_main :
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ z in Metric.ball (0 : H) 1,
            tests.unitCutoff n z •
              ((fderiv ℝ (φ : H → ℝ) z v) • u₀ z)
            ∂MeasureTheory.volume)
        Filter.atTop
        (𝓝
          (∫ z in Metric.ball (0 : H) 1,
            (fderiv ℝ (φ : H → ℝ) z v) • u₀ z
            ∂MeasureTheory.volume)) :=
    by
      simpa [smoothTests] using
        euclideanSobolev_smooth_collar_unit_left_main_pairing_tendsto
          smoothTests v hunit_target_int
  have hannulus_main :
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
            tests.annulusCutoff n z •
              ((fderiv ℝ (φ : H → ℝ) z v) • u₁ z)
            ∂MeasureTheory.volume)
        Filter.atTop
        (𝓝
          (∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
            (fderiv ℝ (φ : H → ℝ) z v) • u₁ z
            ∂MeasureTheory.volume)) :=
    by
      simpa [smoothTests] using
        euclideanSobolev_smooth_collar_annulus_left_main_pairing_tendsto
          smoothTests v hannulus_target_int
  have hmain_sum := hunit_main.add hannulus_main
  have hsplit :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_left_main_setIntegral_identity
      φ v hunit_target_int hannulus_target_int _hleft_int
  rw [hsplit] at hmain_sum
  have herror :
      Filter.Tendsto
        (fun n : ℕ ↦
          ((∫ z in Metric.ball (0 : H) 1,
              (fderiv ℝ (tests.unitTest n : H → ℝ) z v) • u₀ z
              ∂MeasureTheory.volume) +
            ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
              (fderiv ℝ (tests.annulusTest n : H → ℝ) z v) • u₁ z
              ∂MeasureTheory.volume) -
            ((∫ z in Metric.ball (0 : H) 1,
                tests.unitCutoff n z •
                  ((fderiv ℝ (φ : H → ℝ) z v) • u₀ z)
                ∂MeasureTheory.volume) +
              ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
                tests.annulusCutoff n z •
                  ((fderiv ℝ (φ : H → ℝ) z v) • u₁ z)
                ∂MeasureTheory.volume))
        Filter.atTop (𝓝 (0 : ℝ)) :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_smooth_collar_cutoff_left_derivative_collar_error_tendsto_zero
      _hinner₀ _hinner₁ _houter φ v tests _hunit_left_int _hannulus_left_int
      _hleft_int
  have hcombined := herror.add hmain_sum
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcombined

/--
%%handwave
name:
  Smooth collar cutoffs have the left pairing limit
statement:
  For a smooth collar cutoff family, the sum of the two local left pairings
  converges to the left pairing of the glued function.
proof:
  The local weak derivative hypotheses give integrability of the local left
  pairings for each cutoff test.  Then apply the trace collar control theorem
  for the chosen smooth collar family.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_smooth_collar_cutoff_left_pairing_limit
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ} {du₀ du₁ : H → H →L[ℝ] ℝ}
    (hunit : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u₀ du₀)
    (hannulus : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H) u₁ du₁)
    {τ : H → ℝ}
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hleft_int : Integrable
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0))
      (MeasureTheory.volume.restrict Set.univ))
    (tests :
      EuclideanSobolevUnitBallAnnulusL1TraceGlueTraceControlledSmoothCollarCutoffTests
        (u₀ := u₀) (u₁ := u₁) (τ := τ) φ v) :
    Filter.Tendsto
      (fun n : ℕ ↦
        (∫ z in Metric.ball (0 : H) 1,
          (fderiv ℝ (tests.unitTest n : H → ℝ) z v) • u₀ z
          ∂MeasureTheory.volume) +
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          (fderiv ℝ (tests.annulusTest n : H → ℝ) z v) • u₁ z
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in Set.univ,
          (fderiv ℝ (φ : H → ℝ) z v) •
            (if ‖z‖ < 1 then
              u₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              u₁ z
          else
            0) ∂MeasureTheory.volume)) := by
  exact
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_smooth_collar_cutoff_left_pairing_limit_of_trace_collar_control
      _hinner₀ _hinner₁ _houter φ v tests
      (fun n ↦ (hunit (tests.unitTest n) v).1)
      (fun n ↦ (hannulus (tests.annulusTest n) v).1)
      _hleft_int

/--
%%handwave
name:
  Dominated convergence gives the right pairing limit
statement:
  Let smooth collar tests be bounded by a fixed ambient test and equal that
  ambient test away from collars whose widths tend to zero.  If the glued
  derivative pairing with the ambient test is integrable, then the sum of the
  local right pairings converges to the right pairing of the glued derivative.
proof:
  On every point away from the boundary spheres, the corresponding cutoff is
  eventually equal to one.  The pointwise bounds by the ambient test give an
  integrable dominating function from the assumed integrability of the glued
  derivative pairing, and dominated convergence gives the result.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_smooth_collar_cutoff_right_pairing_limit_of_dominated_convergence
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {du₀ du₁ : H → H →L[ℝ] ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (tests :
      EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests φ)
    (_hright_int : Integrable
      (fun z : H ↦
        φ z •
          ((if ‖z‖ < 1 then
            du₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            du₁ z
          else
            0) v))
      (MeasureTheory.volume.restrict Set.univ))
    (_hunit_right_int : ∀ n : ℕ, Integrable
      (fun z : H ↦ (tests.unitTest n : H → ℝ) z • du₀ z v)
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hannulus_right_int : ∀ n : ℕ, Integrable
      (fun z : H ↦ (tests.annulusTest n : H → ℝ) z • du₁ z v)
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    :
    Filter.Tendsto
      (fun n : ℕ ↦
        (∫ z in Metric.ball (0 : H) 1,
          (tests.unitTest n : H → ℝ) z • du₀ z v
          ∂MeasureTheory.volume) +
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          (tests.annulusTest n : H → ℝ) z • du₁ z v
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in Set.univ,
          φ z •
            ((if ‖z‖ < 1 then
              du₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              du₁ z
            else
              0) v) ∂MeasureTheory.volume)) := by
  have hunit_target_int :
      Integrable
        (fun z : H ↦ φ z • du₀ z v)
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
    have hμ_le :
        MeasureTheory.volume.restrict (Metric.ball (0 : H) 1) ≤
          MeasureTheory.volume.restrict Set.univ :=
      Measure.restrict_mono (Set.subset_univ _) le_rfl
    have hglobal_local := _hright_int.mono_measure hμ_le
    refine hglobal_local.congr ?_
    refine ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet ?_
    intro z hz
    have hz_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    simp [hz_norm]
  have hannulus_target_int :
      Integrable
        (fun z : H ↦ φ z • du₁ z v)
        (MeasureTheory.volume.restrict
          (euclideanSobolevUnitBallReflectionAnnulus H)) := by
    have hμ_le :
        MeasureTheory.volume.restrict
            (euclideanSobolevUnitBallReflectionAnnulus H) ≤
          MeasureTheory.volume.restrict Set.univ :=
      Measure.restrict_mono (Set.subset_univ _) le_rfl
    have hglobal_local := _hright_int.mono_measure hμ_le
    refine hglobal_local.congr ?_
    refine ae_restrict_of_forall_mem
      (euclideanSobolevUnitBallReflectionAnnulus_isOpen (H := H)).measurableSet ?_
    intro z hz
    have hz_inner : 1 < ‖z‖ := by
      simpa [euclideanSobolevUnitBallReflectionAnnulus] using hz.1
    have hz_not_unit : ¬ ‖z‖ < 1 := by
      linarith
    have hz_outer : ‖z‖ < (3 / 2 : ℝ) := by
      simpa [euclideanSobolevUnitBallReflectionAnnulus] using hz.2
    simp [hz_not_unit, hz_outer]
  have hunit_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ z in Metric.ball (0 : H) 1,
            (tests.unitTest n : H → ℝ) z • du₀ z v
            ∂MeasureTheory.volume)
        Filter.atTop
        (𝓝
          (∫ z in Metric.ball (0 : H) 1,
            φ z • du₀ z v ∂MeasureTheory.volume)) :=
    euclideanSobolev_smooth_collar_unit_right_pairing_tendsto
      tests v hunit_target_int _hunit_right_int
  have hannulus_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
            (tests.annulusTest n : H → ℝ) z • du₁ z v
            ∂MeasureTheory.volume)
        Filter.atTop
        (𝓝
          (∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
            φ z • du₁ z v ∂MeasureTheory.volume)) :=
    euclideanSobolev_smooth_collar_annulus_right_pairing_tendsto
      tests v hannulus_target_int _hannulus_right_int
  have hsplit :=
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_right_pairing_setIntegral_identity
      φ v hunit_target_int hannulus_target_int _hright_int
  have hsum := hunit_tendsto.add hannulus_tendsto
  rw [hsplit] at hsum
  simpa using hsum

/--
%%handwave
name:
  Smooth collar cutoffs have the right pairing limit
statement:
  For a smooth collar cutoff family, the sum of the two local right pairings
  converges to the right pairing of the glued derivative.
proof:
  The local weak derivative hypotheses give integrability of the local right
  pairings for each cutoff test.  Then apply dominated convergence for the
  bounded collar family.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_smooth_collar_cutoff_right_pairing_limit
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ} {du₀ du₁ : H → H →L[ℝ] ℝ}
    (hunit : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u₀ du₀)
    (hannulus : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H) u₁ du₁)
    {τ : H → ℝ}
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (_hright_int : Integrable
      (fun z : H ↦
        φ z •
          ((if ‖z‖ < 1 then
            du₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            du₁ z
          else
            0) v))
      (MeasureTheory.volume.restrict Set.univ))
    (tests :
      EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests φ) :
    Filter.Tendsto
      (fun n : ℕ ↦
        (∫ z in Metric.ball (0 : H) 1,
          (tests.unitTest n : H → ℝ) z • du₀ z v
          ∂MeasureTheory.volume) +
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          (tests.annulusTest n : H → ℝ) z • du₁ z v
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in Set.univ,
          φ z •
            ((if ‖z‖ < 1 then
              du₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              du₁ z
            else
              0) v) ∂MeasureTheory.volume)) := by
  exact
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_smooth_collar_cutoff_right_pairing_limit_of_dominated_convergence
      φ v tests _hright_int
      (fun n ↦ (hunit (tests.unitTest n) v).2.1)
      (fun n ↦ (hannulus (tests.annulusTest n) v).2.1)

/--
%%handwave
name:
  Smooth collar cutoffs have the required pairing limits
statement:
  Let a Sobolev function be given on the unit ball and another one on the
  annulus \(1<\|x\|<3/2\), with matching \(L^1\)-traces on the unit sphere
  and zero \(L^1\)-trace on the outer sphere.  For every compactly supported
  ambient test function and direction, there are smooth cutoff tests on the
  unit ball and on the annulus such that the sums of the two local left and
  right pairings converge to the corresponding pairings for the glued
  function and glued derivative.
proof:
  Choose radial collar cutoffs which are equal to one away from collars of
  width \(\varepsilon_n\) and which interpolate linearly across those
  collars, then smooth them without changing the pairing limits.  On compact
  subsets away from the two spheres, the cutoffs are eventually equal to one,
  so the interior contributions converge by dominated convergence.  The
  remaining terms are supported in collars whose thickness tends to zero.  The
  ordinary collar terms vanish by absolute continuity of the integral, and
  the derivative-of-cutoff terms are controlled by the normalized
  \(L^1\)-trace hypotheses on the inner and outer spheres.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_smooth_collar_cutoff_pairing_limits
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ} {du₀ du₁ : H → H →L[ℝ] ℝ}
    (_hunit : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u₀ du₀)
    (_hannulus : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H) u₁ du₁)
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    {τ : H → ℝ}
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v)
    (_hleft_int : Integrable
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0))
      (MeasureTheory.volume.restrict Set.univ))
    (_hright_int : Integrable
      (fun z : H ↦
        φ z •
          ((if ‖z‖ < 1 then
            du₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            du₁ z
          else
            0) v))
      (MeasureTheory.volume.restrict Set.univ))
    :
    ∃ tests : EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestFunctions φ,
      Filter.Tendsto
          (fun n : ℕ ↦
            (∫ z in Metric.ball (0 : H) 1,
              (fderiv ℝ (tests.unitTest n : H → ℝ) z v) • u₀ z
              ∂MeasureTheory.volume) +
            ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
              (fderiv ℝ (tests.annulusTest n : H → ℝ) z v) • u₁ z
              ∂MeasureTheory.volume)
          Filter.atTop
          (𝓝
            (∫ z in Set.univ,
              (fderiv ℝ (φ : H → ℝ) z v) •
                (if ‖z‖ < 1 then
                  u₀ z
                else if ‖z‖ < (3 / 2 : ℝ) then
                  u₁ z
                else
                  0) ∂MeasureTheory.volume)) ∧
        Filter.Tendsto
          (fun n : ℕ ↦
            (∫ z in Metric.ball (0 : H) 1,
              (tests.unitTest n : H → ℝ) z • du₀ z v
              ∂MeasureTheory.volume) +
            ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
              (tests.annulusTest n : H → ℝ) z • du₁ z v
              ∂MeasureTheory.volume)
          Filter.atTop
          (𝓝
            (∫ z in Set.univ,
              φ z •
                ((if ‖z‖ < 1 then
                  du₀ z
                else if ‖z‖ < (3 / 2 : ℝ) then
                  du₁ z
                else
              0) v) ∂MeasureTheory.volume)) := by
  rcases
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_trace_controlled_smooth_collar_cutoff_tests
      hu₀_aesm hu₁_aesm _hinner₀ _hinner₁ _houter φ v hτ_weight with
    ⟨tests⟩
  let smoothTests :
      EuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests φ :=
    tests.toEuclideanSobolevUnitBallAnnulusL1TraceGlueSmoothCollarCutoffTests
  let rawTests :
      EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestFunctions φ :=
    smoothTests.toEuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestFunctions
  have hleft :
      Filter.Tendsto
          (fun n : ℕ ↦
            (∫ z in Metric.ball (0 : H) 1,
              (fderiv ℝ (rawTests.unitTest n : H → ℝ) z v) • u₀ z
              ∂MeasureTheory.volume) +
            ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
              (fderiv ℝ (rawTests.annulusTest n : H → ℝ) z v) • u₁ z
              ∂MeasureTheory.volume)
          Filter.atTop
          (𝓝
            (∫ z in Set.univ,
              (fderiv ℝ (φ : H → ℝ) z v) •
                (if ‖z‖ < 1 then
                  u₀ z
                else if ‖z‖ < (3 / 2 : ℝ) then
                  u₁ z
                else
                  0) ∂MeasureTheory.volume)) := by
    simpa [rawTests] using
      euclideanSobolev_unit_ball_annulus_l1_trace_glue_smooth_collar_cutoff_left_pairing_limit
        _hunit _hannulus _hinner₀ _hinner₁ _houter φ v _hleft_int tests
  have hright :
      Filter.Tendsto
          (fun n : ℕ ↦
            (∫ z in Metric.ball (0 : H) 1,
              (rawTests.unitTest n : H → ℝ) z • du₀ z v
              ∂MeasureTheory.volume) +
            ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
              (rawTests.annulusTest n : H → ℝ) z • du₁ z v
              ∂MeasureTheory.volume)
          Filter.atTop
          (𝓝
            (∫ z in Set.univ,
              φ z •
                ((if ‖z‖ < 1 then
                  du₀ z
                else if ‖z‖ < (3 / 2 : ℝ) then
                  du₁ z
                else
                  0) v) ∂MeasureTheory.volume)) := by
    simpa [rawTests] using
      euclideanSobolev_unit_ball_annulus_l1_trace_glue_smooth_collar_cutoff_right_pairing_limit
        _hunit _hannulus _hinner₀ _hinner₁ _houter φ v _hright_int smoothTests
  exact ⟨rawTests, hleft, hright⟩

/--
%%handwave
name:
  Shrinking cutoff tests converge to the glued pairings
statement:
  Under the same hypotheses, the selected smooth collar cutoff tests give a
  convergence data package: the two local left pairings converge to the
  global left pairing of the glued function, and the two local right pairings
  converge to the global right pairing of the glued derivative.
proof:
  Apply the smooth collar cutoff limit construction and package its two
  convergence statements.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_cutoffTestConvergence
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ} {du₀ du₁ : H → H →L[ℝ] ℝ}
    (_hunit : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u₀ du₀)
    (_hannulus : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H) u₁ du₁)
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    {τ : H → ℝ}
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v)
    (_hleft_int : Integrable
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0))
      (MeasureTheory.volume.restrict Set.univ))
    (_hright_int : Integrable
      (fun z : H ↦
        φ z •
          ((if ‖z‖ < 1 then
            du₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            du₁ z
          else
            0) v))
      (MeasureTheory.volume.restrict Set.univ))
    :
    ∃ tests : EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestFunctions φ,
      EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestConvergence
        u₀ u₁ du₀ du₁ φ v tests := by
  rcases
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_smooth_collar_cutoff_pairing_limits
      _hunit _hannulus hu₀_aesm hu₁_aesm _hinner₀ _hinner₁ _houter φ v
      hτ_weight _hleft_int _hright_int with
    ⟨tests, hleft, hright⟩
  exact ⟨tests, ⟨hleft, hright⟩⟩

/--
Cutoff test data for gluing across the unit sphere and the sphere of radius
`3 / 2`, localized to one ambient test function and one direction.
-/
structure EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H]
    (u₀ u₁ : H → ℝ) (du₀ du₁ : H → H →L[ℝ] ℝ)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H) extends
    EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestFunctions φ where
  left_tendsto :
    Filter.Tendsto
      (fun n : ℕ ↦
        (∫ z in Metric.ball (0 : H) 1,
          (fderiv ℝ (unitTest n : H → ℝ) z v) • u₀ z
          ∂MeasureTheory.volume) +
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          (fderiv ℝ (annulusTest n : H → ℝ) z v) • u₁ z
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in Set.univ,
          (fderiv ℝ (φ : H → ℝ) z v) •
            (if ‖z‖ < 1 then
              u₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              u₁ z
            else
              0) ∂MeasureTheory.volume))
  right_tendsto :
    Filter.Tendsto
      (fun n : ℕ ↦
        (∫ z in Metric.ball (0 : H) 1,
          (unitTest n : H → ℝ) z • du₀ z v
          ∂MeasureTheory.volume) +
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
          (annulusTest n : H → ℝ) z • du₁ z v
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in Set.univ,
          φ z •
            ((if ‖z‖ < 1 then
              du₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              du₁ z
            else
              0) v) ∂MeasureTheory.volume))

/--
%%handwave
name:
  Collar-cutoff limits imply the glued test identity
statement:
  Suppose that the two local weak identities, after inserting radial collar
  cutoffs and summing the unit-ball and annular contributions, give a sequence
  of identities whose left and right sides converge to the global glued test
  pairings.  Then the global glued test identity follows.
proof:
  The approximate left sides converge to the desired left side, while the
  negatives of the approximate right sides converge to the negative of the
  desired right side.  Since the approximate identities identify these two
  sequences termwise, uniqueness of limits gives the result.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_test_identity_of_cutoffLimitData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H]
    {u₀ u₁ : H → ℝ} {du₀ du₁ : H → H →L[ℝ] ℝ}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction (Set.univ : Set H))
    (v : H)
    (hdata :
      EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffLimitData
        u₀ u₁ du₀ du₁ φ v) :
    ∫ z in Set.univ,
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0) ∂MeasureTheory.volume =
      -∫ z in Set.univ,
        φ z •
          ((if ‖z‖ < 1 then
            du₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            du₁ z
          else
            0) v) ∂MeasureTheory.volume := by
  let Llim : ℝ :=
    ∫ z in Set.univ,
      (fderiv ℝ (φ : H → ℝ) z v) •
        (if ‖z‖ < 1 then
          u₀ z
        else if ‖z‖ < (3 / 2 : ℝ) then
          u₁ z
        else
          0) ∂MeasureTheory.volume
  let Rlim : ℝ :=
    ∫ z in Set.univ,
      φ z •
        ((if ‖z‖ < 1 then
          du₀ z
        else if ‖z‖ < (3 / 2 : ℝ) then
          du₁ z
        else
          0) v) ∂MeasureTheory.volume
  have hnegR_tendsto_to_Llim :
      Filter.Tendsto (fun n : ℕ ↦ -hdata.rightApprox n)
        Filter.atTop (𝓝 Llim) := by
    exact Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n ↦ hdata.local_identity n)
      (by simpa [Llim] using hdata.left_tendsto)
  have hnegR_tendsto_to_neg_Rlim :
      Filter.Tendsto (fun n : ℕ ↦ -hdata.rightApprox n)
        Filter.atTop (𝓝 (-Rlim)) := by
    have hR_tendsto :
        Filter.Tendsto hdata.rightApprox Filter.atTop (𝓝 Rlim) := by
      simpa [Rlim] using hdata.right_tendsto
    exact hR_tendsto.neg
  have hlim_eq : Llim = -Rlim :=
    tendsto_nhds_unique hnegR_tendsto_to_Llim hnegR_tendsto_to_neg_Rlim
  simpa [Llim, Rlim] using hlim_eq

/--
%%handwave
name:
  Local weak identities give cutoff pairing sequences
statement:
  If cutoff tests on the unit ball and annulus have left and right pairings
  converging to the global glued pairings, then the corresponding summed
  pairings form sequences satisfying the termwise identity
  \(L_n=-R_n\).
proof:
  Apply the weak derivative identity on the unit ball to the unit cutoff test
  and on the annulus to the annular cutoff test.  Adding the two identities
  gives the termwise identity for the summed pairings, while the convergence
  hypotheses are exactly the required limiting statements.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_cutoffSequences_of_testData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H]
    {u₀ u₁ : H → ℝ} {du₀ du₁ : H → H →L[ℝ] ℝ}
    (hunit : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u₀ du₀)
    (hannulus : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H) u₁ du₁)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Set.univ)
    (v : H)
    (hdata :
      EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestData
        u₀ u₁ du₀ du₁ φ v) :
    ∃ (leftApprox rightApprox : ℕ → ℝ),
      (∀ n : ℕ, leftApprox n = -rightApprox n) ∧
        Filter.Tendsto leftApprox Filter.atTop
          (𝓝
            (∫ z in Set.univ,
              (fderiv ℝ (φ : H → ℝ) z v) •
                (if ‖z‖ < 1 then
                  u₀ z
                else if ‖z‖ < (3 / 2 : ℝ) then
                  u₁ z
                else
                  0) ∂MeasureTheory.volume)) ∧
        Filter.Tendsto rightApprox Filter.atTop
          (𝓝
            (∫ z in Set.univ,
              φ z •
                ((if ‖z‖ < 1 then
                  du₀ z
                else if ‖z‖ < (3 / 2 : ℝ) then
                  du₁ z
                else
                  0) v) ∂MeasureTheory.volume)) := by
  let leftApprox : ℕ → ℝ := fun n ↦
    (∫ z in Metric.ball (0 : H) 1,
      (fderiv ℝ (hdata.unitTest n : H → ℝ) z v) • u₀ z
      ∂MeasureTheory.volume) +
    ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
      (fderiv ℝ (hdata.annulusTest n : H → ℝ) z v) • u₁ z
      ∂MeasureTheory.volume
  let rightApprox : ℕ → ℝ := fun n ↦
    (∫ z in Metric.ball (0 : H) 1,
      (hdata.unitTest n : H → ℝ) z • du₀ z v
      ∂MeasureTheory.volume) +
    ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
      (hdata.annulusTest n : H → ℝ) z • du₁ z v
      ∂MeasureTheory.volume
  refine ⟨leftApprox, rightApprox, ?_, ?_, ?_⟩
  · intro n
    rcases hunit (hdata.unitTest n) v with ⟨_hL0, _hR0, h0⟩
    rcases hannulus (hdata.annulusTest n) v with ⟨_hL1, _hR1, h1⟩
    have h0' :
        ∫ z in Metric.ball (0 : H) 1,
            (fderiv ℝ (hdata.unitTest n : H → ℝ) z v) * u₀ z
            ∂MeasureTheory.volume =
          -∫ z in Metric.ball (0 : H) 1,
            (hdata.unitTest n : H → ℝ) z * du₀ z v
            ∂MeasureTheory.volume := by
      simpa [smul_eq_mul] using h0
    have h1' :
        ∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
            (fderiv ℝ (hdata.annulusTest n : H → ℝ) z v) * u₁ z
            ∂MeasureTheory.volume =
          -∫ z in euclideanSobolevUnitBallReflectionAnnulus H,
            (hdata.annulusTest n : H → ℝ) z * du₁ z v
            ∂MeasureTheory.volume := by
      simpa [smul_eq_mul] using h1
    dsimp [leftApprox, rightApprox]
    rw [h0', h1']
    ring
  · simpa [leftApprox] using hdata.left_tendsto
  · simpa [rightApprox] using hdata.right_tendsto

/--
%%handwave
name:
  Existence of gluing cutoff tests
statement:
  Under the local weak derivative identities on the unit ball and on the
  annulus, and under the matching \(L^1\)-trace hypotheses on the two boundary
  spheres, there are smooth compactly supported unit-ball and annular test
  functions whose local pairings converge to the global glued pairings.
proof:
  Choose smooth radial cutoffs which are one away from collars of the unit
  sphere and the sphere of radius \(3/2\), and which transition across
  collars of width tending to zero.  The left and right local pairings
  converge to the global pairings because ordinary collar terms vanish by
  absolute continuity of the integral, while the jump terms vanish by the
  assumed normalized \(L^1\)-trace convergence.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_cutoffTestData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ} {du₀ du₁ : H → H →L[ℝ] ℝ}
    (_hunit : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u₀ du₀)
    (_hannulus : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H) u₁ du₁)
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    {τ : H → ℝ}
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Set.univ)
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v)
    (_hleft_int : Integrable
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0))
      (MeasureTheory.volume.restrict Set.univ))
    (_hright_int : Integrable
      (fun z : H ↦
        φ z •
          ((if ‖z‖ < 1 then
            du₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            du₁ z
          else
            0) v))
      (MeasureTheory.volume.restrict Set.univ)) :
    Nonempty
      (EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestData
        u₀ u₁ du₀ du₁ φ v) := by
  rcases
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_cutoffTestConvergence
      _hunit _hannulus hu₀_aesm hu₁_aesm _hinner₀ _hinner₁ _houter φ v
      hτ_weight _hleft_int _hright_int with
    ⟨tests, hconv⟩
  exact
    ⟨{ toEuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffTestFunctions := tests
       left_tendsto := hconv.left_tendsto
       right_tendsto := hconv.right_tendsto }⟩

/--
%%handwave
name:
  Collar-cutoff sequences for gluing across two concentric spheres
statement:
  Under the local weak derivative identities on the unit ball and on the
  annulus, and under the matching \(L^1\)-trace hypotheses on the two boundary
  spheres, there are cutoff-localized left and right test pairings which are
  equal term by term and converge to the global glued pairings.
proof:
  Choose smooth radial cutoffs which are one away from collars of the unit
  sphere and the sphere of radius \(3/2\), and which transition across
  collars of width tending to zero.  Apply the two local weak identities to
  the cutoff tests.  The bulk cutoff errors vanish by absolute continuity of
  the integral, and the jump terms vanish by the assumed normalized
  \(L^1\)-trace convergence.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_cutoffSequences
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ} {du₀ du₁ : H → H →L[ℝ] ℝ}
    (_hunit : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u₀ du₀)
    (_hannulus : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H) u₁ du₁)
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    {τ : H → ℝ}
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Set.univ)
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v)
    (_hleft_int : Integrable
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0))
      (MeasureTheory.volume.restrict Set.univ))
    (_hright_int : Integrable
      (fun z : H ↦
        φ z •
          ((if ‖z‖ < 1 then
            du₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            du₁ z
          else
            0) v))
      (MeasureTheory.volume.restrict Set.univ)) :
    ∃ (leftApprox rightApprox : ℕ → ℝ),
      (∀ n : ℕ, leftApprox n = -rightApprox n) ∧
        Filter.Tendsto leftApprox Filter.atTop
          (𝓝
            (∫ z in Set.univ,
              (fderiv ℝ (φ : H → ℝ) z v) •
                (if ‖z‖ < 1 then
                  u₀ z
                else if ‖z‖ < (3 / 2 : ℝ) then
                  u₁ z
                else
                  0) ∂MeasureTheory.volume)) ∧
        Filter.Tendsto rightApprox Filter.atTop
          (𝓝
            (∫ z in Set.univ,
              φ z •
                ((if ‖z‖ < 1 then
                  du₀ z
                else if ‖z‖ < (3 / 2 : ℝ) then
                  du₁ z
                else
                  0) v) ∂MeasureTheory.volume)) := by
  rcases
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_cutoffTestData
      _hunit _hannulus hu₀_aesm hu₁_aesm _hinner₀ _hinner₁ _houter φ v hτ_weight
      _hleft_int _hright_int with
    ⟨hdata⟩
  exact
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_cutoffSequences_of_testData
      _hunit _hannulus φ v hdata

/--
%%handwave
name:
  Collar-cutoff approximation for gluing across two concentric spheres
statement:
  Under the local weak derivative identities on the unit ball and on the
  annulus, and under the matching \(L^1\)-trace hypotheses on the two boundary
  spheres, the collar-cutoff approximations of the glued test pairings exist
  and converge to the global glued pairings.
proof:
  Package
  [the cutoff-localized pairings with their termwise identities and
  limits](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_annulus_l1_trace_glue_cutoffSequences)
  into the corresponding approximation data.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_cutoffLimitData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ} {du₀ du₁ : H → H →L[ℝ] ℝ}
    (_hunit : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u₀ du₀)
    (_hannulus : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H) u₁ du₁)
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    {τ : H → ℝ}
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Set.univ)
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v)
    (_hleft_int : Integrable
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0))
      (MeasureTheory.volume.restrict Set.univ))
    (_hright_int : Integrable
      (fun z : H ↦
        φ z •
          ((if ‖z‖ < 1 then
            du₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            du₁ z
          else
            0) v))
      (MeasureTheory.volume.restrict Set.univ)) :
    Nonempty
      (EuclideanSobolevUnitBallAnnulusL1TraceGlueCutoffLimitData
        u₀ u₁ du₀ du₁ φ v) := by
  rcases
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_cutoffSequences
      _hunit _hannulus hu₀_aesm hu₁_aesm _hinner₀ _hinner₁ _houter φ v hτ_weight
      _hleft_int _hright_int with
    ⟨leftApprox, rightApprox, hlocal, hleft, hright⟩
  exact
    ⟨{ leftApprox := leftApprox
       rightApprox := rightApprox
       local_identity := hlocal
       left_tendsto := hleft
       right_tendsto := hright }⟩

/--
%%handwave
name:
  Test-function collar identity for gluing across two concentric spheres
statement:
  Under the weak derivative identities on the unit ball and on the annulus,
  under the matching \(L^1\) trace hypotheses on the two boundary spheres,
  and assuming the two global test pairings are integrable, the piecewise
  glued function and derivative field satisfy the global integration-by-parts
  identity for the fixed test function and direction.
proof:
  Fix a test function and a direction.  Choose radial cutoffs which are
  identically one away from collars of the unit sphere and the sphere of
  radius \(3/2\), and which transition linearly across collars of width
  \(\varepsilon\).  Applying the two local weak derivative identities to the
  cutoff tests gives the desired global identity plus collar error terms.
  The ordinary collar terms tend to zero by absolute continuity of the
  integral on compact sets, and the jump terms tend to zero by the assumed
  normalized \(L^1\)-trace convergence.
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_test_identity
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ} {du₀ du₁ : H → H →L[ℝ] ℝ}
    (hunit : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u₀ du₀)
    (hannulus : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H) u₁ du₁)
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    {τ : H → ℝ}
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Set.univ)
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v)
    (_hleft_int : Integrable
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0))
      (MeasureTheory.volume.restrict Set.univ))
    (_hright_int : Integrable
      (fun z : H ↦
        φ z •
          ((if ‖z‖ < 1 then
            du₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            du₁ z
          else
            0) v))
      (MeasureTheory.volume.restrict Set.univ)) :
    ∫ z in Set.univ,
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0) ∂MeasureTheory.volume =
      -∫ z in Set.univ,
        φ z •
          ((if ‖z‖ < 1 then
            du₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            du₁ z
          else
            0) v) ∂MeasureTheory.volume := by
  rcases
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_cutoffLimitData
      hunit hannulus hu₀_aesm hu₁_aesm _hinner₀ _hinner₁ _houter φ v hτ_weight
      _hleft_int _hright_int with
    ⟨hdata⟩
  exact
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_test_identity_of_cutoffLimitData
      φ v hdata

/--
%%handwave
name:
  Test-function form of gluing across two concentric spheres
statement:
  Under the weak derivative identities on the unit ball and on the annulus,
  under the matching \(L^1\) trace hypotheses on the two boundary spheres,
  and assuming the two global test pairings are integrable, every smooth
  compactly supported test function on the ambient space satisfies the global
  integration-by-parts identity for the piecewise glued function and the
  piecewise glued derivative field.
proof:
  Combine the assumed test-pairing integrability with
  [the collar-limit integration-by-parts identity](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_annulus_l1_trace_glue_test_identity).
-/
theorem euclideanSobolev_unit_ball_annulus_l1_trace_glue_test
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ} {du₀ du₁ : H → H →L[ℝ] ℝ}
    (hunit : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u₀ du₀)
    (hannulus : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H) u₁ du₁)
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    {τ : H → ℝ}
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction Set.univ)
    (v : H)
    (hτ_weight :
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v)
    (hleft_int : Integrable
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0))
      (MeasureTheory.volume.restrict Set.univ))
    (hright_int : Integrable
      (fun z : H ↦
        φ z •
          ((if ‖z‖ < 1 then
            du₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            du₁ z
          else
            0) v))
      (MeasureTheory.volume.restrict Set.univ)) :
    Integrable
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          (if ‖z‖ < 1 then
            u₀ z
          else if ‖z‖ < (3 / 2 : ℝ) then
            u₁ z
          else
            0))
      (MeasureTheory.volume.restrict Set.univ) ∧
      Integrable
        (fun z : H ↦
          φ z •
            ((if ‖z‖ < 1 then
              du₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              du₁ z
            else
              0) v))
        (MeasureTheory.volume.restrict Set.univ) ∧
        ∫ z in Set.univ,
            (fderiv ℝ (φ : H → ℝ) z v) •
              (if ‖z‖ < 1 then
                u₀ z
              else if ‖z‖ < (3 / 2 : ℝ) then
                u₁ z
              else
                0) ∂MeasureTheory.volume =
          -∫ z in Set.univ,
            φ z •
              ((if ‖z‖ < 1 then
                du₀ z
              else if ‖z‖ < (3 / 2 : ℝ) then
                du₁ z
              else
                0) v) ∂MeasureTheory.volume := by
  refine ⟨hleft_int, hright_int, ?_⟩
  exact
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_test_identity
      hunit hannulus hu₀_aesm hu₁_aesm _hinner₀ _hinner₁ _houter φ v
      hτ_weight hleft_int hright_int

/--
%%handwave
name:
  Gluing weak derivatives across two concentric spheres
statement:
  Let \(u_0\) have weak derivative \(du_0\) on the unit ball, and let \(u_1\)
  have weak derivative \(du_1\) on the annulus \(1<\|x\|<3/2\).  If the two
  functions have a common \(L^1\) trace on the unit sphere, the annular
  function has zero \(L^1\) trace on the sphere of radius \(3/2\), and the
  global test pairings for the glued function are integrable, then the
  function equal to \(u_0\) for \(\|x\|<1\), equal to \(u_1\) for
  \(1\le \|x\|<3/2\), and zero outside, has as weak derivative the analogous
  piecewise field.
proof:
  Apply
  [the test-function integration-by-parts identity for the piecewise glued
  function and derivative field](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_annulus_l1_trace_glue_test)
  to each smooth compactly supported test function and each constant
  direction.
-/
theorem euclideanSobolev_unit_ball_annulus_piecewise_glue_weakDerivative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u₀ u₁ : H → ℝ} {du₀ du₁ : H → H →L[ℝ] ℝ}
    (hunit : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) u₀ du₀)
    (hannulus : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H) u₁ du₁)
    (hu₀_aesm : AEStronglyMeasurable u₀
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hu₁_aesm : AEStronglyMeasurable u₁
      (MeasureTheory.volume.restrict
        (euclideanSobolevUnitBallReflectionAnnulus H)))
    (_hintegrable : ∀
      (φ : SmoothCompactlySupportedManifoldCoordinateFunction Set.univ)
      (v : H),
      Integrable
        (fun z : H ↦
          (fderiv ℝ (φ : H → ℝ) z v) •
            (if ‖z‖ < 1 then
              u₀ z
            else if ‖z‖ < (3 / 2 : ℝ) then
              u₁ z
            else
              0))
        (MeasureTheory.volume.restrict Set.univ) ∧
        Integrable
          (fun z : H ↦
            φ z •
              ((if ‖z‖ < 1 then
                du₀ z
              else if ‖z‖ < (3 / 2 : ℝ) then
                du₁ z
              else
                0) v))
          (MeasureTheory.volume.restrict Set.univ))
    {τ : H → ℝ}
    (_hinner₀ : HasL1TraceFromInsideSphere (H := H) 1 u₀ τ)
    (_hinner₁ : HasL1TraceFromOutsideSphere (H := H) 1 u₁ τ)
    (_houter : HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
      u₁ (fun _x : H ↦ 0))
    (_hτ_weight : ∀
      (φ : SmoothCompactlySupportedManifoldCoordinateFunction Set.univ)
      (v : H),
      EuclideanSobolevUnitSphereWeightedTraceIntegrable (H := H) τ φ v)
    :
    IsWeakDerivativeOnEuclideanRegionWithValues Set.univ
      (fun x : H ↦
        if ‖x‖ < 1 then
          u₀ x
        else if ‖x‖ < (3 / 2 : ℝ) then
          u₁ x
        else
          0)
      (fun x : H ↦
        if ‖x‖ < 1 then
          du₀ x
        else if ‖x‖ < (3 / 2 : ℝ) then
          du₁ x
        else
          0) := by
  intro φ v
  rcases _hintegrable φ v with ⟨hleft_int, hright_int⟩
  exact
    euclideanSobolev_unit_ball_annulus_l1_trace_glue_test
      hunit hannulus hu₀_aesm hu₁_aesm _hinner₀ _hinner₁ _houter φ v
      (_hτ_weight φ v) hleft_int hright_int

/--
%%handwave
name:
  Test-pairing integrability for the radial reflection extension
statement:
  The two global test pairings which occur in the weak derivative identity for
  the radial reflection extension are integrable for every smooth compactly
  supported test function and every constant direction.
-/
def euclideanSobolevUnitBallRadialReflectionGlueTestPairingsIntegrable
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H]
    (w : H → ℝ) (dw : H → H →L[ℝ] ℝ) : Prop :=
  ∀ (φ : SmoothCompactlySupportedManifoldCoordinateFunction Set.univ)
    (v : H),
    Integrable
      (fun z : H ↦
        (fderiv ℝ (φ : H → ℝ) z v) •
          euclideanSobolevUnitBallReflectionExtension w z)
      (MeasureTheory.volume.restrict Set.univ) ∧
      Integrable
        (fun z : H ↦
          φ z •
            (euclideanSobolevUnitBallRadialReflectionDerivativeExtension
              w dw z v))
        (MeasureTheory.volume.restrict Set.univ)

/--
%%handwave
name:
  Gluing the reflected weak derivative
statement:
  If \(w\in W^{1,2}\) on the unit ball and the weak derivative identity holds
  for the tapered reflected pullback on the annulus \(1<\|x\|<3/2\), then the
  piecewise reflected extension has the piecewise derivative field as a
  global weak derivative.
proof:
  Split every compactly supported test integral into the unit ball, the
  annulus, and the exterior of the closed ball of radius \(3/2\).  The exterior
  contribution vanishes because the extension and derivative field are zero
  there.  Across the unit sphere the reflected copy has the same \(L^1\) trace
  as the original function, and across the sphere of radius \(3/2\) the taper
  has zero \(L^1\) trace.  The two boundary spheres have measure zero by
  [Euclidean spheres have measure zero](lean:JJMath.Uniformization.euclidean_volume_sphere_zero),
  and the Sobolev gluing theorem across Lipschitz hypersurfaces supplies the
  global integration-by-parts identity.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_glue_weakDerivative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hunit : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hannulus : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H)
      (fun x : H ↦
        (3 - 2 * ‖x‖) * w (euclideanSobolevUnitBallRadialReflection x))
      (fun x : H ↦
        (3 - 2 * ‖x‖) •
            (dw (euclideanSobolevUnitBallRadialReflection x)).comp
              (fderiv ℝ (fun y : H ↦
                euclideanSobolevUnitBallRadialReflection y) x) +
          w (euclideanSobolevUnitBallRadialReflection x) •
            fderiv ℝ (fun y : H ↦ (3 : ℝ) - 2 * ‖y‖) x))
    (htest_integrable :
      euclideanSobolevUnitBallRadialReflectionGlueTestPairingsIntegrable
        w dw) :
    IsWeakDerivativeOnEuclideanRegionWithValues Set.univ
      (euclideanSobolevUnitBallReflectionExtension w)
      (euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw) := by
  let u₁ : H → ℝ := fun x : H ↦
    (3 - 2 * ‖x‖) * w (euclideanSobolevUnitBallRadialReflection x)
  let du₁ : H → H →L[ℝ] ℝ := fun x : H ↦
    (3 - 2 * ‖x‖) •
        (dw (euclideanSobolevUnitBallRadialReflection x)).comp
          (fderiv ℝ (fun y : H ↦
            euclideanSobolevUnitBallRadialReflection y) x) +
      w (euclideanSobolevUnitBallRadialReflection x) •
        fderiv ℝ (fun y : H ↦ (3 : ℝ) - 2 * ‖y‖) x
  rcases
    euclideanSobolev_unit_ball_radial_reflection_inner_trace_weighted_integrable
      hunit hw hdw with
    ⟨τ, hτ_weight, htrace_inner₀, htrace_inner₁⟩
  have htrace_outer :
      HasL1TraceFromInsideSphere (H := H) (3 / 2 : ℝ)
        u₁ (fun _x : H ↦ 0) := by
    simpa [u₁] using
      euclideanSobolev_unit_ball_radial_reflection_outer_trace_zero
        (H := H) (w := w) (_hw := hw)
  have htest_integrable' :
      ∀ (φ : SmoothCompactlySupportedManifoldCoordinateFunction Set.univ)
        (v : H),
        Integrable
          (fun z : H ↦
            (fderiv ℝ (φ : H → ℝ) z v) •
              (if ‖z‖ < 1 then
                w z
              else if ‖z‖ < (3 / 2 : ℝ) then
                u₁ z
              else
                0))
          (MeasureTheory.volume.restrict Set.univ) ∧
          Integrable
            (fun z : H ↦
              φ z •
                ((if ‖z‖ < 1 then
                  dw z
                else if ‖z‖ < (3 / 2 : ℝ) then
                  du₁ z
                else
                  0) v))
            (MeasureTheory.volume.restrict Set.univ) := by
    intro φ v
    rcases htest_integrable φ v with ⟨hleft, hright⟩
    refine ⟨?_, ?_⟩
    · simpa [u₁, euclideanSobolevUnitBallReflectionExtension,
        smul_eq_mul, Measure.restrict_univ] using hleft
    · simpa [du₁, euclideanSobolevUnitBallRadialReflectionDerivativeExtension,
        smul_eq_mul, Measure.restrict_univ] using hright
  have hu₁_aesm :
      AEStronglyMeasurable u₁
        (MeasureTheory.volume.restrict
          (euclideanSobolevUnitBallReflectionAnnulus H)) := by
    have hpull_mem :
        MemLp (fun x : H ↦ w (euclideanSobolevUnitBallRadialReflection x))
          2
          (MeasureTheory.volume.restrict
            (euclideanSobolevUnitBallReflectionAnnulus H)) :=
      euclideanSobolev_unit_ball_radial_reflection_annulus_pullback_memLp
        (H := H) hw
    have hscalar_cont :
        Continuous (fun x : H ↦ (3 : ℝ) - 2 * ‖x‖) := by
      fun_prop
    simpa [u₁, smul_eq_mul] using
      hscalar_cont.aestronglyMeasurable.mul hpull_mem.aestronglyMeasurable
  simpa [u₁, du₁, euclideanSobolevUnitBallReflectionExtension,
    euclideanSobolevUnitBallRadialReflectionDerivativeExtension] using
      euclideanSobolev_unit_ball_annulus_piecewise_glue_weakDerivative
        (u₀ := w) (u₁ := u₁) (du₀ := dw) (du₁ := du₁)
        hunit hannulus hw.aestronglyMeasurable hu₁_aesm htest_integrable'
        htrace_inner₀ htrace_inner₁ htrace_outer hτ_weight

private theorem memLp_two_add_eLpNorm_le_of_component_bounds
    {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {u v : α → E} {Cu Cv S : ℝ≥0∞}
    (hS_top : S < ⊤) (hCu_top : Cu < ⊤) (hCv_top : Cv < ⊤)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hu_bound : eLpNorm u 2 μ ≤ Cu * S)
    (hv_bound : eLpNorm v 2 μ ≤ Cv * S) :
    MemLp (u + v) 2 μ ∧
      eLpNorm (u + v) 2 μ ≤ (Cu + Cv) * S := by
  have huv_meas : AEStronglyMeasurable (u + v) μ :=
    hu.aestronglyMeasurable.add hv.aestronglyMeasurable
  have hbound :
      eLpNorm (u + v) 2 μ ≤ Cu * S + Cv * S := by
    calc
      eLpNorm (u + v) 2 μ
          ≤ eLpNorm u 2 μ + eLpNorm v 2 μ :=
            eLpNorm_add_le hu.aestronglyMeasurable hv.aestronglyMeasurable
              (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      _ ≤ Cu * S + Cv * S :=
          add_le_add hu_bound hv_bound
  have hbound_top : Cu * S + Cv * S < ⊤ :=
    ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top hCu_top hS_top,
        ENNReal.mul_lt_top hCv_top hS_top⟩
  refine ⟨⟨huv_meas, lt_of_le_of_lt hbound hbound_top⟩, ?_⟩
  calc
    eLpNorm (u + v) 2 μ ≤ Cu * S + Cv * S := hbound
    _ = (Cu + Cv) * S := by
        rw [add_mul]

/--
%%handwave
name:
  Interior value estimate for the radial reflection extension
statement:
  The interior contribution to the reflected extension is square integrable
  on the ambient space, and its \(L^2\)-norm is bounded by the original
  unit-ball graph norm.
proof:
  The interior part is the indicator of the unit ball times \(w\).  The
  \(L^2\)-norm of an indicator is the \(L^2\)-norm with respect to the
  restricted measure, so the bound follows immediately.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_extension_unit_graph_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    ∃ C : ℝ≥0∞,
      C < ⊤ ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues
              (Metric.ball (0 : H) 1) w dw →
            MemLp w 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp dw 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp (euclideanSobolevUnitBallReflectionExtensionUnitPart w)
              2 (MeasureTheory.volume : Measure H) ∧
              eLpNorm (euclideanSobolevUnitBallReflectionExtensionUnitPart w)
                  2 (MeasureTheory.volume : Measure H) ≤
                C * (eLpNorm w 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1)) +
                  eLpNorm dw 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1))) := by
  refine ⟨1, by simp, ?_⟩
  intro w dw _hweak hw _hdw
  let B : Set H := Metric.ball (0 : H) 1
  let μ : Measure H := MeasureTheory.volume
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hpart_eq :
      euclideanSobolevUnitBallReflectionExtensionUnitPart w =
        B.indicator w := by
    funext x
    by_cases hx : x ∈ B
    · have hxnorm : ‖x‖ < 1 := by
        simpa [B, Metric.mem_ball, dist_eq_norm] using hx
      simp [euclideanSobolevUnitBallReflectionExtensionUnitPart,
        B, hx, hxnorm]
    · have hxnorm : ¬ ‖x‖ < 1 := by
        intro hxnorm
        exact hx (by simpa [B, Metric.mem_ball, dist_eq_norm] using hxnorm)
      simp [euclideanSobolevUnitBallReflectionExtensionUnitPart,
        B, hx, hxnorm]
  have hpart_mem :
      MemLp (euclideanSobolevUnitBallReflectionExtensionUnitPart w)
        2 μ := by
    rw [hpart_eq]
    exact (memLp_indicator_iff_restrict (μ := μ) (p := (2 : ℝ≥0∞))
      (f := w) hB).2 (by simpa [B, μ] using hw)
  refine ⟨by simpa [μ] using hpart_mem, ?_⟩
  calc
    eLpNorm (euclideanSobolevUnitBallReflectionExtensionUnitPart w) 2 μ
        = eLpNorm (B.indicator w) 2 μ := by rw [hpart_eq]
    _ = eLpNorm w 2 (μ.restrict B) :=
        eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ)
          (p := (2 : ℝ≥0∞)) (f := w) hB
    _ ≤
        eLpNorm w 2 (μ.restrict B) +
          eLpNorm dw 2 (μ.restrict B) := by
        exact le_add_right le_rfl
    _ = (1 : ℝ≥0∞) *
        (eLpNorm w 2 (μ.restrict B) +
          eLpNorm dw 2 (μ.restrict B)) := by simp
    _ =
        (1 : ℝ≥0∞) *
        (eLpNorm w 2
            (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) +
          eLpNorm dw 2
            (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) := by
        simp [B, μ]

private theorem euclideanSobolev_unit_ball_radial_reflection_annulus_indicator_pullback_bound
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E] :
    ∃ C : ℝ≥0∞,
      C < ⊤ ∧
        ∀ {f : H → E},
          MemLp f 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp
              ((euclideanSobolevUnitBallReflectionAnnulus H).indicator
                (fun z : H ↦ f (euclideanSobolevUnitBallRadialReflection z)))
              2 (MeasureTheory.volume : Measure H) ∧
              eLpNorm
                  ((euclideanSobolevUnitBallReflectionAnnulus H).indicator
                    (fun z : H ↦ f
                      (euclideanSobolevUnitBallRadialReflection z)))
                  2 (MeasureTheory.volume : Measure H) ≤
                C * eLpNorm f 2
                  (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
  let U : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let Ω₀ : Set H := euclideanSobolevUnitBallPunctured H
  let B : Set H := Metric.ball (0 : H) 1
  let R : H → H := euclideanSobolevUnitBallRadialReflection
  let μ : Measure H := MeasureTheory.volume
  have hR_meas : Measurable R := by
    simpa [R] using euclideanSobolevUnitBallRadialReflection_measurable
      (H := H)
  rcases
    map_restrict_le_smul_of_inverse_lipschitzOnWith
      (U := U) (Ω := Ω₀) (T := R) (S := R)
      (L := (12 : ℝ≥0))
      hR_meas
      (by
        simpa [U, Ω₀, R] using
          euclideanSobolevUnitBallRadialReflection_mapsTo_annulus_punctured
            (H := H))
      (by
        intro x hx
        simpa [U, R] using
          euclideanSobolevUnitBallRadialReflection_involutive_on_annulus
            (H := H) (x := x) hx)
      (by
        simpa [Ω₀, R] using
          euclideanSobolevUnitBallRadialReflection_lipschitzOnWith_punctured
            (H := H)) with
    ⟨D, hD_ne_top, hmap_le⟩
  let A : ℝ≥0∞ := D ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  have hA_ne_top : A ≠ ⊤ := by
    dsimp [A]
    exact ENNReal.rpow_ne_top_of_nonneg
      (by positivity :
        0 ≤ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal)
      hD_ne_top
  refine ⟨A, lt_top_iff_ne_top.mpr hA_ne_top, ?_⟩
  intro f hf
  have hΩ₀_subset : Ω₀ ⊆ B := by
    simpa [Ω₀, B] using
      euclideanSobolevUnitBallPunctured_subset_unit_ball (H := H)
  have hmeasure_le : μ.restrict Ω₀ ≤ μ.restrict B :=
    Measure.restrict_mono_set μ hΩ₀_subset
  have hfΩ₀ : MemLp f 2 (μ.restrict Ω₀) :=
    hf.mono_measure (by simpa [μ, B] using hmeasure_le)
  have hmap_le' :
      Measure.map R (μ.restrict U) ≤ D • μ.restrict Ω₀ := by
    simpa [μ] using hmap_le
  have hf_map : MemLp f 2 (Measure.map R (μ.restrict U)) :=
    hfΩ₀.of_measure_le_smul hD_ne_top hmap_le'
  have hR_aemeas_U : AEMeasurable R (μ.restrict U) :=
    hR_meas.aemeasurable
  have hcomp_mem : MemLp (fun z : H ↦ f (R z)) 2 (μ.restrict U) := by
    simpa [Function.comp_def, R] using
      hf_map.comp_of_map hR_aemeas_U
  have hmap_ac :
      Measure.map R (μ.restrict U) ≪ μ.restrict Ω₀ :=
    Measure.absolutelyContinuous_of_le_smul hmap_le'
  have hcomp_bound :
      eLpNorm (fun z : H ↦ f (R z)) 2 (μ.restrict U) ≤
        A * eLpNorm f 2 (μ.restrict B) := by
    have hf_map_aesm :
        AEStronglyMeasurable f (Measure.map R (μ.restrict U)) :=
      hfΩ₀.aestronglyMeasurable.mono_ac hmap_ac
    calc
      eLpNorm (fun z : H ↦ f (R z)) 2 (μ.restrict U)
          = eLpNorm f 2 (Measure.map R (μ.restrict U)) := by
            exact (eLpNorm_map_measure hf_map_aesm hR_aemeas_U).symm
      _ ≤ eLpNorm f 2 (D • μ.restrict Ω₀) :=
            eLpNorm_mono_measure f hmap_le'
      _ = A * eLpNorm f 2 (μ.restrict Ω₀) := by
            dsimp [A]
            rw [eLpNorm_smul_measure_of_ne_top
              (show (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) from ENNReal.coe_ne_top),
              smul_eq_mul]
      _ ≤ A * eLpNorm f 2 (μ.restrict B) :=
            mul_le_mul_right (eLpNorm_mono_measure f hmeasure_le) A
  have hU_meas : MeasurableSet U :=
    (euclideanSobolevUnitBallReflectionAnnulus_isOpen (H := H)).measurableSet
  let pull : H → E := U.indicator (fun z : H ↦ f (R z))
  have hpull_mem : MemLp pull 2 μ := by
    exact (memLp_indicator_iff_restrict (μ := μ) (p := (2 : ℝ≥0∞))
      (f := fun z : H ↦ f (R z)) hU_meas).2
        (by simpa [pull] using hcomp_mem)
  refine ⟨by simpa [pull, U, R, μ] using hpull_mem, ?_⟩
  calc
    eLpNorm
        ((euclideanSobolevUnitBallReflectionAnnulus H).indicator
          (fun z : H ↦ f (euclideanSobolevUnitBallRadialReflection z)))
        2 μ
        = eLpNorm pull 2 μ := by
          simp [pull, U, R]
    _ = eLpNorm (fun z : H ↦ f (R z)) 2 (μ.restrict U) := by
          simpa [pull] using
            eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ)
              (p := (2 : ℝ≥0∞)) (f := fun z : H ↦ f (R z))
              hU_meas
    _ ≤ A * eLpNorm f 2 (μ.restrict B) := hcomp_bound
    _ =
        A * eLpNorm f 2
          (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
        simp [μ, B]

/--
%%handwave
name:
  Annular value estimate for the radial reflection extension
statement:
  The annular reflected contribution to the extension is square integrable
  on the ambient space, and its \(L^2\)-norm is bounded by a finite multiple
  of the original unit-ball graph norm.
proof:
  On the annulus \(1\le\|x\|<3/2\), radial reflection maps into the inner
  shell \(1/2<\|x\|<1\).  The taper is uniformly bounded and the
  change-of-variables density is uniformly controlled on this shell, so the
  annular \(L^2\)-norm is bounded by the \(L^2\)-norm of \(w\) on the unit
  ball.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_extension_annulus_graph_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    ∃ C : ℝ≥0∞,
      C < ⊤ ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues
              (Metric.ball (0 : H) 1) w dw →
            MemLp w 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp dw 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp (euclideanSobolevUnitBallReflectionExtensionAnnulusPart w)
              2 (MeasureTheory.volume : Measure H) ∧
              eLpNorm (euclideanSobolevUnitBallReflectionExtensionAnnulusPart w)
                  2 (MeasureTheory.volume : Measure H) ≤
                C * (eLpNorm w 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1)) +
                  eLpNorm dw 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1))) := by
  let U : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let Ω₀ : Set H := euclideanSobolevUnitBallPunctured H
  let B : Set H := Metric.ball (0 : H) 1
  let R : H → H := euclideanSobolevUnitBallRadialReflection
  let μ : Measure H := MeasureTheory.volume
  have hR_meas : Measurable R := by
    simpa [R] using euclideanSobolevUnitBallRadialReflection_measurable
      (H := H)
  rcases
    map_restrict_le_smul_of_inverse_lipschitzOnWith
      (U := U) (Ω := Ω₀) (T := R) (S := R)
      (L := (12 : ℝ≥0))
      hR_meas
      (by
        simpa [U, Ω₀, R] using
          euclideanSobolevUnitBallRadialReflection_mapsTo_annulus_punctured
            (H := H))
      (by
        intro x hx
        simpa [U, R] using
          euclideanSobolevUnitBallRadialReflection_involutive_on_annulus
            (H := H) (x := x) hx)
      (by
        simpa [Ω₀, R] using
          euclideanSobolevUnitBallRadialReflection_lipschitzOnWith_punctured
            (H := H)) with
    ⟨D, hD_ne_top, hmap_le⟩
  let A : ℝ≥0∞ := D ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  have hA_ne_top : A ≠ ⊤ := by
    dsimp [A]
    exact ENNReal.rpow_ne_top_of_nonneg
      (by positivity :
        0 ≤ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal)
      hD_ne_top
  refine ⟨A, lt_top_iff_ne_top.mpr hA_ne_top, ?_⟩
  intro w dw _hweak hw _hdw
  have hΩ₀_subset : Ω₀ ⊆ B := by
    simpa [Ω₀, B] using
      euclideanSobolevUnitBallPunctured_subset_unit_ball (H := H)
  have hmeasure_le : μ.restrict Ω₀ ≤ μ.restrict B := by
    exact Measure.restrict_mono_set μ hΩ₀_subset
  have hwΩ₀ : MemLp w 2 (μ.restrict Ω₀) :=
    hw.mono_measure (by simpa [μ, B] using hmeasure_le)
  have hmap_le' :
      Measure.map R (μ.restrict U) ≤ D • μ.restrict Ω₀ := by
    simpa [μ] using hmap_le
  have hw_map : MemLp w 2 (Measure.map R (μ.restrict U)) :=
    hwΩ₀.of_measure_le_smul hD_ne_top hmap_le'
  have hR_aemeas_U : AEMeasurable R (μ.restrict U) :=
    hR_meas.aemeasurable
  have hcomp_mem : MemLp (fun z : H ↦ w (R z)) 2 (μ.restrict U) := by
    simpa [Function.comp_def, R] using
      hw_map.comp_of_map hR_aemeas_U
  have hmap_ac :
      Measure.map R (μ.restrict U) ≪ μ.restrict Ω₀ :=
    Measure.absolutelyContinuous_of_le_smul hmap_le'
  have hcomp_bound :
      eLpNorm (fun z : H ↦ w (R z)) 2 (μ.restrict U) ≤
        A * eLpNorm w 2 (μ.restrict B) := by
    have hw_map_aesm :
        AEStronglyMeasurable w (Measure.map R (μ.restrict U)) :=
      hwΩ₀.aestronglyMeasurable.mono_ac hmap_ac
    calc
      eLpNorm (fun z : H ↦ w (R z)) 2 (μ.restrict U)
          = eLpNorm w 2 (Measure.map R (μ.restrict U)) := by
            exact (eLpNorm_map_measure hw_map_aesm hR_aemeas_U).symm
      _ ≤ eLpNorm w 2 (D • μ.restrict Ω₀) :=
            eLpNorm_mono_measure w hmap_le'
      _ = A * eLpNorm w 2 (μ.restrict Ω₀) := by
            dsimp [A]
            rw [eLpNorm_smul_measure_of_ne_top
              (show (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) from ENNReal.coe_ne_top),
              smul_eq_mul]
      _ ≤ A * eLpNorm w 2 (μ.restrict B) :=
            mul_le_mul_right (eLpNorm_mono_measure w hmeasure_le) A
  have hU_meas : MeasurableSet U :=
    (euclideanSobolevUnitBallReflectionAnnulus_isOpen (H := H)).measurableSet
  let pull : H → ℝ := U.indicator (fun z : H ↦ w (R z))
  have hpull_mem : MemLp pull 2 μ := by
    exact (memLp_indicator_iff_restrict (μ := μ) (p := (2 : ℝ≥0∞))
      (f := fun z : H ↦ w (R z)) hU_meas).2
        (by simpa [pull] using hcomp_mem)
  have hpull_bound :
      eLpNorm pull 2 μ ≤ A * eLpNorm w 2 (μ.restrict B) := by
    calc
      eLpNorm pull 2 μ
          = eLpNorm (fun z : H ↦ w (R z)) 2 (μ.restrict U) := by
            simpa [pull] using
              eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ)
                (p := (2 : ℝ≥0∞)) (f := fun z : H ↦ w (R z))
                hU_meas
      _ ≤ A * eLpNorm w 2 (μ.restrict B) := hcomp_bound
  let prod : H → ℝ := fun x : H ↦ (3 - 2 * ‖x‖) * pull x
  have hscalar_aesm :
      AEStronglyMeasurable (fun x : H ↦ (3 : ℝ) - 2 * ‖x‖) μ := by
    measurability
  have hprod_aesm : AEStronglyMeasurable prod μ := by
    change AEStronglyMeasurable
      (fun x : H ↦ ((3 : ℝ) - 2 * ‖x‖) * pull x) μ
    exact hscalar_aesm.mul hpull_mem.aestronglyMeasurable
  have hprod_point :
      ∀ᵐ x ∂μ, ‖prod x‖ ≤ (1 : ℝ) * ‖pull x‖ := by
    filter_upwards [] with x
    by_cases hxU : x ∈ U
    · have hxU' : (1 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ) := by
        simpa [U, euclideanSobolevUnitBallReflectionAnnulus] using hxU
      have htaper_nonneg : 0 ≤ (3 : ℝ) - 2 * ‖x‖ := by
        linarith [hxU'.2]
      have htaper_le_one : (3 : ℝ) - 2 * ‖x‖ ≤ 1 := by
        linarith [hxU'.1]
      have htaper_abs : |(3 : ℝ) - 2 * ‖x‖| ≤ 1 := by
        rw [abs_of_nonneg htaper_nonneg]
        exact htaper_le_one
      calc
        ‖prod x‖ = |(3 : ℝ) - 2 * ‖x‖| * ‖pull x‖ := by
          simp [prod, norm_mul, Real.norm_eq_abs]
        _ ≤ 1 * ‖pull x‖ :=
          mul_le_mul_of_nonneg_right htaper_abs (norm_nonneg _)
    · have hpull_zero : pull x = 0 := by
        simp [pull, hxU]
      simp [prod, hpull_zero]
  have hprod_mem : MemLp prod 2 μ :=
    MemLp.of_le_mul hpull_mem hprod_aesm hprod_point
  have hprod_bound :
      eLpNorm prod 2 μ ≤ eLpNorm pull 2 μ := by
    calc
      eLpNorm prod 2 μ
          ≤ ENNReal.ofReal (1 : ℝ) * eLpNorm pull 2 μ :=
            eLpNorm_le_mul_eLpNorm_of_ae_le_mul hprod_point 2
      _ = eLpNorm pull 2 μ := by simp
  have hsphere_zero : μ {x : H | ‖x‖ = 1} = 0 := by
    have hs :=
      euclidean_volume_sphere_zero (H := H) (c := (0 : H)) (r := (1 : ℝ))
        (by norm_num)
    simpa [μ, Metric.sphere, dist_eq_norm] using hs
  have hprod_eq_part :
      prod =ᵐ[μ] euclideanSobolevUnitBallReflectionExtensionAnnulusPart w := by
    filter_upwards [compl_mem_ae_iff.mpr hsphere_zero] with x hx_not_sphere
    have hnorm_ne : ‖x‖ ≠ (1 : ℝ) := by
      simpa using hx_not_sphere
    by_cases hxU : x ∈ U
    · have hxU' : (1 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ) := by
        simpa [U, euclideanSobolevUnitBallReflectionAnnulus] using hxU
      have hclosed : 1 ≤ ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ) :=
        ⟨hxU'.1.le, hxU'.2⟩
      simp [prod, pull, U, R,
        euclideanSobolevUnitBallReflectionExtensionAnnulusPart,
        hxU, hclosed]
    · have hclosed_false :
          ¬ (1 ≤ ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)) := by
        intro hclosed
        have hnot_lt : ¬ (1 : ℝ) < ‖x‖ := by
          intro hlt
          exact hxU (by
            simpa [U, euclideanSobolevUnitBallReflectionAnnulus] using
              (And.intro hlt hclosed.2))
        have hle : ‖x‖ ≤ (1 : ℝ) := not_lt.mp hnot_lt
        have heq : ‖x‖ = (1 : ℝ) := le_antisymm hle hclosed.1
        exact hnorm_ne heq
      simp [prod, pull, U, R,
        euclideanSobolevUnitBallReflectionExtensionAnnulusPart,
        hxU, hclosed_false]
  have hpart_mem :
      MemLp (euclideanSobolevUnitBallReflectionExtensionAnnulusPart w) 2 μ :=
    MemLp.ae_eq hprod_eq_part hprod_mem
  refine ⟨by simpa [μ] using hpart_mem, ?_⟩
  calc
    eLpNorm (euclideanSobolevUnitBallReflectionExtensionAnnulusPart w) 2 μ
        = eLpNorm prod 2 μ := by
          exact (eLpNorm_congr_ae hprod_eq_part).symm
    _ ≤ eLpNorm pull 2 μ := hprod_bound
    _ ≤ A * eLpNorm w 2 (μ.restrict B) := hpull_bound
    _ ≤ A * (eLpNorm w 2 (μ.restrict B) +
          eLpNorm dw 2 (μ.restrict B)) :=
        mul_le_mul_right (le_add_right le_rfl) A
    _ =
        A * (eLpNorm w 2
            (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) +
          eLpNorm dw 2
            (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) := by
        simp [μ, B]

/--
%%handwave
name:
  Value estimate for the radial reflection extension
statement:
  For Sobolev pairs on the Euclidean unit ball, the \(L^2\)-norm of the
  reflected extension is bounded by a finite multiple of the original
  \(W^{1,2}\) graph norm on the ball.
proof:
  Split the extension into the unit ball, annulus, and exterior.  The exterior
  contribution is zero.  On the unit ball the extension is the original
  function.  On the annulus, the reflected copy lands in the inner shell
  \(1/2<\|x\|<1\), the taper is uniformly bounded, and the
  change-of-variables density is uniformly controlled.  Combine the two
  piecewise \(L^2\)-estimates with the triangle inequality.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_extension_value_graph_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    ∃ C : ℝ≥0∞,
      C < ⊤ ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues
              (Metric.ball (0 : H) 1) w dw →
            MemLp w 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp dw 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp (euclideanSobolevUnitBallReflectionExtension w) 2
              (MeasureTheory.volume : Measure H) ∧
              eLpNorm (euclideanSobolevUnitBallReflectionExtension w) 2
                  (MeasureTheory.volume : Measure H) ≤
                C * (eLpNorm w 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1)) +
                  eLpNorm dw 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1))) := by
  rcases
      euclideanSobolev_unit_ball_radial_reflection_extension_unit_graph_bound
        (H := H) with
    ⟨Cunit, hCunit_top, hUnit⟩
  rcases
      euclideanSobolev_unit_ball_radial_reflection_extension_annulus_graph_bound
        (H := H) with
    ⟨Cann, hCann_top, hAnn⟩
  refine
    ⟨Cunit + Cann, ENNReal.add_lt_top.2 ⟨hCunit_top, hCann_top⟩, ?_⟩
  intro w dw hweak hw hdw
  let μ : Measure H := MeasureTheory.volume
  let S : ℝ≥0∞ :=
    eLpNorm w 2
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) +
      eLpNorm dw 2
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))
  let U : H → ℝ :=
    euclideanSobolevUnitBallReflectionExtensionUnitPart w
  let A : H → ℝ :=
    euclideanSobolevUnitBallReflectionExtensionAnnulusPart w
  rcases hUnit hweak hw hdw with ⟨hU_mem, hU_bound⟩
  rcases hAnn hweak hw hdw with ⟨hA_mem, hA_bound⟩
  have hU_mem' : MemLp U 2 μ := by
    simpa [U, μ] using hU_mem
  have hA_mem' : MemLp A 2 μ := by
    simpa [A, μ] using hA_mem
  have hU_bound' : eLpNorm U 2 μ ≤ Cunit * S := by
    simpa [U, μ, S] using hU_bound
  have hA_bound' : eLpNorm A 2 μ ≤ Cann * S := by
    simpa [A, μ, S] using hA_bound
  have hparts_eq :
      euclideanSobolevUnitBallReflectionExtension w = U + A := by
    simpa [U, A, Pi.add_apply] using
      euclideanSobolevUnitBallReflectionExtension_eq_parts w
  have hS_top : S < ⊤ := by
    dsimp [S]
    exact ENNReal.add_lt_top.2 ⟨hw.2, hdw.2⟩
  have hsum :
      MemLp (U + A) 2 μ ∧
        eLpNorm (U + A) 2 μ ≤ (Cunit + Cann) * S :=
    memLp_two_add_eLpNorm_le_of_component_bounds
      (α := H) (E := ℝ) (μ := μ)
      (u := U) (v := A)
      (Cu := Cunit) (Cv := Cann) (S := S)
      hS_top hCunit_top hCann_top
      hU_mem' hA_mem' hU_bound' hA_bound'
  have hvalue_mem :
      MemLp (euclideanSobolevUnitBallReflectionExtension w) 2 μ := by
    rw [hparts_eq]
    exact hsum.1
  refine ⟨by simpa [μ] using hvalue_mem, ?_⟩
  calc
    eLpNorm (euclideanSobolevUnitBallReflectionExtension w) 2 μ
        = eLpNorm (U + A) 2 μ := by
          rw [hparts_eq]
    _ ≤ (Cunit + Cann) * S := hsum.2
    _ =
        (Cunit + Cann) *
          (eLpNorm w 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) +
            eLpNorm dw 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) := by
        simp [S]

/--
%%handwave
name:
  Interior derivative estimate for the radial reflection extension
statement:
  The interior contribution to the derivative field is square integrable on
  the ambient space, and its \(L^2\)-norm is bounded by the original
  unit-ball graph norm.
proof:
  The interior part is the indicator of the unit ball times \(dw\).  The
  \(L^2\)-norm of an indicator is the \(L^2\)-norm with respect to the
  restricted measure, so the bound follows immediately.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_derivative_unit_part_graph_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    ∃ C : ℝ≥0∞,
      C < ⊤ ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues
              (Metric.ball (0 : H) 1) w dw →
            MemLp w 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp dw 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp
              (euclideanSobolevUnitBallRadialReflectionDerivativeUnitPart dw)
              2 (MeasureTheory.volume : Measure H) ∧
              eLpNorm
                  (euclideanSobolevUnitBallRadialReflectionDerivativeUnitPart dw)
                  2 (MeasureTheory.volume : Measure H) ≤
                C * (eLpNorm w 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1)) +
                  eLpNorm dw 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1))) := by
  refine ⟨1, by simp, ?_⟩
  intro w dw _hweak _hw hdw
  let B : Set H := Metric.ball (0 : H) 1
  let μ : Measure H := MeasureTheory.volume
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hpart_eq :
      euclideanSobolevUnitBallRadialReflectionDerivativeUnitPart dw =
        B.indicator dw := by
    funext x
    by_cases hx : x ∈ B
    · have hxnorm : ‖x‖ < 1 := by
        simpa [B, Metric.mem_ball, dist_eq_norm] using hx
      simp [euclideanSobolevUnitBallRadialReflectionDerivativeUnitPart,
        B, hx, hxnorm]
    · have hxnorm : ¬ ‖x‖ < 1 := by
        intro hxnorm
        exact hx (by simpa [B, Metric.mem_ball, dist_eq_norm] using hxnorm)
      simp [euclideanSobolevUnitBallRadialReflectionDerivativeUnitPart,
        B, hx, hxnorm]
  have hpart_mem :
      MemLp (euclideanSobolevUnitBallRadialReflectionDerivativeUnitPart dw)
        2 μ := by
    rw [hpart_eq]
    exact (memLp_indicator_iff_restrict (μ := μ) (p := (2 : ℝ≥0∞))
      (f := dw) hB).2 (by simpa [B, μ] using hdw)
  refine ⟨by simpa [μ] using hpart_mem, ?_⟩
  calc
    eLpNorm (euclideanSobolevUnitBallRadialReflectionDerivativeUnitPart dw)
        2 μ
        = eLpNorm (B.indicator dw) 2 μ := by rw [hpart_eq]
    _ = eLpNorm dw 2 (μ.restrict B) :=
        eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ)
          (p := (2 : ℝ≥0∞)) (f := dw) hB
    _ ≤
        eLpNorm w 2 (μ.restrict B) +
          eLpNorm dw 2 (μ.restrict B) := by
        exact le_add_left le_rfl
    _ = (1 : ℝ≥0∞) *
        (eLpNorm w 2 (μ.restrict B) +
          eLpNorm dw 2 (μ.restrict B)) := by simp
    _ =
        (1 : ℝ≥0∞) *
        (eLpNorm w 2
            (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) +
          eLpNorm dw 2
            (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) := by
        simp [B, μ]

private theorem euclideanSobolev_unit_ball_taper_fderiv_norm_le_two
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : H) :
    ‖fderiv ℝ (fun y : H ↦ (3 : ℝ) - 2 * ‖y‖) x‖ ≤ (2 : ℝ) := by
  let τ : H → ℝ := fun y : H ↦ (3 : ℝ) - 2 * ‖y‖
  have hτ_lip : LipschitzOnWith (2 : ℝ≥0) τ Set.univ := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro y _ z _
    have hdiff :
        τ y - τ z = -2 * (‖y‖ - ‖z‖) := by
      dsimp [τ]
      ring
    calc
      dist (τ y) (τ z)
          = |τ y - τ z| := by
            rw [Real.dist_eq]
      _ = 2 * |‖y‖ - ‖z‖| := by
            rw [hdiff, abs_mul, abs_neg,
              abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * ‖y - z‖ :=
            mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le y z)
              (by norm_num : (0 : ℝ) ≤ 2)
      _ = (2 : ℝ≥0) * dist y z := by
            rw [dist_eq_norm]
            norm_num
  simpa [τ] using
    norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ)
      (x₀ := x) (s := (Set.univ : Set H)) Filter.univ_mem hτ_lip

private theorem euclideanSobolevUnitBallRadialReflection_fderiv_norm_le_five_on_annulus
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x : H}
    (hx : x ∈ euclideanSobolevUnitBallReflectionAnnulus H) :
    ‖fderiv ℝ (fun y : H ↦ euclideanSobolevUnitBallRadialReflection y) x‖
      ≤ (5 : ℝ) := by
  have hU_nhds :
      euclideanSobolevUnitBallReflectionAnnulus H ∈ 𝓝 x :=
    (euclideanSobolevUnitBallReflectionAnnulus_isOpen (H := H)).mem_nhds hx
  simpa using
    norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ)
      (x₀ := x) (s := euclideanSobolevUnitBallReflectionAnnulus H)
      hU_nhds
      (euclideanSobolevUnitBallRadialReflection_lipschitzOnWith_annulus
        (H := H))

/--
%%handwave
name:
  Chain-rule derivative estimate on the reflected annulus
statement:
  The annular term obtained by pulling back \(dw\) through radial reflection
  has \(L^2\)-norm bounded by a finite multiple of the original unit-ball
  graph norm.
proof:
  On the annulus \(1\le\|x\|<3/2\), the radial reflection maps into the
  inner shell \(1/2<\|x\|<1\).  The taper, the differential of the reflection,
  and the change-of-variables density are uniformly bounded there.  Hence the
  annular \(L^2\)-norm is bounded by the \(L^2\)-norm of \(dw\) on the unit
  ball.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_derivative_annulus_chain_graph_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    ∃ C : ℝ≥0∞,
      C < ⊤ ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues
              (Metric.ball (0 : H) 1) w dw →
            MemLp w 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp dw 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp
              (euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusChainPart
                dw)
              2 (MeasureTheory.volume : Measure H) ∧
              eLpNorm
                  (euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusChainPart
                    dw)
                  2 (MeasureTheory.volume : Measure H) ≤
                C * (eLpNorm w 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1)) +
                  eLpNorm dw 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1))) := by
  rcases
    euclideanSobolev_unit_ball_radial_reflection_annulus_indicator_pullback_bound
      (H := H) (E := H →L[ℝ] ℝ) with
    ⟨Cpull, hCpull_top, hPull⟩
  let C : ℝ≥0∞ := ENNReal.ofReal (5 : ℝ) * Cpull
  have hC_top : C < ⊤ := by
    dsimp [C]
    exact ENNReal.mul_lt_top (by simp) hCpull_top
  refine ⟨C, hC_top, ?_⟩
  intro w dw _hweak _hw hdw
  let U : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let B : Set H := Metric.ball (0 : H) 1
  let R : H → H := euclideanSobolevUnitBallRadialReflection
  let μ : Measure H := MeasureTheory.volume
  let pull : H → H →L[ℝ] ℝ := U.indicator (fun z : H ↦ dw (R z))
  rcases hPull (f := dw) hdw with ⟨hpull_mem₀, hpull_bound₀⟩
  have hpull_mem : MemLp pull 2 μ := by
    simpa [pull, U, R, μ] using hpull_mem₀
  have hpull_bound :
      eLpNorm pull 2 μ ≤
        Cpull * eLpNorm dw 2 (μ.restrict B) := by
    simpa [pull, U, R, μ, B] using hpull_bound₀
  let raw : H → H →L[ℝ] ℝ :=
    fun x : H ↦
      (3 - 2 * ‖x‖) •
        (pull x).comp
          (fderiv ℝ (fun y : H ↦ euclideanSobolevUnitBallRadialReflection y) x)
  have hscalar_aesm :
      AEStronglyMeasurable (fun x : H ↦ (3 : ℝ) - 2 * ‖x‖) μ := by
    measurability
  have hDR_aesm :
      AEStronglyMeasurable
        (fun x : H ↦
          fderiv ℝ
            (fun y : H ↦ euclideanSobolevUnitBallRadialReflection y) x) μ :=
    (measurable_fderiv ℝ
      (fun y : H ↦ euclideanSobolevUnitBallRadialReflection y)).aestronglyMeasurable
  let compCLM :
      (H →L[ℝ] ℝ) →L[ℝ] (H →L[ℝ] H) →L[ℝ] H →L[ℝ] ℝ :=
    ContinuousLinearMap.compL ℝ H H ℝ
  have hcomp_aesm :
      AEStronglyMeasurable
        (fun x : H ↦
          (pull x).comp
            (fderiv ℝ
              (fun y : H ↦ euclideanSobolevUnitBallRadialReflection y) x)) μ := by
    simpa [compCLM] using
      compCLM.aestronglyMeasurable_comp₂
        hpull_mem.aestronglyMeasurable hDR_aesm
  have hraw_aesm : AEStronglyMeasurable raw μ := by
    change AEStronglyMeasurable
      (fun x : H ↦
        ((3 : ℝ) - 2 * ‖x‖) •
          (pull x).comp
            (fderiv ℝ
              (fun y : H ↦ euclideanSobolevUnitBallRadialReflection y) x)) μ
    exact hscalar_aesm.smul hcomp_aesm
  have hraw_point :
      ∀ᵐ x ∂μ, ‖raw x‖ ≤ (5 : ℝ) * ‖pull x‖ := by
    filter_upwards [] with x
    by_cases hxU : x ∈ U
    · have hxU' : (1 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ) := by
        simpa [U, euclideanSobolevUnitBallReflectionAnnulus] using hxU
      have htaper_nonneg : 0 ≤ (3 : ℝ) - 2 * ‖x‖ := by
        linarith [hxU'.2]
      have htaper_le_one : (3 : ℝ) - 2 * ‖x‖ ≤ 1 := by
        linarith [hxU'.1]
      have htaper_abs : |(3 : ℝ) - 2 * ‖x‖| ≤ 1 := by
        rw [abs_of_nonneg htaper_nonneg]
        exact htaper_le_one
      have hDR :
          ‖fderiv ℝ
              (fun y : H ↦ euclideanSobolevUnitBallRadialReflection y) x‖
            ≤ (5 : ℝ) := by
        simpa [U] using
          euclideanSobolevUnitBallRadialReflection_fderiv_norm_le_five_on_annulus
            (H := H) (x := x) hxU
      have hcomp_norm :
          ‖(pull x).comp
              (fderiv ℝ
                (fun y : H ↦ euclideanSobolevUnitBallRadialReflection y) x)‖
            ≤ ‖pull x‖ *
                ‖fderiv ℝ
                  (fun y : H ↦ euclideanSobolevUnitBallRadialReflection y) x‖ :=
        (pull x).opNorm_comp_le
          (fderiv ℝ
            (fun y : H ↦ euclideanSobolevUnitBallRadialReflection y) x)
      calc
        ‖raw x‖ =
            |(3 : ℝ) - 2 * ‖x‖| *
              ‖(pull x).comp
                (fderiv ℝ
                  (fun y : H ↦ euclideanSobolevUnitBallRadialReflection y) x)‖ := by
          simp [raw, norm_smul, Real.norm_eq_abs]
        _ ≤ 1 *
              ‖(pull x).comp
                (fderiv ℝ
                  (fun y : H ↦ euclideanSobolevUnitBallRadialReflection y) x)‖ :=
          mul_le_mul_of_nonneg_right htaper_abs (norm_nonneg _)
        _ ≤ ‖pull x‖ * 5 := by
          simpa using
            le_trans hcomp_norm
              (mul_le_mul_of_nonneg_left hDR (norm_nonneg _))
        _ = (5 : ℝ) * ‖pull x‖ := by ring
    · have hpull_zero : pull x = 0 := by
        simp [pull, hxU]
      simp [raw, hpull_zero]
  have hraw_mem : MemLp raw 2 μ :=
    MemLp.of_le_mul hpull_mem hraw_aesm hraw_point
  have hraw_bound :
      eLpNorm raw 2 μ ≤ ENNReal.ofReal (5 : ℝ) * eLpNorm pull 2 μ :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hraw_point 2
  have hsphere_zero : μ {x : H | ‖x‖ = 1} = 0 := by
    have hs :=
      euclidean_volume_sphere_zero (H := H) (c := (0 : H)) (r := (1 : ℝ))
        (by norm_num)
    simpa [μ, Metric.sphere, dist_eq_norm] using hs
  have hraw_eq_part :
      raw =ᵐ[μ]
        euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusChainPart dw := by
    filter_upwards [compl_mem_ae_iff.mpr hsphere_zero] with x hx_not_sphere
    have hnorm_ne : ‖x‖ ≠ (1 : ℝ) := by
      simpa using hx_not_sphere
    by_cases hxU : x ∈ U
    · have hxU' : (1 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ) := by
        simpa [U, euclideanSobolevUnitBallReflectionAnnulus] using hxU
      have hclosed : 1 ≤ ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ) :=
        ⟨hxU'.1.le, hxU'.2⟩
      simp [raw, pull, U, R,
        euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusChainPart,
        hxU, hclosed]
    · have hclosed_false :
          ¬ (1 ≤ ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)) := by
        intro hclosed
        have hnot_lt : ¬ (1 : ℝ) < ‖x‖ := by
          intro hlt
          exact hxU (by
            simpa [U, euclideanSobolevUnitBallReflectionAnnulus] using
              (And.intro hlt hclosed.2))
        have hle : ‖x‖ ≤ (1 : ℝ) := not_lt.mp hnot_lt
        have heq : ‖x‖ = (1 : ℝ) := le_antisymm hle hclosed.1
        exact hnorm_ne heq
      simp [raw, pull, U, R,
        euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusChainPart,
        hxU, hclosed_false]
  have hpart_mem :
      MemLp
        (euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusChainPart dw)
        2 μ :=
    MemLp.ae_eq hraw_eq_part hraw_mem
  refine ⟨by simpa [μ] using hpart_mem, ?_⟩
  calc
    eLpNorm
        (euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusChainPart dw)
        2 μ
        = eLpNorm raw 2 μ := by
          exact (eLpNorm_congr_ae hraw_eq_part).symm
    _ ≤ ENNReal.ofReal (5 : ℝ) * eLpNorm pull 2 μ := hraw_bound
    _ ≤ ENNReal.ofReal (5 : ℝ) *
          (Cpull * eLpNorm dw 2 (μ.restrict B)) :=
        mul_le_mul_right hpull_bound (ENNReal.ofReal (5 : ℝ))
    _ = C * eLpNorm dw 2 (μ.restrict B) := by
        simp [C, mul_assoc]
    _ ≤ C * (eLpNorm w 2 (μ.restrict B) +
          eLpNorm dw 2 (μ.restrict B)) :=
        mul_le_mul_right (le_add_left le_rfl) C
    _ =
        C * (eLpNorm w 2
            (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) +
          eLpNorm dw 2
            (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) := by
        simp [μ, B]

/--
%%handwave
name:
  Taper-gradient derivative estimate on the reflected annulus
statement:
  The annular term obtained by multiplying the reflected value by the
  differential of the taper has \(L^2\)-norm bounded by a finite multiple of
  the original unit-ball graph norm.
proof:
  The differential of \(3-2\|x\|\) is uniformly bounded away from the origin,
  and radial reflection carries the annulus \(1\le\|x\|<3/2\) into the inner
  shell \(1/2<\|x\|<1\) with uniformly controlled distortion.  Thus this
  term is controlled by the \(L^2\)-norm of \(w\) on the unit ball.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_derivative_annulus_value_graph_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    ∃ C : ℝ≥0∞,
      C < ⊤ ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues
              (Metric.ball (0 : H) 1) w dw →
            MemLp w 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp dw 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp
              (euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusValuePart
                w)
              2 (MeasureTheory.volume : Measure H) ∧
              eLpNorm
                  (euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusValuePart
                    w)
                  2 (MeasureTheory.volume : Measure H) ≤
                C * (eLpNorm w 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1)) +
                  eLpNorm dw 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1))) := by
  rcases
    euclideanSobolev_unit_ball_radial_reflection_annulus_indicator_pullback_bound
      (H := H) (E := ℝ) with
    ⟨Cpull, hCpull_top, hPull⟩
  let C : ℝ≥0∞ := ENNReal.ofReal (2 : ℝ) * Cpull
  have hC_top : C < ⊤ := by
    dsimp [C]
    exact ENNReal.mul_lt_top (by simp) hCpull_top
  refine ⟨C, hC_top, ?_⟩
  intro w dw _hweak hw _hdw
  let U : Set H := euclideanSobolevUnitBallReflectionAnnulus H
  let B : Set H := Metric.ball (0 : H) 1
  let R : H → H := euclideanSobolevUnitBallRadialReflection
  let μ : Measure H := MeasureTheory.volume
  let τ : H → ℝ := fun y : H ↦ (3 : ℝ) - 2 * ‖y‖
  let pull : H → ℝ := U.indicator (fun z : H ↦ w (R z))
  rcases hPull (f := w) hw with ⟨hpull_mem₀, hpull_bound₀⟩
  have hpull_mem : MemLp pull 2 μ := by
    simpa [pull, U, R, μ] using hpull_mem₀
  have hpull_bound :
      eLpNorm pull 2 μ ≤
        Cpull * eLpNorm w 2 (μ.restrict B) := by
    simpa [pull, U, R, μ, B] using hpull_bound₀
  let raw : H → H →L[ℝ] ℝ :=
    fun x : H ↦ pull x • fderiv ℝ τ x
  have hfderiv_aesm :
      AEStronglyMeasurable (fun x : H ↦ fderiv ℝ τ x) μ :=
    (measurable_fderiv ℝ τ).aestronglyMeasurable
  have hraw_aesm : AEStronglyMeasurable raw μ := by
    change AEStronglyMeasurable
      (fun x : H ↦ pull x • fderiv ℝ τ x) μ
    exact hpull_mem.aestronglyMeasurable.smul hfderiv_aesm
  have hraw_point :
      ∀ᵐ x ∂μ, ‖raw x‖ ≤ (2 : ℝ) * ‖pull x‖ := by
    filter_upwards [] with x
    have hD : ‖fderiv ℝ τ x‖ ≤ (2 : ℝ) := by
      simpa [τ] using
        euclideanSobolev_unit_ball_taper_fderiv_norm_le_two (H := H) x
    calc
      ‖raw x‖ = ‖pull x‖ * ‖fderiv ℝ τ x‖ := by
        simp [raw, norm_smul]
      _ ≤ ‖pull x‖ * 2 :=
        mul_le_mul_of_nonneg_left hD (norm_nonneg _)
      _ = (2 : ℝ) * ‖pull x‖ := by ring
  have hraw_mem : MemLp raw 2 μ :=
    MemLp.of_le_mul hpull_mem hraw_aesm hraw_point
  have hraw_bound :
      eLpNorm raw 2 μ ≤ ENNReal.ofReal (2 : ℝ) * eLpNorm pull 2 μ :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hraw_point 2
  have hsphere_zero : μ {x : H | ‖x‖ = 1} = 0 := by
    have hs :=
      euclidean_volume_sphere_zero (H := H) (c := (0 : H)) (r := (1 : ℝ))
        (by norm_num)
    simpa [μ, Metric.sphere, dist_eq_norm] using hs
  have hraw_eq_part :
      raw =ᵐ[μ]
        euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusValuePart w := by
    filter_upwards [compl_mem_ae_iff.mpr hsphere_zero] with x hx_not_sphere
    have hnorm_ne : ‖x‖ ≠ (1 : ℝ) := by
      simpa using hx_not_sphere
    by_cases hxU : x ∈ U
    · have hxU' : (1 : ℝ) < ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ) := by
        simpa [U, euclideanSobolevUnitBallReflectionAnnulus] using hxU
      have hclosed : 1 ≤ ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ) :=
        ⟨hxU'.1.le, hxU'.2⟩
      simp [raw, pull, U, R, τ,
        euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusValuePart,
        hxU, hclosed]
    · have hclosed_false :
          ¬ (1 ≤ ‖x‖ ∧ ‖x‖ < (3 / 2 : ℝ)) := by
        intro hclosed
        have hnot_lt : ¬ (1 : ℝ) < ‖x‖ := by
          intro hlt
          exact hxU (by
            simpa [U, euclideanSobolevUnitBallReflectionAnnulus] using
              (And.intro hlt hclosed.2))
        have hle : ‖x‖ ≤ (1 : ℝ) := not_lt.mp hnot_lt
        have heq : ‖x‖ = (1 : ℝ) := le_antisymm hle hclosed.1
        exact hnorm_ne heq
      simp [raw, pull, U, R, τ,
        euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusValuePart,
        hxU, hclosed_false]
  have hpart_mem :
      MemLp
        (euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusValuePart w)
        2 μ :=
    MemLp.ae_eq hraw_eq_part hraw_mem
  refine ⟨by simpa [μ] using hpart_mem, ?_⟩
  calc
    eLpNorm
        (euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusValuePart w)
        2 μ
        = eLpNorm raw 2 μ := by
          exact (eLpNorm_congr_ae hraw_eq_part).symm
    _ ≤ ENNReal.ofReal (2 : ℝ) * eLpNorm pull 2 μ := hraw_bound
    _ ≤ ENNReal.ofReal (2 : ℝ) *
          (Cpull * eLpNorm w 2 (μ.restrict B)) :=
        mul_le_mul_right hpull_bound (ENNReal.ofReal (2 : ℝ))
    _ = C * eLpNorm w 2 (μ.restrict B) := by
        simp [C, mul_assoc]
    _ ≤ C * (eLpNorm w 2 (μ.restrict B) +
          eLpNorm dw 2 (μ.restrict B)) :=
        mul_le_mul_right (le_add_right le_rfl) C
    _ =
        C * (eLpNorm w 2
            (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) +
          eLpNorm dw 2
            (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) := by
        simp [μ, B]

private theorem memLp_three_add_eLpNorm_le_of_component_bounds
    {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {u v t : α → E} {Cu Cv Ct S : ℝ≥0∞}
    (hS_top : S < ⊤) (hCu_top : Cu < ⊤) (hCv_top : Cv < ⊤)
    (hCt_top : Ct < ⊤)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (ht : MemLp t 2 μ)
    (hu_bound : eLpNorm u 2 μ ≤ Cu * S)
    (hv_bound : eLpNorm v 2 μ ≤ Cv * S)
    (ht_bound : eLpNorm t 2 μ ≤ Ct * S) :
    MemLp (u + v + t) 2 μ ∧
      eLpNorm (u + v + t) 2 μ ≤ (Cu + Cv + Ct) * S := by
  have huv_meas : AEStronglyMeasurable (u + v) μ :=
    hu.aestronglyMeasurable.add hv.aestronglyMeasurable
  have huv_t_meas : AEStronglyMeasurable (u + v + t) μ :=
    huv_meas.add ht.aestronglyMeasurable
  have hbound :
      eLpNorm (u + v + t) 2 μ ≤
        (Cu * S + Cv * S) + Ct * S := by
    calc
      eLpNorm (u + v + t) 2 μ
          ≤ eLpNorm (u + v) 2 μ + eLpNorm t 2 μ :=
            eLpNorm_add_le huv_meas ht.aestronglyMeasurable
              (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      _ ≤ (eLpNorm u 2 μ + eLpNorm v 2 μ) + eLpNorm t 2 μ := by
          exact add_le_add_left
            (eLpNorm_add_le hu.aestronglyMeasurable hv.aestronglyMeasurable
              (by norm_num : (1 : ℝ≥0∞) ≤ 2))
            _
      _ ≤ (Cu * S + Cv * S) + Ct * S :=
          add_le_add (add_le_add hu_bound hv_bound) ht_bound
  have hbound_top :
      (Cu * S + Cv * S) + Ct * S < ⊤ := by
    refine ENNReal.add_lt_top.2 ?_
    constructor
    · exact ENNReal.add_lt_top.2
        ⟨ENNReal.mul_lt_top hCu_top hS_top,
          ENNReal.mul_lt_top hCv_top hS_top⟩
    · exact ENNReal.mul_lt_top hCt_top hS_top
  refine ⟨⟨huv_t_meas, lt_of_le_of_lt hbound hbound_top⟩, ?_⟩
  calc
    eLpNorm (u + v + t) 2 μ
        ≤ (Cu * S + Cv * S) + Ct * S := hbound
    _ = (Cu + Cv + Ct) * S := by
        rw [add_mul, add_mul]

/--
%%handwave
name:
  Derivative estimate for the radial reflection extension
statement:
  For Sobolev pairs on the Euclidean unit ball, the \(L^2\)-norm of the
  derivative field assigned to the radial reflection extension is bounded by
  a finite multiple of the original \(W^{1,2}\) graph norm on the ball.
proof:
  On the unit ball the assigned field is the original weak derivative, and
  outside the ball of radius \(3/2\) it vanishes.  On the annulus, decompose
  the product-rule field into the tapered pullback of \(dw\) and the taper
  derivative times the reflected value.  Since the reflected shell stays
  away from the origin, the radial differential and change-of-variables
  weights are uniformly controlled.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_extension_derivative_graph_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    ∃ C : ℝ≥0∞,
      C < ⊤ ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues
              (Metric.ball (0 : H) 1) w dw →
            MemLp w 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp dw 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp
              (euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw)
              2 (MeasureTheory.volume : Measure H) ∧
              eLpNorm
                  (euclideanSobolevUnitBallRadialReflectionDerivativeExtension
                    w dw)
                  2 (MeasureTheory.volume : Measure H) ≤
                C * (eLpNorm w 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1)) +
                  eLpNorm dw 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1))) := by
  rcases
      euclideanSobolev_unit_ball_radial_reflection_derivative_unit_part_graph_bound
        (H := H) with
    ⟨Cunit, hCunit_top, hUnit⟩
  rcases
      euclideanSobolev_unit_ball_radial_reflection_derivative_annulus_chain_graph_bound
        (H := H) with
    ⟨Cchain, hCchain_top, hChain⟩
  rcases
      euclideanSobolev_unit_ball_radial_reflection_derivative_annulus_value_graph_bound
        (H := H) with
    ⟨Cvalue, hCvalue_top, hValue⟩
  refine
    ⟨Cunit + Cchain + Cvalue,
      ENNReal.add_lt_top.2
        ⟨ENNReal.add_lt_top.2 ⟨hCunit_top, hCchain_top⟩,
          hCvalue_top⟩,
      ?_⟩
  intro w dw hweak hw hdw
  let μ : Measure H := MeasureTheory.volume
  let S : ℝ≥0∞ :=
    eLpNorm w 2
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) +
      eLpNorm dw 2
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))
  let U : H → H →L[ℝ] ℝ :=
    euclideanSobolevUnitBallRadialReflectionDerivativeUnitPart dw
  let A : H → H →L[ℝ] ℝ :=
    euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusChainPart dw
  let V : H → H →L[ℝ] ℝ :=
    euclideanSobolevUnitBallRadialReflectionDerivativeAnnulusValuePart w
  rcases hUnit hweak hw hdw with ⟨hU_mem, hU_bound⟩
  rcases hChain hweak hw hdw with ⟨hA_mem, hA_bound⟩
  rcases hValue hweak hw hdw with ⟨hV_mem, hV_bound⟩
  have hU_mem' : MemLp U 2 μ := by
    simpa [U, μ] using hU_mem
  have hA_mem' : MemLp A 2 μ := by
    simpa [A, μ] using hA_mem
  have hV_mem' : MemLp V 2 μ := by
    simpa [V, μ] using hV_mem
  have hU_bound' : eLpNorm U 2 μ ≤ Cunit * S := by
    simpa [U, μ, S] using hU_bound
  have hA_bound' : eLpNorm A 2 μ ≤ Cchain * S := by
    simpa [A, μ, S] using hA_bound
  have hV_bound' : eLpNorm V 2 μ ≤ Cvalue * S := by
    simpa [V, μ, S] using hV_bound
  have hparts_eq :
      euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw =
        U + A + V := by
    simpa [U, A, V, Pi.add_apply] using
      euclideanSobolevUnitBallRadialReflectionDerivativeExtension_eq_parts
        w dw
  have hS_top : S < ⊤ := by
    dsimp [S]
    exact ENNReal.add_lt_top.2 ⟨hw.2, hdw.2⟩
  have hsum :
      MemLp (U + A + V) 2 μ ∧
        eLpNorm (U + A + V) 2 μ ≤
          (Cunit + Cchain + Cvalue) * S :=
    memLp_three_add_eLpNorm_le_of_component_bounds
      (α := H) (E := H →L[ℝ] ℝ) (μ := μ)
      (u := U) (v := A) (t := V)
      (Cu := Cunit) (Cv := Cchain) (Ct := Cvalue) (S := S)
      hS_top hCunit_top hCchain_top hCvalue_top
      hU_mem' hA_mem' hV_mem' hU_bound' hA_bound' hV_bound'
  have hderiv_mem :
      MemLp
        (euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw)
        2 μ := by
    rw [hparts_eq]
    exact hsum.1
  refine ⟨by simpa [μ] using hderiv_mem, ?_⟩
  calc
    eLpNorm
        (euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw)
        2 μ
        = eLpNorm (U + A + V) 2 μ := by
          rw [hparts_eq]
    _ ≤ (Cunit + Cchain + Cvalue) * S := hsum.2
    _ =
        (Cunit + Cchain + Cvalue) *
          (eLpNorm w 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) +
            eLpNorm dw 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) := by
        simp [S]

/--
%%handwave
name:
  Graph-norm estimate for the reflected extension
statement:
  In every finite-dimensional real normed vector space, one finite constant
  controls the global \(L^2\) graph norm of the radial reflection extension of
  a Sobolev pair by the \(L^2\) graph norm of the original pair on the unit
  ball.
proof:
  Combine the separate value and derivative estimates, and take the sum of
  their constants.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_extension_graph_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    ∃ C : ℝ≥0∞,
      C < ⊤ ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues
              (Metric.ball (0 : H) 1) w dw →
            MemLp w 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp dw 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp (euclideanSobolevUnitBallReflectionExtension w) 2
              (MeasureTheory.volume : Measure H) ∧
              MemLp (euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw)
                2 (MeasureTheory.volume : Measure H) ∧
              eLpNorm (euclideanSobolevUnitBallReflectionExtension w) 2
                  (MeasureTheory.volume : Measure H) +
                  eLpNorm
                    (euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw)
                    2 (MeasureTheory.volume : Measure H) ≤
                C * (eLpNorm w 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1)) +
                  eLpNorm dw 2
                    (MeasureTheory.volume.restrict
                      (Metric.ball (0 : H) 1))) := by
  rcases
      euclideanSobolev_unit_ball_radial_reflection_extension_value_graph_bound
        (H := H) with
    ⟨Cw, hCw_top, hW⟩
  rcases
      euclideanSobolev_unit_ball_radial_reflection_extension_derivative_graph_bound
        (H := H) with
    ⟨Cd, hCd_top, hDW⟩
  refine ⟨Cw + Cd, ENNReal.add_lt_top.2 ⟨hCw_top, hCd_top⟩, ?_⟩
  intro w dw hweak hw hdw
  let S : ℝ≥0∞ :=
    eLpNorm w 2
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) +
      eLpNorm dw 2
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))
  rcases hW hweak hw hdw with ⟨hW_l2, hW_bound⟩
  rcases hDW hweak hw hdw with ⟨hDW_l2, hDW_bound⟩
  refine ⟨hW_l2, hDW_l2, ?_⟩
  calc
    eLpNorm (euclideanSobolevUnitBallReflectionExtension w) 2
          (MeasureTheory.volume : Measure H) +
        eLpNorm
          (euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw)
          2 (MeasureTheory.volume : Measure H)
        ≤ Cw * S + Cd * S := by
          exact add_le_add hW_bound hDW_bound
    _ = (Cw + Cd) * S := by
      rw [add_mul]

/--
%%handwave
name:
  Test-pairing integrability for radial reflection gluing
statement:
  For a \(W^{1,2}\) function on the unit ball, the global test pairings
  involving the radial reflection extension and its assigned derivative field
  are integrable for every smooth compactly supported test function and every
  constant direction.
proof:
  The value pairing is controlled by the \(L^2\)-bound for the reflected
  value extension, because the derivative of the test function is bounded and
  compactly supported.  The derivative pairing is controlled in the same way
  by the \(L^2\)-bound for the piecewise derivative field and the boundedness
  of the test function.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_glue_test_integrable
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hunit : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (_hannulus : IsWeakDerivativeOnEuclideanRegionWithValues
      (euclideanSobolevUnitBallReflectionAnnulus H)
      (fun x : H ↦
        (3 - 2 * ‖x‖) * w (euclideanSobolevUnitBallRadialReflection x))
      (fun x : H ↦
        (3 - 2 * ‖x‖) •
            (dw (euclideanSobolevUnitBallRadialReflection x)).comp
              (fderiv ℝ (fun y : H ↦
                euclideanSobolevUnitBallRadialReflection y) x) +
          w (euclideanSobolevUnitBallRadialReflection x) •
            fderiv ℝ (fun y : H ↦ (3 : ℝ) - 2 * ‖y‖) x)) :
    euclideanSobolevUnitBallRadialReflectionGlueTestPairingsIntegrable
      w dw := by
  rcases euclideanSobolev_unit_ball_radial_reflection_extension_graph_bound
      (H := H) with
    ⟨C, hC_top, hgraph⟩
  rcases hgraph hunit hw hdw with ⟨hW_l2, hDW_l2, _hbound⟩
  intro φ v
  let W : H → ℝ := euclideanSobolevUnitBallReflectionExtension w
  let DW : H → H →L[ℝ] ℝ :=
    euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw
  have hW_loc :
      LocallyIntegrableOn W Set.univ (MeasureTheory.volume : Measure H) := by
    simpa [W] using memLp_two_locallyIntegrableOn_univ hW_l2
  let L : (H →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ v
  have hDW_eval_l2 : MemLp (fun z : H ↦ DW z v) 2
      (MeasureTheory.volume : Measure H) := by
    simpa [L, DW, Function.comp_def] using L.comp_memLp' hDW_l2
  have hDW_eval_loc :
      LocallyIntegrableOn (fun z : H ↦ DW z v) Set.univ
        (MeasureTheory.volume : Measure H) := by
    exact memLp_two_locallyIntegrableOn_univ hDW_eval_l2
  have hleft_cont :
      Continuous (fun z : H ↦ fderiv ℝ (φ : H → ℝ) z v) :=
    ((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hleft_support :
      tsupport (fun z : H ↦ fderiv ℝ (φ : H → ℝ) z v) ⊆ Set.univ :=
    Set.subset_univ _
  have hleft_compact :
      IsCompact (tsupport (fun z : H ↦ fderiv ℝ (φ : H → ℝ) z v)) :=
    φ.compact_support.of_isClosed_subset
      (isClosed_tsupport _)
      (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (φ : H → ℝ)) v)
  have hleft :
      Integrable
        (fun z : H ↦
          (fderiv ℝ (φ : H → ℝ) z v) *
            W z)
        (MeasureTheory.volume : Measure H) :=
    locallyIntegrableOn_mul_left_integrable_global_of_tsupport_subset
      hW_loc hleft_cont hleft_support hleft_compact
  have hright_cont : Continuous (φ : H → ℝ) :=
    φ.smooth.continuous
  have hright_support : tsupport (φ : H → ℝ) ⊆ Set.univ :=
    Set.subset_univ _
  have hright :
      Integrable
        (fun z : H ↦ (φ : H → ℝ) z * (DW z v))
        (MeasureTheory.volume : Measure H) :=
    locallyIntegrableOn_mul_left_integrable_global_of_tsupport_subset
      hDW_eval_loc hright_cont hright_support φ.compact_support
  refine ⟨?_, ?_⟩
  · simpa [euclideanSobolevUnitBallRadialReflectionGlueTestPairingsIntegrable,
      W, smul_eq_mul, Measure.restrict_univ] using hleft
  · simpa [euclideanSobolevUnitBallRadialReflectionGlueTestPairingsIntegrable,
      DW, smul_eq_mul, Measure.restrict_univ] using hright

/--
%%handwave
name:
  Weak derivative of the reflected extension
statement:
  If \(w\) has weak derivative \(dw\) on the unit ball, then the radial
  reflection extension has the piecewise radial-reflection derivative field
  as a global weak derivative.
proof:
  Apply
  [the weak chain rule on the reflected annulus](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_reflection_annulus_weakDerivative)
  and then
  [glue the reflected weak derivative across the null spheres](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_reflection_glue_weakDerivative).
-/
theorem euclideanSobolev_unit_ball_radial_reflection_extension_weakDerivative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    IsWeakDerivativeOnEuclideanRegionWithValues Set.univ
      (euclideanSobolevUnitBallReflectionExtension w)
      (euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw) := by
  let hannulus :=
    euclideanSobolev_unit_ball_radial_reflection_annulus_weakDerivative
      hweak hw hdw
  exact
    euclideanSobolev_unit_ball_radial_reflection_glue_weakDerivative
      hweak hw hdw hannulus
      (euclideanSobolev_unit_ball_radial_reflection_glue_test_integrable
        hweak hw hdw hannulus)

/--
%%handwave
name:
  Core Sobolev estimate for radial reflection
statement:
  In every standard finite-dimensional Euclidean space, the radial reflection
  extension from the unit ball has a global weak derivative with finite
  \(L^2\) graph norm controlled by the original unit-ball graph norm, and the
  derivative field agrees almost everywhere with the original derivative
  inside the unit ball.
proof:
  Use
  [the weak derivative of the reflected extension](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_reflection_extension_weakDerivative)
  for the global integration-by-parts identity, and use
  [the graph-norm estimate for the reflected extension](lean:JJMath.Uniformization.euclideanSobolev_unit_ball_radial_reflection_extension_graph_bound)
  for global square-integrability and the norm bound.  The derivative field
  agrees with \(dw\) on the unit ball by the definition of the piecewise
  field.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_extension_core
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] :
    ∃ C : ℝ≥0∞,
      C < ⊤ ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues
              (Metric.ball (0 : H) 1) w dw →
            MemLp w 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp dw 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            ∃ DW : H → H →L[ℝ] ℝ,
              IsWeakDerivativeOnEuclideanRegionWithValues Set.univ
                (euclideanSobolevUnitBallReflectionExtension w) DW ∧
                MemLp (euclideanSobolevUnitBallReflectionExtension w) 2
                  (MeasureTheory.volume : Measure H) ∧
                MemLp DW 2 (MeasureTheory.volume : Measure H) ∧
                DW =ᵐ[MeasureTheory.volume.restrict
                    (Metric.ball (0 : H) 1)] dw ∧
                eLpNorm (euclideanSobolevUnitBallReflectionExtension w) 2
                    (MeasureTheory.volume : Measure H) +
                    eLpNorm DW 2
                      (MeasureTheory.volume : Measure H) ≤
                  C * (eLpNorm w 2
                      (MeasureTheory.volume.restrict
                        (Metric.ball (0 : H) 1)) +
                    eLpNorm dw 2
                      (MeasureTheory.volume.restrict
                        (Metric.ball (0 : H) 1))) := by
  rcases euclideanSobolev_unit_ball_radial_reflection_extension_graph_bound
      (H := H) with
    ⟨C, hC_top, hgraph⟩
  refine ⟨C, hC_top, ?_⟩
  intro w dw hweak hw hdw
  let DW : H → H →L[ℝ] ℝ :=
    euclideanSobolevUnitBallRadialReflectionDerivativeExtension w dw
  rcases hgraph hweak hw hdw with ⟨hW_l2, hDW_l2, hbound⟩
  exact
    ⟨DW,
      euclideanSobolev_unit_ball_radial_reflection_extension_weakDerivative
        hweak hw hdw,
      hW_l2, hDW_l2,
      euclideanSobolevUnitBallRadialReflectionDerivativeExtension_ae_eq_on_unit_ball
        (μ := MeasureTheory.volume) w dw,
      hbound⟩

section StandardEuclideanBallExtensions

variable {ι : Type} [Fintype ι]

local notation "H" => EuclideanSpace ℝ ι

/--
%%handwave
name:
  Bounded Sobolev radial reflection extension operator
statement:
  In every standard finite-dimensional Euclidean space, the radial reflection
  extension from the unit ball is a bounded scalar \(W^{1,2}\) extension
  operator.  For every weak Sobolev pair on the unit ball, the reflected
  function has some global weak derivative, the extended pair agrees with the
  original pair almost everywhere on the unit ball, and the global \(L^2\)
  graph norm is bounded by a finite multiple of the original unit-ball graph
  norm.
proof:
  Combine the core radial reflection estimate with the elementary fact that
  the reflected extension is exactly the original function inside the unit
  ball.
-/
theorem euclideanSobolev_unit_ball_radial_reflection_extension_operator :
    ∃ C : ℝ≥0∞,
      C < ⊤ ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues
              (Metric.ball (0 : H) 1) w dw →
            MemLp w 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp dw 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            ∃ DW : H → H →L[ℝ] ℝ,
              IsWeakDerivativeOnEuclideanRegionWithValues Set.univ
                (euclideanSobolevUnitBallReflectionExtension w) DW ∧
                MemLp (euclideanSobolevUnitBallReflectionExtension w) 2
                  (MeasureTheory.volume : Measure H) ∧
                MemLp DW 2 (MeasureTheory.volume : Measure H) ∧
                euclideanSobolevUnitBallReflectionExtension w
                  =ᵐ[MeasureTheory.volume.restrict
                    (Metric.ball (0 : H) 1)] w ∧
                DW =ᵐ[MeasureTheory.volume.restrict
                    (Metric.ball (0 : H) 1)] dw ∧
                eLpNorm (euclideanSobolevUnitBallReflectionExtension w) 2
                    (MeasureTheory.volume : Measure H) +
                    eLpNorm DW 2
                      (MeasureTheory.volume : Measure H) ≤
                  C * (eLpNorm w 2
                      (MeasureTheory.volume.restrict
                        (Metric.ball (0 : H) 1)) +
                    eLpNorm dw 2
                      (MeasureTheory.volume.restrict
                        (Metric.ball (0 : H) 1))) := by
  rcases
    @euclideanSobolev_unit_ball_radial_reflection_extension_core
      H _ _ _ _ _ _ with
    ⟨C, hC_top, hExt⟩
  refine ⟨C, hC_top, ?_⟩
  intro w dw hweak hw hdw
  rcases hExt hweak hw hdw with
    ⟨DW, hweak_ext, hW_l2, hDW_l2, hDW_eq, hbound⟩
  exact
    ⟨DW, hweak_ext, hW_l2, hDW_l2,
      euclideanSobolevUnitBallReflectionExtension_ae_eq_on_unit_ball
        (μ := MeasureTheory.volume) w,
      hDW_eq, hbound⟩

/--
%%handwave
name:
  Bounded Sobolev extension operator for the Euclidean unit ball
statement:
  In every standard finite-dimensional Euclidean space there is a bounded
  extension operator for scalar \(W^{1,2}\) functions on the unit ball centered
  at the origin.  For every weak Sobolev pair on the unit ball, the extended
  function has some global weak derivative, the extended pair agrees with the
  original pair almost everywhere on the unit ball, and the global \(L^2\)
  graph norm is bounded by a finite multiple of the original unit-ball graph
  norm.
proof:
  Use the radial reflection extension from the unit ball and the boundedness
  estimate for that construction.
-/
theorem euclideanSobolev_unit_ball_bounded_extension_operator :
    ∃ (Ext : (H → ℝ) → H → ℝ) (C : ℝ≥0∞),
      C < ⊤ ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues
              (Metric.ball (0 : H) 1) w dw →
            MemLp w 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp dw 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            ∃ DW : H → H →L[ℝ] ℝ,
              IsWeakDerivativeOnEuclideanRegionWithValues Set.univ
                (Ext w) DW ∧
                MemLp (Ext w) 2 (MeasureTheory.volume : Measure H) ∧
                MemLp DW 2 (MeasureTheory.volume : Measure H) ∧
                Ext w =ᵐ[MeasureTheory.volume.restrict
                    (Metric.ball (0 : H) 1)] w ∧
                DW =ᵐ[MeasureTheory.volume.restrict
                    (Metric.ball (0 : H) 1)] dw ∧
                eLpNorm (Ext w) 2 (MeasureTheory.volume : Measure H) +
                    eLpNorm DW 2
                      (MeasureTheory.volume : Measure H) ≤
                  C * (eLpNorm w 2
                      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) +
                    eLpNorm dw 2
                      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) := by
  rcases
    @euclideanSobolev_unit_ball_radial_reflection_extension_operator ι _ with
    ⟨C, hC_top, hExt⟩
  exact ⟨euclideanSobolevUnitBallReflectionExtension, C, hC_top, hExt⟩

/--
%%handwave
name:
  Bounded Sobolev extension assignments for the Euclidean unit ball
statement:
  In every standard finite-dimensional Euclidean space there are extension
  assignments for scalar \(W^{1,2}\) data on the unit ball centered at the
  origin.  For every weak Sobolev pair on the unit ball, the assigned global
  pair has the assigned field as its global weak derivative, agrees with the
  original pair almost everywhere on the unit ball, and has globally finite
  \(L^2\) graph norm bounded by a finite multiple of the original unit-ball
  graph norm.
proof:
  Use the bounded extension operator for the unit ball.  For each admissible
  weak Sobolev pair, choose one global weak derivative of the extended
  function satisfying the same bound and the same almost-everywhere agreement
  on the unit ball.
-/
theorem euclideanSobolev_unit_ball_bounded_extension_assignments :
    ∃ (Ext : (H → ℝ) → H → ℝ)
      (DExt : (H → ℝ) → (H → H →L[ℝ] ℝ) → H → H →L[ℝ] ℝ)
      (C : ℝ≥0∞),
      C < ⊤ ∧
        ∀ {w : H → ℝ} {dw : H → H →L[ℝ] ℝ},
          IsWeakDerivativeOnEuclideanRegionWithValues
              (Metric.ball (0 : H) 1) w dw →
            MemLp w 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            MemLp dw 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) →
            IsWeakDerivativeOnEuclideanRegionWithValues Set.univ
              (Ext w) (DExt w dw) ∧
              MemLp (Ext w) 2 (MeasureTheory.volume : Measure H) ∧
              MemLp (DExt w dw) 2 (MeasureTheory.volume : Measure H) ∧
              Ext w =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)]
                w ∧
              DExt w dw =ᵐ[MeasureTheory.volume.restrict
                  (Metric.ball (0 : H) 1)] dw ∧
              eLpNorm (Ext w) 2 (MeasureTheory.volume : Measure H) +
                  eLpNorm (DExt w dw) 2
                    (MeasureTheory.volume : Measure H) ≤
                C * (eLpNorm w 2
                    (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) +
                  eLpNorm dw 2
                    (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) := by
  classical
  rcases
    @euclideanSobolev_unit_ball_bounded_extension_operator ι _ with
    ⟨Ext, C, hC_top, hExt⟩
  let Good :
      (H → ℝ) → (H → H →L[ℝ] ℝ) →
        (H → H →L[ℝ] ℝ) → Prop :=
    fun w dw DW ↦
      IsWeakDerivativeOnEuclideanRegionWithValues Set.univ (Ext w) DW ∧
        MemLp (Ext w) 2 (MeasureTheory.volume : Measure H) ∧
        MemLp DW 2 (MeasureTheory.volume : Measure H) ∧
        Ext w =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)]
          w ∧
        DW =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)]
          dw ∧
        eLpNorm (Ext w) 2 (MeasureTheory.volume : Measure H) +
            eLpNorm DW 2 (MeasureTheory.volume : Measure H) ≤
          C * (eLpNorm w 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) +
            eLpNorm dw 2
              (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
  let DExt : (H → ℝ) → (H → H →L[ℝ] ℝ) → H → H →L[ℝ] ℝ :=
    fun w dw ↦
      if h : ∃ DW : H → H →L[ℝ] ℝ, Good w dw DW then
        Classical.choose h
      else
        0
  refine ⟨Ext, DExt, C, hC_top, ?_⟩
  intro w dw hweak hw hdw
  have hgood_exists : ∃ DW : H → H →L[ℝ] ℝ, Good w dw DW :=
    hExt hweak hw hdw
  have hDExt_good : Good w dw (DExt w dw) := by
    dsimp [DExt]
    rw [dif_pos hgood_exists]
    exact Classical.choose_spec hgood_exists
  exact hDExt_good

/--
%%handwave
name:
  Global \(L^2\) Sobolev extension from the unit Euclidean ball
statement:
  A scalar \(W^{1,2}\) pair on the unit Euclidean ball centered at the origin
  has a global \(W^{1,2}\) extension to the ambient Euclidean space.  The
  extension and its derivative are globally square-integrable and agree with
  the original pair almost everywhere on the ball.
proof:
  Apply the bounded extension theorem for the unit ball and keep the assigned
  global representative and derivative field.
-/
theorem euclideanSobolev_global_l2_extension_memLp_from_unit_ball_domain
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) 1) w dw)
    (hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)))
    (hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1))) :
    ∃ (W : H → ℝ) (DW : H → H →L[ℝ] ℝ),
      IsWeakDerivativeOnEuclideanRegionWithValues Set.univ W DW ∧
        MemLp W 2 (MeasureTheory.volume : Measure H) ∧
        MemLp DW 2 (MeasureTheory.volume : Measure H) ∧
        W =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] w ∧
        DW =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)] dw := by
  rcases
    @euclideanSobolev_unit_ball_bounded_extension_assignments ι _ with
    ⟨Ext, DExt, _C, _hC_top, hExt⟩
  rcases hExt (w := w) (dw := dw) hweak hw hdw with
    ⟨hweak_ext, hW_l2, hDW_l2, hW_eq, hDW_eq, _hbound⟩
  exact ⟨Ext w, DExt w dw, hweak_ext, hW_l2, hDW_l2, hW_eq, hDW_eq⟩

/--
%%handwave
name:
  Global \(L^2\) Sobolev extension from a centered Euclidean ball
statement:
  A scalar \(W^{1,2}\) pair on a Euclidean ball centered at the origin has a
  global \(W^{1,2}\) extension to the ambient Euclidean space.  The extension
  and its derivative are globally square-integrable and agree with the
  original pair almost everywhere on the ball.
proof:
  Dilate the ball to the unit ball, apply the unit-ball extension theorem,
  and dilate the extension back.  Haar measure changes by a constant Jacobian
  factor under dilation, so square-integrability and almost-everywhere
  agreement are preserved.  The weak-derivative field transforms by the
  chain-rule factor for the dilation.
-/
theorem euclideanSobolev_global_l2_extension_memLp_from_centered_ball_domain
    {r : ℝ}
    (hr_pos : 0 < r)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : H) r) w dw)
    (hw : MemLp w 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) r)))
    (hdw : MemLp dw 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) r))) :
    ∃ (W : H → ℝ) (DW : H → H →L[ℝ] ℝ),
      IsWeakDerivativeOnEuclideanRegionWithValues Set.univ W DW ∧
        MemLp W 2 (MeasureTheory.volume : Measure H) ∧
        MemLp DW 2 (MeasureTheory.volume : Measure H) ∧
        W =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) r)] w ∧
        DW =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : H) r)] dw := by
  let T : H → H := fun z ↦ r • z
  let S : H → H := fun z ↦ r⁻¹ • z
  let Br : Set H := Metric.ball (0 : H) r
  let B1 : Set H := Metric.ball (0 : H) 1
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hr_inv_pos : 0 < r⁻¹ := inv_pos.mpr hr_pos
  have hpre_T : T ⁻¹' Br = B1 := by
    have hpre :=
      @preimage_const_smul_ball_zero_of_pos H _ _
         (a := r) (R := (1 : ℝ)) hr_pos
    change (fun z : H ↦ r • z) ⁻¹' Metric.ball (0 : H) r =
      Metric.ball (0 : H) 1
    simpa only [mul_one] using hpre
  have hpre_S : S ⁻¹' B1 = Br := by
    have hpre :=
      @preimage_const_smul_ball_zero_of_pos H _ _
         (a := r⁻¹) (R := r) hr_inv_pos
    have hmul : r⁻¹ * r = 1 := inv_mul_cancel₀ hr_ne
    change (fun z : H ↦ r⁻¹ • z) ⁻¹' Metric.ball (0 : H) 1 =
      Metric.ball (0 : H) r
    simpa only [hmul] using hpre
  let wpull : H → ℝ := fun z ↦ w (T z)
  let dwpull : H → H →L[ℝ] ℝ := fun z ↦ r • dw (T z)
  have hweak_pull :
      IsWeakDerivativeOnEuclideanRegionWithValues B1 wpull dwpull := by
    have hweak_pre :=
      IsWeakDerivativeOnEuclideanRegionWithValues.comp_smul
        hweak hr_ne
    simpa [wpull, dwpull, T, Br, hpre_T] using hweak_pre
  have hw_pull : MemLp wpull 2 (MeasureTheory.volume.restrict B1) := by
    have hw' : MemLp (fun z : H ↦ w (r • z)) 2
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
      simpa [mul_one] using
        memLp_comp_const_smul_of_memLp_restrict_ball_zero
          (a := r) (R := (1 : ℝ)) (f := w) hr_pos
          (by simpa [mul_one] using hw)
    simpa [wpull, T, B1] using hw'
  have hdw_pull : MemLp dwpull 2 (MeasureTheory.volume.restrict B1) := by
    have hdw_comp : MemLp (fun z : H ↦ dw (r • z)) 2
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
      simpa [mul_one] using
        memLp_comp_const_smul_of_memLp_restrict_ball_zero
          (a := r) (R := (1 : ℝ)) (f := dw) hr_pos
          (by simpa [mul_one] using hdw)
    have hdw_scaled : MemLp (fun z : H ↦ r • dw (r • z)) 2
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) 1)) := by
      simpa using hdw_comp.const_smul r
    simpa [dwpull, T, B1] using hdw_scaled
  rcases
    euclideanSobolev_global_l2_extension_memLp_from_unit_ball_domain
      (w := wpull) (dw := dwpull) hweak_pull hw_pull hdw_pull with
    ⟨W1, DW1, hweak1, hW1_l2, hDW1_l2, hW1_eq, hDW1_eq⟩
  let W : H → ℝ := fun z ↦ W1 (S z)
  let DW : H → H →L[ℝ] ℝ := fun z ↦ r⁻¹ • DW1 (S z)
  have hweak_ext :
      IsWeakDerivativeOnEuclideanRegionWithValues Set.univ W DW := by
    have hweak_pre :=
      IsWeakDerivativeOnEuclideanRegionWithValues.comp_smul
        hweak1 (inv_ne_zero hr_ne)
    simpa [W, DW, S] using hweak_pre
  have hW_l2 : MemLp W 2 (MeasureTheory.volume : Measure H) := by
    simpa [W, S] using
      memLp_comp_const_smul_of_memLp_volume
        (a := r⁻¹) (f := W1) (inv_ne_zero hr_ne) hW1_l2
  have hDW_l2 : MemLp DW 2 (MeasureTheory.volume : Measure H) := by
    have hcomp : MemLp (fun z : H ↦ DW1 (r⁻¹ • z)) 2
        (MeasureTheory.volume : Measure H) := by
      simpa using
        memLp_comp_const_smul_of_memLp_volume
          (a := r⁻¹) (f := DW1)
          (inv_ne_zero hr_ne) hDW1_l2
    have hscaled : MemLp (fun z : H ↦ r⁻¹ • DW1 (r⁻¹ • z)) 2
        (MeasureTheory.volume : Measure H) := by
      simpa using hcomp.const_smul r⁻¹
    simpa [DW, S] using hscaled
  have hS_qmp :
      Measure.QuasiMeasurePreserving S
        (MeasureTheory.volume.restrict Br)
        (MeasureTheory.volume.restrict B1) := by
    have hq :=
      @quasiMeasurePreserving_const_smul_restrict_ball_zero
         H _ _ _ _ _ _
         (a := r⁻¹) (R := r) hr_inv_pos
    have hmul : r⁻¹ * r = 1 := inv_mul_cancel₀ hr_ne
    simpa [S, Br, B1, hmul] using hq
  have hW_eq_comp :
      W =ᵐ[MeasureTheory.volume.restrict Br]
        fun z : H ↦ wpull (S z) := by
    have hcomp :=
      hS_qmp.ae_eq_comp hW1_eq
    simpa [W, wpull, S] using hcomp
  have hW_pull_eq :
      (fun z : H ↦ wpull (S z)) =ᵐ[MeasureTheory.volume.restrict Br] w :=
    Filter.Eventually.of_forall fun z ↦ by
      have hTS : T (S z) = z := by
        simp [T, S, smul_smul, mul_inv_cancel₀ hr_ne]
      simp [wpull, hTS]
  have hDW_eq_comp :
      DW =ᵐ[MeasureTheory.volume.restrict Br]
        fun z : H ↦ r⁻¹ • dwpull (S z) := by
    have hcomp :=
      hS_qmp.ae_eq_comp hDW1_eq
    filter_upwards [hcomp] with z hz
    change r⁻¹ • DW1 (S z) = r⁻¹ • dwpull (S z)
    simpa [Function.comp_def] using
      congrArg (fun L : H →L[ℝ] ℝ ↦ r⁻¹ • L) hz
  have hDW_pull_eq :
      (fun z : H ↦ r⁻¹ • dwpull (S z)) =ᵐ[MeasureTheory.volume.restrict Br] dw :=
    Filter.Eventually.of_forall fun z ↦ by
      have hTS : T (S z) = z := by
        simp [T, S, smul_smul, mul_inv_cancel₀ hr_ne]
      simp [dwpull, hTS, inv_smul_smul₀ hr_ne]
  exact
    ⟨W, DW, hweak_ext, hW_l2, hDW_l2,
      hW_eq_comp.trans hW_pull_eq, hDW_eq_comp.trans hDW_pull_eq⟩

/--
%%handwave
name:
  Global \(L^2\) Sobolev extension from a Euclidean ball
statement:
  A scalar \(W^{1,2}\) pair on a Euclidean ball has a global \(W^{1,2}\)
  extension to the ambient Euclidean space.  The extension and its derivative
  are globally square-integrable and agree with the original pair almost
  everywhere on the ball.
proof:
  Translate the ball to the origin, apply the centered-ball extension
  theorem, and translate the extension back.  Haar measure is invariant under
  translations, so square-integrability and almost-everywhere agreement are
  preserved.  The weak-derivative identity is preserved by translating the
  compactly supported test functions.
-/
theorem euclideanSobolev_global_l2_extension_memLp_from_ball_domain
    {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball c r) w dw)
    (hw : MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdw : MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r))) :
    ∃ (W : H → ℝ) (DW : H → H →L[ℝ] ℝ),
      IsWeakDerivativeOnEuclideanRegionWithValues Set.univ W DW ∧
        MemLp W 2 (MeasureTheory.volume : Measure H) ∧
        MemLp DW 2 (MeasureTheory.volume : Measure H) ∧
        W =ᵐ[MeasureTheory.volume.restrict (Metric.ball c r)] w ∧
        DW =ᵐ[MeasureTheory.volume.restrict (Metric.ball c r)] dw := by
  let T : H → H := fun z ↦ z + c
  let S : H → H := fun z ↦ z + (-c)
  let Bc : Set H := Metric.ball c r
  let B0 : Set H := Metric.ball (0 : H) r
  have hpre_T : T ⁻¹' Bc = B0 := by
    exact preimage_add_right_ball_center  c r
  have hpre_S : S ⁻¹' B0 = Bc := by
    exact preimage_add_right_neg_ball_zero  c r
  have hT_mp : MeasurePreserving T
      (MeasureTheory.volume : Measure H) MeasureTheory.volume := by
    simpa [T] using measurePreserving_add_right_volume  c
  have hT_emb : MeasurableEmbedding T := by
    simpa [T] using measurableEmbedding_add_right  c
  have hS_mp : MeasurePreserving S
      (MeasureTheory.volume : Measure H) MeasureTheory.volume := by
    simpa [S] using measurePreserving_add_right_volume  (-c)
  have hS_emb : MeasurableEmbedding S := by
    simpa [S] using measurableEmbedding_add_right  (-c)
  let wpull : H → ℝ := fun z ↦ w (T z)
  let dwpull : H → H →L[ℝ] ℝ := fun z ↦ dw (T z)
  have hweak_pull :
      IsWeakDerivativeOnEuclideanRegionWithValues B0 wpull dwpull := by
    have hweak_pre :=
      IsWeakDerivativeOnEuclideanRegionWithValues.comp_add_right
        hweak c
    simpa [wpull, dwpull, T, Bc, hpre_T] using hweak_pre
  have hT_mp_restrict :
      MeasurePreserving T (MeasureTheory.volume.restrict B0)
        (MeasureTheory.volume.restrict Bc) := by
    have h :=
      hT_mp.restrict_preimage_emb hT_emb Bc
    simpa [hpre_T] using h
  have hw_pull : MemLp wpull 2 (MeasureTheory.volume.restrict B0) := by
    simpa [wpull, T] using hw.comp_measurePreserving hT_mp_restrict
  have hdw_pull : MemLp dwpull 2 (MeasureTheory.volume.restrict B0) := by
    simpa [dwpull, T] using hdw.comp_measurePreserving hT_mp_restrict
  rcases
    euclideanSobolev_global_l2_extension_memLp_from_centered_ball_domain
      (r := r) (w := wpull) (dw := dwpull)
      hr_pos hweak_pull hw_pull hdw_pull with
    ⟨W0, DW0, hweak0, hW0_l2, hDW0_l2, hW0_eq, hDW0_eq⟩
  let W : H → ℝ := fun z ↦ W0 (S z)
  let DW : H → H →L[ℝ] ℝ := fun z ↦ DW0 (S z)
  have hweak_ext :
      IsWeakDerivativeOnEuclideanRegionWithValues Set.univ W DW := by
    have hweak_pre :=
      IsWeakDerivativeOnEuclideanRegionWithValues.comp_add_right
        hweak0 (-c)
    simpa [W, DW, S] using hweak_pre
  have hW_l2 : MemLp W 2 (MeasureTheory.volume : Measure H) := by
    simpa [W, S] using hW0_l2.comp_measurePreserving hS_mp
  have hDW_l2 : MemLp DW 2 (MeasureTheory.volume : Measure H) := by
    simpa [DW, S] using hDW0_l2.comp_measurePreserving hS_mp
  have hS_mp_restrict :
      MeasurePreserving S (MeasureTheory.volume.restrict Bc)
        (MeasureTheory.volume.restrict B0) := by
    have h :=
      hS_mp.restrict_preimage_emb hS_emb B0
    simpa [hpre_S] using h
  have hW_eq_comp :
      W =ᵐ[MeasureTheory.volume.restrict Bc]
        fun z : H ↦ wpull (S z) := by
    have hcomp :=
      hS_mp_restrict.quasiMeasurePreserving.ae_eq_comp hW0_eq
    simpa [W, wpull, S] using hcomp
  have hW_pull_eq :
      (fun z : H ↦ wpull (S z)) =ᵐ[MeasureTheory.volume.restrict Bc] w :=
    Filter.Eventually.of_forall fun z ↦ by
      simp [wpull, T, S, add_assoc]
  have hDW_eq_comp :
      DW =ᵐ[MeasureTheory.volume.restrict Bc]
        fun z : H ↦ dwpull (S z) := by
    have hcomp :=
      hS_mp_restrict.quasiMeasurePreserving.ae_eq_comp hDW0_eq
    simpa [DW, dwpull, S] using hcomp
  have hDW_pull_eq :
      (fun z : H ↦ dwpull (S z)) =ᵐ[MeasureTheory.volume.restrict Bc] dw :=
    Filter.Eventually.of_forall fun z ↦ by
      simp [dwpull, T, S, add_assoc]
  exact
    ⟨W, DW, hweak_ext, hW_l2, hDW_l2,
      hW_eq_comp.trans hW_pull_eq, hDW_eq_comp.trans hDW_pull_eq⟩

/--
%%handwave
name:
  \(W^{1,2}\) extension from a Euclidean ball as a domain
statement:
  A scalar \(W^{1,2}\) pair on a Euclidean ball has a global \(W^{1,2}\)
  extension to the ambient Euclidean space.  The extension and its derivative
  are locally integrable, globally square-integrable, and agree with the
  original pair almost everywhere on the ball.
proof:
  Apply the global \(L^2\) extension theorem.  Global \(L^2\)-control implies
  local integrability on compact sets, and the same holds after evaluating
  the derivative field in any fixed direction.
-/
theorem euclideanSobolev_global_l2_extension_from_ball_domain
    {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball c r) w dw)
    (hw : MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdw : MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r))) :
    ∃ (W : H → ℝ) (DW : H → H →L[ℝ] ℝ),
      IsWeakDerivativeOnEuclideanRegionWithValues Set.univ W DW ∧
        LocallyIntegrableOn W Set.univ
          (MeasureTheory.volume : Measure H) ∧
        (∀ h : H, LocallyIntegrableOn (fun z ↦ DW z h) Set.univ
          (MeasureTheory.volume : Measure H)) ∧
        MemLp W 2 (MeasureTheory.volume : Measure H) ∧
        MemLp DW 2 (MeasureTheory.volume : Measure H) ∧
        W =ᵐ[MeasureTheory.volume.restrict (Metric.ball c r)] w ∧
        DW =ᵐ[MeasureTheory.volume.restrict (Metric.ball c r)] dw := by
  rcases
    euclideanSobolev_global_l2_extension_memLp_from_ball_domain
      (c := c) (r := r) (w := w) (dw := dw)
      hr_pos hweak hw hdw with
    ⟨W, DW, hweak_ext, hW_l2, hDW_l2, hW_eq, hDW_eq⟩
  have hW_loc :
      LocallyIntegrableOn W Set.univ
        (MeasureTheory.volume : Measure H) :=
    memLp_two_locallyIntegrableOn_univ hW_l2
  have hDW_loc :
      ∀ h : H, LocallyIntegrableOn (fun z ↦ DW z h) Set.univ
        (MeasureTheory.volume : Measure H) := by
    intro h
    let L : (H →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ h
    have h_eval : MemLp (fun z : H ↦ DW z h) 2
        (MeasureTheory.volume : Measure H) := by
      simpa [L, Function.comp_def] using L.comp_memLp' hDW_l2
    exact memLp_two_locallyIntegrableOn_univ h_eval
  exact ⟨W, DW, hweak_ext, hW_loc, hDW_loc, hW_l2, hDW_l2, hW_eq, hDW_eq⟩

/--
%%handwave
name:
  \(W^{1,2}\) extension from a Euclidean ball
statement:
  A scalar \(W^{1,2}\) pair on a Euclidean ball contained in an open weak
  derivative region has a global \(W^{1,2}\) extension to the ambient vector
  space.  The extension and its derivative are locally integrable, globally
  square-integrable, and agree with the original pair almost everywhere on
  the ball.
proof:
  This is the standard bounded extension theorem for Sobolev functions on
  balls in finite-dimensional Euclidean spaces.
-/
theorem euclideanSobolev_global_l2_extension_from_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (_hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw)
    (hw : MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdw : MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r))) :
    ∃ (W : H → ℝ) (DW : H → H →L[ℝ] ℝ),
      IsWeakDerivativeOnEuclideanRegionWithValues Set.univ W DW ∧
        LocallyIntegrableOn W Set.univ
          (MeasureTheory.volume : Measure H) ∧
        (∀ h : H, LocallyIntegrableOn (fun z ↦ DW z h) Set.univ
          (MeasureTheory.volume : Measure H)) ∧
        MemLp W 2 (MeasureTheory.volume : Measure H) ∧
        MemLp DW 2 (MeasureTheory.volume : Measure H) ∧
        W =ᵐ[MeasureTheory.volume.restrict (Metric.ball c r)] w ∧
        DW =ᵐ[MeasureTheory.volume.restrict (Metric.ball c r)] dw := by
  have hweak_ball :
      IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.ball c r) w dw :=
    IsWeakDerivativeOnEuclideanRegionWithValues.mono_set hweak hballΩ
  exact
    euclideanSobolev_global_l2_extension_from_ball_domain
      (c := c) (r := r) (w := w) (dw := dw)
      hr_pos hweak_ball hw hdw

/--
%%handwave
name:
  Compactly supported Sobolev extension from a Euclidean ball
statement:
  A scalar \(W^{1,2}\) pair on a Euclidean ball contained in an open weak
  derivative region has a compactly supported global \(W^{1,2}\) extension
  to the ambient Euclidean space which agrees with the original pair almost
  everywhere on the ball.
proof:
  This is the standard bounded extension theorem for balls.  After extending
  across the boundary, multiply by a smooth compactly supported cutoff which
  is identically one on the original ball.
-/
theorem euclideanSobolev_compactlySupported_global_extension_l2_from_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw)
    (hw : MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdw : MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r))) :
    ∃ (W : H → ℝ) (DW : H → H →L[ℝ] ℝ),
      IsWeakDerivativeOnEuclideanRegionWithValues Set.univ W DW ∧
        Integrable W (MeasureTheory.volume : Measure H) ∧
        Integrable DW (MeasureTheory.volume : Measure H) ∧
        MemLp W 2 (MeasureTheory.volume : Measure H) ∧
        MemLp DW 2 (MeasureTheory.volume : Measure H) ∧
        W =ᵐ[MeasureTheory.volume.restrict (Metric.ball c r)] w ∧
        DW =ᵐ[MeasureTheory.volume.restrict (Metric.ball c r)] dw := by
  classical
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let Q : Set H := Metric.closedBall c r
  rcases
    euclideanSobolev_global_l2_extension_from_ball
      (Ω := Ω) (c := c) (r := r) (w := w) (dw := dw)
      hr_pos hΩ_open hballΩ hweak hw hdw with
    ⟨W, DW, hweak_ext, hW_loc, hDW_loc, hW_l2, hDW_l2, hW_eq, hDW_eq⟩
  have hQ : IsCompact Q := by
    dsimp [Q]
    exact isCompact_closedBall c r
  rcases exists_scalarWeakSobolevCutoff hQ (Set.subset_univ Q) isOpen_univ with
    ⟨χ⟩
  let Wc : H → ℝ := fun z ↦ χ z * W z
  let DWc : H → H →L[ℝ] ℝ :=
    scalarWeakSobolevCutoffDerivative (χ : H → ℝ) W DW
  let K : Set H := tsupport (χ : H → ℝ)
  let μK : Measure H := MeasureTheory.volume.restrict K
  have hK : IsCompact K := χ.compact_support
  have hW_K : MemLp W 2 μK := by
    dsimp [μK]
    exact hW_l2.mono_measure Measure.restrict_le_self
  have hWc_K : MemLp Wc 2 μK := by
    dsimp [Wc]
    exact
      memLp_restrict_mul_left_of_isCompact_of_continuousOn hK
        χ.smooth.continuous.continuousOn hW_K
  have hDWc_eval_mem :
      ∀ i : Fin (Module.finrank ℝ H),
        MemLp (fun z ↦ DWc z (Module.finBasis ℝ H i)) 2 μK := by
    intro i
    let e : H := Module.finBasis ℝ H i
    let L : (H →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ e
    have hDW_eval_global : MemLp (fun z : H ↦ DW z e) 2
        (MeasureTheory.volume : Measure H) := by
      simpa [L, Function.comp_def] using L.comp_memLp' hDW_l2
    have hDW_eval_K : MemLp (fun z : H ↦ DW z e) 2 μK := by
      dsimp [μK]
      exact hDW_eval_global.mono_measure Measure.restrict_le_self
    have hχ_DW : MemLp (fun z : H ↦ χ z * DW z e) 2 μK :=
      memLp_restrict_mul_left_of_isCompact_of_continuousOn hK
        χ.smooth.continuous.continuousOn hDW_eval_K
    have hDχ_cont :
        ContinuousOn (fun z : H ↦ fderiv ℝ (χ : H → ℝ) z e) K :=
      ((χ.smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const).continuousOn
    have hDχ_W : MemLp (fun z : H ↦ fderiv ℝ (χ : H → ℝ) z e * W z) 2 μK :=
      memLp_restrict_mul_left_of_isCompact_of_continuousOn hK hDχ_cont hW_K
    have hW_Dχ : MemLp (fun z : H ↦ W z * fderiv ℝ (χ : H → ℝ) z e) 2 μK := by
      simpa [mul_comm] using hDχ_W
    simpa [DWc, e, scalarWeakSobolevCutoffDerivative_apply] using
      hχ_DW.add hW_Dχ
  have hDWc_K : MemLp DWc 2 μK := by
    let ι := Fin (Module.finrank ℝ H)
    let B : ℝ≥0∞ :=
      ∑ i : ι, eLpNorm (fun z ↦ DWc z (Module.finBasis ℝ H i)) 2 μK
    have hB_top : B < ⊤ := by
      dsimp [B, ι]
      exact ENNReal.sum_lt_top.2
        (fun i _hi ↦ (hDWc_eval_mem i).eLpNorm_lt_top)
    have h_eval :
        ∀ i : ι,
          MemLp (fun z ↦ DWc z (Module.finBasis ℝ H i)) 2 μK ∧
            eLpNorm (fun z ↦ DWc z (Module.finBasis ℝ H i)) 2 μK ≤ B := by
      intro i
      refine ⟨hDWc_eval_mem i, ?_⟩
      dsimp [B, ι]
      exact Finset.single_le_sum
        (f := fun j : ι ↦
          eLpNorm (fun z ↦ DWc z (Module.finBasis ℝ H j)) 2 μK)
        (fun j _hj ↦ zero_le)
        (Finset.mem_univ i)
    rcases
      continuousLinearMap_memLp_and_eLpNorm_le_of_basis_eval_bound
        (F := DWc) hB_top h_eval with
      ⟨C, hC_top, hDWc_mem, _hDWc_bound⟩
    exact hDWc_mem
  have hWc_support : Function.support Wc ⊆ K := by
    intro z hz
    exact subset_tsupport (χ : H → ℝ)
      (Function.support_mul_subset_left (f := (χ : H → ℝ)) (g := W) hz)
  have hDWc_support : Function.support DWc ⊆ K := by
    intro z hz
    by_contra hzK
    have hχ_zero : χ z = 0 := image_eq_zero_of_notMem_tsupport hzK
    have hDχ_zero : fderiv ℝ (χ : H → ℝ) z = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := (χ : H → ℝ)) hzK
    have hDWc_zero : DWc z = 0 := by
      simp [DWc, scalarWeakSobolevCutoffDerivative, hχ_zero, hDχ_zero]
    exact hz hDWc_zero
  have hWc_int : Integrable Wc (MeasureTheory.volume : Measure H) := by
    haveI : IsFiniteMeasure μK := isFiniteMeasure_restrict.2 hK.measure_ne_top
    have hWc_K_int : Integrable Wc μK :=
      hWc_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact
      (integrableOn_iff_integrable_of_support_subset
        (μ := (MeasureTheory.volume : Measure H)) (s := K) (f := Wc)
        hWc_support).mp hWc_K_int
  have hDWc_int : Integrable DWc (MeasureTheory.volume : Measure H) := by
    haveI : IsFiniteMeasure μK := isFiniteMeasure_restrict.2 hK.measure_ne_top
    have hDWc_K_int : Integrable DWc μK :=
      hDWc_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact
      (integrableOn_iff_integrable_of_support_subset
        (μ := (MeasureTheory.volume : Measure H)) (s := K) (f := DWc)
        hDWc_support).mp hDWc_K_int
  have hWc_l2 : MemLp Wc 2 (MeasureTheory.volume : Measure H) :=
    memLp_of_integrable_and_restrict_support hWc_int hWc_K hWc_support
  have hDWc_l2 : MemLp DWc 2 (MeasureTheory.volume : Measure H) :=
    memLp_of_integrable_and_restrict_support hDWc_int hDWc_K hDWc_support
  have hweak_scalar :
      KinnunenWeakDerivativeOnEuclideanRegionScalar Set.univ W DW := by
    simpa [KinnunenWeakDerivativeOnEuclideanRegionScalar,
      IsWeakDerivativeOnEuclideanRegionScalar,
      IsWeakDerivativeOnEuclideanRegionWithValues] using hweak_ext
  have hweak_cut_scalar :
      KinnunenWeakDerivativeOnEuclideanRegionScalar Set.univ Wc DWc := by
    simpa [Wc, DWc] using
      scalarWeakSobolevCutoffDerivative_weakDerivative χ hweak_scalar hW_loc
  have hweak_cut :
      IsWeakDerivativeOnEuclideanRegionWithValues Set.univ Wc DWc := by
    simpa [KinnunenWeakDerivativeOnEuclideanRegionScalar,
      IsWeakDerivativeOnEuclideanRegionScalar,
      IsWeakDerivativeOnEuclideanRegionWithValues] using hweak_cut_scalar
  have hWc_eq_W :
      Wc =ᵐ[MeasureTheory.volume.restrict (Metric.ball c r)] W := by
    exact ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet
      fun z hz ↦ by
        have hzQ : z ∈ Q := by
          exact Metric.ball_subset_closedBall hz
        simp [Wc, χ.eq_one_on z hzQ]
  have hDWc_eq_DW :
      DWc =ᵐ[MeasureTheory.volume.restrict (Metric.ball c r)] DW := by
    exact ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet
      fun z hz ↦ by
        have hzQ : z ∈ Q := by
          exact Metric.ball_subset_closedBall hz
        ext v
        exact χ.cutoffDerivative_eq_on z hzQ
  refine
    ⟨Wc, DWc, hweak_cut, hWc_int, hDWc_int, hWc_l2, hDWc_l2, ?_, ?_⟩
  · exact hWc_eq_W.trans hW_eq
  · exact hDWc_eq_DW.trans hDW_eq

/--
%%handwave
name:
  Integrable Sobolev extension from a Euclidean ball
statement:
  A scalar \(W^{1,2}\) pair on a Euclidean ball contained in an open weak
  derivative region has a globally integrable \(W^{1,2}\) extension to the
  ambient Euclidean space which agrees with the original pair almost everywhere
  on the ball and is square-integrable on any fixed larger closed ball.
proof:
  Apply the compactly supported global extension theorem.  Global
  square-integrability restricts to the larger closed ball.
-/
theorem euclideanSobolev_global_integrable_extension_l2_from_ball
    {Ω : Set H} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hΩ_open : IsOpen Ω)
    (hballΩ : Metric.ball c r ⊆ Ω)
    {w : H → ℝ} {dw : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω w dw)
    (hw : MemLp w 2 (MeasureTheory.volume.restrict (Metric.ball c r)))
    (hdw : MemLp dw 2 (MeasureTheory.volume.restrict (Metric.ball c r))) :
    ∃ (W : H → ℝ) (DW : H → H →L[ℝ] ℝ),
      IsWeakDerivativeOnEuclideanRegionWithValues Set.univ W DW ∧
        Integrable W (MeasureTheory.volume : Measure H) ∧
        Integrable DW (MeasureTheory.volume : Measure H) ∧
        MemLp W 2
          (MeasureTheory.volume.restrict (Metric.closedBall c (r + 1))) ∧
        MemLp DW 2
          (MeasureTheory.volume.restrict (Metric.closedBall c (r + 1))) ∧
        W =ᵐ[MeasureTheory.volume.restrict (Metric.ball c r)] w ∧
        DW =ᵐ[MeasureTheory.volume.restrict (Metric.ball c r)] dw := by
  rcases
    euclideanSobolev_compactlySupported_global_extension_l2_from_ball
      (Ω := Ω) (c := c) (r := r) (w := w) (dw := dw)
      hr_pos hΩ_open hballΩ hweak hw hdw with
    ⟨W, DW, hweak_ext, hW_int, hDW_int, hW_l2, hDW_l2, hW_eq, hDW_eq⟩
  refine ⟨W, DW, hweak_ext, hW_int, hDW_int, ?_, ?_, hW_eq, hDW_eq⟩
  · exact hW_l2.mono_measure Measure.restrict_le_self
  · exact hDW_l2.mono_measure Measure.restrict_le_self

end StandardEuclideanBallExtensions

end

end Uniformization

end JJMath
