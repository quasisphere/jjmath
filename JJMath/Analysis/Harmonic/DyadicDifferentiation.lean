import JJMath.Analysis.Harmonic.Dyadic
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Lebesgue differentiation along planar dyadic squares

This file transfers the Lebesgue differentiation theorem for shrinking
closed balls to the nested dyadic squares selected by a point. The transfer
uses only a fixed geometric comparison: a dyadic square containing a point is
contained in the disk centered at that point with four times the square's
side length, and that disk has `16 * π` times the square's area.
-/

namespace JJMath

open Set MeasureTheory Filter Metric
open scoped Topology ENNReal

namespace HarmonicAnalysis

noncomputable section

/--
%%handwave
name:
  Dyadic mean oscillation is controlled by centered-ball mean oscillation
statement:
  Let $f:\mathbb C\to E$ be integrable and let $z\in Q_{n,k}$. Then
  $$
    \fint_{Q_{n,k}}\|f(y)-f(z)\|\,dy
    \leq16\pi\fint_{\overline B(z,4\cdot2^n)}
      \|f(y)-f(z)\|\,dy.
  $$
proof:
  The square lies in the displayed centered disk. Monotonicity of the
  integral applies to the nonnegative integrand, and the disk has area
  $\pi(4\cdot2^n)^2=16\pi|Q_{n,k}|$.
-/
theorem dyadicAverage_norm_sub_le_closedBallAverage
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : Integrable f volume) (n : ℤ) (k : ℤ × ℤ) {z : ℂ}
    (hz : z ∈ dyadicSquare n k) :
    (⨍ y in dyadicSquare n k, ‖f y - f z‖ ∂volume) ≤
      16 * Real.pi *
        ⨍ y in closedBall z (4 * dyadicSide n), ‖f y - f z‖ ∂volume := by
  let h : ℂ → ℝ := fun y ↦ ‖f y - f z‖
  have hball_int : IntegrableOn h (closedBall z (4 * dyadicSide n)) volume := by
    exact (hf.integrableOn.sub
      (integrableOn_const measure_closedBall_lt_top.ne)).norm
  have hmono : (∫ y in dyadicSquare n k, h y ∂volume) ≤
      ∫ y in closedBall z (4 * dyadicSide n), h y ∂volume := by
    apply setIntegral_mono_set hball_int
      (ae_of_all _ fun y ↦ norm_nonneg (f y - f z))
    exact ae_of_all _ fun _ hy ↦ dyadicSquare_subset_closedBall_center n k hz hy
  rw [setAverage_eq, setAverage_eq]
  simp only [smul_eq_mul]
  rw [measureReal_def, volume_dyadicSquare,
    ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [measureReal_def, Complex.volume_closedBall, ENNReal.toReal_mul,
    ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (dyadicSide_pos n).le),
    ENNReal.coe_toReal]
  have hs : 0 < dyadicSide n := dyadicSide_pos n
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [inv_mul_eq_div, inv_mul_eq_div]
  apply (div_le_iff₀ (sq_pos_of_pos hs)).2
  calc
    ∫ y in dyadicSquare n k, ‖f y - f z‖ ∂volume ≤
        ∫ y in closedBall z (4 * dyadicSide n), ‖f y - f z‖ ∂volume := hmono
    _ = 16 * Real.pi *
        ((∫ y in closedBall z (4 * dyadicSide n), ‖f y - f z‖ ∂volume) /
          ((4 * dyadicSide n) ^ 2 * Real.pi)) * dyadicSide n ^ 2 := by
      field_simp
      ring

/--
%%handwave
name:
  Lebesgue differentiation along point-selected dyadic squares
statement:
  If $f:\mathbb C\to E$ is integrable, then for almost every
  $z\in\mathbb C$,
  $$
    \lim_{j\to\infty}
      \fint_{Q_{-j,k_j(z)}}\|f(y)-f(z)\|\,dy=0,
  $$
  where $Q_{-j,k_j(z)}$ is the unique dyadic square of scale $-j$
  containing $z$.
proof:
  The radii $4\cdot2^{-j}$ tend to zero through positive values. Apply the
  Lebesgue differentiation theorem to the corresponding centered disks and
  squeeze the dyadic averages using [the fixed disk comparison](lean:JJMath.HarmonicAnalysis.dyadicAverage_norm_sub_le_closedBallAverage).
-/
theorem ae_tendsto_dyadicAverage_norm_sub
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : Integrable f volume) :
    ∀ᵐ z ∂volume,
      Tendsto
        (fun j : ℕ ↦
          ⨍ y in dyadicSquare (-(j : ℤ)) (dyadicIndex (-(j : ℤ)) z),
            ‖f y - f z‖ ∂volume)
        atTop (nhds 0) := by
  have hglobal :=
    IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
      (μ := volume) hf.locallyIntegrable 0
  filter_upwards [hglobal] with z hz
  have hdelta :
      Tendsto (fun j : ℕ ↦ 4 * dyadicSide (-(j : ℤ))) atTop
        (nhdsWithin (0 : ℝ) (Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using
        (tendsto_nhdsWithin_iff.mp tendsto_dyadicSide_neg_nat).1.const_mul 4
    · exact Eventually.of_forall fun j ↦
        mul_pos (by norm_num) (dyadicSide_pos (-(j : ℤ)))
  have hball :
      Tendsto
        (fun j : ℕ ↦
          ⨍ y in closedBall z (4 * dyadicSide (-(j : ℤ))), ‖f y - f z‖
            ∂volume)
        atTop (nhds 0) := by
    apply hz (w := fun _ : ℕ ↦ z)
      (δ := fun j : ℕ ↦ 4 * dyadicSide (-(j : ℤ))) hdelta
    exact Eventually.of_forall fun _ ↦ by simp
  have hupper :
      Tendsto
        (fun j : ℕ ↦ 16 * Real.pi *
          ⨍ y in closedBall z (4 * dyadicSide (-(j : ℤ))), ‖f y - f z‖
            ∂volume)
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hball
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ ↦ by
      rw [setAverage_eq]
      simp only [smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
        (integral_nonneg fun _ ↦ norm_nonneg _)
  · exact Eventually.of_forall fun j ↦
      dyadicAverage_norm_sub_le_closedBallAverage hf (-(j : ℤ))
        (dyadicIndex (-(j : ℤ)) z)
        (mem_dyadicSquare_dyadicIndex (-(j : ℤ)) z)
  · exact hupper

end

end HarmonicAnalysis

end JJMath
