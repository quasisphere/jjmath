import JJMath.Analysis.Sobolev.Poincare
import JJMath.Quasiconformal.LocalSobolev
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Approximate differentiability of planar Sobolev maps

This file develops the local Lebesgue-point and mean-oscillation inputs for
approximate differentiability. The scale-covariant Poincare estimate is
provided by `JJMath.Analysis.Sobolev.Poincare`.
-/

namespace JJMath

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology BoundedContinuousFunction

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Open and closed complex balls agree almost everywhere
statement:
  For every $x\in\mathbb C$ and $r\in\mathbb R$, the open ball $B(x,r)$
  and closed ball $\overline B(x,r)$ differ by a planar null set.
proof:
  The open ball is contained in the closed ball, and the explicit planar
  volume formulas give both sets the same finite measure.
-/
theorem complex_closedBall_ae_eq_ball (x : ℂ) (r : ℝ) :
    closedBall x r =ᵐ[MeasureTheory.volume] ball x r := by
  have hmeasure : MeasureTheory.volume (closedBall x r) ≤
      MeasureTheory.volume (ball x r) := by
    rw [Complex.volume_closedBall, Complex.volume_ball]
  exact (ae_eq_of_subset_of_measure_ge ball_subset_closedBall hmeasure
    measurableSet_ball.nullMeasurableSet
    (by
      rw [Complex.volume_closedBall]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        ENNReal.coe_ne_top)).symm

/--
%%handwave
name:
  Real planar volume of a complex ball
statement:
  For $r\geq0$, the real-valued planar volume of $B(x,r)\subseteq\mathbb C$
  is $\pi r^2$.
proof:
  Take the real value of the explicit extended-nonnegative volume formula for
  complex balls.
-/
theorem complex_volume_real_ball (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    MeasureTheory.volume.real (ball x r) = r ^ 2 * Real.pi := by
  rw [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul]
  simp [ENNReal.toReal_ofReal hr]

/--
%%handwave
name:
  Two-coordinate representation of a planar real-linear map
statement:
  A real-linear map $L:\mathbb C\to\mathbb C$ is represented by the pair
  $(L(1),L(i))$, equipped with the Euclidean product norm.
-/
def planarRealLinearCoordinatePairCLM :
    (ℂ →L[ℝ] ℂ) →L[ℝ] WithLp 2 (ℂ × ℂ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).prod
      (ContinuousLinearMap.apply ℝ ℂ Complex.I))

/--
%%handwave
name:
  Operator norm controlled by two planar coordinates
statement:
  For every real-linear map $L:\mathbb C\to\mathbb C$,
  $$
    \|L\|^2\leq 2\bigl(\|L(1)\|^2+\|L(i)\|^2\bigr).
  $$
proof:
  Express the operator norm as $\|\partial_zL\|+\|\partial_{\bar z}L\|$.
  The two Wirtinger components are each at most
  $(\|L(1)\|+\|L(i)\|)/2$, and
  $(a+b)^2\leq2(a^2+b^2)$.
-/
theorem norm_sq_le_two_mul_planarRealLinearCoordinatePairCLM_norm_sq
    (L : ℂ →L[ℝ] ℂ) :
    ‖L‖ ^ 2 ≤ 2 * ‖planarRealLinearCoordinatePairCLM L‖ ^ 2 := by
  have hnorm : ‖L‖ ≤ ‖L 1‖ + ‖L Complex.I‖ := by
    have hDZ :
        ‖weakDZ L‖ ≤ (1 / 2 : ℝ) * (‖L 1‖ + ‖L Complex.I‖) := by
      rw [weakDZ, norm_mul]
      have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [hhalf]
      gcongr
      calc
        ‖L 1 - Complex.I * L Complex.I‖
            ≤ ‖L 1‖ + ‖Complex.I * L Complex.I‖ := norm_sub_le _ _
        _ = ‖L 1‖ + ‖L Complex.I‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
    have hDBar :
        ‖weakDBar L‖ ≤ (1 / 2 : ℝ) * (‖L 1‖ + ‖L Complex.I‖) := by
      rw [weakDBar, norm_mul]
      have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [hhalf]
      gcongr
      calc
        ‖L 1 + Complex.I * L Complex.I‖
            ≤ ‖L 1‖ + ‖Complex.I * L Complex.I‖ := norm_add_le _ _
        _ = ‖L 1‖ + ‖L Complex.I‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
    rw [norm_eq_norm_weakDZ_add_norm_weakDBar]
    linarith
  have hsum_sq :
      (‖L 1‖ + ‖L Complex.I‖) ^ 2 ≤
        2 * (‖L 1‖ ^ 2 + ‖L Complex.I‖ ^ 2) := by
    nlinarith [sq_nonneg (‖L 1‖ - ‖L Complex.I‖)]
  calc
    ‖L‖ ^ 2 ≤ (‖L 1‖ + ‖L Complex.I‖) ^ 2 := by
      nlinarith [norm_nonneg L, norm_nonneg (L 1), norm_nonneg (L Complex.I)]
    _ ≤ 2 * (‖L 1‖ ^ 2 + ‖L Complex.I‖ ^ 2) := hsum_sq
    _ = 2 * ‖planarRealLinearCoordinatePairCLM L‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp [planarRealLinearCoordinatePairCLM]

private def postcompRealPartCLM :
    (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (isBoundedBilinearMap_comp
    (𝕜 := ℝ) (E := ℂ) (F := ℂ) (G := ℝ)).toContinuousLinearMap
      Complex.reCLM

private def postcompImaginaryPartCLM :
    (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (isBoundedBilinearMap_comp
    (𝕜 := ℝ) (E := ℂ) (F := ℂ) (G := ℝ)).toContinuousLinearMap
      Complex.imCLM

/--
%%handwave
name:
  Scale-covariant planar $L^2$ Poincare inequality for complex values
statement:
  There is a finite constant $C$, independent of $c\in\mathbb C$ and $r>0$,
  such that every complex-valued weak Sobolev function $u$ on $B(c,r)$
  admits $a\in\mathbb C$ satisfying
  $$
    \|u-a\|_{L^2(B(c,r))}
      \leq Cr\,\|Du\|_{L^2(B(c,r))}.
  $$
proof:
  Apply the [uniform real-valued estimate](lean:JJMath.Uniformization.complex_euclideanSobolev_poincare_L2_scale_covariant) to the real and imaginary parts. Postcomposition by either coordinate functional does not increase the operator norm of the weak differential, while the complex norm is at most the sum of the absolute values of the two coordinates.
-/
theorem complex_valued_euclideanSobolev_poincare_L2_scale_covariant :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ {c : ℂ} {r : ℝ}, 0 < r →
        ∀ {u : ℂ → ℂ} {du : ℂ → ℂ →L[ℝ] ℂ},
          JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
              (Metric.ball c r) u du →
          MemLp u 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) →
          MemLp du 2
            (MeasureTheory.volume.restrict (Metric.ball c r)) →
          ∃ a : ℂ,
            AEStronglyMeasurable (fun z : ℂ ↦ u z - a)
              (MeasureTheory.volume.restrict (Metric.ball c r)) ∧
            eLpNorm (fun z : ℂ ↦ u z - a) 2
                (MeasureTheory.volume.restrict (Metric.ball c r)) ≤
              C * ENNReal.ofReal r *
                eLpNorm du 2
                  (MeasureTheory.volume.restrict (Metric.ball c r)) := by
  rcases
      JJMath.Uniformization.complex_euclideanSobolev_poincare_L2_scale_covariant
    with ⟨C, hC_top, hC⟩
  refine ⟨2 * C, ENNReal.mul_lt_top (by norm_num) hC_top, ?_⟩
  intro c r hr u du hweak hu hdu
  let uRe : ℂ → ℝ := fun z ↦ (u z).re
  let uIm : ℂ → ℝ := fun z ↦ (u z).im
  let duRe : ℂ → ℂ →L[ℝ] ℝ := fun z ↦ Complex.reCLM.comp (du z)
  let duIm : ℂ → ℂ →L[ℝ] ℝ := fun z ↦ Complex.imCLM.comp (du z)
  have hweakRe :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.ball c r) uRe duRe := by
    simpa [uRe, duRe] using
      weakDerivative_postcomp_continuousLinearMap Complex.reCLM hweak
  have hweakIm :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.ball c r) uIm duIm := by
    simpa [uIm, duIm] using
      weakDerivative_postcomp_continuousLinearMap Complex.imCLM hweak
  have huRe : MemLp uRe 2
      (MeasureTheory.volume.restrict (Metric.ball c r)) := by
    simpa [uRe] using hu.continuousLinearMap_comp Complex.reCLM
  have huIm : MemLp uIm 2
      (MeasureTheory.volume.restrict (Metric.ball c r)) := by
    simpa [uIm] using hu.continuousLinearMap_comp Complex.imCLM
  have hduRe : MemLp duRe 2
      (MeasureTheory.volume.restrict (Metric.ball c r)) := by
    simpa [duRe, postcompRealPartCLM] using
      hdu.continuousLinearMap_comp postcompRealPartCLM
  have hduIm : MemLp duIm 2
      (MeasureTheory.volume.restrict (Metric.ball c r)) := by
    simpa [duIm, postcompImaginaryPartCLM] using
      hdu.continuousLinearMap_comp postcompImaginaryPartCLM
  rcases hC hr hweakRe huRe hduRe with ⟨aRe, haRe_meas, haRe⟩
  rcases hC hr hweakIm huIm hduIm with ⟨aIm, haIm_meas, haIm⟩
  let a : ℂ := ⟨aRe, aIm⟩
  refine ⟨a, ?_, ?_⟩
  · exact hu.aestronglyMeasurable.sub aestronglyMeasurable_const
  · let μ := MeasureTheory.volume.restrict (Metric.ball c r)
    have hduRe_le : eLpNorm duRe 2 μ ≤ eLpNorm du 2 μ := by
      apply eLpNorm_mono
      intro z
      calc
        ‖duRe z‖ ≤ ‖Complex.reCLM‖ * ‖du z‖ := by
          simpa [duRe] using Complex.reCLM.opNorm_comp_le (du z)
        _ = ‖du z‖ := by rw [Complex.reCLM_norm, one_mul]
    have hduIm_le : eLpNorm duIm 2 μ ≤ eLpNorm du 2 μ := by
      apply eLpNorm_mono
      intro z
      calc
        ‖duIm z‖ ≤ ‖Complex.imCLM‖ * ‖du z‖ := by
          simpa [duIm] using Complex.imCLM.opNorm_comp_le (du z)
        _ = ‖du z‖ := by rw [Complex.imCLM_norm, one_mul]
    have haRe' : eLpNorm (fun z ↦ uRe z - aRe) 2 μ ≤
        C * ENNReal.ofReal r * eLpNorm du 2 μ :=
      haRe.trans (by
        change C * ENNReal.ofReal r * eLpNorm duRe 2 μ ≤ _
        gcongr)
    have haIm' : eLpNorm (fun z ↦ uIm z - aIm) 2 μ ≤
        C * ENNReal.ofReal r * eLpNorm du 2 μ :=
      haIm.trans (by
        change C * ENNReal.ofReal r * eLpNorm duIm 2 μ ≤ _
        gcongr)
    have hmono : eLpNorm (fun z : ℂ ↦ u z - a) 2 μ ≤
        eLpNorm (fun z : ℂ ↦
          ‖uRe z - aRe‖ + ‖uIm z - aIm‖) 2 μ := by
      apply eLpNorm_mono
      intro z
      rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      simpa [uRe, uIm, a, Real.norm_eq_abs] using
        Complex.norm_le_abs_re_add_abs_im (u z - a)
    have hadd : eLpNorm (fun z : ℂ ↦
          ‖uRe z - aRe‖ + ‖uIm z - aIm‖) 2 μ ≤
        eLpNorm (fun z : ℂ ↦ uRe z - aRe) 2 μ +
          eLpNorm (fun z : ℂ ↦ uIm z - aIm) 2 μ := by
      have hraw := eLpNorm_add_le haRe_meas.norm haIm_meas.norm
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      simpa only [Pi.add_apply, eLpNorm_norm] using hraw
    calc
      eLpNorm (fun z : ℂ ↦ u z - a) 2 μ
          ≤ eLpNorm (fun z : ℂ ↦
            ‖uRe z - aRe‖ + ‖uIm z - aIm‖) 2 μ := hmono
      _ ≤ eLpNorm (fun z : ℂ ↦ uRe z - aRe) 2 μ +
          eLpNorm (fun z : ℂ ↦ uIm z - aIm) 2 μ := hadd
      _ ≤ (C * ENNReal.ofReal r * eLpNorm du 2 μ) +
          (C * ENNReal.ofReal r * eLpNorm du 2 μ) := add_le_add haRe' haIm'
      _ = (2 * C) * ENNReal.ofReal r * eLpNorm du 2 μ := by ring

/--
%%handwave
name:
  Scale-covariant Poincare estimate for the affine Sobolev remainder
statement:
  There is a finite constant $C$ such that, whenever
  $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, $r>0$, and $\overline B(x,r)\subseteq\Omega$, some $a\in\mathbb C$
  satisfies
  $$
    \|f(y)-Df(x)(y-x)-a\|_{L^2(B(x,r))}
      \leq Cr\,\|Df-Df(x)\|_{L^2(B(x,r))}.
  $$
proof:
  The affine map $y\mapsto Df(x)(y-x)$ has constant weak differential
  $Df(x)$. Subtract it from $f$ and apply the [complex-valued uniform
  Poincare estimate](lean:JJMath.Quasiconformal.complex_valued_euclideanSobolev_poincare_L2_scale_covariant) to the resulting weak Sobolev pair.
-/
theorem localW12_affine_remainder_poincare_L2 :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ},
        IsLocalW12On Ω f df →
        ∀ {x : ℂ} {r : ℝ}, 0 < r → closedBall x r ⊆ Ω →
          ∃ a : ℂ,
            AEStronglyMeasurable
              (fun y : ℂ ↦ f y - df x (y - x) - a)
              (MeasureTheory.volume.restrict (ball x r)) ∧
            eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - a) 2
                (MeasureTheory.volume.restrict (ball x r)) ≤
              C * ENNReal.ofReal r *
                eLpNorm (fun y : ℂ ↦ df y - df x) 2
                  (MeasureTheory.volume.restrict (ball x r)) := by
  rcases complex_valued_euclideanSobolev_poincare_L2_scale_covariant with
    ⟨C, hC_top, hPoincare⟩
  refine ⟨C, hC_top, ?_⟩
  intro Ω f df h x r hr hclosed
  let ℓ : ℂ → ℂ := fun y ↦ df x (y - x)
  let dℓ : ℂ → ℂ →L[ℝ] ℂ := fun _ ↦ df x
  let u : ℂ → ℂ := fun y ↦ f y - ℓ y
  let du : ℂ → ℂ →L[ℝ] ℂ := fun y ↦ df y - dℓ y
  have hℓ_cont : ContDiff ℝ 1 ℓ := by
    exact (df x).contDiff.comp (contDiff_id.sub contDiff_const)
  have hweakℓ_raw :=
    weakDerivativeOn_of_contDiff (Ω := ball x r) hℓ_cont
  have hweakℓ :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        (ball x r) ℓ dℓ := by
    have hfderiv : ∀ y : ℂ, fderiv ℝ ℓ y = df x := by
      intro y
      have hsub := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x
      have hcomp := (df x).hasFDerivAt.comp y hsub
      change fderiv ℝ ((df x) ∘ fun z : ℂ ↦ z - x) y = df x
      exact hcomp.fderiv
    simpa [hfderiv, dℓ] using hweakℓ_raw
  have hweakf :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        (ball x r) f df :=
    h.2.1.mono_set (ball_subset_closedBall.trans hclosed)
  have hweaku :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        (ball x r) u du := by
    simpa [u, du] using hweakf.sub hweakℓ
  have hlocal := h.2.2 (closedBall x r) (isCompact_closedBall _ _) hclosed
  have hf_ball : MemLp f 2
      (MeasureTheory.volume.restrict (ball x r)) :=
    hlocal.1.mono_measure
      (Measure.restrict_mono ball_subset_closedBall le_rfl)
  have hdf_ball : MemLp df 2
      (MeasureTheory.volume.restrict (ball x r)) :=
    hlocal.2.mono_measure
      (Measure.restrict_mono ball_subset_closedBall le_rfl)
  have hℓ_closed : MemLp ℓ 2
      (MeasureTheory.volume.restrict (closedBall x r)) :=
    memLp_restrict_of_isCompact_of_continuousOn
      (isCompact_closedBall x r) hℓ_cont.continuous.continuousOn
  have hℓ_ball : MemLp ℓ 2
      (MeasureTheory.volume.restrict (ball x r)) :=
    hℓ_closed.mono_measure
      (Measure.restrict_mono ball_subset_closedBall le_rfl)
  have hu : MemLp u 2
      (MeasureTheory.volume.restrict (ball x r)) := by
    simpa [u] using hf_ball.sub hℓ_ball
  haveI : IsFiniteMeasure
      (MeasureTheory.volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.2
      (ne_of_lt (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
        (isCompact_closedBall x r).measure_lt_top))
  have hdℓ : MemLp dℓ 2
      (MeasureTheory.volume.restrict (ball x r)) := by
    exact memLp_const (df x)
  have hdu : MemLp du 2
      (MeasureTheory.volume.restrict (ball x r)) := by
    simpa [du] using hdf_ball.sub hdℓ
  simpa [u, du, ℓ, dℓ] using hPoincare hr hweaku hu hdu

/--
%%handwave
name:
  Approximate real differential in the plane
statement:
  A real-linear map $A:\mathbb C\to\mathbb C$ is the approximate
  differential of $f$ at $x$ if, for every $\varepsilon>0$, the relative
  volume in $\overline B(x,r)$ of the set where
  $$
    \|f(y)-f(x)-A(y-x)\|>\varepsilon\|y-x\|
  $$
  tends to zero as $r\downarrow0$.
-/
def HasApproxFDerivAt (f : ℂ → ℂ) (A : ℂ →L[ℝ] ℂ) (x : ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto
      (fun r : ℝ ↦
        MeasureTheory.volume
            {y : ℂ | y ∈ closedBall x r ∧
              ε * ‖y - x‖ < ‖f y - f x - A (y - x)‖} /
          MeasureTheory.volume (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0)

/--
%%handwave
name:
  Vanishing scale-normalized $L^2$ remainder implies approximate differentiability
statement:
  Let $A:\mathbb C\to\mathbb C$ be real-linear. Suppose that
  $f-f(x)-A(\cdot-x)$ belongs to $L^2(B(x,r))$ for every sufficiently small
  $r>0$ and
  $$
    \frac{\|f(y)-f(x)-A(y-x)\|_{L^2(B(x,r))}}{r^2}
      \longrightarrow0.
  $$
  Then $A$ is the approximate differential of $f$ at $x$.
proof:
  For fixed $\varepsilon>0$, split the bad subset of $B(x,r)$ into the inner ball $B(x,\tau r)$ and its complementary annulus. The inner ball has relative area $\tau^2$. On the annulus, bad points satisfy $\|f(y)-f(x)-A(y-x)\|\geq\varepsilon\tau r$, so the $L^2$ Chebyshev inequality bounds their relative area by
  $$
    \frac1{\varepsilon^2\tau^2\pi}
      \left(
        \frac{\|f-f(x)-A(\cdot-x)\|_{L^2(B(x,r))}}{r^2}
      \right)^2.
  $$
  First choose $\tau$ so that $\tau^2$ is arbitrarily small, and then let $r\downarrow0$.
-/
theorem hasApproxFDerivAt_of_tendsto_eLpNorm_affine_remainder_div_sq
    {f : ℂ → ℂ} {A : ℂ →L[ℝ] ℂ} {x : ℂ}
    (hmem : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      MemLp (fun y : ℂ ↦ f y - f x - A (y - x)) 2
        (MeasureTheory.volume.restrict (ball x r)))
    (hq : Tendsto
      (fun r : ℝ ↦
        (eLpNorm (fun y : ℂ ↦ f y - f x - A (y - x)) 2
          (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    HasApproxFDerivAt f A x := by
  intro ε hε
  let rem : ℂ → ℂ := fun y ↦ f y - f x - A (y - x)
  let density : ℝ → ℝ≥0∞ := fun r ↦
    MeasureTheory.volume
        {y : ℂ | y ∈ closedBall x r ∧ ε * ‖y - x‖ < ‖rem y‖} /
      MeasureTheory.volume (closedBall x r)
  have hdensity_ne_top (r : ℝ) : density r ≠ ∞ := by
    have hsub :
        {y : ℂ | y ∈ closedBall x r ∧ ε * ‖y - x‖ < ‖rem y‖} ⊆
          closedBall x r := fun _ hy ↦ hy.1
    have hnum_ne_top :
        MeasureTheory.volume
            {y : ℂ | y ∈ closedBall x r ∧ ε * ‖y - x‖ < ‖rem y‖} ≠ ∞ :=
      measure_ne_top_of_subset hsub (isCompact_closedBall x r).measure_ne_top
    by_cases hden : MeasureTheory.volume (closedBall x r) = 0
    · have hnum : MeasureTheory.volume
          {y : ℂ | y ∈ closedBall x r ∧ ε * ‖y - x‖ < ‖rem y‖} = 0 :=
        measure_mono_null hsub hden
      change MeasureTheory.volume
          {y : ℂ | y ∈ closedBall x r ∧ ε * ‖y - x‖ < ‖rem y‖} /
            MeasureTheory.volume (closedBall x r) ≠ ∞
      rw [hnum, hden]
      simp
    · exact ENNReal.div_ne_top hnum_ne_top hden
  rw [← ENNReal.tendsto_toReal_zero_iff hdensity_ne_top]
  change Tendsto (fun r : ℝ ↦ (density r).toReal)
    (𝓝[>] (0 : ℝ)) (𝓝 0)
  rw [tendsto_order]
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall fun r ↦
      lt_of_lt_of_le hb ENNReal.toReal_nonneg
  · intro b hb
    let τ : ℝ := min (1 / 2) (b / 4)
    have hτ : 0 < τ := by
      dsimp [τ]
      exact lt_min (by norm_num) (by linarith)
    have hτ_one : τ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hτ_sq : τ ^ 2 < b := by
      by_cases hb2 : b ≤ 2
      · have hτ_le : τ ≤ b / 4 := min_le_right _ _
        nlinarith [sq_nonneg τ]
      · have hτ_le : τ ≤ 1 / 2 := min_le_left _ _
        nlinarith [sq_nonneg τ]
    let upper : ℝ → ℝ := fun r ↦
      τ ^ 2 +
        ((eLpNorm rem 2
          (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2) ^ 2 /
            (ε ^ 2 * τ ^ 2 * Real.pi)
    have hden_pos : 0 < ε ^ 2 * τ ^ 2 * Real.pi := by positivity
    have hupper : Tendsto upper (𝓝[>] (0 : ℝ)) (𝓝 (τ ^ 2)) := by
      dsimp [upper, rem]
      have hsq := hq.pow 2
      have hdiv := hsq.div_const (ε ^ 2 * τ ^ 2 * Real.pi)
      simpa using tendsto_const_nhds.add hdiv
    have hupper_lt : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), upper r < b :=
      (tendsto_order.1 hupper).2 b hτ_sq
    have hbound : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
        (density r).toReal ≤ upper r := by
      filter_upwards [self_mem_nhdsWithin, hmem] with r hr hmem_r
      have hr0 : 0 < r := hr
      let μr : Measure ℂ := MeasureTheory.volume.restrict (ball x r)
      haveI : IsFiniteMeasure μr :=
        isFiniteMeasure_restrict.2
          (ne_of_lt (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
            (isCompact_closedBall x r).measure_lt_top))
      let t : ℝ := ε * τ * r
      have ht : 0 < t := by dsimp [t]; positivity
      let S : Set ℂ := {y : ℂ | ENNReal.ofReal t ≤ ‖rem y‖ₑ}
      have hrem_aesm : AEStronglyMeasurable rem μr := by
        change AEStronglyMeasurable
          (fun y : ℂ ↦ f y - f x - A (y - x)) μr
        exact hmem_r.aestronglyMeasurable
      have hS_null : NullMeasurableSet S μr := by
        exact hrem_aesm.enorm.nullMeasurable measurableSet_Ici
      have hcheb :
          ENNReal.ofReal t ^ (2 : ℝ) * μr S ≤
            eLpNorm rem 2 μr ^ (2 : ℝ) := by
        have hcheb' := mul_meas_ge_le_pow_eLpNorm'
          μr (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
          hrem_aesm (ENNReal.ofReal t)
        change ENNReal.ofReal t ^ (2 : ℝ) * μr S ≤
          eLpNorm rem 2 μr ^ (2 : ℝ) at hcheb'
        exact hcheb'
      have hleft_ne_top :
          ENNReal.ofReal t ^ (2 : ℝ) * μr S ≠ ∞ := by
        exact ENNReal.mul_ne_top (by finiteness)
          (measure_ne_top μr S)
      have hcheb_real :=
        (ENNReal.toReal_le_toReal hleft_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by positivity)
            hmem_r.eLpNorm_ne_top)).2 hcheb
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
        ENNReal.toReal_ofReal ht.le, ← ENNReal.toReal_rpow] at hcheb_real
      rw [Real.rpow_two, Real.rpow_two] at hcheb_real
      have hS_bound : μr.real S ≤
          (eLpNorm rem 2 μr).toReal ^ 2 / t ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos ht)).2
        rw [mul_comm]
        exact hcheb_real
      let badClosed : Set ℂ :=
        {y : ℂ | y ∈ closedBall x r ∧
          ε * ‖y - x‖ < ‖rem y‖}
      let badOpen : Set ℂ :=
        {y : ℂ | y ∈ ball x r ∧
          ε * ‖y - x‖ < ‖rem y‖}
      have hbad_ae : badClosed =ᵐ[MeasureTheory.volume] badOpen := by
        filter_upwards [complex_closedBall_ae_eq_ball x r] with y hy
        simpa only [badClosed, badOpen] using
          congrArg (fun p : Prop ↦ p ∧ ε * ‖y - x‖ < ‖rem y‖) hy
      have hbad_sub : badOpen ⊆ closedBall x (τ * r) ∪ (S ∩ ball x r) := by
        intro y hy
        by_cases hinner : ‖y - x‖ ≤ τ * r
        · apply Or.inl
          rw [mem_closedBall, dist_eq_norm]
          exact hinner
        · apply Or.inr
          constructor
          · dsimp [S, t]
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (le_of_lt (by
              have houter : τ * r < ‖y - x‖ := lt_of_not_ge hinner
              nlinarith [hy.2]))
          · exact hy.1
      have hbad_real : MeasureTheory.volume.real badClosed ≤
          (τ * r) ^ 2 * Real.pi + μr.real S := by
        rw [measureReal_congr hbad_ae]
        calc
          MeasureTheory.volume.real badOpen ≤
              MeasureTheory.volume.real
                (closedBall x (τ * r) ∪ (S ∩ ball x r)) :=
            measureReal_mono hbad_sub (measure_ne_top_of_subset (by
              intro y hy
              rcases hy with hy | hy
              · exact Metric.closedBall_subset_closedBall
                  (by nlinarith [hτ_one, hr0]) hy
              · exact ball_subset_closedBall hy.2)
                (isCompact_closedBall x r).measure_ne_top)
          _ ≤ MeasureTheory.volume.real (closedBall x (τ * r)) +
              MeasureTheory.volume.real (S ∩ ball x r) :=
            measureReal_union_le _ _
          _ = (τ * r) ^ 2 * Real.pi + μr.real S := by
            have hclosed : MeasureTheory.volume.real (closedBall x (τ * r)) =
                (τ * r) ^ 2 * Real.pi := by
              rw [measureReal_congr (complex_closedBall_ae_eq_ball x (τ * r)),
                complex_volume_real_ball x (mul_nonneg hτ.le hr0.le)]
            rw [hclosed, measureReal_restrict_apply₀ hS_null]
      have hden_real : MeasureTheory.volume.real (closedBall x r) =
          r ^ 2 * Real.pi := by
        rw [measureReal_congr (complex_closedBall_ae_eq_ball x r),
          complex_volume_real_ball x hr0.le]
      have hdensity_real : (density r).toReal =
          MeasureTheory.volume.real badClosed / (r ^ 2 * Real.pi) := by
        dsimp [density, badClosed]
        rw [ENNReal.toReal_div]
        change MeasureTheory.volume.real badClosed /
            MeasureTheory.volume.real (closedBall x r) = _
        rw [hden_real]
      rw [hdensity_real]
      dsimp [upper]
      calc
        MeasureTheory.volume.real badClosed / (r ^ 2 * Real.pi) ≤
            (((τ * r) ^ 2 * Real.pi) + μr.real S) /
              (r ^ 2 * Real.pi) := by
          gcongr
        _ ≤ (((τ * r) ^ 2 * Real.pi) +
              (eLpNorm rem 2 μr).toReal ^ 2 / t ^ 2) /
              (r ^ 2 * Real.pi) := by
          gcongr
        _ = τ ^ 2 +
            ((eLpNorm rem 2 μr).toReal / r ^ 2) ^ 2 /
              (ε ^ 2 * τ ^ 2 * Real.pi) := by
          dsimp [t]
          field_simp [ne_of_gt hr0, ne_of_gt hε, ne_of_gt hτ,
            ne_of_gt Real.pi_pos]
    filter_upwards [hbound, hupper_lt] with r hle hlt
    exact lt_of_le_of_lt hle hlt

/--
%%handwave
name:
  Local Lebesgue differentiation on planar open sets
statement:
  Let $\Omega\subseteq\mathbb C$ be open and let $f:\Omega\to E$ be locally
  integrable. For almost every $x\in\Omega$,
  $$
    \lim_{r\downarrow0}
      \fint_{\overline B(x,r)}\|f(y)-f(x)\|\,dy=0.
  $$
proof:
  Cover $\Omega$ by countably many open sets on which the corresponding
  zero extension of $f$ is globally integrable. Apply the Lebesgue
  differentiation theorem to each extension. At a point of an open piece,
  every sufficiently small closed ball stays in that piece, so its averages
  agree with the averages of $f$.
-/
theorem ae_tendsto_average_norm_sub_closedBall_of_locallyIntegrableOn
    {E : Type} [NormedAddCommGroup E]
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → E}
    (hf : LocallyIntegrableOn f Ω MeasureTheory.volume) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
      Tendsto
        (fun r : ℝ ↦
          ⨍ y in closedBall x r, ‖f y - f x‖ ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rcases hf.exists_nat_integrableOn with
    ⟨u, hu_open, hΩ_cover, hu_integrable⟩
  let V : ℕ → Set ℂ := fun n ↦ u n ∩ Ω
  have hV_open : ∀ n, IsOpen (V n) := fun n ↦
    (hu_open n).inter hΩ
  have hpiece : ∀ n, ∀ᵐ x ∂MeasureTheory.volume.restrict (V n),
      Tendsto
        (fun r : ℝ ↦
          ⨍ y in closedBall x r, ‖f y - f x‖ ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro n
    let g : ℂ → E := (V n).indicator f
    have hV_meas : MeasurableSet (V n) := (hV_open n).measurableSet
    have hg : Integrable g MeasureTheory.volume := by
      rw [integrable_indicator_iff hV_meas]
      simpa [V] using hu_integrable n
    have hglobal :=
      IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
        (μ := MeasureTheory.volume) hg.locallyIntegrable 0
    filter_upwards [ae_restrict_mem hV_meas, ae_restrict_of_ae hglobal]
      with x hxV hx
    have hxraw :
        Tendsto
          (fun r : ℝ ↦
            ⨍ y in closedBall x r, ‖g y - g x‖ ∂MeasureTheory.volume)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      apply hx (w := fun _ : ℝ ↦ x) (δ := fun r : ℝ ↦ r)
      · exact tendsto_id
      · filter_upwards with r
        simp
    rcases Metric.isOpen_iff.mp (hV_open n) x hxV with
      ⟨ε, hε_pos, hballV⟩
    apply hxraw.congr'
    have heps : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < ε :=
      Filter.Eventually.filter_mono inf_le_left
        ((tendsto_order.1 tendsto_id).2 ε hε_pos)
    filter_upwards [heps] with r hr
    apply setAverage_congr_fun measurableSet_closedBall
    filter_upwards with y hy
    have hyV : y ∈ V n := hballV (lt_of_le_of_lt hy hr)
    simp [g, indicator_of_mem hyV, indicator_of_mem hxV]
  have hΩ_eq : Ω = ⋃ n, V n := by
    rw [← iUnion_inter]
    exact (inter_eq_right.mpr hΩ_cover).symm
  rw [hΩ_eq, ae_restrict_iUnion_iff]
  exact hpiece

/--
%%handwave
name:
  Squared finite $L^2$ norm as an integral
statement:
  If $u:X\to E$ belongs to $L^2(\mu)$, then
  $$
    \|u\|_{L^2(\mu)}^2=\int_X\|u(x)\|^2\,d\mu(x),
  $$
  where the finite extended norm is viewed as a real number.
proof:
  Use the integral formula for the finite $L^2$ norm, identify the exponent
  $1/2$ with the square root, and square it using nonnegativity of the
  integral.
-/
theorem eLpNorm_two_toReal_sq_eq_integral_norm_sq
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {u : X → E} (hu : MemLp u 2 μ) :
    (eLpNorm u 2 μ).toReal ^ (2 : ℕ) =
      ∫ x, ‖u x‖ ^ (2 : ℕ) ∂μ := by
  have h_int : Integrable (fun x : X ↦ ‖u x‖ ^ (2 : ℕ)) μ :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have h_nonneg : 0 ≤ ∫ x, ‖u x‖ ^ (2 : ℕ) ∂μ :=
    integral_nonneg fun x ↦ sq_nonneg ‖u x‖
  have hnorm :
      (eLpNorm u 2 μ).toReal =
        Real.sqrt (∫ x, ‖u x‖ ^ (2 : ℕ) ∂μ) := by
    have hlp :=
      lpNorm_eq_integral_norm_rpow_toReal
        (μ := μ) (f := u) (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num) hu.aestronglyMeasurable
    have htoReal := toReal_eLpNorm
      (μ := μ) (f := u) (p := (2 : ℝ≥0∞)) hu.aestronglyMeasurable
    calc
      (eLpNorm u 2 μ).toReal = lpNorm u 2 μ := htoReal
      _ = (∫ x, ‖u x‖ ^ (2 : ℝ≥0∞).toReal ∂μ) ^
            ((2 : ℝ≥0∞).toReal)⁻¹ := hlp
      _ = (∫ x, ‖u x‖ ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) := by
            norm_num
      _ = Real.sqrt (∫ x, ‖u x‖ ^ (2 : ℕ) ∂μ) := by
            rw [Real.sqrt_eq_rpow]
  calc
    (eLpNorm u 2 μ).toReal ^ (2 : ℕ)
        = (Real.sqrt (∫ x, ‖u x‖ ^ (2 : ℕ) ∂μ)) ^ (2 : ℕ) := by
          rw [hnorm]
    _ = ∫ x, ‖u x‖ ^ (2 : ℕ) ∂μ := by
          rw [Real.sq_sqrt h_nonneg]

/--
%%handwave
name:
  Squared $L^2$ norm as ball volume times mean square
statement:
  If $r>0$ and $u\in L^2(B(x,r),E)$, then
  $$
    \|u\|_{L^2(B(x,r))}^2
      =|B(x,r)|\fint_{B(x,r)}\|u(y)\|^2\,dy.
  $$
proof:
  Use [the integral formula for the squared $L^2$ norm](lean:JJMath.Quasiconformal.eLpNorm_two_toReal_sq_eq_integral_norm_sq) and unfold the average. The positive finite ball volume cancels its reciprocal.
-/
theorem eLpNorm_two_toReal_sq_eq_volume_real_mul_setAverage_norm_sq
    {E : Type} [NormedAddCommGroup E] {u : ℂ → E}
    (x : ℂ) {r : ℝ} (hr : 0 < r)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict (ball x r))) :
    (eLpNorm u 2
        (MeasureTheory.volume.restrict (ball x r))).toReal ^ 2 =
      MeasureTheory.volume.real (ball x r) *
        (⨍ y in ball x r, ‖u y‖ ^ 2 ∂MeasureTheory.volume) := by
  rw [eLpNorm_two_toReal_sq_eq_integral_norm_sq hu]
  simp only [average_eq, smul_eq_mul, measureReal_restrict_apply_univ]
  have hvol_pos : 0 < MeasureTheory.volume.real (ball x r) := by
    rw [complex_volume_real_ball x hr.le]
    positivity
  field_simp

/--
%%handwave
name:
  $L^2$ norm of a constant on a planar ball
statement:
  If $r>0$ and $c$ belongs to a normed additive group, then
  $$
    \|c\|_{L^2(B(x,r))}=\|c\|r\sqrt\pi.
  $$
proof:
  The $L^2$ norm of a constant is its norm times the square root of the measure, and $|B(x,r)|=\pi r^2$.
-/
theorem eLpNorm_const_two_ball_toReal
    {E : Type} [NormedAddCommGroup E] (c : E) (x : ℂ)
    {r : ℝ} (hr : 0 < r) :
    (eLpNorm (fun _ : ℂ ↦ c) 2
      (MeasureTheory.volume.restrict (ball x r))).toReal =
        ‖c‖ * (r * Real.sqrt Real.pi) := by
  rw [toReal_eLpNorm aestronglyMeasurable_const,
    lpNorm_const' (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)]
  norm_num
  left
  rw [complex_volume_real_ball x hr.le, ← Real.sqrt_eq_rpow]
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs, abs_of_pos hr]

/--
%%handwave
name:
  Scale bound for a linear map on a planar ball
statement:
  For a real-linear map $A:\mathbb C\to\mathbb C$ and $r>0$,
  $$
    \frac{\|A(y-x)\|_{L^2(B(x,r))}}r
      \leq \|A\|\sqrt\pi\,r.
  $$
proof:
  On $B(x,r)$ one has $\|A(y-x)\|\leq\|A\|r$. Bound the $L^2$ norm by the norm of this constant function and use $|B(x,r)|=\pi r^2$.
-/
theorem eLpNorm_apply_sub_center_toReal_div_radius_le
    (A : ℂ →L[ℝ] ℂ) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    (eLpNorm (fun y : ℂ ↦ A (y - x)) 2
      (MeasureTheory.volume.restrict (ball x r))).toReal / r ≤
        ‖A‖ * Real.sqrt Real.pi * r := by
  let μ : Measure ℂ := MeasureTheory.volume.restrict (ball x r)
  have hmono :
      eLpNorm (fun y : ℂ ↦ A (y - x)) 2 μ ≤
        eLpNorm (fun _ : ℂ ↦ ‖A‖ * r) 2 μ := by
    apply eLpNorm_mono_ae_real
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    calc
      ‖A (y - x)‖ ≤ ‖A‖ * ‖y - x‖ := A.le_opNorm (y - x)
      _ ≤ ‖A‖ * r := by
        gcongr
        rw [mem_ball, dist_eq_norm] at hy
        exact le_of_lt hy
  have hconst_ne_top :
      eLpNorm (fun _ : ℂ ↦ ‖A‖ * r) 2 μ ≠ ∞ := by
    haveI : IsFiniteMeasure μ :=
      isFiniteMeasure_restrict.2
        (ne_of_lt (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
          (isCompact_closedBall x r).measure_lt_top))
    exact (memLp_const (‖A‖ * r)).eLpNorm_ne_top
  have hreal := (ENNReal.toReal_le_toReal
    (ne_top_of_le_ne_top hconst_ne_top hmono) hconst_ne_top).2 hmono
  have hconst_real :
      (eLpNorm (fun _ : ℂ ↦ ‖A‖ * r) 2 μ).toReal =
        (‖A‖ * r) * (r * Real.sqrt Real.pi) := by
    rw [toReal_eLpNorm aestronglyMeasurable_const,
      lpNorm_const' (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)]
    norm_num
    have hvol : μ.real Set.univ = r ^ 2 * Real.pi := by
      simp [μ, complex_volume_real_ball x hr.le]
    rw [hvol, ← Real.sqrt_eq_rpow]
    rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs, abs_of_pos hr]
  rw [hconst_real] at hreal
  apply (div_le_iff₀ hr).2
  calc
    (eLpNorm (fun y : ℂ ↦ A (y - x)) 2 μ).toReal ≤
        (‖A‖ * r) * (r * Real.sqrt Real.pi) := hreal
    _ = (‖A‖ * Real.sqrt Real.pi * r) * r := by ring

/--
%%handwave
name:
  Comparing two constants by nested-ball $L^2$ errors
statement:
  Let $0<s\leq r$, let $u:B(x,r)\to E$, and let $a,b\in E$. If
  $u-a\in L^2(B(x,r))$ and $u-b\in L^2(B(x,s))$, then
  $$
    \|a-b\|\sqrt{|B(x,s)|}
      \leq \|u-a\|_{L^2(B(x,r))}
        +\|u-b\|_{L^2(B(x,s))}.
  $$
proof:
  Restrict $u-a$ to the smaller ball. The constant function $a-b$ is the
  difference $(u-b)-(u-a)$, so the $L^2$ triangle inequality gives the
  estimate. Its $L^2$ norm is $\|a-b\|\sqrt{|B(x,s)|}$.
-/
theorem norm_sub_mul_sqrt_volume_real_ball_le_eLpNorm_add
    {E : Type} [NormedAddCommGroup E] {u : ℂ → E}
    {x : ℂ} {r s : ℝ} (hsr : s ≤ r) {a b : E}
    (hua : MemLp (fun y : ℂ ↦ u y - a) 2
      (MeasureTheory.volume.restrict (ball x r)))
    (hub : MemLp (fun y : ℂ ↦ u y - b) 2
      (MeasureTheory.volume.restrict (ball x s))) :
    ‖a - b‖ * Real.sqrt (MeasureTheory.volume.real (ball x s)) ≤
      (eLpNorm (fun y : ℂ ↦ u y - a) 2
        (MeasureTheory.volume.restrict (ball x r))).toReal +
      (eLpNorm (fun y : ℂ ↦ u y - b) 2
        (MeasureTheory.volume.restrict (ball x s))).toReal := by
  let μs : Measure ℂ := MeasureTheory.volume.restrict (ball x s)
  have hball : ball x s ⊆ ball x r := ball_subset_ball hsr
  have hua_s : MemLp (fun y : ℂ ↦ u y - a) 2 μs :=
    hua.mono_measure (Measure.restrict_mono hball le_rfl)
  have htri :
      eLpNorm (fun _ : ℂ ↦ a - b) 2 μs ≤
        eLpNorm (fun y : ℂ ↦ u y - b) 2 μs +
          eLpNorm (fun y : ℂ ↦ u y - a) 2 μs := by
    have hraw := eLpNorm_sub_le hub.aestronglyMeasurable
      hua_s.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hfun :
        ((fun y : ℂ ↦ u y - b) - fun y : ℂ ↦ u y - a) =
          fun _ : ℂ ↦ a - b := by
      funext y
      simp only [Pi.sub_apply]
      abel
    rw [hfun] at hraw
    simpa [μs] using hraw
  have hconst : MemLp (fun _ : ℂ ↦ a - b) 2 μs := by
    haveI : IsFiniteMeasure μs :=
      isFiniteMeasure_restrict.2
        (ne_of_lt (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
          (isCompact_closedBall x s).measure_lt_top))
    exact memLp_const (a - b)
  have hright_ne_top :
      eLpNorm (fun y : ℂ ↦ u y - b) 2 μs +
          eLpNorm (fun y : ℂ ↦ u y - a) 2 μs ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hub.eLpNorm_ne_top, hua_s.eLpNorm_ne_top⟩
  have hreal :=
    (ENNReal.toReal_le_toReal hconst.eLpNorm_ne_top hright_ne_top).2 htri
  rw [ENNReal.toReal_add hub.eLpNorm_ne_top hua_s.eLpNorm_ne_top,
    toReal_eLpNorm aestronglyMeasurable_const,
    lpNorm_const' (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)] at hreal
  have hmeasure : μs.real univ = MeasureTheory.volume.real (ball x s) := by
    simp [μs]
  rw [hmeasure] at hreal
  norm_num at hreal
  have hmono :
      (eLpNorm (fun y : ℂ ↦ u y - a) 2 μs).toReal ≤
        (eLpNorm (fun y : ℂ ↦ u y - a) 2
          (MeasureTheory.volume.restrict (ball x r))).toReal := by
    apply ENNReal.toReal_mono hua.eLpNorm_ne_top
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hball le_rfl)
  rw [Real.sqrt_eq_rpow]
  calc
    ‖a - b‖ * MeasureTheory.volume.real (ball x s) ^ (1 / 2 : ℝ)
        ≤ (eLpNorm (fun y : ℂ ↦ u y - b) 2
              (MeasureTheory.volume.restrict (ball x s))).toReal +
            (eLpNorm (fun y : ℂ ↦ u y - a) 2 μs).toReal := hreal
    _ ≤ (eLpNorm (fun y : ℂ ↦ u y - b) 2
              (MeasureTheory.volume.restrict (ball x s))).toReal +
            (eLpNorm (fun y : ℂ ↦ u y - a) 2
              (MeasureTheory.volume.restrict (ball x r))).toReal :=
          add_le_add_right hmono _
    _ = (eLpNorm (fun y : ℂ ↦ u y - a) 2
              (MeasureTheory.volume.restrict (ball x r))).toReal +
            (eLpNorm (fun y : ℂ ↦ u y - b) 2
              (MeasureTheory.volume.restrict (ball x s))).toReal := add_comm _ _

/--
%%handwave
name:
  Explicit planar nested-ball comparison of constants
statement:
  Under the same hypotheses, if $0<s\leq r$, then
  $$
    \|a-b\|s\sqrt\pi
      \leq \|u-a\|_{L^2(B(x,r))}
        +\|u-b\|_{L^2(B(x,s))}.
  $$
proof:
  Apply [the nested-ball $L^2$ comparison](lean:JJMath.Quasiconformal.norm_sub_mul_sqrt_volume_real_ball_le_eLpNorm_add) and use $|B(x,s)|=\pi s^2$.
-/
theorem norm_sub_mul_radius_mul_sqrt_pi_le_eLpNorm_add
    {E : Type} [NormedAddCommGroup E] {u : ℂ → E}
    {x : ℂ} {r s : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    {a b : E}
    (hua : MemLp (fun y : ℂ ↦ u y - a) 2
      (MeasureTheory.volume.restrict (ball x r)))
    (hub : MemLp (fun y : ℂ ↦ u y - b) 2
      (MeasureTheory.volume.restrict (ball x s))) :
    ‖a - b‖ * (s * Real.sqrt Real.pi) ≤
      (eLpNorm (fun y : ℂ ↦ u y - a) 2
        (MeasureTheory.volume.restrict (ball x r))).toReal +
      (eLpNorm (fun y : ℂ ↦ u y - b) 2
        (MeasureTheory.volume.restrict (ball x s))).toReal := by
  have h := norm_sub_mul_sqrt_volume_real_ball_le_eLpNorm_add hsr hua hub
  rw [complex_volume_real_ball x hs.le] at h
  have hsqrt : Real.sqrt (s ^ 2 * Real.pi) = s * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs, abs_of_pos hs]
  rwa [hsqrt] at h

/--
%%handwave
name:
  Half-scale variation of centers with vanishing normalized error
statement:
  Let $u$ be defined on the plane and let $a_r$ be constants such that
  $u-a_r\in L^2(B(x,r))$ for all sufficiently small $r>0$. If
  $$
    \frac{\|u-a_r\|_{L^2(B(x,r))}}{r^2}\longrightarrow0,
  $$
  then
  $$
    \frac{\|a_r-a_{r/2}\|}{r}\longrightarrow0.
  $$
proof:
  Apply [the explicit nested-ball comparison of constants](lean:JJMath.Quasiconformal.norm_sub_mul_radius_mul_sqrt_pi_le_eLpNorm_add) to $B(x,r/2)\subseteq B(x,r)$. After division by $r^2$, the two error terms are respectively the normalized error at $r$ and one quarter of the normalized error at $r/2$.
-/
theorem tendsto_norm_sub_center_half_div_radius
    {E : Type} [NormedAddCommGroup E] {u : ℂ → E}
    {x : ℂ} {a : ℝ → E}
    (hmem : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      MemLp (fun y : ℂ ↦ u y - a r) 2
        (MeasureTheory.volume.restrict (ball x r)))
    (hq : Tendsto
      (fun r : ℝ ↦
        (eLpNorm (fun y : ℂ ↦ u y - a r) 2
          (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun r : ℝ ↦ ‖a r - a (r / 2)‖ / r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hhalf : Tendsto (fun r : ℝ ↦ r / 2)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have ht : Tendsto (fun r : ℝ ↦ (1 / 2 : ℝ) * r)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using
          (tendsto_const_nhds.mul
            (tendsto_id.mono_left nhdsWithin_le_nhds :
              Tendsto (fun r : ℝ ↦ r) (𝓝[>] (0 : ℝ)) (𝓝 0)))
      simpa [div_eq_mul_inv, mul_comm] using ht
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : 0 < r := hr
      exact div_pos hr0 (by norm_num)
  have hq_half : Tendsto
      (fun r : ℝ ↦
        (eLpNorm (fun y : ℂ ↦ u y - a (r / 2)) 2
          (MeasureTheory.volume.restrict (ball x (r / 2)))).toReal /
            (r / 2) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := hq.comp hhalf
  let upper : ℝ → ℝ := fun r ↦
    (2 / Real.sqrt Real.pi) *
      ((eLpNorm (fun y : ℂ ↦ u y - a r) 2
          (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2 +
        (1 / 4) *
          ((eLpNorm (fun y : ℂ ↦ u y - a (r / 2)) 2
            (MeasureTheory.volume.restrict (ball x (r / 2)))).toReal /
              (r / 2) ^ 2))
  have hupper : Tendsto upper (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    dsimp [upper]
    simpa using tendsto_const_nhds.mul
      (hq.add (tendsto_const_nhds.mul hq_half))
  have hmem_half : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      MemLp (fun y : ℂ ↦ u y - a (r / 2)) 2
        (MeasureTheory.volume.restrict (ball x (r / 2))) :=
    hhalf.eventually hmem
  have hbounds : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ ‖a r - a (r / 2)‖ / r ∧
        ‖a r - a (r / 2)‖ / r ≤ upper r := by
    filter_upwards [self_mem_nhdsWithin, hmem, hmem_half]
      with r hr hmem_r hmem_half_r
    have hr0 : 0 < r := hr
    have hrhalf : 0 < r / 2 := div_pos hr0 (by norm_num)
    have hcompare := norm_sub_mul_radius_mul_sqrt_pi_le_eLpNorm_add
      hrhalf (by linarith : r / 2 ≤ r) hmem_r hmem_half_r
    constructor
    · positivity
    · dsimp [upper]
      have hsqrt_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
      rw [div_le_iff₀ hr0]
      have hscaled :
          ‖a r - a (r / 2)‖ * (r * Real.sqrt Real.pi) ≤
            2 *
              ((eLpNorm (fun y : ℂ ↦ u y - a r) 2
                  (MeasureTheory.volume.restrict (ball x r))).toReal +
                (eLpNorm (fun y : ℂ ↦ u y - a (r / 2)) 2
                  (MeasureTheory.volume.restrict (ball x (r / 2)))).toReal) := by
        calc
          ‖a r - a (r / 2)‖ * (r * Real.sqrt Real.pi)
              = 2 * (‖a r - a (r / 2)‖ *
                  ((r / 2) * Real.sqrt Real.pi)) := by ring
          _ ≤ 2 *
              ((eLpNorm (fun y : ℂ ↦ u y - a r) 2
                  (MeasureTheory.volume.restrict (ball x r))).toReal +
                (eLpNorm (fun y : ℂ ↦ u y - a (r / 2)) 2
                  (MeasureTheory.volume.restrict (ball x (r / 2)))).toReal) := by
                gcongr
      calc
        ‖a r - a (r / 2)‖ ≤
            2 *
                ((eLpNorm (fun y : ℂ ↦ u y - a r) 2
                    (MeasureTheory.volume.restrict (ball x r))).toReal +
                  (eLpNorm (fun y : ℂ ↦ u y - a (r / 2)) 2
                    (MeasureTheory.volume.restrict (ball x (r / 2)))).toReal) /
              (r * Real.sqrt Real.pi) :=
          (le_div_iff₀ (mul_pos hr0 hsqrt_pos)).2 hscaled
        _ = (2 / Real.sqrt Real.pi) *
            ((eLpNorm (fun y : ℂ ↦ u y - a r) 2
                (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2 +
              (1 / 4) *
                ((eLpNorm (fun y : ℂ ↦ u y - a (r / 2)) 2
                  (MeasureTheory.volume.restrict (ball x (r / 2)))).toReal /
                    (r / 2) ^ 2)) * r := by
              field_simp [ne_of_gt hr0, ne_of_gt hsqrt_pos]
              ring
  exact squeeze_zero' (hbounds.mono fun _ hr ↦ hr.1)
    (hbounds.mono fun _ hr ↦ hr.2) hupper

/--
%%handwave
name:
  Identification of moving centers from a reference value
statement:
  Let $u$ be defined on the plane, let $a_r$ be constants, and let $c$ be
  fixed. Suppose that $u-a_r$ and $u-c$ belong to $L^2(B(x,r))$ for all
  sufficiently small $r>0$, and that
  $$
    \frac{\|u-a_r\|_{L^2(B(x,r))}}{r^2}\longrightarrow0,
    \qquad
    \frac{\|u-c\|_{L^2(B(x,r))}}r\longrightarrow0.
  $$
  Then $a_r\to c$ as $r\downarrow0$.
proof:
  Apply [the explicit comparison of two constants on a planar ball](lean:JJMath.Quasiconformal.norm_sub_mul_radius_mul_sqrt_pi_le_eLpNorm_add) with both radii equal to $r$. After division by $r\sqrt\pi$, the first error is $r$ times its $r^2$-normalized value and the second is its $r$-normalized value, so both terms vanish.
-/
theorem tendsto_center_of_eLpNorm_div_sq_and_reference_div_radius
    {E : Type} [NormedAddCommGroup E] {u : ℂ → E}
    {x : ℂ} {a : ℝ → E} {c : E}
    (hmem_a : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      MemLp (fun y : ℂ ↦ u y - a r) 2
        (MeasureTheory.volume.restrict (ball x r)))
    (hqa : Tendsto
      (fun r : ℝ ↦
        (eLpNorm (fun y : ℂ ↦ u y - a r) 2
          (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hmem_c : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      MemLp (fun y : ℂ ↦ u y - c) 2
        (MeasureTheory.volume.restrict (ball x r)))
    (hqc : Tendsto
      (fun r : ℝ ↦
        (eLpNorm (fun y : ℂ ↦ u y - c) 2
          (MeasureTheory.volume.restrict (ball x r))).toReal / r)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun r : ℝ ↦ ‖a r - c‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let upper : ℝ → ℝ := fun r ↦
    (1 / Real.sqrt Real.pi) *
      (((eLpNorm (fun y : ℂ ↦ u y - a r) 2
          (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2) * r +
        (eLpNorm (fun y : ℂ ↦ u y - c) 2
          (MeasureTheory.volume.restrict (ball x r))).toReal / r)
  have hr_zero : Tendsto (fun r : ℝ ↦ r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hupper : Tendsto upper (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    dsimp [upper]
    simpa using tendsto_const_nhds.mul ((hqa.mul hr_zero).add hqc)
  have hbounds : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ ‖a r - c‖ ∧ ‖a r - c‖ ≤ upper r := by
    filter_upwards [self_mem_nhdsWithin, hmem_a, hmem_c]
      with r hr hmem_a_r hmem_c_r
    have hr0 : 0 < r := hr
    have hcompare := norm_sub_mul_radius_mul_sqrt_pi_le_eLpNorm_add
      hr0 (le_refl r) hmem_a_r hmem_c_r
    constructor
    · positivity
    · dsimp [upper]
      have hsqrt_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
      calc
        ‖a r - c‖ ≤
            (((eLpNorm (fun y : ℂ ↦ u y - a r) 2
                  (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2) * r +
                (eLpNorm (fun y : ℂ ↦ u y - c) 2
                  (MeasureTheory.volume.restrict (ball x r))).toReal / r) /
              Real.sqrt Real.pi := by
          apply (le_div_iff₀ hsqrt_pos).2
          calc
            ‖a r - c‖ * Real.sqrt Real.pi
              ≤ ((eLpNorm (fun y : ℂ ↦ u y - a r) 2
                  (MeasureTheory.volume.restrict (ball x r))).toReal +
                (eLpNorm (fun y : ℂ ↦ u y - c) 2
                  (MeasureTheory.volume.restrict (ball x r))).toReal) / r := by
                apply (le_div_iff₀ hr0).2
                calc
                  ‖a r - c‖ * Real.sqrt Real.pi * r =
                      ‖a r - c‖ * (r * Real.sqrt Real.pi) := by ring
                  _ ≤ _ := hcompare
            _ = ((eLpNorm (fun y : ℂ ↦ u y - a r) 2
                (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2) * r +
              (eLpNorm (fun y : ℂ ↦ u y - c) 2
                (MeasureTheory.volume.restrict (ball x r))).toReal / r := by
              field_simp [ne_of_gt hr0]
        _ = 1 / Real.sqrt Real.pi *
            (((eLpNorm (fun y : ℂ ↦ u y - a r) 2
                (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2) * r +
              (eLpNorm (fun y : ℂ ↦ u y - c) 2
                (MeasureTheory.volume.restrict (ball x r))).toReal / r) := by
          ring
  exact squeeze_zero' (hbounds.mono fun _ hr ↦ hr.1)
    (hbounds.mono fun _ hr ↦ hr.2) hupper

/--
%%handwave
name:
  Dyadic upgrade from half-scale control to first-order convergence
statement:
  Let $a_r$ be points in a normed additive group and let $c$ be fixed. If
  $a_r\to c$ and
  $$
    \frac{\|a_r-a_{r/2}\|}{r}\longrightarrow0,
  $$
  then
  $$
    \frac{\|a_r-c\|}{r}\longrightarrow0
    \qquad(r\downarrow0).
  $$
proof:
  Given $\varepsilon>0$, the half-scale increments are at most
  $\varepsilon s/4$ at every sufficiently small scale $s$. Telescope from
  $r$ through $r2^{-n}$; the geometric sum bounds
  $\|a_r-a_{r2^{-n}}\|$ by $\varepsilon r/2$, uniformly in $n$. Since
  $a_{r2^{-n}}\to c$, pass to the limit in $n$ and divide by $r$.
-/
theorem tendsto_norm_sub_center_div_radius_of_half
    {E : Type} [NormedAddCommGroup E] {a : ℝ → E} {c : E}
    (hcenter : Tendsto (fun r : ℝ ↦ ‖a r - c‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hhalf : Tendsto (fun r : ℝ ↦ ‖a r - a (r / 2)‖ / r)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun r : ℝ ↦ ‖a r - c‖ / r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact lt_of_lt_of_le hb (div_nonneg (norm_nonneg _) (le_of_lt hr))
  · intro b hb
    let η : ℝ := b / 4
    have hη : 0 < η := by dsimp [η]; linarith
    have hinc_event : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
        ‖a s - a (s / 2)‖ / s < η :=
      (tendsto_order.1 hhalf).2 η hη
    rcases Metric.mem_nhdsWithin_iff.1 hinc_event with
      ⟨δ, hδ, hδ_bound⟩
    have hr_small : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < δ :=
      Filter.Eventually.filter_mono inf_le_left
        ((tendsto_order.1 tendsto_id).2 δ hδ)
    filter_upwards [self_mem_nhdsWithin, hr_small] with r hr hrδ
    have hr0 : 0 < r := hr
    let q : ℝ := 1 / 2
    have hq0 : 0 < q := by dsimp [q]; norm_num
    have hq1 : q < 1 := by dsimp [q]; norm_num
    have hinc (n : ℕ) :
        ‖a (r * q ^ n) - a (r * q ^ (n + 1))‖ ≤
          η * (r * q ^ n) := by
      have hs0 : 0 < r * q ^ n := mul_pos hr0 (pow_pos hq0 n)
      have hsδ : r * q ^ n < δ := by
        have hpow_le : q ^ n ≤ 1 := pow_le_one₀ hq0.le hq1.le
        exact lt_of_le_of_lt (by nlinarith) hrδ
      have hs_mem : r * q ^ n ∈ ball (0 : ℝ) δ ∩ Ioi 0 := by
        constructor
        · rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs0]
          exact hsδ
        · exact hs0
      have hraw := hδ_bound hs_mem
      change ‖a (r * q ^ n) - a ((r * q ^ n) / 2)‖ /
          (r * q ^ n) < η at hraw
      have hstep : (r * q ^ n) / 2 = r * q ^ (n + 1) := by
        dsimp [q]
        rw [pow_succ]
        ring
      rw [hstep] at hraw
      exact le_of_lt ((div_lt_iff₀ hs0).1 hraw)
    have htel : ∀ n : ℕ,
        ‖a r - a (r * q ^ n)‖ ≤
          2 * η * r * (1 - q ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          calc
            ‖a r - a (r * q ^ (n + 1))‖ =
                ‖(a r - a (r * q ^ n)) +
                  (a (r * q ^ n) - a (r * q ^ (n + 1)))‖ := by
                    congr 1
                    abel
            _ ≤ ‖a r - a (r * q ^ n)‖ +
                ‖a (r * q ^ n) - a (r * q ^ (n + 1))‖ := norm_add_le _ _
            _ ≤ 2 * η * r * (1 - q ^ n) + η * (r * q ^ n) :=
              add_le_add ih (hinc n)
            _ = 2 * η * r * (1 - q ^ (n + 1)) := by
              dsimp [q]
              rw [pow_succ]
              ring
    have hcoarse (n : ℕ) :
        ‖a r - a (r * q ^ n)‖ ≤ 2 * η * r := by
      calc
        ‖a r - a (r * q ^ n)‖ ≤
            2 * η * r * (1 - q ^ n) := htel n
        _ ≤ 2 * η * r := by
          have hpow_nonneg : 0 ≤ q ^ n := (pow_pos hq0 n).le
          have hcoeff : 0 ≤ 2 * η * r := by positivity
          nlinarith
    have hscale : Tendsto (fun n : ℕ ↦ r * q ^ n)
        atTop (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · simpa using tendsto_const_nhds.mul
          (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1)
      · exact Filter.Eventually.of_forall fun n ↦ mul_pos hr0 (pow_pos hq0 n)
    have ha : Tendsto a (𝓝[>] (0 : ℝ)) (𝓝 c) :=
      tendsto_iff_norm_sub_tendsto_zero.2 hcenter
    have haseq : Tendsto (fun n : ℕ ↦ a (r * q ^ n))
        atTop (𝓝 c) := ha.comp hscale
    have hdist : Tendsto (fun n : ℕ ↦ ‖a r - a (r * q ^ n)‖)
        atTop (𝓝 ‖a r - c‖) := by
      simpa using (tendsto_const_nhds.sub haseq).norm
    have hlimit : ‖a r - c‖ ≤ 2 * η * r :=
      le_of_tendsto hdist (Filter.Eventually.of_forall hcoarse)
    apply (div_lt_iff₀ hr0).2
    dsimp [η] at hlimit
    nlinarith

/--
%%handwave
name:
  Mean-square difference controlled by first and second moments
statement:
  In a real inner-product space, for every $a,b$,
  $$
    \|a-b\|^2
      \leq \bigl|\|a\|^2-\|b\|^2\bigr|
        +2\|b\|\,\|a-b\|.
  $$
proof:
  Expand $\|a-b\|^2$ using the inner product, rewrite it as the difference
  of the squared norms minus $2\langle a-b,b\rangle$, and apply
  Cauchy--Schwarz.
-/
theorem norm_sub_sq_le_abs_norm_sq_sub_add
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) :
    ‖a - b‖ ^ 2 ≤ |‖a‖ ^ 2 - ‖b‖ ^ 2| +
      2 * ‖b‖ * ‖a - b‖ := by
  have hid :
      ‖a - b‖ ^ 2 =
        (‖a‖ ^ 2 - ‖b‖ ^ 2) - 2 * inner ℝ (a - b) b := by
    rw [norm_sub_sq_real]
    simp only [inner_sub_left, real_inner_self_eq_norm_sq]
    ring
  rw [hid]
  calc
    (‖a‖ ^ 2 - ‖b‖ ^ 2) - 2 * inner ℝ (a - b) b
        ≤ |‖a‖ ^ 2 - ‖b‖ ^ 2| + |2 * inner ℝ (a - b) b| := by
          linarith [le_abs_self (‖a‖ ^ 2 - ‖b‖ ^ 2),
            neg_le_abs (2 * inner ℝ (a - b) b)]
    _ ≤ |‖a‖ ^ 2 - ‖b‖ ^ 2| + 2 * ‖b‖ * ‖a - b‖ := by
      gcongr
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_real_inner_le_norm (a - b) b,
        norm_nonneg (a - b), norm_nonneg b]

/--
%%handwave
name:
  Mean-square Lebesgue differentiation for a global $L^2$ field
statement:
  Let $f:\mathbb C\to E$ take values in a real inner-product space and
  satisfy $f\in L^2(\mathbb C)$. Then for almost every $x$,
  $$
    \lim_{r\downarrow0}
      \fint_{\overline B(x,r)}\|f(y)-f(x)\|^2\,dy=0.
  $$
proof:
  Lebesgue differentiation applies both to $f$ and to the integrable scalar
  function $\|f\|^2$. Bound the mean-square difference by [the sum of their two mean oscillations](lean:JJMath.Quasiconformal.norm_sub_sq_le_abs_norm_sq_sub_add) and squeeze.
-/
theorem ae_tendsto_average_norm_sq_sub_closedBall_of_memLp
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : ℂ → E} (hf : MemLp f 2 MeasureTheory.volume) :
    ∀ᵐ x ∂MeasureTheory.volume,
      Tendsto
        (fun r : ℝ ↦
          ⨍ y in closedBall x r, ‖f y - f x‖ ^ 2
            ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let q : ℂ → ℝ := fun y ↦ ‖f y‖ ^ 2
  have hq_int : Integrable q MeasureTheory.volume := by
    simpa [q] using hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hf_lebesgue : ∀ᵐ x ∂MeasureTheory.volume,
      Tendsto
        (fun r : ℝ ↦
          ⨍ y in closedBall x r, ‖f y - f x‖ ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using
      (ae_tendsto_average_norm_sub_closedBall_of_locallyIntegrableOn
        (f := f) isOpen_univ
          ((hf.locallyIntegrable (by norm_num)).locallyIntegrableOn univ))
  have hq_lebesgue : ∀ᵐ x ∂MeasureTheory.volume,
      Tendsto
        (fun r : ℝ ↦
          ⨍ y in closedBall x r, |q y - q x| ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [Real.norm_eq_abs] using
      (ae_tendsto_average_norm_sub_closedBall_of_locallyIntegrableOn
        (f := q) isOpen_univ
          (hq_int.locallyIntegrable.locallyIntegrableOn univ))
  filter_upwards [hf_lebesgue, hq_lebesgue] with x hfx hqx
  let k : ℝ := 2 * ‖f x‖
  have hupper_tendsto :
      Tendsto
        (fun r : ℝ ↦
          (⨍ y in closedBall x r, |q y - q x|
              ∂MeasureTheory.volume) +
            k * (⨍ y in closedBall x r, ‖f y - f x‖
              ∂MeasureTheory.volume))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hqx.add (tendsto_const_nhds.mul hfx)
  have hbounds : ∀ r : ℝ,
      0 ≤ ⨍ y in closedBall x r, ‖f y - f x‖ ^ 2
          ∂MeasureTheory.volume ∧
      (⨍ y in closedBall x r, ‖f y - f x‖ ^ 2
          ∂MeasureTheory.volume) ≤
        (⨍ y in closedBall x r, |q y - q x|
          ∂MeasureTheory.volume) +
          k * (⨍ y in closedBall x r, ‖f y - f x‖
            ∂MeasureTheory.volume) := by
    intro r
    let μr : Measure ℂ :=
      MeasureTheory.volume.restrict (closedBall x r)
    haveI : IsFiniteMeasure μr :=
      isFiniteMeasure_restrict.2 (isCompact_closedBall x r).measure_ne_top
    have hf_r : MemLp f 2 μr := hf.mono_measure Measure.restrict_le_self
    have hdiff_r : MemLp (fun y ↦ f y - f x) 2 μr :=
      hf_r.sub (memLp_const (f x))
    have hsq_int : Integrable (fun y ↦ ‖f y - f x‖ ^ 2) μr :=
      hdiff_r.integrable_norm_pow (by norm_num)
    have hdiff_int : Integrable (fun y ↦ ‖f y - f x‖) μr :=
      (hdiff_r.integrable (by norm_num)).norm
    have hq_r : Integrable q μr :=
      hq_int.mono_measure Measure.restrict_le_self
    have hqdiff_int : Integrable (fun y ↦ |q y - q x|) μr :=
      (hq_r.sub (integrable_const (q x))).abs
    have hkdiff_int : Integrable (fun y ↦ k * ‖f y - f x‖) μr :=
      hdiff_int.const_mul k
    have hpoint : ∀ y : ℂ,
        ‖f y - f x‖ ^ 2 ≤
          |q y - q x| + k * ‖f y - f x‖ := by
      intro y
      simpa [q, k, mul_assoc] using
        norm_sub_sq_le_abs_norm_sq_sub_add (f y) (f x)
    have hint_le :
        ∫ y, ‖f y - f x‖ ^ 2 ∂μr ≤
          ∫ y, |q y - q x| + k * ‖f y - f x‖ ∂μr :=
      integral_mono hsq_int (hqdiff_int.add hkdiff_int) hpoint
    have havg_le :
        (⨍ y, ‖f y - f x‖ ^ 2 ∂μr) ≤
          ⨍ y, |q y - q x| + k * ‖f y - f x‖ ∂μr := by
      simp only [average_eq, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left hint_le (by positivity)
    have havg_rhs :
        (⨍ y, |q y - q x| + k * ‖f y - f x‖ ∂μr) =
          (⨍ y, |q y - q x| ∂μr) +
            k * (⨍ y, ‖f y - f x‖ ∂μr) := by
      simp only [average_eq, smul_eq_mul]
      rw [integral_add hqdiff_int hkdiff_int, integral_const_mul]
      ring
    constructor
    · simp only [setAverage_eq, smul_eq_mul]
      positivity
    · simpa [μr, havg_rhs] using havg_le
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun r ↦ (hbounds r).1)
    (Filter.Eventually.of_forall fun r ↦ (hbounds r).2)
    hupper_tendsto

/--
%%handwave
name:
  Local mean-square Lebesgue differentiation from compact $L^2$ bounds
statement:
  Let $\Omega\subseteq\mathbb C$ be open and let $f:\Omega\to E$ take
  values in a real inner-product space. If $f\in L^2(K)$ for every compact
  $K\subseteq\Omega$, then for almost every $x\in\Omega$,
  $$
    \lim_{r\downarrow0}
      \fint_{\overline B(x,r)}\|f(y)-f(x)\|^2\,dy=0.
  $$
proof:
  Cover $\Omega$ by countably many relatively compact balls. On each ball,
  extend $f$ by zero; its global $L^2$ bound follows from the compact bound on
  the corresponding closed ball. Apply [global mean-square Lebesgue differentiation](lean:JJMath.Quasiconformal.ae_tendsto_average_norm_sq_sub_closedBall_of_memLp), then use openness to identify sufficiently small centered-ball averages with those of $f$.
-/
theorem ae_tendsto_average_norm_sq_sub_closedBall_of_memLpOn_compacts
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → E}
    (hf : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      MemLp f 2 (MeasureTheory.volume.restrict K)) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
      Tendsto
        (fun r : ℝ ↦
          ⨍ y in closedBall x r, ‖f y - f x‖ ^ 2
            ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hball : ∀ x : Ω, ∃ R : ℝ, 0 < R ∧ ball (x : ℂ) R ⊆ Ω := by
    intro x
    exact Metric.isOpen_iff.mp hΩ x x.2
  choose R hR_pos hR_ball using hball
  let r : Ω → ℝ := fun x ↦ R x / 2
  let V : Ω → Set ℂ := fun x ↦ ball (x : ℂ) (r x)
  have hr_pos : ∀ x : Ω, 0 < r x := fun x ↦ by
    dsimp [r]
    linarith [hR_pos x]
  have hV_open : ∀ x : Ω, IsOpen (V x) := fun _ ↦ isOpen_ball
  have hxV : ∀ x : Ω, (x : ℂ) ∈ V x := fun x ↦
    mem_ball_self (hr_pos x)
  have hclosedΩ : ∀ x : Ω, closedBall (x : ℂ) (r x) ⊆ Ω := by
    intro x y hy
    apply hR_ball x
    have hlt : r x < R x := by
      dsimp [r]
      linarith [hR_pos x]
    exact lt_of_le_of_lt hy hlt
  have hVΩ : ∀ x : Ω, V x ⊆ Ω := fun x ↦
    ball_subset_closedBall.trans (hclosedΩ x)
  have hmem : ∀ x : Ω,
      MemLp ((V x).indicator f) 2 MeasureTheory.volume := by
    intro x
    rw [memLp_indicator_iff_restrict (hV_open x).measurableSet]
    exact (hf (closedBall (x : ℂ) (r x))
      (isCompact_closedBall _ _) (hclosedΩ x)).mono_measure
        (Measure.restrict_mono ball_subset_closedBall le_rfl)
  obtain ⟨T, hT_count, hT_union⟩ :
      ∃ T : Set Ω, T.Countable ∧
        ⋃ x ∈ T, V x = ⋃ x : Ω, V x :=
    TopologicalSpace.isOpen_iUnion_countable V hV_open
  haveI : Countable T := hT_count.to_subtype
  have hΩ_eq : Ω = ⋃ x : T, V x.1 := by
    apply Subset.antisymm
    · intro y hy
      have hyall : y ∈ ⋃ x : Ω, V x :=
        mem_iUnion_of_mem ⟨y, hy⟩ (hxV ⟨y, hy⟩)
      rw [← hT_union] at hyall
      rcases Set.mem_iUnion₂.mp hyall with ⟨x, hxT, hyV⟩
      exact mem_iUnion_of_mem ⟨x, hxT⟩ hyV
    · intro y hy
      rcases Set.mem_iUnion.mp hy with ⟨x, hyV⟩
      exact hVΩ x.1 hyV
  have hpiece : ∀ x : T,
      ∀ᵐ y ∂MeasureTheory.volume.restrict (V x.1),
        Tendsto
          (fun s : ℝ ↦
            ⨍ z in closedBall y s, ‖f z - f y‖ ^ 2
              ∂MeasureTheory.volume)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro x
    let g : ℂ → E := (V x.1).indicator f
    have hV_meas : MeasurableSet (V x.1) := (hV_open x.1).measurableSet
    have hglobal :=
      ae_tendsto_average_norm_sq_sub_closedBall_of_memLp (hmem x.1)
    filter_upwards [ae_restrict_mem hV_meas, ae_restrict_of_ae hglobal]
      with y hyV hyglobal
    have hyraw :
        Tendsto
          (fun s : ℝ ↦
            ⨍ z in closedBall y s, ‖g z - g y‖ ^ 2
              ∂MeasureTheory.volume)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa [g] using hyglobal
    rcases Metric.isOpen_iff.mp (hV_open x.1) y hyV with
      ⟨ε, hε_pos, hε_ball⟩
    apply hyraw.congr'
    have heps : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s < ε :=
      Filter.Eventually.filter_mono inf_le_left
        ((tendsto_order.1 tendsto_id).2 ε hε_pos)
    filter_upwards [heps] with s hs
    apply setAverage_congr_fun measurableSet_closedBall
    filter_upwards with z hz
    have hzV : z ∈ V x.1 := hε_ball (lt_of_le_of_lt hz hs)
    simp [g, indicator_of_mem hzV, indicator_of_mem hyV]
  rw [hΩ_eq, ae_restrict_iUnion_iff]
  exact hpiece

/--
%%handwave
name:
  Scale-normalized local $L^2$ oscillation of a Hilbert-valued field
statement:
  Let $\Omega\subseteq\mathbb C$ be open and let $f:\Omega\to E$ take
  values in a real Hilbert space. If $f\in L^2(K)$ for every compact
  $K\subseteq\Omega$, then for almost every $x\in\Omega$,
  $$
    \frac{\|f-f(x)\|_{L^2(B(x,r))}}r\longrightarrow0
    \qquad(r\downarrow0).
  $$
proof:
  By [local mean-square Lebesgue differentiation](lean:JJMath.Quasiconformal.ae_tendsto_average_norm_sq_sub_closedBall_of_memLpOn_compacts), the mean of $\|f-f(x)\|^2$ tends to zero at almost every point. Open and closed planar balls agree up to a null set, and $|B(x,r)|=\pi r^2$ converts the square root of this mean into the scale-normalized $L^2$ norm.
-/
theorem ae_tendsto_eLpNorm_sub_div_radius_of_memLpOn_compacts
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → E}
    (hf : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      MemLp f 2 (MeasureTheory.volume.restrict K)) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
      Tendsto
        (fun r : ℝ ↦
          (eLpNorm (fun y : ℂ ↦ f y - f x) 2
            (MeasureTheory.volume.restrict (ball x r))).toReal / r)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards
    [ae_restrict_mem hΩ.measurableSet,
      ae_tendsto_average_norm_sq_sub_closedBall_of_memLpOn_compacts hΩ hf]
    with x hxΩ hxavg_closed
  have hxavg :
      Tendsto
        (fun r : ℝ ↦
          ⨍ y in ball x r, ‖f y - f x‖ ^ 2 ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply hxavg_closed.congr'
    filter_upwards with r
    exact setAverage_congr (complex_closedBall_ae_eq_ball x r)
  rcases Metric.isOpen_iff.mp hΩ x hxΩ with ⟨R, hR_pos, hR_ball⟩
  let K : Set ℂ := closedBall x (R / 2)
  have hhalf_pos : 0 < R / 2 := by linarith
  have hKΩ : K ⊆ Ω := by
    intro y hy
    apply hR_ball
    rw [mem_ball]
    change dist y x ≤ R / 2 at hy
    linarith
  have hfK : MemLp f 2 (MeasureTheory.volume.restrict K) :=
    hf K (isCompact_closedBall _ _) hKΩ
  have hscaled :
      Tendsto
        (fun r : ℝ ↦ Real.pi *
          (⨍ y in ball x r, ‖f y - f x‖ ^ 2
            ∂MeasureTheory.volume))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hxavg
  have hsqrt :
      Tendsto
        (fun r : ℝ ↦ Real.sqrt (Real.pi *
          (⨍ y in ball x r, ‖f y - f x‖ ^ 2
            ∂MeasureTheory.volume)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hscaled
  apply hsqrt.congr'
  have hr_small : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < R / 2 :=
    Filter.Eventually.filter_mono inf_le_left
      ((tendsto_order.1 tendsto_id).2 (R / 2) hhalf_pos)
  filter_upwards [self_mem_nhdsWithin, hr_small] with r hr_pos hr_small
  have hr0 : 0 < r := hr_pos
  have hballK : ball x r ⊆ K := by
    intro y hy
    exact le_trans (le_of_lt hy) (le_of_lt hr_small)
  have hf_r : MemLp f 2
      (MeasureTheory.volume.restrict (ball x r)) :=
    hfK.mono_measure (Measure.restrict_mono hballK le_rfl)
  haveI : IsFiniteMeasure
      (MeasureTheory.volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.2
      (ne_of_lt (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
        (isCompact_closedBall x r).measure_lt_top))
  have hdiff_r : MemLp (fun y : ℂ ↦ f y - f x) 2
      (MeasureTheory.volume.restrict (ball x r)) :=
    hf_r.sub (memLp_const (f x))
  have hsq :=
    eLpNorm_two_toReal_sq_eq_volume_real_mul_setAverage_norm_sq
      (u := fun y : ℂ ↦ f y - f x) x hr0 hdiff_r
  rw [complex_volume_real_ball x hr0.le] at hsq
  rw [← Real.sqrt_sq (div_nonneg ENNReal.toReal_nonneg hr0.le)]
  congr 1
  rw [div_pow, hsq]
  field_simp [ne_of_gt hr0]

/--
%%handwave
name:
  Scale-normalized $L^2$ oscillation of a planar Sobolev map
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$, then for almost every
  $x\in\Omega$,
  $$
    \frac{\|f-f(x)\|_{L^2(B(x,r))}}r\longrightarrow0
    \qquad(r\downarrow0).
  $$
proof:
  A locally Sobolev map belongs to $L^2$ on every compact subset of its domain, so this is [scale-normalized local $L^2$ differentiation](lean:JJMath.Quasiconformal.ae_tendsto_eLpNorm_sub_div_radius_of_memLpOn_compacts).
-/
theorem IsLocalW12On.ae_tendsto_eLpNorm_value_sub_div_radius
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
      Tendsto
        (fun r : ℝ ↦
          (eLpNorm (fun y : ℂ ↦ f y - f x) 2
            (MeasureTheory.volume.restrict (ball x r))).toReal / r)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  ae_tendsto_eLpNorm_sub_div_radius_of_memLpOn_compacts h.1
    (fun K hK hKΩ ↦ (h.2.2 K hK hKΩ).1)

/--
%%handwave
name:
  Scale-normalized affine reference error of a planar Sobolev map
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then for almost every $x\in\Omega$,
  $$
    \frac{\|f(y)-Df(x)(y-x)-f(x)\|_{L^2(B(x,r))}}r
      \longrightarrow0
    \qquad(r\downarrow0).
  $$
proof:
  The triangle inequality bounds this expression by [the scale-normalized $L^2$ oscillation of $f$](lean:JJMath.Quasiconformal.IsLocalW12On.ae_tendsto_eLpNorm_value_sub_div_radius) plus $\|Df(x)(y-x)\|_{L^2(B(x,r))}/r$. The latter is at most $\|Df(x)\|\sqrt\pi\,r$ by [the linear-map scale bound](lean:JJMath.Quasiconformal.eLpNorm_apply_sub_center_toReal_div_radius_le).
-/
theorem IsLocalW12On.ae_tendsto_eLpNorm_affine_reference_sub_div_radius
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
      Tendsto
        (fun r : ℝ ↦
          (eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - f x) 2
            (MeasureTheory.volume.restrict (ball x r))).toReal / r)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards
    [ae_restrict_mem h.1.measurableSet,
      h.ae_tendsto_eLpNorm_value_sub_div_radius]
    with x hxΩ hxvalue
  rcases Metric.isOpen_iff.mp h.1 x hxΩ with ⟨R, hR_pos, hR_ball⟩
  let K : Set ℂ := closedBall x (R / 2)
  have hhalf_pos : 0 < R / 2 := by linarith
  have hKΩ : K ⊆ Ω := by
    intro y hy
    apply hR_ball
    rw [mem_ball]
    change dist y x ≤ R / 2 at hy
    linarith
  have hfK : MemLp f 2 (MeasureTheory.volume.restrict K) :=
    (h.2.2 K (isCompact_closedBall _ _) hKΩ).1
  let upper : ℝ → ℝ := fun r ↦
    (eLpNorm (fun y : ℂ ↦ f y - f x) 2
      (MeasureTheory.volume.restrict (ball x r))).toReal / r +
      ‖df x‖ * Real.sqrt Real.pi * r
  have hr_zero : Tendsto (fun r : ℝ ↦ r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hupper : Tendsto upper (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    dsimp [upper]
    simpa using hxvalue.add (tendsto_const_nhds.mul hr_zero)
  have hr_small : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < R / 2 :=
    Filter.Eventually.filter_mono inf_le_left
      ((tendsto_order.1 tendsto_id).2 (R / 2) hhalf_pos)
  have hbounds : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ (eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - f x) 2
          (MeasureTheory.volume.restrict (ball x r))).toReal / r ∧
        (eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - f x) 2
          (MeasureTheory.volume.restrict (ball x r))).toReal / r ≤ upper r := by
    filter_upwards [self_mem_nhdsWithin, hr_small] with r hr hr_small
    have hr0 : 0 < r := hr
    let μr : Measure ℂ := MeasureTheory.volume.restrict (ball x r)
    have hballK : ball x r ⊆ K := by
      intro y hy
      exact le_trans (le_of_lt hy) (le_of_lt hr_small)
    have hf_r : MemLp f 2 μr :=
      hfK.mono_measure (Measure.restrict_mono hballK le_rfl)
    haveI : IsFiniteMeasure μr :=
      isFiniteMeasure_restrict.2
        (ne_of_lt (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
          (isCompact_closedBall x r).measure_lt_top))
    have hvalue_r : MemLp (fun y : ℂ ↦ f y - f x) 2 μr :=
      hf_r.sub (memLp_const (f x))
    have hlinear_r : MemLp (fun y : ℂ ↦ df x (y - x)) 2 μr := by
      apply MemLp.of_bound
        ((df x).continuous.comp
          (continuous_id.sub continuous_const)).aestronglyMeasurable
        (‖df x‖ * r)
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      calc
        ‖df x (y - x)‖ ≤ ‖df x‖ * ‖y - x‖ := (df x).le_opNorm (y - x)
        _ ≤ ‖df x‖ * r := by
          gcongr
          rw [mem_ball, dist_eq_norm] at hy
          exact le_of_lt hy
    have hfun :
        (fun y : ℂ ↦ f y - df x (y - x) - f x) =
          ((fun y : ℂ ↦ f y - f x) - fun y : ℂ ↦ df x (y - x)) := by
      funext y
      simp only [Pi.sub_apply]
      abel
    have hcorrect_r :
        MemLp (fun y : ℂ ↦ f y - df x (y - x) - f x) 2 μr := by
      have hsub := hvalue_r.sub hlinear_r
      rw [hfun]
      exact hsub
    have htri :
        eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - f x) 2 μr ≤
          eLpNorm (fun y : ℂ ↦ f y - f x) 2 μr +
            eLpNorm (fun y : ℂ ↦ df x (y - x)) 2 μr := by
      have hraw := eLpNorm_sub_le hvalue_r.aestronglyMeasurable
        hlinear_r.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      rw [hfun]
      exact hraw
    have hright_ne_top :
        eLpNorm (fun y : ℂ ↦ f y - f x) 2 μr +
            eLpNorm (fun y : ℂ ↦ df x (y - x)) 2 μr ≠ ∞ :=
      ENNReal.add_ne_top.mpr
        ⟨hvalue_r.eLpNorm_ne_top, hlinear_r.eLpNorm_ne_top⟩
    have hreal := (ENNReal.toReal_le_toReal hcorrect_r.eLpNorm_ne_top
      hright_ne_top).2 htri
    rw [ENNReal.toReal_add hvalue_r.eLpNorm_ne_top
      hlinear_r.eLpNorm_ne_top] at hreal
    have hlinear_bound :=
      eLpNorm_apply_sub_center_toReal_div_radius_le (df x) x hr0
    constructor
    · positivity
    · dsimp [upper]
      calc
        (eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - f x) 2 μr).toReal / r
            ≤ ((eLpNorm (fun y : ℂ ↦ f y - f x) 2 μr).toReal +
                (eLpNorm (fun y : ℂ ↦ df x (y - x)) 2 μr).toReal) / r :=
              div_le_div_of_nonneg_right hreal hr0.le
        _ = (eLpNorm (fun y : ℂ ↦ f y - f x) 2 μr).toReal / r +
              (eLpNorm (fun y : ℂ ↦ df x (y - x)) 2 μr).toReal / r := by
            ring
        _ ≤ (eLpNorm (fun y : ℂ ↦ f y - f x) 2 μr).toReal / r +
              ‖df x‖ * Real.sqrt Real.pi * r := by
            gcongr
  exact squeeze_zero' (hbounds.mono fun _ hr ↦ hr.1)
    (hbounds.mono fun _ hr ↦ hr.2) hupper

/--
%%handwave
name:
  Mean-square Lebesgue points of a planar weak differential
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then for almost every $x\in\Omega$,
  $$
    \lim_{r\downarrow0}
      \fint_{\overline B(x,r)}\|Df(y)-Df(x)\|^2\,dy=0.
  $$
proof:
  Represent each real-linear map by the Euclidean pair of its values on
  $1$ and $i$. This pair is locally square-integrable, so
  [local mean-square Lebesgue differentiation](lean:JJMath.Quasiconformal.ae_tendsto_average_norm_sq_sub_closedBall_of_memLpOn_compacts) applies. The [operator-norm square is at most twice the coordinate-pair norm square](lean:JJMath.Quasiconformal.norm_sq_le_two_mul_planarRealLinearCoordinatePairCLM_norm_sq), and a local compact $L^2$ bound justifies integrating this inequality on sufficiently small balls.
-/
theorem IsLocalW12On.ae_tendsto_average_differential_norm_sq_sub_closedBall
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
      Tendsto
        (fun r : ℝ ↦
          ⨍ y in closedBall x r, ‖df y - df x‖ ^ 2
            ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let T := planarRealLinearCoordinatePairCLM
  have hT_mem : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      MemLp (fun z ↦ T (df z)) 2
        (MeasureTheory.volume.restrict K) := by
    intro K hK hKΩ
    exact (h.2.2 K hK hKΩ).2.continuousLinearMap_comp T
  have hT_diff :=
    ae_tendsto_average_norm_sq_sub_closedBall_of_memLpOn_compacts
      h.1 hT_mem
  filter_upwards [ae_restrict_mem h.1.measurableSet, hT_diff]
    with x hxΩ hxT
  rcases Metric.isOpen_iff.mp h.1 x hxΩ with ⟨R, hR_pos, hR_ball⟩
  let K : Set ℂ := closedBall x (R / 2)
  have hhalf_pos : 0 < R / 2 := by linarith
  have hKΩ : K ⊆ Ω := by
    intro y hy
    apply hR_ball
    rw [mem_ball]
    change dist y x ≤ R / 2 at hy
    linarith
  have hdfK : MemLp df 2 (MeasureTheory.volume.restrict K) :=
    (h.2.2 K (isCompact_closedBall _ _) hKΩ).2
  have hupper :
      Tendsto
        (fun r : ℝ ↦
          2 * (⨍ y in closedBall x r,
            ‖T (df y) - T (df x)‖ ^ 2 ∂MeasureTheory.volume))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hxT
  have hr_small : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < R / 2 :=
    Filter.Eventually.filter_mono inf_le_left
      ((tendsto_order.1 tendsto_id).2 (R / 2) hhalf_pos)
  have hbounds : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ ⨍ y in closedBall x r, ‖df y - df x‖ ^ 2
          ∂MeasureTheory.volume ∧
      (⨍ y in closedBall x r, ‖df y - df x‖ ^ 2
          ∂MeasureTheory.volume) ≤
        2 * (⨍ y in closedBall x r,
          ‖T (df y) - T (df x)‖ ^ 2 ∂MeasureTheory.volume) := by
    filter_upwards [hr_small] with r hr
    let μr : Measure ℂ :=
      MeasureTheory.volume.restrict (closedBall x r)
    haveI : IsFiniteMeasure μr :=
      isFiniteMeasure_restrict.2 (isCompact_closedBall x r).measure_ne_top
    have hballK : closedBall x r ⊆ K := by
      intro y hy
      exact le_trans hy (le_of_lt hr)
    have hdf_r : MemLp df 2 μr :=
      hdfK.mono_measure (Measure.restrict_mono hballK le_rfl)
    have hdiff_r : MemLp (fun y ↦ df y - df x) 2 μr :=
      hdf_r.sub (memLp_const (df x))
    have hTdiff_r : MemLp (fun y ↦ T (df y - df x)) 2 μr :=
      hdiff_r.continuousLinearMap_comp T
    have hleft_int : Integrable (fun y ↦ ‖df y - df x‖ ^ 2) μr :=
      hdiff_r.integrable_norm_pow (by norm_num)
    have hright_int : Integrable
        (fun y ↦ 2 * ‖T (df y) - T (df x)‖ ^ 2) μr := by
      have hcoord_int : Integrable
          (fun y ↦ ‖T (df y - df x)‖ ^ 2) μr :=
        hTdiff_r.integrable_norm_pow (by norm_num)
      simpa only [map_sub] using hcoord_int.const_mul 2
    have hpoint : ∀ y : ℂ,
        ‖df y - df x‖ ^ 2 ≤
          2 * ‖T (df y) - T (df x)‖ ^ 2 := by
      intro y
      simpa only [map_sub] using
        norm_sq_le_two_mul_planarRealLinearCoordinatePairCLM_norm_sq
          (df y - df x)
    have hint_le :
        ∫ y, ‖df y - df x‖ ^ 2 ∂μr ≤
          ∫ y, 2 * ‖T (df y) - T (df x)‖ ^ 2 ∂μr :=
      integral_mono hleft_int hright_int hpoint
    constructor
    · simp only [setAverage_eq, smul_eq_mul]
      positivity
    · simp only [average_eq, smul_eq_mul]
      change (μr.real univ)⁻¹ * ∫ y, ‖df y - df x‖ ^ 2 ∂μr ≤
        2 * ((μr.real univ)⁻¹ *
          ∫ y, ‖T (df y) - T (df x)‖ ^ 2 ∂μr)
      rw [integral_const_mul] at hint_le
      calc
        (μr.real univ)⁻¹ * ∫ y, ‖df y - df x‖ ^ 2 ∂μr
            ≤ (μr.real univ)⁻¹ *
                (2 * ∫ y, ‖T (df y) - T (df x)‖ ^ 2 ∂μr) :=
              mul_le_mul_of_nonneg_left hint_le (by positivity)
        _ = 2 * ((μr.real univ)⁻¹ *
              ∫ y, ‖T (df y) - T (df x)‖ ^ 2 ∂μr) := by ring
  exact squeeze_zero' (hbounds.mono fun _ hr ↦ hr.1)
    (hbounds.mono fun _ hr ↦ hr.2) hupper

/--
%%handwave
name:
  Mean-square weak-differential oscillation on open balls
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then for almost every $x\in\Omega$,
  $$
    \lim_{r\downarrow0}
      \fint_{B(x,r)}\|Df(y)-Df(x)\|^2\,dy=0.
  $$
proof:
  Apply [mean-square differentiation on closed balls](lean:JJMath.Quasiconformal.IsLocalW12On.ae_tendsto_average_differential_norm_sq_sub_closedBall). Open and closed planar balls differ by a null sphere, so their averages agree at every radius.
-/
theorem IsLocalW12On.ae_tendsto_average_differential_norm_sq_sub_ball
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
      Tendsto
        (fun r : ℝ ↦
          ⨍ y in ball x r, ‖df y - df x‖ ^ 2
            ∂MeasureTheory.volume)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards
    [h.ae_tendsto_average_differential_norm_sq_sub_closedBall]
    with x hx
  apply hx.congr'
  filter_upwards with r
  exact setAverage_congr (complex_closedBall_ae_eq_ball x r)

/--
%%handwave
name:
  Scale-normalized $L^2$ oscillation of the weak differential
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then for almost every $x\in\Omega$,
  $$
    \frac{\|Df-Df(x)\|_{L^2(B(x,r))}}{r}\longrightarrow0
    \qquad(r\downarrow0).
  $$
proof:
  The squared $L^2$ norm is ball volume times the mean-square oscillation.
  Since $|B(x,r)|=\pi r^2$, division by $r$ identifies the normalized norm
  with the square root of $\pi$ times [the vanishing mean-square
  oscillation](lean:JJMath.Quasiconformal.IsLocalW12On.ae_tendsto_average_differential_norm_sq_sub_ball).
-/
theorem IsLocalW12On.ae_tendsto_eLpNorm_differential_sub_div_radius
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
      Tendsto
        (fun r : ℝ ↦
          (eLpNorm (fun y : ℂ ↦ df y - df x) 2
            (MeasureTheory.volume.restrict (ball x r))).toReal / r)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards
    [ae_restrict_mem h.1.measurableSet,
      h.ae_tendsto_average_differential_norm_sq_sub_ball]
    with x hxΩ hxavg
  rcases Metric.isOpen_iff.mp h.1 x hxΩ with ⟨R, hR_pos, hR_ball⟩
  let K : Set ℂ := closedBall x (R / 2)
  have hhalf_pos : 0 < R / 2 := by linarith
  have hKΩ : K ⊆ Ω := by
    intro y hy
    apply hR_ball
    rw [mem_ball]
    change dist y x ≤ R / 2 at hy
    linarith
  have hdfK : MemLp df 2 (MeasureTheory.volume.restrict K) :=
    (h.2.2 K (isCompact_closedBall _ _) hKΩ).2
  have hscaled :
      Tendsto
        (fun r : ℝ ↦ Real.pi *
          (⨍ y in ball x r, ‖df y - df x‖ ^ 2
            ∂MeasureTheory.volume))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hxavg
  have hsqrt :
      Tendsto
        (fun r : ℝ ↦ Real.sqrt (Real.pi *
          (⨍ y in ball x r, ‖df y - df x‖ ^ 2
            ∂MeasureTheory.volume)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hscaled
  apply hsqrt.congr'
  have hr_small : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < R / 2 :=
    Filter.Eventually.filter_mono inf_le_left
      ((tendsto_order.1 tendsto_id).2 (R / 2) hhalf_pos)
  filter_upwards [self_mem_nhdsWithin, hr_small] with r hr_pos hr_small
  have hr0 : 0 < r := hr_pos
  have hballK : ball x r ⊆ K := by
    intro y hy
    exact le_trans (le_of_lt hy) (le_of_lt hr_small)
  have hdf_r : MemLp df 2
      (MeasureTheory.volume.restrict (ball x r)) :=
    hdfK.mono_measure (Measure.restrict_mono hballK le_rfl)
  haveI : IsFiniteMeasure
      (MeasureTheory.volume.restrict (ball x r)) :=
    isFiniteMeasure_restrict.2
      (ne_of_lt (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
        (isCompact_closedBall x r).measure_lt_top))
  have hdiff_r : MemLp (fun y : ℂ ↦ df y - df x) 2
      (MeasureTheory.volume.restrict (ball x r)) :=
    hdf_r.sub (memLp_const (df x))
  have hsq :=
    eLpNorm_two_toReal_sq_eq_volume_real_mul_setAverage_norm_sq
      (u := fun y : ℂ ↦ df y - df x) x hr0 hdiff_r
  rw [complex_volume_real_ball x hr0.le] at hsq
  rw [← Real.sqrt_sq (div_nonneg ENNReal.toReal_nonneg hr0.le)]
  congr 1
  rw [div_pow, hsq]
  field_simp [ne_of_gt hr0]

/--
%%handwave
name:
  Vanishing scale-normalized affine remainder modulo constants
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then for almost every $x\in\Omega$ there are constants
  $a_r\in\mathbb C$ such that the affine remainders belong to
  $L^2(B(x,r))$ for all sufficiently small $r>0$ and
  $$
    \frac{\|f(y)-Df(x)(y-x)-a_r\|_{L^2(B(x,r))}}{r^2}
      \longrightarrow0.
  $$
proof:
  Apply the [uniform affine-remainder Poincare estimate](lean:JJMath.Quasiconformal.localW12_affine_remainder_poincare_L2) at each sufficiently small radius and choose one admissible constant $a_r$. After division by $r^2$, its upper bound is a fixed finite constant times [the scale-normalized $L^2$ oscillation of $Df$](lean:JJMath.Quasiconformal.IsLocalW12On.ae_tendsto_eLpNorm_differential_sub_div_radius), which tends to zero.
-/
theorem IsLocalW12On.ae_exists_affine_remainder_center_eLpNorm_div_sq_tendsto_zero
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
      ∃ a : ℝ → ℂ,
        (∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
          MemLp (fun y : ℂ ↦ f y - df x (y - x) - a r) 2
            (MeasureTheory.volume.restrict (ball x r))) ∧
        Tendsto
          (fun r : ℝ ↦
            (eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - a r) 2
              (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  rcases localW12_affine_remainder_poincare_L2 with ⟨C, hC_top, hP⟩
  filter_upwards
    [ae_restrict_mem h.1.measurableSet,
      h.ae_tendsto_eLpNorm_differential_sub_div_radius]
    with x hxΩ hdx
  rcases Metric.isOpen_iff.mp h.1 x hxΩ with ⟨R, hR_pos, hR_ball⟩
  let K : Set ℂ := closedBall x (R / 2)
  have hhalf_pos : 0 < R / 2 := by linarith
  have hKΩ : K ⊆ Ω := by
    intro y hy
    apply hR_ball
    rw [mem_ball]
    change dist y x ≤ R / 2 at hy
    linarith
  have hdfK : MemLp df 2 (MeasureTheory.volume.restrict K) :=
    (h.2.2 K (isCompact_closedBall _ _) hKΩ).2
  let Good : ℝ → Prop := fun r ↦ 0 < r ∧ closedBall x r ⊆ Ω
  let a : ℝ → ℂ := fun r ↦
    if hr : Good r then Classical.choose (hP h hr.1 hr.2) else 0
  have ha (r : ℝ) (hr : Good r) :
      AEStronglyMeasurable
          (fun y : ℂ ↦ f y - df x (y - x) - a r)
          (MeasureTheory.volume.restrict (ball x r)) ∧
        eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - a r) 2
            (MeasureTheory.volume.restrict (ball x r)) ≤
          C * ENNReal.ofReal r *
            eLpNorm (fun y : ℂ ↦ df y - df x) 2
              (MeasureTheory.volume.restrict (ball x r)) := by
    dsimp [a]
    rw [dif_pos hr]
    exact Classical.choose_spec (hP h hr.1 hr.2)
  have hr_small : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < R / 2 :=
    Filter.Eventually.filter_mono inf_le_left
      ((tendsto_order.1 tendsto_id).2 (R / 2) hhalf_pos)
  have hbounds : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      MemLp (fun y : ℂ ↦ f y - df x (y - x) - a r) 2
          (MeasureTheory.volume.restrict (ball x r)) ∧
        0 ≤ (eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - a r) 2
            (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2 ∧
        (eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - a r) 2
            (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2 ≤
          C.toReal *
            ((eLpNorm (fun y : ℂ ↦ df y - df x) 2
              (MeasureTheory.volume.restrict (ball x r))).toReal / r) := by
    filter_upwards [self_mem_nhdsWithin, hr_small] with r hr_pos hr_small
    have hr0 : 0 < r := hr_pos
    have hclosedΩ : closedBall x r ⊆ Ω := by
      intro y hy
      exact hKΩ (le_trans hy (le_of_lt hr_small))
    have hgood : Good r := ⟨hr0, hclosedΩ⟩
    have hballK : ball x r ⊆ K := by
      intro y hy
      exact le_trans (le_of_lt hy) (le_of_lt hr_small)
    have hdf_r : MemLp df 2
        (MeasureTheory.volume.restrict (ball x r)) :=
      hdfK.mono_measure (Measure.restrict_mono hballK le_rfl)
    haveI : IsFiniteMeasure
        (MeasureTheory.volume.restrict (ball x r)) :=
      isFiniteMeasure_restrict.2
        (ne_of_lt (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
          (isCompact_closedBall x r).measure_lt_top))
    have hdiff_r : MemLp (fun y : ℂ ↦ df y - df x) 2
        (MeasureTheory.volume.restrict (ball x r)) :=
      hdf_r.sub (memLp_const (df x))
    have hbound := (ha r hgood).2
    have hright_ne_top :
        C * ENNReal.ofReal r *
            eLpNorm (fun y : ℂ ↦ df y - df x) 2
              (MeasureTheory.volume.restrict (ball x r)) ≠ ⊤ :=
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (ne_of_lt hC_top) ENNReal.ofReal_ne_top)
        hdiff_r.eLpNorm_ne_top
    have hleft_ne_top :
        eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - a r) 2
            (MeasureTheory.volume.restrict (ball x r)) ≠ ⊤ :=
      ne_top_of_le_ne_top hright_ne_top hbound
    have hmem : MemLp (fun y : ℂ ↦ f y - df x (y - x) - a r) 2
        (MeasureTheory.volume.restrict (ball x r)) :=
      ⟨(ha r hgood).1, lt_top_iff_ne_top.mpr hleft_ne_top⟩
    have hreal :=
      (ENNReal.toReal_le_toReal hleft_ne_top hright_ne_top).2 hbound
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hr0.le] at hreal
    refine ⟨hmem, by positivity, ?_⟩
    apply (div_le_iff₀ (sq_pos_of_pos hr0)).2
    calc
      (eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - a r) 2
          (MeasureTheory.volume.restrict (ball x r))).toReal
          ≤ C.toReal * r *
              (eLpNorm (fun y : ℂ ↦ df y - df x) 2
                (MeasureTheory.volume.restrict (ball x r))).toReal := hreal
      _ = (C.toReal *
            ((eLpNorm (fun y : ℂ ↦ df y - df x) 2
              (MeasureTheory.volume.restrict (ball x r))).toReal / r)) * r ^ 2 := by
          field_simp [ne_of_gt hr0]
  refine ⟨a, hbounds.mono fun _ hr ↦ hr.1, ?_⟩
  have hupper :
      Tendsto
        (fun r : ℝ ↦ C.toReal *
          ((eLpNorm (fun y : ℂ ↦ df y - df x) 2
            (MeasureTheory.volume.restrict (ball x r))).toReal / r))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hdx
  exact squeeze_zero' (hbounds.mono fun _ hr ↦ hr.2.1)
    (hbounds.mono fun _ hr ↦ hr.2.2) hupper

/--
%%handwave
name:
  Poincare centers converge to the Sobolev value with half-scale control
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then for almost every $x\in\Omega$ there are constants
  $a_r\in\mathbb C$ such that $f-Df(x)(\cdot-x)-a_r$ belongs to
  $L^2(B(x,r))$ for all sufficiently small $r>0$,
  $$
    \frac{\|f-Df(x)(\cdot-x)-a_r\|_{L^2(B(x,r))}}{r^2}\to0,
    \qquad a_r\to f(x),
  $$
  and
  $$
    \frac{\|a_r-a_{r/2}\|}{r}\to0.
  $$
proof:
  Choose the centers using [the affine-remainder Poincare estimate](lean:JJMath.Quasiconformal.IsLocalW12On.ae_exists_affine_remainder_center_eLpNorm_div_sq_tendsto_zero). Compare them with $f(x)$ using [the scale-normalized affine reference error](lean:JJMath.Quasiconformal.IsLocalW12On.ae_tendsto_eLpNorm_affine_reference_sub_div_radius) and [identification from a reference value](lean:JJMath.Quasiconformal.tendsto_center_of_eLpNorm_div_sq_and_reference_div_radius). The half-scale conclusion is [the nested-ball center estimate](lean:JJMath.Quasiconformal.tendsto_norm_sub_center_half_div_radius).
-/
theorem IsLocalW12On.ae_exists_affine_remainder_center_with_convergence
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
      ∃ a : ℝ → ℂ,
        (∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
          MemLp (fun y : ℂ ↦ f y - df x (y - x) - a r) 2
            (MeasureTheory.volume.restrict (ball x r))) ∧
        Tendsto
          (fun r : ℝ ↦
            (eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - a r) 2
              (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2)
          (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
        Tendsto (fun r : ℝ ↦ ‖a r - f x‖)
          (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
        Tendsto (fun r : ℝ ↦ ‖a r - a (r / 2)‖ / r)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards
    [h.ae_exists_affine_remainder_center_eLpNorm_div_sq_tendsto_zero,
      h.ae_tendsto_eLpNorm_affine_reference_sub_div_radius]
    with x hxcenters hxreference
  rcases hxcenters with ⟨a, hmem_a, hqa⟩
  have hmem_ref : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      MemLp (fun y : ℂ ↦ f y - df x (y - x) - f x) 2
        (MeasureTheory.volume.restrict (ball x r)) := by
    filter_upwards [hmem_a] with r hmem_a_r
    let μr : Measure ℂ := MeasureTheory.volume.restrict (ball x r)
    haveI : IsFiniteMeasure μr :=
      isFiniteMeasure_restrict.2
        (ne_of_lt (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
          (isCompact_closedBall x r).measure_lt_top))
    have hconst : MemLp (fun _ : ℂ ↦ a r - f x) 2 μr :=
      memLp_const (a r - f x)
    have hadd := hmem_a_r.add hconst
    convert hadd using 1
    funext y
    simp only [Pi.add_apply]
    abel
  have hcenter : Tendsto (fun r : ℝ ↦ ‖a r - f x‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_center_of_eLpNorm_div_sq_and_reference_div_radius
      hmem_a hqa hmem_ref hxreference
  have hhalf : Tendsto (fun r : ℝ ↦ ‖a r - a (r / 2)‖ / r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_norm_sub_center_half_div_radius hmem_a hqa
  exact ⟨a, hmem_a, hqa, hcenter, hhalf⟩

/--
%%handwave
name:
  Vanishing fixed-center affine remainder in $L^2$
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then for almost every $x\in\Omega$,
  $$
    \frac{\|f(y)-f(x)-Df(x)(y-x)\|_{L^2(B(x,r))}}{r^2}
      \longrightarrow0
    \qquad(r\downarrow0).
  $$
proof:
  Choose moving Poincare centers with [ordinary convergence and half-scale control](lean:JJMath.Quasiconformal.IsLocalW12On.ae_exists_affine_remainder_center_with_convergence). The [dyadic center lemma](lean:JJMath.Quasiconformal.tendsto_norm_sub_center_div_radius_of_half) upgrades these properties to $\|a_r-f(x)\|/r\to0$. The triangle inequality replaces $a_r$ by $f(x)$; [the $L^2$ norm of the constant difference on $B(x,r)$](lean:JJMath.Quasiconformal.eLpNorm_const_two_ball_toReal) contributes exactly $\sqrt\pi\,\|a_r-f(x)\|/r$ after division by $r^2$.
-/
theorem IsLocalW12On.ae_tendsto_eLpNorm_affine_remainder_div_sq
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
      Tendsto
        (fun r : ℝ ↦
          (eLpNorm (fun y : ℂ ↦ f y - f x - df x (y - x)) 2
            (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [h.ae_exists_affine_remainder_center_with_convergence]
    with x hx
  rcases hx with ⟨a, hmem, hq, hcenter, hhalf⟩
  have hfirst : Tendsto (fun r : ℝ ↦ ‖a r - f x‖ / r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_norm_sub_center_div_radius_of_half hcenter hhalf
  let upper : ℝ → ℝ := fun r ↦
    (eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - a r) 2
      (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2 +
      Real.sqrt Real.pi * (‖a r - f x‖ / r)
  have hupper : Tendsto upper (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    dsimp [upper]
    simpa using hq.add (tendsto_const_nhds.mul hfirst)
  have hbounds : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ (eLpNorm (fun y : ℂ ↦ f y - f x - df x (y - x)) 2
          (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2 ∧
        (eLpNorm (fun y : ℂ ↦ f y - f x - df x (y - x)) 2
          (MeasureTheory.volume.restrict (ball x r))).toReal / r ^ 2 ≤ upper r := by
    filter_upwards [self_mem_nhdsWithin, hmem] with r hr hmem_r
    have hr0 : 0 < r := hr
    let μr : Measure ℂ := MeasureTheory.volume.restrict (ball x r)
    haveI : IsFiniteMeasure μr :=
      isFiniteMeasure_restrict.2
        (ne_of_lt (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
          (isCompact_closedBall x r).measure_lt_top))
    have hconst : MemLp (fun _ : ℂ ↦ a r - f x) 2 μr :=
      memLp_const (a r - f x)
    have hfun :
        (fun y : ℂ ↦ f y - f x - df x (y - x)) =
          ((fun y : ℂ ↦ f y - df x (y - x) - a r) +
            fun _ : ℂ ↦ a r - f x) := by
      funext y
      simp only [Pi.add_apply]
      abel
    have hfixed :
        MemLp (fun y : ℂ ↦ f y - f x - df x (y - x)) 2 μr := by
      rw [hfun]
      exact hmem_r.add hconst
    have htri :
        eLpNorm (fun y : ℂ ↦ f y - f x - df x (y - x)) 2 μr ≤
          eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - a r) 2 μr +
            eLpNorm (fun _ : ℂ ↦ a r - f x) 2 μr := by
      have hraw := eLpNorm_add_le hmem_r.aestronglyMeasurable
        hconst.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      rw [hfun]
      exact hraw
    have hright_ne_top :
        eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - a r) 2 μr +
            eLpNorm (fun _ : ℂ ↦ a r - f x) 2 μr ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨hmem_r.eLpNorm_ne_top, hconst.eLpNorm_ne_top⟩
    have hreal := (ENNReal.toReal_le_toReal hfixed.eLpNorm_ne_top
      hright_ne_top).2 htri
    rw [ENNReal.toReal_add hmem_r.eLpNorm_ne_top hconst.eLpNorm_ne_top,
      eLpNorm_const_two_ball_toReal (a r - f x) x hr0] at hreal
    constructor
    · positivity
    · dsimp [upper]
      calc
        (eLpNorm (fun y : ℂ ↦ f y - f x - df x (y - x)) 2 μr).toReal / r ^ 2 ≤
            ((eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - a r) 2 μr).toReal +
              ‖a r - f x‖ * (r * Real.sqrt Real.pi)) / r ^ 2 :=
          div_le_div_of_nonneg_right hreal (sq_nonneg r)
        _ = (eLpNorm (fun y : ℂ ↦ f y - df x (y - x) - a r) 2 μr).toReal / r ^ 2 +
              Real.sqrt Real.pi * (‖a r - f x‖ / r) := by
          field_simp [ne_of_gt hr0]
  exact squeeze_zero' (hbounds.mono fun _ hr ↦ hr.1)
    (hbounds.mono fun _ hr ↦ hr.2) hupper

/--
%%handwave
name:
  Approximate differentiability of planar local $W^{1,2}$ maps
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then $f$ is approximately differentiable at almost every
  $x\in\Omega$, with approximate differential $Df(x)$.
proof:
  At almost every point, [the fixed-center affine remainder has $L^2$ norm $o(r^2)$](lean:JJMath.Quasiconformal.IsLocalW12On.ae_tendsto_eLpNorm_affine_remainder_div_sq). Local $W^{1,2}$ bounds ensure that this remainder belongs to $L^2$ on every sufficiently small ball. Apply [the annular Chebyshev criterion for approximate differentiability](lean:JJMath.Quasiconformal.hasApproxFDerivAt_of_tendsto_eLpNorm_affine_remainder_div_sq).
tags:
  milestone
-/
theorem IsLocalW12On.ae_hasApproxFDerivAt
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
      HasApproxFDerivAt f (df x) x := by
  filter_upwards
    [ae_restrict_mem h.1.measurableSet,
      h.ae_tendsto_eLpNorm_affine_remainder_div_sq]
    with x hxΩ hxremainder
  rcases Metric.isOpen_iff.mp h.1 x hxΩ with ⟨R, hR_pos, hR_ball⟩
  let K : Set ℂ := closedBall x (R / 2)
  have hhalf_pos : 0 < R / 2 := by linarith
  have hKΩ : K ⊆ Ω := by
    intro y hy
    apply hR_ball
    rw [mem_ball]
    change dist y x ≤ R / 2 at hy
    linarith
  have hfK : MemLp f 2 (MeasureTheory.volume.restrict K) :=
    (h.2.2 K (isCompact_closedBall _ _) hKΩ).1
  have hr_small : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < R / 2 :=
    Filter.Eventually.filter_mono inf_le_left
      ((tendsto_order.1 tendsto_id).2 (R / 2) hhalf_pos)
  have hmem : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      MemLp (fun y : ℂ ↦ f y - f x - df x (y - x)) 2
        (MeasureTheory.volume.restrict (ball x r)) := by
    filter_upwards [self_mem_nhdsWithin, hr_small] with r hr hr_small
    have hr0 : 0 < r := hr
    let μr : Measure ℂ := MeasureTheory.volume.restrict (ball x r)
    have hballK : ball x r ⊆ K := by
      intro y hy
      exact le_trans (le_of_lt hy) (le_of_lt hr_small)
    have hf_r : MemLp f 2 μr :=
      hfK.mono_measure (Measure.restrict_mono hballK le_rfl)
    haveI : IsFiniteMeasure μr :=
      isFiniteMeasure_restrict.2
        (ne_of_lt (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
          (isCompact_closedBall x r).measure_lt_top))
    have hvalue_r : MemLp (fun y : ℂ ↦ f y - f x) 2 μr :=
      hf_r.sub (memLp_const (f x))
    have hlinear_r : MemLp (fun y : ℂ ↦ df x (y - x)) 2 μr := by
      apply MemLp.of_bound
        ((df x).continuous.comp
          (continuous_id.sub continuous_const)).aestronglyMeasurable
        (‖df x‖ * r)
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      calc
        ‖df x (y - x)‖ ≤ ‖df x‖ * ‖y - x‖ := (df x).le_opNorm (y - x)
        _ ≤ ‖df x‖ * r := by
          gcongr
          rw [mem_ball, dist_eq_norm] at hy
          exact le_of_lt hy
    simpa only [Pi.sub_apply] using hvalue_r.sub hlinear_r
  exact hasApproxFDerivAt_of_tendsto_eLpNorm_affine_remainder_div_sq
    hmem hxremainder

/--
%%handwave
name:
  Measurable full-measure core of an almost-everywhere property
statement:
  Let $S$ be measurable and suppose a property $P(x)$ holds for almost every
  $x\in S$. Then there is a measurable set $E\subseteq S$ that covers almost
  every point of $S$ and on which $P(x)$ holds at every point.
proof:
  Intersect the almost-everywhere property with almost-everywhere membership
  in $S$. The almost-everywhere filter is generated by measurable sets, so the
  resulting event contains a measurable event of full measure.
-/
theorem exists_measurable_ae_subset_of_ae
    {S : Set ℂ} (hS : MeasurableSet S) {P : ℂ → Prop}
    (hP : ∀ᵐ x ∂MeasureTheory.volume.restrict S, P x) :
    ∃ E : Set ℂ,
      MeasurableSet E ∧ E ⊆ S ∧
        (∀ᵐ x ∂MeasureTheory.volume.restrict S, x ∈ E) ∧
          ∀ x, x ∈ E → P x := by
  rcases ((ae_restrict_mem hS).and hP).exists_measurable_mem with
    ⟨E, hEae, hEmeas, hE⟩
  exact ⟨E, hEmeas, fun x hx ↦ (hE x hx).1, hEae,
    fun x hx ↦ (hE x hx).2⟩

/--
%%handwave
name:
  Measurable representative core for the Lusin--Whitney construction
statement:
  Let $S\subseteq\mathbb C$ be measurable. Suppose $f$ and $A$ are strongly
  measurable up to null sets on $S$, and $A(x)$ is the approximate
  differential of $f$ at almost every $x\in S$. Then there are globally
  strongly measurable representatives $f_0,A_0$ and a measurable
  full-measure set $E\subseteq S$ such that, at every $x\in E$,
  $$
    f_0(x)=f(x),\qquad A_0(x)=A(x),
  $$
  and $A(x)$ is the approximate differential of $f$ at $x$.
proof:
  Take the canonical strongly measurable representatives and intersect their
  two almost-everywhere equality events with the approximate-differential
  event. Extract a measurable full-measure subset on which all three facts
  hold pointwise.
-/
theorem exists_lusinWhitney_measurable_core
    {S : Set ℂ} {f : ℂ → ℂ} {A : ℂ → ℂ →L[ℝ] ℂ}
    (hS : MeasurableSet S)
    (hf : AEStronglyMeasurable f (MeasureTheory.volume.restrict S))
    (hA : AEStronglyMeasurable A (MeasureTheory.volume.restrict S))
    (happrox : ∀ᵐ x ∂MeasureTheory.volume.restrict S,
      HasApproxFDerivAt f (A x) x) :
    ∃ f₀ : ℂ → ℂ, ∃ A₀ : ℂ → ℂ →L[ℝ] ℂ, ∃ E : Set ℂ,
      StronglyMeasurable f₀ ∧ StronglyMeasurable A₀ ∧
        MeasurableSet E ∧ E ⊆ S ∧
          (∀ᵐ x ∂MeasureTheory.volume.restrict S, x ∈ E) ∧
            ∀ x, x ∈ E →
              f₀ x = f x ∧ A₀ x = A x ∧ HasApproxFDerivAt f (A x) x := by
  let f₀ : ℂ → ℂ := hf.mk f
  let A₀ : ℂ → ℂ →L[ℝ] ℂ := hA.mk A
  have hgood : ∀ᵐ x ∂MeasureTheory.volume.restrict S,
      f₀ x = f x ∧ A₀ x = A x ∧ HasApproxFDerivAt f (A x) x := by
    filter_upwards [hf.ae_eq_mk, hA.ae_eq_mk, happrox] with x hfx hAx hx
    exact ⟨hfx.symm, hAx.symm, hx⟩
  rcases exists_measurable_ae_subset_of_ae hS hgood with
    ⟨E, hEmeas, hES, hEae, hE⟩
  exact ⟨f₀, A₀, E, hf.stronglyMeasurable_mk, hA.stronglyMeasurable_mk,
    hEmeas, hES, hEae, hE⟩

/--
%%handwave
name:
  Lusin continuity on a large measurable subset
statement:
  Let $S\subseteq\mathbb C$ be measurable with finite area. Let
  $g:\mathbb C\to V$ be strongly measurable, where $V$ is a normed space,
  and suppose $g\in L^1(S)$. For every $\varepsilon>0$, there is a
  measurable $U\subseteq S$ such that
  $$
    |S\setminus U|\leq\varepsilon
  $$
  and $g|_U$ is continuous.
proof:
  Approximate $g$ in $L^1(S)$ by bounded continuous functions. Convergence in
  $L^1$ gives convergence in measure, so a subsequence converges almost
  everywhere. Egorov's theorem makes this subsequence uniformly convergent
  outside a measurable set of area at most $\varepsilon$. Its limit is
  continuous on the remaining subset.
-/
theorem exists_lusin_continuousOn_subset
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [SecondCountableTopology V]
    {S : Set ℂ} (hS : MeasurableSet S)
    (hSfinite : MeasureTheory.volume S ≠ ∞) {g : ℂ → V}
    (hg : StronglyMeasurable g)
    (hgmem : MemLp g 1 (MeasureTheory.volume.restrict S))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set ℂ,
      MeasurableSet U ∧ U ⊆ S ∧
        MeasureTheory.volume (S \ U) ≤ ENNReal.ofReal ε ∧
          ContinuousOn g U := by
  let μ : Measure ℂ := MeasureTheory.volume.restrict S
  haveI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.2 hSfinite
  have happrox (n : ℕ) :
      ∃ q : ℂ →ᵇ V,
        eLpNorm (g - (q : ℂ → V)) 1 μ ≤ (2 : ℝ≥0∞)⁻¹ ^ n ∧
          MemLp q 1 μ :=
    hgmem.exists_boundedContinuous_eLpNorm_sub_le ENNReal.one_ne_top
      (pow_ne_zero n (by simp))
  choose q hq hqmem using happrox
  have hdyadic : Tendsto (fun n : ℕ ↦ (2 : ℝ≥0∞)⁻¹ ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hnorm_gq : Tendsto
      (fun n : ℕ ↦ eLpNorm (g - (q n : ℂ → V)) 1 μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdyadic
      (fun _ ↦ bot_le) hq
  have hnorm_qg : Tendsto
      (fun n : ℕ ↦ eLpNorm ((q n : ℂ → V) - g) 1 μ) atTop (𝓝 0) := by
    rw [show (fun n : ℕ ↦ eLpNorm ((q n : ℂ → V) - g) 1 μ) =
        fun n : ℕ ↦ eLpNorm (g - (q n : ℂ → V)) 1 μ by
      funext n
      exact eLpNorm_sub_comm _ _ _ _]
    exact hnorm_gq
  have hmeasure : TendstoInMeasure μ (fun n ↦ (q n : ℂ → V)) atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)
      (fun n ↦ (q n).continuous.stronglyMeasurable.aestronglyMeasurable)
      hg.aestronglyMeasurable hnorm_qg
  rcases hmeasure.exists_seq_tendsto_ae with ⟨ns, _hns, hns⟩
  rcases tendstoUniformlyOn_of_ae_tendsto'
      (fun n ↦ (q (ns n)).continuous.stronglyMeasurable) hg hns hε with
    ⟨T, hTmeas, hμT, huniform⟩
  refine ⟨S \ T, hS.diff hTmeas, diff_subset, ?_, ?_⟩
  · have hset : S \ (S \ T) = T ∩ S := by
      ext x
      simp only [mem_diff, mem_inter_iff]
      tauto
    rw [hset]
    simpa only [μ, Measure.restrict_apply hTmeas] using hμT
  · apply (huniform.continuousOn
      (Frequently.of_forall fun n ↦ (q (ns n)).continuous.continuousOn)).mono
    exact diff_subset_compl S T

/--
%%handwave
name:
  Countable Lusin continuity decomposition
statement:
  If $S\subseteq\mathbb C$ is measurable and $g:\mathbb C\to V$ is strongly
  measurable, then there are measurable sets $U_n\subseteq S$ covering
  almost every point of $S$ such that $g|_{U_n}$ is continuous for every
  $n$.
proof:
  Exhaust $S$ by the finite-area sets on which both the source point and
  $\|g\|$ are bounded. On each such set, $g$ belongs to $L^1$. Apply Lusin
  continuity with exceptional areas tending to zero; the union of the
  resulting pieces covers that bounded set up to a null set. Pair the two
  countable indices.
-/
theorem StronglyMeasurable.exists_countable_measurable_cover_continuousOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [SecondCountableTopology V]
    {S : Set ℂ} {g : ℂ → V} (hg : StronglyMeasurable g)
    (hS : MeasurableSet S) :
    ∃ U : ℕ → Set ℂ,
      (∀ n, MeasurableSet (U n)) ∧
        (∀ n, U n ⊆ S) ∧
          (∀ᵐ x ∂MeasureTheory.volume.restrict S, x ∈ ⋃ n, U n) ∧
            ∀ n, ContinuousOn g (U n) := by
  let B : ℕ → Set ℂ := fun m ↦
    S ∩ closedBall 0 (m : ℝ) ∩ {x : ℂ | ‖g x‖ ≤ (m : ℝ)}
  let δ : ℕ → ℝ := fun j ↦ ((2 : ℝ)⁻¹) ^ j
  have hδpos (j : ℕ) : 0 < δ j := by
    simp only [δ]
    positivity
  have hBmeas (m : ℕ) : MeasurableSet (B m) := by
    exact (hS.inter measurableSet_closedBall).inter
      (measurableSet_le hg.norm.measurable measurable_const)
  have hBfinite (m : ℕ) : MeasureTheory.volume (B m) ≠ ∞ := by
    apply ne_of_lt
    exact (measure_mono (show B m ⊆ closedBall 0 (m : ℝ) by
      intro x hx
      exact hx.1.2)).trans_lt
        (isCompact_closedBall (0 : ℂ) (m : ℝ)).measure_lt_top
  have hgmem (m : ℕ) :
      MemLp g 1 (MeasureTheory.volume.restrict (B m)) := by
    letI : IsFiniteMeasure (MeasureTheory.volume.restrict (B m)) :=
      isFiniteMeasure_restrict.2 (hBfinite m)
    apply MemLp.of_bound
      (hg.aestronglyMeasurable.mono_measure Measure.restrict_le_self) (m : ℝ)
    filter_upwards [ae_restrict_mem (hBmeas m)] with x hx
    exact hx.2
  have hpiece (m j : ℕ) :
      ∃ U : Set ℂ,
        MeasurableSet U ∧ U ⊆ B m ∧
          MeasureTheory.volume (B m \ U) ≤
            ENNReal.ofReal (δ j) ∧
              ContinuousOn g U :=
    exists_lusin_continuousOn_subset (hBmeas m) (hBfinite m) hg
      (hgmem m) (hδpos j)
  choose U hUmeas hUB hUloss hUcont using hpiece
  have hcoverB (m : ℕ) :
      MeasureTheory.volume (B m \ ⋃ j, U m j) = 0 := by
    have hle (j : ℕ) :
        MeasureTheory.volume (B m \ ⋃ j, U m j) ≤
          ENNReal.ofReal (δ j) := by
      exact (measure_mono (diff_subset_diff_right
        (subset_iUnion (fun j ↦ U m j) j))).trans (hUloss m j)
    have hradius : Tendsto δ atTop (𝓝 (0 : ℝ)) := by
      simpa only [δ] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by positivity : 0 ≤ ((2 : ℝ)⁻¹))
          (by norm_num : ((2 : ℝ)⁻¹) < 1))
    have hupper : Tendsto (fun j ↦ ENNReal.ofReal (δ j))
        atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hradius
    have hzero : Tendsto
        (fun _j : ℕ ↦ MeasureTheory.volume (B m \ ⋃ j, U m j))
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
        (fun _ ↦ bot_le) hle
    exact tendsto_nhds_unique tendsto_const_nhds hzero
  have hSB : S ⊆ ⋃ m, B m := by
    intro x hxS
    obtain ⟨m : ℕ, hm⟩ := exists_nat_gt (max (dist 0 x) ‖g x‖)
    apply mem_iUnion.2
    refine ⟨m, ⟨⟨hxS, ?_⟩, ?_⟩⟩
    · exact mem_closedBall'.2 ((le_max_left _ _).trans hm.le)
    · exact (le_max_right _ _).trans hm.le
  have hbad : MeasureTheory.volume
      (S \ ⋃ (m : ℕ) (j : ℕ), U m j) = 0 := by
    apply measure_mono_null _ (measure_iUnion_null hcoverB)
    intro x hx
    rcases mem_iUnion.1 (hSB hx.1) with ⟨m, hxm⟩
    apply mem_iUnion.2
    refine ⟨m, hxm, ?_⟩
    intro hxU
    rcases mem_iUnion.1 hxU with ⟨j, hxUj⟩
    exact hx.2 (mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨j, hxUj⟩⟩)
  let T : ℕ → Set ℂ := fun n ↦ U n.unpair.1 n.unpair.2
  refine ⟨T, fun n ↦ hUmeas _ _, fun n x hx ↦ (hUB _ _ hx).1.1, ?_,
    fun n ↦ hUcont _ _⟩
  have hTunion : (⋃ n, T n) = ⋃ (m : ℕ) (j : ℕ), U m j := by
    exact Set.iUnion_unpair U
  show (⋃ n, T n) ∈ ae (MeasureTheory.volume.restrict S)
  rw [mem_ae_iff, Measure.restrict_apply]
  · simpa only [hTunion, diff_eq, inter_comm] using hbad
  · exact (MeasurableSet.iUnion (fun n ↦ hUmeas _ _)).compl

/--
%%handwave
name:
  Simultaneous Egorov theorem for countably many sequences
statement:
  Let $S$ be measurable with finite measure. For every $k\in\mathbb N$, let
  $u_{k,n}:S\to\mathbb R$ be measurable and converge to zero almost
  everywhere as $n\to\infty$. For every $\varepsilon>0$, there is a
  measurable $T\subseteq S$ with $|T|\leq\varepsilon$ such that, for every
  $k$, the sequence $u_{k,n}$ converges uniformly to zero on $S\setminus T$.
proof:
  Apply Egorov's theorem to the $k$-th sequence with exceptional-measure
  budget $(\varepsilon/2)2^{-k}$. Remove the union of the exceptional sets.
  Their measures sum to at most $\varepsilon$, and restricting a uniformly
  convergent sequence to the smaller common good set preserves uniform
  convergence.
-/
theorem exists_simultaneous_egorov_set
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α}
    (hS : MeasurableSet S) (hSfinite : μ S ≠ ∞)
    {u : ℕ → ℕ → α → ℝ}
    (hu : ∀ k n, Measurable (u k n))
    (hlim : ∀ k, ∀ᵐ x ∂μ, x ∈ S →
      Tendsto (fun n ↦ u k n x) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Set α,
      T ⊆ S ∧ MeasurableSet T ∧ μ T ≤ ENNReal.ofReal ε ∧
        ∀ k, TendstoUniformlyOn (u k) (fun _ ↦ 0) atTop (S \ T) := by
  let δ : ℕ → ℝ := fun k ↦ (ε / 2) * (2 : ℝ)⁻¹ ^ k
  have hδpos (k : ℕ) : 0 < δ k := by
    dsimp only [δ]
    positivity
  have hEgorov (k : ℕ) :
      ∃ T ⊆ S, MeasurableSet T ∧ μ T ≤ ENNReal.ofReal (δ k) ∧
        TendstoUniformlyOn (u k) (fun _ ↦ 0) atTop (S \ T) :=
    tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist
      (fun n ↦ (hu k n).edist measurable_const) hS hSfinite (hlim k) (hδpos k)
  choose T hTS hTmeas hTmeasure hTuniform using hEgorov
  refine ⟨⋃ k, T k, iUnion_subset hTS, MeasurableSet.iUnion hTmeas, ?_, ?_⟩
  · refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum hTmeasure).trans ?_)
    simp_rw [δ, ENNReal.ofReal_mul (half_pos hε).le]
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg,
      inv_eq_one_div, tsum_geometric_two,
      ← ENNReal.ofReal_mul (half_pos hε).le,
      div_mul_cancel₀ ε two_ne_zero]
    · intro n
      positivity
    · rw [inv_eq_one_div]
      exact summable_geometric_two
  · intro k
    apply (hTuniform k).mono
    intro x hx
    exact ⟨hx.1, fun hxTk ↦ hx.2 (mem_iUnion_of_mem k hxTk)⟩

/--
%%handwave
name:
  Two-point affine-approximation bad set
statement:
  Given $E\subseteq\mathbb C$, $f:\mathbb C\to\mathbb C$, a field of
  real-linear maps $A(x)$, and $\varepsilon,r\in\mathbb R$, define the bad
  set to consist of pairs $(x,y)$ such that
  $$
    y\in E\cap\overline B(x,r)
    \quad\text{and}\quad
    \varepsilon|y-x|
      <|f(y)-f(x)-A(x)(y-x)|.
  $$
-/
def approxFDerivBadPairs
    (E : Set ℂ) (f : ℂ → ℂ) (A : ℂ → ℂ →L[ℝ] ℂ) (ε r : ℝ) : Set (ℂ × ℂ) :=
  {p : ℂ × ℂ | p.2 ∈ E ∧ p.2 ∈ closedBall p.1 r ∧
    ε * ‖p.2 - p.1‖ < ‖f p.2 - f p.1 - A p.1 (p.2 - p.1)‖}

/--
%%handwave
name:
  Measurability of the two-point affine-error set
statement:
  Let $E\subseteq\mathbb C$ be measurable, let
  $f:\mathbb C\to\mathbb C$ and
  $A:\mathbb C\to\operatorname{Hom}_{\mathbb R}(\mathbb C,\mathbb C)$ be
  strongly measurable, and let $\varepsilon,r\in\mathbb R$. Then the set of
  pairs $(x,y)$ such that $y\in E\cap\overline B(x,r)$ and
  $$
    \varepsilon|y-x|<|f(y)-f(x)-A(x)(y-x)|
  $$
  is measurable in $\mathbb C\times\mathbb C$.
proof:
  Membership in the moving closed ball is a measurable distance inequality.
  Joint evaluation $(L,v)\mapsto L(v)$ is continuous, so the affine remainder
  is measurable; intersect its strict norm inequality with the measurable
  core and ball conditions.
-/
theorem measurableSet_approxFDerivBadPairs
    {E : Set ℂ} {f : ℂ → ℂ} {A : ℂ → ℂ →L[ℝ] ℂ} {r ε : ℝ}
    (hE : MeasurableSet E) (hf : StronglyMeasurable f)
    (hA : StronglyMeasurable A) :
    MeasurableSet (approxFDerivBadPairs E f A ε r) := by
  have hball : MeasurableSet {p : ℂ × ℂ | p.2 ∈ closedBall p.1 r} := by
    exact measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
  have hA_apply : Measurable fun p : ℂ × ℂ ↦ A p.1 (p.2 - p.1) := by
    exact (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((hA.measurable.comp measurable_fst).prodMk
        (measurable_snd.sub measurable_fst))
  have herror : Measurable fun p : ℂ × ℂ ↦
      ‖f p.2 - f p.1 - A p.1 (p.2 - p.1)‖ :=
    (((hf.measurable.comp measurable_snd).sub
      (hf.measurable.comp measurable_fst)).sub hA_apply).norm
  have hthreshold : Measurable fun p : ℂ × ℂ ↦ ε * ‖p.2 - p.1‖ :=
    measurable_const.mul (measurable_snd.sub measurable_fst).norm
  simpa only [approxFDerivBadPairs, Set.setOf_and] using
    (hE.preimage measurable_snd).inter
      (hball.inter (measurableSet_lt hthreshold herror))

/--
%%handwave
name:
  Measurability of affine-error section volumes
statement:
  Under the same hypotheses, for fixed $\varepsilon,r\in\mathbb R$ the map
  $$
    x\longmapsto\left|\left\{y\in E\cap\overline B(x,r):
      \varepsilon|y-x|<|f(y)-f(x)-A(x)(y-x)|\right\}\right|
  $$
  is measurable as an extended-nonnegative-real-valued function.
proof:
  The two-point affine-error set is measurable, and the volume of the vertical
  section of a measurable subset of a product is a measurable function of the
  first coordinate.
-/
theorem measurable_approxFDerivBadPairs_section_volume
    {E : Set ℂ} {f : ℂ → ℂ} {A : ℂ → ℂ →L[ℝ] ℂ} {r ε : ℝ}
    (hE : MeasurableSet E) (hf : StronglyMeasurable f)
    (hA : StronglyMeasurable A) :
    Measurable fun x : ℂ ↦ MeasureTheory.volume
      (Prod.mk x ⁻¹' approxFDerivBadPairs E f A ε r) :=
  measurable_measure_prodMk_left
    (measurableSet_approxFDerivBadPairs hE hf hA)

/--
%%handwave
name:
  Moving-ball density bad set
statement:
  Given $E\subseteq\mathbb C$ and $r\in\mathbb R$, define the density bad
  set to consist of pairs $(x,y)$ with
  $$
    y\in\overline B(x,r)\setminus E.
  $$
-/
def coreDensityBadPairs (E : Set ℂ) (r : ℝ) : Set (ℂ × ℂ) :=
  {p : ℂ × ℂ | p.2 ∈ closedBall p.1 r ∧ p.2 ∉ E}

/--
%%handwave
name:
  Measurability of moving-ball core defects
statement:
  If $E\subseteq\mathbb C$ is measurable and $r\in\mathbb R$, then the set
  of pairs $(x,y)$ with $y\in\overline B(x,r)\setminus E$ is measurable in
  $\mathbb C\times\mathbb C$.
proof:
  The moving-ball condition is a measurable distance inequality and the
  complement of $E$ is measurable.
-/
theorem measurableSet_coreDensityBadPairs
    {E : Set ℂ} {r : ℝ} (hE : MeasurableSet E) :
    MeasurableSet (coreDensityBadPairs E r) := by
  have hball : MeasurableSet {p : ℂ × ℂ | p.2 ∈ closedBall p.1 r} :=
    measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
  simpa only [coreDensityBadPairs, Set.setOf_and] using
    hball.inter (hE.compl.preimage measurable_snd)

/--
%%handwave
name:
  Relative moving-ball density defect
statement:
  For $E\subseteq\mathbb C$, $r\in\mathbb R$, and $x\in\mathbb C$, define
  $$
    \delta_{E,r}(x)
      =\frac{|\overline B(x,r)\setminus E|}
             {|\overline B(x,r)|}
      \in[0,\infty].
  $$
-/
def coreDensityDefect (E : Set ℂ) (r : ℝ) (x : ℂ) : ℝ≥0∞ :=
  MeasureTheory.volume (Prod.mk x ⁻¹' coreDensityBadPairs E r) /
    MeasureTheory.volume (closedBall x r)

/--
%%handwave
name:
  Measurability of the normalized core-density defect
statement:
  If $E\subseteq\mathbb C$ is measurable and $r\in\mathbb R$, then
  $$
    x\longmapsto\frac{|\overline B(x,r)\setminus E|}
                         {|\overline B(x,r)|}
  $$
  is measurable.
proof:
  The numerator is the volume of a section of a measurable two-point set.
  The explicit planar closed-ball volume formula makes the denominator a
  measurable constant, and division in $\mathbb R_{\geq0}\cup\{\infty\}$ is
  measurable.
-/
theorem measurable_coreDensityDefect
    {E : Set ℂ} {r : ℝ} (hE : MeasurableSet E) :
    Measurable (coreDensityDefect E r) := by
  have hnum : Measurable fun x : ℂ ↦
      MeasureTheory.volume (Prod.mk x ⁻¹' coreDensityBadPairs E r) :=
    measurable_measure_prodMk_left (measurableSet_coreDensityBadPairs hE)
  have hden : Measurable fun x : ℂ ↦
      MeasureTheory.volume (closedBall x r) := by
    simp only [Complex.volume_closedBall]
    exact measurable_const
  exact hnum.div hden

/--
%%handwave
name:
  Normalized affine-approximation defect
statement:
  For $E,f,A,\varepsilon,r$ and $x\in\mathbb C$, define the affine defect
  $$
    \beta_{E,f,A;\varepsilon,r}(x)
      =\frac{\left|\left\{y\in E\cap\overline B(x,r):
        \varepsilon|y-x|<|f(y)-f(x)-A(x)(y-x)|\right\}\right|}
             {|\overline B(x,r)|}.
  $$
-/
def approxFDerivDefect
    (E : Set ℂ) (f : ℂ → ℂ) (A : ℂ → ℂ →L[ℝ] ℂ)
    (ε r : ℝ) (x : ℂ) : ℝ≥0∞ :=
  MeasureTheory.volume (Prod.mk x ⁻¹' approxFDerivBadPairs E f A ε r) /
    MeasureTheory.volume (closedBall x r)

/--
%%handwave
name:
  Measurability of the normalized affine-approximation defect
statement:
  Let $E\subseteq\mathbb C$ be measurable and let $f$ and $A$ be strongly
  measurable. For fixed $\varepsilon,r\in\mathbb R$, the relative volume
  $$
    x\longmapsto\frac{\left|\left\{y\in E\cap\overline B(x,r):
      \varepsilon|y-x|<|f(y)-f(x)-A(x)(y-x)|\right\}\right|}
                         {|\overline B(x,r)|}
  $$
  is measurable.
proof:
  The numerator is the measurable section-volume function for the two-point
  affine-error set, and the planar closed-ball volume in the denominator is
  independent of the center.
-/
theorem measurable_approxFDerivDefect
    {E : Set ℂ} {f : ℂ → ℂ} {A : ℂ → ℂ →L[ℝ] ℂ} {r ε : ℝ}
    (hE : MeasurableSet E) (hf : StronglyMeasurable f)
    (hA : StronglyMeasurable A) :
    Measurable (approxFDerivDefect E f A ε r) := by
  have hnum : Measurable fun x : ℂ ↦
      MeasureTheory.volume
        (Prod.mk x ⁻¹' approxFDerivBadPairs E f A ε r) :=
    measurable_approxFDerivBadPairs_section_volume hE hf hA
  have hden : Measurable fun x : ℂ ↦
      MeasureTheory.volume (closedBall x r) := by
    simp only [Complex.volume_closedBall]
    exact measurable_const
  exact hnum.div hden

/--
%%handwave
name:
  Core-density defects are finite at positive radii
statement:
  If $r>0$, then for every $E\subseteq\mathbb C$ and $x\in\mathbb C$,
  $$
    \frac{|\overline B(x,r)\setminus E|}{|\overline B(x,r)|}<\infty.
  $$
proof:
  The numerator is at most the finite area of $\overline B(x,r)$, while the
  denominator is positive.
-/
theorem coreDensityDefect_ne_top
    {E : Set ℂ} {r : ℝ} (hr : 0 < r) (x : ℂ) :
    coreDensityDefect E r x ≠ ∞ := by
  have hden0 : MeasureTheory.volume (closedBall x r) ≠ 0 := by
    rw [Complex.volume_closedBall]
    exact mul_ne_zero
      (pow_ne_zero _ (ENNReal.ofReal_pos.2 hr).ne')
      (ENNReal.coe_ne_zero.mpr NNReal.pi_pos.ne')
  have hdentop : MeasureTheory.volume (closedBall x r) ≠ ∞ := by
    rw [Complex.volume_closedBall]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      ENNReal.coe_ne_top
  apply ENNReal.div_ne_top _ hden0
  apply lt_top_iff_ne_top.mp
  exact (measure_mono (fun y hy ↦ hy.1)).trans_lt
    (lt_top_iff_ne_top.mpr hdentop)

/--
%%handwave
name:
  Affine-error defects are finite at positive radii
statement:
  If $r>0$, then for every $E,f,A,\varepsilon$ and $x\in\mathbb C$, the
  normalized affine-error area in $\overline B(x,r)$ is finite.
proof:
  Its numerator measures a subset of the finite-area ball
  $\overline B(x,r)$, and the ball has positive area.
-/
theorem approxFDerivDefect_ne_top
    {E : Set ℂ} {f : ℂ → ℂ} {A : ℂ → ℂ →L[ℝ] ℂ} {ε r : ℝ}
    (hr : 0 < r) (x : ℂ) :
    approxFDerivDefect E f A ε r x ≠ ∞ := by
  have hden0 : MeasureTheory.volume (closedBall x r) ≠ 0 := by
    rw [Complex.volume_closedBall]
    exact mul_ne_zero
      (pow_ne_zero _ (ENNReal.ofReal_pos.2 hr).ne')
      (ENNReal.coe_ne_zero.mpr NNReal.pi_pos.ne')
  have hdentop : MeasureTheory.volume (closedBall x r) ≠ ∞ := by
    rw [Complex.volume_closedBall]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      ENNReal.coe_ne_top
  apply ENNReal.div_ne_top _ hden0
  apply lt_top_iff_ne_top.mp
  exact (measure_mono (fun y hy ↦ hy.2.1)).trans_lt
    (lt_top_iff_ne_top.mpr hdentop)

/--
%%handwave
name:
  Monotonicity of affine-error defects in the tolerance
statement:
  If $\varepsilon_1\le\varepsilon_2$, then for every $E,f,A,r,x$,
  $$
    b_{\varepsilon_2,r}(x)\le b_{\varepsilon_1,r}(x),
  $$
  where $b_{\varepsilon,r}(x)$ is the normalized area on which the affine
  error exceeds $\varepsilon|z-x|$.
proof:
  Every point whose error exceeds the larger threshold also exceeds the
  smaller threshold. Apply monotonicity of measure and divide by the common
  ball area.
-/
theorem approxFDerivDefect_anti_tolerance
    {E : Set ℂ} {f : ℂ → ℂ} {A : ℂ → ℂ →L[ℝ] ℂ}
    {ε₁ ε₂ r : ℝ} (hε : ε₁ ≤ ε₂) (x : ℂ) :
    approxFDerivDefect E f A ε₂ r x ≤
      approxFDerivDefect E f A ε₁ r x := by
  apply ENNReal.div_le_div_right
  apply measure_mono
  intro y hy
  change (x, y) ∈ approxFDerivBadPairs E f A ε₂ r at hy
  change (x, y) ∈ approxFDerivBadPairs E f A ε₁ r
  exact ⟨hy.1, hy.2.1,
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hε (norm_nonneg _)) hy.2.2⟩

/--
%%handwave
name:
  Dyadic Lusin--Whitney radius
statement:
  For $n\in\mathbb N$, define the $n$th Lusin--Whitney radius by
  $$
    r_n=2^{-n}.
  $$
-/
def lusinWhitneyRadius (n : ℕ) : ℝ := ((2 : ℝ)⁻¹) ^ n

/--
%%handwave
name:
  Positivity of the Lusin--Whitney radii
statement:
  For every $n\in\mathbb N$, the dyadic radius $2^{-n}$ is positive.
proof:
  The reciprocal of $2$ is positive, and positive numbers have positive
  natural powers.
-/
theorem lusinWhitneyRadius_pos (n : ℕ) : 0 < lusinWhitneyRadius n := by
  simp only [lusinWhitneyRadius]
  positivity

/--
%%handwave
name:
  Dyadic radii tend to zero from above
statement:
  The sequence $2^{-n}$ tends to $0$ through positive real numbers.
proof:
  It is the sequence of powers of $1/2$, which tends to zero because
  $0\leq1/2<1$; every term is positive.
-/
theorem tendsto_lusinWhitneyRadius :
    Tendsto lusinWhitneyRadius atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa only [lusinWhitneyRadius] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ ((2 : ℝ)⁻¹))
        (by norm_num : ((2 : ℝ)⁻¹) < 1))
  · filter_upwards with n
    exact lusinWhitneyRadius_pos n

/--
%%handwave
name:
  A dyadic radius comparable to a prescribed separation
statement:
  Let $N\in\mathbb N$ and $d>0$. If $d\le 2^{-N}/2$, then there is
  $n\ge N$ such that
  $$
    2d\le 2^{-n}<4d.
  $$
proof:
  Choose the first $n\ge N$ for which $2^{-n}<4d$. If $n=N$, the lower
  bound is the hypothesis. Otherwise minimality gives
  $2^{-(n-1)}\ge4d$, and halving gives $2^{-n}\ge2d$.
-/
theorem exists_lusinWhitneyRadius_comparable
    {d : ℝ} (N : ℕ) (hd : 0 < d)
    (hdhalf : d ≤ lusinWhitneyRadius N / 2) :
    ∃ n : ℕ, N ≤ n ∧ 2 * d ≤ lusinWhitneyRadius n ∧
      lusinWhitneyRadius n < 4 * d := by
  have ht : Tendsto lusinWhitneyRadius atTop (𝓝 (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mp tendsto_lusinWhitneyRadius |>.1
  have hev : ∀ᶠ n : ℕ in atTop,
      N ≤ n ∧ lusinWhitneyRadius n < 4 * d :=
    (eventually_ge_atTop N).and
      ((tendsto_order.mp ht).2 (4 * d) (by positivity))
  have hex : ∃ n : ℕ, N ≤ n ∧ lusinWhitneyRadius n < 4 * d := hev.exists
  let n := Nat.find hex
  have hn := Nat.find_spec hex
  refine ⟨n, hn.1, ?_, hn.2⟩
  by_cases hnN : n = N
  · rw [hnN]
    linarith
  · have hNn : N < n := lt_of_le_of_ne hn.1 (Ne.symm hnN)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hNn)
    have hNk : N ≤ k := by omega
    have hprev : 4 * d ≤ lusinWhitneyRadius k := by
      apply le_of_not_gt
      intro hklt
      exact Nat.find_min hex (by simpa only [n, hk] using Nat.lt_succ_self k)
        ⟨hNk, hklt⟩
    change 2 * d ≤ lusinWhitneyRadius n
    rw [hk]
    rw [show lusinWhitneyRadius (k + 1) = lusinWhitneyRadius k / 2 by
      simp only [lusinWhitneyRadius, pow_succ]
      ring]
    linarith

/--
%%handwave
name:
  Approximate differentials give vanishing dyadic core defects
statement:
  Suppose $A(x)$ is the approximate differential of $f$ at $x$. For every
  $E\subseteq\mathbb C$ and every $\varepsilon>0$, the relative volume of
  $$
    \left\{y\in E\cap\overline B(x,2^{-n}):
      \varepsilon|y-x|<|f(y)-f(x)-A(x)(y-x)|\right\}
  $$
  in $\overline B(x,2^{-n})$ tends to zero as $n\to\infty$.
proof:
  The displayed set is contained in the full affine-error set from the
  definition of approximate differentiability. Compose its limiting estimate
  with the positive dyadic radii and use monotonicity of volume.
-/
theorem HasApproxFDerivAt.tendsto_approxFDerivDefect_lusinWhitneyRadius
    {E : Set ℂ} {f : ℂ → ℂ} {A : ℂ → ℂ →L[ℝ] ℂ} {x : ℂ}
    (h : HasApproxFDerivAt f (A x) x) {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ ↦ approxFDerivDefect E f A ε (lusinWhitneyRadius n) x)
      atTop (𝓝 0) := by
  have hfull : Tendsto
      (fun n : ℕ ↦
        MeasureTheory.volume
            {y : ℂ | y ∈ closedBall x (lusinWhitneyRadius n) ∧
              ε * ‖y - x‖ < ‖f y - f x - A x (y - x)‖} /
          MeasureTheory.volume (closedBall x (lusinWhitneyRadius n)))
      atTop (𝓝 0) :=
    (h ε hε).comp tendsto_lusinWhitneyRadius
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hfull (fun _ ↦ bot_le) ?_
  intro n
  apply ENNReal.div_le_div_right
  apply measure_mono
  intro y hy
  change (x, y) ∈ approxFDerivBadPairs E f A ε (lusinWhitneyRadius n) at hy
  exact ⟨hy.2.1, hy.2.2⟩

/--
%%handwave
name:
  Dyadic defects are unchanged on a representative core
statement:
  Let $f_0=f$ and $A_0=A$ on $E$, let $x\in E$, and suppose $A(x)$ is the
  approximate differential of $f$ at $x$. Then for every $\varepsilon>0$,
  the normalized affine-error defects computed from $f_0,A_0$ on
  $E\cap\overline B(x,2^{-n})$ tend to zero.
proof:
  Both base-point values and every comparison-point value in the section lie
  in $E$, so replacing $f,A$ by $f_0,A_0$ leaves every affine-error section
  unchanged. Apply the dyadic consequence of approximate differentiability.
-/
theorem HasApproxFDerivAt.tendsto_approxFDerivDefect_lusinWhitneyRadius_of_eqOn
    {E : Set ℂ} {f f₀ : ℂ → ℂ} {A A₀ : ℂ → ℂ →L[ℝ] ℂ} {x : ℂ}
    (h : HasApproxFDerivAt f (A x) x) (hfx : Set.EqOn f₀ f E)
    (hAx : Set.EqOn A₀ A E) (hxE : x ∈ E) {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ ↦ approxFDerivDefect E f₀ A₀ ε (lusinWhitneyRadius n) x)
      atTop (𝓝 0) := by
  have hsection (n : ℕ) :
      Prod.mk x ⁻¹' approxFDerivBadPairs E f₀ A₀ ε (lusinWhitneyRadius n) =
        Prod.mk x ⁻¹' approxFDerivBadPairs E f A ε (lusinWhitneyRadius n) := by
    ext y
    by_cases hyE : y ∈ E
    · simp only [approxFDerivBadPairs, Set.mem_preimage, Set.mem_setOf_eq,
        hyE, true_and]
      rw [hfx hxE, hfx hyE, hAx hxE]
    · simp only [approxFDerivBadPairs, Set.mem_preimage, Set.mem_setOf_eq,
        hyE, false_and]
  simpa only [approxFDerivDefect, hsection] using
    h.tendsto_approxFDerivDefect_lusinWhitneyRadius (E := E) hε

/--
%%handwave
name:
  Almost every core point has vanishing dyadic density defect
statement:
  If $E\subseteq\mathbb C$ is measurable, then for almost every $x\in E$,
  $$
    \frac{|\overline B(x,2^{-n})\setminus E|}
         {|\overline B(x,2^{-n})|}\longrightarrow0.
  $$
proof:
  Apply the planar Lebesgue density theorem to the measurable complement of
  $E$. At points of $E$ its indicator is zero, and composing the resulting
  radius limit with $2^{-n}\to0^+$ gives the claim.
-/
theorem ae_tendsto_coreDensityDefect_lusinWhitneyRadius
    {E : Set ℂ} (hE : MeasurableSet E) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict E,
      Tendsto (fun n : ℕ ↦ coreDensityDefect E (lusinWhitneyRadius n) x)
        atTop (𝓝 0) := by
  have hdensity :=
    Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet
      MeasureTheory.volume hE.compl
  filter_upwards [ae_restrict_mem hE, ae_restrict_of_ae hdensity] with x hxE hx
  have hxcompl : x ∉ Eᶜ := by simpa using hxE
  have hxzero : Tendsto
      (fun r : ℝ ↦
        MeasureTheory.volume (Eᶜ ∩ closedBall x r) /
          MeasureTheory.volume (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Set.indicator_of_notMem hxcompl] using hx
  have hsection (r : ℝ) :
      Prod.mk x ⁻¹' coreDensityBadPairs E r = Eᶜ ∩ closedBall x r := by
    ext y
    simp only [coreDensityBadPairs, Set.mem_preimage, Set.mem_setOf_eq,
      mem_inter_iff, mem_compl_iff]
    tauto
  simpa only [coreDensityDefect, hsection] using
    hxzero.comp tendsto_lusinWhitneyRadius

/--
%%handwave
name:
  Three small planar defects do not fill a half-radius ball
statement:
  For every $x\in\mathbb C$ and $r>0$, three sets whose areas are each
  strictly less than $1/16$ of the area of $\overline B(x,r)$ have total
  area strictly less than the area of $\overline B(x,r/2)$:
  $$
    3\cdot\frac1{16}|\overline B(x,r)|
      < |\overline B(x,r/2)|.
  $$
proof:
  Use $|\overline B(x,r)|=\pi r^2$ and
  $|\overline B(x,r/2)|=\frac14\pi r^2$, then compare
  $3/16<1/4$.
-/
theorem three_sixteenth_ball_volumes_lt_half_ball_volume
    {x : ℂ} {r : ℝ} (hr : 0 < r) :
    (16 : ℝ≥0∞)⁻¹ * MeasureTheory.volume (closedBall x r) +
          (16 : ℝ≥0∞)⁻¹ * MeasureTheory.volume (closedBall x r) +
        (16 : ℝ≥0∞)⁻¹ * MeasureTheory.volume (closedBall x r) <
      MeasureTheory.volume (closedBall x (r / 2)) := by
  let V : ℝ≥0∞ := MeasureTheory.volume (closedBall x r)
  let q : ℝ≥0∞ := (16 : ℝ≥0∞)⁻¹
  have hVtop : V ≠ ∞ := by
    dsimp only [V]
    rw [Complex.volume_closedBall]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      ENNReal.coe_ne_top
  have hqtop : q ≠ ∞ := ENNReal.inv_ne_top.mpr (by norm_num)
  have hterm : q * V ≠ ∞ := ENNReal.mul_ne_top hqtop hVtop
  have htwo : q * V + q * V ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hterm, hterm⟩
  have hleft : q * V + q * V + q * V ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨htwo, hterm⟩
  have hright : MeasureTheory.volume (closedBall x (r / 2)) ≠ ∞ := by
    rw [Complex.volume_closedBall]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      ENNReal.coe_ne_top
  change q * V + q * V + q * V < _
  rw [← ENNReal.toReal_lt_toReal hleft hright,
    ENNReal.toReal_add htwo hterm, ENNReal.toReal_add hterm hterm]
  dsimp only [q, V]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    Complex.volume_closedBall, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ r / 2),
    ENNReal.coe_toReal]
  norm_num
  ring_nf
  have hprod : 0 < r ^ 2 * Real.pi :=
    mul_pos (sq_pos_of_pos hr) Real.pi_pos
  nlinarith

/--
%%handwave
name:
  A common good point for two approximate affine expansions
statement:
  Let $E\subseteq\mathbb C$, let $x,y\in\mathbb C$, and suppose
  $|y-x|\le r/2$ with $r>0$. If the relative area of
  $\overline B(x,r)\setminus E$ and the relative areas of the affine-error
  sets at $x$ and $y$ are each less than $1/16$, then there is
  $z\in E\cap\overline B(x,r/2)$ such that
  $$
    |f(z)-f(x)-A(x)(z-x)|\le\varepsilon|z-x|
  $$
  and
  $$
    |f(z)-f(y)-A(y)(z-y)|\le\varepsilon|z-y|.
  $$
proof:
  The half-radius ball lies in both comparison balls. If every point in it
  were outside $E$ or bad for one of the two affine expansions, its area
  would be at most the sum of the three defect areas, contradicting
  [three such defects have less area than the half-radius ball](lean:JJMath.Quasiconformal.three_sixteenth_ball_volumes_lt_half_ball_volume).
-/
theorem exists_common_good_point_of_defects_lt_inv_sixteen
    {E : Set ℂ} {f : ℂ → ℂ} {A : ℂ → ℂ →L[ℝ] ℂ}
    {x y : ℂ} {ε r : ℝ} (hr : 0 < r)
    (hxy : ‖y - x‖ ≤ r / 2)
    (hcore : coreDensityDefect E r x < (16 : ℝ≥0∞)⁻¹)
    (hbadx : approxFDerivDefect E f A ε r x < (16 : ℝ≥0∞)⁻¹)
    (hbady : approxFDerivDefect E f A ε r y < (16 : ℝ≥0∞)⁻¹) :
    ∃ z : ℂ, z ∈ E ∧ z ∈ closedBall x (r / 2) ∧
      ‖f z - f x - A x (z - x)‖ ≤ ε * ‖z - x‖ ∧
        ‖f z - f y - A y (z - y)‖ ≤ ε * ‖z - y‖ := by
  let D := Prod.mk x ⁻¹' coreDensityBadPairs E r
  let Bx := Prod.mk x ⁻¹' approxFDerivBadPairs E f A ε r
  let By := Prod.mk y ⁻¹' approxFDerivBadPairs E f A ε r
  let C := closedBall x (r / 2)
  have hvolx0 : MeasureTheory.volume (closedBall x r) ≠ 0 := by
    rw [Complex.volume_closedBall]
    exact mul_ne_zero
      (pow_ne_zero _ (ENNReal.ofReal_pos.2 hr).ne')
      (ENNReal.coe_ne_zero.mpr NNReal.pi_pos.ne')
  have hvolx_top : MeasureTheory.volume (closedBall x r) ≠ ∞ := by
    rw [Complex.volume_closedBall]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      ENNReal.coe_ne_top
  have hvoly0 : MeasureTheory.volume (closedBall y r) ≠ 0 := by
    simpa only [Complex.volume_closedBall] using hvolx0
  have hvoly_top : MeasureTheory.volume (closedBall y r) ≠ ∞ := by
    simpa only [Complex.volume_closedBall] using hvolx_top
  have hD : MeasureTheory.volume D <
      (16 : ℝ≥0∞)⁻¹ * MeasureTheory.volume (closedBall x r) := by
    exact (ENNReal.div_lt_iff (.inl hvolx0) (.inl hvolx_top)).mp hcore
  have hBx : MeasureTheory.volume Bx <
      (16 : ℝ≥0∞)⁻¹ * MeasureTheory.volume (closedBall x r) := by
    exact (ENNReal.div_lt_iff (.inl hvolx0) (.inl hvolx_top)).mp hbadx
  have hBy : MeasureTheory.volume By <
      (16 : ℝ≥0∞)⁻¹ * MeasureTheory.volume (closedBall y r) := by
    exact (ENNReal.div_lt_iff (.inl hvoly0) (.inl hvoly_top)).mp hbady
  have hBy' : MeasureTheory.volume By <
      (16 : ℝ≥0∞)⁻¹ * MeasureTheory.volume (closedBall x r) := by
    simpa only [Complex.volume_closedBall] using hBy
  have hsum : MeasureTheory.volume D + MeasureTheory.volume Bx +
      MeasureTheory.volume By < MeasureTheory.volume C := by
    calc
      MeasureTheory.volume D + MeasureTheory.volume Bx + MeasureTheory.volume By <
          (16 : ℝ≥0∞)⁻¹ * MeasureTheory.volume (closedBall x r) +
            (16 : ℝ≥0∞)⁻¹ * MeasureTheory.volume (closedBall x r) +
              (16 : ℝ≥0∞)⁻¹ * MeasureTheory.volume (closedBall x r) :=
        ENNReal.add_lt_add (ENNReal.add_lt_add hD hBx) hBy'
      _ < MeasureTheory.volume C := by
        exact three_sixteenth_ball_volumes_lt_half_ball_volume hr
  have hunion : MeasureTheory.volume (D ∪ Bx ∪ By) <
      MeasureTheory.volume C := by
    exact (le_trans (measure_union_le (D ∪ Bx) By)
      (add_le_add (measure_union_le D Bx) le_rfl)).trans_lt hsum
  have hnot : ¬ C ⊆ D ∪ Bx ∪ By := by
    intro hsub
    exact (not_lt_of_ge (measure_mono hsub)) hunion
  rcases Set.not_subset.mp hnot with ⟨z, hzC, hz⟩
  have hzD : z ∉ D := fun h ↦ hz (mem_union_left _ (mem_union_left _ h))
  have hzBx : z ∉ Bx := fun h ↦ hz (mem_union_left _ (mem_union_right _ h))
  have hzBy : z ∉ By := fun h ↦ hz (mem_union_right _ h)
  have hzE : z ∈ E := by
    by_contra hzE
    apply hzD
    change z ∈ closedBall x r ∧ z ∉ E
    refine ⟨Metric.closedBall_subset_closedBall (by linarith) hzC, hzE⟩
  have hzByBall : z ∈ closedBall y r := by
    apply Metric.closedBall_subset_closedBall' (x := x)
      (y := y) (ε₁ := r / 2) (ε₂ := r)
    · rw [dist_eq_norm, norm_sub_rev]
      linarith
    · exact hzC
  refine ⟨z, hzE, hzC, ?_, ?_⟩
  · change ¬(z ∈ E ∧ z ∈ closedBall x r ∧
      ε * ‖z - x‖ < ‖f z - f x - A x (z - x)‖) at hzBx
    push Not at hzBx
    exact hzBx hzE (Metric.closedBall_subset_closedBall (by linarith) hzC)
  · change ¬(z ∈ E ∧ z ∈ closedBall y r ∧
      ε * ‖z - y‖ < ‖f z - f y - A y (z - y)‖) at hzBy
    push Not at hzBy
    exact hzBy hzE hzByBall

/--
%%handwave
name:
  Uniform dyadic defects give a relative Fréchet differential
statement:
  Let $E,T\subseteq\mathbb C$ and let
  $A:\mathbb C\to\operatorname{Hom}_{\mathbb R}(\mathbb C,\mathbb C)$ be
  continuous on $T$. Suppose that, uniformly for $x\in T$ and all
  sufficiently small dyadic radii, the relative density defect of $E$ is
  less than $1/16$. Suppose also that for every $\eta>0$, uniformly for
  $x\in T$ and all sufficiently small dyadic radii, the relative area on
  which
  $$
    |f(z)-f(x)-A(x)(z-x)|>\eta|z-x|
  $$
  is less than $1/16$. Then $f$ has Fréchet differential $A(x)$ at every
  $x\in T$ relative to $T$.
proof:
  For nearby distinct $x,y\in T$, choose a sufficiently late dyadic radius
  $r$ with $2|y-x|\le r<4|y-x|$. The [common-good-point lemma](lean:JJMath.Quasiconformal.exists_common_good_point_of_defects_lt_inv_sixteen) gives a point $z\in E$ where both affine expansions have error at most
  $\eta$ times the corresponding distance. Subtract the two expansions.
  The two error terms are bounded by $5\eta|y-x|$, while continuity of $A$
  makes the remaining term $o(|y-x|)$.
-/
theorem hasFDerivWithinAt_of_uniform_lusinWhitney_defects
    {E T : Set ℂ} {f : ℂ → ℂ} {A : ℂ → ℂ →L[ℝ] ℂ}
    (hcont : ContinuousOn A T)
    (hcore : ∃ N : ℕ, ∀ n, N ≤ n → ∀ x ∈ T,
      coreDensityDefect E (lusinWhitneyRadius n) x < (16 : ℝ≥0∞)⁻¹)
    (hbad : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n, N ≤ n → ∀ x ∈ T,
      approxFDerivDefect E f A η (lusinWhitneyRadius n) x <
        (16 : ℝ≥0∞)⁻¹) :
    ∀ x, x ∈ T → HasFDerivWithinAt f (A x) T x := by
  intro x hx
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  let η : ℝ := c / 20
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨Ncore, hNcore⟩ := hcore
  obtain ⟨Nbad, hNbad⟩ := hbad η hη
  let N := max Ncore Nbad
  have hAev : ∀ᶠ y in 𝓝[T] x, ‖A y - A x‖ < c / 12 := by
    have ht := (Metric.tendsto_nhds.mp (hcont x hx)) (c / 12) (by positivity)
    simpa only [dist_eq_norm] using ht
  have hid : Tendsto (fun y : ℂ ↦ y) (𝓝[T] x) (𝓝 x) :=
    tendsto_id.mono_left inf_le_left
  have hdist : ∀ᶠ y in 𝓝[T] x,
      ‖y - x‖ < lusinWhitneyRadius N / 2 := by
    have ht := (Metric.tendsto_nhds.mp hid) (lusinWhitneyRadius N / 2)
      (div_pos (lusinWhitneyRadius_pos N) (by norm_num))
    simpa only [dist_eq_norm] using ht
  filter_upwards [self_mem_nhdsWithin, hAev, hdist] with y hyT hyA hyclose
  by_cases hyx : y = x
  · subst y
    simp
  · have hd : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
    obtain ⟨n, hnN, hnlow, hnup⟩ :=
      exists_lusinWhitneyRadius_comparable N hd hyclose.le
    have hncore : Ncore ≤ n := (le_max_left _ _).trans hnN
    have hnbad : Nbad ≤ n := (le_max_right _ _).trans hnN
    obtain ⟨z, _hzE, hzxball, hzxgood, hzygood⟩ :=
      exists_common_good_point_of_defects_lt_inv_sixteen
        (lusinWhitneyRadius_pos n) (by linarith)
        (hNcore n hncore x hx) (hNbad n hnbad x hx) (hNbad n hnbad y hyT)
    have hzx : ‖z - x‖ < 2 * ‖y - x‖ := by
      have hzle : ‖z - x‖ ≤ lusinWhitneyRadius n / 2 := by
        simpa only [mem_closedBall, dist_eq_norm] using hzxball
      linarith
    have hzy : ‖z - y‖ < 3 * ‖y - x‖ := by
      calc
        ‖z - y‖ = ‖(z - x) - (y - x)‖ := by congr 1 <;> ring
        _ ≤ ‖z - x‖ + ‖y - x‖ := norm_sub_le _ _
        _ < 3 * ‖y - x‖ := by linarith
    have hAapply : ‖(A y - A x) (z - y)‖ ≤
        ‖A y - A x‖ * ‖z - y‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hidR :
        f y - f x - A x (y - x) =
          (f z - f x - A x (z - x)) -
            (f z - f y - A y (z - y)) +
              -(A y - A x) (z - y) := by
      simp only [ContinuousLinearMap.sub_apply, map_sub]
      abel
    rw [hidR]
    calc
      ‖(f z - f x - A x (z - x)) -
          (f z - f y - A y (z - y)) + -(A y - A x) (z - y)‖
          ≤ ‖f z - f x - A x (z - x)‖ +
              ‖f z - f y - A y (z - y)‖ +
                ‖(A y - A x) (z - y)‖ := by
            exact (norm_add_le _ _).trans
              (by simpa only [norm_neg] using
                add_le_add (norm_sub_le
                  (f z - f x - A x (z - x))
                  (f z - f y - A y (z - y))) le_rfl)
      _ ≤ η * ‖z - x‖ + η * ‖z - y‖ +
            ‖A y - A x‖ * ‖z - y‖ := by gcongr
      _ ≤ c * ‖y - x‖ := by
        dsimp only [η]
        have hzx0 := norm_nonneg (z - x)
        have hzy0 := norm_nonneg (z - y)
        have hdist0 := norm_nonneg (y - x)
        nlinarith

/--
%%handwave
name:
  Countable differentiability decomposition from approximate differentials
statement:
  Let $S\subseteq\mathbb C$ be measurable, and let
  $f:S\to\mathbb C$ and $A:S\to\operatorname{Hom}_{\mathbb R}(\mathbb C,\mathbb C)$
  be measurable up to null sets. If $A(x)$ is the approximate differential
  of $f$ at almost every $x\in S$, then there are measurable sets
  $S_n\subseteq S$ covering almost every point of $S$ such that, for every
  $x\in S_n$, $f$ has differential $A(x)$ at $x$ relative to $S_n$.
proof:
  Pass to measurable representatives on a full-measure core and remove the
  null set where that core does not have density one. On bounded pieces, use
  Egorov's theorem simultaneously for the density defect and the affine-error
  defects at the tolerances $1/(k+1)$. Intersect the resulting uniform pieces
  with a countable Lusin continuity cover for $A$. On every intersection,
  [uniform dyadic defects and continuity of $A$ give the relative Fréchet differential](lean:JJMath.Quasiconformal.hasFDerivWithinAt_of_uniform_lusinWhitney_defects). Letting the Egorov loss tend to zero and pairing the countable indices gives a measurable cover of almost every point of $S$.
-/
theorem exists_countable_measurable_cover_hasFDerivWithinAt_of_ae_hasApproxFDerivAt
    {S : Set ℂ} {f : ℂ → ℂ} {A : ℂ → ℂ →L[ℝ] ℂ}
    (hS : MeasurableSet S)
    (hf : AEStronglyMeasurable f (MeasureTheory.volume.restrict S))
    (hA : AEStronglyMeasurable A (MeasureTheory.volume.restrict S))
    (happrox : ∀ᵐ x ∂MeasureTheory.volume.restrict S,
      HasApproxFDerivAt f (A x) x) :
    ∃ T : ℕ → Set ℂ,
      (∀ n, MeasurableSet (T n)) ∧
        (∀ n, T n ⊆ S) ∧
          (∀ᵐ x ∂MeasureTheory.volume.restrict S, x ∈ ⋃ n, T n) ∧
            ∀ n x, x ∈ T n → HasFDerivWithinAt f (A x) (T n) x := by
  rcases exists_lusinWhitney_measurable_core hS hf hA happrox with
    ⟨f₀, A₀, E, hf₀, hA₀, hEmeas, hES, hEae, hEpoint⟩
  have hfEq : Set.EqOn f₀ f E := fun x hx ↦ (hEpoint x hx).1
  have hAEq : Set.EqOn A₀ A E := fun x hx ↦ (hEpoint x hx).2.1
  rcases exists_measurable_ae_subset_of_ae hEmeas
      (ae_tendsto_coreDensityDefect_lusinWhitneyRadius hEmeas) with
    ⟨H, hHmeas, hHE, hHaeE, hHdensity⟩
  have hHaeS : ∀ᵐ x ∂MeasureTheory.volume.restrict S, x ∈ H := by
    have hcond : ∀ᵐ x ∂MeasureTheory.volume, x ∈ E → x ∈ H :=
      (ae_restrict_iff' hEmeas).mp hHaeE
    filter_upwards [hEae, ae_restrict_of_ae hcond] with x hxE hxcond
    exact hxcond hxE
  let η : ℕ → ℝ := fun k ↦ 1 / (k + 1 : ℝ)
  have hηpos (k : ℕ) : 0 < η k := by
    dsimp only [η]
    positivity
  have hApproxDefect (k : ℕ) (x : ℂ) (hx : x ∈ H) :
      Tendsto
        (fun n : ℕ ↦ approxFDerivDefect E f₀ A₀ (η k)
          (lusinWhitneyRadius n) x) atTop (𝓝 0) := by
    exact (hEpoint x (hHE hx)).2.2
      |>.tendsto_approxFDerivDefect_lusinWhitneyRadius_of_eqOn
        hfEq hAEq (hHE hx) (hηpos k)
  let B : ℕ → Set ℂ := fun m ↦ H ∩ closedBall 0 (m : ℝ)
  have hBmeas (m : ℕ) : MeasurableSet (B m) :=
    hHmeas.inter measurableSet_closedBall
  have hBfinite (m : ℕ) : MeasureTheory.volume (B m) ≠ ∞ := by
    apply ne_of_lt
    exact (measure_mono
      (show B m ⊆ closedBall 0 (m : ℝ) from inter_subset_right)).trans_lt
        (isCompact_closedBall (0 : ℂ) (m : ℝ)).measure_lt_top
  let u : ℕ → ℕ → ℂ → ℝ := fun k n x ↦
    match k with
    | 0 => (coreDensityDefect E (lusinWhitneyRadius n) x).toReal
    | k + 1 =>
        (approxFDerivDefect E f₀ A₀ (η k) (lusinWhitneyRadius n) x).toReal
  have hu (k n : ℕ) : Measurable (u k n) := by
    cases k with
    | zero =>
        exact (measurable_coreDensityDefect hEmeas).ennreal_toReal
    | succ k =>
        exact (measurable_approxFDerivDefect hEmeas hf₀ hA₀).ennreal_toReal
  have hlim (m k : ℕ) : ∀ᵐ x ∂MeasureTheory.volume, x ∈ B m →
      Tendsto (fun n ↦ u k n x) atTop (𝓝 0) := by
    apply ae_of_all
    intro x hx
    cases k with
    | zero =>
        exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
          (hHdensity x hx.1)
    | succ k =>
        exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
          (hApproxDefect k x hx.1)
  let δ : ℕ → ℝ := fun j ↦ ((2 : ℝ)⁻¹) ^ j
  have hδpos (j : ℕ) : 0 < δ j := by
    dsimp only [δ]
    positivity
  have hEgorov (m j : ℕ) :
      ∃ Q : Set ℂ, Q ⊆ B m ∧ MeasurableSet Q ∧
        MeasureTheory.volume Q ≤ ENNReal.ofReal (δ j) ∧
          ∀ k, TendstoUniformlyOn (u k) (fun _ ↦ 0) atTop (B m \ Q) :=
    exists_simultaneous_egorov_set (hBmeas m) (hBfinite m) hu (hlim m)
      (hδpos j)
  choose Q hQB hQmeas hQmeasure hQuniform using hEgorov
  rcases StronglyMeasurable.exists_countable_measurable_cover_continuousOn
      hA₀ hHmeas with
    ⟨U, hUmeas, _hUH, hUcover, hUcont⟩
  let G : ℕ → ℕ → Set ℂ := fun m j ↦ B m \ Q m j
  have hGmeas (m j : ℕ) : MeasurableSet (G m j) :=
    (hBmeas m).diff (hQmeas m j)
  have hGH (m j : ℕ) : G m j ⊆ H :=
    diff_subset.trans inter_subset_left
  have hBG (m j : ℕ) : B m \ G m j = Q m j := by
    ext x
    simp only [G, mem_diff]
    constructor
    · intro hx
      by_contra hxQ
      exact hx.2 ⟨hx.1, hxQ⟩
    · intro hxQ
      exact ⟨hQB m j hxQ, fun hx ↦ hx.2 hxQ⟩
  have hcoverB (m : ℕ) :
      MeasureTheory.volume (B m \ ⋃ j, G m j) = 0 := by
    have hle (j : ℕ) :
        MeasureTheory.volume (B m \ ⋃ j, G m j) ≤ ENNReal.ofReal (δ j) := by
      calc
        MeasureTheory.volume (B m \ ⋃ j, G m j)
            ≤ MeasureTheory.volume (B m \ G m j) :=
          measure_mono (diff_subset_diff_right (subset_iUnion (fun j ↦ G m j) j))
        _ = MeasureTheory.volume (Q m j) := by rw [hBG]
        _ ≤ ENNReal.ofReal (δ j) := hQmeasure m j
    have hradius : Tendsto δ atTop (𝓝 (0 : ℝ)) := by
      simpa only [δ] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by positivity : 0 ≤ ((2 : ℝ)⁻¹))
          (by norm_num : ((2 : ℝ)⁻¹) < 1))
    have hupper : Tendsto (fun j ↦ ENNReal.ofReal (δ j)) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hradius
    have hzero : Tendsto
        (fun _j : ℕ ↦ MeasureTheory.volume (B m \ ⋃ j, G m j))
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
        (fun _ ↦ bot_le) hle
    exact tendsto_nhds_unique tendsto_const_nhds hzero
  have hHB : H ⊆ ⋃ m, B m := by
    intro x hxH
    obtain ⟨m : ℕ, hm⟩ := exists_nat_gt (dist 0 x)
    apply mem_iUnion.2
    exact ⟨m, hxH, mem_closedBall'.2 hm.le⟩
  have hbadG : MeasureTheory.volume
      (H \ ⋃ (m : ℕ) (j : ℕ), G m j) = 0 := by
    apply measure_mono_null _ (measure_iUnion_null hcoverB)
    intro x hx
    rcases mem_iUnion.1 (hHB hx.1) with ⟨m, hxm⟩
    apply mem_iUnion.2
    refine ⟨m, hxm, ?_⟩
    intro hxG
    rcases mem_iUnion.1 hxG with ⟨j, hxGj⟩
    exact hx.2 (mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨j, hxGj⟩⟩)
  let V : ℕ → Set ℂ := fun n ↦ G n.unpair.1 n.unpair.2
  have hVmeas (n : ℕ) : MeasurableSet (V n) := hGmeas _ _
  have hVH (n : ℕ) : V n ⊆ H := hGH _ _
  have hVunion : (⋃ n, V n) = ⋃ (m : ℕ) (j : ℕ), G m j :=
    Set.iUnion_unpair G
  have hVcover : ∀ᵐ x ∂MeasureTheory.volume.restrict H, x ∈ ⋃ n, V n := by
    show (⋃ n, V n) ∈ ae (MeasureTheory.volume.restrict H)
    rw [mem_ae_iff, Measure.restrict_apply]
    · simpa only [hVunion, diff_eq, inter_comm] using hbadG
    · exact (MeasurableSet.iUnion hVmeas).compl
  let T : ℕ → Set ℂ := fun n ↦ V n.unpair.1 ∩ U n.unpair.2
  have hTmeas (n : ℕ) : MeasurableSet (T n) :=
    (hVmeas _).inter (hUmeas _)
  have hTS (n : ℕ) : T n ⊆ S := by
    intro x hx
    exact hES (hHE (hVH _ hx.1))
  have hTunion : (⋃ n, T n) = (⋃ a, V a) ∩ ⋃ b, U b := by
    rw [show (⋃ n, T n) = ⋃ (a : ℕ) (b : ℕ), V a ∩ U b by
      exact Set.iUnion_unpair (fun a b ↦ V a ∩ U b)]
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    tauto
  have hTcover : ∀ᵐ x ∂MeasureTheory.volume.restrict S, x ∈ ⋃ n, T n := by
    have hVcond : ∀ᵐ x ∂MeasureTheory.volume, x ∈ H → x ∈ ⋃ n, V n :=
      (ae_restrict_iff' hHmeas).mp hVcover
    have hUcond : ∀ᵐ x ∂MeasureTheory.volume, x ∈ H → x ∈ ⋃ n, U n :=
      (ae_restrict_iff' hHmeas).mp hUcover
    filter_upwards [hHaeS, ae_restrict_of_ae hVcond,
      ae_restrict_of_ae hUcond] with x hxH hxV hxU
    rw [hTunion]
    exact ⟨hxV hxH, hxU hxH⟩
  refine ⟨T, hTmeas, hTS, hTcover, ?_⟩
  intro n x hx
  let a := n.unpair.1
  let b := n.unpair.2
  let m := a.unpair.1
  let j := a.unpair.2
  have hT_eq : T n = G m j ∩ U b := by rfl
  have hcontT : ContinuousOn A₀ (T n) := by
    rw [hT_eq]
    exact (hUcont b).mono inter_subset_right
  have huniform (k : ℕ) :
      TendstoUniformlyOn (u k) (fun _ ↦ 0) atTop (T n) := by
    rw [hT_eq]
    exact (hQuniform m j k).mono inter_subset_left
  have hcoreT : ∃ N : ℕ, ∀ q, N ≤ q → ∀ y ∈ T n,
      coreDensityDefect E (lusinWhitneyRadius q) y < (16 : ℝ≥0∞)⁻¹ := by
    have hev := (Metric.tendstoUniformlyOn_iff.mp (huniform 0))
      (1 / 16 : ℝ) (by norm_num)
    rw [eventually_atTop] at hev
    rcases hev with ⟨N, hN⟩
    refine ⟨N, fun q hq y hy ↦ ?_⟩
    have hreal : (coreDensityDefect E (lusinWhitneyRadius q) y).toReal <
        (1 / 16 : ℝ) := by
      simpa only [u, Real.dist_eq, zero_sub, abs_neg,
        abs_of_nonneg ENNReal.toReal_nonneg] using hN q hq y hy
    apply (ENNReal.toReal_lt_toReal
      (coreDensityDefect_ne_top (lusinWhitneyRadius_pos q) y)
      (ENNReal.inv_ne_top.mpr (by norm_num))).mp
    simpa only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, one_div] using hreal
  have hbadT : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ q, N ≤ q → ∀ y ∈ T n,
      approxFDerivDefect E f₀ A₀ ε (lusinWhitneyRadius q) y <
        (16 : ℝ≥0∞)⁻¹ := by
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    have hkη : η k < ε := by simpa only [η] using hk
    have hev := (Metric.tendstoUniformlyOn_iff.mp (huniform (k + 1)))
      (1 / 16 : ℝ) (by norm_num)
    rw [eventually_atTop] at hev
    rcases hev with ⟨N, hN⟩
    refine ⟨N, fun q hq y hy ↦ ?_⟩
    have hreal :
        (approxFDerivDefect E f₀ A₀ (η k) (lusinWhitneyRadius q) y).toReal <
          (1 / 16 : ℝ) := by
      simpa only [u, Real.dist_eq, zero_sub, abs_neg,
        abs_of_nonneg ENNReal.toReal_nonneg] using hN q hq y hy
    have hsmall :
        approxFDerivDefect E f₀ A₀ (η k) (lusinWhitneyRadius q) y <
          (16 : ℝ≥0∞)⁻¹ := by
      apply (ENNReal.toReal_lt_toReal
        (approxFDerivDefect_ne_top (lusinWhitneyRadius_pos q) y)
        (ENNReal.inv_ne_top.mpr (by norm_num))).mp
      simpa only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, one_div] using hreal
    exact (approxFDerivDefect_anti_tolerance hkη.le y).trans_lt hsmall
  have hderiv₀ := hasFDerivWithinAt_of_uniform_lusinWhitney_defects
    hcontT hcoreT hbadT x hx
  have hxE : x ∈ E := hHE (hVH _ hx.1)
  have hfEqT : Set.EqOn f f₀ (T n) := by
    intro y hy
    exact (hfEq (hHE (hVH _ hy.1))).symm
  exact (hderiv₀.congr' hfEqT hx).congr_fderiv (hAEq hxE)

/--
%%handwave
name:
  Countable differentiability decomposition of planar local $W^{1,2}$ maps
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then there are measurable sets $S_n\subseteq\Omega$ covering almost
  every point of $\Omega$ such that $f$ has differential $Df(x)$ at every
  $x\in S_n$ relative to $S_n$.
proof:
  The map and its weak differential are measurable up to null sets by local
  integrability. At almost every source point, [the weak differential is the approximate differential](lean:JJMath.Quasiconformal.IsLocalW12On.ae_hasApproxFDerivAt). Apply [the countable measurable decomposition of an approximately differentiable map](lean:JJMath.Quasiconformal.exists_countable_measurable_cover_hasFDerivWithinAt_of_ae_hasApproxFDerivAt).
-/
theorem IsLocalW12On.exists_countable_measurable_cover_hasFDerivWithinAt
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) :
    ∃ T : ℕ → Set ℂ,
      (∀ n, MeasurableSet (T n)) ∧
        (∀ n, T n ⊆ Ω) ∧
          (∀ᵐ x ∂MeasureTheory.volume.restrict Ω, x ∈ ⋃ n, T n) ∧
            ∀ n x, x ∈ T n → HasFDerivWithinAt f (df x) (T n) x := by
  exact
    exists_countable_measurable_cover_hasFDerivWithinAt_of_ae_hasApproxFDerivAt
      h.1.measurableSet h.value_locallyIntegrableOn.aestronglyMeasurable
        h.differential_locallyIntegrableOn.aestronglyMeasurable
          h.ae_hasApproxFDerivAt

end

end Quasiconformal

end JJMath
