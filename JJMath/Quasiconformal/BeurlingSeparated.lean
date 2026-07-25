import JJMath.Quasiconformal.BeurlingApproximation
import JJMath.Quasiconformal.BeurlingRepresentation
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Beurling kernel on separated disks

This file proves the continuity estimate needed to extend the physical-kernel
formula from test functions to rough Calderón--Zygmund bad pieces.  Data are
supported in the disk of radius `3r/2`, while the output is measured outside
the disk of radius `2r`.  On this separated region the kernel has the uniform
radial bound `|K(x-w)| ≤ 16 π⁻¹ |x-c|⁻²`.
-/

namespace JJMath

open Set MeasureTheory Metric

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Physical Beurling kernel integral
statement:
  For $h:\mathbb C\to\mathbb C$, define its physical Beurling kernel
  integral by
  $$
    \mathcal K h(x)=\int_{\mathbb C}
      -\frac{h(w)}{\pi(x-w)^2}\,dw.
  $$
-/
def beurlingKernelIntegral (h : ℂ → ℂ) (x : ℂ) : ℂ :=
  ∫ w : ℂ, planarBeurlingKernel (x - w) * h w ∂volume

/--
%%handwave
name:
  Measurability of the physical Beurling kernel integral
statement:
  If $h:\mathbb C\to\mathbb C$ is strongly measurable almost everywhere,
  then $x\mapsto\mathcal K h(x)$ is strongly measurable almost everywhere.
proof:
  The integrand $(x,w)\mapsto K(x-w)h(w)$ is strongly measurable almost
  everywhere. Measurability is preserved by the parameterized Bochner
  integral.
-/
theorem aestronglyMeasurable_beurlingKernelIntegral
    {h : ℂ → ℂ} (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (beurlingKernelIntegral h) volume := by
  have hK : Measurable planarBeurlingKernel := by
    unfold planarBeurlingKernel
    fun_prop
  unfold beurlingKernelIntegral
  have hjoint : AEStronglyMeasurable
      (fun p : ℂ × ℂ ↦ planarBeurlingKernel (p.1 - p.2) * h p.2)
      (volume.prod volume) :=
    (hK.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable.mul
      hh.comp_snd
  exact hjoint.integral_prod_right'

/--
%%handwave
name:
  Separation between the intermediate disk and doubled exterior
statement:
  Let $r>0$. If $|w-c|\leq3r/2$ and $2r<|x-c|$, then
  $$
    |x-c|\leq4|x-w|.
  $$
proof:
  The triangle inequality gives $|x-c|\leq|x-w|+|w-c|$, while
  $|w-c|\leq3r/2<3|x-c|/4$.
-/
theorem norm_sub_le_four_mul_norm_sub_of_mem_intermediateDisk_of_mem_exterior
    {c x w : ℂ} {r : ℝ}
    (hw : ‖w - c‖ ≤ 3 * r / 2) (hx : 2 * r < ‖x - c‖) :
    ‖x - c‖ ≤ 4 * ‖x - w‖ := by
  have htri : ‖x - c‖ ≤ ‖x - w‖ + ‖w - c‖ := by
    calc
      ‖x - c‖ = ‖(x - w) + (w - c)‖ := by ring_nf
      _ ≤ ‖x - w‖ + ‖w - c‖ := norm_add_le _ _
  have hwrx : ‖w - c‖ < 3 * ‖x - c‖ / 4 := by
    calc
      ‖w - c‖ ≤ 3 * r / 2 := hw
      _ < 3 * ‖x - c‖ / 4 := by linarith
  linarith

/--
%%handwave
name:
  Reciprocal separation estimate
statement:
  Let $r>0$. If $|w-c|\leq3r/2$ and $2r<|x-c|$, then
  $$
    |x-w|^{-1}\leq4|x-c|^{-1}.
  $$
proof:
  The separation estimate gives $|x-c|/4\leq|x-w|$ and both sides are
  positive. Invert the inequality.
-/
theorem norm_sub_inv_le_four_mul_norm_sub_inv_of_mem_intermediateDisk_of_mem_exterior
    {c x w : ℂ} {r : ℝ} (hr : 0 < r)
    (hw : ‖w - c‖ ≤ 3 * r / 2) (hx : 2 * r < ‖x - c‖) :
    ‖x - w‖⁻¹ ≤ 4 * ‖x - c‖⁻¹ := by
  have hxpos : 0 < ‖x - c‖ := (by positivity : 0 < 2 * r).trans hx
  have hsep :=
    norm_sub_le_four_mul_norm_sub_of_mem_intermediateDisk_of_mem_exterior
      hw hx
  have hxwpos : 0 < ‖x - w‖ := by nlinarith
  have hquarter : ‖x - c‖ / 4 ≤ ‖x - w‖ := by linarith
  calc
    ‖x - w‖⁻¹ ≤ (‖x - c‖ / 4)⁻¹ :=
      (inv_le_inv₀ hxwpos (div_pos hxpos (by norm_num))).2 hquarter
    _ = 4 * ‖x - c‖⁻¹ := by field_simp

/--
%%handwave
name:
  Radial bound for the separated Beurling integrand
statement:
  Let $r>0$, $|w-c|\leq3r/2$, and $2r<|x-c|$. Then for every
  $v\in\mathbb C$,
  $$
    |K(x-w)v|
      \leq16\pi^{-1}|x-c|^{-2}|v|.
  $$
proof:
  Use $|K(z)|=\pi^{-1}|z|^{-2}$ and square the reciprocal separation
  estimate.
-/
theorem norm_planarBeurlingKernel_mul_le_of_mem_intermediateDisk_of_mem_exterior
    {c x w v : ℂ} {r : ℝ} (hr : 0 < r)
    (hw : ‖w - c‖ ≤ 3 * r / 2) (hx : 2 * r < ‖x - c‖) :
    ‖planarBeurlingKernel (x - w) * v‖ ≤
      16 * (Real.pi)⁻¹ * (‖x - c‖⁻¹ ^ (2 : ℕ)) * ‖v‖ := by
  have hinv :=
    norm_sub_inv_le_four_mul_norm_sub_inv_of_mem_intermediateDisk_of_mem_exterior
      hr hw hx
  rw [norm_mul, norm_planarBeurlingKernel]
  calc
    (Real.pi)⁻¹ * ‖x - w‖⁻¹ ^ (2 : ℕ) * ‖v‖ ≤
        (Real.pi)⁻¹ * (4 * ‖x - c‖⁻¹) ^ (2 : ℕ) * ‖v‖ := by
      gcongr
    _ = 16 * (Real.pi)⁻¹ * (‖x - c‖⁻¹ ^ (2 : ℕ)) * ‖v‖ := by ring

/--
%%handwave
name:
  Integrability of a separated Beurling kernel section
statement:
  Let $h\in L^1(\mathbb C)$ vanish outside
  $\overline B(c,3r/2)$, where $r>0$. If $2r<|x-c|$, then
  $w\mapsto K(x-w)h(w)$ is integrable.
proof:
  On the support of $h$, the integrand is bounded by the constant
  $16\pi^{-1}|x-c|^{-2}$ times $|h(w)|$.
-/
theorem integrable_planarBeurlingKernel_mul_of_support_intermediateDisk_of_mem_exterior
    {h : ℂ → ℂ} (hh : Integrable h volume)
    {c x : ℂ} {r : ℝ} (hr : 0 < r)
    (hhsupp : ∀ w : ℂ, h w ≠ 0 → ‖w - c‖ ≤ 3 * r / 2)
    (hx : 2 * r < ‖x - c‖) :
    Integrable (fun w : ℂ ↦ planarBeurlingKernel (x - w) * h w) volume := by
  let A : ℝ := 16 * (Real.pi)⁻¹ * (‖x - c‖⁻¹ ^ (2 : ℕ))
  have hdom : Integrable (fun w : ℂ ↦ A * ‖h w‖) volume :=
    hh.norm.const_mul A
  have hmeas : AEStronglyMeasurable
      (fun w : ℂ ↦ planarBeurlingKernel (x - w) * h w) volume := by
    have hK : Measurable planarBeurlingKernel := by
      unfold planarBeurlingKernel
      fun_prop
    exact (hK.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
      hh.aestronglyMeasurable
  apply Integrable.mono' hdom hmeas
  filter_upwards with w
  by_cases hhw : h w = 0
  · simp [hhw]
  · have hbound :=
      norm_planarBeurlingKernel_mul_le_of_mem_intermediateDisk_of_mem_exterior
        hr (hhsupp w hhw) hx (v := h w)
    simpa only [A, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        (mul_nonneg (by positivity) (inv_nonneg.mpr Real.pi_pos.le))
        (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) 2))] using hbound

/--
%%handwave
name:
  Linearity of the separated physical Beurling integral
statement:
  Let $r>0$ and suppose $h,g\in L^1(\mathbb C)$ both vanish outside
  $\overline B(c,3r/2)$. If $2r<|x-c|$, then
  $$
    \mathcal K(h-g)(x)=\mathcal K h(x)-\mathcal K g(x).
  $$
proof:
  The two kernel sections are integrable on the separated region, so
  linearity of the Bochner integral applies.
-/
theorem beurlingKernelIntegral_sub_of_support_intermediateDisk_of_mem_exterior
    {h g : ℂ → ℂ} (hh : Integrable h volume) (hg : Integrable g volume)
    {c x : ℂ} {r : ℝ} (hr : 0 < r)
    (hhsupp : ∀ w : ℂ, h w ≠ 0 → ‖w - c‖ ≤ 3 * r / 2)
    (hgsupp : ∀ w : ℂ, g w ≠ 0 → ‖w - c‖ ≤ 3 * r / 2)
    (hx : 2 * r < ‖x - c‖) :
    beurlingKernelIntegral (h - g) x =
      beurlingKernelIntegral h x - beurlingKernelIntegral g x := by
  have hhK :=
    integrable_planarBeurlingKernel_mul_of_support_intermediateDisk_of_mem_exterior
      hh hr hhsupp hx
  have hgK :=
    integrable_planarBeurlingKernel_mul_of_support_intermediateDisk_of_mem_exterior
      hg hr hgsupp hx
  rw [beurlingKernelIntegral, beurlingKernelIntegral,
    beurlingKernelIntegral, ← integral_sub hhK hgK]
  apply integral_congr_ae
  filter_upwards with w
  simp only [Pi.sub_apply]
  ring

/--
%%handwave
name:
  Pointwise bound for a separated Beurling kernel integral
statement:
  Let $h\in L^1(\mathbb C)$ vanish outside
  $\overline B(c,3r/2)$, where $r>0$. If $2r<|x-c|$, then
  $$
    |\mathcal K h(x)|
      \leq16\pi^{-1}|x-c|^{-2}\int_{\mathbb C}|h(w)|\,dw.
  $$
proof:
  Bound the norm of the integral by the integral of the norm, apply the
  separated kernel estimate pointwise on the support of $h$, and pull out
  the constant radial factor.
-/
theorem norm_beurlingKernelIntegral_le_of_support_intermediateDisk_of_mem_exterior
    {h : ℂ → ℂ} (hh : Integrable h volume)
    {c x : ℂ} {r : ℝ} (hr : 0 < r)
    (hhsupp : ∀ w : ℂ, h w ≠ 0 → ‖w - c‖ ≤ 3 * r / 2)
    (hx : 2 * r < ‖x - c‖) :
    ‖beurlingKernelIntegral h x‖ ≤
      (16 * (Real.pi)⁻¹ * (‖x - c‖⁻¹ ^ (2 : ℕ))) *
        ∫ w : ℂ, ‖h w‖ ∂volume := by
  let A : ℝ := 16 * (Real.pi)⁻¹ * (‖x - c‖⁻¹ ^ (2 : ℕ))
  have hint :=
    integrable_planarBeurlingKernel_mul_of_support_intermediateDisk_of_mem_exterior
      hh hr hhsupp hx
  have hdom : Integrable (fun w : ℂ ↦ A * ‖h w‖) volume :=
    hh.norm.const_mul A
  calc
    ‖beurlingKernelIntegral h x‖ ≤
        ∫ w : ℂ, ‖planarBeurlingKernel (x - w) * h w‖ ∂volume :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ w : ℂ, A * ‖h w‖ ∂volume := by
      apply integral_mono hint.norm hdom
      intro w
      by_cases hhw : h w = 0
      · simp [hhw]
      · exact norm_planarBeurlingKernel_mul_le_of_mem_intermediateDisk_of_mem_exterior
          hr (hhsupp w hhw) hx
    _ = A * ∫ w : ℂ, ‖h w‖ ∂volume := by rw [integral_const_mul]
    _ = _ := rfl

/--
%%handwave
name:
  Square integrability of a separated physical Beurling integral
statement:
  Let $h\in L^1(\mathbb C)$ vanish outside
  $\overline B(c,3r/2)$, where $r>0$. Then
  $x\mapsto|\mathcal K h(x)|^2$ is integrable on $\{|x-c|>2r\}$.
proof:
  The pointwise bound gives
  $|\mathcal K h(x)|^2\leq
  (16\pi^{-1}\|h\|_1)^2|x-c|^{-4}$. The translated
  inverse-fourth-power tail is integrable.
-/
theorem integrableOn_norm_sq_beurlingKernelIntegral_of_support_intermediateDisk
    {h : ℂ → ℂ} (hh : Integrable h volume)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hhsupp : ∀ w : ℂ, h w ≠ 0 → ‖w - c‖ ≤ 3 * r / 2) :
    IntegrableOn (fun x : ℂ ↦ ‖beurlingKernelIntegral h x‖ ^ (2 : ℕ))
      {x : ℂ | 2 * r < ‖x - c‖} volume := by
  let I : ℝ := ∫ w : ℂ, ‖h w‖ ∂volume
  let A : ℝ := (16 * (Real.pi)⁻¹ * I) ^ (2 : ℕ)
  have hI : 0 ≤ I := integral_nonneg fun w ↦ norm_nonneg (h w)
  have hA : 0 ≤ A := sq_nonneg _
  have hdom : IntegrableOn
      (fun x : ℂ ↦ A * (‖x - c‖⁻¹ ^ (4 : ℕ)))
      {x : ℂ | 2 * r < ‖x - c‖} volume :=
    (HarmonicAnalysis.integrableOn_norm_sub_inv_four_exterior
      (2 * r) (by positivity) c).const_mul A
  apply Integrable.mono' hdom
    (((aestronglyMeasurable_beurlingKernelIntegral hh.aestronglyMeasurable).norm
      |>.aemeasurable.pow_const 2).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self)
  filter_upwards [ae_restrict_mem
      ((isOpen_lt continuous_const
        (continuous_id.sub continuous_const).norm).measurableSet)] with x hx
  have hpoint :=
    norm_beurlingKernelIntegral_le_of_support_intermediateDisk_of_mem_exterior
      hh hr hhsupp hx
  have hraw : ‖beurlingKernelIntegral h x‖ ^ (2 : ℕ) ≤
      A * (‖x - c‖⁻¹ ^ (4 : ℕ)) := by
    calc
      ‖beurlingKernelIntegral h x‖ ^ (2 : ℕ) ≤
          ((16 * (Real.pi)⁻¹ * (‖x - c‖⁻¹ ^ (2 : ℕ))) * I) ^
            (2 : ℕ) := by gcongr
      _ = A * (‖x - c‖⁻¹ ^ (4 : ℕ)) := by
        dsimp only [A, I]
        ring
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg (beurlingKernelIntegral h x)) 2),
    abs_of_nonneg (mul_nonneg hA
      (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) 4))] using hraw

/--
%%handwave
name:
  $L^1$-to-exterior-$L^2$ bound for the physical Beurling integral
statement:
  Let $h\in L^1(\mathbb C)$ vanish outside
  $\overline B(c,3r/2)$, where $r>0$. Then
  $$
    \int_{|x-c|>2r}|\mathcal K h(x)|^2\,dx
      \leq
      (16\pi^{-1}\|h\|_1)^2\frac{2\pi}{(2r)^2}.
  $$
proof:
  Square the separated pointwise bound, integrate, and use the translated
  inverse-fourth-power tail estimate.
-/
theorem setIntegral_norm_sq_beurlingKernelIntegral_le_of_support_intermediateDisk
    {h : ℂ → ℂ} (hh : Integrable h volume)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hhsupp : ∀ w : ℂ, h w ≠ 0 → ‖w - c‖ ≤ 3 * r / 2) :
    (∫ x in {x : ℂ | 2 * r < ‖x - c‖},
        ‖beurlingKernelIntegral h x‖ ^ (2 : ℕ) ∂volume) ≤
      (16 * (Real.pi)⁻¹ * (∫ w : ℂ, ‖h w‖ ∂volume)) ^ (2 : ℕ) *
        (2 * Real.pi / (2 * r) ^ 2) := by
  let I : ℝ := ∫ w : ℂ, ‖h w‖ ∂volume
  let A : ℝ := (16 * (Real.pi)⁻¹ * I) ^ (2 : ℕ)
  have hA : 0 ≤ A := sq_nonneg _
  have hout :=
    integrableOn_norm_sq_beurlingKernelIntegral_of_support_intermediateDisk
      hh hr hhsupp
  have hdom : IntegrableOn
      (fun x : ℂ ↦ A * (‖x - c‖⁻¹ ^ (4 : ℕ)))
      {x : ℂ | 2 * r < ‖x - c‖} volume :=
    (HarmonicAnalysis.integrableOn_norm_sub_inv_four_exterior
      (2 * r) (by positivity) c).const_mul A
  calc
    (∫ x in {x : ℂ | 2 * r < ‖x - c‖},
        ‖beurlingKernelIntegral h x‖ ^ (2 : ℕ) ∂volume) ≤
        ∫ x in {x : ℂ | 2 * r < ‖x - c‖},
          A * (‖x - c‖⁻¹ ^ (4 : ℕ)) ∂volume := by
      apply integral_mono_ae hout hdom
      filter_upwards [ae_restrict_mem
          ((isOpen_lt continuous_const
            (continuous_id.sub continuous_const).norm).measurableSet)] with x hx
      have hpoint :=
        norm_beurlingKernelIntegral_le_of_support_intermediateDisk_of_mem_exterior
          hh hr hhsupp hx
      calc
        ‖beurlingKernelIntegral h x‖ ^ (2 : ℕ) ≤
            ((16 * (Real.pi)⁻¹ * (‖x - c‖⁻¹ ^ (2 : ℕ))) * I) ^
              (2 : ℕ) := by gcongr
        _ = A * (‖x - c‖⁻¹ ^ (4 : ℕ)) := by
          dsimp only [A, I]
          ring
    _ = A * (∫ x in {x : ℂ | 2 * r < ‖x - c‖},
        ‖x - c‖⁻¹ ^ (4 : ℕ) ∂volume) := by rw [integral_const_mul]
    _ ≤ A * (2 * Real.pi / (2 * r) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (HarmonicAnalysis.setIntegral_norm_sub_inv_four_exterior_le
          (2 * r) (by positivity) c) hA
    _ = _ := rfl

/--
%%handwave
name:
  Compactly supported $L^2$ data are integrable
statement:
  Let $h\in L^2(\mathbb C)$ vanish outside a closed disk
  $\overline B(c,R)$. Then $h\in L^1(\mathbb C)$.
proof:
  The closed disk has finite area. On its restricted measure, the inclusion
  $L^2\subseteq L^1$ follows from Hölder's inequality. Since $h$ vanishes
  off the disk, restricted and global integrability agree.
-/
theorem integrable_of_memLp_two_of_support_closedBall
    {h : ℂ → ℂ} (hh : MemLp h 2 volume)
    {c : ℂ} {R : ℝ}
    (hhsupp : ∀ w : ℂ, h w ≠ 0 → ‖w - c‖ ≤ R) :
    Integrable h volume := by
  let D : Set ℂ := Metric.closedBall c R
  have hDcompact : IsCompact D := isCompact_closedBall c R
  haveI : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.2 hDcompact.measure_ne_top
  have hsupp : Function.support h ⊆ D := by
    intro w hw
    simpa only [D, Metric.mem_closedBall, dist_eq_norm] using hhsupp w hw
  apply (integrableOn_iff_integrable_of_support_subset hsupp).1
  exact (hh.restrict D).integrable (by norm_num)

/--
%%handwave
name:
  $L^1$ bound for disk-supported $L^2$ data
statement:
  Let $h\in L^2(\mathbb C)$ vanish outside $\overline B(c,R)$. Then
  $$
    \left(\int_{\mathbb C}|h(w)|\,dw\right)^2
      \leq |\overline B(c,R)|
        \int_{\mathbb C}|h(w)|^2\,dw.
  $$
proof:
  Apply Hölder's inequality with exponents $2$ and $2$ to $|h|$ and the
  constant function one on the disk. Square the resulting inequality and
  use that $h$ vanishes off the disk.
-/
theorem integral_norm_sq_le_volume_mul_integral_norm_sq_of_memLp_two_of_support_closedBall
    {h : ℂ → ℂ} (hh : MemLp h 2 volume)
    {c : ℂ} {R : ℝ}
    (hhsupp : ∀ w : ℂ, h w ≠ 0 → ‖w - c‖ ≤ R) :
    (∫ w : ℂ, ‖h w‖ ∂volume) ^ (2 : ℕ) ≤
      (volume (Metric.closedBall c R)).toReal *
        ∫ w : ℂ, ‖h w‖ ^ (2 : ℕ) ∂volume := by
  let D : Set ℂ := Metric.closedBall c R
  have hDcompact : IsCompact D := isCompact_closedBall c R
  haveI : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.2 hDcompact.measure_ne_top
  have hsupp : Function.support h ⊆ D := by
    intro w hw
    simpa only [D, Metric.mem_closedBall, dist_eq_norm] using hhsupp w hw
  have hhD : MemLp (fun w : ℂ ↦ ‖h w‖) (ENNReal.ofReal (2 : ℝ))
      (volume.restrict D) := by
    simpa using (hh.restrict D).norm
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := volume.restrict D) Real.HolderConjugate.two_two
    hhD (memLp_const (1 : ℝ))
  have hglobal : (∫ w : ℂ, ‖h w‖ ∂volume) =
      ∫ w in D, ‖h w‖ ∂volume := by
    symm
    rw [← integral_indicator hDcompact.measurableSet]
    apply integral_congr_ae
    filter_upwards with w
    by_cases hw : w ∈ D
    · simp [hw]
    · have hzero : h w = 0 := by
        by_contra hn
        exact hw (hsupp hn)
      simp [hw, hzero]
  have hholder' : (∫ w in D, ‖h w‖ ∂volume) ≤
      ((∫ w in D, ‖h w‖ ^ 2 ∂volume) ^ (1 / (2 : ℝ))) *
        ((volume D).toReal ^ (1 / (2 : ℝ))) := by
    simpa only [Real.norm_of_nonneg (norm_nonneg _), norm_one, mul_one,
      Real.rpow_two, one_pow, integral_const, Measure.restrict_apply_univ,
      measureReal_def, smul_eq_mul] using hholder
  rw [hglobal]
  have henergy : 0 ≤ ∫ w in D, ‖h w‖ ^ 2 ∂volume :=
    integral_nonneg fun w ↦ sq_nonneg ‖h w‖
  have hvol : 0 ≤ (volume D).toReal := ENNReal.toReal_nonneg
  have henergyRoot :
      ((∫ w in D, ‖h w‖ ^ 2 ∂volume) ^ (2 : ℝ)⁻¹) ^ (2 : ℕ) =
        ∫ w in D, ‖h w‖ ^ 2 ∂volume :=
    Real.rpow_inv_natCast_pow henergy (by norm_num)
  have hvolumeRoot :
      ((volume D).toReal ^ (2 : ℝ)⁻¹) ^ (2 : ℕ) =
        (volume D).toReal :=
    Real.rpow_inv_natCast_pow hvol (by norm_num)
  calc
    (∫ w in D, ‖h w‖ ∂volume) ^ (2 : ℕ) ≤
        (((∫ w in D, ‖h w‖ ^ 2 ∂volume) ^ (1 / (2 : ℝ))) *
          ((volume D).toReal ^ (1 / (2 : ℝ)))) ^ (2 : ℕ) := by gcongr
    _ = (volume D).toReal * ∫ w in D, ‖h w‖ ^ 2 ∂volume := by
      rw [mul_pow, show (1 / (2 : ℝ)) = (2 : ℝ)⁻¹ by norm_num,
        henergyRoot, hvolumeRoot]
      ring
    _ ≤ (volume D).toReal * ∫ w : ℂ, ‖h w‖ ^ 2 ∂volume := by
      apply mul_le_mul_of_nonneg_left _ hvol
      exact setIntegral_le_integral
        ((memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).1 hh)
        (ae_of_all _ fun w ↦ sq_nonneg ‖h w‖)

/--
%%handwave
name:
  Separated-disk $L^2$ continuity of the physical Beurling integral
statement:
  Let $r>0$ and let $h\in L^2(\mathbb C)$ vanish outside
  $D=\overline B(c,3r/2)$. Then
  $$
    \int_{|x-c|>2r}|\mathcal K h(x)|^2\,dx
      \leq C_r\int_{\mathbb C}|h(w)|^2\,dw,
  $$
  where
  $$
    C_r=(16\pi^{-1})^2|D|\frac{2\pi}{(2r)^2}.
  $$
proof:
  Apply the $L^1$-to-exterior-$L^2$ estimate, then bound
  $\|h\|_1^2$ by $|D|\|h\|_2^2$ using Hölder's inequality.
-/
theorem setIntegral_norm_sq_beurlingKernelIntegral_le_of_memLp_two_of_support_intermediateDisk
    {h : ℂ → ℂ} (hh : MemLp h 2 volume)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hhsupp : ∀ w : ℂ, h w ≠ 0 → ‖w - c‖ ≤ 3 * r / 2) :
    (∫ x in {x : ℂ | 2 * r < ‖x - c‖},
        ‖beurlingKernelIntegral h x‖ ^ (2 : ℕ) ∂volume) ≤
      ((16 * (Real.pi)⁻¹) ^ (2 : ℕ) *
          (volume (Metric.closedBall c (3 * r / 2))).toReal *
          (2 * Real.pi / (2 * r) ^ 2)) *
        ∫ w : ℂ, ‖h w‖ ^ (2 : ℕ) ∂volume := by
  let I : ℝ := ∫ w : ℂ, ‖h w‖ ∂volume
  let E : ℝ := ∫ w : ℂ, ‖h w‖ ^ (2 : ℕ) ∂volume
  let V : ℝ := (volume (Metric.closedBall c (3 * r / 2))).toReal
  let T : ℝ := 2 * Real.pi / (2 * r) ^ 2
  let C : ℝ := (16 * (Real.pi)⁻¹) ^ (2 : ℕ)
  have hint : Integrable h volume :=
    integrable_of_memLp_two_of_support_closedBall hh hhsupp
  have hout :=
    setIntegral_norm_sq_beurlingKernelIntegral_le_of_support_intermediateDisk
      hint hr hhsupp
  have hI : I ^ (2 : ℕ) ≤ V * E := by
    exact integral_norm_sq_le_volume_mul_integral_norm_sq_of_memLp_two_of_support_closedBall
      hh hhsupp
  have hC : 0 ≤ C := sq_nonneg _
  have hT : 0 ≤ T := by
    dsimp only [T]
    positivity
  calc
    (∫ x in {x : ℂ | 2 * r < ‖x - c‖},
        ‖beurlingKernelIntegral h x‖ ^ (2 : ℕ) ∂volume) ≤
        (16 * (Real.pi)⁻¹ * I) ^ (2 : ℕ) * T := by
      simpa only [I, T] using hout
    _ = C * I ^ (2 : ℕ) * T := by
      dsimp only [C]
      ring
    _ ≤ C * (V * E) * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hI hC) hT
    _ = (C * V * T) * E := by ring
    _ = _ := rfl

/--
%%handwave
name:
  Separated physical Beurling integrals belong to exterior $L^2$
statement:
  Let $r>0$ and let $h\in L^2(\mathbb C)$ vanish outside
  $\overline B(c,3r/2)$. Then $\mathcal K h$ belongs to
  $L^2(\{x:|x-c|>2r\})$.
proof:
  Compact support makes $h$ integrable. The separated pointwise kernel
  bound then gives integrability of $|\mathcal K h|^2$ on the exterior.
-/
theorem memLp_two_beurlingKernelIntegral_restrict_exterior_of_support_intermediateDisk
    {h : ℂ → ℂ} (hh : MemLp h 2 volume)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hhsupp : ∀ w : ℂ, h w ≠ 0 → ‖w - c‖ ≤ 3 * r / 2) :
    MemLp (beurlingKernelIntegral h) 2
      (volume.restrict {x : ℂ | 2 * r < ‖x - c‖}) := by
  have hint : Integrable h volume :=
    integrable_of_memLp_two_of_support_closedBall hh hhsupp
  apply (memLp_two_iff_integrable_sq_norm
    ((aestronglyMeasurable_beurlingKernelIntegral hh.aestronglyMeasurable).mono_measure
      Measure.restrict_le_self)).2
  exact integrableOn_norm_sq_beurlingKernelIntegral_of_support_intermediateDisk
    hint hr hhsupp

/--
%%handwave
name:
  Squared exterior $L^2$ bound for the physical Beurling integral
statement:
  Let $r>0$ and let $h\in L^2(\mathbb C)$ vanish outside
  $D=\overline B(c,3r/2)$. Then
  $$
    \|\mathcal K h\|_{L^2(|x-c|>2r)}^2
      \leq (16\pi^{-1})^2|D|\frac{2\pi}{(2r)^2}
        \|h\|_{L^2(\mathbb C)}^2.
  $$
proof:
  Rewrite both squared $L^2$ seminorms as integrals of squared norms and
  apply the separated-disk integral estimate.
-/
theorem eLpNorm_two_toReal_sq_beurlingKernelIntegral_restrict_exterior_le
    {h : ℂ → ℂ} (hh : MemLp h 2 volume)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hhsupp : ∀ w : ℂ, h w ≠ 0 → ‖w - c‖ ≤ 3 * r / 2) :
    (eLpNorm (beurlingKernelIntegral h) 2
        (volume.restrict {x : ℂ | 2 * r < ‖x - c‖})).toReal ^ (2 : ℕ) ≤
      ((16 * (Real.pi)⁻¹) ^ (2 : ℕ) *
          (volume (Metric.closedBall c (3 * r / 2))).toReal *
          (2 * Real.pi / (2 * r) ^ 2)) *
        (eLpNorm h 2 volume).toReal ^ (2 : ℕ) := by
  have hout : MemLp (beurlingKernelIntegral h) 2
      (volume.restrict {x : ℂ | 2 * r < ‖x - c‖}) :=
    memLp_two_beurlingKernelIntegral_restrict_exterior_of_support_intermediateDisk
      hh hr hhsupp
  rw [eLpNorm_two_toReal_sq_eq_integral_norm_sq hout,
    eLpNorm_two_toReal_sq_eq_integral_norm_sq hh]
  exact setIntegral_norm_sq_beurlingKernelIntegral_le_of_memLp_two_of_support_intermediateDisk
    hh hr hhsupp

end

end Quasiconformal

end JJMath
