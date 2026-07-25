import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Polar-coordinate formulas for planar annuli

This file records a reusable polar-coordinate formula for set integrals over
centered planar annuli. The statement is vector-valued and does not impose
integrability hypotheses: as usual for the Bochner integral, both sides are
defined to be zero when the corresponding integrand is not integrable.
-/

namespace JJMath

open Set MeasureTheory

namespace HarmonicAnalysis

noncomputable section

/--
%%handwave
name:
  Polar-coordinate formula outside a disk
statement:
  Let $E$ be a real normed vector space, let $F:\mathbb C\to E$, and let
  $a>0$. Then
  $$
    \int_{|z|>a}F(z)\,dz
      =\int_a^\infty\int_{-\pi}^{\pi}
        r\,F(re^{i\theta})\,d\theta\,dr.
  $$
proof:
  Apply planar polar change of variables to the product of $F$ with the
  indicator of $\{|z|>a\}$. On the polar chart this indicator becomes the
  radial condition $r>a$, while the Jacobian is $r$.
-/
theorem setIntegral_exterior_eq_polar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℂ → E) {a : ℝ} (ha : 0 < a) :
    (∫ z in {z : ℂ | a < ‖z‖}, F z) =
      ∫ p in Ioi a ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • F (Complex.polarCoord.symm p) := by
  let A : Set ℂ := {z : ℂ | a < ‖z‖}
  let B : Set (ℝ × ℝ) := Ioi a ×ˢ Set.univ
  let H : ℝ × ℝ → E := fun p ↦
    p.1 • F (Complex.polarCoord.symm p)
  have hAmeas : MeasurableSet A :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hBmeas : MeasurableSet B := measurableSet_Ioi.prod MeasurableSet.univ
  have hpolar := Complex.integral_comp_polarCoord_symm (A.indicator F)
  calc
    (∫ z in A, F z) = ∫ z : ℂ, A.indicator F z :=
      (integral_indicator hAmeas).symm
    _ = ∫ p in Complex.polarCoord.target,
        p.1 • A.indicator F (Complex.polarCoord.symm p) := hpolar.symm
    _ = ∫ p in Complex.polarCoord.target, B.indicator H p := by
      refine setIntegral_congr_fun
        Complex.polarCoord.open_target.measurableSet ?_
      intro p hp
      have hp' : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := by
        simpa [Complex.polarCoord_target] using hp
      have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hp'.1]
      by_cases hpB : p ∈ B
      · have hpA : Complex.polarCoord.symm p ∈ A := by
          change a < ‖Complex.polarCoord.symm p‖
          rw [hnorm]
          exact hpB.1
        change p.1 • A.indicator F (Complex.polarCoord.symm p) =
          B.indicator H p
        rw [Set.indicator_of_mem hpA, Set.indicator_of_mem hpB]
      · have hpA : Complex.polarCoord.symm p ∉ A := by
          intro hpA
          apply hpB
          refine ⟨?_, trivial⟩
          change a < ‖Complex.polarCoord.symm p‖ at hpA
          rwa [hnorm] at hpA
        change p.1 • A.indicator F (Complex.polarCoord.symm p) =
          B.indicator H p
        rw [Set.indicator_of_notMem hpA, Set.indicator_of_notMem hpB,
          smul_zero]
    _ = ∫ p in Complex.polarCoord.target ∩ B, H p := by
      rw [setIntegral_indicator hBmeas]
    _ = ∫ p in Ioi a ×ˢ Ioo (-Real.pi) Real.pi, H p := by
      have hset : Complex.polarCoord.target ∩ B =
          Ioi a ×ˢ Ioo (-Real.pi) Real.pi := by
        ext p
        simp only [Complex.polarCoord_target, B, mem_inter_iff, mem_prod,
          mem_Ioi, mem_Ioo, mem_univ, and_true]
        constructor
        · rintro ⟨⟨hp0, hpθ⟩, hpr⟩
          exact ⟨hpr, hpθ⟩
        · rintro ⟨hpr, hpθ⟩
          exact ⟨⟨ha.trans hpr, hpθ⟩, hpr⟩
      rw [hset]
    _ = _ := rfl

/--
%%handwave
name:
  Integral of the planar inverse-cube tail
statement:
  For every $a>0$,
  $$
    \int_{|z|>a}\frac{dz}{|z|^3}=\frac{2\pi}{a}.
  $$
proof:
  Polar coordinates reduce the integral to
  $2\pi\int_a^\infty r^{-2}\,dr=2\pi/a$.
-/
theorem setIntegral_norm_inv_cube_exterior
    (a : ℝ) (ha : 0 < a) :
    (∫ z in {z : ℂ | a < ‖z‖}, ‖z‖⁻¹ ^ (3 : ℕ)) =
      2 * Real.pi / a := by
  rw [setIntegral_exterior_eq_polar _ ha, Measure.volume_eq_prod]
  calc
    (∫ p in Ioi a ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • ‖Complex.polarCoord.symm p‖⁻¹ ^ (3 : ℕ)) =
      ∫ p in Ioi a ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 ^ (-2 : ℝ) * (1 : ℝ) := by
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      have hr : 0 < p.1 := ha.trans hp.1
      change p.1 * ‖Complex.polarCoord.symm p‖⁻¹ ^ (3 : ℕ) =
        p.1 ^ (-2 : ℝ) * 1
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
      rw [Real.rpow_neg hr.le]
      norm_num [Real.rpow_two]
      field_simp
    _ = (∫ r in Ioi a, r ^ (-2 : ℝ)) *
        ∫ _θ in Ioo (-Real.pi) Real.pi, (1 : ℝ) :=
      MeasureTheory.setIntegral_prod_mul
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun r : ℝ ↦ r ^ (-2 : ℝ)) (fun _θ : ℝ ↦ (1 : ℝ))
        (Ioi a) (Ioo (-Real.pi) Real.pi)
    _ = 2 * Real.pi / a := by
      have hradial := integral_Ioi_rpow_of_lt
        (a := (-2 : ℝ)) (by norm_num) ha
      have hradial' :
          (∫ r in Ioi a, r ^ (-2 : ℝ)) = a⁻¹ := by
        rw [hradial]
        norm_num
        rw [Real.rpow_neg_one]
      have hangle :
          (∫ _θ in Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
            2 * Real.pi := by
        simp [Real.pi_pos.le]
        ring
      rw [hradial', hangle]
      field_simp

/--
%%handwave
name:
  Integrability of the planar inverse-cube tail
statement:
  For every $a>0$, the function $z\mapsto|z|^{-3}$ is integrable on
  $\{z:|z|>a\}$.
proof:
  On $|z|>a$, compare $|z|^{-3}$ with a constant multiple of
  $(1+|z|)^{-3}$. The latter is integrable on the plane because its decay
  exponent $3$ exceeds the real dimension $2$.
-/
theorem integrableOn_norm_inv_cube_exterior (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun z : ℂ ↦ ‖z‖⁻¹ ^ (3 : ℕ))
      {z : ℂ | a < ‖z‖} volume := by
  have hJ : Integrable
      (fun z : ℂ ↦ (1 + ‖z‖) ^ (-3 : ℝ)) volume := by
    apply integrable_one_add_norm
    rw [Complex.finrank_real_complex]
    norm_num
  have hJ' : Integrable
      (fun z : ℂ ↦ (1 + ‖z‖)⁻¹ ^ (3 : ℕ)) volume := by
    refine hJ.congr (ae_of_all _ fun z ↦ ?_)
    change (1 + ‖z‖) ^ (-3 : ℝ) = (1 + ‖z‖)⁻¹ ^ (3 : ℕ)
    rw [Real.rpow_neg (by positivity)]
    norm_num [Real.rpow_natCast]
  have hdom : Integrable
      (fun z : ℂ ↦ (1 + a⁻¹) ^ (3 : ℕ) *
        ((1 + ‖z‖)⁻¹ ^ (3 : ℕ))) volume :=
    hJ'.const_mul _
  refine Integrable.mono' hdom.integrableOn ?_ ?_
  · exact ((continuous_norm.measurable).inv.pow_const 3).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem
      ((isOpen_lt continuous_const continuous_norm).measurableSet)] with z hz
    have hzpos : 0 < ‖z‖ := ha.trans hz
    have hinv : ‖z‖⁻¹ ≤ a⁻¹ :=
      (inv_le_inv₀ hzpos ha).2 hz.le
    have hone : ‖z‖⁻¹ ≤
        (1 + a⁻¹) * (1 + ‖z‖)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]
      calc
        ‖z‖⁻¹ * (1 + ‖z‖) = 1 + ‖z‖⁻¹ := by
          field_simp
          ring
        _ ≤ 1 + a⁻¹ := add_le_add le_rfl hinv
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg z)) hone 3]

/--
%%handwave
name:
  Integral of a translated planar inverse-cube tail
statement:
  For every $a>0$ and $c\in\mathbb C$,
  $$
    \int_{|z-c|>a}\frac{dz}{|z-c|^3}=\frac{2\pi}{a}.
  $$
proof:
  Translate the integration variable by $c$ and apply the centered
  inverse-cube tail formula.
-/
theorem setIntegral_norm_sub_inv_cube_exterior
    (a : ℝ) (ha : 0 < a) (c : ℂ) :
    (∫ z in {z : ℂ | a < ‖z - c‖}, ‖z - c‖⁻¹ ^ (3 : ℕ)) =
      2 * Real.pi / a := by
  let A : Set ℂ := {z : ℂ | a < ‖z - c‖}
  let F : ℂ → ℝ := fun z ↦ A.indicator
    (fun w ↦ ‖w - c‖⁻¹ ^ (3 : ℕ)) z
  have hAmeas : MeasurableSet A :=
    (isOpen_lt continuous_const
      (continuous_id.sub continuous_const).norm).measurableSet
  have hshift :=
    integral_add_right_eq_self (μ := (volume : Measure ℂ)) F c
  have hcenter : (∫ z : ℂ, F (z + c)) =
      ∫ z in {z : ℂ | a < ‖z‖}, ‖z‖⁻¹ ^ (3 : ℕ) := by
    rw [← integral_indicator
      ((isOpen_lt continuous_const continuous_norm).measurableSet)]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : a < ‖z‖ <;> simp [F, A, hz]
  rw [← integral_indicator hAmeas]
  change (∫ z : ℂ, F z) = _
  rw [← hshift, hcenter, setIntegral_norm_inv_cube_exterior a ha]

/--
%%handwave
name:
  Integrability of a translated planar inverse-cube tail
statement:
  For every $a>0$ and $c\in\mathbb C$, the function
  $z\mapsto|z-c|^{-3}$ is integrable on $\{z:|z-c|>a\}$.
proof:
  Translate the integrable centered inverse-cube tail by $c$; planar
  Lebesgue measure is translation invariant.
-/
theorem integrableOn_norm_sub_inv_cube_exterior
    (a : ℝ) (ha : 0 < a) (c : ℂ) :
    IntegrableOn (fun z : ℂ ↦ ‖z - c‖⁻¹ ^ (3 : ℕ))
      {z : ℂ | a < ‖z - c‖} volume := by
  let A : Set ℂ := {z : ℂ | a < ‖z‖}
  let f : ℂ → ℝ := fun z ↦ ‖z‖⁻¹ ^ (3 : ℕ)
  have hAmeas : MeasurableSet A :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hcenter : Integrable (A.indicator f) volume :=
    (integrableOn_norm_inv_cube_exterior a ha).integrable_indicator hAmeas
  have hshift : Integrable (fun z : ℂ ↦ A.indicator f (-c + z)) volume :=
    hcenter.comp_add_left (-c)
  let B : Set ℂ := {z : ℂ | a < ‖z - c‖}
  have hBmeas : MeasurableSet B :=
    (isOpen_lt continuous_const
      (continuous_id.sub continuous_const).norm).measurableSet
  have hshift' : Integrable (B.indicator
      (fun z : ℂ ↦ ‖z - c‖⁻¹ ^ (3 : ℕ))) volume := by
    simpa [A, B, f, sub_eq_add_neg, add_comm] using hshift
  exact hshift'.integrableOn.congr_fun
    (fun z hz ↦ by simp [B, hz]) hBmeas

/--
%%handwave
name:
  Integrability of the planar inverse-fourth-power tail
statement:
  For every $a>0$, the function $z\mapsto|z|^{-4}$ is integrable on
  $\{z:|z|>a\}$.
proof:
  On $|z|>a$, one has $|z|^{-4}\leq a^{-1}|z|^{-3}$. Apply the
  integrability of the inverse-cube tail.
-/
theorem integrableOn_norm_inv_four_exterior (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun z : ℂ ↦ ‖z‖⁻¹ ^ (4 : ℕ))
      {z : ℂ | a < ‖z‖} volume := by
  let A : Set ℂ := {z : ℂ | a < ‖z‖}
  have hdom : IntegrableOn
      (fun z : ℂ ↦ a⁻¹ * (‖z‖⁻¹ ^ (3 : ℕ))) A volume :=
    (integrableOn_norm_inv_cube_exterior a ha).const_mul a⁻¹
  apply Integrable.mono' hdom
    ((continuous_norm.measurable.inv.pow_const 4).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem
      ((isOpen_lt continuous_const continuous_norm).measurableSet)] with z hz
  have hzpos : 0 < ‖z‖ := ha.trans hz
  have hinv : ‖z‖⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hzpos ha).2 hz.le
  have hraw :
      ‖z‖⁻¹ ^ (4 : ℕ) ≤ a⁻¹ * (‖z‖⁻¹ ^ (3 : ℕ)) := by
    calc
      ‖z‖⁻¹ ^ (4 : ℕ) = ‖z‖⁻¹ * (‖z‖⁻¹ ^ (3 : ℕ)) := by ring
      _ ≤ a⁻¹ * (‖z‖⁻¹ ^ (3 : ℕ)) := by gcongr
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (norm_nonneg z)) 4),
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr ha.le)
      (pow_nonneg (inv_nonneg.mpr (norm_nonneg z)) 3))] using hraw

/--
%%handwave
name:
  Bound for the planar inverse-fourth-power tail
statement:
  For every $a>0$,
  $$
    \int_{|z|>a}|z|^{-4}\,dz\leq\frac{2\pi}{a^2}.
  $$
proof:
  Use $|z|^{-4}\leq a^{-1}|z|^{-3}$ on the exterior and the exact
  inverse-cube integral $\int_{|z|>a}|z|^{-3}\,dz=2\pi/a$.
-/
theorem setIntegral_norm_inv_four_exterior_le (a : ℝ) (ha : 0 < a) :
    (∫ z in {z : ℂ | a < ‖z‖}, ‖z‖⁻¹ ^ (4 : ℕ)) ≤
      2 * Real.pi / a ^ 2 := by
  let A : Set ℂ := {z : ℂ | a < ‖z‖}
  have hfour := integrableOn_norm_inv_four_exterior a ha
  have hdom : IntegrableOn
      (fun z : ℂ ↦ a⁻¹ * (‖z‖⁻¹ ^ (3 : ℕ))) A volume :=
    (integrableOn_norm_inv_cube_exterior a ha).const_mul a⁻¹
  calc
    (∫ z in A, ‖z‖⁻¹ ^ (4 : ℕ)) ≤
        ∫ z in A, a⁻¹ * (‖z‖⁻¹ ^ (3 : ℕ)) := by
      apply integral_mono_ae hfour hdom
      filter_upwards [ae_restrict_mem
          ((isOpen_lt continuous_const continuous_norm).measurableSet)] with z hz
      have hzpos : 0 < ‖z‖ := ha.trans hz
      have hinv : ‖z‖⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hzpos ha).2 hz.le
      calc
        ‖z‖⁻¹ ^ (4 : ℕ) = ‖z‖⁻¹ * (‖z‖⁻¹ ^ (3 : ℕ)) := by ring
        _ ≤ a⁻¹ * (‖z‖⁻¹ ^ (3 : ℕ)) := by gcongr
    _ = a⁻¹ * (2 * Real.pi / a) := by
      rw [integral_const_mul, setIntegral_norm_inv_cube_exterior a ha]
    _ = 2 * Real.pi / a ^ 2 := by field_simp

/--
%%handwave
name:
  Integrability of a translated inverse-fourth-power tail
statement:
  For every $a>0$ and $c\in\mathbb C$, the function
  $z\mapsto|z-c|^{-4}$ is integrable on $\{z:|z-c|>a\}$.
proof:
  Translate the integrable centered inverse-fourth-power tail by $c$.
-/
theorem integrableOn_norm_sub_inv_four_exterior
    (a : ℝ) (ha : 0 < a) (c : ℂ) :
    IntegrableOn (fun z : ℂ ↦ ‖z - c‖⁻¹ ^ (4 : ℕ))
      {z : ℂ | a < ‖z - c‖} volume := by
  let A : Set ℂ := {z : ℂ | a < ‖z‖}
  let f : ℂ → ℝ := fun z ↦ ‖z‖⁻¹ ^ (4 : ℕ)
  have hAmeas : MeasurableSet A :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hcenter : Integrable (A.indicator f) volume :=
    (integrableOn_norm_inv_four_exterior a ha).integrable_indicator hAmeas
  have hshift : Integrable (fun z : ℂ ↦ A.indicator f (-c + z)) volume :=
    hcenter.comp_add_left (-c)
  let B : Set ℂ := {z : ℂ | a < ‖z - c‖}
  have hBmeas : MeasurableSet B :=
    (isOpen_lt continuous_const
      (continuous_id.sub continuous_const).norm).measurableSet
  have hshift' : Integrable (B.indicator
      (fun z : ℂ ↦ ‖z - c‖⁻¹ ^ (4 : ℕ))) volume := by
    simpa [A, B, f, sub_eq_add_neg, add_comm] using hshift
  exact hshift'.integrableOn.congr_fun
    (fun z hz ↦ by simp [B, hz]) hBmeas

/--
%%handwave
name:
  Bound for a translated inverse-fourth-power tail
statement:
  For every $a>0$ and $c\in\mathbb C$,
  $$
    \int_{|z-c|>a}|z-c|^{-4}\,dz\leq\frac{2\pi}{a^2}.
  $$
proof:
  Translate the domain and integrand to the origin and apply the centered
  inverse-fourth-power bound.
-/
theorem setIntegral_norm_sub_inv_four_exterior_le
    (a : ℝ) (ha : 0 < a) (c : ℂ) :
    (∫ z in {z : ℂ | a < ‖z - c‖}, ‖z - c‖⁻¹ ^ (4 : ℕ)) ≤
      2 * Real.pi / a ^ 2 := by
  let A : Set ℂ := {z : ℂ | a < ‖z - c‖}
  let F : ℂ → ℝ := fun z ↦ A.indicator
    (fun w ↦ ‖w - c‖⁻¹ ^ (4 : ℕ)) z
  have hAmeas : MeasurableSet A :=
    (isOpen_lt continuous_const
      (continuous_id.sub continuous_const).norm).measurableSet
  have hshift := integral_add_right_eq_self (μ := (volume : Measure ℂ)) F c
  have hcenter : (∫ z : ℂ, F (z + c)) =
      ∫ z in {z : ℂ | a < ‖z‖}, ‖z‖⁻¹ ^ (4 : ℕ) := by
    rw [← integral_indicator
      ((isOpen_lt continuous_const continuous_norm).measurableSet)]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : a < ‖z‖ <;> simp [F, A, hz]
  rw [← integral_indicator hAmeas]
  change (∫ z : ℂ, F z) ≤ _
  rw [← hshift, hcenter]
  exact setIntegral_norm_inv_four_exterior_le a ha

end

end HarmonicAnalysis

end JJMath
