import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import JJMath.Quasiconformal.BeurlingWeakExtension

/-!
# Interpolation estimates for the Beurling transform

This file develops the high/low truncation estimate that combines the weak
$(1,1)$ Beurling transform with its exact $L^2$ isometry. It is the analytic
core of the strong $L^p$ construction for $1<p<2$.
-/

namespace JJMath

open MeasureTheory Filter
open scoped ENNReal

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  A bounded part of an integrable function is square integrable
statement:
  Let $f:X\to E$ be integrable and strongly measurable, and let
  $0\leq u<\infty$. Then
  $$
    1_{\{\|f\|\leq u\}}f\in L^2(X).
  $$
proof:
  On the indicated set, $\|f\|^2\leq u\|f\|$. The right-hand side is
  integrable because $f\in L^1$.
-/
theorem memLp_two_indicator_compl_enorm_gt
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (f : α → E) (μ : Measure α) (hf : Integrable f μ)
    (hfm : StronglyMeasurable f) {u : ENNReal} (hu : u ≠ ∞) :
    MemLp ({x | u < ‖f x‖ₑ}ᶜ.indicator f) 2 μ := by
  let A : Set α := {x | u < ‖f x‖ₑ}
  have hA : MeasurableSet A := by
    exact measurableSet_lt measurable_const hfm.enorm
  have hlo_meas : AEStronglyMeasurable (Aᶜ.indicator f) μ :=
    hfm.aestronglyMeasurable.indicator hA.compl
  apply (integrable_norm_rpow_iff hlo_meas (by norm_num) (by norm_num)).1
  simp only [ENNReal.toReal_ofNat]
  apply Integrable.mono'
      (hf.norm.const_mul u.toReal)
      ((hlo_meas.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
  filter_upwards with x
  by_cases hx : x ∈ Aᶜ
  · rw [Set.indicator_of_mem hx]
    have hbound_enorm : ‖f x‖ₑ ≤ u := by
      simpa only [A, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] using hx
    have hbound : ‖f x‖ ≤ u.toReal := by
      rw [← toReal_enorm]
      exact ENNReal.toReal_mono hu hbound_enorm
    rw [Real.rpow_two]
    change |‖f x‖ ^ 2| ≤ u.toReal * ‖f x‖
    calc
      |‖f x‖ ^ 2| = ‖f x‖ ^ 2 := abs_of_nonneg (sq_nonneg ‖f x‖)
      _ = ‖f x‖ * ‖f x‖ := pow_two ‖f x‖
      _ ≤ u.toReal * ‖f x‖ :=
        mul_le_mul_of_nonneg_right hbound (norm_nonneg (f x))
  · rw [Set.indicator_of_notMem hx, norm_zero]
    norm_num
    exact mul_nonneg ENNReal.toReal_nonneg (norm_nonneg (f x))

/--
%%handwave
name:
  Squared $L^2$ seminorm as an integral
statement:
  For every function $f:X\to E$,
  $$
    \|f\|_{L^2}^2=\int_X\|f(x)\|^2\,d\mu(x)
  $$
  as an identity in $[0,\infty]$.
proof:
  This is the integral definition of the extended $L^2$ seminorm, with the
  outer square root cancelled by squaring.
-/
theorem eLpNorm_two_sq_eq_lintegral_enorm_sq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (f : α → E) (μ : Measure α) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  simpa only [NNReal.coe_ofNat, ENNReal.rpow_two] using
    (eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f)
      (p := (2 : NNReal)) (by norm_num))

/--
%%handwave
name:
  Normalized power tail integral
statement:
  If $r>0$ and $p<2$, then
  $$
    (2-p)r^2\int_r^\infty t^{p-3}\,dt=r^p.
  $$
  The equality is interpreted as an equality of nonnegative extended
  integrals.
proof:
  Since $p-3<-1$, the improper power integral converges and equals
  $-r^{p-2}/(p-2)$. Multiplication by $(2-p)r^2$ gives $r^p$.
-/
theorem lintegral_Ioi_ofReal_two_sub_mul_rpow_mul_sq
    {p r : ℝ} (hp2 : p < 2) (hr : 0 < r) :
    (∫⁻ t in Set.Ioi r,
      ENNReal.ofReal ((2 - p) * t ^ (p - 3) * r ^ 2)) =
        ENNReal.ofReal (r ^ p) := by
  have hexp : p - 3 < -1 := by linarith
  have hbase : IntegrableOn (fun t : ℝ ↦ t ^ (p - 3)) (Set.Ioi r) :=
    integrableOn_Ioi_rpow_of_lt hexp hr
  have hint : IntegrableOn
      (fun t : ℝ ↦ (2 - p) * t ^ (p - 3) * r ^ 2) (Set.Ioi r) :=
    (hbase.const_mul (2 - p)).mul_const (r ^ 2)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi r)]
      (fun t : ℝ ↦ (2 - p) * t ^ (p - 3) * r ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hp2.le)
        (Real.rpow_nonneg (hr.trans ht).le (p - 3)))
      (sq_nonneg r)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [integral_mul_const, integral_const_mul,
    integral_Ioi_rpow_of_lt hexp hr]
  apply congrArg ENNReal.ofReal
  have hpne : p - 2 ≠ 0 := by linarith
  rw [show p - 3 + 1 = p - 2 by ring]
  calc
    (2 - p) * (-r ^ (p - 2) / (p - 2)) * r ^ 2 =
        r ^ (p - 2) * r ^ 2 := by
      field_simp
      ring
    _ = r ^ ((p - 2) + 2) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_add hr (p - 2) 2).symm
    _ = r ^ p := by ring_nf

/--
%%handwave
name:
  Integrated lower-tail identity
statement:
  Let $f:X\to E$ be strongly measurable on a $\sigma$-finite measure space,
  let $0<p<2$, and put
  $L_f(t)=\int_{\{|f|\leq t\}}|f|^2\,d\mu$. Then
  $$
    \int_0^\infty (2-p)t^{p-3}L_f(t)\,dt
      =\int_X|f|^p\,d\mu.
  $$
proof:
  Tonelli's theorem exchanges the threshold and space integrals. For a fixed
  value $r=|f(x)|>0$, the remaining threshold integral is the normalized
  power-tail integral
  $(2-p)r^2\int_r^\infty t^{p-3}\,dt=r^p$; the case $r=0$ is immediate.
-/
theorem lintegral_two_sub_mul_lower_tail_eq_lintegral_rpow
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (f : α → E) (μ : Measure α) [SFinite μ] (hf : StronglyMeasurable f)
    {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) :
    (∫⁻ t in Set.Ioi (0 : ℝ),
      ∫⁻ x in {x | ‖f x‖ ≤ t},
        ENNReal.ofReal ((2 - p) * t ^ (p - 3)) * ‖f x‖ₑ ^ 2 ∂μ) =
      ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let w : ℝ → ENNReal := fun t ↦
    ENNReal.ofReal ((2 - p) * t ^ (p - 3))
  let G : ℝ → α → ENNReal := fun t x ↦
    {y | ‖f y‖ ≤ t}.indicator (fun y ↦ w t * ‖f y‖ₑ ^ 2) x
  have hw_real : ContinuousOn
      (fun t : ℝ ↦ (2 - p) * t ^ (p - 3)) (Set.Ioi 0) := by
    exact continuousOn_const.mul
      (continuousOn_id.rpow_const fun t ht ↦ Or.inl ht.ne')
  have hw : AEMeasurable w ν := by
    exact (hw_real.aestronglyMeasurable measurableSet_Ioi).aemeasurable.ennreal_ofReal
  have hs : MeasurableSet {q : ℝ × α | ‖f q.2‖ ≤ q.1} := by
    exact measurableSet_le (hf.norm.measurable.comp measurable_snd) measurable_fst
  have hG : AEMeasurable (Function.uncurry G) (ν.prod μ) := by
    have hw_fst : AEMeasurable (fun q : ℝ × α ↦ w q.1) (ν.prod μ) :=
      hw.comp_fst
    have hnorm_snd : AEMeasurable
        (fun q : ℝ × α ↦ ‖f q.2‖ₑ ^ 2) (ν.prod μ) :=
      ((hf.enorm.pow_const 2).comp measurable_snd).aemeasurable
    exact (hw_fst.mul hnorm_snd).indicator₀ hs.nullMeasurableSet
  have hswap :
      (∫⁻ t, ∫⁻ x, G t x ∂μ ∂ν) =
        ∫⁻ x, ∫⁻ t, G t x ∂ν ∂μ :=
    lintegral_lintegral_swap hG
  have hleft :
      (∫⁻ t in Set.Ioi (0 : ℝ),
        ∫⁻ x in {x | ‖f x‖ ≤ t},
          ENNReal.ofReal ((2 - p) * t ^ (p - 3)) * ‖f x‖ₑ ^ 2 ∂μ) =
        ∫⁻ t, ∫⁻ x, G t x ∂μ ∂ν := by
    change (∫⁻ t, ∫⁻ x in {x | ‖f x‖ ≤ t},
      w t * ‖f x‖ₑ ^ 2 ∂μ ∂ν) = _
    apply lintegral_congr
    intro t
    exact (lintegral_indicator
      (μ := μ) (f := fun x ↦ w t * ‖f x‖ₑ ^ 2)
      (measurableSet_le hf.norm.measurable measurable_const)).symm
  have hinner : ∀ x,
      (∫⁻ t, G t x ∂ν) = ‖f x‖ₑ ^ p := by
    intro x
    let r : ℝ := ‖f x‖
    by_cases hr0 : r = 0
    · have hfx : f x = 0 := norm_eq_zero.mp hr0
      have hGzero : (fun t ↦ G t x) = 0 := by
        funext t
        by_cases ht : 0 ≤ t <;> simp [G, hfx, ht]
      rw [hGzero, lintegral_zero_fun]
      simp [hfx, ENNReal.zero_rpow_of_pos hp0]
    · have hr : 0 < r := lt_of_le_of_ne (norm_nonneg (f x)) (Ne.symm hr0)
      calc
        (∫⁻ t, G t x ∂ν) =
            ∫⁻ t in Set.Ioi r,
              ENNReal.ofReal ((2 - p) * t ^ (p - 3) * r ^ 2) := by
          change (∫⁻ t,
            (Set.Ici r).indicator (fun t ↦ w t * ‖f x‖ₑ ^ 2) t ∂ν) = _
          rw [lintegral_indicator measurableSet_Ici]
          rw [show ν.restrict (Set.Ici r) =
              volume.restrict (Set.Ici r) by
            simpa only [ν] using
              (Measure.restrict_restrict_of_subset
                (μ := volume) (s := Set.Ici r) (t := Set.Ioi (0 : ℝ))
                (fun t ht ↦ hr.trans_le ht))]
          rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici]
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have hweight : 0 ≤ (2 - p) * t ^ (p - 3) :=
            mul_nonneg (sub_nonneg.mpr hp2.le)
              (Real.rpow_nonneg (hr.trans ht).le (p - 3))
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg (f x)) 2,
            ← ENNReal.ofReal_mul hweight]
        _ = ENNReal.ofReal (r ^ p) :=
          lintegral_Ioi_ofReal_two_sub_mul_rpow_mul_sq hp2 hr
        _ = ‖f x‖ₑ ^ p := by
          rw [← ofReal_norm,
            ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) hp0.le]
  rw [hleft, hswap]
  exact lintegral_congr hinner

/--
%%handwave
name:
  Normalized power head integral
statement:
  If $r>0$ and $p>1$, then
  $$
    (p-1)r\int_0^r t^{p-2}\,dt=r^p.
  $$
  The equality is interpreted as an equality of nonnegative extended
  integrals.
proof:
  Since $p-2>-1$, the power is integrable at zero and its integral is
  $r^{p-1}/(p-1)$. Multiplication by $(p-1)r$ gives $r^p$.
-/
theorem lintegral_Ioo_ofReal_sub_one_mul_rpow_mul
    {p r : ℝ} (hp1 : 1 < p) (hr : 0 < r) :
    (∫⁻ t in Set.Ioo (0 : ℝ) r,
      ENNReal.ofReal ((p - 1) * t ^ (p - 2) * r)) =
        ENNReal.ofReal (r ^ p) := by
  have hexp : -1 < p - 2 := by linarith
  have hbase : IntegrableOn (fun t : ℝ ↦ t ^ (p - 2)) (Set.Ioo 0 r) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hr).2 hexp
  have hint : IntegrableOn
      (fun t : ℝ ↦ (p - 1) * t ^ (p - 2) * r) (Set.Ioo 0 r) :=
    (hbase.const_mul (p - 1)).mul_const r
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) r)]
      (fun t : ℝ ↦ (p - 1) * t ^ (p - 2) * r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hp1.le)
        (Real.rpow_nonneg ht.1.le (p - 2))) hr.le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [integral_mul_const, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hr.le,
    integral_rpow (Or.inl hexp)]
  apply congrArg ENNReal.ofReal
  have hpne : p - 1 ≠ 0 := by linarith
  rw [show p - 2 + 1 = p - 1 by ring,
    Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  calc
    (p - 1) * ((r ^ (p - 1) - 0) / (p - 1)) * r =
        r ^ (p - 1) * r := by
      field_simp
      simp
    _ = r ^ ((p - 1) + 1) := by
      conv_lhs => rhs; rw [← Real.rpow_one r]
      exact (Real.rpow_add hr (p - 1) 1).symm
    _ = r ^ p := by ring_nf

/--
%%handwave
name:
  Integrated upper-tail identity
statement:
  Let $f:X\to E$ be strongly measurable on a $\sigma$-finite measure space,
  let $p>1$, and put
  $H_f(t)=\int_{\{|f|>t\}}|f|\,d\mu$. Then
  $$
    \int_0^\infty (p-1)t^{p-2}H_f(t)\,dt
      =\int_X|f|^p\,d\mu.
  $$
proof:
  Tonelli's theorem exchanges the threshold and space integrals. For a fixed
  value $r=|f(x)|>0$, the remaining threshold integral is
  $(p-1)r\int_0^r t^{p-2}\,dt=r^p$; the case $r=0$ is immediate.
-/
theorem lintegral_sub_one_mul_upper_tail_eq_lintegral_rpow
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (f : α → E) (μ : Measure α) [SFinite μ] (hf : StronglyMeasurable f)
    {p : ℝ} (hp1 : 1 < p) :
    (∫⁻ t in Set.Ioi (0 : ℝ),
      ∫⁻ x in {x | t < ‖f x‖},
        ENNReal.ofReal ((p - 1) * t ^ (p - 2)) * ‖f x‖ₑ ∂μ) =
      ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let w : ℝ → ENNReal := fun t ↦
    ENNReal.ofReal ((p - 1) * t ^ (p - 2))
  let G : ℝ → α → ENNReal := fun t x ↦
    {y | t < ‖f y‖}.indicator (fun y ↦ w t * ‖f y‖ₑ) x
  have hw_real : ContinuousOn
      (fun t : ℝ ↦ (p - 1) * t ^ (p - 2)) (Set.Ioi 0) := by
    exact continuousOn_const.mul
      (continuousOn_id.rpow_const fun t ht ↦ Or.inl ht.ne')
  have hw : AEMeasurable w ν := by
    exact (hw_real.aestronglyMeasurable measurableSet_Ioi).aemeasurable.ennreal_ofReal
  have hs : MeasurableSet {q : ℝ × α | q.1 < ‖f q.2‖} := by
    exact measurableSet_lt measurable_fst (hf.norm.measurable.comp measurable_snd)
  have hG : AEMeasurable (Function.uncurry G) (ν.prod μ) := by
    have hw_fst : AEMeasurable (fun q : ℝ × α ↦ w q.1) (ν.prod μ) :=
      hw.comp_fst
    have hnorm_snd : AEMeasurable
        (fun q : ℝ × α ↦ ‖f q.2‖ₑ) (ν.prod μ) :=
      (hf.enorm.comp measurable_snd).aemeasurable
    exact (hw_fst.mul hnorm_snd).indicator₀ hs.nullMeasurableSet
  have hswap :
      (∫⁻ t, ∫⁻ x, G t x ∂μ ∂ν) =
        ∫⁻ x, ∫⁻ t, G t x ∂ν ∂μ :=
    lintegral_lintegral_swap hG
  have hleft :
      (∫⁻ t in Set.Ioi (0 : ℝ),
        ∫⁻ x in {x | t < ‖f x‖},
          ENNReal.ofReal ((p - 1) * t ^ (p - 2)) * ‖f x‖ₑ ∂μ) =
        ∫⁻ t, ∫⁻ x, G t x ∂μ ∂ν := by
    change (∫⁻ t, ∫⁻ x in {x | t < ‖f x‖},
      w t * ‖f x‖ₑ ∂μ ∂ν) = _
    apply lintegral_congr
    intro t
    exact (lintegral_indicator
      (μ := μ) (f := fun x ↦ w t * ‖f x‖ₑ)
      (measurableSet_lt measurable_const hf.norm.measurable)).symm
  have hinner : ∀ x,
      (∫⁻ t, G t x ∂ν) = ‖f x‖ₑ ^ p := by
    intro x
    let r : ℝ := ‖f x‖
    by_cases hr0 : r = 0
    · have hfx : f x = 0 := norm_eq_zero.mp hr0
      have hGzero : (fun t ↦ G t x) = 0 := by
        funext t
        simp [G, hfx]
      rw [hGzero, lintegral_zero_fun]
      simp [hfx, ENNReal.zero_rpow_of_pos (lt_trans zero_lt_one hp1)]
    · have hr : 0 < r := lt_of_le_of_ne (norm_nonneg (f x)) (Ne.symm hr0)
      calc
        (∫⁻ t, G t x ∂ν) =
            ∫⁻ t in Set.Ioo (0 : ℝ) r,
              ENNReal.ofReal ((p - 1) * t ^ (p - 2) * r) := by
          change (∫⁻ t,
            (Set.Iio r).indicator (fun t ↦ w t * ‖f x‖ₑ) t ∂ν) = _
          rw [lintegral_indicator measurableSet_Iio]
          rw [show ν.restrict (Set.Iio r) =
              volume.restrict (Set.Ioo (0 : ℝ) r) by
            dsimp only [ν]
            rw [Measure.restrict_restrict measurableSet_Iio]
            congr 1
            ext t
            simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi,
              Set.mem_Ioo]
            tauto]
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          have hweight : 0 ≤ (p - 1) * t ^ (p - 2) :=
            mul_nonneg (sub_nonneg.mpr hp1.le)
              (Real.rpow_nonneg ht.1.le (p - 2))
          rw [← ofReal_norm, ← ENNReal.ofReal_mul hweight]
        _ = ENNReal.ofReal (r ^ p) :=
          lintegral_Ioo_ofReal_sub_one_mul_rpow_mul hp1 hr
        _ = ‖f x‖ₑ ^ p := by
          rw [← ofReal_norm,
            ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x))
              (lt_trans zero_lt_one hp1).le]
  rw [hleft, hswap]
  exact lintegral_congr hinner

/--
%%handwave
name:
  Weighted upper-tail integral
statement:
  Under the hypotheses of the integrated upper-tail identity, if $p>1$ then
  $$
    \int_0^\infty t^{p-2}
      \left(\int_{\{|f|>t\}}|f|\,d\mu\right)dt
      =\frac1{p-1}\int_X|f|^p\,d\mu.
  $$
proof:
  Factor the positive constant $p-1$ out of the normalized upper-tail
  identity and cancel it in $[0,\infty]$.
-/
theorem lintegral_upper_tail_mul_rpow_eq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (f : α → E) (μ : Measure α) [SFinite μ] (hf : StronglyMeasurable f)
    {p : ℝ} (hp1 : 1 < p) :
    (∫⁻ t in Set.Ioi (0 : ℝ),
      (∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ∂μ) *
        ENNReal.ofReal (t ^ (p - 2))) =
      (ENNReal.ofReal (p - 1))⁻¹ * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  let q : ENNReal := ENNReal.ofReal (p - 1)
  let R : ENNReal := ∫⁻ t in Set.Ioi (0 : ℝ),
    (∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ∂μ) *
      ENNReal.ofReal (t ^ (p - 2))
  have hfactor :
      (∫⁻ t in Set.Ioi (0 : ℝ),
        ∫⁻ x in {x | t < ‖f x‖},
          ENNReal.ofReal ((p - 1) * t ^ (p - 2)) * ‖f x‖ₑ ∂μ) =
        q * R := by
    simp_rw [ENNReal.ofReal_mul (sub_nonneg.mpr hp1.le)]
    change (∫⁻ t in Set.Ioi (0 : ℝ),
      ∫⁻ x in {x | t < ‖f x‖},
        q * ENNReal.ofReal (t ^ (p - 2)) * ‖f x‖ₑ ∂μ) = q * R
    calc
      _ = ∫⁻ t in Set.Ioi (0 : ℝ), q *
          ((∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ∂μ) *
            ENNReal.ofReal (t ^ (p - 2))) := by
        apply lintegral_congr
        intro t
        simp only [mul_assoc]
        rw [lintegral_const_mul' q _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' (ENNReal.ofReal (t ^ (p - 2)))
            (fun x ↦ ‖f x‖ₑ) ENNReal.ofReal_ne_top]
        ac_rfl
      _ = q * R := by
        rw [lintegral_const_mul' q _ ENNReal.ofReal_ne_top]
  have hnorm := lintegral_sub_one_mul_upper_tail_eq_lintegral_rpow
    f μ hf hp1
  have hq0 : q ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hp1)
  have hqtop : q ≠ ∞ := ENNReal.ofReal_ne_top
  change R = q⁻¹ * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ
  rw [← hnorm, hfactor, ← mul_assoc,
    ENNReal.inv_mul_cancel hq0 hqtop, one_mul]

/--
%%handwave
name:
  Weighted lower-tail integral
statement:
  Under the hypotheses of the integrated lower-tail identity, if $0<p<2$
  then
  $$
    \int_0^\infty t^{p-3}
      \left(\int_{\{|f|\leq t\}}|f|^2\,d\mu\right)dt
      =\frac1{2-p}\int_X|f|^p\,d\mu.
  $$
proof:
  Factor the positive constant $2-p$ out of the normalized lower-tail
  identity and cancel it in $[0,\infty]$.
-/
theorem lintegral_lower_tail_mul_rpow_eq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (f : α → E) (μ : Measure α) [SFinite μ] (hf : StronglyMeasurable f)
    {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) :
    (∫⁻ t in Set.Ioi (0 : ℝ),
      (∫⁻ x in {x | ‖f x‖ ≤ t}, ‖f x‖ₑ ^ 2 ∂μ) *
        ENNReal.ofReal (t ^ (p - 3))) =
      (ENNReal.ofReal (2 - p))⁻¹ * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  let q : ENNReal := ENNReal.ofReal (2 - p)
  let R : ENNReal := ∫⁻ t in Set.Ioi (0 : ℝ),
    (∫⁻ x in {x | ‖f x‖ ≤ t}, ‖f x‖ₑ ^ 2 ∂μ) *
      ENNReal.ofReal (t ^ (p - 3))
  have hfactor :
      (∫⁻ t in Set.Ioi (0 : ℝ),
        ∫⁻ x in {x | ‖f x‖ ≤ t},
          ENNReal.ofReal ((2 - p) * t ^ (p - 3)) * ‖f x‖ₑ ^ 2 ∂μ) =
        q * R := by
    simp_rw [ENNReal.ofReal_mul (sub_nonneg.mpr hp2.le)]
    change (∫⁻ t in Set.Ioi (0 : ℝ),
      ∫⁻ x in {x | ‖f x‖ ≤ t},
        q * ENNReal.ofReal (t ^ (p - 3)) * ‖f x‖ₑ ^ 2 ∂μ) = q * R
    calc
      _ = ∫⁻ t in Set.Ioi (0 : ℝ), q *
          ((∫⁻ x in {x | ‖f x‖ ≤ t}, ‖f x‖ₑ ^ 2 ∂μ) *
            ENNReal.ofReal (t ^ (p - 3))) := by
        apply lintegral_congr
        intro t
        simp only [mul_assoc]
        rw [lintegral_const_mul' q _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' (ENNReal.ofReal (t ^ (p - 3)))
            (fun x ↦ ‖f x‖ₑ ^ 2) ENNReal.ofReal_ne_top]
        ac_rfl
      _ = q * R := by
        rw [lintegral_const_mul' q _ ENNReal.ofReal_ne_top]
  have hnorm := lintegral_two_sub_mul_lower_tail_eq_lintegral_rpow
    f μ hf hp0 hp2
  have hq0 : q ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hp2)
  have hqtop : q ≠ ∞ := ENNReal.ofReal_ne_top
  change R = q⁻¹ * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ
  rw [← hnorm, hfactor, ← mul_assoc,
    ENNReal.inv_mul_cancel hq0 hqtop, one_mul]

/--
%%handwave
name:
  High-low distribution estimate for the Beurling transform
statement:
  Let $F\in L^1(\mathbb C)$, let $0\leq u<\infty$, and let
  $0<t<\infty$. Put
  $$
    F_{>u}=1_{\{|F|>u\}}F,
    \qquad F_{\leq u}=1_{\{|F|\leq u\}}F.
  $$
  Then
  $$
  \begin{aligned}
    |\{|\mathcal SF|\geq t\}|
    \leq{}&
      \frac{(40+16\pi)\int_{\mathbb C}|F_{>u}(z)|\,dz}{t/2}\\
      &+\frac{\int_{\mathbb C}|F_{\leq u}(z)|^2\,dz}{(t/2)^2}.
  \end{aligned}
  $$
proof:
  Decompose $F=F_{>u}+F_{\leq u}$ and use the half-threshold distribution
  bound for a sum. Apply the weak $(1,1)$ estimate to the high part. The low
  part is in $L^2$; compatibility with the Fourier-multiplier transform,
  Chebyshev's inequality, and the $L^2$ isometry give its second term.
-/
theorem beurlingTransformL1_distribution_le_high_low
    (F : ℂ →₁[volume] ℂ) {u t : ENNReal}
    (hu : u ≠ ∞) (ht0 : t ≠ 0) (httop : t ≠ ∞) :
    let A : Set ℂ := {z | u < ‖(F : ℂ → ℂ) z‖ₑ}
    HarmonicAnalysis.distributionFunction
        (beurlingTransformL1 F : ℂ → ℂ) volume t ≤
      (ENNReal.ofReal (40 + 16 * Real.pi) *
          ∫⁻ z, ‖A.indicator (F : ℂ → ℂ) z‖ₑ ∂volume) / (t / 2) +
        (∫⁻ z, ‖Aᶜ.indicator (F : ℂ → ℂ) z‖ₑ ^ 2 ∂volume) /
          ((t / 2) ^ 2) := by
  dsimp only
  let f : ℂ → ℂ := (F : ℂ → ℂ)
  let A : Set ℂ := {z | u < ‖f z‖ₑ}
  let hi : ℂ → ℂ := A.indicator f
  let lo : ℂ → ℂ := Aᶜ.indicator f
  have hf_int : Integrable f volume := L1.integrable_coeFn F
  have hf_meas : StronglyMeasurable f := Lp.stronglyMeasurable F
  have hA : MeasurableSet A := by
    exact measurableSet_lt measurable_const hf_meas.enorm
  have hhi_int : Integrable hi volume := hf_int.indicator hA
  have hlo_int : Integrable lo volume := hf_int.indicator hA.compl
  let hhi₁ : MemLp hi 1 volume := memLp_one_iff_integrable.mpr hhi_int
  let hlo₁ : MemLp lo 1 volume := memLp_one_iff_integrable.mpr hlo_int
  let H : ℂ →₁[volume] ℂ := hhi₁.toLp hi
  let L : ℂ →₁[volume] ℂ := hlo₁.toLp lo
  have hHcoe : (H : ℂ → ℂ) =ᵐ[volume] hi := hhi₁.coeFn_toLp
  have hLcoe : (L : ℂ → ℂ) =ᵐ[volume] lo := hlo₁.coeFn_toLp
  have hsplit : F = H + L := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add H L, hHcoe, hLcoe] with z hadd hhi hlo
    rw [hadd]
    simp only [Pi.add_apply, hhi, hlo]
    exact (congrFun (Set.indicator_self_add_compl A f) z).symm
  have htransform_class :
      beurlingTransformL1 F =
        beurlingTransformL1 H + beurlingTransformL1 L := by
    rw [hsplit]
    exact beurlingTransformL1_add H L
  have htransform : (beurlingTransformL1 F : ℂ → ℂ) =ᵐ[volume]
      (beurlingTransformL1 H : ℂ → ℂ) +
        (beurlingTransformL1 L : ℂ → ℂ) := by
    rw [htransform_class]
    exact AEEqFun.coeFn_add _ _
  have hdist_split : HarmonicAnalysis.distributionFunction
      (beurlingTransformL1 F : ℂ → ℂ) volume t =
      HarmonicAnalysis.distributionFunction
        ((beurlingTransformL1 H : ℂ → ℂ) +
          (beurlingTransformL1 L : ℂ → ℂ)) volume t :=
    HarmonicAnalysis.distributionFunction_congr_ae htransform t
  let q : ENNReal := t / 2
  have hq0 : q ≠ 0 := by
    exact ENNReal.div_ne_zero.2 ⟨ht0, by norm_num⟩
  have hqtop : q ≠ ∞ := by
    exact ENNReal.div_ne_top httop (by norm_num)
  have hHmass : (∫⁻ z, ‖(H : ℂ → ℂ) z‖ₑ ∂volume) =
      ∫⁻ z, ‖hi z‖ₑ ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [hHcoe] with z hz
    rw [hz]
  have hhigh_mul : q * HarmonicAnalysis.distributionFunction
      (beurlingTransformL1 H : ℂ → ℂ) volume q ≤
      ENNReal.ofReal (40 + 16 * Real.pi) *
        ∫⁻ z, ‖hi z‖ₑ ∂volume := by
    simpa only [hHmass] using
      beurlingTransformL1_distribution_le H hq0 hqtop
  have hhigh : HarmonicAnalysis.distributionFunction
      (beurlingTransformL1 H : ℂ → ℂ) volume q ≤
      (ENNReal.ofReal (40 + 16 * Real.pi) *
        ∫⁻ z, ‖hi z‖ₑ ∂volume) / q := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hq0) (Or.inl hqtop)).2
    simpa only [mul_comm] using hhigh_mul
  have hlo₂ : MemLp lo 2 volume := by
    simpa only [lo, A, f] using
      memLp_two_indicator_compl_enorm_gt f volume hf_int hf_meas hu
  have hL₂ : MemLp (L : ℂ → ℂ) 2 volume := hlo₂.ae_eq hLcoe.symm
  let hL₁' : MemLp (L : ℂ → ℂ) 1 volume :=
    memLp_one_iff_integrable.mpr (L1.integrable_coeFn L)
  have hLclass : hL₁'.toLp (L : ℂ → ℂ) = L := by
    apply Lp.ext
    exact hL₁'.coeFn_toLp
  have hcompat : (beurlingTransformL1 L : ℂ → ℂ) =ᵐ[volume]
      (beurlingTransformL2 (hL₂.toLp (L : ℂ → ℂ)) : ℂ → ℂ) := by
    have h := beurlingTransformL1_ae_eq_beurlingTransformL2
      (L : ℂ → ℂ) (L1.integrable_coeFn L) hL₂
    dsimp only at h
    rw [hLclass] at h
    exact h
  let L₂ : PlaneL2 := hL₂.toLp (L : ℂ → ℂ)
  have hlow_dist : HarmonicAnalysis.distributionFunction
      (beurlingTransformL1 L : ℂ → ℂ) volume q =
      HarmonicAnalysis.distributionFunction
        (beurlingTransformL2 L₂ : ℂ → ℂ) volume q := by
    exact HarmonicAnalysis.distributionFunction_congr_ae hcompat q
  have hlow_norm : eLpNorm (beurlingTransformL2 L₂ : ℂ → ℂ) 2 volume =
      eLpNorm lo 2 volume := by
    calc
      eLpNorm (beurlingTransformL2 L₂ : ℂ → ℂ) 2 volume =
          eLpNorm (L₂ : ℂ → ℂ) 2 volume :=
        eLpNorm_two_beurlingTransformL2_apply L₂
      _ = eLpNorm (L : ℂ → ℂ) 2 volume :=
        eLpNorm_congr_ae hL₂.coeFn_toLp
      _ = eLpNorm lo 2 volume := eLpNorm_congr_ae hLcoe
  have hlow_mul : q ^ 2 * HarmonicAnalysis.distributionFunction
      (beurlingTransformL2 L₂ : ℂ → ℂ) volume q ≤
      eLpNorm lo 2 volume ^ 2 := by
    rw [← hlow_norm]
    simpa only [HarmonicAnalysis.distributionFunction,
      ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      (mul_meas_ge_le_pow_eLpNorm' volume
        (p := (2 : ENNReal)) (by norm_num) (by norm_num)
        (Lp.aestronglyMeasurable (beurlingTransformL2 L₂)) q)
  have hlow : HarmonicAnalysis.distributionFunction
      (beurlingTransformL1 L : ℂ → ℂ) volume q ≤
      (∫⁻ z, ‖lo z‖ₑ ^ 2 ∂volume) / (q ^ 2) := by
    rw [hlow_dist, ← eLpNorm_two_sq_eq_lintegral_enorm_sq lo volume]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (pow_ne_zero 2 hq0))
      (Or.inl (ENNReal.pow_ne_top hqtop))).2
    simpa only [mul_comm] using hlow_mul
  rw [hdist_split]
  refine (HarmonicAnalysis.distributionFunction_add_le_half
    (beurlingTransformL1 H : ℂ → ℂ)
    (beurlingTransformL1 L : ℂ → ℂ) volume t).trans ?_
  simpa only [q, hi, lo, A, f] using add_le_add hhigh hlow

/--
%%handwave
name:
  Strong $L^p$ moment bound for the weak-$L^1$ Beurling transform
statement:
  Let $F\in L^1(\mathbb C)$ and $1<p<2$. Then
  $$
  \begin{aligned}
    \int_{\mathbb C}|\mathcal SF|^p
      \leq p\left(
        \frac{2(40+16\pi)}{p-1}+\frac4{2-p}
      \right)\int_{\mathbb C}|F|^p.
  \end{aligned}
  $$
  The inequality is valid in $[0,\infty]$, before assuming that the input
  $p$th moment is finite.
proof:
  Apply layer cake to $\mathcal SF$, use the high-low distribution estimate
  with splitting height $u=t$, and multiply by $t^{p-1}$. The upper-tail and
  lower-tail identities integrate the two resulting terms with factors
  $(p-1)^{-1}$ and $(2-p)^{-1}$, respectively.
-/
theorem lintegral_rpow_beurlingTransformL1_le
    (F : ℂ →₁[volume] ℂ) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (∫⁻ z, ‖(beurlingTransformL1 F : ℂ → ℂ) z‖ₑ ^ p ∂volume) ≤
      ENNReal.ofReal p *
        ((ENNReal.ofReal 2 * ENNReal.ofReal (40 + 16 * Real.pi) *
              (ENNReal.ofReal (p - 1))⁻¹ +
            ENNReal.ofReal 4 * (ENNReal.ofReal (2 - p))⁻¹) *
          ∫⁻ z, ‖(F : ℂ → ℂ) z‖ₑ ^ p ∂volume) := by
  let f : ℂ → ℂ := (F : ℂ → ℂ)
  let S : ℂ → ℂ := (beurlingTransformL1 F : ℂ → ℂ)
  let C : ENNReal := ENNReal.ofReal (40 + 16 * Real.pi)
  let ν : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hf_meas : StronglyMeasurable f := Lp.stronglyMeasurable F
  have hS_meas : AEStronglyMeasurable S volume :=
    (beurlingTransformL1 F).aestronglyMeasurable
  have hweighted : ∀ᵐ t ∂ν,
      HarmonicAnalysis.distributionFunction S volume (ENNReal.ofReal t) *
          ENNReal.ofReal (t ^ (p - 1)) ≤
        (ENNReal.ofReal 2 * C) *
            ((∫⁻ z in {z | t < ‖f z‖}, ‖f z‖ₑ ∂volume) *
              ENNReal.ofReal (t ^ (p - 2))) +
          ENNReal.ofReal 4 *
            ((∫⁻ z in {z | ‖f z‖ ≤ t}, ‖f z‖ₑ ^ 2 ∂volume) *
              ENNReal.ofReal (t ^ (p - 3))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    let T : ENNReal := ENNReal.ofReal t
    let A : Set ℂ := {z | T < ‖f z‖ₑ}
    have hT0 : T ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr ht
    have hTtop : T ≠ ∞ := ENNReal.ofReal_ne_top
    have hA : MeasurableSet A :=
      measurableSet_lt measurable_const hf_meas.enorm
    have hAeq : A = {z | t < ‖f z‖} := by
      ext z
      simp only [A, Set.mem_setOf_eq, T, ← ofReal_norm,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le]
    have hAceq : Aᶜ = {z | ‖f z‖ ≤ t} := by
      rw [hAeq]
      ext z
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    have hhigh_mass :
        (∫⁻ z, ‖A.indicator f z‖ₑ ∂volume) =
          ∫⁻ z in A, ‖f z‖ₑ ∂volume := by
      rw [← lintegral_indicator hA]
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ A <;> simp [hz]
    have hlow_energy :
        (∫⁻ z, ‖Aᶜ.indicator f z‖ₑ ^ 2 ∂volume) =
          ∫⁻ z in Aᶜ, ‖f z‖ₑ ^ 2 ∂volume := by
      rw [← lintegral_indicator hA.compl]
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ Aᶜ <;> simp [hz]
    have hb := beurlingTransformL1_distribution_le_high_low
      F (u := T) (t := T) hTtop hT0 hTtop
    dsimp only at hb
    change HarmonicAnalysis.distributionFunction S volume T ≤
      (C * ∫⁻ z, ‖A.indicator f z‖ₑ ∂volume) / (T / 2) +
        (∫⁻ z, ‖Aᶜ.indicator f z‖ₑ ^ 2 ∂volume) / ((T / 2) ^ 2) at hb
    rw [hhigh_mass, hlow_energy, hAceq, hAeq] at hb
    have hden : T / 2 = ENNReal.ofReal (t / 2) := by
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num]
      exact (ENNReal.ofReal_div_of_pos (x := t)
        (by norm_num : (0 : ℝ) < 2)).symm
    have ht2 : 0 < t / 2 := div_pos ht (by norm_num)
    have hreal_high : t ^ (p - 1) / (t / 2) = 2 * t ^ (p - 2) := by
      rw [show p - 2 = (p - 1) - 1 by ring,
        Real.rpow_sub ht (p - 1) 1, Real.rpow_one]
      field_simp
    have hreal_low : t ^ (p - 1) / (t / 2) ^ 2 = 4 * t ^ (p - 3) := by
      rw [show p - 3 = (p - 1) - 2 by ring,
        Real.rpow_sub ht (p - 1) 2, Real.rpow_two]
      field_simp
      ring
    have hscalar_high :
        ENNReal.ofReal (t ^ (p - 1)) / (T / 2) =
          ENNReal.ofReal 2 * ENNReal.ofReal (t ^ (p - 2)) := by
      rw [hden, ← ENNReal.ofReal_div_of_pos ht2, hreal_high,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hscalar_low :
        ENNReal.ofReal (t ^ (p - 1)) / ((T / 2) ^ 2) =
          ENNReal.ofReal 4 * ENNReal.ofReal (t ^ (p - 3)) := by
      rw [hden, ← ENNReal.ofReal_pow ht2.le 2,
        ← ENNReal.ofReal_div_of_pos (sq_pos_of_pos ht2), hreal_low,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    calc
      HarmonicAnalysis.distributionFunction S volume T *
          ENNReal.ofReal (t ^ (p - 1)) ≤
          ((C * ∫⁻ z in {z | t < ‖f z‖}, ‖f z‖ₑ ∂volume) / (T / 2) +
            (∫⁻ z in {z | ‖f z‖ ≤ t}, ‖f z‖ₑ ^ 2 ∂volume) /
              ((T / 2) ^ 2)) * ENNReal.ofReal (t ^ (p - 1)) :=
        mul_le_mul_right' hb _
      _ = (ENNReal.ofReal 2 * C) *
            ((∫⁻ z in {z | t < ‖f z‖}, ‖f z‖ₑ ∂volume) *
              ENNReal.ofReal (t ^ (p - 2))) +
          ENNReal.ofReal 4 *
            ((∫⁻ z in {z | ‖f z‖ ≤ t}, ‖f z‖ₑ ^ 2 ∂volume) *
              ENNReal.ofReal (t ^ (p - 3))) := by
        have hhigh :
            ((C * ∫⁻ z in {z | t < ‖f z‖}, ‖f z‖ₑ ∂volume) / (T / 2)) *
                ENNReal.ofReal (t ^ (p - 1)) =
              (ENNReal.ofReal 2 * C) *
                ((∫⁻ z in {z | t < ‖f z‖}, ‖f z‖ₑ ∂volume) *
                  ENNReal.ofReal (t ^ (p - 2))) := by
          calc
            _ = (C * ∫⁻ z in {z | t < ‖f z‖}, ‖f z‖ₑ ∂volume) *
                (ENNReal.ofReal (t ^ (p - 1)) / (T / 2)) := by
              simp only [div_eq_mul_inv]
              ac_rfl
            _ = _ := by rw [hscalar_high]; ac_rfl
        have hlow :
            ((∫⁻ z in {z | ‖f z‖ ≤ t}, ‖f z‖ₑ ^ 2 ∂volume) /
                ((T / 2) ^ 2)) * ENNReal.ofReal (t ^ (p - 1)) =
              ENNReal.ofReal 4 *
                ((∫⁻ z in {z | ‖f z‖ ≤ t}, ‖f z‖ₑ ^ 2 ∂volume) *
                  ENNReal.ofReal (t ^ (p - 3))) := by
          calc
            _ = (∫⁻ z in {z | ‖f z‖ ≤ t}, ‖f z‖ₑ ^ 2 ∂volume) *
                (ENNReal.ofReal (t ^ (p - 1)) / ((T / 2) ^ 2)) := by
              simp only [div_eq_mul_inv]
              ac_rfl
            _ = _ := by rw [hscalar_low]; ac_rfl
        rw [add_mul, hhigh, hlow]
  let U : ℝ → ENNReal := fun t ↦
    (∫⁻ z in {z | t < ‖f z‖}, ‖f z‖ₑ ∂volume) *
      ENNReal.ofReal (t ^ (p - 2))
  let L : ℝ → ENNReal := fun t ↦
    (∫⁻ z in {z | ‖f z‖ ≤ t}, ‖f z‖ₑ ^ 2 ∂volume) *
      ENNReal.ofReal (t ^ (p - 3))
  let G : ℝ → ℂ → ENNReal := fun t z ↦
    {x | t < ‖f x‖}.indicator (fun x ↦ ‖f x‖ₑ) z
  have hGset : MeasurableSet {q : ℝ × ℂ | q.1 < ‖f q.2‖} := by
    exact measurableSet_lt measurable_fst
      (hf_meas.norm.measurable.comp measurable_snd)
  have hG : AEMeasurable (Function.uncurry G) (ν.prod volume) := by
    exact ((hf_meas.enorm.comp measurable_snd).aemeasurable).indicator₀
      hGset.nullMeasurableSet
  have hGfiber : AEMeasurable (fun t ↦ ∫⁻ z, G t z ∂volume) ν :=
    hG.lintegral_prod_right'
  have hupperMass : AEMeasurable
      (fun t ↦ ∫⁻ z in {z | t < ‖f z‖}, ‖f z‖ₑ ∂volume) ν := by
    apply hGfiber.congr
    filter_upwards with t
    simpa only [G] using
      (lintegral_indicator (μ := volume) (f := fun z ↦ ‖f z‖ₑ)
        (measurableSet_lt measurable_const hf_meas.norm.measurable))
  have hupperWeight : AEMeasurable
      (fun t ↦ ENNReal.ofReal (t ^ (p - 2))) ν := by
    have hcontinuous : ContinuousOn (fun t : ℝ ↦ t ^ (p - 2)) (Set.Ioi 0) :=
      continuousOn_id.rpow_const fun t ht ↦ Or.inl ht.ne'
    exact (hcontinuous.aestronglyMeasurable measurableSet_Ioi).aemeasurable.ennreal_ofReal
  have hU : AEMeasurable U ν := by
    exact hupperMass.mul hupperWeight
  have hupper : AEMeasurable
      (fun t ↦ (ENNReal.ofReal 2 * C) * U t) ν := by
    exact aemeasurable_const.mul hU
  have hint_le :
      (∫⁻ t, HarmonicAnalysis.distributionFunction S volume (ENNReal.ofReal t) *
          ENNReal.ofReal (t ^ (p - 1)) ∂ν) ≤
        ∫⁻ t, (ENNReal.ofReal 2 * C) * U t + ENNReal.ofReal 4 * L t ∂ν := by
    exact lintegral_mono_ae hweighted
  have hsplit :
      (∫⁻ t, (ENNReal.ofReal 2 * C) * U t + ENNReal.ofReal 4 * L t ∂ν) =
        (ENNReal.ofReal 2 * C) * (∫⁻ t, U t ∂ν) +
          ENNReal.ofReal 4 * (∫⁻ t, L t ∂ν) := by
    rw [lintegral_add_left' hupper]
    rw [lintegral_const_mul' (ENNReal.ofReal 2 * C) U
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      lintegral_const_mul' (ENNReal.ofReal 4) L ENNReal.ofReal_ne_top]
  have hUintegral :
      (∫⁻ t, U t ∂ν) =
        (ENNReal.ofReal (p - 1))⁻¹ * ∫⁻ z, ‖f z‖ₑ ^ p ∂volume := by
    simpa only [U, ν] using
      (lintegral_upper_tail_mul_rpow_eq f volume hf_meas hp1)
  have hLintegral :
      (∫⁻ t, L t ∂ν) =
        (ENNReal.ofReal (2 - p))⁻¹ * ∫⁻ z, ‖f z‖ₑ ^ p ∂volume := by
    simpa only [L, ν] using
      (lintegral_lower_tail_mul_rpow_eq f volume hf_meas hp0 hp2)
  have hdist :
      (∫⁻ t, HarmonicAnalysis.distributionFunction S volume (ENNReal.ofReal t) *
          ENNReal.ofReal (t ^ (p - 1)) ∂ν) ≤
        (ENNReal.ofReal 2 * C * (ENNReal.ofReal (p - 1))⁻¹ +
            ENNReal.ofReal 4 * (ENNReal.ofReal (2 - p))⁻¹) *
          ∫⁻ z, ‖f z‖ₑ ^ p ∂volume := by
    calc
      _ ≤ ∫⁻ t, (ENNReal.ofReal 2 * C) * U t + ENNReal.ofReal 4 * L t ∂ν :=
        hint_le
      _ = (ENNReal.ofReal 2 * C) * (∫⁻ t, U t ∂ν) +
          ENNReal.ofReal 4 * (∫⁻ t, L t ∂ν) := hsplit
      _ = _ := by
        rw [hUintegral, hLintegral, add_mul]
        ac_rfl
  rw [HarmonicAnalysis.lintegral_enorm_rpow_eq_lintegral_distributionFunction
    S volume hS_meas hp0]
  apply mul_le_mul_left'
  simpa only [ν, C, f] using hdist

/--
%%handwave
name:
  Strong $L^p$ norm bound on integrable inputs
statement:
  Let $F\in L^1(\mathbb C)$ and $1<p<2$. Then
  $$
    \|\mathcal SF\|_p
      \leq
      \left[p\left(
        \frac{2(40+16\pi)}{p-1}+\frac4{2-p}
      \right)\right]^{1/p}\|F\|_p,
  $$
  with extended values allowed on both sides.
proof:
  Take the positive $p$th root of [the strong $p$th-moment inequality](lean:JJMath.Quasiconformal.lintegral_rpow_beurlingTransformL1_le) and use multiplicativity of nonnegative real powers.
-/
theorem eLpNorm_beurlingTransformL1_le
    (F : ℂ →₁[volume] ℂ) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    eLpNorm (beurlingTransformL1 F : ℂ → ℂ) (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal p *
          (ENNReal.ofReal 2 * ENNReal.ofReal (40 + 16 * Real.pi) *
                (ENNReal.ofReal (p - 1))⁻¹ +
            ENNReal.ofReal 4 * (ENNReal.ofReal (2 - p))⁻¹)) ^ (1 / p) *
        eLpNorm (F : ℂ → ℂ) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hpinv : 0 ≤ 1 / p := (one_div_pos.mpr hp0).le
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hp_ne_top : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  calc
    (∫⁻ z, ‖(beurlingTransformL1 F : ℂ → ℂ) z‖ₑ ^ p ∂volume) ^ (1 / p) ≤
        (ENNReal.ofReal p *
          ((ENNReal.ofReal 2 * ENNReal.ofReal (40 + 16 * Real.pi) *
                (ENNReal.ofReal (p - 1))⁻¹ +
            ENNReal.ofReal 4 * (ENNReal.ofReal (2 - p))⁻¹) *
              ∫⁻ z, ‖(F : ℂ → ℂ) z‖ₑ ^ p ∂volume)) ^ (1 / p) := by
      exact ENNReal.rpow_le_rpow
        (lintegral_rpow_beurlingTransformL1_le F hp1 hp2) hpinv
    _ = (ENNReal.ofReal p *
          (ENNReal.ofReal 2 * ENNReal.ofReal (40 + 16 * Real.pi) *
                (ENNReal.ofReal (p - 1))⁻¹ +
            ENNReal.ofReal 4 * (ENNReal.ofReal (2 - p))⁻¹)) ^ (1 / p) *
        (∫⁻ z, ‖(F : ℂ → ℂ) z‖ₑ ^ p ∂volume) ^ (1 / p) := by
      rw [← mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ hpinv]

/--
%%handwave
name:
  $L^p$ membership of the Beurling transform on the integrable intersection
statement:
  Let $F\in L^1(\mathbb C)$, let $1<p<2$, and suppose additionally that
  $F\in L^p(\mathbb C)$. Then the weak-$L^1$ Beurling transform
  $\mathcal SF$ belongs to $L^p(\mathbb C)$.
proof:
  The [strong $L^p$ norm bound](lean:JJMath.Quasiconformal.eLpNorm_beurlingTransformL1_le) bounds the output norm by a finite constant times the finite input norm.
-/
theorem memLp_beurlingTransformL1
    (F : ℂ →₁[volume] ℂ) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hFp : MemLp (F : ℂ → ℂ) (ENNReal.ofReal p) volume) :
    MemLp (beurlingTransformL1 F : ℂ → ℂ) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hq1 : 0 < ENNReal.ofReal (p - 1) :=
    ENNReal.ofReal_pos.mpr (sub_pos.mpr hp1)
  have hq2 : 0 < ENNReal.ofReal (2 - p) :=
    ENNReal.ofReal_pos.mpr (sub_pos.mpr hp2)
  have hB :
      ENNReal.ofReal 2 * ENNReal.ofReal (40 + 16 * Real.pi) *
            (ENNReal.ofReal (p - 1))⁻¹ +
          ENNReal.ofReal 4 * (ENNReal.ofReal (2 - p))⁻¹ < ∞ := by
    rw [ENNReal.add_lt_top]
    constructor
    · exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        (ENNReal.inv_lt_top.mpr hq1)
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.inv_lt_top.mpr hq2)
  have hbase :
      ENNReal.ofReal p *
          (ENNReal.ofReal 2 * ENNReal.ofReal (40 + 16 * Real.pi) *
                (ENNReal.ofReal (p - 1))⁻¹ +
            ENNReal.ofReal 4 * (ENNReal.ofReal (2 - p))⁻¹) < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB
  have hconstant :
      (ENNReal.ofReal p *
          (ENNReal.ofReal 2 * ENNReal.ofReal (40 + 16 * Real.pi) *
                (ENNReal.ofReal (p - 1))⁻¹ +
            ENNReal.ofReal 4 * (ENNReal.ofReal (2 - p))⁻¹)) ^ (1 / p) < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hp0.le) hbase.ne
  refine ⟨(beurlingTransformL1 F).aestronglyMeasurable, ?_⟩
  exact (eLpNorm_beurlingTransformL1_le F hp1 hp2).trans_lt
    (ENNReal.mul_lt_top hconstant hFp.2)

end

end Quasiconformal

end JJMath
