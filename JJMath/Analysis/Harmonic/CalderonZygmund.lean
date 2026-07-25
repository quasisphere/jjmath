import JJMath.Analysis.Harmonic.Kernel
import JJMath.Analysis.Harmonic.Polar
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Elementary Calderón--Zygmund tail estimates

This file begins the operator-estimate layer with the geometric integral
behind the bad-part argument. A first-difference kernel in the plane has an
integrable translated tail outside twice the support radius, with a bound
independent of that radius. Subsequent files will combine this estimate with
mean-zero decomposition pieces, Fubini, and the $L^2$ bound.
-/

namespace JJMath

open Set MeasureTheory ENNReal

namespace HarmonicAnalysis

noncomputable section

/--
%%handwave
name:
  Almost-everywhere summability from summable integrated norms
statement:
  Let $(F_i)_{i\in I}$ be a countable family of integrable functions
  $F_i:X\to E$. If
  $$
    \sum_i\int_X\|F_i(x)\|\,d\mu(x)<\infty,
  $$
  then for almost every $x\in X$ the numerical series
  $\sum_i\|F_i(x)\|$ converges.
proof:
  Tonelli's theorem identifies the integral of the nonnegative extended-real
  pointwise sum with the sum of the integrals. Finiteness of the latter makes
  the pointwise sum finite almost everywhere.
-/
theorem ae_summable_norm_of_summable_integral_norm
    {α ι E : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    [NormedAddCommGroup E]
    {F : ι → α → E} (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i ↦ ∫ x, ‖F i x‖ ∂μ) :
    ∀ᵐ x ∂μ, Summable fun i ↦ ‖F i x‖ := by
  have hFi_meas (i : ι) : AEMeasurable (fun x ↦ ‖F i x‖ₑ) μ :=
    (hF_int i).aestronglyMeasurable.enorm
  have hlin : ∑' i, ∫⁻ x, ‖F i x‖ₑ ∂μ ≠ ∞ := by
    have hi (i : ι) : ∫⁻ x, ‖F i x‖ₑ ∂μ =
        ‖∫ x, ‖F i x‖ ∂μ‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hF_int i).norm, coe_nnreal_eq,
        coe_nnnorm, Real.norm_of_nonneg
          (integral_nonneg (fun x ↦ norm_nonneg (F i x)))]
      simp only [coe_nnnorm]
    rw [funext hi]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 hF_sum.abs
  have htotal : ∫⁻ x, ∑' i, ‖F i x‖ₑ ∂μ ≠ ∞ := by
    rw [lintegral_tsum hFi_meas]
    exact hlin
  refine (ae_lt_top' (AEMeasurable.tsum hFi_meas) htotal).mono ?_
  intro x hx
  have hnn : Summable fun i ↦ ‖F i x‖₊ := by
    apply ENNReal.tsum_coe_ne_top_iff_summable.1
    simpa only [enorm_eq_nnnorm] using hx.ne
  simpa only [coe_nnnorm] using NNReal.summable_coe.2 hnn

/--
%%handwave
name:
  Integrability of an absolutely summable family of integrable functions
statement:
  Let $(F_i)_{i\in I}$ be a countable family of integrable functions
  $F_i:X\to E$, where $E$ is complete. If
  $$
    \sum_i\int_X\|F_i(x)\|\,d\mu(x)<\infty,
  $$
  then the pointwise sum $x\mapsto\sum_iF_i(x)$ is integrable.
proof:
  The pointwise norm series is summable almost everywhere and its sum is
  integrable by Tonelli's theorem. The norm of the vector series is bounded
  by this integrable numerical sum.
-/
theorem integrable_tsum_of_summable_integral_norm
    {α ι E : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    [NormedAddCommGroup E] [CompleteSpace E]
    {F : ι → α → E} (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i ↦ ∫ x, ‖F i x‖ ∂μ) :
    Integrable (fun x ↦ ∑' i, F i x) μ := by
  have hFi_meas (i : ι) : AEMeasurable (fun x ↦ ‖F i x‖ₑ) μ :=
    (hF_int i).aestronglyMeasurable.enorm
  have hlin : ∑' i, ∫⁻ x, ‖F i x‖ₑ ∂μ ≠ ∞ := by
    have hi (i : ι) : ∫⁻ x, ‖F i x‖ₑ ∂μ =
        ‖∫ x, ‖F i x‖ ∂μ‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hF_int i).norm, coe_nnreal_eq,
        coe_nnnorm, Real.norm_of_nonneg
          (integral_nonneg (fun x ↦ norm_nonneg (F i x)))]
      simp only [coe_nnnorm]
    rw [funext hi]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 hF_sum.abs
  have hsum_norm := ae_summable_norm_of_summable_integral_norm hF_int hF_sum
  have hbound : Integrable (fun x ↦ ∑' i, (‖F i x‖₊ : ℝ)) μ := by
    constructor
    · fun_prop
    · dsimp [HasFiniteIntegral]
      have hfinite : ∫⁻ x, ∑' i, ‖F i x‖ₑ ∂μ < ∞ := by
        rw [lintegral_tsum hFi_meas, lt_top_iff_ne_top]
        exact hlin
      convert! hfinite using 1
      apply lintegral_congr_ae
      simp_rw [← coe_nnnorm, ← NNReal.coe_tsum, enorm_eq_nnnorm,
        NNReal.nnnorm_eq]
      filter_upwards [hsum_norm] with x hx
      exact ENNReal.coe_tsum (NNReal.summable_coe.mp hx)
  apply Integrable.mono' hbound
    (AEStronglyMeasurable.tsum fun i ↦ (hF_int i).aestronglyMeasurable)
  filter_upwards [hsum_norm] with x hx
  exact norm_tsum_le_tsum_norm hx

/--
%%handwave
name:
  Integrated tail of a planar kernel first difference
statement:
  Let $K:\mathbb C\to E$ satisfy
  $$
    |K(x-h)-K(x)|\leq C\frac{|h|}{|x|^3}
    \quad\text{when }2|h|\leq|x|,
  $$
  where $C\geq0$. If $r>0$ and $|y-c|\leq r$, then
  $$
    \int_{|x-c|>2r}|K(x-y)-K(x-c)|\,dx\leq\pi C.
  $$
proof:
  On the integration region, $2|y-c|\leq|x-c|$, so the first-difference
  estimate bounds the integrand by $Cr|x-c|^{-3}$. Apply
  [the translated inverse-cube integral equals $2\pi/a$](lean:JJMath.HarmonicAnalysis.setIntegral_norm_sub_inv_cube_exterior) with $a=2r$.
-/
theorem HasKernelFirstDifference.setIntegral_norm_sub_sub_exterior_le
    {E : Type*} [NormedAddCommGroup E]
    (K : ℂ → E) {C r : ℝ}
    (hK : HasKernelFirstDifference K 2 C)
    (hC : 0 ≤ C) (hr : 0 < r) (c y : ℂ)
    (hy : ‖y - c‖ ≤ r) :
    (∫ x in {x : ℂ | 2 * r < ‖x - c‖},
      ‖K (x - y) - K (x - c)‖) ≤ Real.pi * C := by
  let s : Set ℂ := {x : ℂ | 2 * r < ‖x - c‖}
  let f : ℂ → ℝ := fun x ↦ ‖K (x - y) - K (x - c)‖
  let g : ℂ → ℝ := fun x ↦
    C * r * (‖x - c‖⁻¹ ^ (3 : ℕ))
  have hs : MeasurableSet s :=
    (isOpen_lt continuous_const
      (continuous_id.sub continuous_const).norm).measurableSet
  have h2r : 0 < 2 * r := by positivity
  have hg : IntegrableOn g s volume := by
    exact (integrableOn_norm_sub_inv_cube_exterior (2 * r) h2r c).const_mul
      (C * r)
  have hnonneg : 0 ≤ᶠ[ae (volume.restrict s)] f :=
    Filter.Eventually.of_forall fun x ↦ norm_nonneg _
  have hle : f ≤ᶠ[ae (volume.restrict s)] g := by
    filter_upwards [ae_restrict_mem hs] with x hx
    have hxpos : 0 < ‖x - c‖ := h2r.trans hx
    have hscale : 2 * ‖y - c‖ ≤ ‖x - c‖ := by
      calc
        2 * ‖y - c‖ ≤ 2 * r :=
          mul_le_mul_of_nonneg_left hy (by norm_num)
        _ ≤ ‖x - c‖ := hx.le
    calc
      f x ≤ C * ‖y - c‖ / ‖x - c‖ ^ (2 + 1) :=
        hK.sub_sub_le x y c hscale
      _ ≤ C * r / ‖x - c‖ ^ (2 + 1) := by gcongr
      _ = g x := by
        simp only [Nat.reduceAdd]
        rw [div_eq_mul_inv, ← inv_pow]
  have hmono : (∫ x in s, f x) ≤ ∫ x in s, g x :=
    integral_mono_of_nonneg hnonneg hg hle
  calc
    (∫ x in {x : ℂ | 2 * r < ‖x - c‖},
        ‖K (x - y) - K (x - c)‖) = ∫ x in s, f x := rfl
    _ ≤ ∫ x in s, g x := hmono
    _ = C * r * (2 * Real.pi / (2 * r)) := by
      rw [show (∫ x in s, g x) =
          C * r * ∫ x in s, ‖x - c‖⁻¹ ^ (3 : ℕ) by
        simp only [g]
        rw [integral_const_mul]]
      rw [setIntegral_norm_sub_inv_cube_exterior (2 * r) h2r c]
    _ = Real.pi * C := by
      field_simp

/--
%%handwave
name:
  Product integrability of a bad-piece kernel difference
statement:
  Let $K:\mathbb C\to\mathbb C$ be measurable and satisfy
  $$
    |K(x-h)-K(x)|\leq C\frac{|h|}{|x|^3}
    \quad\text{when }2|h|\leq|x|,
  $$
  where $C\geq0$. If $r>0$ and $b\in L^1(\mathbb C)$ vanishes outside
  $|y-c|\leq r$, then
  $$
    (x,y)\longmapsto\bigl(K(x-y)-K(x-c)\bigr)b(y)
  $$
  is integrable on $\{|x-c|>2r\}\times\mathbb C$.
proof:
  The norm is at most $Cr|x-c|^{-3}|b(y)|$. This is an integrable product by
  [integrability of the translated inverse-cube tail](lean:JJMath.HarmonicAnalysis.integrableOn_norm_sub_inv_cube_exterior) and the integrability of $b$.
-/
theorem HasKernelFirstDifference.integrable_kernelDifference_mul_prod_exterior
    (K : ℂ → ℂ) {C r : ℝ}
    (hK : HasKernelFirstDifference K 2 C)
    (hKm : Measurable K) (hC : 0 ≤ C) (hr : 0 < r)
    (c : ℂ) (b : ℂ → ℂ) (hb : Integrable b volume)
    (hbsupp : ∀ y : ℂ, b y ≠ 0 → ‖y - c‖ ≤ r) :
    Integrable
      (fun p : ℂ × ℂ ↦ (K (p.1 - p.2) - K (p.1 - c)) * b p.2)
      ((volume.restrict {x : ℂ | 2 * r < ‖x - c‖}).prod volume) := by
  let s : Set ℂ := {x : ℂ | 2 * r < ‖x - c‖}
  let μs : Measure ℂ := volume.restrict s
  let q : ℂ × ℂ → ℂ := fun p ↦
    (K (p.1 - p.2) - K (p.1 - c)) * b p.2
  let d : ℂ × ℂ → ℝ := fun p ↦
    (C * r * (‖p.1 - c‖⁻¹ ^ (3 : ℕ))) * ‖b p.2‖
  have hs : MeasurableSet s :=
    (isOpen_lt continuous_const
      (continuous_id.sub continuous_const).norm).measurableSet
  have h2r : 0 < 2 * r := by positivity
  have hx : Integrable
      (fun x : ℂ ↦ C * r * (‖x - c‖⁻¹ ^ (3 : ℕ))) μs := by
    exact (integrableOn_norm_sub_inv_cube_exterior (2 * r) h2r c).const_mul
      (C * r)
  have hd : Integrable d (μs.prod volume) := by
    exact hx.mul_prod hb.norm
  have hqmeas : AEStronglyMeasurable q (μs.prod volume) := by
    have hdiff : AEStronglyMeasurable
        (fun p : ℂ × ℂ ↦ K (p.1 - p.2) - K (p.1 - c))
        (μs.prod volume) :=
      ((hKm.comp (measurable_fst.sub measurable_snd)).sub
        (hKm.comp (measurable_fst.sub measurable_const))).aestronglyMeasurable
    exact hdiff.mul hb.1.comp_snd
  have hxmem : ∀ᵐ p : ℂ × ℂ ∂μs.prod volume, p.1 ∈ s := by
    apply (Measure.ae_prod_iff_ae_ae (hs.preimage measurable_fst)).2
    filter_upwards [ae_restrict_mem hs] with x hx
    exact Filter.Eventually.of_forall fun _y ↦ hx
  have hqd : ∀ᵐ p : ℂ × ℂ ∂μs.prod volume, ‖q p‖ ≤ d p := by
    filter_upwards [hxmem] with p hp
    by_cases hbp : b p.2 = 0
    · simp [q, d, hbp]
    · have hyp : ‖p.2 - c‖ ≤ r := hbsupp p.2 hbp
      have hscale : 2 * ‖p.2 - c‖ ≤ ‖p.1 - c‖ := by
        calc
          2 * ‖p.2 - c‖ ≤ 2 * r :=
            mul_le_mul_of_nonneg_left hyp (by norm_num)
          _ ≤ ‖p.1 - c‖ := hp.le
      have hdiff := hK.sub_sub_le p.1 p.2 c hscale
      have hdiff' : ‖K (p.1 - p.2) - K (p.1 - c)‖ ≤
          C * r * (‖p.1 - c‖⁻¹ ^ (3 : ℕ)) := by
        calc
          _ ≤ C * ‖p.2 - c‖ / ‖p.1 - c‖ ^ (2 + 1) := hdiff
          _ ≤ C * r / ‖p.1 - c‖ ^ (2 + 1) := by gcongr
          _ = C * r * (‖p.1 - c‖⁻¹ ^ (3 : ℕ)) := by
            simp only [Nat.reduceAdd]
            rw [div_eq_mul_inv, ← inv_pow]
      change ‖(K (p.1 - p.2) - K (p.1 - c)) * b p.2‖ ≤
        (C * r * (‖p.1 - c‖⁻¹ ^ (3 : ℕ))) * ‖b p.2‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hdiff' (norm_nonneg _)
  exact hd.mono' hqmeas hqd

/--
%%handwave
name:
  Integrated tail of a bad-piece kernel difference
statement:
  Let $K:\mathbb C\to\mathbb C$ be measurable and satisfy
  $$
    |K(x-h)-K(x)|\leq C\frac{|h|}{|x|^3}
    \quad\text{when }2|h|\leq|x|,
  $$
  where $C\geq0$. Let $r>0$, and let $b\in L^1(\mathbb C)$ vanish outside
  the closed disk $|y-c|\leq r$. Then
  $$
    \int_{|x-c|>2r}
      \left|\int_{\mathbb C}
        \bigl(K(x-y)-K(x-c)\bigr)b(y)\,dy\right|\,dx
      \leq \pi C\int_{\mathbb C}|b(y)|\,dy.
  $$
proof:
  On the product of the exterior disk with the support of $b$, dominate the
  integrand by $Cr|x-c|^{-3}|b(y)|$. This product is integrable. Tonelli's
  theorem and [the integrated first-difference bound is at most $\pi C$](lean:JJMath.HarmonicAnalysis.HasKernelFirstDifference.setIntegral_norm_sub_sub_exterior_le) then give the result.
-/
theorem HasKernelFirstDifference.setIntegral_norm_integral_sub_sub_mul_le
    (K : ℂ → ℂ) {C r : ℝ}
    (hK : HasKernelFirstDifference K 2 C)
    (hKm : Measurable K) (hC : 0 ≤ C) (hr : 0 < r)
    (c : ℂ) (b : ℂ → ℂ) (hb : Integrable b volume)
    (hbsupp : ∀ y : ℂ, b y ≠ 0 → ‖y - c‖ ≤ r) :
    (∫ x in {x : ℂ | 2 * r < ‖x - c‖},
        ‖∫ y : ℂ, (K (x - y) - K (x - c)) * b y ∂volume‖) ≤
      Real.pi * C * ∫ y : ℂ, ‖b y‖ ∂volume := by
  let s : Set ℂ := {x : ℂ | 2 * r < ‖x - c‖}
  let μs : Measure ℂ := volume.restrict s
  let q : ℂ × ℂ → ℂ := fun p ↦
    (K (p.1 - p.2) - K (p.1 - c)) * b p.2
  have hq : Integrable q (μs.prod volume) := by
    simpa only [q, μs, s] using
      hK.integrable_kernelDifference_mul_prod_exterior
        K hKm hC hr c b hb hbsupp
  have hleftInt : Integrable
      (fun x : ℂ ↦ ∫ y : ℂ, ‖q (x, y)‖ ∂volume) μs :=
    hq.integral_norm_prod_left
  have hinner :
      (fun x : ℂ ↦ ‖∫ y : ℂ, q (x, y) ∂volume‖) ≤ᶠ[ae μs]
        (fun x : ℂ ↦ ∫ y : ℂ, ‖q (x, y)‖ ∂volume) :=
    Filter.Eventually.of_forall fun x ↦ norm_integral_le_integral_norm _
  have hfirst :
      (∫ x : ℂ, ‖∫ y : ℂ, q (x, y) ∂volume‖ ∂μs) ≤
        ∫ x : ℂ, ∫ y : ℂ, ‖q (x, y)‖ ∂volume ∂μs :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) hleftInt hinner
  have hswap :
      (∫ x : ℂ, ∫ y : ℂ, ‖q (x, y)‖ ∂volume ∂μs) =
        ∫ y : ℂ, ∫ x : ℂ, ‖q (x, y)‖ ∂μs ∂volume := by
    calc
      _ = ∫ p : ℂ × ℂ, ‖q p‖ ∂μs.prod volume :=
        (integral_prod _ hq.norm).symm
      _ = ∫ p : ℂ × ℂ, ‖q p.swap‖ ∂volume.prod μs :=
        (integral_prod_swap _).symm
      _ = _ := integral_prod _ hq.norm.swap
  have hybound : ∀ y : ℂ,
      (∫ x : ℂ, ‖q (x, y)‖ ∂μs) ≤ Real.pi * C * ‖b y‖ := by
    intro y
    by_cases hby : b y = 0
    · simp [q, hby]
    · have hy := hbsupp y hby
      have htail := hK.setIntegral_norm_sub_sub_exterior_le
        K hC hr c y hy
      calc
        (∫ x : ℂ, ‖q (x, y)‖ ∂μs) =
            (∫ x in s, ‖K (x - y) - K (x - c)‖ * ‖b y‖) := by
          apply integral_congr_ae
          filter_upwards with x
          simp [q]
        _ = (∫ x in s, ‖K (x - y) - K (x - c)‖) * ‖b y‖ := by
          rw [integral_mul_const]
        _ ≤ (Real.pi * C) * ‖b y‖ :=
          mul_le_mul_of_nonneg_right htail (norm_nonneg _)
        _ = Real.pi * C * ‖b y‖ := rfl
  have hright :
      (∫ y : ℂ, ∫ x : ℂ, ‖q (x, y)‖ ∂μs ∂volume) ≤
        ∫ y : ℂ, Real.pi * C * ‖b y‖ ∂volume := by
    exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun y ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      (hb.norm.const_mul (Real.pi * C))
      (Filter.Eventually.of_forall hybound)
  calc
    (∫ x in {x : ℂ | 2 * r < ‖x - c‖},
        ‖∫ y : ℂ, (K (x - y) - K (x - c)) * b y ∂volume‖) =
      ∫ x : ℂ, ‖∫ y : ℂ, q (x, y) ∂volume‖ ∂μs := rfl
    _ ≤ ∫ x : ℂ, ∫ y : ℂ, ‖q (x, y)‖ ∂volume ∂μs := hfirst
    _ = ∫ y : ℂ, ∫ x : ℂ, ‖q (x, y)‖ ∂μs ∂volume := hswap
    _ ≤ ∫ y : ℂ, Real.pi * C * ‖b y‖ ∂volume := hright
    _ = Real.pi * C * ∫ y : ℂ, ‖b y‖ ∂volume := by
      rw [integral_const_mul]

/--
%%handwave
name:
  Kernel cancellation against a mean-zero function
statement:
  Let $b:\mathbb C\to\mathbb C$ be integrable with
  $\int_{\mathbb C}b=0$. If
  $y\mapsto\bigl(K(x-y)-K(x-c)\bigr)b(y)$ is integrable, then
  $$
    \int_{\mathbb C}K(x-y)b(y)\,dy
      =\int_{\mathbb C}\bigl(K(x-y)-K(x-c)\bigr)b(y)\,dy.
  $$
proof:
  Add $K(x-c)b(y)$ to the kernel difference and integrate. Its integral is
  $K(x-c)\int b=0$.
-/
theorem integral_kernel_mul_eq_integral_sub_sub_mul_of_integral_eq_zero
    (K b : ℂ → ℂ) (x c : ℂ)
    (hb : Integrable b volume)
    (hdiff : Integrable
      (fun y : ℂ ↦ (K (x - y) - K (x - c)) * b y) volume)
    (hmean : ∫ y : ℂ, b y ∂volume = 0) :
    (∫ y : ℂ, K (x - y) * b y ∂volume) =
      ∫ y : ℂ, (K (x - y) - K (x - c)) * b y ∂volume := by
  have hconst : Integrable (fun y : ℂ ↦ K (x - c) * b y) volume :=
    hb.const_mul _
  have hsplit : (fun y : ℂ ↦ K (x - y) * b y) =
      fun y : ℂ ↦
        (K (x - y) - K (x - c)) * b y + K (x - c) * b y := by
    funext y
    ring
  rw [hsplit, integral_add hdiff hconst, integral_const_mul, hmean]
  simp

/--
%%handwave
name:
  Integrability of a mean-zero kernel convolution on the exterior
statement:
  Under the planar first-difference estimate with $C\geq0$, let $r>0$ and
  let $b\in L^1(\mathbb C)$ be supported in $|y-c|\leq r$ with
  $\int_{\mathbb C}b=0$. Then
  $$
    x\longmapsto\int_{\mathbb C}K(x-y)b(y)\,dy
  $$
  is integrable on $|x-c|>2r$.
proof:
  Fubini makes the kernel-difference slice integrable for almost every
  exterior point. Mean-zero subtraction identifies that slice with the
  ordinary convolution almost everywhere.
-/
theorem HasKernelFirstDifference.integrableOn_integral_mul_exterior_of_integral_eq_zero
    (K : ℂ → ℂ) {C r : ℝ}
    (hK : HasKernelFirstDifference K 2 C)
    (hKm : Measurable K) (hC : 0 ≤ C) (hr : 0 < r)
    (c : ℂ) (b : ℂ → ℂ) (hb : Integrable b volume)
    (hbsupp : ∀ y : ℂ, b y ≠ 0 → ‖y - c‖ ≤ r)
    (hmean : ∫ y : ℂ, b y ∂volume = 0) :
    IntegrableOn
      (fun x : ℂ ↦ ∫ y : ℂ, K (x - y) * b y ∂volume)
      {x : ℂ | 2 * r < ‖x - c‖} volume := by
  let s : Set ℂ := {x : ℂ | 2 * r < ‖x - c‖}
  let μs : Measure ℂ := volume.restrict s
  let q : ℂ × ℂ → ℂ := fun p ↦
    (K (p.1 - p.2) - K (p.1 - c)) * b p.2
  have hq : Integrable q (μs.prod volume) := by
    simpa only [q, μs, s] using
      HasKernelFirstDifference.integrable_kernelDifference_mul_prod_exterior
        K hK hKm hC hr c b hb hbsupp
  have heq : (fun x : ℂ ↦ ∫ y : ℂ, K (x - y) * b y ∂volume) =ᵐ[μs]
      fun x : ℂ ↦ ∫ y : ℂ, q (x, y) ∂volume := by
    filter_upwards [hq.prod_right_ae] with x hx
    exact integral_kernel_mul_eq_integral_sub_sub_mul_of_integral_eq_zero
      K b x c hb (by simpa only [q] using hx) hmean
  exact hq.integral_prod_left.congr heq.symm

/--
%%handwave
name:
  Integrated kernel tail of a mean-zero bad piece
statement:
  Let $K:\mathbb C\to\mathbb C$ be measurable and satisfy
  $$
    |K(x-h)-K(x)|\leq C\frac{|h|}{|x|^3}
    \quad\text{when }2|h|\leq|x|,
  $$
  where $C\geq0$. Let $r>0$, and let $b\in L^1(\mathbb C)$ be supported in
  $|y-c|\leq r$ and satisfy $\int_{\mathbb C}b=0$. Then
  $$
    \int_{|x-c|>2r}
      \left|\int_{\mathbb C}K(x-y)b(y)\,dy\right|\,dx
      \leq\pi C\int_{\mathbb C}|b(y)|\,dy.
  $$
proof:
  Almost every exterior slice of the kernel-difference product is
  integrable. Apply [mean-zero subtraction leaves the kernel integral unchanged](lean:JJMath.HarmonicAnalysis.integral_kernel_mul_eq_integral_sub_sub_mul_of_integral_eq_zero), then use [the integrated kernel-difference estimate](lean:JJMath.HarmonicAnalysis.HasKernelFirstDifference.setIntegral_norm_integral_sub_sub_mul_le).
-/
theorem HasKernelFirstDifference.setIntegral_norm_integral_mul_le_of_integral_eq_zero
    (K : ℂ → ℂ) {C r : ℝ}
    (hK : HasKernelFirstDifference K 2 C)
    (hKm : Measurable K) (hC : 0 ≤ C) (hr : 0 < r)
    (c : ℂ) (b : ℂ → ℂ) (hb : Integrable b volume)
    (hbsupp : ∀ y : ℂ, b y ≠ 0 → ‖y - c‖ ≤ r)
    (hmean : ∫ y : ℂ, b y ∂volume = 0) :
    (∫ x in {x : ℂ | 2 * r < ‖x - c‖},
        ‖∫ y : ℂ, K (x - y) * b y ∂volume‖) ≤
      Real.pi * C * ∫ y : ℂ, ‖b y‖ ∂volume := by
  let s : Set ℂ := {x : ℂ | 2 * r < ‖x - c‖}
  let μs : Measure ℂ := volume.restrict s
  let q : ℂ × ℂ → ℂ := fun p ↦
    (K (p.1 - p.2) - K (p.1 - c)) * b p.2
  have hq : Integrable q (μs.prod volume) := by
    simpa only [q, μs, s] using
      HasKernelFirstDifference.integrable_kernelDifference_mul_prod_exterior
        K hK hKm hC hr c b hb hbsupp
  have heq : ∀ᵐ x ∂μs,
      (∫ y : ℂ, K (x - y) * b y ∂volume) =
        ∫ y : ℂ, (K (x - y) - K (x - c)) * b y ∂volume := by
    filter_upwards [hq.prod_right_ae] with x hx
    exact integral_kernel_mul_eq_integral_sub_sub_mul_of_integral_eq_zero
      K b x c hb (by simpa only [q] using hx) hmean
  calc
    (∫ x in {x : ℂ | 2 * r < ‖x - c‖},
        ‖∫ y : ℂ, K (x - y) * b y ∂volume‖) =
      ∫ x in {x : ℂ | 2 * r < ‖x - c‖},
        ‖∫ y : ℂ, (K (x - y) - K (x - c)) * b y ∂volume‖ := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]
    _ ≤ Real.pi * C * ∫ y : ℂ, ‖b y‖ ∂volume :=
      hK.setIntegral_norm_integral_sub_sub_mul_le
        K hKm hC hr c b hb hbsupp

/--
%%handwave
name:
  Integrability of a countable sum of mean-zero kernel tails
statement:
  Let $K:\mathbb C\to\mathbb C$ satisfy the measurable planar
  first-difference estimate with constant $C\geq0$. Let $(b_i)_{i\in I}$ be
  a countable family of integrable functions, where $b_i$ is supported in
  $|y-c_i|\leq r_i$, $r_i>0$, and $\int b_i=0$. If
  $\sum_i\|b_i\|_1<\infty$, then
  $$
    x\longmapsto\sum_i\int_{\mathbb C}K(x-y)b_i(y)\,dy
  $$
  is integrable on the common exterior
  $\{x:|x-c_i|>2r_i\text{ for every }i\}$.
proof:
  Restrict each tail to the common exterior. The first-difference estimate
  bounds its $L^1$ norm by $\pi C\|b_i\|_1$, so the restricted integrated
  norms are summable. Apply [integrability of an absolutely summable family](lean:JJMath.HarmonicAnalysis.integrable_tsum_of_summable_integral_norm) and identify the restricted pointwise sum.
-/
theorem HasKernelFirstDifference.integrableOn_tsum_integral_mul_of_integral_eq_zero
    {ι : Type*} [Countable ι]
    (K : ℂ → ℂ) {C : ℝ}
    (hK : HasKernelFirstDifference K 2 C)
    (hKm : Measurable K) (hC : 0 ≤ C)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (c : ι → ℂ)
    (b : ι → ℂ → ℂ) (hb : ∀ i, Integrable (b i) volume)
    (hbsupp : ∀ i y, b i y ≠ 0 → ‖y - c i‖ ≤ r i)
    (hmean : ∀ i, ∫ y : ℂ, b i y ∂volume = 0)
    (hmass : Summable fun i ↦ ∫ y : ℂ, ‖b i y‖ ∂volume) :
    IntegrableOn
      (fun x ↦ ∑' i, ∫ y : ℂ, K (x - y) * b i y ∂volume)
      {x : ℂ | ∀ i, 2 * r i < ‖x - c i‖} volume := by
  let t : Set ℂ := {x : ℂ | ∀ i, 2 * r i < ‖x - c i‖}
  let A : ι → ℂ → ℂ := fun i x ↦
    ∫ y : ℂ, K (x - y) * b i y ∂volume
  let F : ι → ℂ → ℂ := fun i ↦ t.indicator (A i)
  have ht : MeasurableSet t := by
    dsimp only [t]
    measurability
  have hAi (i : ι) : IntegrableOn (A i)
      {x : ℂ | 2 * r i < ‖x - c i‖} volume := by
    simpa only [A] using
      (HasKernelFirstDifference.integrableOn_integral_mul_exterior_of_integral_eq_zero
        K hK hKm hC (hr i) (c i) (b i) (hb i) (hbsupp i) (hmean i))
  have hsub (i : ι) : t ⊆ {x : ℂ | 2 * r i < ‖x - c i‖} :=
    fun _ hx ↦ hx i
  have hFi (i : ι) : Integrable (F i) volume := by
    simpa only [F] using ((hAi i).mono_set (hsub i)).integrable_indicator ht
  have hFi_bound (i : ι) : (∫ x, ‖F i x‖ ∂volume) ≤
      Real.pi * C * ∫ y, ‖b i y‖ ∂volume := by
    calc
      (∫ x, ‖F i x‖ ∂volume) = ∫ x in t, ‖A i x‖ ∂volume := by
        simp only [F, norm_indicator_eq_indicator_norm, integral_indicator ht]
      _ ≤ ∫ x in {x : ℂ | 2 * r i < ‖x - c i‖}, ‖A i x‖ ∂volume := by
        apply setIntegral_mono_set (hAi i).norm
          (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
        exact Filter.Eventually.of_forall fun _ hx ↦ hsub i hx
      _ ≤ Real.pi * C * ∫ y, ‖b i y‖ ∂volume := by
        simpa only [A] using
          (HasKernelFirstDifference.setIntegral_norm_integral_mul_le_of_integral_eq_zero
            K hK hKm hC (hr i) (c i) (b i) (hb i) (hbsupp i) (hmean i))
  have hFi_sum : Summable fun i ↦ ∫ x, ‖F i x‖ ∂volume := by
    apply Summable.of_nonneg_of_le
    · exact fun i ↦ integral_nonneg fun _ ↦ norm_nonneg _
    · exact hFi_bound
    · exact hmass.mul_left (Real.pi * C)
  have hsumF : Integrable (fun x ↦ ∑' i, F i x) volume :=
    integrable_tsum_of_summable_integral_norm hFi hFi_sum
  apply IntegrableOn.congr_fun hsumF.integrableOn _ ht
  intro x hx
  simp only [F, A, indicator_of_mem hx]

/--
%%handwave
name:
  Exterior tail of a countable sum of bad pieces
statement:
  Let $K:\mathbb C\to\mathbb C$ satisfy the measurable planar
  first-difference estimate with constant $C\geq0$. Let $(b_i)_{i\in I}$ be
  a countable family of integrable functions such that $b_i$ is supported in
  $|y-c_i|\leq r_i$, where $r_i>0$, and $\int_{\mathbb C}b_i=0$. If
  $\sum_i\|b_i\|_1<\infty$, then
  $$
    \int_{|x-c_i|>2r_i\ \forall i}
      \left|\sum_i\int_{\mathbb C}K(x-y)b_i(y)\,dy\right|\,dx
      \leq \pi C\sum_i\|b_i\|_1.
  $$
proof:
  Restrict every convolution tail to the common exterior. The individual
  exterior estimates make the restricted $L^1$ norms summable, so the
  pointwise series is integrable. The norm of its sum is bounded by the sum
  of its norms; Tonelli's theorem and the individual tail estimates finish
  the argument.
-/
theorem HasKernelFirstDifference.setIntegral_norm_tsum_integral_mul_le_of_integral_eq_zero
    {ι : Type*} [Countable ι]
    (K : ℂ → ℂ) {C : ℝ}
    (hK : HasKernelFirstDifference K 2 C)
    (hKm : Measurable K) (hC : 0 ≤ C)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (c : ι → ℂ)
    (b : ι → ℂ → ℂ) (hb : ∀ i, Integrable (b i) volume)
    (hbsupp : ∀ i y, b i y ≠ 0 → ‖y - c i‖ ≤ r i)
    (hmean : ∀ i, ∫ y : ℂ, b i y ∂volume = 0)
    (hmass : Summable fun i ↦ ∫ y : ℂ, ‖b i y‖ ∂volume) :
    (∫ x in {x : ℂ | ∀ i, 2 * r i < ‖x - c i‖},
        ‖∑' i, ∫ y : ℂ, K (x - y) * b i y ∂volume‖) ≤
      Real.pi * C * ∑' i, ∫ y : ℂ, ‖b i y‖ ∂volume := by
  let t : Set ℂ := {x : ℂ | ∀ i, 2 * r i < ‖x - c i‖}
  let A : ι → ℂ → ℂ := fun i x ↦
    ∫ y : ℂ, K (x - y) * b i y ∂volume
  let F : ι → ℂ → ℂ := fun i ↦ t.indicator (A i)
  have ht : MeasurableSet t := by
    dsimp only [t]
    measurability
  have hAi : ∀ i, IntegrableOn (A i)
      {x : ℂ | 2 * r i < ‖x - c i‖} volume := by
    intro i
    simpa only [A] using
      (HasKernelFirstDifference.integrableOn_integral_mul_exterior_of_integral_eq_zero
        K hK hKm hC (hr i) (c i) (b i) (hb i) (hbsupp i) (hmean i))
  have hsub : ∀ i, t ⊆ {x : ℂ | 2 * r i < ‖x - c i‖} := by
    intro i x hx
    exact hx i
  have hFi : ∀ i, Integrable (F i) volume := by
    intro i
    simpa only [F] using ((hAi i).mono_set (hsub i)).integrable_indicator ht
  have hFi_bound : ∀ i, (∫ x, ‖F i x‖ ∂volume) ≤
      Real.pi * C * ∫ y, ‖b i y‖ ∂volume := by
    intro i
    calc
      (∫ x, ‖F i x‖ ∂volume) = ∫ x in t, ‖A i x‖ ∂volume := by
        simp only [F, norm_indicator_eq_indicator_norm, integral_indicator ht]
      _ ≤ ∫ x in {x : ℂ | 2 * r i < ‖x - c i‖}, ‖A i x‖ ∂volume := by
        apply setIntegral_mono_set (hAi i).norm
          (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
        exact Filter.Eventually.of_forall fun x hx ↦ hsub i hx
      _ ≤ Real.pi * C * ∫ y, ‖b i y‖ ∂volume := by
        simpa only [A] using
          (HasKernelFirstDifference.setIntegral_norm_integral_mul_le_of_integral_eq_zero
            K hK hKm hC (hr i) (c i) (b i) (hb i) (hbsupp i) (hmean i))
  have hFi_sum : Summable fun i ↦ ∫ x, ‖F i x‖ ∂volume := by
    apply Summable.of_nonneg_of_le
    · intro i
      exact integral_nonneg fun _ ↦ norm_nonneg _
    · exact hFi_bound
    · exact hmass.mul_left (Real.pi * C)
  have hsumF : Integrable (fun x ↦ ∑' i, F i x) volume :=
    integrable_tsum_of_summable_integral_norm hFi hFi_sum
  have hnormFi_sum : Summable fun i ↦
      ∫ x, ‖(fun x ↦ ‖F i x‖) x‖ ∂volume := by
    simpa only [norm_norm] using hFi_sum
  have hsumNorm : Integrable (fun x ↦ ∑' i, ‖F i x‖) volume :=
    integrable_tsum_of_summable_integral_norm (fun i ↦ (hFi i).norm) hnormFi_sum
  have hpoint : ∀ᵐ x ∂volume,
      ‖∑' i, F i x‖ ≤ ∑' i, ‖F i x‖ := by
    filter_upwards [ae_summable_norm_of_summable_integral_norm hFi hFi_sum]
      with x hx
    exact norm_tsum_le_tsum_norm hx
  have hseteq :
      (∫ x in t, ‖∑' i, A i x‖ ∂volume) =
        ∫ x in t, ‖∑' i, F i x‖ ∂volume := by
    apply setIntegral_congr_fun ht
    intro x hx
    change ‖∑' i, A i x‖ = ‖∑' i, F i x‖
    congr 1
    apply tsum_congr
    intro i
    simp only [F, indicator_of_mem hx]
  calc
    (∫ x in {x : ℂ | ∀ i, 2 * r i < ‖x - c i‖},
        ‖∑' i, ∫ y : ℂ, K (x - y) * b i y ∂volume‖) =
        ∫ x in t, ‖∑' i, A i x‖ ∂volume := by rfl
    _ = ∫ x in t, ‖∑' i, F i x‖ ∂volume := hseteq
    _ ≤ ∫ x, ‖∑' i, F i x‖ ∂volume :=
      setIntegral_le_integral hsumF.norm
        (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
    _ ≤ ∫ x, ∑' i, ‖F i x‖ ∂volume :=
      integral_mono_ae hsumF.norm hsumNorm hpoint
    _ = ∑' i, ∫ x, ‖F i x‖ ∂volume := by
      symm
      exact integral_tsum_of_summable_integral_norm
        (fun i ↦ (hFi i).norm) hnormFi_sum
    _ ≤ ∑' i, Real.pi * C * ∫ y, ‖b i y‖ ∂volume :=
      hFi_sum.tsum_le_tsum hFi_bound (hmass.mul_left (Real.pi * C))
    _ = Real.pi * C * ∑' i, ∫ y, ‖b i y‖ ∂volume := by
      rw [tsum_mul_left]

end

end HarmonicAnalysis

end JJMath
