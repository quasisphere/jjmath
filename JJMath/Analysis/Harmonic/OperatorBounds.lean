import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Weak and strong operator bounds

This file introduces the operator estimates used by the harmonic-analysis
layer. Weak type `(1,1)` is written in the division-free distribution-function
form `λ μ({‖Tf‖ ≥ λ}) ≤ C ∫ ‖f‖`. Strong type is expressed directly with
Mathlib's `eLpNorm`, so it remains meaningful before finiteness is known.
-/

namespace JJMath

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace HarmonicAnalysis

noncomputable section

/--
%%handwave
name:
  Distribution function
statement:
  For $f:\alpha\to E$ on $(\alpha,\mu)$, its distribution function is
  $d_f(\lambda)=\mu\{x:\lambda\leq|f(x)|\}$ for
  $\lambda\in[0,\infty]$.
-/
def distributionFunction
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (f : α → E) (μ : Measure α) (t : ENNReal) : ENNReal :=
  μ {x : α | t ≤ ‖f x‖ₑ}

/--
%%handwave
name:
  Almost-everywhere invariance of distribution functions
statement:
  If $f,g:X\to E$ agree almost everywhere, then for every
  $t\in[0,\infty]$,
  $$
    \mu\{x:t\leq\|f(x)\|\}=\mu\{x:t\leq\|g(x)\|\}.
  $$
proof:
  The two superlevel sets agree outside the null set on which $f$ and $g$
  may differ.
-/
theorem distributionFunction_congr_ae
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {f g : α → E} {μ : Measure α} (hfg : f =ᵐ[μ] g) (t : ENNReal) :
    distributionFunction f μ t = distributionFunction g μ t := by
  apply measure_congr
  filter_upwards [hfg] with x hx
  change (t ≤ ‖f x‖ₑ) = (t ≤ ‖g x‖ₑ)
  rw [hx]

/--
%%handwave
name:
  Layer-cake formula for a norm distribution
statement:
  Let $f:X\to E$ be strongly measurable almost everywhere and let $p>0$.
  Then
  $$
    \int_X\|f(x)\|^p\,d\mu(x)
      =p\int_0^\infty t^{p-1}d_f(t)\,dt,
    \qquad d_f(t)=\mu\{x:t\leq\|f(x)\|\},
  $$
  with both sides interpreted in $[0,\infty]$.
proof:
  Apply the layer-cake formula for a positive real power to the nonnegative
  measurable function $x\mapsto\|f(x)\|$, then identify real thresholds and
  norms with their extended nonnegative-real images.
-/
theorem lintegral_enorm_rpow_eq_lintegral_distributionFunction
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (f : α → E) (μ : Measure α) (hf : AEStronglyMeasurable f μ)
    {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) = ENNReal.ofReal p *
      ∫⁻ t in Set.Ioi (0 : ℝ),
        distributionFunction f μ (ENNReal.ofReal t) *
          ENNReal.ofReal (t ^ (p - 1)) := by
  have hlayer := lintegral_rpow_eq_lintegral_meas_le_mul μ
    (f := fun x ↦ ‖f x‖) (Eventually.of_forall fun x ↦ norm_nonneg (f x))
    hf.norm.aemeasurable hp
  have hsets : ∀ t : ℝ,
      μ {x | t ≤ ‖f x‖} =
        distributionFunction f μ (ENNReal.ofReal t) := by
    intro t
    simp only [distributionFunction]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, ← ofReal_norm,
      ENNReal.ofReal_le_ofReal_iff (norm_nonneg (f x))]
  simp_rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f _)) hp.le,
    ofReal_norm, hsets] at hlayer
  exact hlayer

/--
%%handwave
name:
  Distribution bound for a sum at half threshold
statement:
  For functions $f,g:X\to E$ and every $t\in[0,\infty]$,
  $$
    \mu\{x:t\leq|f(x)+g(x)|\}
      \leq\mu\{x:t/2\leq|f(x)|\}
        +\mu\{x:t/2\leq|g(x)|\}.
  $$
proof:
  If both summands have norm strictly below $t/2$, the triangle inequality
  makes the norm of their sum strictly below $t$. Thus the $t$-superlevel set
  of the sum is contained in the union of the two half-threshold superlevel
  sets.
-/
theorem distributionFunction_add_le_half
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (f g : α → E) (μ : Measure α) (t : ENNReal) :
    distributionFunction (f + g) μ t ≤
      distributionFunction f μ (t / 2) +
        distributionFunction g μ (t / 2) := by
  calc
    distributionFunction (f + g) μ t ≤
        μ ({x | t / 2 ≤ ‖f x‖ₑ} ∪ {x | t / 2 ≤ ‖g x‖ₑ}) := by
      apply measure_mono
      intro x hx
      by_contra hxu
      simp only [mem_union, mem_setOf_eq, not_or, not_le] at hxu
      have hlt : ‖(f + g) x‖ₑ < t := by
        rw [Pi.add_apply]
        calc
          ‖f x + g x‖ₑ ≤ ‖f x‖ₑ + ‖g x‖ₑ := enorm_add_le _ _
          _ < t / 2 + t / 2 := ENNReal.add_lt_add_of_lt_of_le
            (ne_top_of_lt hxu.2) hxu.1 hxu.2.le
          _ = t := ENNReal.add_halves t
      exact (not_lt_of_ge hx) hlt
    _ ≤ μ {x | t / 2 ≤ ‖f x‖ₑ} + μ {x | t / 2 ≤ ‖g x‖ₑ} :=
      measure_union_le _ _

/--
%%handwave
name:
  Squared $L^2$ norm as an integral
statement:
  If $f:\alpha\to E$ belongs to $L^2(\mu)$, then its class in
  $L^2(\mu;E)$ satisfies
  $$
    \|[f]\|_{L^2}^2=\int_\alpha\|f(x)\|^2\,d\mu(x).
  $$
proof:
  The definition of the $L^2$ norm is the square root of the integral on the
  right. The integral is nonnegative, so squaring recovers it.
-/
theorem norm_toLp_two_sq_eq_integral_norm_sq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ :=
    integral_nonneg fun x ↦ sq_nonneg ‖f x‖
  rw [Lp.norm_toLp]
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_ofReal]
  simp only [Real.rpow_two]
  exact Real.rpow_inv_natCast_pow hnonneg (by norm_num : (2 : ℕ) ≠ 0)
  exact Real.rpow_nonneg
    (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg (f x)) _) _

/--
%%handwave
name:
  Squared finite $L^2$ seminorm as an integral
statement:
  If $f\in L^2(\mu;E)$, then
  $$
    \|f\|_{L^2(\mu)}^2
      =\int\|f(x)\|^2\,d\mu(x).
  $$
proof:
  The real value of the finite $L^2$ seminorm is the norm of the associated
  $L^2$ equivalence class. Apply the integral formula for the square of that
  norm.
-/
theorem eLpNorm_two_toReal_sq_eq_integral_norm_sq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ (2 : ℕ) =
      ∫ x, ‖f x‖ ^ (2 : ℕ) ∂μ := by
  rw [← Lp.norm_toLp f hf]
  exact norm_toLp_two_sq_eq_integral_norm_sq hf

/--
%%handwave
name:
  Vanishing weak distribution bounds imply convergence in measure
statement:
  Let $F_i:X\to E$, let $m_i\in[0,\infty]$, and suppose $m_i\to0$ along a
  filter. If $C<\infty$ and, for every finite $t>0$,
  $$
    t\,\mu\{x:t\leq\|F_i(x)\|\}\leq C m_i,
  $$
  then $F_i\to0$ in measure.
proof:
  Divide the distribution estimate by the positive finite threshold $t$.
  The resulting upper bound $Cm_i/t$ tends to zero, so the superlevel
  measures tend to zero by squeezing.
-/
theorem tendstoInMeasure_zero_of_weak_distribution_bound
    {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {u : Filter ι} {F : ι → α → E}
    {mass : ι → ENNReal} {C : ENNReal}
    (hC : C ≠ ∞) (hmass : Tendsto mass u (𝓝 0))
    (hweak : ∀ i t, t ≠ 0 → t ≠ ∞ →
      t * distributionFunction (F i) μ t ≤ C * mass i) :
    TendstoInMeasure μ F u 0 := by
  rw [tendstoInMeasure_iff_enorm]
  intro t ht httop
  have hCmass : Tendsto (fun i ↦ C * mass i) u (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hmass (Or.inr hC)
  have hupper : Tendsto (fun i ↦ C * mass i / t) u (𝓝 0) := by
    simpa using ENNReal.Tendsto.div_const hCmass (Or.inr ht.ne')
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hupper (fun _ ↦ zero_le) (fun i ↦ ?_)
  apply (ENNReal.le_div_iff_mul_le (Or.inl ht.ne') (Or.inl httop)).2
  rw [mul_comm]
  simpa only [Pi.zero_apply, sub_zero, distributionFunction] using
    hweak i t ht.ne' httop

/--
%%handwave
name:
  Weak distribution bounds pass to almost-everywhere limits
statement:
  Let $F_n:X\to E$ converge almost everywhere to $F$, let $m_n\to m$ in
  $[0,\infty]$, and let $C<\infty$. Suppose that for every finite $s>0$,
  $$
    s\,\mu\{x:s\leq|F_n(x)|\}\leq C m_n.
  $$
  Then the limit satisfies the same estimate with no loss in the constant:
  $$
    s\,\mu\{x:s\leq|F(x)|\}\leq C m.
  $$
proof:
  Fix $0<a<1$. Almost-everywhere convergence puts the $s$-superlevel set
  of $F$ inside the eventual $(as)$-superlevel set of the sequence. Write
  that eventual set as the increasing union of tail intersections. Every
  tail intersection lies in every later superlevel set, so its measure obeys
  the required bound after passing $m_n\to m$. Continuity of measure from
  below handles the increasing union. Finally let $a\uparrow1$.
-/
theorem weak_distribution_bound_of_tendsto_ae
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {F : ℕ → α → E} {G : α → E}
    {mass : ℕ → ENNReal} {massLimit C : ENNReal}
    (hC : C ≠ ∞)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ F n x) atTop (𝓝 (G x)))
    (hmass : Tendsto mass atTop (𝓝 massLimit))
    (hweak : ∀ n t, t ≠ 0 → t ≠ ∞ →
      t * distributionFunction (F n) μ t ≤ C * mass n)
    {t : ENNReal} (ht0 : t ≠ 0) (httop : t ≠ ∞) :
    t * distributionFunction G μ t ≤ C * massLimit := by
  apply ENNReal.le_of_forall_lt_one_mul_le
  intro a ha
  by_cases ha0 : a = 0
  · simp only [ha0, zero_mul, zero_le]
  have hatop : a ≠ ∞ := ne_top_of_lt (ha.trans ENNReal.one_lt_top)
  have hat0 : a * t ≠ 0 := mul_ne_zero ha0 ht0
  have hattop : a * t ≠ ∞ := ENNReal.mul_ne_top hatop httop
  have hat_lt : a * t < t := by
    simpa only [one_mul] using ENNReal.mul_lt_mul_left ht0 httop ha
  let B : ℕ → Set α := fun n ↦ {x | a * t ≤ ‖F n x‖ₑ}
  let tail : ℕ → Set α := fun N ↦ ⋂ n, ⋂ (_ : N ≤ n), B n
  have htail_mono : Monotone tail := by
    intro N M hNM x hx
    simp only [tail, Set.mem_iInter] at hx ⊢
    intro n hMn
    exact hx n (hNM.trans hMn)
  have hsubset : {x | t ≤ ‖G x‖ₑ} ≤ᶠ[ae μ] ⋃ N, tail N := by
    filter_upwards [hlim] with x hx hxt
    have hnorm := hx.enorm
    have hev : ∀ᶠ n in atTop, a * t ≤ ‖F n x‖ₑ :=
      ((tendsto_order.mp hnorm).1 (a * t) (hat_lt.trans_le hxt)).mono
        fun _ hn ↦ hn.le
    rcases (eventually_atTop.1 hev) with ⟨N, hN⟩
    apply Set.mem_iUnion.2
    refine ⟨N, ?_⟩
    simp only [tail, Set.mem_iInter]
    intro n hNn
    exact hN n hNn
  have hCmass : Tendsto (fun n ↦ C * mass n) atTop (𝓝 (C * massLimit)) := by
    exact ENNReal.Tendsto.const_mul hmass (Or.inr hC)
  have htail_bound : ∀ N, (a * t) * μ (tail N) ≤ C * massLimit := by
    intro N
    apply ge_of_tendsto hCmass
    filter_upwards [eventually_ge_atTop N] with n hNn
    calc
      (a * t) * μ (tail N) ≤ (a * t) * μ (B n) := by
        gcongr
        exact Set.iInter₂_subset n hNn
      _ ≤ C * mass n := hweak n (a * t) hat0 hattop
  have hmeasure := tendsto_measure_iUnion_atTop (μ := μ) htail_mono
  have hscaled : Tendsto (fun N ↦ (a * t) * μ (tail N)) atTop
      (𝓝 ((a * t) * μ (⋃ N, tail N))) := by
    exact ENNReal.Tendsto.const_mul hmeasure (Or.inr hattop)
  have hunion : (a * t) * μ (⋃ N, tail N) ≤ C * massLimit :=
    le_of_tendsto hscaled (Eventually.of_forall htail_bound)
  rw [← mul_assoc, distributionFunction]
  exact (mul_le_mul_right (measure_mono_ae hsubset) (a * t)).trans hunion

/--
%%handwave
name:
  Dominated convergence in $L^2$
statement:
  Let $a\in L^2(\mu;E)$ and let $b_n:\alpha\to F$ be measurable. Suppose
  $b_n(x)\to0$ for almost every $x$ and
  $$
    |b_n(x)|\leq C|a(x)|
  $$
  almost everywhere for every $n$. Then every $b_n$ belongs to $L^2(\mu)$
  and $\|b_n\|_{L^2(\mu)}\to0$.
proof:
  The squared norms converge pointwise to zero and are dominated by the
  integrable function $C^2|a|^2$. Dominated convergence makes their
  integrals tend to zero. Taking square roots and using the integral formula
  for the $L^2$ seminorm gives the conclusion.
-/
theorem memLp_two_and_eLpNorm_tendsto_zero_of_ae_tendsto_of_norm_le_mul
    {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure α} {a : α → E} {b : ℕ → α → F} {C : ℝ}
    (ha : MemLp a 2 μ)
    (hb_meas : ∀ n, AEStronglyMeasurable (b n) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖b n x‖ ≤ C * ‖a x‖)
    (hb_zero : ∀ᵐ x ∂μ,
      Filter.Tendsto (fun n ↦ b n x) Filter.atTop (𝓝 0)) :
    (∀ n, MemLp (b n) 2 μ) ∧
      Filter.Tendsto (fun n ↦ eLpNorm (b n) 2 μ)
        Filter.atTop (𝓝 0) := by
  have hb_mem : ∀ n, MemLp (b n) 2 μ := fun n ↦
    ha.of_le_mul (hb_meas n) (hbound n)
  have ha_sq_int : Integrable (fun x ↦ ‖a x‖ ^ (2 : ℕ)) μ :=
    (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).1 ha
  have hdom_int : Integrable
      (fun x ↦ C ^ (2 : ℕ) * ‖a x‖ ^ (2 : ℕ)) μ :=
    ha_sq_int.const_mul _
  have hsq_meas : ∀ n, AEStronglyMeasurable
      (fun x ↦ ‖b n x‖ ^ (2 : ℕ)) μ := fun n ↦
    (hb_meas n).norm.pow _
  have hsq_bound : ∀ n, ∀ᵐ x ∂μ,
      ‖‖b n x‖ ^ (2 : ℕ)‖ ≤
        C ^ (2 : ℕ) * ‖a x‖ ^ (2 : ℕ) := by
    intro n
    filter_upwards [hbound n] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (b n x), norm_nonneg (a x)]
  have hsq_zero : ∀ᵐ x ∂μ,
      Filter.Tendsto (fun n ↦ ‖b n x‖ ^ (2 : ℕ))
        Filter.atTop (𝓝 0) := by
    filter_upwards [hb_zero] with x hx
    simpa using hx.norm.pow 2
  have hint : Filter.Tendsto
      (fun n ↦ ∫ x, ‖b n x‖ ^ (2 : ℕ) ∂μ)
      Filter.atTop (𝓝 0) := by
    simpa using
      (tendsto_integral_of_dominated_convergence
        (μ := μ) (F := fun n x ↦ ‖b n x‖ ^ (2 : ℕ))
        (f := fun _ ↦ (0 : ℝ))
        (fun x ↦ C ^ (2 : ℕ) * ‖a x‖ ^ (2 : ℕ))
        hsq_meas hdom_int hsq_bound hsq_zero)
  have hreal : Filter.Tendsto
      (fun n ↦ (eLpNorm (b n) 2 μ).toReal)
      Filter.atTop (𝓝 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hint
    simp only [Real.sqrt_zero] at hsqrt
    convert hsqrt using 1
    funext n
    calc
      (eLpNorm (b n) 2 μ).toReal =
          Real.sqrt ((eLpNorm (b n) 2 μ).toReal ^ (2 : ℕ)) :=
        (Real.sqrt_sq ENNReal.toReal_nonneg).symm
      _ = Real.sqrt (∫ x, ‖b n x‖ ^ (2 : ℕ) ∂μ) := by
        rw [eLpNorm_two_toReal_sq_eq_integral_norm_sq (hb_mem n)]
  refine ⟨hb_mem, ?_⟩
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun n ↦ (hb_mem n).eLpNorm_lt_top.ne)).mp hreal

end

end HarmonicAnalysis

end JJMath
