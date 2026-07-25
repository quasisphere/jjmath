import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Completeness tools for convergence in measure

This file develops the two structural facts needed to extend weak-type
operators by density. Convergence in measure is stable under addition, and a
sequence which is Cauchy in measure has a rapidly convergent subsequence. On
a finite measure space the latter yields a limit in measure for the entire
sequence.
-/

namespace JJMath

open Set MeasureTheory Filter
open scoped ENNReal Topology BigOperators

noncomputable section

/--
%%handwave
name:
  Addition preserves convergence in measure
statement:
  Let $f_i,g_i:X\to E$, where $E$ is a normed additive group. If
  $f_i\to f$ and $g_i\to g$ in measure along the same filter, then
  $f_i+g_i\to f+g$ in measure.
proof:
  If $|(f_i-f)+(g_i-g)|\geq t$, then at least one summand has norm at least
  $t/2$. The exceptional measure is therefore bounded by the sum of the two
  half-threshold exceptional measures, both of which tend to zero.
-/
theorem tendstoInMeasure_add
    {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {u : Filter ι}
    {f h : ι → α → E} {g k : α → E}
    (hf : TendstoInMeasure μ f u g) (hh : TendstoInMeasure μ h u k) :
    TendstoInMeasure μ (fun i ↦ f i + h i) u (g + k) := by
  rw [tendstoInMeasure_iff_enorm]
  intro t ht httop
  have ht2 : 0 < t / 2 := ENNReal.div_pos ht.ne' (by norm_num)
  have ht2top : t / 2 ≠ ∞ := ENNReal.div_ne_top httop (by norm_num)
  have hf2 := (tendstoInMeasure_iff_enorm.mp hf) (t / 2) ht2 ht2top
  have hh2 := (tendstoInMeasure_iff_enorm.mp hh) (t / 2) ht2 ht2top
  have hsum : Tendsto
      (fun i ↦ μ {x | t / 2 ≤ ‖f i x - g x‖ₑ} +
        μ {x | t / 2 ≤ ‖h i x - k x‖ₑ}) u (𝓝 0) := by
    simpa using hf2.add hh2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hsum (fun _ ↦ zero_le) (fun i ↦ ?_)
  calc
    μ {x | t ≤ ‖(f i + h i) x - (g + k) x‖ₑ} ≤
        μ ({x | t / 2 ≤ ‖f i x - g x‖ₑ} ∪
          {x | t / 2 ≤ ‖h i x - k x‖ₑ}) := by
      apply measure_mono
      intro x hx
      by_contra hxu
      simp only [mem_union, mem_setOf_eq, not_or, not_le] at hxu
      have hlt : ‖(f i + h i) x - (g + k) x‖ₑ < t := by
        rw [show (f i + h i) x - (g + k) x =
          (f i x - g x) + (h i x - k x) by
            simp only [Pi.add_apply]
            abel]
        calc
          ‖(f i x - g x) + (h i x - k x)‖ₑ ≤
              ‖f i x - g x‖ₑ + ‖h i x - k x‖ₑ := enorm_add_le _ _
          _ < t / 2 + t / 2 := ENNReal.add_lt_add_of_lt_of_le
            (ne_top_of_lt hxu.2) hxu.1 hxu.2.le
          _ = t := ENNReal.add_halves t
      exact (not_lt_of_ge hx) hlt
    _ ≤ μ {x | t / 2 ≤ ‖f i x - g x‖ₑ} +
        μ {x | t / 2 ≤ ‖h i x - k x‖ₑ} := measure_union_le _ _

/--
%%handwave
name:
  Negation preserves convergence in measure
statement:
  If $f_i\to f$ in measure in a normed additive group, then
  $-f_i\to-f$ in measure.
proof:
  The error is negated and therefore has exactly the same norm, so all
  exceptional sets are unchanged.
-/
theorem tendstoInMeasure_neg
    {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {u : Filter ι} {f : ι → α → E} {g : α → E}
    (hf : TendstoInMeasure μ f u g) :
    TendstoInMeasure μ (fun i ↦ -f i) u (-g) := by
  rw [tendstoInMeasure_iff_enorm] at hf ⊢
  intro t ht httop
  simpa only [Pi.neg_apply, neg_sub_neg, enorm_sub_rev] using hf t ht httop

/--
%%handwave
name:
  Subtraction preserves convergence in measure
statement:
  If $f_i\to f$ and $g_i\to g$ in measure along the same filter, then
  $f_i-g_i\to f-g$ in measure.
proof:
  Combine preservation under negation with preservation under addition.
-/
theorem tendstoInMeasure_sub
    {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {u : Filter ι}
    {f h : ι → α → E} {g k : α → E}
    (hf : TendstoInMeasure μ f u g) (hh : TendstoInMeasure μ h u k) :
    TendstoInMeasure μ (fun i ↦ f i - h i) u (g - k) := by
  simpa only [sub_eq_add_neg] using tendstoInMeasure_add hf (tendstoInMeasure_neg hh)

/--
%%handwave
name:
  Fixed scalar multiplication preserves convergence in measure
statement:
  Let $f_i,g:X\to E$, where $E$ is a normed space over a normed division
  ring. If $f_i\to g$ in measure, then for every fixed scalar $c$,
  $$
    c f_i\longrightarrow c g
  $$
  in measure.
proof:
  The case $c=0$ is immediate. If $c\ne0$, the exceptional set at threshold
  $t$ after multiplication by $c$ is exactly the original exceptional set at
  threshold $t/|c|$.
-/
theorem tendstoInMeasure_const_smul
    {α E 𝕜 ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedField 𝕜] [NormedSpace 𝕜 E]
    {μ : Measure α} {u : Filter ι} {f : ι → α → E} {g : α → E}
    (c : 𝕜) (hf : TendstoInMeasure μ f u g) :
    TendstoInMeasure μ (fun i ↦ c • f i) u (c • g) := by
  rw [tendstoInMeasure_iff_norm] at hf ⊢
  intro ε hε
  by_cases hc : c = 0
  · simpa [hc, not_le_of_gt hε] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ENNReal)) u (𝓝 0))
  have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hscaled := hf (ε / ‖c‖) (div_pos hε hcnorm)
  refine Tendsto.congr' ?_ hscaled
  filter_upwards with i
  apply congrArg μ
  ext x
  simp only [Pi.smul_apply, ← smul_sub, norm_smul]
  simpa only [mul_comm] using
    (div_le_iff₀ hcnorm : ε / ‖c‖ ≤ ‖f i x - g x‖ ↔
      ε ≤ ‖f i x - g x‖ * ‖c‖)

/--
%%handwave
name:
  Convergence in measure for a dominated measure
statement:
  If $\nu\leq\mu$ and $f_i\to f$ in measure with respect to $\mu$, then
  $f_i\to f$ in measure with respect to $\nu$.
proof:
  Every exceptional set has $\nu$-measure at most its $\mu$-measure, so its
  $\nu$-measure tends to zero by squeezing.
-/
theorem tendstoInMeasure_mono_measure
    {α E ι : Type*} [MeasurableSpace α] [EDist E]
    {μ ν : Measure α} {f : ι → α → E} {g : α → E} {u : Filter ι}
    (hνμ : ν ≤ μ) (h : TendstoInMeasure μ f u g) :
    TendstoInMeasure ν f u g := by
  intro ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h ε hε) (fun _ ↦ bot_le) (fun i ↦ hνμ _)

/--
%%handwave
name:
  Almost-everywhere convergent subsequence of a sequence Cauchy in measure
statement:
  Let $E$ be a complete normed additive group and let $f_n:X\to E$ be
  strongly measurable almost everywhere. If
  $$
    f_n-f_m\longrightarrow0
  $$
  in measure as $n,m\to\infty$, then there are a strongly measurable
  $g:X\to E$ and a strictly increasing sequence $n_k$ such that
  $f_{n_k}(x)\to g(x)$ for almost every $x$.
proof:
  Choose $n_k$ so that the measure of
  $\{|f_{n_{k+1}}-f_{n_k}|\geq2^{-k}\}$ is at most $2^{-k}$.
  Borel--Cantelli makes these exceptional events occur only finitely often
  almost everywhere. Hence the consecutive pointwise distances are bounded
  by a summable geometric series, so completeness of $E$ gives a pointwise
  limit. An almost-everywhere limit of strongly measurable functions is
  strongly measurable almost everywhere.
-/
theorem exists_strictMono_tendsto_ae_of_cauchyInMeasure
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [CompleteSpace E] {μ : Measure α} {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hc : TendstoInMeasure μ
      (fun nm : ℕ × ℕ ↦ f nm.1 - f nm.2) (atTop ×ˢ atTop) 0) :
    ∃ g : α → E, AEStronglyMeasurable g μ ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        ∀ᵐ x ∂μ, Tendsto (fun k ↦ f (ns k) x) atTop (𝓝 (g x)) := by
  let q : ℕ → ENNReal := fun k ↦ (2 : ENNReal)⁻¹ ^ k
  have hqpos (k : ℕ) : 0 < q k := by
    simp only [q]
    exact ENNReal.pow_pos (by simp) _
  have hN_exists : ∀ k, ∃ N : ℕ, ∀ n m, N ≤ n → N ≤ m →
      μ {x | q k ≤ ‖f n x - f m x‖ₑ} ≤ q k := by
    intro k
    have hev := (ENNReal.tendsto_nhds_zero.mp (hc (q k) (hqpos k)))
      (q k) (hqpos k)
    rw [Filter.prod_atTop_atTop_eq] at hev
    rw [Filter.eventually_atTop_prod_self] at hev
    rcases hev with ⟨N, hN⟩
    refine ⟨N, fun n m hn hm ↦ ?_⟩
    simpa only [Pi.sub_apply, Pi.zero_apply, edist_eq_enorm_sub, sub_zero] using
      hN n m hn hm
  choose N hN using hN_exists
  let ns : ℕ → ℕ := fun k ↦
    Nat.rec (N 0) (fun j previous ↦ max (N (j + 1)) (previous + 1)) k
  have hNns : ∀ k, N k ≤ ns k := by
    intro k
    cases k with
    | zero => exact le_refl (N 0)
    | succ k =>
        simp only [ns]
        exact le_max_left _ _
  have hns_strict : StrictMono ns := by
    apply strictMono_nat_of_lt_succ
    intro k
    simp only [ns]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  let A : ℕ → Set α := fun k ↦
    {x | q k ≤ ‖f (ns (k + 1)) x - f (ns k) x‖ₑ}
  have hA (k : ℕ) : μ (A k) ≤ q k := by
    apply hN k
    · exact hNns k |>.trans (hns_strict.monotone (Nat.le_succ k))
    · exact hNns k
  have hqtop : (∑' k, q k) ≠ ∞ := by
    simp only [q, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hAtop : (∑' k, μ (A k)) ≠ ∞ :=
    ne_top_of_le_ne_top hqtop (ENNReal.tsum_le_tsum hA)
  have hae_eventually : ∀ᵐ x ∂μ, ∀ᶠ k in atTop, x ∉ A k :=
    ae_eventually_notMem hAtop
  let g : α → E := fun x ↦ limUnder atTop (fun k ↦ f (ns k) x)
  have hsub_ae : ∀ᵐ x ∂μ,
      Tendsto (fun k ↦ f (ns k) x) atTop (𝓝 (g x)) := by
    filter_upwards [hae_eventually] with x hx
    rw [eventually_atTop] at hx
    rcases hx with ⟨K, hK⟩
    have hdist : ∀ k, K ≤ k →
        dist (f (ns k) x) (f (ns (k + 1)) x) < (q k).toReal := by
      intro k hk
      have hnot := hK k hk
      have henorm : ‖f (ns (k + 1)) x - f (ns k) x‖ₑ < q k := by
        simpa only [A, mem_setOf_eq, not_le] using hnot
      have hreal := (ENNReal.toReal_lt_toReal enorm_ne_top (by
        simp only [q]
        finiteness)).2 henorm
      simpa only [toReal_enorm, dist_eq_norm, norm_sub_rev] using hreal
    have hsummable : Summable fun k ↦
        dist (f (ns k) x) (f (ns (k + 1)) x) := by
      apply Summable.comp_nat_add (k := K)
      apply Summable.of_nonneg_of_le (fun k ↦ dist_nonneg)
      · intro k
        exact (hdist (k + K) (Nat.le_add_left K k)).le
      · simpa only [q, ENNReal.toReal_pow, ENNReal.toReal_inv,
          ENNReal.toReal_ofNat, one_div] using
          (summable_nat_add_iff K).2 summable_geometric_two
    exact (cauchySeq_of_summable_dist hsummable).tendsto_limUnder
  refine ⟨g, ?_, ns, hns_strict, hsub_ae⟩
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun k ↦ hf (ns k)) hsub_ae

/--
%%handwave
name:
  A convergent subsequence identifies the limit of a sequence Cauchy in measure
statement:
  Let $(X,\mu)$ have finite measure and let $f_n:X\to E$ be strongly
  measurable almost everywhere. Suppose $f_n-f_m\to0$ in measure as
  $n,m\to\infty$. If $n_k$ is strictly increasing and
  $f_{n_k}(x)\to g(x)$ almost everywhere, then $f_n\to g$ in measure.
proof:
  Almost-everywhere convergence of the subsequence implies convergence in
  measure because $\mu(X)<\infty$. The two-parameter Cauchy hypothesis gives
  $f_n-f_{n_k}\to0$ in measure along the diagonal pair $(n,n_k)$. Add the two
  convergences and use $f_n=(f_n-f_{n_k})+f_{n_k}$.
-/
theorem tendstoInMeasure_of_cauchyInMeasure_of_subseq_ae
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → E} {g : α → E}
    {ns : ℕ → ℕ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hc : TendstoInMeasure μ
      (fun nm : ℕ × ℕ ↦ f nm.1 - f nm.2) (atTop ×ˢ atTop) 0)
    (hns : StrictMono ns)
    (hsub_ae : ∀ᵐ x ∂μ,
      Tendsto (fun k ↦ f (ns k) x) atTop (𝓝 (g x))) :
    TendstoInMeasure μ f atTop g := by
  have hsub : TendstoInMeasure μ (fun n ↦ f (ns n)) atTop g :=
    tendstoInMeasure_of_tendsto_ae (fun n ↦ hf (ns n)) hsub_ae
  have hpair : Tendsto (fun n : ℕ ↦ (n, ns n)) atTop (atTop ×ˢ atTop) :=
    tendsto_id.prodMk hns.tendsto_atTop
  have hdiff : TendstoInMeasure μ (fun n ↦ f n - f (ns n)) atTop 0 := by
    simpa only [Function.comp_apply] using hc.comp hpair
  have hfull := tendstoInMeasure_add hdiff hsub
  simpa only [Pi.add_apply, Pi.sub_apply, sub_add_cancel, Pi.zero_apply, zero_add] using hfull

end

end JJMath
