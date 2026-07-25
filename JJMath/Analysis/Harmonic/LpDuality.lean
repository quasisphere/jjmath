import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Quantitative duality for scalar `Lᵖ` spaces

This file develops the norming-function truncations used to recover strong
`Lᵠ` membership from bounded integral pairings against `Lᵖ` test functions.
The first application is the Beurling transform above exponent two.
-/

namespace JJMath

open Set MeasureTheory Filter
open scoped ENNReal ComplexConjugate Topology

namespace HarmonicAnalysis

noncomputable section

/--
%%handwave
name:
  Complex $L^q$ norming value
statement:
  For $q\geq2$ and $z\in\mathbb C$, define
  $$
    N_q(z)=|z|^{q-2}\overline z.
  $$
  Multiplication by $z$ gives $|z|^q$, while
  $|N_q(z)|=|z|^{q-1}$.
-/
def complexLpNormingValue (q : ℝ) (z : ℂ) : ℂ :=
  ((‖z‖ ^ (q - 2) : ℝ) : ℂ) * starRingEnd ℂ z

/--
%%handwave
name:
  Continuity of the complex $L^q$ norming value
statement:
  If $q\geq2$, then the map
  $z\mapsto |z|^{q-2}\overline z$ is continuous on $\mathbb C$.
proof:
  The norm and complex conjugation are continuous, and the nonnegative real
  power $r\mapsto r^{q-2}$ is continuous because $q-2\geq0$.
-/
theorem continuous_complexLpNormingValue {q : ℝ} (hq : 2 ≤ q) :
    Continuous (complexLpNormingValue q) := by
  simpa only [complexLpNormingValue, Function.comp_apply] using
    (Complex.continuous_ofReal.comp
      (continuous_norm.rpow_const fun _ ↦ Or.inr (sub_nonneg.mpr hq))).mul
        Complex.continuous_conj

/--
%%handwave
name:
  Norm of the complex $L^q$ norming value
statement:
  If $q\geq2$, then every $z\in\mathbb C$ satisfies
  $$
    \bigl||z|^{q-2}\overline z\bigr|=|z|^{q-1}.
  $$
proof:
  Conjugation preserves the norm, and the real-power identity
  $|z|^{q-2}|z|=|z|^{q-1}$ is valid at zero because both exponents are
  nonnegative.
-/
theorem norm_complexLpNormingValue {q : ℝ} (hq : 2 ≤ q) (z : ℂ) :
    ‖complexLpNormingValue q z‖ = ‖z‖ ^ (q - 1) := by
  rw [complexLpNormingValue, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _),
    show starRingEnd ℂ z = conj z from rfl, Complex.norm_conj]
  nth_rewrite 2 [← Real.rpow_one ‖z‖]
  rw [← Real.rpow_add_of_nonneg (norm_nonneg z)
    (sub_nonneg.mpr hq) zero_le_one]
  have hexp : q - 2 + 1 = q - 1 := by linarith
  rw [hexp]

/--
%%handwave
name:
  Norming identity for a complex value
statement:
  If $q\geq2$, then every $z\in\mathbb C$ satisfies
  $$
    z\,N_q(z)=|z|^q,
    \qquad N_q(z)=|z|^{q-2}\overline z,
  $$
  where the nonnegative real number $|z|^q$ is viewed as complex.
proof:
  Use $z\overline z=|z|^2$ and combine the nonnegative real powers with
  exponents $q-2$ and $2$.
-/
theorem mul_complexLpNormingValue {q : ℝ} (hq : 2 ≤ q) (z : ℂ) :
    z * complexLpNormingValue q z = ((‖z‖ ^ q : ℝ) : ℂ) := by
  calc
    z * complexLpNormingValue q z =
        ((‖z‖ ^ (q - 2) : ℝ) : ℂ) * (z * starRingEnd ℂ z) := by
      rw [complexLpNormingValue]
      ac_rfl
    _ = ((‖z‖ ^ (q - 2) : ℝ) : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [show starRingEnd ℂ z = conj z from rfl, Complex.mul_conj',
        ← Complex.ofReal_pow]
    _ = ((‖z‖ ^ (q - 2) * ‖z‖ ^ 2 : ℝ) : ℂ) := by norm_num
    _ = ((‖z‖ ^ q : ℝ) : ℂ) := by
      rw [← Real.rpow_two,
        ← Real.rpow_add_of_nonneg (norm_nonneg z)
          (sub_nonneg.mpr hq) (by norm_num)]
      have hexp : q - 2 + 2 = q := by linarith
      rw [hexp]

/--
%%handwave
name:
  Finite-measure truncation set for an $L^q$ norming function
statement:
  On a sigma-finite measure space, for a function $h:X\to\mathbb C$ and
  $n\in\mathbb N$, define
  $$
    E_n=\{x:x\in S_n,\ |h(x)|\leq n\},
  $$
  where $(S_n)$ is the canonical increasing measurable finite-measure
  exhaustion.
-/
def lpNormingTruncationSet
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (h : α → ℂ) (n : ℕ) : Set α :=
  spanningSets μ n ∩ {x | ‖h x‖ ≤ n}

/--
%%handwave
name:
  Measurability of the norming truncation set
statement:
  If $h:X\to\mathbb C$ is strongly measurable, then every set
  $$E_n=S_n\cap\{|h|\leq n\}$$
  is measurable.
proof:
  The exhaustion set $S_n$ is measurable and the norm of a strongly
  measurable complex function is measurable.
-/
theorem measurableSet_lpNormingTruncationSet
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {h : α → ℂ} (hh : StronglyMeasurable h) (n : ℕ) :
    MeasurableSet (lpNormingTruncationSet μ h n) := by
  exact (measurableSet_spanningSets μ n).inter
    (measurableSet_le hh.norm.measurable measurable_const)

/--
%%handwave
name:
  Truncated complex $L^q$ norming function
statement:
  For $q\geq2$, a strongly measurable $h:X\to\mathbb C$, and
  $E_n=S_n\cap\{|h|\leq n\}$, define
  $$
    g_n(x)=\mathbf 1_{E_n}(x)|h(x)|^{q-2}\overline{h(x)}.
  $$
  This is bounded and supported on a finite-measure set.
-/
def complexLpNormingTruncation
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (q : ℝ) (h : α → ℂ) (n : ℕ) : α → ℂ :=
  (lpNormingTruncationSet μ h n).indicator
    (fun x ↦ complexLpNormingValue q (h x))

/--
%%handwave
name:
  Strong measurability of the truncated norming function
statement:
  If $q\geq2$ and $h:X\to\mathbb C$ is strongly measurable, then every
  truncated norming function
  $g_n=\mathbf 1_{E_n}|h|^{q-2}\overline h$ is strongly measurable.
proof:
  Compose $h$ with the continuous norming-value map and restrict the result
  to the measurable set $E_n$.
-/
theorem stronglyMeasurable_complexLpNormingTruncation
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {q : ℝ} (hq : 2 ≤ q) {h : α → ℂ} (hh : StronglyMeasurable h)
    (n : ℕ) :
    StronglyMeasurable (complexLpNormingTruncation μ q h n) := by
  exact ((continuous_complexLpNormingValue hq).comp_stronglyMeasurable hh).indicator
    (measurableSet_lpNormingTruncationSet hh n)

/--
%%handwave
name:
  Support of the truncated norming function
statement:
  The truncated norming function $g_n$ vanishes outside the finite-measure
  exhaustion set $S_n$.
proof:
  Its defining indicator set $E_n$ is contained in $S_n$.
-/
theorem complexLpNormingTruncation_eq_zero_of_not_mem_spanningSets
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {q : ℝ} {h : α → ℂ} {n : ℕ} {x : α}
    (hx : x ∉ spanningSets μ n) :
    complexLpNormingTruncation μ q h n x = 0 := by
  rw [complexLpNormingTruncation, Set.indicator_of_notMem]
  exact fun hx' ↦ hx hx'.1

/--
%%handwave
name:
  Pointwise bound for a truncated norming function
statement:
  If $q\geq2$, then for every $x\in X$ and $n\in\mathbb N$,
  $$
    |g_n(x)|\leq n^{q-1}.
  $$
proof:
  Outside $E_n$ the function is zero. On $E_n$, the norming-value formula
  gives $|g_n|=|h|^{q-1}$, which is at most $n^{q-1}$ because
  $|h|\leq n$ and $q-1\geq0$.
-/
theorem norm_complexLpNormingTruncation_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {q : ℝ} (hq : 2 ≤ q) {h : α → ℂ} (n : ℕ) (x : α) :
    ‖complexLpNormingTruncation μ q h n x‖ ≤ (n : ℝ) ^ (q - 1) := by
  by_cases hx : x ∈ lpNormingTruncationSet μ h n
  · rw [complexLpNormingTruncation, Set.indicator_of_mem hx,
      norm_complexLpNormingValue hq]
    exact Real.rpow_le_rpow (norm_nonneg (h x)) hx.2 (by linarith)
  · rw [complexLpNormingTruncation, Set.indicator_of_notMem hx, norm_zero]
    positivity

/--
%%handwave
name:
  Truncated norming functions belong to every finite $L^p$
statement:
  Let $q\geq2$. For every exponent $0<p<\infty$, every strongly measurable
  $h:X\to\mathbb C$, and every $n$, the truncated norming function
  $g_n=\mathbf 1_{E_n}|h|^{q-2}\overline h$ belongs to $L^p(X)$.
proof:
  The function is bounded by $n^{q-1}$ and supported on the finite-measure
  set $S_n$. Thus it belongs to $L^\infty$, and finite-measure support lowers
  the exponent to any finite $p$.
-/
theorem memLp_complexLpNormingTruncation
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {q : ℝ} (hq : 2 ≤ q) {h : α → ℂ} (hh : StronglyMeasurable h)
    (n : ℕ) (p : ENNReal) :
    MemLp (complexLpNormingTruncation μ q h n) p μ := by
  have htop : MemLp (complexLpNormingTruncation μ q h n) ∞ μ :=
    memLp_top_of_bound
      (stronglyMeasurable_complexLpNormingTruncation hq hh n).aestronglyMeasurable
      ((n : ℝ) ^ (q - 1))
      (ae_of_all μ (norm_complexLpNormingTruncation_le hq n))
  exact htop.mono_exponent_of_measure_support_ne_top
    (fun x hx ↦ complexLpNormingTruncation_eq_zero_of_not_mem_spanningSets hx)
    (measure_spanningSets_lt_top μ n).ne le_top

/--
%%handwave
name:
  Supported simple approximation of a truncated norming function
statement:
  Let $q\geq2$, let $h:X\to\mathbb C$ be strongly measurable, and let
  $g_n=\mathbf1_{E_n}|h|^{q-2}\overline h$. The $k$th supported simple
  approximation is obtained by applying the canonical range approximation
  to $g_n$ and then setting it equal to zero off $E_n$.
-/
def complexLpNormingTruncationApproximation
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (q : ℝ) (hq : 2 ≤ q) (h : α → ℂ) (hh : StronglyMeasurable h)
    (n k : ℕ) : SimpleFunc α ℂ :=
  let g := complexLpNormingTruncation μ q h n
  let hg := stronglyMeasurable_complexLpNormingTruncation
    (μ := μ) (h := h) hq hh n
  (SimpleFunc.approxOn g hg.measurable (Set.range g ∪ {0}) 0 (by simp) k).piecewise
    (lpNormingTruncationSet μ h n)
    (measurableSet_lpNormingTruncationSet hh n)
    (SimpleFunc.const α 0)

/--
%%handwave
name:
  Pointwise convergence of supported norming approximants
statement:
  For $q\geq2$ and strongly measurable $h:X\to\mathbb C$, the supported
  simple approximants $g_{n,k}$ converge pointwise to the truncated norming
  function $g_n$:
  $$g_{n,k}(x)\longrightarrow g_n(x)$$
  for every $x\in X$.
proof:
  On $E_n$ this is pointwise convergence of the canonical range-simple
  approximations. Off $E_n$, both the supported approximants and $g_n$ are
  identically zero.
-/
theorem tendsto_complexLpNormingTruncationApproximation
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {q : ℝ} (hq : 2 ≤ q) {h : α → ℂ} (hh : StronglyMeasurable h)
    (n : ℕ) (x : α) :
    Tendsto
      (fun k ↦ complexLpNormingTruncationApproximation μ q hq h hh n k x)
      Filter.atTop (𝓝 (complexLpNormingTruncation μ q h n x)) := by
  by_cases hx : x ∈ lpNormingTruncationSet μ h n
  · simp only [complexLpNormingTruncationApproximation,
      SimpleFunc.piecewise_apply,
      if_pos hx]
    exact SimpleFunc.tendsto_approxOn
      (stronglyMeasurable_complexLpNormingTruncation hq hh n).measurable
      (by simp) (subset_closure (by simp))
  · simp only [complexLpNormingTruncationApproximation,
      SimpleFunc.piecewise_apply, if_neg hx, SimpleFunc.const_apply]
    rw [complexLpNormingTruncation, Set.indicator_of_notMem hx]
    exact tendsto_const_nhds

/--
%%handwave
name:
  Uniform bound for supported norming approximants
statement:
  For $q\geq2$, every supported simple approximant satisfies
  $$
    |g_{n,k}(x)|\leq 2n^{q-1}
  $$
  for all $n,k$ and $x$.
proof:
  On $E_n$, a canonical range-simple approximant has norm at most twice the
  norm of its target, and $|g_n|\leq n^{q-1}$. Off $E_n$ it is zero.
-/
theorem norm_complexLpNormingTruncationApproximation_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {q : ℝ} (hq : 2 ≤ q) {h : α → ℂ} (hh : StronglyMeasurable h)
    (n k : ℕ) (x : α) :
    ‖complexLpNormingTruncationApproximation μ q hq h hh n k x‖ ≤
      2 * (n : ℝ) ^ (q - 1) := by
  by_cases hx : x ∈ lpNormingTruncationSet μ h n
  · rw [complexLpNormingTruncationApproximation,
      SimpleFunc.piecewise_apply, if_pos hx]
    calc
      ‖SimpleFunc.approxOn
          (complexLpNormingTruncation μ q h n)
          (stronglyMeasurable_complexLpNormingTruncation hq hh n).measurable
          (Set.range (complexLpNormingTruncation μ q h n) ∪ {0}) 0
          (by simp) k x‖
          ≤ ‖complexLpNormingTruncation μ q h n x‖ +
              ‖complexLpNormingTruncation μ q h n x‖ :=
        SimpleFunc.norm_approxOn_zero_le
          (stronglyMeasurable_complexLpNormingTruncation hq hh n).measurable
          (by simp) x k
      _ ≤ (n : ℝ) ^ (q - 1) + (n : ℝ) ^ (q - 1) :=
        add_le_add
          (norm_complexLpNormingTruncation_le hq n x)
          (norm_complexLpNormingTruncation_le hq n x)
      _ = 2 * (n : ℝ) ^ (q - 1) := by linarith
  · rw [complexLpNormingTruncationApproximation,
      SimpleFunc.piecewise_apply, if_neg hx, SimpleFunc.const_apply, norm_zero]
    positivity

/--
%%handwave
name:
  Finite-exponent integrability of supported norming approximants
statement:
  For $q\geq2$, every supported simple norming approximant $g_{n,k}$ belongs
  to $L^r(X)$ for every finite or infinite exponent $r$.
proof:
  The approximant is bounded by $2n^{q-1}$ and vanishes outside the
  finite-measure exhaustion set $S_n$.
-/
theorem memLp_complexLpNormingTruncationApproximation
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {q : ℝ} (hq : 2 ≤ q) {h : α → ℂ} (hh : StronglyMeasurable h)
    (n k : ℕ) (p : ENNReal) :
    MemLp
      (complexLpNormingTruncationApproximation μ q hq h hh n k : α → ℂ)
      p μ := by
  have htop : MemLp
      (complexLpNormingTruncationApproximation μ q hq h hh n k : α → ℂ)
      ∞ μ :=
    memLp_top_of_bound
      (complexLpNormingTruncationApproximation μ q hq h hh n k).aestronglyMeasurable
      (2 * (n : ℝ) ^ (q - 1))
      (ae_of_all μ (norm_complexLpNormingTruncationApproximation_le hq hh n k))
  exact htop.mono_exponent_of_measure_support_ne_top
    (fun x hx ↦ by
      rw [complexLpNormingTruncationApproximation,
        SimpleFunc.piecewise_apply, if_neg]
      · exact SimpleFunc.const_apply _ _
      · exact fun hx' ↦ hx hx'.1)
    (measure_spanningSets_lt_top μ n).ne le_top

/--
%%handwave
name:
  Convergence of pairings with supported norming approximants
statement:
  Let $q\geq2$ and let $h:X\to\mathbb C$ be strongly measurable. For each
  fixed truncation level $n$, the supported simple approximants satisfy
  $$
    \int_X h\,g_{n,k}\,d\mu
      \longrightarrow \int_X h\,g_n\,d\mu.
  $$
proof:
  The products converge pointwise. They vanish off $E_n$, while on $E_n$
  one has $|h|\leq n$ and $|g_{n,k}|\leq2n^{q-1}$. Thus a constant multiple
  of the indicator of the finite-measure set $S_n$ is an integrable
  dominating function.
-/
theorem tendsto_integral_mul_complexLpNormingTruncationApproximation
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {q : ℝ} (hq : 2 ≤ q) {h : α → ℂ} (hh : StronglyMeasurable h)
    (n : ℕ) :
    Tendsto
      (fun k ↦ ∫ x,
        h x * complexLpNormingTruncationApproximation μ q hq h hh n k x ∂μ)
      atTop
      (𝓝 (∫ x, h x * complexLpNormingTruncation μ q h n x ∂μ)) := by
  let C : ℝ := (n : ℝ) * (2 * (n : ℝ) ^ (q - 1))
  let bound : α → ℝ := (spanningSets μ n).indicator (fun _ ↦ C)
  apply tendsto_integral_of_dominated_convergence bound
  · intro k
    exact (hh.mul
      (complexLpNormingTruncationApproximation μ q hq h hh n k).measurable.stronglyMeasurable).aestronglyMeasurable
  · exact memLp_one_iff_integrable.mp
      (memLp_indicator_const 1 (measurableSet_spanningSets μ n) C
        (Or.inr (measure_spanningSets_lt_top μ n).ne))
  · intro k
    apply ae_of_all
    intro x
    by_cases hx : x ∈ lpNormingTruncationSet μ h n
    · dsimp only [bound, C]
      rw [Set.indicator_of_mem hx.1, norm_mul]
      exact mul_le_mul hx.2
        (norm_complexLpNormingTruncationApproximation_le hq hh n k x)
        (norm_nonneg _) (Nat.cast_nonneg n)
    · rw [complexLpNormingTruncationApproximation,
        SimpleFunc.piecewise_apply, if_neg hx, SimpleFunc.const_apply,
        mul_zero, norm_zero]
      exact Set.indicator_nonneg (fun _ _ ↦ by positivity) _
  · apply ae_of_all
    intro x
    exact tendsto_const_nhds.mul
      (tendsto_complexLpNormingTruncationApproximation hq hh n x)

/--
%%handwave
name:
  $L^p$ convergence of supported norming approximants
statement:
  Let $q\geq2$, let $h:X\to\mathbb C$ be strongly measurable, and let
  $p<\infty$. For every fixed truncation level $n$,
  $$
    \|g_{n,k}-g_n\|_p\longrightarrow0.
  $$
proof:
  Before restricting to $E_n$, the canonical range-simple approximants
  converge to $g_n$ in $L^p$. Restriction to $E_n$ does not increase the
  $L^p$ seminorm, and $g_n$ already vanishes off $E_n$.
-/
theorem eLpNorm_complexLpNormingTruncationApproximation_sub_tendsto_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {q : ℝ} (hq : 2 ≤ q) {h : α → ℂ} (hh : StronglyMeasurable h)
    (n : ℕ) (p : ENNReal) (hp : p ≠ ∞) :
    Tendsto
      (fun k ↦ eLpNorm
        ((complexLpNormingTruncationApproximation μ q hq h hh n k : α → ℂ) -
          complexLpNormingTruncation μ q h n) p μ)
      atTop (𝓝 0) := by
  let g := complexLpNormingTruncation μ q h n
  let hg := stronglyMeasurable_complexLpNormingTruncation
    (μ := μ) (h := h) hq hh n
  let A : ℕ → SimpleFunc α ℂ := fun k ↦
    SimpleFunc.approxOn g hg.measurable (Set.range g ∪ {0}) 0 (by simp) k
  have hraw : Tendsto
      (fun k ↦ eLpNorm ((A k : α → ℂ) - g) p μ) atTop (𝓝 0) := by
    exact SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm hp hg.measurable
      (memLp_complexLpNormingTruncation hq hh n p).2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hraw ?_ ?_
  · intro k
    exact bot_le
  · intro k
    apply eLpNorm_mono_ae
    apply ae_of_all
    intro x
    by_cases hx : x ∈ lpNormingTruncationSet μ h n
    · change ‖complexLpNormingTruncationApproximation μ q hq h hh n k x -
          complexLpNormingTruncation μ q h n x‖ ≤ ‖A k x - g x‖
      rw [complexLpNormingTruncationApproximation,
        SimpleFunc.piecewise_apply, if_pos hx]
    · change ‖complexLpNormingTruncationApproximation μ q hq h hh n k x -
          complexLpNormingTruncation μ q h n x‖ ≤ ‖A k x - g x‖
      rw [complexLpNormingTruncationApproximation,
        SimpleFunc.piecewise_apply, if_neg hx, SimpleFunc.const_apply,
        complexLpNormingTruncation, Set.indicator_of_notMem hx,
        zero_sub, neg_zero, norm_zero]
      exact norm_nonneg _

/--
%%handwave
name:
  Convergence of the norms of supported norming approximants
statement:
  Let $q\geq2$, let $h:X\to\mathbb C$ be strongly measurable, and let
  $1\leq p<\infty$. For every fixed truncation level $n$,
  $$
    \|g_{n,k}\|_p\longrightarrow\|g_n\|_p.
  $$
proof:
  The supported approximants converge to $g_n$ in $L^p$. Regard them as
  elements of the Banach space $L^p(X)$ and apply continuity of its norm.
-/
theorem lpNorm_complexLpNormingTruncationApproximation_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {q : ℝ} (hq : 2 ≤ q) {h : α → ℂ} (hh : StronglyMeasurable h)
    (n : ℕ) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Tendsto
      (fun k ↦ lpNorm
        (complexLpNormingTruncationApproximation μ q hq h hh n k : α → ℂ)
        p μ)
      atTop (𝓝 (lpNorm (complexLpNormingTruncation μ q h n) p μ)) := by
  let f : ℕ → α → ℂ := fun k ↦
    complexLpNormingTruncationApproximation μ q hq h hh n k
  let hf : ∀ k, MemLp (f k) p μ := fun k ↦
    memLp_complexLpNormingTruncationApproximation hq hh n k p
  let g := complexLpNormingTruncation μ q h n
  let hg : MemLp g p μ := memLp_complexLpNormingTruncation hq hh n p
  have hLp : Tendsto (fun k ↦ (hf k).toLp (f k)) atTop (𝓝 (hg.toLp g)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).2
      (eLpNorm_complexLpNormingTruncationApproximation_sub_tendsto_zero
        hq hh n p hp)
  have hnorm : Tendsto (fun k ↦ ‖(hf k).toLp (f k)‖) atTop
      (𝓝 ‖hg.toLp g‖) := continuous_norm.continuousAt.tendsto.comp hLp
  convert hnorm using 1
  · funext k
    rw [Lp.norm_toLp, toReal_eLpNorm (hf k).aestronglyMeasurable]
  · rw [Lp.norm_toLp, toReal_eLpNorm hg.aestronglyMeasurable]

/--
%%handwave
name:
  Pairing bound for an exact truncated norming function
statement:
  Suppose $p$ and $q$ are Hölder conjugate, $q\geq2$, and
  $h:X\to\mathbb C$ is strongly measurable. If every simple
  $s\in L^p(X)$ satisfies
  $$
    \left|\int_X hs\,d\mu\right|\leq C\|s\|_p,
  $$
  then every truncated norming function
  $g_n=\mathbf1_{E_n}|h|^{q-2}\overline h$ satisfies the same estimate.
proof:
  Apply the assumed estimate to the supported simple approximants
  $g_{n,k}$. Their pairings with $h$ and their $L^p$ norms converge to the
  corresponding quantities for $g_n$, so the inequality is closed under the
  limit.
-/
theorem norm_integral_mul_complexLpNormingTruncation_le_of_simpleFunc
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {p q C : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q)
    {h : α → ℂ} (hh : StronglyMeasurable h)
    (hpair : ∀ (s : SimpleFunc α ℂ),
      MemLp (s : α → ℂ) (ENNReal.ofReal p) μ →
        ‖∫ x, h x * s x ∂μ‖ ≤
          C * lpNorm (s : α → ℂ) (ENNReal.ofReal p) μ)
    (n : ℕ) :
    ‖∫ x, h x * complexLpNormingTruncation μ q h n x ∂μ‖ ≤
      C * lpNorm (complexLpNormingTruncation μ q h n)
        (ENNReal.ofReal p) μ := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr hpq.lt.le⟩
  have hleft : Tendsto
      (fun k ↦ ‖∫ x,
        h x * complexLpNormingTruncationApproximation μ q hq h hh n k x ∂μ‖)
      atTop
      (𝓝 ‖∫ x, h x * complexLpNormingTruncation μ q h n x ∂μ‖) :=
    continuous_norm.continuousAt.tendsto.comp
      (tendsto_integral_mul_complexLpNormingTruncationApproximation hq hh n)
  have hright : Tendsto
      (fun k ↦ C * lpNorm
        (complexLpNormingTruncationApproximation μ q hq h hh n k : α → ℂ)
        (ENNReal.ofReal p) μ)
      atTop
      (𝓝 (C * lpNorm (complexLpNormingTruncation μ q h n)
        (ENNReal.ofReal p) μ)) :=
    tendsto_const_nhds.mul
      (lpNorm_complexLpNormingTruncationApproximation_tendsto
        hq hh n (ENNReal.ofReal p) ENNReal.ofReal_ne_top)
  exact le_of_tendsto_of_tendsto' hleft hright fun k ↦
    hpair (complexLpNormingTruncationApproximation μ q hq h hh n k)
      (memLp_complexLpNormingTruncationApproximation
        hq hh n k (ENNReal.ofReal p))

/--
%%handwave
name:
  Pairing with a truncated complex norming function
statement:
  Let $q\geq2$, let $h:X\to\mathbb C$, and let
  $g_n=\mathbf 1_{E_n}|h|^{q-2}\overline h$. Then every $x\in X$ satisfies
  $$
    h(x)g_n(x)=\mathbf 1_{E_n}(x)|h(x)|^q,
  $$
  where the nonnegative value on the right is viewed as a complex number.
proof:
  On $E_n$ this is the scalar norming identity
  $z|z|^{q-2}\overline z=|z|^q$; off $E_n$ both sides vanish.
-/
theorem mul_complexLpNormingTruncation
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {q : ℝ} (hq : 2 ≤ q) (h : α → ℂ) (n : ℕ) (x : α) :
    h x * complexLpNormingTruncation μ q h n x =
      (lpNormingTruncationSet μ h n).indicator
        (fun y ↦ ((‖h y‖ ^ q : ℝ) : ℂ)) x := by
  by_cases hx : x ∈ lpNormingTruncationSet μ h n
  · rw [complexLpNormingTruncation, Set.indicator_of_mem hx,
      Set.indicator_of_mem hx, mul_complexLpNormingValue hq]
  · rw [complexLpNormingTruncation, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem hx, mul_zero]

/--
%%handwave
name:
  Integral form of the truncated norming pairing
statement:
  Let $q\geq2$ and let $h:X\to\mathbb C$. Then
  $$
    \int_X h g_n\,d\mu
      =\int_X\mathbf1_{E_n}|h|^q\,d\mu,
  $$
  where the real integral on the right is viewed as a complex number.
proof:
  The integrands agree pointwise by the norming identity. Integration of a
  real-valued function commutes with its inclusion into the complex numbers.
-/
theorem integral_mul_complexLpNormingTruncation
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {q : ℝ} (hq : 2 ≤ q) (h : α → ℂ) (n : ℕ) :
    ∫ x, h x * complexLpNormingTruncation μ q h n x ∂μ =
      ((∫ x, (lpNormingTruncationSet μ h n).indicator
        (fun y ↦ ‖h y‖ ^ q) x ∂μ : ℝ) : ℂ) := by
  calc
    (∫ x, h x * complexLpNormingTruncation μ q h n x ∂μ) =
        ∫ x, (((lpNormingTruncationSet μ h n).indicator
          (fun y ↦ ‖h y‖ ^ q) x : ℝ) : ℂ) ∂μ := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      change h x * complexLpNormingTruncation μ q h n x =
        (((lpNormingTruncationSet μ h n).indicator
          (fun y ↦ ‖h y‖ ^ q) x : ℝ) : ℂ)
      rw [mul_complexLpNormingTruncation hq h n]
      by_cases hx : x ∈ lpNormingTruncationSet μ h n <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
    _ = _ := integral_ofReal

/--
%%handwave
name:
  Power of the truncated norming function
statement:
  Suppose $p$ and $q$ are Hölder conjugate and $q\geq2$. For
  $g_n=\mathbf 1_{E_n}|h|^{q-2}\overline h$, every $x\in X$ satisfies
  $$
    |g_n(x)|^p=\mathbf 1_{E_n}(x)|h(x)|^q.
  $$
proof:
  On $E_n$, use $|g_n|=|h|^{q-1}$ and the conjugate-exponent identity
  $(q-1)p=q$. Off $E_n$ both sides are zero.
-/
theorem norm_rpow_complexLpNormingTruncation
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q)
    (h : α → ℂ) (n : ℕ) (x : α) :
    ‖complexLpNormingTruncation μ q h n x‖ ^ p =
      (lpNormingTruncationSet μ h n).indicator
        (fun y ↦ ‖h y‖ ^ q) x := by
  by_cases hx : x ∈ lpNormingTruncationSet μ h n
  · rw [complexLpNormingTruncation, Set.indicator_of_mem hx,
      Set.indicator_of_mem hx, norm_complexLpNormingValue hq,
      ← Real.rpow_mul (norm_nonneg (h x)), hpq.symm.sub_one_mul_conj]
  · rw [complexLpNormingTruncation, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem hx, norm_zero,
      Real.zero_rpow (ne_of_gt hpq.pos)]

/--
%%handwave
name:
  Exact $L^p$ norm of a truncated norming function
statement:
  Suppose $p$ and $q$ are Hölder conjugate, $q\geq2$, and
  $h:X\to\mathbb C$ is strongly measurable. For
  $g_n=\mathbf 1_{E_n}|h|^{q-2}\overline h$,
  $$
    \|g_n\|_p
      =\left(\int_X\mathbf 1_{E_n}|h|^q\,d\mu\right)^{1/p}.
  $$
proof:
  Use the integral formula for the finite real-valued $L^p$ seminorm and
  the pointwise identity $|g_n|^p=\mathbf 1_{E_n}|h|^q$.
-/
theorem lpNorm_complexLpNormingTruncation
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q)
    {h : α → ℂ} (hh : StronglyMeasurable h) (n : ℕ) :
    lpNorm (complexLpNormingTruncation μ q h n) (ENNReal.ofReal p) μ =
      (∫ x, (lpNormingTruncationSet μ h n).indicator
          (fun y ↦ ‖h y‖ ^ q) x ∂μ) ^ p⁻¹ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (ENNReal.ofReal_pos.mpr hpq.pos).ne' ENNReal.ofReal_ne_top
    (stronglyMeasurable_complexLpNormingTruncation hq hh n).aestronglyMeasurable,
    ENNReal.toReal_ofReal hpq.pos.le]
  congr 1
  apply integral_congr_ae
  exact ae_of_all μ (norm_rpow_complexLpNormingTruncation hpq hq h n)

/--
%%handwave
name:
  Truncated scalar inequality from bounded simple pairings
statement:
  Suppose $p$ and $q$ are Hölder conjugate, $q\geq2$, and
  $h:X\to\mathbb C$ is strongly measurable. If every simple
  $s\in L^p(X)$ satisfies
  $$
    \left|\int_X hs\,d\mu\right|\leq C\|s\|_p,
  $$
  then, for
  $A_n=\int_X\mathbf1_{E_n}|h|^q\,d\mu$,
  $$
    A_n\leq C A_n^{1/p}.
  $$
proof:
  Pass the simple-test estimate to the exact norming truncation $g_n$, then
  substitute the identities
  $\int hg_n=A_n$ and $\|g_n\|_p=A_n^{1/p}$.
-/
theorem integral_lpNormingTruncation_rpow_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {p q C : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q)
    {h : α → ℂ} (hh : StronglyMeasurable h)
    (hpair : ∀ (s : SimpleFunc α ℂ),
      MemLp (s : α → ℂ) (ENNReal.ofReal p) μ →
        ‖∫ x, h x * s x ∂μ‖ ≤
          C * lpNorm (s : α → ℂ) (ENNReal.ofReal p) μ)
    (n : ℕ) :
    let A := ∫ x, (lpNormingTruncationSet μ h n).indicator
      (fun y ↦ ‖h y‖ ^ q) x ∂μ
    A ≤ C * A ^ p⁻¹ := by
  dsimp only
  have hA : 0 ≤ ∫ x, (lpNormingTruncationSet μ h n).indicator
      (fun y ↦ ‖h y‖ ^ q) x ∂μ :=
    integral_nonneg fun x ↦ Set.indicator_nonneg
      (fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) x
  simpa only [integral_mul_complexLpNormingTruncation hq h n,
    Complex.norm_real, Real.norm_of_nonneg hA,
    lpNorm_complexLpNormingTruncation hpq hq hh n] using
      (norm_integral_mul_complexLpNormingTruncation_le_of_simpleFunc
        hpq hq hh hpair n)

/--
%%handwave
name:
  Solving the conjugate-power scalar inequality
statement:
  Let $p$ and $q$ be Hölder conjugate, let $A,C\geq0$, and suppose
  $$A\leq C A^{1/p}.$$
  Then
  $$A^{1/q}\leq C.$$
proof:
  If $A=0$, the conclusion follows from $C\geq0$. Otherwise divide by the
  positive number $A^{1/p}$ and use
  $1/q=1-1/p$.
-/
theorem rpow_inv_le_of_le_mul_rpow_inv
    {p q A C : ℝ} (hpq : p.HolderConjugate q)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (h : A ≤ C * A ^ p⁻¹) :
    A ^ q⁻¹ ≤ C := by
  rcases hA.eq_or_lt with (rfl | hApos)
  · rw [Real.zero_rpow hpq.symm.inv_ne_zero]
    exact hC
  · have hpowpos : 0 < A ^ p⁻¹ := Real.rpow_pos_of_pos hApos _
    have hdiv : A / A ^ p⁻¹ ≤ C := (div_le_iff₀ hpowpos).2 h
    calc
      A ^ q⁻¹ = A ^ (1 - p⁻¹) := by rw [hpq.one_sub_inv]
      _ = A ^ 1 / A ^ p⁻¹ := Real.rpow_sub hApos 1 p⁻¹
      _ = A / A ^ p⁻¹ := by rw [Real.rpow_one]
      _ ≤ C := hdiv

/--
%%handwave
name:
  Uniform conjugate-root bound on truncated $q$th moments
statement:
  Under the bounded simple-pairing hypothesis with $C\geq0$, every
  truncated moment
  $$A_n=\int_X\mathbf1_{E_n}|h|^q\,d\mu$$
  satisfies
  $$A_n^{1/q}\leq C.$$
proof:
  The norming test gives $A_n\leq C A_n^{1/p}$. Apply the scalar
  conjugate-power inequality.
-/
theorem integral_lpNormingTruncation_rpow_rpow_inv_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {p q C : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q)
    {h : α → ℂ} (hh : StronglyMeasurable h) (hC : 0 ≤ C)
    (hpair : ∀ (s : SimpleFunc α ℂ),
      MemLp (s : α → ℂ) (ENNReal.ofReal p) μ →
        ‖∫ x, h x * s x ∂μ‖ ≤
          C * lpNorm (s : α → ℂ) (ENNReal.ofReal p) μ)
    (n : ℕ) :
    (∫ x, (lpNormingTruncationSet μ h n).indicator
      (fun y ↦ ‖h y‖ ^ q) x ∂μ) ^ q⁻¹ ≤ C := by
  apply rpow_inv_le_of_le_mul_rpow_inv hpq
  · exact integral_nonneg fun x ↦ Set.indicator_nonneg
      (fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) x
  · exact hC
  · exact integral_lpNormingTruncation_rpow_le hpq hq hh hpair n

/--
%%handwave
name:
  Monotonicity of the norming truncation sets
statement:
  The sets
  $$E_n=S_n\cap\{|h|\leq n\}$$
  increase with $n$.
proof:
  Both the finite-measure exhaustion sets $S_n$ and the norm thresholds
  $\{|h|\leq n\}$ increase with $n$.
-/
theorem monotone_lpNormingTruncationSet
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (h : α → ℂ) :
    Monotone (lpNormingTruncationSet μ h) := by
  intro m n hmn x hx
  refine ⟨spanningSets_mono hmn hx.1, ?_⟩
  show ‖h x‖ ≤ (n : ℝ)
  exact hx.2.trans (Nat.cast_le.mpr hmn)

/--
%%handwave
name:
  Exhaustion by the norming truncation sets
statement:
  On a sigma-finite measure space, the increasing sets
  $$E_n=S_n\cap\{|h|\leq n\}$$
  exhaust the whole space:
  $$\bigcup_{n=0}^{\infty}E_n=X.$$
proof:
  Every point lies in some finite-measure exhaustion set $S_m$, and its
  finite norm is bounded by some natural number $k$. It then lies in
  $E_{\max(m,k)}$.
-/
theorem iUnion_lpNormingTruncationSet
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (h : α → ℂ) :
    ⋃ n, lpNormingTruncationSet μ h n = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  have hxS : x ∈ ⋃ n, spanningSets μ n := by
    rw [iUnion_spanningSets μ]
    exact Set.mem_univ x
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hxS
  obtain ⟨k, hk⟩ := exists_nat_ge ‖h x‖
  apply Set.mem_iUnion.mpr
  refine ⟨max m k, ?_⟩
  exact ⟨spanningSets_mono (le_max_left m k) hm,
    hk.trans (Nat.cast_le.mpr (le_max_right m k))⟩

/--
%%handwave
name:
  $L^r$ membership of the truncated original function
statement:
  If $h:X\to\mathbb C$ is strongly measurable, then
  $\mathbf1_{E_n}h$ belongs to $L^r(X)$ for every exponent
  $0\leq r\leq\infty$.
proof:
  On $E_n$ the function is bounded by $n$, and it vanishes outside the
  finite-measure exhaustion set $S_n$.
-/
theorem memLp_indicator_lpNormingTruncationSet
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {h : α → ℂ} (hh : StronglyMeasurable h) (n : ℕ) (r : ENNReal) :
    MemLp ((lpNormingTruncationSet μ h n).indicator h) r μ := by
  have htop : MemLp ((lpNormingTruncationSet μ h n).indicator h) ∞ μ :=
    memLp_top_of_bound
      (hh.indicator (measurableSet_lpNormingTruncationSet hh n)).aestronglyMeasurable
      n <| ae_of_all μ fun x ↦ by
        by_cases hx : x ∈ lpNormingTruncationSet μ h n
        · rw [Set.indicator_of_mem hx]
          exact hx.2
        · rw [Set.indicator_of_notMem hx, norm_zero]
          positivity
  exact htop.mono_exponent_of_measure_support_ne_top
    (fun x hx ↦ by
      rw [Set.indicator_of_notMem]
      exact fun hx' ↦ hx hx'.1)
    (measure_spanningSets_lt_top μ n).ne le_top

/--
%%handwave
name:
  Exact $L^q$ norm on a norming truncation set
statement:
  Let $q>0$ and let $h:X\to\mathbb C$ be strongly measurable. Then
  $$
    \|\mathbf1_{E_n}h\|_q
      =\left(\int_X\mathbf1_{E_n}|h|^q\,d\mu\right)^{1/q}.
  $$
proof:
  Apply the integral formula for the finite real-valued $L^q$ seminorm and
  move the norm and positive power through the indicator.
-/
theorem lpNorm_indicator_lpNormingTruncationSet
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {q : ℝ} (hq : 0 < q) {h : α → ℂ} (hh : StronglyMeasurable h)
    (n : ℕ) :
    lpNorm ((lpNormingTruncationSet μ h n).indicator h)
      (ENNReal.ofReal q) μ =
      (∫ x, (lpNormingTruncationSet μ h n).indicator
        (fun y ↦ ‖h y‖ ^ q) x ∂μ) ^ q⁻¹ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top
    (hh.indicator (measurableSet_lpNormingTruncationSet hh n)).aestronglyMeasurable,
    ENNReal.toReal_ofReal hq.le]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro x
  change ‖(lpNormingTruncationSet μ h n).indicator h x‖ ^ q =
    (lpNormingTruncationSet μ h n).indicator (fun y ↦ ‖h y‖ ^ q) x
  by_cases hx : x ∈ lpNormingTruncationSet μ h n
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
      norm_zero, Real.zero_rpow hq.ne']

/--
%%handwave
name:
  Quantitative $L^p$ duality from finite-support simple tests
statement:
  Let $(X,\mu)$ be sigma-finite, let $p$ and $q$ be Hölder conjugate with
  $q\geq2$, and let $h:X\to\mathbb C$ be strongly measurable. Suppose
  $C\geq0$ and every simple $s\in L^p(X)$ satisfies
  $$
    \left|\int_X h s\,d\mu\right|\leq C\|s\|_p.
  $$
  Then $h\in L^q(X)$ and
  $$\|h\|_q\leq C.$$
proof:
  Test first against supported simple approximations of
  $\mathbf1_{E_n}|h|^{q-2}\overline h$. This gives
  $\|\mathbf1_{E_n}h\|_q\leq C$ for every $n$. The increasing sets $E_n$
  exhaust $X$, so Fatou's lemma for $L^q$ seminorms gives the same bound for
  $h$.
-/
theorem memLp_and_lpNorm_le_of_simpleFunc_pairing
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {p q C : ℝ} (hpq : p.HolderConjugate q) (hq : 2 ≤ q)
    {h : α → ℂ} (hh : StronglyMeasurable h) (hC : 0 ≤ C)
    (hpair : ∀ (s : SimpleFunc α ℂ),
      MemLp (s : α → ℂ) (ENNReal.ofReal p) μ →
        ‖∫ x, h x * s x ∂μ‖ ≤
          C * lpNorm (s : α → ℂ) (ENNReal.ofReal p) μ) :
    MemLp h (ENNReal.ofReal q) μ ∧
      lpNorm h (ENNReal.ofReal q) μ ≤ C := by
  let f : ℕ → α → ℂ := fun n ↦
    (lpNormingTruncationSet μ h n).indicator h
  have hf : ∀ n, MemLp (f n) (ENNReal.ofReal q) μ := fun n ↦
    memLp_indicator_lpNormingTruncationSet hh n (ENNReal.ofReal q)
  have hnorm : ∀ n, lpNorm (f n) (ENNReal.ofReal q) μ ≤ C := by
    intro n
    rw [lpNorm_indicator_lpNormingTruncationSet hpq.symm.pos hh n]
    exact integral_lpNormingTruncation_rpow_rpow_inv_le
      hpq hq hh hC hpair n
  have henorm : ∀ n, eLpNorm (f n) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C := by
    intro n
    rw [← ofReal_lpNorm (hf n)]
    exact ENNReal.ofReal_le_ofReal (hnorm n)
  have heventually_mem (x : α) :
      ∀ᶠ n in atTop, x ∈ lpNormingTruncationSet μ h n := by
    have hxU : x ∈ ⋃ n, lpNormingTruncationSet μ h n := by
      rw [iUnion_lpNormingTruncationSet μ h]
      exact Set.mem_univ x
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxU
    filter_upwards [eventually_ge_atTop n] with m hnm
    exact monotone_lpNormingTruncationSet μ h hnm hn
  have htendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (h x)) := by
    apply ae_of_all
    intro x
    exact tendsto_const_nhds.congr' <|
      (heventually_mem x).mono fun n hn ↦
        (Set.indicator_of_mem hn h).symm
  have heLpNorm : eLpNorm h (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C :=
    Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall henorm)
      (fun n ↦ (hf n).aestronglyMeasurable) htendsto
  have hmem : MemLp h (ENNReal.ofReal q) μ :=
    ⟨hh.aestronglyMeasurable,
      lt_of_le_of_lt heLpNorm ENNReal.ofReal_lt_top⟩
  refine ⟨hmem, ?_⟩
  calc
    lpNorm h (ENNReal.ofReal q) μ =
        (eLpNorm h (ENNReal.ofReal q) μ).toReal :=
      (toReal_eLpNorm hh.aestronglyMeasurable).symm
    _ ≤ (ENNReal.ofReal C).toReal :=
      (ENNReal.toReal_le_toReal hmem.eLpNorm_ne_top ENNReal.ofReal_ne_top).2
        heLpNorm
    _ = C := ENNReal.toReal_ofReal hC

end

end HarmonicAnalysis

end JJMath
