import JJMath.Analysis.Harmonic.CalderonZygmundDecomposition
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Calderón--Zygmund good and bad pieces

This file constructs the analytic pieces attached to the maximal dyadic
stopping squares. It begins with one square: subtract the vector average of
the function on that square and extend the result by zero. The resulting bad
piece is integrable, supported on the square, has mean zero, and costs at most
twice the original `L¹` mass on the square.
-/

namespace JJMath

open Set MeasureTheory Filter Function
open scoped ENNReal

namespace HarmonicAnalysis

noncomputable section

/--
%%handwave
name:
  Calderón--Zygmund bad part on one set
statement:
  Let $f:\mathbb C\to E$ and $Q\subseteq\mathbb C$. The bad part of $f$
  attached to $Q$ is
  $$
    b_Q(x)=\mathbf 1_Q(x)\left(f(x)-\fint_Q f(y)\,dy\right).
  $$
-/
def calderonZygmundBadPart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (Q : Set ℂ) : ℂ → E :=
  Q.indicator (fun x ↦ f x - ⨍ y in Q, f y ∂volume)

/--
%%handwave
name:
  Formula for a bad part on its supporting set
statement:
  If $x\in Q$, then
  $$
    b_Q(x)=f(x)-\fint_Q f(y)\,dy.
  $$
proof:
  On $Q$, the indicator in the definition of $b_Q$ equals one.
-/
theorem calderonZygmundBadPart_apply_of_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (Q : Set ℂ) {x : ℂ} (hx : x ∈ Q) :
    calderonZygmundBadPart f Q x = f x - ⨍ y in Q, f y ∂volume := by
  simp [calderonZygmundBadPart, hx]

/--
%%handwave
name:
  A bad part vanishes off its supporting set
statement:
  If $x\notin Q$, then $b_Q(x)=0$.
proof:
  Off $Q$, the indicator in the definition of $b_Q$ vanishes.
-/
theorem calderonZygmundBadPart_apply_of_not_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (Q : Set ℂ) {x : ℂ} (hx : x ∉ Q) :
    calderonZygmundBadPart f Q x = 0 := by
  simp [calderonZygmundBadPart, hx]

/--
%%handwave
name:
  Support of a single Calderón--Zygmund bad part
statement:
  The support of $b_Q$ is contained in $Q$:
  $$\operatorname{supp} b_Q\subseteq Q.$$
proof:
  The bad part vanishes at every point outside $Q$.
-/
theorem support_calderonZygmundBadPart_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (Q : Set ℂ) :
    support (calderonZygmundBadPart f Q) ⊆ Q := by
  intro x hx
  by_contra hxQ
  exact hx (calderonZygmundBadPart_apply_of_not_mem f Q hxQ)

/--
%%handwave
name:
  Integrability of a single Calderón--Zygmund bad part
statement:
  Let $f:\mathbb C\to E$ be integrable and let $Q$ be measurable with finite
  area. Then $b_Q$ is integrable on the plane.
proof:
  On $Q$, the bad part is the difference of the integrable restriction of
  $f$ and a constant function on a finite-measure set; off $Q$ it vanishes.
-/
theorem Integrable.integrable_calderonZygmundBadPart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : Integrable f volume) {Q : Set ℂ}
    (hQ : MeasurableSet Q) (hQtop : volume Q ≠ ∞) :
    Integrable (calderonZygmundBadPart f Q) volume := by
  rw [calderonZygmundBadPart, integrable_indicator_iff hQ]
  exact hf.integrableOn.sub (integrableOn_const hQtop)

/--
%%handwave
name:
  Square integrability of a single Calderón--Zygmund bad part
statement:
  Let $f\in L^2(\mathbb C;E)$ and let $Q\subseteq\mathbb C$ be measurable
  with finite area. Then
  $$
    b_Q=\mathbf 1_Q\left(f-\fint_Qf\right)
  $$
  belongs to $L^2(\mathbb C;E)$.
proof:
  On the restricted finite measure space $Q$, both $f$ and the constant
  average $\fint_Qf$ belong to $L^2$. Their difference is therefore in
  $L^2(Q)$, and extension by zero preserves the $L^2$ property.
-/
theorem MemLp.memLp_two_calderonZygmundBadPart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} (hf : MemLp f 2 volume) {Q : Set ℂ}
    (hQ : MeasurableSet Q) (hQtop : volume Q ≠ ∞) :
    MemLp (calderonZygmundBadPart f Q) 2 volume := by
  letI : IsFiniteMeasure (volume.restrict Q) :=
    isFiniteMeasure_restrict.2 hQtop
  rw [calderonZygmundBadPart, memLp_indicator_iff_restrict hQ]
  exact (hf.mono_measure Measure.restrict_le_self).sub
    (memLp_const (μ := volume.restrict Q) (p := 2)
      (⨍ y in Q, f y ∂volume))

/--
%%handwave
name:
  Cancellation of a single Calderón--Zygmund bad part
statement:
  Let $f:\mathbb C\to E$ be integrable and let $Q$ be measurable with finite
  area. Then
  $$
    \int_{\mathbb C} b_Q(x)\,dx=0.
  $$
proof:
  Restrict the integral to $Q$. The integral of the constant average equals
  $|Q|\fint_Qf=\int_Qf$, so the two terms cancel.
-/
theorem integral_calderonZygmundBadPart_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : Integrable f volume) {Q : Set ℂ}
    (hQ : MeasurableSet Q) (hQtop : volume Q ≠ ∞) :
    ∫ x, calderonZygmundBadPart f Q x ∂volume = 0 := by
  rw [calderonZygmundBadPart, integral_indicator hQ]
  rw [integral_sub hf.integrableOn (integrableOn_const hQtop)]
  rw [setIntegral_const, measure_smul_setAverage f hQtop]
  exact sub_self _

/--
%%handwave
name:
  Norm of a vector average is controlled by the average norm
statement:
  Let $f:\mathbb C\to E$ be integrable on a finite-area measurable set $Q$.
  Then
  $$
    |Q|\left\|\fint_Q f(x)\,dx\right\|
      \leq\int_Q\|f(x)\|\,dx.
  $$
proof:
  Use $|Q|\fint_Qf=\int_Qf$ and the norm inequality for the Bochner
  integral.
-/
theorem volume_toReal_mul_norm_setAverage_le_setIntegral_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} {Q : Set ℂ} (_hf : IntegrableOn f Q volume)
    (hQtop : volume Q ≠ ∞) :
    (volume Q).toReal * ‖⨍ x in Q, f x ∂volume‖ ≤
      ∫ x in Q, ‖f x‖ ∂volume := by
  calc
    (volume Q).toReal * ‖⨍ x in Q, f x ∂volume‖ =
        ‖(volume Q).toReal • ⨍ x in Q, f x ∂volume‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    _ = ‖∫ x in Q, f x ∂volume‖ := by
      change ‖volume.real Q • ⨍ x in Q, f x ∂volume‖ = _
      rw [measure_smul_setAverage f hQtop]
    _ ≤ ∫ x in Q, ‖f x‖ ∂volume := norm_integral_le_integral_norm _

/--
%%handwave
name:
  $L^1$ bound for a single Calderón--Zygmund bad part
statement:
  Let $f:\mathbb C\to E$ be integrable and let $Q$ be measurable with finite
  area. Then
  $$
    \int_{\mathbb C}\|b_Q(x)\|\,dx
      \leq2\int_Q\|f(x)\|\,dx.
  $$
proof:
  On $Q$, the triangle inequality gives
  $\|b_Q\|\leq\|f\|+\|f_Q\|$. Integrate this inequality and use
  [the norm of the vector average is controlled by the average norm](lean:JJMath.HarmonicAnalysis.volume_toReal_mul_norm_setAverage_le_setIntegral_norm).
-/
theorem integral_norm_calderonZygmundBadPart_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : Integrable f volume) {Q : Set ℂ}
    (hQ : MeasurableSet Q) (hQtop : volume Q ≠ ∞) :
    (∫ x, ‖calderonZygmundBadPart f Q x‖ ∂volume) ≤
      2 * ∫ x in Q, ‖f x‖ ∂volume := by
  let avg : E := ⨍ y in Q, f y ∂volume
  have hdiff_int : IntegrableOn (fun x ↦ ‖f x - avg‖) Q volume :=
    (hf.integrableOn.sub (integrableOn_const (C := avg) hQtop)).norm
  have hmono : (∫ x in Q, ‖f x - avg‖ ∂volume) ≤
      ∫ x in Q, ‖f x‖ + ‖avg‖ ∂volume := by
    apply setIntegral_mono_on hdiff_int
      (hf.norm.integrableOn.add (integrableOn_const (C := ‖avg‖) hQtop)) hQ
    intro x _hx
    exact norm_sub_le _ _
  have havg : (volume Q).toReal * ‖avg‖ ≤ ∫ x in Q, ‖f x‖ ∂volume := by
    exact volume_toReal_mul_norm_setAverage_le_setIntegral_norm hf.integrableOn hQtop
  calc
    (∫ x, ‖calderonZygmundBadPart f Q x‖ ∂volume) =
        ∫ x in Q, ‖f x - avg‖ ∂volume := by
      rw [calderonZygmundBadPart]
      simp only [norm_indicator_eq_indicator_norm]
      rw [integral_indicator hQ]
    _ ≤ ∫ x in Q, ‖f x‖ + ‖avg‖ ∂volume := hmono
    _ = (∫ x in Q, ‖f x‖ ∂volume) + (volume Q).toReal * ‖avg‖ := by
      rw [integral_add hf.norm.integrableOn (integrableOn_const hQtop),
        setIntegral_const]
      simp only [smul_eq_mul, measureReal_def]
    _ ≤ 2 * ∫ x in Q, ‖f x‖ ∂volume := by linarith

/--
%%handwave
name:
  Average bound on a maximal bad square
statement:
  Let $f:\mathbb C\to E$ be integrable. If $Q$ is a maximal bad dyadic
  square at level $\alpha$, then
  $$
    \left\|\fint_Q f(x)\,dx\right\|\leq4\alpha.
  $$
proof:
  The norm of the vector average is at most the average of $\|f\|$. Apply
  [the upper integral bound $\int_Q\|f\|\leq4\alpha|Q|$](lean:JJMath.HarmonicAnalysis.setIntegral_norm_le_four_mul_level_mul_volume_of_mem_maximalBadDyadicSquares) and divide by the positive area of $Q$.
-/
theorem norm_setAverage_le_four_mul_level_of_mem_maximalBadDyadicSquares
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : Integrable f volume) {level : ℝ} {Q : Set ℂ}
    (hQ : Q ∈ maximalBadDyadicSquares f level) :
    ‖⨍ x in Q, f x ∂volume‖ ≤ 4 * level := by
  rcases hQ with ⟨n, k, hbad, rfl, hmaximal⟩
  have hmem : dyadicSquare n k ∈ maximalBadDyadicSquares f level :=
    ⟨n, k, hbad, rfl, hmaximal⟩
  have harea : 0 < (volume (dyadicSquare n k)).toReal :=
    volume_toReal_pos_of_mem_maximalBadDyadicSquares hmem
  have havg := volume_toReal_mul_norm_setAverage_le_setIntegral_norm
    hf.integrableOn (volume_ne_top_of_mem_maximalBadDyadicSquares hmem)
  have hupper :=
    setIntegral_norm_le_four_mul_level_mul_volume_of_mem_maximalBadDyadicSquares
      hf hmem
  nlinarith

/--
%%handwave
name:
  Summation of the $L^1$ masses on maximal bad squares
statement:
  Let $f:\mathbb C\to E$ be integrable. The integrals of $\|f\|$ over the
  maximal bad squares at level $\alpha$ sum to the integral over their union:
  $$
    \sum_Q\int_Q\|f(x)\|\,dx
      =\int_{\bigcup Q}\|f(x)\|\,dx.
  $$
proof:
  The maximal family is countable, its members are measurable, and distinct
  members are disjoint. Apply countable additivity of the Bochner integral
  for the nonnegative integrable function $\|f\|$.
-/
theorem hasSum_setIntegral_norm_maximalBadDyadicSquares
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : Integrable f volume) (level : ℝ) :
    HasSum
      (fun Q : maximalBadDyadicSquares f level ↦
        ∫ x in (Q : Set ℂ), ‖f x‖ ∂volume)
      (∫ x in maximalBadDyadicRegion f level, ‖f x‖ ∂volume) := by
  letI := (countable_maximalBadDyadicSquares f level).toEncodable
  have hpair : Pairwise
      (Disjoint on fun Q : maximalBadDyadicSquares f level ↦ (Q : Set ℂ)) := by
    intro Q R hne
    apply pairwiseDisjoint_maximalBadDyadicSquares f level Q.2 R.2
    intro hQR
    exact hne (Subtype.ext hQR)
  have hsum := hasSum_integral_iUnion
    (f := fun x ↦ ‖f x‖)
    (fun Q : maximalBadDyadicSquares f level ↦
      measurableSet_of_mem_maximalBadDyadicSquares Q.2)
    hpair hf.norm.integrableOn
  simpa only [maximalBadDyadicRegion, sUnion_eq_biUnion, iUnion_subtype] using hsum

/--
%%handwave
name:
  Summability of the $L^1$ norms of all bad parts
statement:
  Let $f:\mathbb C\to E$ be integrable. For the maximal bad squares at level
  $\alpha$, the series
  $$
    \sum_Q\int_{\mathbb C}\|b_Q(x)\|\,dx
  $$
  converges.
proof:
  For each square, [the bad-part norm is at most $2\int_Q\|f\|$](lean:JJMath.HarmonicAnalysis.integral_norm_calderonZygmundBadPart_le). The dominating series converges because the disjoint-square masses sum to the integral over their union.
-/
theorem summable_integral_norm_calderonZygmundBadPart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : Integrable f volume) (level : ℝ) :
    Summable (fun Q : maximalBadDyadicSquares f level ↦
      ∫ x, ‖calderonZygmundBadPart f (Q : Set ℂ) x‖ ∂volume) := by
  let mass : maximalBadDyadicSquares f level → ℝ := fun Q ↦
    ∫ x in (Q : Set ℂ), ‖f x‖ ∂volume
  have hmass : Summable mass :=
    (hasSum_setIntegral_norm_maximalBadDyadicSquares hf level).summable
  apply Summable.of_nonneg_of_le
  · intro Q
    exact integral_nonneg fun _ ↦ norm_nonneg _
  · intro Q
    exact integral_norm_calderonZygmundBadPart_le hf
      (measurableSet_of_mem_maximalBadDyadicSquares Q.2)
      (volume_ne_top_of_mem_maximalBadDyadicSquares Q.2)
  · exact hmass.mul_left 2

/--
%%handwave
name:
  Total $L^1$ mass of the Calderón--Zygmund bad pieces
statement:
  Let $f:\mathbb C\to E$ be integrable. For the maximal bad squares at any
  level,
  $$
    \sum_Q\int_{\mathbb C}\|b_Q(x)\|\,dx
      \leq2\int_{\mathbb C}\|f(x)\|\,dx.
  $$
proof:
  Each bad part costs at most twice the mass of $f$ on its supporting square.
  The maximal squares are pairwise disjoint, so those local masses sum to the
  mass on their union, which is at most the global mass.
-/
theorem tsum_integral_norm_calderonZygmundBadPart_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : Integrable f volume) (level : ℝ) :
    (∑' Q : maximalBadDyadicSquares f level,
        ∫ x, ‖calderonZygmundBadPart f (Q : Set ℂ) x‖ ∂volume) ≤
      2 * ∫ x, ‖f x‖ ∂volume := by
  let mass : maximalBadDyadicSquares f level → ℝ := fun Q ↦
    ∫ x in (Q : Set ℂ), ‖f x‖ ∂volume
  have hmass := hasSum_setIntegral_norm_maximalBadDyadicSquares hf level
  have hbad := summable_integral_norm_calderonZygmundBadPart hf level
  calc
    (∑' Q : maximalBadDyadicSquares f level,
        ∫ x, ‖calderonZygmundBadPart f (Q : Set ℂ) x‖ ∂volume) ≤
        ∑' Q, 2 * mass Q := by
      apply hbad.tsum_le_tsum
      · intro Q
        exact integral_norm_calderonZygmundBadPart_le hf
          (measurableSet_of_mem_maximalBadDyadicSquares Q.2)
          (volume_ne_top_of_mem_maximalBadDyadicSquares Q.2)
      · exact hmass.summable.mul_left 2
    _ = 2 * ∫ x in maximalBadDyadicRegion f level, ‖f x‖ ∂volume := by
      rw [tsum_mul_left, hmass.tsum_eq]
    _ ≤ 2 * ∫ x, ‖f x‖ ∂volume := by
      exact mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hf.norm
          (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)) (by norm_num)

/--
%%handwave
name:
  Total Calderón--Zygmund bad part
statement:
  For a function $f$ and a level $\alpha$, the total bad part is the
  pointwise sum
  $$
    b(x)=\sum_{Q\,\mathrm{maximal\ bad}} b_Q(x).
  $$
  The sum has at most one nonzero term at every point because the maximal
  squares are pairwise disjoint.
-/
def calderonZygmundBadSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (level : ℝ) (x : ℂ) : E :=
  ∑' Q : maximalBadDyadicSquares f level,
    calderonZygmundBadPart f (Q : Set ℂ) x

/--
%%handwave
name:
  Calderón--Zygmund good part
statement:
  For a function $f$ and a level $\alpha$, the good part is
  $$
    g=f-\sum_{Q\,\mathrm{maximal\ bad}}b_Q.
  $$
-/
def calderonZygmundGoodPart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (level : ℝ) (x : ℂ) : E :=
  f x - calderonZygmundBadSum f level x

/--
%%handwave
name:
  Pointwise summability of the bad-part family
statement:
  For every $x\in\mathbb C$, the family $(b_Q(x))_Q$ over the maximal bad
  squares is summable.
proof:
  If two terms were nonzero, $x$ would belong to two distinct maximal bad
  squares, contradicting their disjointness. Thus the family has support of
  cardinality at most one.
-/
theorem summable_calderonZygmundBadPart_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (level : ℝ) (x : ℂ) :
    Summable (fun Q : maximalBadDyadicSquares f level ↦
      calderonZygmundBadPart f (Q : Set ℂ) x) := by
  apply summable_of_hasFiniteSupport
  apply Set.Subsingleton.finite
  intro Q hQ R hR
  by_contra hne
  have hsets : (Q : Set ℂ) ≠ (R : Set ℂ) := by
    intro h
    exact hne (Subtype.ext h)
  have hdisj := pairwiseDisjoint_maximalBadDyadicSquares f level Q.2 R.2 hsets
  have hxQ : x ∈ (Q : Set ℂ) :=
    support_calderonZygmundBadPart_subset f (Q : Set ℂ) hQ
  have hxR : x ∈ (R : Set ℂ) :=
    support_calderonZygmundBadPart_subset f (R : Set ℂ) hR
  exact Set.disjoint_left.1 hdisj hxQ hxR

/--
%%handwave
name:
  The total bad part vanishes outside the bad region
statement:
  If $x$ lies outside the union of the maximal bad squares, then
  $$b(x)=0.$$
proof:
  Every individual bad part is supported on its corresponding maximal
  square, so every term in the pointwise sum vanishes at $x$.
-/
theorem calderonZygmundBadSum_apply_of_not_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} {level : ℝ} {x : ℂ}
    (hx : x ∉ maximalBadDyadicRegion f level) :
    calderonZygmundBadSum f level x = 0 := by
  rw [calderonZygmundBadSum]
  calc
    (∑' Q : maximalBadDyadicSquares f level,
        calderonZygmundBadPart f (Q : Set ℂ) x) =
        ∑' _Q : maximalBadDyadicSquares f level, (0 : E) := by
      apply tsum_congr
      intro Q
      apply calderonZygmundBadPart_apply_of_not_mem
      intro hxQ
      apply hx
      exact Set.mem_sUnion.2 ⟨(Q : Set ℂ), Q.2, hxQ⟩
    _ = 0 := tsum_zero

/--
%%handwave
name:
  The total bad part equals the unique local bad part on a selected square
statement:
  If $x$ belongs to a maximal bad square $Q$, then
  $$b(x)=b_Q(x).$$
proof:
  Pairwise disjointness makes every term indexed by a different maximal
  square vanish at $x$.
-/
theorem calderonZygmundBadSum_apply_of_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} {level : ℝ}
    (Q : maximalBadDyadicSquares f level) {x : ℂ} (hx : x ∈ (Q : Set ℂ)) :
    calderonZygmundBadSum f level x =
      calderonZygmundBadPart f (Q : Set ℂ) x := by
  rw [calderonZygmundBadSum]
  apply tsum_eq_single Q
  intro R hRQ
  apply calderonZygmundBadPart_apply_of_not_mem
  intro hxR
  have hsets : (R : Set ℂ) ≠ (Q : Set ℂ) := by
    intro h
    exact hRQ (Subtype.ext h)
  have hdisj := pairwiseDisjoint_maximalBadDyadicSquares f level R.2 Q.2 hsets
  exact Set.disjoint_left.1 hdisj hxR hx

/--
%%handwave
name:
  The good part agrees with the original function off the bad region
statement:
  If $x$ lies outside the union of the maximal bad squares, then
  $$g(x)=f(x).$$
proof:
  The total bad part vanishes outside the bad region.
-/
theorem calderonZygmundGoodPart_apply_of_not_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} {level : ℝ} {x : ℂ}
    (hx : x ∉ maximalBadDyadicRegion f level) :
    calderonZygmundGoodPart f level x = f x := by
  rw [calderonZygmundGoodPart,
    calderonZygmundBadSum_apply_of_not_mem hx, sub_zero]

/--
%%handwave
name:
  The good part is the local average on each maximal bad square
statement:
  If $x$ belongs to a maximal bad square $Q$, then
  $$
    g(x)=\fint_Q f(y)\,dy.
  $$
proof:
  At $x$, the total bad part equals
  $b_Q(x)=f(x)-\fint_Qf$; subtracting it from $f(x)$ leaves the average.
-/
theorem calderonZygmundGoodPart_apply_of_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} {level : ℝ}
    (Q : maximalBadDyadicSquares f level) {x : ℂ} (hx : x ∈ (Q : Set ℂ)) :
    calderonZygmundGoodPart f level x =
      ⨍ y in (Q : Set ℂ), f y ∂volume := by
  rw [calderonZygmundGoodPart, calderonZygmundBadSum_apply_of_mem Q hx,
    calderonZygmundBadPart_apply_of_mem f (Q : Set ℂ) hx]
  abel

/--
%%handwave
name:
  Integrability of the total Calderón--Zygmund bad part
statement:
  If $f:\mathbb C\to E$ is integrable, then the total bad part
  $$b=\sum_{Q\,\mathrm{maximal\ bad}}b_Q$$
  is integrable on the plane.
proof:
  On each maximal square, the total bad part equals the corresponding
  integrable single bad part. The sum of the integrals of its norm over the
  disjoint squares converges. The total bad part vanishes outside their
  measurable union, so integrability on that union gives global
  integrability.
-/
theorem Integrable.integrable_calderonZygmundBadSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : Integrable f volume) (level : ℝ) :
    Integrable (calderonZygmundBadSum f level) volume := by
  letI := (countable_maximalBadDyadicSquares f level).toEncodable
  let S := maximalBadDyadicSquares f level
  have hlocal : ∀ Q : S,
      IntegrableOn (calderonZygmundBadSum f level) (Q : Set ℂ) volume := by
    intro Q
    have hpart := Integrable.integrable_calderonZygmundBadPart hf
      (measurableSet_of_mem_maximalBadDyadicSquares Q.2)
      (volume_ne_top_of_mem_maximalBadDyadicSquares Q.2)
    apply hpart.integrableOn.congr_fun _
      (measurableSet_of_mem_maximalBadDyadicSquares Q.2)
    intro x hx
    exact (calderonZygmundBadSum_apply_of_mem Q hx).symm
  have hsum : Summable (fun Q : S ↦
      ∫ x in (Q : Set ℂ), ‖calderonZygmundBadSum f level x‖ ∂volume) := by
    apply (summable_integral_norm_calderonZygmundBadPart hf level).congr
    intro Q
    calc
      (∫ x, ‖calderonZygmundBadPart f (Q : Set ℂ) x‖ ∂volume) =
          ∫ x in (Q : Set ℂ),
            ‖f x - ⨍ y in (Q : Set ℂ), f y ∂volume‖ ∂volume := by
        rw [calderonZygmundBadPart]
        simp only [norm_indicator_eq_indicator_norm]
        rw [integral_indicator
          (measurableSet_of_mem_maximalBadDyadicSquares Q.2)]
      _ = ∫ x in (Q : Set ℂ), ‖calderonZygmundBadSum f level x‖ ∂volume := by
        apply setIntegral_congr_fun
          (measurableSet_of_mem_maximalBadDyadicSquares Q.2)
        intro x hx
        change ‖f x - ⨍ y in (Q : Set ℂ), f y ∂volume‖ =
          ‖calderonZygmundBadSum f level x‖
        rw [calderonZygmundBadSum_apply_of_mem Q hx,
          calderonZygmundBadPart_apply_of_mem f (Q : Set ℂ) hx]
  have hunion : IntegrableOn (calderonZygmundBadSum f level)
      (maximalBadDyadicRegion f level) volume := by
    have h := integrableOn_iUnion_of_summable_integral_norm hlocal hsum
    simpa only [maximalBadDyadicRegion, sUnion_eq_biUnion, iUnion_subtype] using h
  have hind := hunion.integrable_indicator
    (measurableSet_maximalBadDyadicRegion f level)
  apply hind.congr
  filter_upwards with x
  by_cases hx : x ∈ maximalBadDyadicRegion f level
  · simp [hx]
  · simp [hx, calderonZygmundBadSum_apply_of_not_mem hx]

/--
%%handwave
name:
  Integrability of the Calderón--Zygmund good part
statement:
  If $f:\mathbb C\to E$ is integrable, then its good part at every level is
  integrable.
proof:
  The good part is the difference of $f$ and the integrable total bad part.
-/
theorem Integrable.integrable_calderonZygmundGoodPart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : Integrable f volume) (level : ℝ) :
    Integrable (calderonZygmundGoodPart f level) volume := by
  exact hf.sub (Integrable.integrable_calderonZygmundBadSum hf level)

/--
%%handwave
name:
  Exact Calderón--Zygmund decomposition
statement:
  For every $x\in\mathbb C$,
  $$
    f(x)=g(x)+b(x),
  $$
  where $g$ is the good part and $b$ is the total bad part.
proof:
  This is the defining identity $g=f-b$ rearranged in the additive group
  $E$.
-/
theorem calderonZygmundGoodPart_add_badSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (level : ℝ) (x : ℂ) :
    calderonZygmundGoodPart f level x + calderonZygmundBadSum f level x = f x := by
  rw [calderonZygmundGoodPart]
  exact sub_add_cancel _ _

/--
%%handwave
name:
  Reverse exact Calderón--Zygmund decomposition
statement:
  For every $x\in\mathbb C$, the total bad part is the difference between
  the original function and its good part:
  $$
    b(x)=f(x)-g(x).
  $$
proof:
  Rearrange the defining identity $g=f-b$ in the additive group $E$.
-/
theorem calderonZygmundBadSum_eq_sub_goodPart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (level : ℝ) (x : ℂ) :
    calderonZygmundBadSum f level x =
      f x - calderonZygmundGoodPart f level x := by
  rw [calderonZygmundGoodPart]
  exact (sub_sub_cancel _ _).symm

/--
%%handwave
name:
  Essential bound for the Calderón--Zygmund good part
statement:
  If $f:\mathbb C\to E$ is integrable and $\alpha>0$, then
  $$
    \|g(x)\|\leq4\alpha
  $$
  for almost every $x\in\mathbb C$.
proof:
  On a maximal bad square, the good part is the vector average of $f$, whose
  norm is at most $4\alpha$. Outside the bad region, the good part equals
  $f$; dyadic differentiation shows that $\|f\|\leq\alpha$ there almost
  everywhere.
-/
theorem ae_norm_calderonZygmundGoodPart_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : Integrable f volume)
    {level : ℝ} (hlevel : 0 < level) :
    ∀ᵐ x ∂volume, ‖calderonZygmundGoodPart f level x‖ ≤ 4 * level := by
  have houtside : ∀ᵐ x ∂volume,
      x ∉ maximalBadDyadicRegion f level → ‖f x‖ ≤ level := by
    filter_upwards [ae_mem_badDyadicRegion_of_lt_norm hf level] with x hx
    intro hxout
    apply le_of_not_gt
    intro hhigh
    apply hxout
    rw [← badDyadicRegion_eq_maximalBadDyadicRegion hf hlevel]
    exact hx hhigh
  filter_upwards [houtside] with x hxout
  by_cases hx : x ∈ maximalBadDyadicRegion f level
  · rcases Set.mem_sUnion.1 hx with ⟨Q, hQ, hxQ⟩
    let Q' : maximalBadDyadicSquares f level := ⟨Q, hQ⟩
    rw [show calderonZygmundGoodPart f level x =
        ⨍ y in Q, f y ∂volume by
      exact calderonZygmundGoodPart_apply_of_mem Q' hxQ]
    exact norm_setAverage_le_four_mul_level_of_mem_maximalBadDyadicSquares hf hQ
  · rw [calderonZygmundGoodPart_apply_of_not_mem hx]
    exact (hxout hx).trans (by linarith)

/--
%%handwave
name:
  $L^1$ bound for the Calderón--Zygmund good part
statement:
  If $f:\mathbb C\to E$ is integrable, then its good part satisfies
  $$
    \int_{\mathbb C}\|g(x)\|\,dx
      \leq \int_{\mathbb C}\|f(x)\|\,dx.
  $$
proof:
  On each maximal bad square $Q$, the good part is the constant vector
  average $f_Q$, and
  $|Q|\|f_Q\|\leq\int_Q\|f\|$. Sum over the pairwise disjoint maximal
  squares. On the complement of their union, $g=f$.
-/
theorem integral_norm_calderonZygmundGoodPart_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : Integrable f volume) (level : ℝ) :
    (∫ x, ‖calderonZygmundGoodPart f level x‖ ∂volume) ≤
      ∫ x, ‖f x‖ ∂volume := by
  letI := (countable_maximalBadDyadicSquares f level).toEncodable
  let S := maximalBadDyadicSquares f level
  let R := maximalBadDyadicRegion f level
  have hR : MeasurableSet R := measurableSet_maximalBadDyadicRegion f level
  have hpair : Pairwise (Disjoint on fun Q : S ↦ (Q : Set ℂ)) := by
    intro Q T hne
    apply pairwiseDisjoint_maximalBadDyadicSquares f level Q.2 T.2
    intro hQT
    exact hne (Subtype.ext hQT)
  have hgood := Integrable.integrable_calderonZygmundGoodPart hf level
  have hsum_good : HasSum
      (fun Q : S ↦ ∫ x in (Q : Set ℂ),
        ‖calderonZygmundGoodPart f level x‖ ∂volume)
      (∫ x in R, ‖calderonZygmundGoodPart f level x‖ ∂volume) := by
    have h := hasSum_integral_iUnion
      (f := fun x ↦ ‖calderonZygmundGoodPart f level x‖)
      (fun Q : S ↦ measurableSet_of_mem_maximalBadDyadicSquares Q.2)
      hpair hgood.norm.integrableOn
    simpa only [R, maximalBadDyadicRegion, sUnion_eq_biUnion, iUnion_subtype] using h
  have hsum_f : HasSum
      (fun Q : S ↦ ∫ x in (Q : Set ℂ), ‖f x‖ ∂volume)
      (∫ x in R, ‖f x‖ ∂volume) := by
    simpa only [R] using hasSum_setIntegral_norm_maximalBadDyadicSquares hf level
  have hterm : ∀ Q : S,
      (∫ x in (Q : Set ℂ), ‖calderonZygmundGoodPart f level x‖ ∂volume) ≤
        ∫ x in (Q : Set ℂ), ‖f x‖ ∂volume := by
    intro Q
    calc
      (∫ x in (Q : Set ℂ), ‖calderonZygmundGoodPart f level x‖ ∂volume) =
          ∫ _x in (Q : Set ℂ), ‖⨍ y in (Q : Set ℂ), f y ∂volume‖ ∂volume := by
        apply setIntegral_congr_fun
          (measurableSet_of_mem_maximalBadDyadicSquares Q.2)
        intro x hx
        change ‖calderonZygmundGoodPart f level x‖ = _
        rw [calderonZygmundGoodPart_apply_of_mem Q hx]
      _ = (volume (Q : Set ℂ)).toReal *
          ‖⨍ y in (Q : Set ℂ), f y ∂volume‖ := by
        rw [setIntegral_const]
        simp only [smul_eq_mul, measureReal_def]
      _ ≤ ∫ x in (Q : Set ℂ), ‖f x‖ ∂volume :=
        volume_toReal_mul_norm_setAverage_le_setIntegral_norm hf.integrableOn
          (volume_ne_top_of_mem_maximalBadDyadicSquares Q.2)
  have hregion :
      (∫ x in R, ‖calderonZygmundGoodPart f level x‖ ∂volume) ≤
        ∫ x in R, ‖f x‖ ∂volume := by
    rw [← hsum_good.tsum_eq, ← hsum_f.tsum_eq]
    exact hsum_good.summable.tsum_le_tsum hterm hsum_f.summable
  have hcompl :
      (∫ x in Rᶜ, ‖calderonZygmundGoodPart f level x‖ ∂volume) =
        ∫ x in Rᶜ, ‖f x‖ ∂volume := by
    apply setIntegral_congr_fun hR.compl
    intro x hx
    change ‖calderonZygmundGoodPart f level x‖ = ‖f x‖
    rw [calderonZygmundGoodPart_apply_of_not_mem hx]
  calc
    (∫ x, ‖calderonZygmundGoodPart f level x‖ ∂volume) =
        (∫ x in R, ‖calderonZygmundGoodPart f level x‖ ∂volume) +
          ∫ x in Rᶜ, ‖calderonZygmundGoodPart f level x‖ ∂volume :=
      (integral_add_compl hR hgood.norm).symm
    _ ≤ (∫ x in R, ‖f x‖ ∂volume) + ∫ x in Rᶜ, ‖f x‖ ∂volume :=
      add_le_add hregion hcompl.le
    _ = ∫ x, ‖f x‖ ∂volume := integral_add_compl hR hf.norm

/--
%%handwave
name:
  Square integrability of the Calderón--Zygmund good part
statement:
  Let $f:\mathbb C\to E$ be integrable and let $\alpha>0$. Then
  $$
    x\longmapsto \|g(x)\|^2
  $$
  is integrable on $\mathbb C$.
proof:
  The essential bound $\|g\|\leq4\alpha$ gives
  $\|g\|^2\leq4\alpha\|g\|$ almost everywhere, and $g$ is integrable.
-/
theorem integrable_norm_sq_calderonZygmundGoodPart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : Integrable f volume)
    {level : ℝ} (hlevel : 0 < level) :
    Integrable (fun x ↦ ‖calderonZygmundGoodPart f level x‖ ^ 2) volume := by
  let g := calderonZygmundGoodPart f level
  have hg := Integrable.integrable_calderonZygmundGoodPart hf level
  have hdom : Integrable (fun x ↦ (4 * level) * ‖g x‖) volume :=
    hg.norm.const_mul (4 * level)
  have hpoint : ∀ᵐ x ∂volume, ‖g x‖ ^ 2 ≤ (4 * level) * ‖g x‖ := by
    filter_upwards [ae_norm_calderonZygmundGoodPart_le hf hlevel] with x hx
    dsimp only [g]
    nlinarith [norm_nonneg (calderonZygmundGoodPart f level x)]
  apply Integrable.mono' hdom
    ((hg.aestronglyMeasurable.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
  filter_upwards [hpoint] with x hx
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖g x‖)] using hx

/--
%%handwave
name:
  The Calderón--Zygmund good part belongs to $L^2$
statement:
  If $f:\mathbb C\to E$ is integrable and $\alpha>0$, then its good part
  $g$ belongs to $L^2(\mathbb C;E)$.
proof:
  This is the $L^2$-space formulation of the integrability of
  $x\mapsto\|g(x)\|^2$.
-/
theorem memLp_two_calderonZygmundGoodPart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : Integrable f volume)
    {level : ℝ} (hlevel : 0 < level) :
    MemLp (calderonZygmundGoodPart f level) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (Integrable.integrable_calderonZygmundGoodPart hf level).aestronglyMeasurable).2
  exact integrable_norm_sq_calderonZygmundGoodPart hf hlevel

/--
%%handwave
name:
  The total Calderón--Zygmund bad part preserves $L^2$
statement:
  Let $f:\mathbb C\to E$ be both integrable and square-integrable. For every
  $\alpha>0$, the total bad part $b=f-g$ belongs to $L^2(\mathbb C;E)$.
proof:
  The good part belongs to $L^2$, so the identity $b=f-g$ and linearity of
  $L^2$ give the result.
-/
theorem memLp_two_calderonZygmundBadSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume)
    {level : ℝ} (hlevel : 0 < level) :
    MemLp (calderonZygmundBadSum f level) 2 volume := by
  have hgood := memLp_two_calderonZygmundGoodPart hf₁ hlevel
  have hsub := hf₂.sub hgood
  apply hsub.ae_eq
  filter_upwards with x
  change f x - calderonZygmundGoodPart f level x =
    calderonZygmundBadSum f level x
  exact (calderonZygmundBadSum_eq_sub_goodPart f level x).symm

/--
%%handwave
name:
  $L^2$ estimate for the Calderón--Zygmund good part
statement:
  If $f:\mathbb C\to E$ is integrable and $\alpha>0$, then
  $$
    \int_{\mathbb C}\|g(x)\|^2\,dx
      \leq4\alpha\int_{\mathbb C}\|f(x)\|\,dx.
  $$
proof:
  By the essential bound, $\|g\|^2\leq4\alpha\|g\|$ almost everywhere.
  Integrate and apply [the estimate $\int\|g\|\leq\int\|f\|$](lean:JJMath.HarmonicAnalysis.integral_norm_calderonZygmundGoodPart_le).
-/
theorem integral_norm_sq_calderonZygmundGoodPart_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} (hf : Integrable f volume)
    {level : ℝ} (hlevel : 0 < level) :
    (∫ x, ‖calderonZygmundGoodPart f level x‖ ^ 2 ∂volume) ≤
      (4 * level) * ∫ x, ‖f x‖ ∂volume := by
  let g := calderonZygmundGoodPart f level
  have hg := Integrable.integrable_calderonZygmundGoodPart hf level
  have hsquare : Integrable (fun x ↦ ‖g x‖ ^ 2) volume := by
    simpa only [g] using integrable_norm_sq_calderonZygmundGoodPart hf hlevel
  have hdom : Integrable (fun x ↦ (4 * level) * ‖g x‖) volume :=
    hg.norm.const_mul (4 * level)
  have hpoint : ∀ᵐ x ∂volume, ‖g x‖ ^ 2 ≤ (4 * level) * ‖g x‖ := by
    filter_upwards [ae_norm_calderonZygmundGoodPart_le hf hlevel] with x hx
    dsimp only [g]
    nlinarith [norm_nonneg (calderonZygmundGoodPart f level x)]
  calc
    (∫ x, ‖calderonZygmundGoodPart f level x‖ ^ 2 ∂volume) =
        ∫ x, ‖g x‖ ^ 2 ∂volume := by rfl
    _ ≤ ∫ x, (4 * level) * ‖g x‖ ∂volume :=
      integral_mono_ae hsquare hdom hpoint
    _ = (4 * level) * ∫ x, ‖g x‖ ∂volume := by rw [integral_const_mul]
    _ ≤ (4 * level) * ∫ x, ‖f x‖ ∂volume := by
      exact mul_le_mul_of_nonneg_left
        (integral_norm_calderonZygmundGoodPart_le hf level) (by positivity)

end

end HarmonicAnalysis

end JJMath
