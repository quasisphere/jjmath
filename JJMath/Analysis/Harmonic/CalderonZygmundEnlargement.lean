import JJMath.Analysis.Harmonic.CalderonZygmund
import JJMath.Analysis.Harmonic.CalderonZygmundPieces
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Enlarged Calderón--Zygmund stopping regions

This file connects the countable kernel-tail estimate to the actual maximal
dyadic stopping squares. A selected dyadic representation supplies a corner
and a controlled support radius for every bad piece. Doubling those support
disks produces the common exterior on which cancellation controls the entire
countable bad-part convolution.
-/

namespace JJMath

open Set MeasureTheory Filter Function
open scoped ENNReal

namespace HarmonicAnalysis

noncomputable section

/--
%%handwave
name:
  Scale of a maximal bad dyadic square
statement:
  Every maximal bad square is a dyadic square. Its selected scale is an
  integer $n$ for which the square has side length $2^n$.
-/
def maximalBadDyadicSquareScale
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {level : ℝ}
    (Q : maximalBadDyadicSquares f level) : ℤ :=
  Q.2.choose

/--
%%handwave
name:
  Index of a maximal bad dyadic square
statement:
  For a maximal bad square with selected scale $n$, its selected index is
  the pair $k\in\mathbb Z^2$ such that the square is $Q_{n,k}$.
-/
def maximalBadDyadicSquareIndex
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {level : ℝ}
    (Q : maximalBadDyadicSquares f level) : ℤ × ℤ :=
  Q.2.choose_spec.choose

/--
%%handwave
name:
  Selected dyadic representation of a maximal bad square
statement:
  If $n$ and $k$ are the selected scale and index of a maximal bad square
  $Q$, then $Q=Q_{n,k}$.
proof:
  This is the dyadic representation contained in the definition of the
  maximal-square family.
-/
theorem maximalBadDyadicSquare_eq_dyadicSquare
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {level : ℝ}
    (Q : maximalBadDyadicSquares f level) :
    (Q : Set ℂ) = dyadicSquare (maximalBadDyadicSquareScale Q)
      (maximalBadDyadicSquareIndex Q) := by
  exact Q.2.choose_spec.choose_spec.2.1

/--
%%handwave
name:
  Corner of a maximal bad dyadic square
statement:
  The selected corner $c_Q$ of a maximal bad square $Q=Q_{n,k}$ is its
  lower-left corner $k_1 2^n+i k_2 2^n$.
-/
def maximalBadDyadicSquareCenter
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {level : ℝ}
    (Q : maximalBadDyadicSquares f level) : ℂ :=
  dyadicCorner (maximalBadDyadicSquareScale Q)
    (maximalBadDyadicSquareIndex Q)

/--
%%handwave
name:
  Support radius of a maximal bad dyadic square
statement:
  For a maximal bad square $Q=Q_{n,k}$, set $r_Q=2^{n+1}$. Then
  $Q\subseteq\overline B(c_Q,r_Q)$.
-/
def maximalBadDyadicSquareRadius
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {level : ℝ}
    (Q : maximalBadDyadicSquares f level) : ℝ :=
  2 * dyadicSide (maximalBadDyadicSquareScale Q)

/--
%%handwave
name:
  Positivity of the maximal-square support radius
statement:
  Every selected support radius satisfies $r_Q>0$.
proof:
  It is twice the positive dyadic side length.
-/
theorem maximalBadDyadicSquareRadius_pos
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {level : ℝ}
    (Q : maximalBadDyadicSquares f level) :
    0 < maximalBadDyadicSquareRadius Q := by
  exact mul_pos (by norm_num) (dyadicSide_pos _)

/--
%%handwave
name:
  A maximal bad square lies in its support disk
statement:
  Every maximal bad square $Q$ satisfies
  $$Q\subseteq\overline B(c_Q,r_Q).$$
proof:
  Use the selected dyadic representation and the corner-centered disk bound
  for a dyadic square.
-/
theorem maximalBadDyadicSquare_subset_closedBall
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {level : ℝ}
    (Q : maximalBadDyadicSquares f level) :
    (Q : Set ℂ) ⊆ Metric.closedBall (maximalBadDyadicSquareCenter Q)
      (maximalBadDyadicSquareRadius Q) := by
  rw [maximalBadDyadicSquare_eq_dyadicSquare Q]
  exact dyadicSquare_subset_closedBall_dyadicCorner _ _

/--
%%handwave
name:
  Support disk for a maximal-square bad part
statement:
  If $b_Q(y)\ne0$, then
  $$|y-c_Q|\leq r_Q.$$
proof:
  The bad part is supported in $Q$, and $Q$ lies in its selected support
  disk.
-/
theorem calderonZygmundBadPart_mem_supportDisk
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} {level : ℝ} (Q : maximalBadDyadicSquares f level)
    {y : ℂ} (hy : calderonZygmundBadPart f (Q : Set ℂ) y ≠ 0) :
    ‖y - maximalBadDyadicSquareCenter Q‖ ≤
      maximalBadDyadicSquareRadius Q := by
  have hyQ : y ∈ (Q : Set ℂ) :=
    support_calderonZygmundBadPart_subset f (Q : Set ℂ) hy
  have hyball := maximalBadDyadicSquare_subset_closedBall Q hyQ
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hyball

/--
%%handwave
name:
  Enlarged maximal bad dyadic region
statement:
  The enlarged bad region is the union of the doubled support disks
  $$
    \Omega^*=\bigcup_Q\overline B(c_Q,2r_Q)
  $$
  over all maximal bad squares $Q$.
-/
def enlargedMaximalBadDyadicRegion
    {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (level : ℝ) : Set ℂ :=
  ⋃ Q : maximalBadDyadicSquares f level,
    Metric.closedBall (maximalBadDyadicSquareCenter Q)
      (2 * maximalBadDyadicSquareRadius Q)

/--
%%handwave
name:
  Measurability of the enlarged maximal bad region
statement:
  The union $\Omega^*$ of the doubled support disks of the maximal bad
  squares is Lebesgue measurable.
proof:
  The maximal family is countable and every closed disk is measurable.
-/
theorem measurableSet_enlargedMaximalBadDyadicRegion
    {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (level : ℝ) :
    MeasurableSet (enlargedMaximalBadDyadicRegion f level) := by
  letI := (countable_maximalBadDyadicSquares f level).toEncodable
  exact MeasurableSet.iUnion fun _ ↦ measurableSet_closedBall

/--
%%handwave
name:
  Area of a doubled maximal-square support disk
statement:
  For every maximal bad square $Q$, the doubled support disk has area
  $$
    |\overline B(c_Q,2r_Q)|=16\pi|Q|.
  $$
proof:
  The square has side length $2^n$, while the doubled support disk has radius
  $4\cdot2^n$. Apply the planar disk-area formula.
-/
theorem volume_toReal_maximalBadDyadicSquare_enlargement
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {level : ℝ}
    (Q : maximalBadDyadicSquares f level) :
    (volume (Metric.closedBall (maximalBadDyadicSquareCenter Q)
      (2 * maximalBadDyadicSquareRadius Q))).toReal =
      16 * Real.pi * (volume (Q : Set ℂ)).toReal := by
  rw [Complex.volume_closedBall, maximalBadDyadicSquare_eq_dyadicSquare Q,
    volume_dyadicSquare]
  simp only [maximalBadDyadicSquareRadius]
  have hr : 0 ≤ 2 * (2 * dyadicSide (maximalBadDyadicSquareScale Q)) :=
    mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (dyadicSide_pos _).le)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal (sq_nonneg _)]
  simp only [ENNReal.coe_toReal, NNReal.coe_real_pi]
  ring

/--
%%handwave
name:
  Area comparison for the enlarged maximal bad region
statement:
  If $f:\mathbb C\to E$ is integrable and $\alpha>0$, then
  $$
    |\Omega^*|\leq16\pi
      \left|\bigcup_{Q\,\mathrm{maximal\ bad}}Q\right|.
  $$
proof:
  Subadditivity bounds the area of the enlarged union by the sum of the
  doubled-disk areas. Each such area is $16\pi|Q|$, and the pairwise
  disjoint maximal squares have summable areas.
-/
theorem volume_toReal_enlargedMaximalBadDyadicRegion_le
    {E : Type*} [NormedAddCommGroup E]
    {f : ℂ → E} (hf : Integrable f volume)
    {level : ℝ} (hlevel : 0 < level) :
    (volume (enlargedMaximalBadDyadicRegion f level)).toReal ≤
      16 * Real.pi *
        (volume (maximalBadDyadicRegion f level)).toReal := by
  let S := maximalBadDyadicSquares f level
  letI := (countable_maximalBadDyadicSquares f level).toEncodable
  let a : S → ℝ := fun Q ↦ (volume (Q : Set ℂ)).toReal
  let mass : S → ℝ := fun Q ↦ ∫ x in (Q : Set ℂ), ‖f x‖ ∂volume
  let B : S → Set ℂ := fun Q ↦
    Metric.closedBall (maximalBadDyadicSquareCenter Q)
      (2 * maximalBadDyadicSquareRadius Q)
  have hmass : Summable mass :=
    (hasSum_setIntegral_norm_maximalBadDyadicSquares hf level).summable
  have ha_nonneg : ∀ Q, 0 ≤ a Q := fun _ ↦ ENNReal.toReal_nonneg
  have ha_le : ∀ Q, a Q ≤ level⁻¹ * mass Q := by
    intro Q
    rcases Q.2 with ⟨n, k, hbad, hQ, _hmaximal⟩
    have h := (lt_div_iff₀ hlevel).2 (by
      simpa only [IsBadDyadicSquare, mul_comm] using hbad)
    change (volume (Q : Set ℂ)).toReal ≤
      level⁻¹ * ∫ x in (Q : Set ℂ), ‖f x‖ ∂volume
    rw [hQ]
    simpa only [div_eq_inv_mul] using h.le
  have hasum : Summable a :=
    Summable.of_nonneg_of_le ha_nonneg ha_le (hmass.mul_left level⁻¹)
  have hBfinite : ∀ Q, volume (B Q) ≠ ∞ := by
    intro Q
    simp only [B, Complex.volume_closedBall]
    finiteness
  have hBreal : Summable fun Q ↦ (volume (B Q)).toReal := by
    apply hasum.mul_left (16 * Real.pi) |>.congr
    intro Q
    simpa only [B, a] using
      (volume_toReal_maximalBadDyadicSquare_enlargement Q).symm
  have hBnn : Summable fun Q ↦ (volume (B Q)).toNNReal := by
    apply NNReal.summable_coe.1
    simpa only [ENNReal.toReal] using hBreal
  have hBtop : (∑' Q, volume (B Q)) ≠ ∞ := by
    have heq : (fun Q ↦ volume (B Q)) =
        fun Q ↦ ((volume (B Q)).toNNReal : ℝ≥0∞) := by
      funext Q
      exact (ENNReal.coe_toNNReal (hBfinite Q)).symm
    rw [heq]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 hBnn
  have hiUnion : volume (enlargedMaximalBadDyadicRegion f level) ≤
      ∑' Q, volume (B Q) := by
    simpa only [enlargedMaximalBadDyadicRegion, B] using
      (measure_iUnion_le (fun Q : S ↦ B Q) :
        volume (⋃ Q, B Q) ≤ ∑' Q, volume (B Q))
  have hregion : (volume (maximalBadDyadicRegion f level)).toReal =
      ∑' Q : S, a Q := by
    rw [maximalBadDyadicRegion]
    rw [measure_sUnion (countable_maximalBadDyadicSquares f level)
      (pairwiseDisjoint_maximalBadDyadicSquares f level)
      (fun Q hQ ↦ measurableSet_of_mem_maximalBadDyadicSquares hQ)]
    exact ENNReal.tsum_toReal_eq (fun Q ↦
      volume_ne_top_of_mem_maximalBadDyadicSquares Q.2)
  calc
    (volume (enlargedMaximalBadDyadicRegion f level)).toReal ≤
        (∑' Q, volume (B Q)).toReal := ENNReal.toReal_mono hBtop hiUnion
    _ = ∑' Q, (volume (B Q)).toReal :=
      ENNReal.tsum_toReal_eq hBfinite
    _ = ∑' Q : S, 16 * Real.pi * a Q := by
      apply tsum_congr
      intro Q
      simpa only [B, a] using
        volume_toReal_maximalBadDyadicSquare_enlargement Q
    _ = 16 * Real.pi * ∑' Q : S, a Q := by rw [tsum_mul_left]
    _ = 16 * Real.pi *
        (volume (maximalBadDyadicRegion f level)).toReal := by rw [hregion]

/--
%%handwave
name:
  The enlarged maximal bad region has finite area
statement:
  If $f$ is integrable and $\alpha>0$, then the enlarged bad region
  $\Omega^*$ has finite planar area.
proof:
  The doubled disk belonging to a maximal bad square $Q$ has area
  $16\pi|Q|$. The bad-square inequality bounds $|Q|$ by
  $\alpha^{-1}\int_Q|f|$, and the pairwise-disjoint square masses form a
  summable family. Countable subadditivity therefore gives
  $|\Omega^*|<\infty$.
-/
theorem volume_enlargedMaximalBadDyadicRegion_ne_top
    {E : Type*} [NormedAddCommGroup E]
    {f : ℂ → E} (hf : Integrable f volume)
    {level : ℝ} (hlevel : 0 < level) :
    volume (enlargedMaximalBadDyadicRegion f level) ≠ ∞ := by
  let S := maximalBadDyadicSquares f level
  letI := (countable_maximalBadDyadicSquares f level).toEncodable
  let a : S → ℝ := fun Q ↦ (volume (Q : Set ℂ)).toReal
  let mass : S → ℝ := fun Q ↦ ∫ x in (Q : Set ℂ), ‖f x‖ ∂volume
  let B : S → Set ℂ := fun Q ↦
    Metric.closedBall (maximalBadDyadicSquareCenter Q)
      (2 * maximalBadDyadicSquareRadius Q)
  have hmass : Summable mass :=
    (hasSum_setIntegral_norm_maximalBadDyadicSquares hf level).summable
  have ha_le (Q : S) : a Q ≤ level⁻¹ * mass Q := by
    rcases Q.2 with ⟨n, k, hbad, hQ, _hmaximal⟩
    have h := (lt_div_iff₀ hlevel).2 (by
      simpa only [IsBadDyadicSquare, mul_comm] using hbad)
    change (volume (Q : Set ℂ)).toReal ≤
      level⁻¹ * ∫ x in (Q : Set ℂ), ‖f x‖ ∂volume
    rw [hQ]
    simpa only [div_eq_inv_mul] using h.le
  have hasum : Summable a :=
    Summable.of_nonneg_of_le (fun _ ↦ ENNReal.toReal_nonneg) ha_le
      (hmass.mul_left level⁻¹)
  have hBfinite (Q : S) : volume (B Q) ≠ ∞ := by
    simp only [B, Complex.volume_closedBall]
    finiteness
  have hBreal : Summable fun Q ↦ (volume (B Q)).toReal := by
    apply hasum.mul_left (16 * Real.pi) |>.congr
    intro Q
    simpa only [B, a] using
      (volume_toReal_maximalBadDyadicSquare_enlargement Q).symm
  have hBnn : Summable fun Q ↦ (volume (B Q)).toNNReal := by
    apply NNReal.summable_coe.1
    simpa only [ENNReal.toReal] using hBreal
  have hBtop : (∑' Q, volume (B Q)) ≠ ∞ := by
    have heq : (fun Q ↦ volume (B Q)) =
        fun Q ↦ ((volume (B Q)).toNNReal : ℝ≥0∞) := by
      funext Q
      exact (ENNReal.coe_toNNReal (hBfinite Q)).symm
    rw [heq]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 hBnn
  apply ne_top_of_le_ne_top hBtop
  simpa only [enlargedMaximalBadDyadicRegion, B] using
    (measure_iUnion_le (fun Q : S ↦ B Q) :
      volume (⋃ Q, B Q) ≤ ∑' Q, volume (B Q))

/--
%%handwave
name:
  Exceptional-area estimate for the enlarged bad region
statement:
  If $f:\mathbb C\to E$ is integrable and $\alpha>0$, then
  $$
    \alpha|\Omega^*|\leq16\pi
      \int_{\mathbb C}\|f(x)\|\,dx.
  $$
proof:
  Combine the area comparison
  $|\Omega^*|\leq16\pi|\bigcup Q|$ with the stopping-time estimate
  $\alpha|\bigcup Q|\leq\|f\|_1$.
-/
theorem level_mul_volume_enlargedMaximalBadDyadicRegion_le
    {E : Type*} [NormedAddCommGroup E]
    {f : ℂ → E} (hf : Integrable f volume)
    {level : ℝ} (hlevel : 0 < level) :
    level * (volume (enlargedMaximalBadDyadicRegion f level)).toReal ≤
      (16 * Real.pi) * ∫ x, ‖f x‖ ∂volume := by
  calc
    level * (volume (enlargedMaximalBadDyadicRegion f level)).toReal ≤
        level * (16 * Real.pi *
          (volume (maximalBadDyadicRegion f level)).toReal) :=
      mul_le_mul_of_nonneg_left
        (volume_toReal_enlargedMaximalBadDyadicRegion_le hf hlevel) hlevel.le
    _ = (16 * Real.pi) *
        (level * (volume (maximalBadDyadicRegion f level)).toReal) := by ring
    _ ≤ (16 * Real.pi) * ∫ x, ‖f x‖ ∂volume :=
      mul_le_mul_of_nonneg_left
        (level_mul_volume_maximalBadDyadicRegion_le_integral_norm hf hlevel)
        (mul_nonneg (by norm_num) Real.pi_pos.le)

/--
%%handwave
name:
  Exceptional-area estimate in extended nonnegative reals
statement:
  If $f:\mathbb C\to E$ is integrable and $\alpha>0$, then
  $$
    \alpha|\Omega^*|
      \leq 16\pi\int_{\mathbb C}\|f(x)\|\,dx,
  $$
  with both sides interpreted in $[0,\infty]$.
proof:
  The enlarged region has finite area, so the product can be evaluated in
  the ordinary nonnegative reals. Apply [the real-valued exceptional-area estimate](lean:JJMath.HarmonicAnalysis.level_mul_volume_enlargedMaximalBadDyadicRegion_le) and then regard both sides as extended nonnegative reals.
-/
theorem ofReal_level_mul_volume_enlargedMaximalBadDyadicRegion_le
    {E : Type*} [NormedAddCommGroup E]
    {f : ℂ → E} (hf : Integrable f volume)
    {level : ℝ} (hlevel : 0 < level) :
    ENNReal.ofReal level *
        volume (enlargedMaximalBadDyadicRegion f level) ≤
      ENNReal.ofReal
        ((16 * Real.pi) * ∫ z, ‖f z‖ ∂volume) := by
  have hregion := volume_enlargedMaximalBadDyadicRegion_ne_top hf hlevel
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hregion)
    ENNReal.ofReal_ne_top).1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hlevel.le,
    ENNReal.toReal_ofReal]
  · exact level_mul_volume_enlargedMaximalBadDyadicRegion_le hf hlevel
  · exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (integral_nonneg fun z ↦ norm_nonneg (f z))

/--
%%handwave
name:
  Common kernel-tail exterior is the complement of the enlarged bad region
statement:
  A point $x$ lies outside every doubled support disk if and only if
  $x\notin\Omega^*$; equivalently,
  $$
    \{x:2r_Q<|x-c_Q|\text{ for every }Q\}=(\Omega^*)^c.
  $$
proof:
  Unfold the union and closed-disk membership, then negate the existential
  inequality.
-/
theorem maximalBadDyadicCommonExterior_eq_compl
    {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (level : ℝ) :
    {x : ℂ | ∀ Q : maximalBadDyadicSquares f level,
      2 * maximalBadDyadicSquareRadius Q <
        ‖x - maximalBadDyadicSquareCenter Q‖} =
      (enlargedMaximalBadDyadicRegion f level)ᶜ := by
  ext x
  simp only [enlargedMaximalBadDyadicRegion, mem_setOf_eq, mem_compl_iff,
    mem_iUnion, Metric.mem_closedBall, dist_eq_norm, not_exists, not_le]

/--
%%handwave
name:
  Integrability of the countable bad-part kernel on the common exterior
statement:
  Let $f:\mathbb C\to\mathbb C$ be integrable and let $K$ satisfy the
  measurable planar first-difference estimate with constant $C\geq0$. If
  $b_Q$ are the Calderón--Zygmund bad pieces at level $\alpha$, then
  $$
    x\longmapsto\sum_Q\int_{\mathbb C}K(x-y)b_Q(y)\,dy
  $$
  is integrable on the complement of the enlarged bad region $\Omega^*$.
proof:
  Every $b_Q$ is integrable, mean zero, and supported in its selected disk,
  and the sum of their $L^1$ norms is finite. Apply [integrability of a countable sum of mean-zero kernel tails](lean:JJMath.HarmonicAnalysis.HasKernelFirstDifference.integrableOn_tsum_integral_mul_of_integral_eq_zero), then identify the common exterior with $(\Omega^*)^c$.
-/
theorem HasKernelFirstDifference.integrableOn_tsum_badPart
    (K : ℂ → ℂ) {C : ℝ}
    (hK : HasKernelFirstDifference K 2 C)
    (hKm : Measurable K) (hC : 0 ≤ C)
    {f : ℂ → ℂ} (hf : Integrable f volume) (level : ℝ) :
    IntegrableOn
      (fun x ↦ ∑' Q : maximalBadDyadicSquares f level,
        ∫ y : ℂ, K (x - y) *
          calderonZygmundBadPart f (Q : Set ℂ) y ∂volume)
      (enlargedMaximalBadDyadicRegion f level)ᶜ volume := by
  letI := (countable_maximalBadDyadicSquares f level).toEncodable
  let b : maximalBadDyadicSquares f level → ℂ → ℂ := fun Q ↦
    calderonZygmundBadPart f (Q : Set ℂ)
  have h :=
    HasKernelFirstDifference.integrableOn_tsum_integral_mul_of_integral_eq_zero
      K hK hKm hC
      (fun Q : maximalBadDyadicSquares f level ↦
        maximalBadDyadicSquareRadius Q)
      maximalBadDyadicSquareRadius_pos
      (fun Q : maximalBadDyadicSquares f level ↦
        maximalBadDyadicSquareCenter Q)
      b
      (fun Q ↦ Integrable.integrable_calderonZygmundBadPart hf
        (measurableSet_of_mem_maximalBadDyadicSquares Q.2)
        (volume_ne_top_of_mem_maximalBadDyadicSquares Q.2))
      (fun Q y hy ↦ calderonZygmundBadPart_mem_supportDisk Q hy)
      (fun Q ↦ integral_calderonZygmundBadPart_eq_zero hf
        (measurableSet_of_mem_maximalBadDyadicSquares Q.2)
        (volume_ne_top_of_mem_maximalBadDyadicSquares Q.2))
      (summable_integral_norm_calderonZygmundBadPart hf level)
  rw [maximalBadDyadicCommonExterior_eq_compl f level] at h
  simpa only [b] using h

/--
%%handwave
name:
  Countable exterior kernel estimate for the Calderón--Zygmund bad part
statement:
  Let $f:\mathbb C\to\mathbb C$ be integrable and let $K$ satisfy the
  measurable planar first-difference estimate with constant $C\geq0$. If
  $b_Q$ are the bad pieces at level $\alpha$, then
  $$
    \int_{(\Omega^*)^c}
      \left|\sum_Q\int_{\mathbb C}K(x-y)b_Q(y)\,dy\right|\,dx
      \leq2\pi C\int_{\mathbb C}|f(y)|\,dy.
  $$
proof:
  Each bad part is integrable, has mean zero, and is supported in its
  selected disk. Apply the countable exterior tail estimate and then use
  the bound $\sum_Q\|b_Q\|_1\leq2\|f\|_1$.
-/
theorem HasKernelFirstDifference.setIntegral_norm_tsum_badPart_le
    (K : ℂ → ℂ) {C : ℝ}
    (hK : HasKernelFirstDifference K 2 C)
    (hKm : Measurable K) (hC : 0 ≤ C)
    {f : ℂ → ℂ} (hf : Integrable f volume) (level : ℝ) :
    (∫ x in (enlargedMaximalBadDyadicRegion f level)ᶜ,
        ‖∑' Q : maximalBadDyadicSquares f level,
          ∫ y : ℂ, K (x - y) *
            calderonZygmundBadPart f (Q : Set ℂ) y ∂volume‖) ≤
      (2 * Real.pi * C) * ∫ y : ℂ, ‖f y‖ ∂volume := by
  letI := (countable_maximalBadDyadicSquares f level).toEncodable
  let b : maximalBadDyadicSquares f level → ℂ → ℂ := fun Q ↦
    calderonZygmundBadPart f (Q : Set ℂ)
  have htail :=
    HasKernelFirstDifference.setIntegral_norm_tsum_integral_mul_le_of_integral_eq_zero
      K hK hKm hC
      (fun Q : maximalBadDyadicSquares f level ↦
        maximalBadDyadicSquareRadius Q)
      maximalBadDyadicSquareRadius_pos
      (fun Q : maximalBadDyadicSquares f level ↦
        maximalBadDyadicSquareCenter Q)
      b
      (fun Q ↦ Integrable.integrable_calderonZygmundBadPart hf
        (measurableSet_of_mem_maximalBadDyadicSquares Q.2)
        (volume_ne_top_of_mem_maximalBadDyadicSquares Q.2))
      (fun Q y hy ↦ calderonZygmundBadPart_mem_supportDisk Q hy)
      (fun Q ↦ integral_calderonZygmundBadPart_eq_zero hf
        (measurableSet_of_mem_maximalBadDyadicSquares Q.2)
        (volume_ne_top_of_mem_maximalBadDyadicSquares Q.2))
      (summable_integral_norm_calderonZygmundBadPart hf level)
  rw [maximalBadDyadicCommonExterior_eq_compl f level] at htail
  calc
    (∫ x in (enlargedMaximalBadDyadicRegion f level)ᶜ,
        ‖∑' Q : maximalBadDyadicSquares f level,
          ∫ y : ℂ, K (x - y) *
            calderonZygmundBadPart f (Q : Set ℂ) y ∂volume‖) ≤
        Real.pi * C *
          ∑' Q : maximalBadDyadicSquares f level,
            ∫ y, ‖calderonZygmundBadPart f (Q : Set ℂ) y‖ ∂volume := by
      simpa only [b] using htail
    _ ≤ Real.pi * C * (2 * ∫ y : ℂ, ‖f y‖ ∂volume) := by
      exact mul_le_mul_of_nonneg_left
        (tsum_integral_norm_calderonZygmundBadPart_le hf level)
        (mul_nonneg Real.pi_pos.le hC)
    _ = (2 * Real.pi * C) * ∫ y : ℂ, ‖f y‖ ∂volume := by ring

end

end HarmonicAnalysis

end JJMath
