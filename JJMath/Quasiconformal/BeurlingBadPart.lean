import JJMath.Quasiconformal.BeurlingRoughRepresentation
import JJMath.Analysis.Harmonic.CalderonZygmundEnlargement
import JJMath.Analysis.Harmonic.OperatorBounds
import Mathlib.Data.Set.FiniteExhaustion

namespace JJMath

namespace Quasiconformal

open Set MeasureTheory Filter
open scoped ENNReal Topology BigOperators

/-!
# The Beurling transform of the total Calderón--Zygmund bad part

This file passes the rough off-support Beurling formula through the countable
family of maximal bad squares. Finite partial bad sums converge in $L^2$ to
the total bad part, while their physical kernel sums converge in $L^1$ on the
complement of the enlarged bad region. Uniqueness of convergence in measure
then identifies the two limits.
-/

/--
%%handwave
name:
  Finite exhaustion of the maximal bad squares
statement:
  For an input $f$ and level $\alpha$, this is a sequence $(\mathcal F_n)$
  of finite subfamilies of the countable family of maximal bad dyadic squares
  whose union is the whole maximal family.
-/
noncomputable def maximalBadDyadicFinsetExhaustion
    {f : ℂ → ℂ} (level : ℝ) : ℕ → Finset (HarmonicAnalysis.maximalBadDyadicSquares f level) :=
  letI := (HarmonicAnalysis.countable_maximalBadDyadicSquares f level).toEncodable
  let X := (Set.countable_univ : Set.Countable
    (Set.univ : Set (HarmonicAnalysis.maximalBadDyadicSquares f level))).finiteExhaustion
  fun n ↦ (X.finite n).toFinset

/--
%%handwave
name:
  Cofinality of the finite maximal-bad-square exhaustion
statement:
  The finite families $\mathcal F_n$ tend to the top element of the directed
  set of finite families: every finite collection of maximal bad squares is
  contained in every sufficiently late $\mathcal F_n$.
proof:
  Choose, for every square in the prescribed finite collection, an index at
  which it enters the countable-set exhaustion, and take the maximum of those
  finitely many indices.
-/
theorem maximalBadDyadicFinsetExhaustion_tendsto
    {f : ℂ → ℂ} (level : ℝ) :
    Tendsto (maximalBadDyadicFinsetExhaustion (f := f) level) atTop atTop := by
  classical
  let S := HarmonicAnalysis.maximalBadDyadicSquares f level
  letI := (HarmonicAnalysis.countable_maximalBadDyadicSquares f level).toEncodable
  let X : Set.FiniteExhaustion (Set.univ : Set S) :=
    (Set.countable_univ : Set.Countable (Set.univ : Set S)).finiteExhaustion
  have hmem (Q : S) : ∃ n : ℕ, Q ∈ X n := by
    have hQ : Q ∈ ⋃ n, X n := by
      rw [X.iUnion_eq]
      exact Set.mem_univ Q
    simpa only [Set.mem_iUnion] using hQ
  choose N hN using hmem
  rw [tendsto_atTop_atTop]
  intro s
  refine ⟨s.sup N, ?_⟩
  intro n hn Q hQs
  have hQN : N Q ≤ s.sup N := Finset.le_sup hQs
  have hQX : Q ∈ X n := X.mono (hQN.trans hn) (hN Q)
  simpa only [maximalBadDyadicFinsetExhaustion, X, Set.Finite.mem_toFinset] using hQX

/--
%%handwave
name:
  Finite partial sum of the Calderón--Zygmund bad part
statement:
  If $b_Q$ is the mean-zero bad piece on a maximal bad square $Q$, the
  $n$-th partial bad sum is
  $$
    b^{(n)}(x)=\sum_{Q\in\mathcal F_n} b_Q(x).
  $$
-/
noncomputable def calderonZygmundBadPartialSum
    (f : ℂ → ℂ) (level : ℝ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ Q ∈ maximalBadDyadicFinsetExhaustion (f := f) level n,
    HarmonicAnalysis.calderonZygmundBadPart f (Q : Set ℂ) x

/--
%%handwave
name:
  Pointwise convergence of finite bad sums
statement:
  For every $x\in\mathbb C$, the partial sums $b^{(n)}(x)$ converge to the
  complete bad sum $b(x)=\sum_Q b_Q(x)$.
proof:
  The bad-piece series is pointwise summable. Compose its sum with the
  cofinal finite exhaustion $\mathcal F_n$.
-/
theorem calderonZygmundBadPartialSum_tendsto
    (f : ℂ → ℂ) (level : ℝ) (x : ℂ) :
    Tendsto (fun n ↦ calderonZygmundBadPartialSum f level n x) atTop
      (𝓝 (HarmonicAnalysis.calderonZygmundBadSum f level x)) := by
  have hsum :=
    (HarmonicAnalysis.summable_calderonZygmundBadPart_apply f level x).hasSum
  exact hsum.comp (maximalBadDyadicFinsetExhaustion_tendsto (f := f) level)

/--
%%handwave
name:
  Partial bad sums are pointwise bounded by the total bad sum
statement:
  For every $n$ and $x$,
  $$
    |b^{(n)}(x)|\leq |b(x)|.
  $$
proof:
  The maximal bad squares are pairwise disjoint. At a fixed point, either all
  selected pieces vanish or exactly one selected piece can be nonzero; in
  the latter case the same piece is the value of the total bad sum.
-/
theorem norm_calderonZygmundBadPartialSum_le
    (f : ℂ → ℂ) (level : ℝ) (n : ℕ) (x : ℂ) :
    ‖calderonZygmundBadPartialSum f level n x‖ ≤
      ‖HarmonicAnalysis.calderonZygmundBadSum f level x‖ := by
  classical
  let F := maximalBadDyadicFinsetExhaustion (f := f) level n
  let B : HarmonicAnalysis.maximalBadDyadicSquares f level → ℂ → ℂ :=
    fun Q ↦ HarmonicAnalysis.calderonZygmundBadPart f (Q : Set ℂ)
  by_cases hzero : ∀ Q ∈ F, B Q x = 0
  · have hpzero : calderonZygmundBadPartialSum f level n x = 0 := by
      simp only [calderonZygmundBadPartialSum]
      exact Finset.sum_eq_zero hzero
    simp [hpzero]
  · push Not at hzero
    obtain ⟨Q, hQF, hQne⟩ := hzero
    have hxQ : x ∈ (Q : Set ℂ) :=
      HarmonicAnalysis.support_calderonZygmundBadPart_subset
        f (Q : Set ℂ) hQne
    have htotal : HarmonicAnalysis.calderonZygmundBadSum f level x = B Q x :=
      HarmonicAnalysis.calderonZygmundBadSum_apply_of_mem Q hxQ
    have hpartial : calderonZygmundBadPartialSum f level n x = B Q x := by
      simp only [calderonZygmundBadPartialSum]
      apply Finset.sum_eq_single_of_mem Q hQF
      intro R hRF hRQ
      apply HarmonicAnalysis.calderonZygmundBadPart_apply_of_not_mem
      intro hxR
      have hsets : (R : Set ℂ) ≠ (Q : Set ℂ) := by
        intro h
        exact hRQ (Subtype.ext h)
      have hdisj :=
        HarmonicAnalysis.pairwiseDisjoint_maximalBadDyadicSquares
          f level R.2 Q.2 hsets
      exact Set.disjoint_left.1 hdisj hxR hxQ
    rw [hpartial, htotal]

/--
%%handwave
name:
  Finite bad sums belong to $L^2$
statement:
  If $f\in L^2(\mathbb C)$, then every finite partial bad sum
  $b^{(n)}=\sum_{Q\in\mathcal F_n}b_Q$ belongs to $L^2(\mathbb C)$.
proof:
  Each square has finite area, so each restricted bad piece is in $L^2$.
  A finite sum of $L^2$ functions is in $L^2$.
-/
theorem memLp_two_calderonZygmundBadPartialSum
    {f : ℂ → ℂ} (hf : MemLp f 2 volume) (level : ℝ) (n : ℕ) :
    MemLp (calderonZygmundBadPartialSum f level n) 2 volume := by
  apply memLp_finsetSum
  intro Q hQ
  exact HarmonicAnalysis.MemLp.memLp_two_calderonZygmundBadPart hf
    (HarmonicAnalysis.measurableSet_of_mem_maximalBadDyadicSquares Q.2)
    (HarmonicAnalysis.volume_ne_top_of_mem_maximalBadDyadicSquares Q.2)

/--
%%handwave
name:
  The $L^2$ class of a finite bad sum
statement:
  In $L^2(\mathbb C)$, the class represented by
  $b^{(n)}=\sum_{Q\in\mathcal F_n}b_Q$ is exactly the finite sum of the
  classes represented by the individual $b_Q$.
proof:
  Representatives of addition in $L^2$ agree almost everywhere with
  pointwise addition. Induct over the finite family $\mathcal F_n$.
-/
theorem calderonZygmundBadPartialSum_toLp_eq_sum
    {f : ℂ → ℂ} (hf : MemLp f 2 volume) (level : ℝ) (n : ℕ) :
    (memLp_two_calderonZygmundBadPartialSum hf level n).toLp
        (calderonZygmundBadPartialSum f level n) =
      ∑ Q ∈ maximalBadDyadicFinsetExhaustion (f := f) level n,
        (HarmonicAnalysis.MemLp.memLp_two_calderonZygmundBadPart hf
          (HarmonicAnalysis.measurableSet_of_mem_maximalBadDyadicSquares Q.2)
          (HarmonicAnalysis.volume_ne_top_of_mem_maximalBadDyadicSquares Q.2)).toLp
            (HarmonicAnalysis.calderonZygmundBadPart f (Q : Set ℂ)) := by
  classical
  let S := HarmonicAnalysis.maximalBadDyadicSquares f level
  let B : S → ℂ → ℂ := fun Q ↦
    HarmonicAnalysis.calderonZygmundBadPart f (Q : Set ℂ)
  let hB (Q : S) : MemLp (B Q) 2 volume :=
    HarmonicAnalysis.MemLp.memLp_two_calderonZygmundBadPart hf
      (HarmonicAnalysis.measurableSet_of_mem_maximalBadDyadicSquares Q.2)
      (HarmonicAnalysis.volume_ne_top_of_mem_maximalBadDyadicSquares Q.2)
  let L (Q : S) : Lp ℂ 2 volume := (hB Q).toLp (B Q)
  let F := maximalBadDyadicFinsetExhaustion (f := f) level n
  have hcoe : ((∑ Q ∈ F, L Q : Lp ℂ 2 volume) : ℂ → ℂ) =ᵐ[volume]
      fun x ↦ ∑ Q ∈ F, B Q x := by
    induction F using Finset.induction_on with
    | empty =>
        filter_upwards [Lp.coeFn_zero (α := ℂ) (μ := volume) (E := ℂ) (p := 2)] with x hx
        exact hx
    | @insert Q s hQs ih =>
        rw [Finset.sum_insert hQs]
        filter_upwards [Lp.coeFn_add (L Q) (∑ R ∈ s, L R),
          (hB Q).coeFn_toLp, ih] with x hxadd hxQ hxs
        simp only [Finset.sum_insert hQs]
        change (L Q : ℂ → ℂ) x = B Q x at hxQ
        change ((∑ R ∈ s, L R : Lp ℂ 2 volume) : ℂ → ℂ) x =
          ∑ R ∈ s, B R x at hxs
        change (((L Q + ∑ R ∈ s, L R : Lp ℂ 2 volume) : ℂ → ℂ) x) =
          B Q x + ∑ R ∈ s, B R x
        rw [hxadd]
        simp only [Pi.add_apply, hxQ, hxs]
  apply Lp.ext
  filter_upwards [(memLp_two_calderonZygmundBadPartialSum hf level n).coeFn_toLp,
    hcoe] with x hx hsum
  simpa only [calderonZygmundBadPartialSum, F, B] using hx.trans hsum.symm


/--
%%handwave
name:
  Physical Beurling formula for a finite bad sum
statement:
  If $f\in L^2(\mathbb C)$, then outside the enlarged bad region
  $\Omega^*$, for almost every $x$,
  $$
    \mathcal S b^{(n)}(x)
      =\sum_{Q\in\mathcal F_n}
        \int_{\mathbb C}-\frac{b_Q(w)}{\pi(x-w)^2}\,dw.
  $$
proof:
  The complement of $\Omega^*$ lies outside the doubled support disk of
  every bad piece. Apply [the rough off-support formula to each $b_Q$](lean:JJMath.Quasiconformal.beurlingTransformL2_eq_kernelIntegral_ae_exterior_of_memLp_two_of_support_closedBall),
  then use linearity of the Beurling transform and sum the finitely many
  almost-everywhere identities.
-/
theorem beurlingTransformL2_badPartialSum_eq_kernelIntegral
    {f : ℂ → ℂ} (hf : MemLp f 2 volume) (level : ℝ) (n : ℕ) :
    (beurlingTransformL2
      ((memLp_two_calderonZygmundBadPartialSum hf level n).toLp
        (calderonZygmundBadPartialSum f level n)) : ℂ → ℂ) =ᵐ[
        volume.restrict
          (HarmonicAnalysis.enlargedMaximalBadDyadicRegion f level)ᶜ]
      fun x ↦ ∑ Q ∈ maximalBadDyadicFinsetExhaustion (f := f) level n,
        beurlingKernelIntegral
          (HarmonicAnalysis.calderonZygmundBadPart f (Q : Set ℂ)) x := by
  classical
  let S := HarmonicAnalysis.maximalBadDyadicSquares f level
  let E : Set ℂ :=
    (HarmonicAnalysis.enlargedMaximalBadDyadicRegion f level)ᶜ
  let μE : Measure ℂ := volume.restrict E
  let B : S → ℂ → ℂ := fun Q ↦
    HarmonicAnalysis.calderonZygmundBadPart f (Q : Set ℂ)
  let hB (Q : S) : MemLp (B Q) 2 volume :=
    HarmonicAnalysis.MemLp.memLp_two_calderonZygmundBadPart hf
      (HarmonicAnalysis.measurableSet_of_mem_maximalBadDyadicSquares Q.2)
      (HarmonicAnalysis.volume_ne_top_of_mem_maximalBadDyadicSquares Q.2)
  let L (Q : S) : Lp ℂ 2 volume := beurlingTransformL2 ((hB Q).toLp (B Q))
  let A (Q : S) : ℂ → ℂ := fun x ↦ beurlingKernelIntegral (B Q) x
  have hrough (Q : S) : (L Q : ℂ → ℂ) =ᵐ[μE] A Q := by
    have hraw :=
      beurlingTransformL2_eq_kernelIntegral_ae_exterior_of_memLp_two_of_support_closedBall
        (hB Q)
        (HarmonicAnalysis.maximalBadDyadicSquareRadius_pos Q)
        (fun w hw ↦ HarmonicAnalysis.calderonZygmundBadPart_mem_supportDisk Q hw)
    apply ae_mono _ hraw
    dsimp only [μE]
    apply Measure.restrict_mono
    · intro x hx
      have hxcommon : x ∈ {x : ℂ | ∀ R : S,
          2 * HarmonicAnalysis.maximalBadDyadicSquareRadius R <
            ‖x - HarmonicAnalysis.maximalBadDyadicSquareCenter R‖} := by
        rw [HarmonicAnalysis.maximalBadDyadicCommonExterior_eq_compl f level]
        exact hx
      exact hxcommon Q
    · exact le_rfl
  let F := maximalBadDyadicFinsetExhaustion (f := f) level n
  have hcoe : ((∑ Q ∈ F, L Q : Lp ℂ 2 volume) : ℂ → ℂ) =ᵐ[μE]
      fun x ↦ ∑ Q ∈ F, A Q x := by
    induction F using Finset.induction_on with
    | empty =>
        filter_upwards [ae_restrict_of_ae
          (Lp.coeFn_zero (α := ℂ) (μ := volume) (E := ℂ) (p := 2))] with x hx
        exact hx
    | @insert Q s hQs ih =>
        rw [Finset.sum_insert hQs]
        filter_upwards [ae_restrict_of_ae
            (Lp.coeFn_add (L Q) (∑ R ∈ s, L R)), hrough Q, ih]
          with x hxadd hxQ hxs
        simp only [Finset.sum_insert hQs]
        change (((L Q + ∑ R ∈ s, L R : Lp ℂ 2 volume) : ℂ → ℂ) x) =
          A Q x + ∑ R ∈ s, A R x
        rw [hxadd]
        simp only [Pi.add_apply, hxQ, hxs]
  rw [calderonZygmundBadPartialSum_toLp_eq_sum hf level n]
  simp only [map_sum]
  simpa only [μE, E, F, L, A, B] using hcoe

/--
%%handwave
name:
  Finite bad sums converge to the total bad part in $L^2$
statement:
  If $f\in L^1(\mathbb C)\cap L^2(\mathbb C)$ and $\alpha>0$, then
  $$
    \|b^{(n)}-b\|_{L^2(\mathbb C)}\longrightarrow0.
  $$
proof:
  The total bad part belongs to $L^2$, the partial sums converge pointwise,
  and pairwise disjointness gives $|b^{(n)}|\leq|b|$. Thus
  $|b^{(n)}-b|\leq2|b|$, and dominated convergence in $L^2$ applies.
-/
theorem calderonZygmundBadPartialSum_sub_badSum_eLpNorm_tendsto
    {f : ℂ → ℂ} (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume)
    {level : ℝ} (hlevel : 0 < level) :
    Tendsto (fun n ↦ eLpNorm
      (calderonZygmundBadPartialSum f level n -
        HarmonicAnalysis.calderonZygmundBadSum f level) 2 volume)
      atTop (𝓝 0) := by
  let b := HarmonicAnalysis.calderonZygmundBadSum f level
  have hb : MemLp b 2 volume :=
    HarmonicAnalysis.memLp_two_calderonZygmundBadSum hf₁ hf₂ hlevel
  have hp (n : ℕ) : MemLp (calderonZygmundBadPartialSum f level n) 2 volume :=
    memLp_two_calderonZygmundBadPartialSum hf₂ level n
  have hresult :=
    HarmonicAnalysis.memLp_two_and_eLpNorm_tendsto_zero_of_ae_tendsto_of_norm_le_mul
    (a := b) (b := fun n ↦ calderonZygmundBadPartialSum f level n - b) (C := 2)
    hb
    (fun n ↦ ((hp n).sub hb).aestronglyMeasurable)
    (fun n ↦ ae_of_all _ fun x ↦ by
      calc
        ‖calderonZygmundBadPartialSum f level n x - b x‖ ≤
            ‖calderonZygmundBadPartialSum f level n x‖ + ‖b x‖ := norm_sub_le _ _
        _ ≤ 2 * ‖b x‖ := by
          have hle := norm_calderonZygmundBadPartialSum_le f level n x
          dsimp only [b] at hle ⊢
          linarith)
    (ae_of_all _ fun x ↦ by
      have hx : Tendsto (fun n ↦ calderonZygmundBadPartialSum f level n x - b x) atTop
          (𝓝 (HarmonicAnalysis.calderonZygmundBadSum f level x - b x)) :=
        (calderonZygmundBadPartialSum_tendsto f level x).sub tendsto_const_nhds
      simpa only [b, sub_self] using hx)
  exact hresult.2

/--
%%handwave
name:
  Almost-everywhere absolute convergence of the exterior bad-kernel series
statement:
  If $f\in L^1(\mathbb C)$, then for almost every
  $x\in(\Omega^*)^c$ the series
  $$
    \sum_Q\int_{\mathbb C}-\frac{b_Q(w)}{\pi(x-w)^2}\,dw
  $$
  converges absolutely.
proof:
  Cancellation of $b_Q$ and the first-difference estimate for the Beurling
  kernel bound the exterior $L^1$ norm by a fixed multiple of $\|b_Q\|_1$.
  The integrated bad-piece norms are summable, so Tonelli gives pointwise
  absolute summability almost everywhere.
-/
theorem beurlingKernelIntegral_badPart_ae_summable_compl_enlarged
    {f : ℂ → ℂ} (hf : Integrable f volume) (level : ℝ) :
    ∀ᵐ x ∂volume.restrict
        (HarmonicAnalysis.enlargedMaximalBadDyadicRegion f level)ᶜ,
      Summable (fun Q : HarmonicAnalysis.maximalBadDyadicSquares f level ↦
        beurlingKernelIntegral
          (HarmonicAnalysis.calderonZygmundBadPart f (Q : Set ℂ)) x) := by
  let S := HarmonicAnalysis.maximalBadDyadicSquares f level
  letI := (HarmonicAnalysis.countable_maximalBadDyadicSquares f level).toEncodable
  let E : Set ℂ :=
    (HarmonicAnalysis.enlargedMaximalBadDyadicRegion f level)ᶜ
  let b : S → ℂ → ℂ := fun Q ↦
    HarmonicAnalysis.calderonZygmundBadPart f (Q : Set ℂ)
  let A : S → ℂ → ℂ := fun Q ↦ beurlingKernelIntegral (b Q)
  let F : S → ℂ → ℂ := fun Q ↦ E.indicator (A Q)
  have hE : MeasurableSet E :=
    (HarmonicAnalysis.measurableSet_enlargedMaximalBadDyadicRegion
      f level).compl
  have hKm : Measurable planarBeurlingKernel := by
    unfold planarBeurlingKernel
    fun_prop
  have hbint (Q : S) : Integrable (b Q) volume :=
    HarmonicAnalysis.Integrable.integrable_calderonZygmundBadPart hf
      (HarmonicAnalysis.measurableSet_of_mem_maximalBadDyadicSquares Q.2)
      (HarmonicAnalysis.volume_ne_top_of_mem_maximalBadDyadicSquares Q.2)
  have hAi (Q : S) : IntegrableOn (A Q)
      {x : ℂ | 2 * HarmonicAnalysis.maximalBadDyadicSquareRadius Q <
        ‖x - HarmonicAnalysis.maximalBadDyadicSquareCenter Q‖} volume := by
    simpa only [A, b, beurlingKernelIntegral] using
      (HarmonicAnalysis.HasKernelFirstDifference.integrableOn_integral_mul_exterior_of_integral_eq_zero
        planarBeurlingKernel planarBeurlingKernel_hasKernelFirstDifference
        hKm (by positivity : 0 ≤ 6 * (Real.pi)⁻¹)
        (HarmonicAnalysis.maximalBadDyadicSquareRadius_pos Q)
        (HarmonicAnalysis.maximalBadDyadicSquareCenter Q) (b Q) (hbint Q)
        (fun y hy ↦ HarmonicAnalysis.calderonZygmundBadPart_mem_supportDisk Q hy)
        (HarmonicAnalysis.integral_calderonZygmundBadPart_eq_zero hf
          (HarmonicAnalysis.measurableSet_of_mem_maximalBadDyadicSquares Q.2)
          (HarmonicAnalysis.volume_ne_top_of_mem_maximalBadDyadicSquares Q.2)))
  have hsub (Q : S) : E ⊆
      {x : ℂ | 2 * HarmonicAnalysis.maximalBadDyadicSquareRadius Q <
        ‖x - HarmonicAnalysis.maximalBadDyadicSquareCenter Q‖} := by
    intro x hx
    have hxcommon : x ∈ {x : ℂ | ∀ R : S,
        2 * HarmonicAnalysis.maximalBadDyadicSquareRadius R <
          ‖x - HarmonicAnalysis.maximalBadDyadicSquareCenter R‖} := by
      rw [HarmonicAnalysis.maximalBadDyadicCommonExterior_eq_compl f level]
      exact hx
    exact hxcommon Q
  have hFint (Q : S) : Integrable (F Q) volume := by
    simpa only [F] using ((hAi Q).mono_set (hsub Q)).integrable_indicator hE
  have hFbound (Q : S) :
      (∫ x, ‖F Q x‖ ∂volume) ≤
        Real.pi * (6 * (Real.pi)⁻¹) * ∫ y, ‖b Q y‖ ∂volume := by
    calc
      (∫ x, ‖F Q x‖ ∂volume) = ∫ x in E, ‖A Q x‖ ∂volume := by
        simp only [F, norm_indicator_eq_indicator_norm, integral_indicator hE]
      _ ≤ ∫ x in {x : ℂ |
          2 * HarmonicAnalysis.maximalBadDyadicSquareRadius Q <
            ‖x - HarmonicAnalysis.maximalBadDyadicSquareCenter Q‖},
          ‖A Q x‖ ∂volume := by
        apply setIntegral_mono_set (hAi Q).norm
          (ae_of_all _ fun _ ↦ norm_nonneg _)
        exact ae_of_all _ fun x hx ↦ hsub Q hx
      _ ≤ Real.pi * (6 * (Real.pi)⁻¹) * ∫ y, ‖b Q y‖ ∂volume := by
        simpa only [A, b, beurlingKernelIntegral] using
          (HarmonicAnalysis.HasKernelFirstDifference.setIntegral_norm_integral_mul_le_of_integral_eq_zero
            planarBeurlingKernel planarBeurlingKernel_hasKernelFirstDifference
            hKm (by positivity : 0 ≤ 6 * (Real.pi)⁻¹)
            (HarmonicAnalysis.maximalBadDyadicSquareRadius_pos Q)
            (HarmonicAnalysis.maximalBadDyadicSquareCenter Q) (b Q) (hbint Q)
            (fun y hy ↦ HarmonicAnalysis.calderonZygmundBadPart_mem_supportDisk Q hy)
            (HarmonicAnalysis.integral_calderonZygmundBadPart_eq_zero hf
              (HarmonicAnalysis.measurableSet_of_mem_maximalBadDyadicSquares Q.2)
              (HarmonicAnalysis.volume_ne_top_of_mem_maximalBadDyadicSquares Q.2)))
  have hFsum : Summable (fun Q : S ↦ ∫ x, ‖F Q x‖ ∂volume) := by
    apply Summable.of_nonneg_of_le
    · exact fun Q ↦ integral_nonneg fun _ ↦ norm_nonneg _
    · exact hFbound
    · exact (HarmonicAnalysis.summable_integral_norm_calderonZygmundBadPart
        hf level).mul_left (Real.pi * (6 * (Real.pi)⁻¹))
  have hae := HarmonicAnalysis.ae_summable_norm_of_summable_integral_norm
    hFint hFsum
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hE] with x hxsum hxE
  change x ∈ E at hxE
  have hxsumF : Summable (fun Q : S ↦ F Q x) := hxsum.of_norm
  have hFA : (fun Q : S ↦ F Q x) = fun Q ↦ A Q x := by
    funext Q
    simp only [F, indicator_of_mem hxE]
  rw [hFA] at hxsumF
  simpa only [A, b] using hxsumF

/--
%%handwave
name:
  Exterior physical bad sums converge in $L^1$
statement:
  If $f\in L^1(\mathbb C)$ and
  $$
    K_Q(x)=\int_{\mathbb C}-\frac{b_Q(w)}{\pi(x-w)^2}\,dw,
  $$
  then on $(\Omega^*)^c$,
  $$
    \left\|\sum_{Q\in\mathcal F_n}K_Q-\sum_QK_Q\right\|_{L^1}
      \longrightarrow0.
  $$
proof:
  The exterior integrals $\int|K_Q|$ form a summable series. Hence the
  pointwise norm series is an integrable majorant, the finite sums converge
  almost everywhere along the cofinal exhaustion, and dominated convergence
  yields convergence in $L^1$.
-/
theorem beurlingKernelIntegral_badPartialSum_eLpNorm_one_tendsto
    {f : ℂ → ℂ} (hf : Integrable f volume) (level : ℝ) :
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ ∑ Q ∈ maximalBadDyadicFinsetExhaustion (f := f) level n,
          beurlingKernelIntegral
            (HarmonicAnalysis.calderonZygmundBadPart f (Q : Set ℂ)) x) -
        fun x ↦ ∑' Q : HarmonicAnalysis.maximalBadDyadicSquares f level,
          beurlingKernelIntegral
            (HarmonicAnalysis.calderonZygmundBadPart f (Q : Set ℂ)) x)
      1 (volume.restrict
        (HarmonicAnalysis.enlargedMaximalBadDyadicRegion f level)ᶜ))
      atTop (nhds 0) := by
  let S := HarmonicAnalysis.maximalBadDyadicSquares f level
  letI := (HarmonicAnalysis.countable_maximalBadDyadicSquares f level).toEncodable
  let E : Set ℂ :=
    (HarmonicAnalysis.enlargedMaximalBadDyadicRegion f level)ᶜ
  let μE : Measure ℂ := volume.restrict E
  let b : S → ℂ → ℂ := fun Q ↦
    HarmonicAnalysis.calderonZygmundBadPart f (Q : Set ℂ)
  let A : S → ℂ → ℂ := fun Q ↦ beurlingKernelIntegral (b Q)
  let P : ℕ → ℂ → ℂ := fun n x ↦
    ∑ Q ∈ maximalBadDyadicFinsetExhaustion (f := f) level n, A Q x
  let T : ℂ → ℂ := fun x ↦ ∑' Q : S, A Q x
  let H : ℂ → ℝ := fun x ↦ ∑' Q : S, ‖A Q x‖
  have hKm : Measurable planarBeurlingKernel := by
    unfold planarBeurlingKernel
    fun_prop
  have hbint (Q : S) : Integrable (b Q) volume :=
    HarmonicAnalysis.Integrable.integrable_calderonZygmundBadPart hf
      (HarmonicAnalysis.measurableSet_of_mem_maximalBadDyadicSquares Q.2)
      (HarmonicAnalysis.volume_ne_top_of_mem_maximalBadDyadicSquares Q.2)
  have hAi (Q : S) : IntegrableOn (A Q)
      {x : ℂ | 2 * HarmonicAnalysis.maximalBadDyadicSquareRadius Q <
        ‖x - HarmonicAnalysis.maximalBadDyadicSquareCenter Q‖} volume := by
    simpa only [A, b, beurlingKernelIntegral] using
      (HarmonicAnalysis.HasKernelFirstDifference.integrableOn_integral_mul_exterior_of_integral_eq_zero
        planarBeurlingKernel planarBeurlingKernel_hasKernelFirstDifference
        hKm (by positivity : 0 ≤ 6 * (Real.pi)⁻¹)
        (HarmonicAnalysis.maximalBadDyadicSquareRadius_pos Q)
        (HarmonicAnalysis.maximalBadDyadicSquareCenter Q) (b Q) (hbint Q)
        (fun y hy ↦ HarmonicAnalysis.calderonZygmundBadPart_mem_supportDisk Q hy)
        (HarmonicAnalysis.integral_calderonZygmundBadPart_eq_zero hf
          (HarmonicAnalysis.measurableSet_of_mem_maximalBadDyadicSquares Q.2)
          (HarmonicAnalysis.volume_ne_top_of_mem_maximalBadDyadicSquares Q.2)))
  have hsub (Q : S) : E ⊆
      {x : ℂ | 2 * HarmonicAnalysis.maximalBadDyadicSquareRadius Q <
        ‖x - HarmonicAnalysis.maximalBadDyadicSquareCenter Q‖} := by
    intro x hx
    have hxcommon : x ∈ {x : ℂ | ∀ R : S,
        2 * HarmonicAnalysis.maximalBadDyadicSquareRadius R <
          ‖x - HarmonicAnalysis.maximalBadDyadicSquareCenter R‖} := by
      rw [HarmonicAnalysis.maximalBadDyadicCommonExterior_eq_compl f level]
      exact hx
    exact hxcommon Q
  have hAint (Q : S) : Integrable (A Q) μE := by
    simpa only [μE] using (hAi Q).mono_set (hsub Q)
  have hAbound (Q : S) :
      (∫ x, ‖A Q x‖ ∂μE) ≤
        Real.pi * (6 * (Real.pi)⁻¹) * ∫ y, ‖b Q y‖ ∂volume := by
    calc
      (∫ x, ‖A Q x‖ ∂μE) = ∫ x in E, ‖A Q x‖ ∂volume := rfl
      _ ≤ ∫ x in {x : ℂ |
          2 * HarmonicAnalysis.maximalBadDyadicSquareRadius Q <
            ‖x - HarmonicAnalysis.maximalBadDyadicSquareCenter Q‖},
          ‖A Q x‖ ∂volume := by
        apply setIntegral_mono_set (hAi Q).norm
          (ae_of_all _ fun _ ↦ norm_nonneg _)
        exact ae_of_all _ fun x hx ↦ hsub Q hx
      _ ≤ Real.pi * (6 * (Real.pi)⁻¹) * ∫ y, ‖b Q y‖ ∂volume := by
        simpa only [A, b, beurlingKernelIntegral] using
          (HarmonicAnalysis.HasKernelFirstDifference.setIntegral_norm_integral_mul_le_of_integral_eq_zero
            planarBeurlingKernel planarBeurlingKernel_hasKernelFirstDifference
            hKm (by positivity : 0 ≤ 6 * (Real.pi)⁻¹)
            (HarmonicAnalysis.maximalBadDyadicSquareRadius_pos Q)
            (HarmonicAnalysis.maximalBadDyadicSquareCenter Q) (b Q) (hbint Q)
            (fun y hy ↦ HarmonicAnalysis.calderonZygmundBadPart_mem_supportDisk Q hy)
            (HarmonicAnalysis.integral_calderonZygmundBadPart_eq_zero hf
              (HarmonicAnalysis.measurableSet_of_mem_maximalBadDyadicSquares Q.2)
              (HarmonicAnalysis.volume_ne_top_of_mem_maximalBadDyadicSquares Q.2)))
  have hAsum : Summable (fun Q : S ↦ ∫ x, ‖A Q x‖ ∂μE) := by
    apply Summable.of_nonneg_of_le
    · exact fun Q ↦ integral_nonneg fun _ ↦ norm_nonneg _
    · exact hAbound
    · exact (HarmonicAnalysis.summable_integral_norm_calderonZygmundBadPart
        hf level).mul_left (Real.pi * (6 * (Real.pi)⁻¹))
  have hH_int : Integrable H μE := by
    apply HarmonicAnalysis.integrable_tsum_of_summable_integral_norm
      (fun Q ↦ (hAint Q).norm)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hAsum
  have hsum_norm : ∀ᵐ x ∂μE, Summable (fun Q : S ↦ ‖A Q x‖) :=
    HarmonicAnalysis.ae_summable_norm_of_summable_integral_norm hAint hAsum
  have hPmeas (n : ℕ) : AEStronglyMeasurable (P n) μE := by
    exact (integrable_finsetSum (maximalBadDyadicFinsetExhaustion (f := f) level n)
      (fun Q _ ↦ hAint Q)).aestronglyMeasurable
  have hPbound (n : ℕ) : ∀ᵐ x ∂μE, ‖P n x‖ ≤ H x := by
    filter_upwards [hsum_norm] with x hx
    calc
      ‖P n x‖ ≤ ∑ Q ∈ maximalBadDyadicFinsetExhaustion (f := f) level n,
          ‖A Q x‖ := by
        dsimp only [P]
        exact norm_sum_le _ _
      _ ≤ ∑' Q : S, ‖A Q x‖ := by
        exact hx.sum_le_tsum _ (fun Q _ ↦ norm_nonneg (A Q x))
      _ = H x := rfl
  have hP_tendsto : ∀ᵐ x ∂μE,
      Tendsto (fun n ↦ P n x) atTop (nhds (T x)) := by
    filter_upwards [hsum_norm] with x hx
    exact hx.of_norm.hasSum.comp
      (maximalBadDyadicFinsetExhaustion_tendsto (f := f) level)
  have hraw := tendsto_lintegral_norm_of_dominated_convergence
    hPmeas hH_int.2 hPbound hP_tendsto
  have heq (z : ℂ) : ENNReal.ofReal ‖z‖ = ‖z‖ₑ := by
    exact ofReal_norm z
  simpa only [eLpNorm_one_eq_lintegral_enorm, heq,
    P, T, A, b, μE, E, Pi.sub_apply] using hraw

/--
%%handwave
name:
  Countable physical formula for the total Beurling bad part
statement:
  Let $f\in L^1(\mathbb C)\cap L^2(\mathbb C)$ and let $\alpha>0$. If $b_Q$
  are its maximal-square bad pieces, $b=\sum_Qb_Q$, and $\Omega^*$ is the
  union of their doubled support disks, then for almost every
  $x\in(\Omega^*)^c$,
  $$
    \mathcal S b(x)=\sum_Q
      \int_{\mathbb C}-\frac{b_Q(w)}{\pi(x-w)^2}\,dw.
  $$
proof:
  The finite bad sums tend to $b$ in $L^2$, so their Beurling transforms
  converge in measure to $\mathcal Sb$. Their finite physical kernel sums
  converge in $L^1$, hence in measure, to the series on the right. The
  [finite physical formula](lean:JJMath.Quasiconformal.beurlingTransformL2_badPartialSum_eq_kernelIntegral)
  identifies the approximating sequences almost everywhere, so uniqueness
  of limits in measure identifies the two limits.
-/
theorem beurlingTransformL2_badSum_eq_tsum_kernelIntegral_ae_compl_enlarged
    {f : ℂ → ℂ} (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume)
    {level : ℝ} (hlevel : 0 < level) :
    (beurlingTransformL2
      ((HarmonicAnalysis.memLp_two_calderonZygmundBadSum hf₁ hf₂ hlevel).toLp
        (HarmonicAnalysis.calderonZygmundBadSum f level)) : ℂ → ℂ) =ᵐ[
      volume.restrict
        (HarmonicAnalysis.enlargedMaximalBadDyadicRegion f level)ᶜ]
      fun x ↦ ∑' Q : HarmonicAnalysis.maximalBadDyadicSquares f level,
        beurlingKernelIntegral
          (HarmonicAnalysis.calderonZygmundBadPart f (Q : Set ℂ)) x := by
  let S := HarmonicAnalysis.maximalBadDyadicSquares f level
  letI := (HarmonicAnalysis.countable_maximalBadDyadicSquares f level).toEncodable
  let E : Set ℂ :=
    (HarmonicAnalysis.enlargedMaximalBadDyadicRegion f level)ᶜ
  let μE : Measure ℂ := volume.restrict E
  let b := HarmonicAnalysis.calderonZygmundBadSum f level
  let hb : MemLp b 2 volume :=
    HarmonicAnalysis.memLp_two_calderonZygmundBadSum hf₁ hf₂ hlevel
  let P : ℕ → ℂ → ℂ := fun n x ↦
    ∑ Q ∈ maximalBadDyadicFinsetExhaustion (f := f) level n,
      beurlingKernelIntegral
        (HarmonicAnalysis.calderonZygmundBadPart f (Q : Set ℂ)) x
  let T : ℂ → ℂ := fun x ↦ ∑' Q : S,
    beurlingKernelIntegral
      (HarmonicAnalysis.calderonZygmundBadPart f (Q : Set ℂ)) x
  have hp (n : ℕ) : MemLp (calderonZygmundBadPartialSum f level n) 2 volume :=
    memLp_two_calderonZygmundBadPartialSum hf₂ level n
  have hinput : Tendsto
      (fun n ↦ (hp n).toLp (calderonZygmundBadPartialSum f level n)) atTop
      (nhds (hb.toLp b)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n ↦ calderonZygmundBadPartialSum f level n) hp b hb).2
    exact calderonZygmundBadPartialSum_sub_badSum_eLpNorm_tendsto hf₁ hf₂ hlevel
  have hfourierGlobal : TendstoInMeasure volume
      (fun n ↦
        (beurlingTransformL2
          ((hp n).toLp (calderonZygmundBadPartialSum f level n)) : ℂ → ℂ))
      atTop (beurlingTransformL2 (hb.toLp b) : ℂ → ℂ) := by
    apply tendstoInMeasure_of_tendsto_Lp
    exact beurlingTransformL2.continuous.continuousAt.tendsto.comp hinput
  have hfourier : TendstoInMeasure μE
      (fun n ↦
        (beurlingTransformL2
          ((hp n).toLp (calderonZygmundBadPartialSum f level n)) : ℂ → ℂ))
      atTop (beurlingTransformL2 (hb.toLp b) : ℂ → ℂ) := by
    exact tendstoInMeasure_mono_measure Measure.restrict_le_self hfourierGlobal
  have hformula (n : ℕ) :
      (beurlingTransformL2
        ((hp n).toLp (calderonZygmundBadPartialSum f level n)) : ℂ → ℂ) =ᵐ[μE]
        P n := by
    simpa only [μE, E, P] using
      beurlingTransformL2_badPartialSum_eq_kernelIntegral hf₂ level n
  have hPmeas (n : ℕ) : AEStronglyMeasurable (P n) μE := by
    exact ((Lp.aestronglyMeasurable
      (beurlingTransformL2
        ((hp n).toLp (calderonZygmundBadPartialSum f level n)))).mono_measure
        Measure.restrict_le_self).congr (hformula n)
  have hPtendsto : ∀ᵐ x ∂μE, Tendsto (fun n ↦ P n x) atTop (nhds (T x)) := by
    filter_upwards [beurlingKernelIntegral_badPart_ae_summable_compl_enlarged
      hf₁ level] with x hx
    exact hx.hasSum.comp
      (maximalBadDyadicFinsetExhaustion_tendsto (f := f) level)
  have hTmeas : AEStronglyMeasurable T μE :=
    aestronglyMeasurable_of_tendsto_ae _ hPmeas hPtendsto
  have hphysical : TendstoInMeasure μE P atTop T := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1)
    · norm_num
    · exact hPmeas
    · exact hTmeas
    · simpa only [P, T, μE, E] using
        beurlingKernelIntegral_badPartialSum_eLpNorm_one_tendsto hf₁ level
  have hphysicalFourier : TendstoInMeasure μE
      (fun n ↦
        (beurlingTransformL2
          ((hp n).toLp (calderonZygmundBadPartialSum f level n)) : ℂ → ℂ))
      atTop T :=
    hphysical.congr_left (fun n ↦ (hformula n).symm)
  simpa only [μE, E, T, hb, b] using
    tendstoInMeasure_ae_unique hfourier hphysicalFourier

end Quasiconformal

end JJMath
