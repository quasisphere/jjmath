import JJMath.Analysis.Harmonic.Dyadic
import JJMath.Analysis.Harmonic.DyadicDifferentiation
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The dyadic Calderón--Zygmund stopping time

This file applies the abstract maximal-square geometry of the planar dyadic
grid to the standard Calderón--Zygmund stopping predicate. A square is bad
when the integral of the norm of the function over the square exceeds the
chosen level times its area. Integrability rules out bad squares at every
sufficiently coarse scale, so every bad square lies in a maximal one. The
resulting maximal family is countable and pairwise disjoint.
-/

namespace JJMath

open Set MeasureTheory Filter Function
open scoped Topology ENNReal

namespace HarmonicAnalysis

noncomputable section

/--
%%handwave
name:
  Bad planar dyadic square
statement:
  Let $f:\mathbb C\to E$ be a normed-space-valued function and let
  $\alpha\in\mathbb R$. The dyadic square $Q_{n,k}$ is bad at level $\alpha$
  when
  $$
    \alpha\,|Q_{n,k}|<\int_{Q_{n,k}}\|f(x)\|\,dx.
  $$
  This division-free formulation is equivalent to requiring the average of
  $\|f\|$ on the square to exceed $\alpha$ whenever $\alpha>0$.
-/
def IsBadDyadicSquare {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (level : ℝ) (n : ℤ) (k : ℤ × ℤ) : Prop :=
  level * (volume (dyadicSquare n k)).toReal <
    ∫ x in dyadicSquare n k, ‖f x‖ ∂volume

/--
%%handwave
name:
  Maximal bad planar dyadic squares
statement:
  The maximal bad-square family of $f$ at level $\alpha$ consists of the
  inclusion-maximal dyadic squares $Q$ satisfying
  $$
    \alpha |Q|<\int_Q\|f(x)\|\,dx.
  $$
-/
def maximalBadDyadicSquares {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (level : ℝ) : Set (Set ℂ) :=
  {Q | IsMaximalDyadicSquare (IsBadDyadicSquare f level) Q}

/--
%%handwave
name:
  Bad dyadic region
statement:
  The bad dyadic region of $f$ at level $\alpha$ is the union of all dyadic
  squares $Q$ satisfying
  $$
    \alpha |Q|<\int_Q\|f(x)\|\,dx.
  $$
-/
def badDyadicRegion {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (level : ℝ) : Set ℂ :=
  {x | ∃ n k, IsBadDyadicSquare f level n k ∧ x ∈ dyadicSquare n k}

/--
%%handwave
name:
  Maximal bad dyadic region
statement:
  The maximal bad dyadic region of $f$ at level $\alpha$ is the union of all
  maximal bad dyadic squares of $f$ at that level.
-/
def maximalBadDyadicRegion {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (level : ℝ) : Set ℂ :=
  ⋃₀ maximalBadDyadicSquares f level

/--
%%handwave
name:
  Integrable functions have no sufficiently coarse bad dyadic squares
statement:
  If $f:\mathbb C\to E$ is integrable and $\alpha>0$, then there is an
  integer scale $M$ such that, for every $m\geq M$ and every dyadic index
  $k$, one has
  $$
    \int_{Q_{m,k}}\|f(x)\|\,dx\leq \alpha |Q_{m,k}|.
  $$
proof:
  The integral over any square is at most $\|f\|_{L^1}$. On the other hand,
  every square of scale $m$ has area $4^m$, which tends to infinity as
  $m\to\infty$. Choose $M$ so that $\alpha4^M>\|f\|_{L^1}$ and use
  monotonicity of integer powers for $m\geq M$.
-/
theorem Integrable.exists_coarse_scale_not_isBadDyadicSquare
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : Integrable f volume) {level : ℝ} (hlevel : 0 < level) :
    ∃ M : ℤ, ∀ m k, M ≤ m → ¬ IsBadDyadicSquare f level m k := by
  let A : ℝ := ∫ x, ‖f x‖ ∂volume
  obtain ⟨N, hN⟩ :=
    pow_unbounded_of_one_lt (A / level) (by norm_num : (1 : ℝ) < 4)
  refine ⟨(N : ℤ), ?_⟩
  intro m k hNm hbad
  have hside : dyadicSide (N : ℤ) ≤ dyadicSide m := by
    exact zpow_le_zpow_right₀ (by norm_num) hNm
  have hsquare : dyadicSide (N : ℤ) ^ 2 ≤ dyadicSide m ^ 2 :=
    pow_le_pow_left₀ (dyadicSide_pos (N : ℤ)).le hside 2
  have harea : (4 : ℝ) ^ N ≤ (volume (dyadicSquare m k)).toReal := by
    rw [volume_dyadicSquare, ENNReal.toReal_ofReal (sq_nonneg _)]
    rw [show (4 : ℝ) ^ N = dyadicSide (N : ℤ) ^ 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      rw [Nat.mul_comm, pow_mul, dyadicSide, zpow_natCast]]
    exact hsquare
  have hglobal : A < level * (volume (dyadicSquare m k)).toReal := by
    simpa [mul_comm] using (div_lt_iff₀ hlevel).mp (hN.trans_le harea)
  have hset : (∫ x in dyadicSquare m k, ‖f x‖ ∂volume) ≤ A := by
    exact setIntegral_le_integral hf.norm
      (ae_of_all _ fun x ↦ norm_nonneg (f x))
  exact (not_lt_of_ge hglobal.le) (hbad.trans_le hset)

/--
%%handwave
name:
  Every bad dyadic square lies in a maximal bad square
statement:
  Let $f:\mathbb C\to E$ be integrable and let $\alpha>0$. If the dyadic
  square $Q_{n,k}$ satisfies
  $$
    \alpha |Q_{n,k}|<\int_{Q_{n,k}}\|f(x)\|\,dx,
  $$
  then there is a maximal bad dyadic square $Q$ with $Q_{n,k}\subseteq Q$.
proof:
  By [integrability rules out all sufficiently coarse bad squares](lean:JJMath.HarmonicAnalysis.Integrable.exists_coarse_scale_not_isBadDyadicSquare). Apply the abstract existence theorem for a maximal dyadic super-square to the bad-square predicate.
-/
theorem IsBadDyadicSquare.exists_maximal_superset
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : Integrable f volume) {level : ℝ} (hlevel : 0 < level)
    {n : ℤ} {k : ℤ × ℤ} (hbad : IsBadDyadicSquare f level n k) :
    ∃ Q : Set ℂ, Q ∈ maximalBadDyadicSquares f level ∧
      dyadicSquare n k ⊆ Q := by
  exact exists_maximalDyadicSquare_superset (IsBadDyadicSquare f level) hbad
    (Integrable.exists_coarse_scale_not_isBadDyadicSquare hf hlevel)

/--
%%handwave
name:
  Maximal bad dyadic squares are pairwise disjoint
statement:
  For every normed-space-valued function $f$ and every level $\alpha$, any
  two distinct maximal bad dyadic squares of $f$ at level $\alpha$ are
  disjoint.
proof:
  This is the [pairwise-disjointness theorem for maximal squares of an arbitrary dyadic predicate](lean:JJMath.HarmonicAnalysis.pairwiseDisjoint_maximalDyadicSquare), applied to the bad-square predicate.
-/
theorem pairwiseDisjoint_maximalBadDyadicSquares
    {E : Type*} [NormedAddCommGroup E] (f : ℂ → E) (level : ℝ) :
    (maximalBadDyadicSquares f level).PairwiseDisjoint id := by
  exact pairwiseDisjoint_maximalDyadicSquare (IsBadDyadicSquare f level)

/--
%%handwave
name:
  Countability of the maximal bad-square family
statement:
  For every normed-space-valued function $f$ and every level $\alpha$, the
  family of maximal bad dyadic squares of $f$ at level $\alpha$ is
  countable.
proof:
  Apply [countability of maximal squares for an arbitrary dyadic predicate](lean:JJMath.HarmonicAnalysis.countable_maximalDyadicSquare) to the bad-square predicate.
-/
theorem countable_maximalBadDyadicSquares
    {E : Type*} [NormedAddCommGroup E] (f : ℂ → E) (level : ℝ) :
    (maximalBadDyadicSquares f level).Countable := by
  exact countable_maximalDyadicSquare (IsBadDyadicSquare f level)

/--
%%handwave
name:
  Measurability of every maximal bad dyadic square
statement:
  Every member of the maximal bad-square family is a Lebesgue measurable
  subset of the plane.
proof:
  By definition, every member of the family is a planar dyadic square, and
  all planar dyadic squares are measurable.
-/
theorem measurableSet_of_mem_maximalBadDyadicSquares
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {level : ℝ}
    {Q : Set ℂ} (hQ : Q ∈ maximalBadDyadicSquares f level) :
    MeasurableSet Q := by
  rcases hQ with ⟨n, k, _hbad, rfl, _hmaximal⟩
  exact measurableSet_dyadicSquare n k

/--
%%handwave
name:
  A maximal bad dyadic square has finite area
statement:
  Every maximal bad dyadic square $Q$ has finite planar area:
  $$|Q|<\infty.$$
proof:
  Such a set is a dyadic square, whose area is the finite real number
  $(2^n)^2$.
-/
theorem volume_ne_top_of_mem_maximalBadDyadicSquares
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {level : ℝ}
    {Q : Set ℂ} (hQ : Q ∈ maximalBadDyadicSquares f level) :
    volume Q ≠ ∞ := by
  rcases hQ with ⟨n, k, _hbad, rfl, _hmaximal⟩
  rw [volume_dyadicSquare]
  exact ENNReal.ofReal_ne_top

/--
%%handwave
name:
  A maximal bad dyadic square has positive area
statement:
  Every maximal bad dyadic square $Q$ has strictly positive planar area:
  $$0<|Q|<\infty.$$
proof:
  Such a set has area $(2^n)^2$, and $2^n>0$.
-/
theorem volume_toReal_pos_of_mem_maximalBadDyadicSquares
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {level : ℝ}
    {Q : Set ℂ} (hQ : Q ∈ maximalBadDyadicSquares f level) :
    0 < (volume Q).toReal := by
  rcases hQ with ⟨n, k, _hbad, rfl, _hmaximal⟩
  rw [volume_dyadicSquare, ENNReal.toReal_ofReal (sq_nonneg _)]
  exact sq_pos_of_pos (dyadicSide_pos n)

/--
%%handwave
name:
  Measurability of the maximal bad dyadic region
statement:
  The union of all maximal bad dyadic squares of a function at a fixed level
  is Lebesgue measurable.
proof:
  The maximal family is countable and each of its members is measurable, so
  its union is measurable.
-/
theorem measurableSet_maximalBadDyadicRegion
    {E : Type*} [NormedAddCommGroup E] (f : ℂ → E) (level : ℝ) :
    MeasurableSet (maximalBadDyadicRegion f level) := by
  exact MeasurableSet.sUnion (countable_maximalBadDyadicSquares f level)
    (fun Q hQ ↦ measurableSet_of_mem_maximalBadDyadicSquares hQ)

/--
%%handwave
name:
  All bad squares are covered by the maximal bad squares
statement:
  If $f:\mathbb C\to E$ is integrable and $\alpha>0$, then the union of all
  bad dyadic squares at level $\alpha$ equals the union of the maximal bad
  dyadic squares:
  $$
    \bigcup_{Q\,\mathrm{bad}}Q
      =\bigcup_{Q\,\mathrm{maximal\ bad}}Q.
  $$
proof:
  [Every bad square lies in a maximal bad square](lean:JJMath.HarmonicAnalysis.IsBadDyadicSquare.exists_maximal_superset), which gives one inclusion. Conversely, every maximal bad square is itself one of the bad squares appearing in the first union.
-/
theorem badDyadicRegion_eq_maximalBadDyadicRegion
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : Integrable f volume) {level : ℝ} (hlevel : 0 < level) :
    badDyadicRegion f level = maximalBadDyadicRegion f level := by
  ext x
  constructor
  · rintro ⟨n, k, hbad, hx⟩
    obtain ⟨Q, hQ, hsub⟩ := hbad.exists_maximal_superset hf hlevel
    exact Set.mem_sUnion.2 ⟨Q, hQ, hsub hx⟩
  · intro hx
    rcases Set.mem_sUnion.1 hx with ⟨Q, hQ, hxQ⟩
    rcases hQ with ⟨n, k, hbad, hQ, _hmaximal⟩
    exact ⟨n, k, hbad, hQ ▸ hxQ⟩

/--
%%handwave
name:
  The bad dyadic region covers the pointwise high-value set almost everywhere
statement:
  If $f:\mathbb C\to E$ is integrable, then for almost every
  $z\in\mathbb C$ and every $\alpha\in\mathbb R$,
  $$
    \alpha<\|f(z)\|\quad\Longrightarrow\quad
    z\in\bigcup_{Q:\,\alpha|Q|<\int_Q\|f\|}Q.
  $$
proof:
  At almost every $z$, [the mean oscillation of $f$ over the point-selected dyadic squares tends to zero](lean:JJMath.HarmonicAnalysis.ae_tendsto_dyadicAverage_norm_sub). If $\|f(z)\|>\alpha$, choose a sufficiently fine square on which the mean oscillation is less than $\|f(z)\|-\alpha$. Integrating the triangle inequality then shows that the mean of $\|f\|$ on that square exceeds $\alpha$.
-/
theorem ae_mem_badDyadicRegion_of_lt_norm
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : Integrable f volume) (level : ℝ) :
    ∀ᵐ z ∂volume, level < ‖f z‖ → z ∈ badDyadicRegion f level := by
  filter_upwards [ae_tendsto_dyadicAverage_norm_sub hf] with z hz
  intro hzlevel
  have hgap : 0 < ‖f z‖ - level := sub_pos.mpr hzlevel
  have hevent : ∀ᶠ j : ℕ in atTop,
      (⨍ y in dyadicSquare (-(j : ℤ)) (dyadicIndex (-(j : ℤ)) z),
        ‖f y - f z‖ ∂volume) < ‖f z‖ - level :=
    (tendsto_order.1 hz).2 _ hgap
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  let n : ℤ := -(N : ℤ)
  let k : ℤ × ℤ := dyadicIndex n z
  have havg : (⨍ y in dyadicSquare n k, ‖f y - f z‖ ∂volume) <
      ‖f z‖ - level := by
    exact hN N le_rfl
  have harea : 0 < (volume (dyadicSquare n k)).toReal := by
    rw [volume_dyadicSquare, ENNReal.toReal_ofReal (sq_nonneg _)]
    exact sq_pos_of_pos (dyadicSide_pos n)
  have hvoltop : volume (dyadicSquare n k) ≠ ∞ := by
    rw [volume_dyadicSquare]
    exact ENNReal.ofReal_ne_top
  have hconst_int : IntegrableOn (fun _ : ℂ ↦ f z) (dyadicSquare n k) volume :=
    integrableOn_const hvoltop
  have hnormdiff_int : IntegrableOn (fun y ↦ ‖f y - f z‖)
      (dyadicSquare n k) volume :=
    (hf.integrableOn.sub hconst_int).norm
  have hsum_int : IntegrableOn (fun y ↦ ‖f y‖ + ‖f y - f z‖)
      (dyadicSquare n k) volume :=
    hf.norm.integrableOn.add hnormdiff_int
  have htriangle : ‖f z‖ * (volume (dyadicSquare n k)).toReal ≤
      ∫ y in dyadicSquare n k, ‖f y‖ + ‖f y - f z‖ ∂volume := by
    apply setIntegral_ge_of_const_le_real (measurableSet_dyadicSquare n k)
      hvoltop _ hsum_int
    intro y _hy
    calc
      ‖f z‖ = ‖f y - (f y - f z)‖ := by congr 1; abel
      _ ≤ ‖f y‖ + ‖f y - f z‖ := norm_sub_le _ _
  have hsplit :
      (∫ y in dyadicSquare n k, ‖f y‖ + ‖f y - f z‖ ∂volume) =
        (∫ y in dyadicSquare n k, ‖f y‖ ∂volume) +
          ∫ y in dyadicSquare n k, ‖f y - f z‖ ∂volume := by
    exact integral_add hf.norm.integrableOn hnormdiff_int
  have hdiff : (∫ y in dyadicSquare n k, ‖f y - f z‖ ∂volume) <
      (‖f z‖ - level) * (volume (dyadicSquare n k)).toReal := by
    rw [setAverage_eq] at havg
    simp only [smul_eq_mul, inv_mul_eq_div] at havg
    exact (div_lt_iff₀ harea).mp havg
  refine ⟨n, k, ?_, mem_dyadicSquare_dyadicIndex n z⟩
  rw [IsBadDyadicSquare]
  rw [hsplit] at htriangle
  nlinarith

/--
%%handwave
name:
  Total area bound for the maximal bad dyadic region
statement:
  If $f:\mathbb C\to E$ is integrable and $\alpha>0$, then
  $$
    \alpha\left|\bigcup_{Q\,\mathrm{maximal\ bad}}Q\right|
      \leq\int_{\mathbb C}\|f(x)\|\,dx.
  $$
proof:
  Index the countable pairwise-disjoint maximal family by the corresponding
  subtype. Countable additivity expresses the area of the union and the
  integral over the union as sums over its squares. On each selected square,
  badness gives $\alpha|Q|<\int_Q\|f\|$. Summing these inequalities and then
  bounding the integral over the union by the global integral proves the
  estimate.
-/
theorem level_mul_volume_maximalBadDyadicRegion_le_integral_norm
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : Integrable f volume) {level : ℝ} (hlevel : 0 < level) :
    level * (volume (maximalBadDyadicRegion f level)).toReal ≤
      ∫ x, ‖f x‖ ∂volume := by
  let S : Set (Set ℂ) := maximalBadDyadicSquares f level
  letI := (countable_maximalBadDyadicSquares f level).toEncodable
  let a : S → ℝ := fun Q ↦ (volume (Q : Set ℂ)).toReal
  let b : S → ℝ := fun Q ↦ ∫ x in (Q : Set ℂ), ‖f x‖ ∂volume
  have hpair : Pairwise (Disjoint on fun Q : S ↦ (Q : Set ℂ)) := by
    intro Q R hne
    apply pairwiseDisjoint_maximalBadDyadicSquares f level Q.2 R.2
    intro hQR
    exact hne (Subtype.ext hQR)
  have hmeas : ∀ Q : S, MeasurableSet (Q : Set ℂ) := fun Q ↦
    measurableSet_of_mem_maximalBadDyadicSquares Q.2
  have hhasSum : HasSum b
      (∫ x in ⋃ Q : S, (Q : Set ℂ), ‖f x‖ ∂volume) := by
    exact hasSum_integral_iUnion hmeas hpair hf.norm.integrableOn
  have hbsum : Summable b := hhasSum.summable
  have ha_nonneg : ∀ Q, 0 ≤ a Q := fun _ ↦ ENNReal.toReal_nonneg
  have hbad : ∀ Q, level * a Q < b Q := by
    intro Q
    rcases Q.2 with ⟨n, k, hbad, hQ, _hmaximal⟩
    simpa only [a, b, IsBadDyadicSquare, hQ] using hbad
  have ha_le : ∀ Q, a Q ≤ level⁻¹ * b Q := by
    intro Q
    have h := (lt_div_iff₀ hlevel).2 (by simpa [mul_comm] using hbad Q)
    simpa only [div_eq_inv_mul] using h.le
  have hasum : Summable a :=
    Summable.of_nonneg_of_le ha_nonneg ha_le (hbsum.mul_left level⁻¹)
  have hsum_le : level * (∑' Q, a Q) ≤ ∑' Q, b Q := by
    rw [← hasum.tsum_mul_left level]
    exact Summable.tsum_le_tsum (fun Q ↦ (hbad Q).le)
      (hasum.mul_left level) hbsum
  have hvolume : (volume (maximalBadDyadicRegion f level)).toReal =
      ∑' Q, a Q := by
    rw [maximalBadDyadicRegion]
    rw [measure_sUnion (countable_maximalBadDyadicSquares f level)
      (pairwiseDisjoint_maximalBadDyadicSquares f level)
      (fun Q hQ ↦ measurableSet_of_mem_maximalBadDyadicSquares hQ)]
    exact ENNReal.tsum_toReal_eq (fun Q ↦ by
      rcases Q.2 with ⟨n, k, _hbad, hQ, _hmaximal⟩
      rw [hQ, volume_dyadicSquare]
      exact ENNReal.ofReal_ne_top)
  rw [hvolume]
  calc
    level * ∑' Q, a Q ≤ ∑' Q, b Q := hsum_le
    _ = ∫ x in ⋃ Q : S, (Q : Set ℂ), ‖f x‖ ∂volume := hhasSum.tsum_eq
    _ ≤ ∫ x, ‖f x‖ ∂volume :=
      setIntegral_le_integral hf.norm (ae_of_all _ fun x ↦ norm_nonneg (f x))

/--
%%handwave
name:
  The parent of a maximal bad square is not bad
statement:
  If $Q_{n,k}$ is maximal among the dyadic squares satisfying
  $$
    \alpha |Q|<\int_Q\|f(x)\|\,dx,
  $$
  then its parent $Q_{n+1,\operatorname{par}(k)}$ does not satisfy this
  strict inequality.
proof:
  If the parent were bad, maximality would make it a subset of the child.
  The child is already contained in its parent, so the sets would be equal,
  contradicting the fact that a parent has four times the child's positive
  area.
-/
theorem not_isBadDyadicSquare_parent_of_mem_maximalBadDyadicSquares
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {level : ℝ}
    {n : ℤ} {k : ℤ × ℤ}
    (hmax : dyadicSquare n k ∈ maximalBadDyadicSquares f level) :
    ¬ IsBadDyadicSquare f level (n + 1) (dyadicParent k) := by
  intro hparent
  rcases hmax with ⟨_m, _l, _hbad, _hQ, hmaximal⟩
  have hsub : dyadicSquare n k ⊆
      dyadicSquare (n + 1) (dyadicParent k) :=
    dyadicSquare_subset_parent n k
  have hback : dyadicSquare (n + 1) (dyadicParent k) ⊆
      dyadicSquare n k :=
    hmaximal (n + 1) (dyadicParent k) hparent hsub
  exact dyadicSquare_ne_parent n k (Subset.antisymm hsub hback)

/--
%%handwave
name:
  Upper average bound on a maximal bad square
statement:
  Let $f:\mathbb C\to E$ be integrable. If $Q$ is a maximal bad dyadic
  square at level $\alpha$, then
  $$
    \int_Q\|f(x)\|\,dx\leq 4\alpha |Q|.
  $$
proof:
  The integral over $Q$ is at most the integral over its parent. By [the parent of a maximal bad square is not bad](lean:JJMath.HarmonicAnalysis.not_isBadDyadicSquare_parent_of_mem_maximalBadDyadicSquares), that parent integral is at most $\alpha$ times the parent area. The parent has four times the area of $Q$.
-/
theorem setIntegral_norm_le_four_mul_level_mul_volume_of_mem_maximalBadDyadicSquares
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : Integrable f volume) {level : ℝ} {n : ℤ} {k : ℤ × ℤ}
    (hmax : dyadicSquare n k ∈ maximalBadDyadicSquares f level) :
    (∫ x in dyadicSquare n k, ‖f x‖ ∂volume) ≤
      4 * level * (volume (dyadicSquare n k)).toReal := by
  have hparent :=
    not_isBadDyadicSquare_parent_of_mem_maximalBadDyadicSquares hmax
  have hmono : (∫ x in dyadicSquare n k, ‖f x‖ ∂volume) ≤
      ∫ x in dyadicSquare (n + 1) (dyadicParent k), ‖f x‖ ∂volume := by
    apply setIntegral_mono_set hf.norm.integrableOn
      (ae_of_all _ fun x ↦ norm_nonneg (f x))
    exact ae_of_all _ fun _ hx ↦ dyadicSquare_subset_parent n k hx
  have hparent_bound :
      (∫ x in dyadicSquare (n + 1) (dyadicParent k), ‖f x‖ ∂volume) ≤
        level * (volume (dyadicSquare (n + 1) (dyadicParent k))).toReal := by
    exact le_of_not_gt hparent
  calc
    (∫ x in dyadicSquare n k, ‖f x‖ ∂volume) ≤
        ∫ x in dyadicSquare (n + 1) (dyadicParent k), ‖f x‖ ∂volume := hmono
    _ ≤ level * (volume (dyadicSquare (n + 1) (dyadicParent k))).toReal :=
      hparent_bound
    _ = 4 * level * (volume (dyadicSquare n k)).toReal := by
      rw [volume_dyadicSquare_parent_toReal]
      ring

end

end HarmonicAnalysis

end JJMath
