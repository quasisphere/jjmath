import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Planar dyadic squares

This file starts the geometric layer for the planar Calderón--Zygmund
decomposition. At each integer scale `n`, the half-open squares have side
length $2^n$ and integer lower-left corners. Floors select the unique square
containing a point. The first API records measurability, the disjoint
partition, exact area, and a simple containing ball for later kernel-tail
estimates.
-/

namespace JJMath

open Set MeasureTheory

namespace HarmonicAnalysis

noncomputable section

/--
%%handwave
name:
  Dyadic side length
statement:
  At integer scale $n\in\mathbb Z$, the planar dyadic side length is $2^n$.
-/
def dyadicSide (n : ℤ) : ℝ := (2 : ℝ) ^ n

/--
%%handwave
name:
  Planar dyadic square
statement:
  For $n\in\mathbb Z$ and $(k_1,k_2)\in\mathbb Z^2$, the corresponding
  half-open dyadic square is
  $$
    [k_1 2^n,(k_1+1)2^n)\times
    [k_2 2^n,(k_2+1)2^n)\subset\mathbb C.
  $$
-/
def dyadicSquare (n : ℤ) (k : ℤ × ℤ) : Set ℂ :=
  {z : ℂ |
    (k.1 : ℝ) * dyadicSide n ≤ z.re ∧
      z.re < (k.1 + 1 : ℤ) * dyadicSide n ∧
    (k.2 : ℝ) * dyadicSide n ≤ z.im ∧
      z.im < (k.2 + 1 : ℤ) * dyadicSide n}

/--
%%handwave
name:
  Dyadic index of a planar point
statement:
  The index of $z\in\mathbb C$ at scale $n$ is
  $$
    \left(\left\lfloor\frac{\operatorname{Re}z}{2^n}\right\rfloor,
    \left\lfloor\frac{\operatorname{Im}z}{2^n}\right\rfloor\right)
    \in\mathbb Z^2.
  $$
-/
def dyadicIndex (n : ℤ) (z : ℂ) : ℤ × ℤ :=
  (⌊z.re / dyadicSide n⌋, ⌊z.im / dyadicSide n⌋)

/--
%%handwave
name:
  Lower-left corner of a planar dyadic square
statement:
  The lower-left corner of the square of scale $n$ and index $(k_1,k_2)$ is
  the complex number $k_1 2^n+i k_2 2^n$.
-/
def dyadicCorner (n : ℤ) (k : ℤ × ℤ) : ℂ :=
  ⟨(k.1 : ℝ) * dyadicSide n, (k.2 : ℝ) * dyadicSide n⟩

/--
%%handwave
name:
  Positivity of dyadic side lengths
statement:
  For every $n\in\mathbb Z$, one has $2^n>0$.
proof:
  Every integer power of a positive real number is positive.
-/
theorem dyadicSide_pos (n : ℤ) : 0 < dyadicSide n := by
  exact zpow_pos (by norm_num) n

/--
%%handwave
name:
  Fine dyadic side lengths tend to zero from above
statement:
  As $j\to\infty$, the positive side lengths $2^{-j}$ tend to zero through
  positive real values.
proof:
  These side lengths are the natural powers of $1/2$, and
  $0<1/2<1$.
-/
theorem tendsto_dyadicSide_neg_nat :
    Filter.Tendsto (fun j : ℕ ↦ dyadicSide (-(j : ℤ))) Filter.atTop
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  simpa only [dyadicSide, zpow_neg, zpow_natCast, inv_pow] using
    (tendsto_pow_atTop_nhdsWithin_zero_of_lt_one
      (by norm_num : 0 < (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1))

/--
%%handwave
name:
  A point lies in the square selected by its dyadic index
statement:
  For every $n\in\mathbb Z$ and $z\in\mathbb C$, the point $z$ belongs to
  the half-open dyadic square whose index is
  $(\lfloor\operatorname{Re}z/2^n\rfloor,
  \lfloor\operatorname{Im}z/2^n\rfloor)$.
proof:
  Apply the defining lower and upper bounds for the floor function to each
  coordinate and multiply by the positive number $2^n$.
-/
theorem mem_dyadicSquare_dyadicIndex (n : ℤ) (z : ℂ) :
    z ∈ dyadicSquare n (dyadicIndex n z) := by
  have hs : 0 < dyadicSide n := dyadicSide_pos n
  have hre_low :
      ((⌊z.re / dyadicSide n⌋ : ℤ) : ℝ) * dyadicSide n ≤ z.re := by
    have h := Int.floor_le (z.re / dyadicSide n)
    calc
      ((⌊z.re / dyadicSide n⌋ : ℤ) : ℝ) * dyadicSide n ≤
          (z.re / dyadicSide n) * dyadicSide n := by gcongr
      _ = z.re := div_mul_cancel₀ _ hs.ne'
  have hre_high : z.re <
      (((⌊z.re / dyadicSide n⌋ : ℤ) + 1 : ℤ) : ℝ) * dyadicSide n := by
    have h := Int.lt_floor_add_one (z.re / dyadicSide n)
    have h' : z.re / dyadicSide n <
        (((⌊z.re / dyadicSide n⌋ : ℤ) + 1 : ℤ) : ℝ) := by
      norm_num at h ⊢
    calc
      z.re = (z.re / dyadicSide n) * dyadicSide n :=
        (div_mul_cancel₀ _ hs.ne').symm
      _ < (((⌊z.re / dyadicSide n⌋ : ℤ) + 1 : ℤ) : ℝ) *
          dyadicSide n := mul_lt_mul_of_pos_right h' hs
  have him_low :
      ((⌊z.im / dyadicSide n⌋ : ℤ) : ℝ) * dyadicSide n ≤ z.im := by
    have h := Int.floor_le (z.im / dyadicSide n)
    calc
      ((⌊z.im / dyadicSide n⌋ : ℤ) : ℝ) * dyadicSide n ≤
          (z.im / dyadicSide n) * dyadicSide n := by gcongr
      _ = z.im := div_mul_cancel₀ _ hs.ne'
  have him_high : z.im <
      (((⌊z.im / dyadicSide n⌋ : ℤ) + 1 : ℤ) : ℝ) * dyadicSide n := by
    have h := Int.lt_floor_add_one (z.im / dyadicSide n)
    have h' : z.im / dyadicSide n <
        (((⌊z.im / dyadicSide n⌋ : ℤ) + 1 : ℤ) : ℝ) := by
      norm_num at h ⊢
    calc
      z.im = (z.im / dyadicSide n) * dyadicSide n :=
        (div_mul_cancel₀ _ hs.ne').symm
      _ < (((⌊z.im / dyadicSide n⌋ : ℤ) + 1 : ℤ) : ℝ) *
          dyadicSide n := mul_lt_mul_of_pos_right h' hs
  exact ⟨hre_low, hre_high, him_low, him_high⟩

/--
%%handwave
name:
  Membership in a dyadic square through the dyadic index
statement:
  A point $z\in\mathbb C$ belongs to the dyadic square of scale $n$ and
  index $k$ if and only if its dyadic index at scale $n$ equals $k$.
proof:
  Divide the four coordinate inequalities by $2^n>0$ and use the
  characterization $\lfloor x\rfloor=k\iff k\leq x<k+1$. The converse uses
  [membership in the square selected by the dyadic index](lean:JJMath.HarmonicAnalysis.mem_dyadicSquare_dyadicIndex).
-/
theorem mem_dyadicSquare_iff_dyadicIndex_eq
    (n : ℤ) (k : ℤ × ℤ) (z : ℂ) :
    z ∈ dyadicSquare n k ↔ dyadicIndex n z = k := by
  have hs : 0 < dyadicSide n := dyadicSide_pos n
  constructor
  · rintro ⟨hre0, hre1, him0, him1⟩
    apply Prod.ext
    · exact Int.floor_eq_iff.mpr ⟨
        (le_div_iff₀ hs).2 hre0,
        (div_lt_iff₀ hs).2 (by simpa using hre1)⟩
    · exact Int.floor_eq_iff.mpr ⟨
        (le_div_iff₀ hs).2 him0,
        (div_lt_iff₀ hs).2 (by simpa using him1)⟩
  · intro h
    rw [← h]
    exact mem_dyadicSquare_dyadicIndex n z

/--
%%handwave
name:
  Measurability of a planar dyadic square
statement:
  Every half-open planar dyadic square is Lebesgue measurable.
proof:
  It is the intersection of four measurable coordinate half-spaces.
-/
theorem measurableSet_dyadicSquare (n : ℤ) (k : ℤ × ℤ) :
    MeasurableSet (dyadicSquare n k) := by
  exact (measurableSet_le measurable_const Complex.measurable_re).inter
    ((measurableSet_lt Complex.measurable_re measurable_const).inter
      ((measurableSet_le measurable_const Complex.measurable_im).inter
        (measurableSet_lt Complex.measurable_im measurable_const)))

/--
%%handwave
name:
  A dyadic square lies in a controlled corner-centered disk
statement:
  The dyadic square of side length $2^n$ and lower-left corner $c$ is
  contained in the closed disk $\overline B(c,2^{n+1})$.
proof:
  Relative to the lower-left corner, both coordinates lie between $0$ and
  $2^n$. Bound the complex norm by the sum of the absolute values of the two
  coordinates.
-/
theorem dyadicSquare_subset_closedBall_dyadicCorner (n : ℤ) (k : ℤ × ℤ) :
    dyadicSquare n k ⊆
      Metric.closedBall (dyadicCorner n k) (2 * dyadicSide n) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hre0 : 0 ≤ (z - dyadicCorner n k).re := by
    change 0 ≤ z.re - (k.1 : ℝ) * dyadicSide n
    exact sub_nonneg.mpr hz.1
  have hre1 : (z - dyadicCorner n k).re ≤ dyadicSide n := by
    have := hz.2.1
    change z.re - (k.1 : ℝ) * dyadicSide n ≤ dyadicSide n
    norm_num at this
    linarith
  have him0 : 0 ≤ (z - dyadicCorner n k).im := by
    change 0 ≤ z.im - (k.2 : ℝ) * dyadicSide n
    exact sub_nonneg.mpr hz.2.2.1
  have him1 : (z - dyadicCorner n k).im ≤ dyadicSide n := by
    have := hz.2.2.2
    change z.im - (k.2 : ℝ) * dyadicSide n ≤ dyadicSide n
    norm_num at this
    linarith
  calc
    ‖z - dyadicCorner n k‖ ≤
        |(z - dyadicCorner n k).re| + |(z - dyadicCorner n k).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = (z - dyadicCorner n k).re + (z - dyadicCorner n k).im := by
      rw [abs_of_nonneg hre0, abs_of_nonneg him0]
    _ ≤ 2 * dyadicSide n := by linarith

/--
%%handwave
name:
  A dyadic square lies in a controlled disk around each of its points
statement:
  If $z\in Q_{n,k}$, then
  $$
    Q_{n,k}\subseteq \overline B(z,4\cdot2^n).
  $$
proof:
  Both $z$ and an arbitrary point of the square lie within distance
  $2\cdot2^n$ of the lower-left corner. The triangle inequality gives the
  stated radius.
-/
theorem dyadicSquare_subset_closedBall_center
    (n : ℤ) (k : ℤ × ℤ) {z : ℂ} (hz : z ∈ dyadicSquare n k) :
    dyadicSquare n k ⊆ Metric.closedBall z (4 * dyadicSide n) := by
  intro y hy
  have hyc := dyadicSquare_subset_closedBall_dyadicCorner n k hy
  have hzc := dyadicSquare_subset_closedBall_dyadicCorner n k hz
  rw [Metric.mem_closedBall] at hyc hzc ⊢
  calc
    dist y z ≤ dist y (dyadicCorner n k) + dist (dyadicCorner n k) z :=
      dist_triangle _ _ _
    _ = dist y (dyadicCorner n k) + dist z (dyadicCorner n k) := by
      rw [dist_comm (dyadicCorner n k) z]
    _ ≤ 2 * dyadicSide n + 2 * dyadicSide n := add_le_add hyc hzc
    _ = 4 * dyadicSide n := by ring

/--
%%handwave
name:
  Area of a planar dyadic square
statement:
  Every planar dyadic square of scale $n$ has Lebesgue area
  $(2^n)^2=2^{2n}$.
proof:
  Pass through the volume-preserving real-imaginary coordinate equivalence.
  The product of the lengths of the two half-open coordinate intervals is
  $(2^n)^2$.
-/
theorem volume_dyadicSquare (n : ℤ) (k : ℤ × ℤ) :
    volume (dyadicSquare n k) =
      ENNReal.ofReal (dyadicSide n ^ (2 : ℕ)) := by
  let a : ℝ := (k.1 : ℝ) * dyadicSide n
  let b : ℝ := (k.1 + 1 : ℤ) * dyadicSide n
  let c : ℝ := (k.2 : ℝ) * dyadicSide n
  let d : ℝ := (k.2 + 1 : ℤ) * dyadicSide n
  have hset : dyadicSquare n k =
      Complex.measurableEquivRealProd ⁻¹' (Set.Ico a b ×ˢ Set.Ico c d) := by
    ext z
    simp [dyadicSquare, a, b, c, d,
      Complex.measurableEquivRealProd_apply, and_assoc]
  rw [hset]
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]
  rw [Measure.volume_eq_prod]
  rw [Measure.prod_prod]
  simp only [Real.volume_Ico]
  have hs : 0 ≤ dyadicSide n := (dyadicSide_pos n).le
  have hab : b - a = dyadicSide n := by
    simp [a, b]
    ring
  have hcd : d - c = dyadicSide n := by
    simp [c, d]
    ring
  rw [hab, hcd, ← ENNReal.ofReal_mul hs]
  simp [pow_two]

/-! ## Parent and ancestor nesting -/

/--
%%handwave
name:
  Parent index of a dyadic square
statement:
  The parent of a dyadic index $(k_1,k_2)\in\mathbb Z^2$ is
  $(\lfloor k_1/2\rfloor,\lfloor k_2/2\rfloor)$, where integer division is
  Euclidean floor division.
-/
def dyadicParent (k : ℤ × ℤ) : ℤ × ℤ :=
  (k.1 / 2, k.2 / 2)

/--
%%handwave
name:
  Iterated dyadic ancestor
statement:
  The ancestor of depth $d\in\mathbb N$ is obtained by applying the dyadic
  parent operation $d$ times.
-/
def dyadicAncestor : ℕ → ℤ × ℤ → ℤ × ℤ
  | 0, k => k
  | d + 1, k => dyadicParent (dyadicAncestor d k)

/--
%%handwave
name:
  Dyadic side length at the parent scale
statement:
  For every $n\in\mathbb Z$, the side length at scale $n+1$ is twice the
  side length at scale $n$:
  $$2^{n+1}=2\cdot2^n.$$
proof:
  This is the addition law for integer powers.
-/
theorem dyadicSide_add_one (n : ℤ) :
    dyadicSide (n + 1) = 2 * dyadicSide n := by
  simp [dyadicSide, zpow_add₀, mul_comm]

/--
%%handwave
name:
  A dyadic square is contained in its parent
statement:
  The square of scale $n$ and index $k$ is contained in the square of scale
  $n+1$ whose index is
  $(\lfloor k_1/2\rfloor,\lfloor k_2/2\rfloor)$.
proof:
  Euclidean division gives
  $2\lfloor k_j/2\rfloor\leq k_j$ and
  $k_j+1\leq2(\lfloor k_j/2\rfloor+1)$ in each coordinate. Multiply these
  inequalities by $2^n>0$ and use $2^{n+1}=2\cdot2^n$.
-/
theorem dyadicSquare_subset_parent (n : ℤ) (k : ℤ × ℤ) :
    dyadicSquare n k ⊆ dyadicSquare (n + 1) (dyadicParent k) := by
  intro z hz
  have hs : 0 < dyadicSide n := dyadicSide_pos n
  have hkre0 : 2 * (k.1 / 2) ≤ k.1 := by omega
  have hkre1 : k.1 + 1 ≤ 2 * (k.1 / 2 + 1) := by omega
  have hkim0 : 2 * (k.2 / 2) ≤ k.2 := by omega
  have hkim1 : k.2 + 1 ≤ 2 * (k.2 / 2 + 1) := by omega
  rw [dyadicSquare, dyadicParent, dyadicSide_add_one]
  constructor
  · calc
      ((k.1 / 2 : ℤ) : ℝ) * (2 * dyadicSide n) =
          ((2 * (k.1 / 2) : ℤ) : ℝ) * dyadicSide n := by
            push_cast
            ring
      _ ≤ (k.1 : ℝ) * dyadicSide n := by gcongr
      _ ≤ z.re := hz.1
  constructor
  · calc
      z.re < ((k.1 + 1 : ℤ) : ℝ) * dyadicSide n := hz.2.1
      _ ≤ (((k.1 / 2 : ℤ) + 1 : ℤ) : ℝ) *
          (2 * dyadicSide n) := by
        rw [show (((k.1 / 2 : ℤ) + 1 : ℤ) : ℝ) *
            (2 * dyadicSide n) =
            ((2 * (k.1 / 2 + 1) : ℤ) : ℝ) * dyadicSide n by
          push_cast
          ring]
        gcongr
  constructor
  · calc
      ((k.2 / 2 : ℤ) : ℝ) * (2 * dyadicSide n) =
          ((2 * (k.2 / 2) : ℤ) : ℝ) * dyadicSide n := by
            push_cast
            ring
      _ ≤ (k.2 : ℝ) * dyadicSide n := by gcongr
      _ ≤ z.im := hz.2.2.1
  · calc
      z.im < ((k.2 + 1 : ℤ) : ℝ) * dyadicSide n := hz.2.2.2
      _ ≤ (((k.2 / 2 : ℤ) + 1 : ℤ) : ℝ) *
          (2 * dyadicSide n) := by
        rw [show (((k.2 / 2 : ℤ) + 1 : ℤ) : ℝ) *
            (2 * dyadicSide n) =
            ((2 * (k.2 / 2 + 1) : ℤ) : ℝ) * dyadicSide n by
          push_cast
          ring]
        gcongr

/--
%%handwave
name:
  A dyadic parent has four times the area of its child
statement:
  For every planar dyadic square $Q_{n,k}$, its parent has area
  $$
    |Q_{n+1,\operatorname{par}(k)}|=4|Q_{n,k}|.
  $$
proof:
  The parent side length is twice the child side length, and the area is the
  square of the side length.
-/
theorem volume_dyadicSquare_parent_toReal (n : ℤ) (k : ℤ × ℤ) :
    (volume (dyadicSquare (n + 1) (dyadicParent k))).toReal =
      4 * (volume (dyadicSquare n k)).toReal := by
  rw [volume_dyadicSquare, volume_dyadicSquare]
  rw [ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (sq_nonneg _), dyadicSide_add_one]
  ring

/--
%%handwave
name:
  A dyadic square differs from its parent
statement:
  Every planar dyadic square is a proper subset of its parent; in particular,
  $Q_{n,k}\ne Q_{n+1,\operatorname{par}(k)}$.
proof:
  Equal sets would have equal areas, contradicting the fact that the parent
  has four times the positive area of the child.
-/
theorem dyadicSquare_ne_parent (n : ℤ) (k : ℤ × ℤ) :
    dyadicSquare n k ≠ dyadicSquare (n + 1) (dyadicParent k) := by
  intro h
  have hv := congrArg (fun Q : Set ℂ ↦ (volume Q).toReal) h
  change (volume (dyadicSquare n k)).toReal =
    (volume (dyadicSquare (n + 1) (dyadicParent k))).toReal at hv
  rw [volume_dyadicSquare, volume_dyadicSquare,
    ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (sq_nonneg _), dyadicSide_add_one] at hv
  nlinarith [dyadicSide_pos n]

/--
%%handwave
name:
  A dyadic square is contained in every iterated ancestor
statement:
  For $d\in\mathbb N$, the square of scale $n$ and index $k$ is contained in
  the square of scale $n+d$ whose index is the depth-$d$ ancestor of $k$.
proof:
  Induct on $d$, applying [a dyadic square is contained in its parent](lean:JJMath.HarmonicAnalysis.dyadicSquare_subset_parent) at each step.
-/
theorem dyadicSquare_subset_ancestor (n : ℤ) (k : ℤ × ℤ) (d : ℕ) :
    dyadicSquare n k ⊆
      dyadicSquare (n + (d : ℤ)) (dyadicAncestor d k) := by
  induction d with
  | zero => simp [dyadicAncestor]
  | succ d ih =>
      exact ih.trans (by
        simpa [dyadicAncestor, Nat.cast_add, add_assoc] using
          dyadicSquare_subset_parent (n + (d : ℤ)) (dyadicAncestor d k))

/--
%%handwave
name:
  Intersecting dyadic squares are nested toward the coarser scale
statement:
  Let $n\leq m$. If the dyadic square $Q$ of scale $n$ intersects the dyadic
  square $R$ of scale $m$, then $Q\subseteq R$.
proof:
  The scale difference $m-n$ is a natural number. The finer square is
  contained in its corresponding ancestor at scale $m$. A point in the
  intersection belongs both to this ancestor and to $R$; uniqueness of the
  dyadic index at scale $m$ identifies the two coarser squares.
-/
theorem dyadicSquare_subset_of_le_of_inter_nonempty
    {n m : ℤ} {k l : ℤ × ℤ} (hnm : n ≤ m)
    (hinter : (dyadicSquare n k ∩ dyadicSquare m l).Nonempty) :
    dyadicSquare n k ⊆ dyadicSquare m l := by
  let d : ℕ := (m - n).toNat
  have hdiff : 0 ≤ m - n := sub_nonneg.mpr hnm
  have hd : n + (d : ℤ) = m := by
    dsimp [d]
    rw [Int.toNat_of_nonneg hdiff]
    omega
  have hsub : dyadicSquare n k ⊆
      dyadicSquare m (dyadicAncestor d k) := by
    simpa only [hd] using dyadicSquare_subset_ancestor n k d
  rcases hinter with ⟨z, hzn, hzm⟩
  have hzanc := hsub hzn
  have hidxAnc := (mem_dyadicSquare_iff_dyadicIndex_eq
    m (dyadicAncestor d k) z).mp hzanc
  have hidxL := (mem_dyadicSquare_iff_dyadicIndex_eq m l z).mp hzm
  have heq : dyadicAncestor d k = l := hidxAnc.symm.trans hidxL
  simpa only [heq] using hsub

/-! ## Maximal subfamilies -/

/--
%%handwave
name:
  Maximal dyadic square for a predicate
statement:
  Let $P(n,k)$ be a predicate on planar dyadic squares. A set $Q$ is a
  maximal dyadic square satisfying $P$ if $Q=Q_{n,k}$ for some pair satisfying
  $P$, and every dyadic square $R$ satisfying $P$ with $Q\subseteq R$ also
  satisfies $R\subseteq Q$.
-/
def IsMaximalDyadicSquare
    (P : ℤ → ℤ × ℤ → Prop) (Q : Set ℂ) : Prop :=
  ∃ n k, P n k ∧ Q = dyadicSquare n k ∧
    ∀ m l, P m l → Q ⊆ dyadicSquare m l → dyadicSquare m l ⊆ Q

/--
%%handwave
name:
  Maximal dyadic squares are pairwise disjoint
statement:
  For any predicate $P$ on planar dyadic squares, distinct maximal squares
  satisfying $P$ are disjoint.
proof:
  If two maximal squares intersect, [the finer square is contained in the coarser square](lean:JJMath.HarmonicAnalysis.dyadicSquare_subset_of_le_of_inter_nonempty). Maximality gives the reverse inclusion, so the two sets are equal.
-/
theorem pairwiseDisjoint_maximalDyadicSquare
    (P : ℤ → ℤ × ℤ → Prop) :
    {Q : Set ℂ | IsMaximalDyadicSquare P Q}.PairwiseDisjoint id := by
  rintro Q ⟨n, k, hP, rfl, hmax⟩ R ⟨m, l, hP', rfl, hmax'⟩ hne
  change Disjoint (dyadicSquare n k) (dyadicSquare m l)
  by_contra hdisj
  have hinter : (dyadicSquare n k ∩ dyadicSquare m l).Nonempty :=
    not_disjoint_iff_nonempty_inter.mp hdisj
  rcases le_total n m with hnm | hmn
  · have hsub := dyadicSquare_subset_of_le_of_inter_nonempty hnm hinter
    have hback := hmax m l hP' hsub
    exact hne (Set.Subset.antisymm hsub hback)
  · have hinter' : (dyadicSquare m l ∩ dyadicSquare n k).Nonempty := by
      simpa [inter_comm] using hinter
    have hsub := dyadicSquare_subset_of_le_of_inter_nonempty hmn hinter'
    have hback := hmax' n k hP hsub
    exact hne (Set.Subset.antisymm hback hsub)

/--
%%handwave
name:
  Countability of the maximal dyadic family
statement:
  For any predicate $P$ on planar dyadic squares, the family of maximal
  squares satisfying $P$ is countable.
proof:
  Every member belongs to the image of the countable parameter set
  $\mathbb Z\times\mathbb Z^2$ under the map $(n,k)\mapsto Q_{n,k}$.
-/
theorem countable_maximalDyadicSquare
    (P : ℤ → ℤ × ℤ → Prop) :
    {Q : Set ℂ | IsMaximalDyadicSquare P Q}.Countable := by
  apply (Set.countable_range
    (fun p : ℤ × (ℤ × ℤ) ↦ dyadicSquare p.1 p.2)).mono
  intro Q hQ
  rcases hQ with ⟨n, k, _hP, hQ, _hmax⟩
  exact ⟨(n, k), hQ.symm⟩

/--
%%handwave
name:
  Nonemptiness of a planar dyadic square
statement:
  Every planar dyadic square contains its lower-left corner and is therefore
  nonempty.
proof:
  The lower coordinate inequalities are equalities at the corner, while the
  upper inequalities follow from $2^n>0$.
-/
theorem dyadicSquare_nonempty (n : ℤ) (k : ℤ × ℤ) :
    (dyadicSquare n k).Nonempty := by
  refine ⟨dyadicCorner n k, ?_⟩
  have hs := dyadicSide_pos n
  constructor
  · rfl
  constructor
  · change (k.1 : ℝ) * dyadicSide n <
      ((k.1 + 1 : ℤ) : ℝ) * dyadicSide n
    norm_num
    nlinarith
  constructor
  · rfl
  · change (k.2 : ℝ) * dyadicSide n <
      ((k.2 + 1 : ℤ) : ℝ) * dyadicSide n
    norm_num
    nlinarith

/--
%%handwave
name:
  Existence of a maximal dyadic super-square
statement:
  Let $P$ be a predicate on dyadic squares which is false at every
  sufficiently coarse scale. Every square satisfying $P$ is contained in a
  maximal square satisfying $P$.
proof:
  Among the scales of all $P$-squares containing the original square, choose
  the greatest integer scale; it exists by the assumed upper bound. Any
  larger $P$-square containing the chosen one would contradict maximality of
  that scale. The [nesting theorem for intersecting dyadic squares](lean:JJMath.HarmonicAnalysis.dyadicSquare_subset_of_le_of_inter_nonempty) supplies the reverse inclusion for an arbitrary containing $P$-square.
-/
theorem exists_maximalDyadicSquare_superset
    (P : ℤ → ℤ × ℤ → Prop) {n : ℤ} {k : ℤ × ℤ}
    (hP : P n k)
    (hbounded : ∃ M : ℤ, ∀ m l, M ≤ m → ¬ P m l) :
    ∃ Q : Set ℂ, IsMaximalDyadicSquare P Q ∧ dyadicSquare n k ⊆ Q := by
  let R : ℤ → Prop := fun m ↦
    ∃ l, P m l ∧ dyadicSquare n k ⊆ dyadicSquare m l
  have hRn : R n := ⟨k, hP, Subset.rfl⟩
  have hRbdd : ∃ M : ℤ, ∀ m, R m → m ≤ M := by
    rcases hbounded with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro m hm
    by_contra hnot
    have hMm : M ≤ m := le_of_not_ge hnot
    rcases hm with ⟨l, hPml, _hsub⟩
    exact hM m l hMm hPml
  obtain ⟨p, hp, hpmax⟩ := Int.exists_greatest_of_bdd hRbdd ⟨n, hRn⟩
  rcases hp with ⟨l, hPl, hbase⟩
  refine ⟨dyadicSquare p l, ⟨p, l, hPl, rfl, ?_⟩, hbase⟩
  intro m j hPm hsub
  have hinter : (dyadicSquare p l ∩ dyadicSquare m j).Nonempty := by
    rcases dyadicSquare_nonempty p l with ⟨z, hz⟩
    exact ⟨z, hz, hsub hz⟩
  have hmp : m ≤ p := by
    rcases le_total p m with hpm | hmp
    · apply hpmax m
      exact ⟨j, hPm, hbase.trans hsub⟩
    · exact hmp
  apply dyadicSquare_subset_of_le_of_inter_nonempty hmp
  simpa [inter_comm] using hinter

end

end HarmonicAnalysis

end JJMath
