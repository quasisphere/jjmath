import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Local Sard theorem for smooth functions on the plane

This file isolates the only Sard input currently needed by the
Green-function/Evans-potential route to uniformization.  The statement is the
bounded local Euclidean theorem for a smooth real-valued function on an open
subset of the complex plane.
-/

namespace JJMath

open scoped Topology Uniformity ContDiff BigOperators

namespace Uniformization

open Asymptotics

/--
%%handwave
name:
  Plane critical value on a set
statement:
  A real number is a critical value of a real-valued function on a subset of
  the complex plane if it is the value of the function at a point of the subset
  where the real differential vanishes.
-/
def PlaneCriticalValueOn (g : ℂ → ℝ) (U : Set ℂ) (c : ℝ) : Prop :=
  ∃ z ∈ U, g z = c ∧ fderiv ℝ g z = 0

/--
%%handwave
name:
  Plane critical set
statement:
  The critical set of a real-valued function on a subset of the complex plane
  consists of the points of the subset where the real differential vanishes.
-/
def PlaneCriticalSet (g : ℂ → ℝ) (U : Set ℂ) : Set ℂ :=
  {z | z ∈ U ∧ fderiv ℝ g z = 0}

/--
%%handwave
name:
  Degenerate second derivative at a plane point
statement:
  A smooth real-valued function has degenerate second derivative at a point of
  the plane if the derivative of its first differential is not invertible
  there.
-/
def PlaneSecondDerivativeDegenerateAt (g : ℂ → ℝ) (z : ℂ) : Prop :=
  ¬ (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ g w) z).IsInvertible

/--
%%handwave
name:
  Vanishing second derivative at a plane point
statement:
  A smooth real-valued function has vanishing second derivative at a point of
  the plane if the derivative of its first differential is zero there.
-/
def PlaneSecondDerivativeZeroAt (g : ℂ → ℝ) (z : ℂ) : Prop :=
  fderiv ℝ (fun w : ℂ ↦ fderiv ℝ g w) z = 0

/--
%%handwave
name:
  Regular second-derivative critical value on a set
statement:
  A critical value is second-derivative regular on a subset of the plane if it
  is attained at a critical point where the second derivative is nondegenerate.
-/
def PlaneSecondDerivativeRegularCriticalValueOn
    (g : ℂ → ℝ) (U : Set ℂ) (c : ℝ) : Prop :=
  ∃ z ∈ U, g z = c ∧ fderiv ℝ g z = 0 ∧
    ¬ PlaneSecondDerivativeDegenerateAt g z

/--
%%handwave
name:
  Degenerate second-derivative critical value on a set
statement:
  A critical value is second-derivative degenerate on a subset of the plane if
  it is attained at a critical point where the second derivative is degenerate.
-/
def PlaneSecondDerivativeDegenerateCriticalValueOn
    (g : ℂ → ℝ) (U : Set ℂ) (c : ℝ) : Prop :=
  ∃ z ∈ U, g z = c ∧ fderiv ℝ g z = 0 ∧
    PlaneSecondDerivativeDegenerateAt g z

/--
%%handwave
name:
  Nonzero singular second-derivative critical value on a set
statement:
  A critical value is nonzero singular on a subset of the plane if it is
  attained at a critical point where the second derivative is singular but not
  zero.
-/
def PlaneSecondDerivativeNonzeroSingularCriticalValueOn
    (g : ℂ → ℝ) (U : Set ℂ) (c : ℝ) : Prop :=
  ∃ z ∈ U, g z = c ∧ fderiv ℝ g z = 0 ∧
    PlaneSecondDerivativeDegenerateAt g z ∧
      ¬ PlaneSecondDerivativeZeroAt g z

/--
%%handwave
name:
  Zero second-derivative critical value on a set
statement:
  A critical value is zero second-derivative on a subset of the plane if it is
  attained at a critical point where the second derivative vanishes.
-/
def PlaneSecondDerivativeZeroCriticalValueOn
    (g : ℂ → ℝ) (U : Set ℂ) (c : ℝ) : Prop :=
  ∃ z ∈ U, g z = c ∧ fderiv ℝ g z = 0 ∧
    PlaneSecondDerivativeZeroAt g z

/--
%%handwave
name:
  Critical values are monotone under restriction
statement:
  If one subset of the plane is contained in another, then every critical value
  attained on the smaller subset is a critical value attained on the larger
  subset.
proof:
  Keep the same critical point witnessing the critical value and use the set
  inclusion to regard it as a point of the larger subset.
-/
theorem planeCriticalValueOn_mono {g : ℂ → ℝ} {S T : Set ℂ}
    (hST : S ⊆ T) :
    {c : ℝ | PlaneCriticalValueOn g S c} ⊆
      {c : ℝ | PlaneCriticalValueOn g T c} := by
  intro c hc
  rcases hc with ⟨z, hzS, hgz, hzcrit⟩
  exact ⟨z, hST hzS, hgz, hzcrit⟩

/--
%%handwave
name:
  Second-derivative regular critical values are monotone under restriction
statement:
  If one subset of the plane is contained in another, then every critical
  value attained on the smaller subset at a critical point with nondegenerate
  second derivative is also attained on the larger subset with the same
  property.
proof:
  The same critical point, value equation, and nondegeneracy condition provide
  the required witness after applying the inclusion of subsets.
-/
theorem planeSecondDerivativeRegularCriticalValueOn_mono {g : ℂ → ℝ} {S T : Set ℂ}
    (hST : S ⊆ T) :
    {c : ℝ | PlaneSecondDerivativeRegularCriticalValueOn g S c} ⊆
      {c : ℝ | PlaneSecondDerivativeRegularCriticalValueOn g T c} := by
  intro c hc
  rcases hc with ⟨z, hzS, hgz, hzcrit, hzreg⟩
  exact ⟨z, hST hzS, hgz, hzcrit, hzreg⟩

/--
%%handwave
name:
  Second-derivative degenerate critical values are monotone under restriction
statement:
  If one subset of the plane is contained in another, then every critical
  value attained on the smaller subset at a critical point with degenerate
  second derivative is also attained on the larger subset with the same
  property.
proof:
  Retain the witnessing critical point and all of its differential properties;
  only its membership is transported along the inclusion.
-/
theorem planeSecondDerivativeDegenerateCriticalValueOn_mono {g : ℂ → ℝ} {S T : Set ℂ}
    (hST : S ⊆ T) :
    {c : ℝ | PlaneSecondDerivativeDegenerateCriticalValueOn g S c} ⊆
      {c : ℝ | PlaneSecondDerivativeDegenerateCriticalValueOn g T c} := by
  intro c hc
  rcases hc with ⟨z, hzS, hgz, hzcrit, hzdeg⟩
  exact ⟨z, hST hzS, hgz, hzcrit, hzdeg⟩

/--
%%handwave
name:
  Degenerate critical values split into nonzero singular and zero parts
statement:
  A critical value attained at a degenerate critical point is either attained
  at a critical point where the second derivative is singular but not zero, or
  at a critical point where the second derivative is zero.
proof:
  For a witnessing degenerate critical point \(z\), distinguish whether its
  second derivative is zero.  The zero case belongs to the second set, and
  otherwise degeneracy together with nonvanishing belongs to the first.
-/
theorem planeSecondDerivativeDegenerateCriticalValues_subset_nonzeroSingular_union_zero
    {g : ℂ → ℝ} {S : Set ℂ} :
    {c : ℝ | PlaneSecondDerivativeDegenerateCriticalValueOn g S c} ⊆
      {c : ℝ | PlaneSecondDerivativeNonzeroSingularCriticalValueOn g S c} ∪
        {c : ℝ | PlaneSecondDerivativeZeroCriticalValueOn g S c} := by
  intro c hc
  rcases hc with ⟨z, hzS, hgz, hzcrit, hzdeg⟩
  by_cases hzero : PlaneSecondDerivativeZeroAt g z
  · exact Or.inr ⟨z, hzS, hgz, hzcrit, hzero⟩
  · exact Or.inl ⟨z, hzS, hgz, hzcrit, hzdeg, hzero⟩

/--
%%handwave
name:
  Degenerate critical values are null from the singular-zero split
statement:
  If the critical values attained at nonzero singular second-derivative
  critical points and at zero second-derivative critical points both have
  measure zero, then all degenerate second-derivative critical values have
  measure zero.
proof:
  By [every degenerate critical value lies in the union of the nonzero singular and zero parts](lean:JJMath.Uniformization.planeSecondDerivativeDegenerateCriticalValues_subset_nonzeroSingular_union_zero).  That union is null because both parts are null, and every subset of a null set is null.
-/
theorem planeSecondDerivativeDegenerateCriticalValues_volume_zero_of_nonzeroSingular_zero_split
    {g : ℂ → ℝ} {S : Set ℂ}
    (hnonzeroSingular :
      MeasureTheory.volume
        {c : ℝ | PlaneSecondDerivativeNonzeroSingularCriticalValueOn g S c} = 0)
    (hzero :
      MeasureTheory.volume
        {c : ℝ | PlaneSecondDerivativeZeroCriticalValueOn g S c} = 0) :
    MeasureTheory.volume
        {c : ℝ | PlaneSecondDerivativeDegenerateCriticalValueOn g S c} = 0 := by
  have hsubset :=
    planeSecondDerivativeDegenerateCriticalValues_subset_nonzeroSingular_union_zero
      (g := g) (S := S)
  have hunion :
      MeasureTheory.volume
          ({c : ℝ | PlaneSecondDerivativeNonzeroSingularCriticalValueOn g S c} ∪
            {c : ℝ | PlaneSecondDerivativeZeroCriticalValueOn g S c}) = 0 := by
    rw [MeasureTheory.measure_union_null_iff]
    exact ⟨hnonzeroSingular, hzero⟩
  exact MeasureTheory.measure_mono_null hsubset hunion

/--
%%handwave
name:
  Critical values under a countable cover
statement:
  If a subset of the plane is covered by countably many subsets, then its
  critical values are contained in the countable union of the critical values
  attained on the covering subsets.
proof:
  A critical value has a witnessing critical point \(z\) in the original set.
  Choose a member of the cover containing \(z\); the same point witnesses
  membership in that piece’s critical-value set.
-/
theorem planeCriticalValues_subset_iUnion {ι : Type*} [Countable ι]
    {g : ℂ → ℝ} {S : Set ℂ}
    {A : ι → Set ℂ} (hcover : S ⊆ ⋃ i : ι, A i) :
    {c : ℝ | PlaneCriticalValueOn g S c} ⊆
      ⋃ i : ι, {c : ℝ | PlaneCriticalValueOn g (A i) c} := by
  intro c hc
  rcases hc with ⟨z, hzS, hgz, hzcrit⟩
  rcases Set.mem_iUnion.mp (hcover hzS) with ⟨i, hzA⟩
  exact Set.mem_iUnion.mpr ⟨i, z, hzA, hgz, hzcrit⟩

/--
%%handwave
name:
  Countable critical-value covers preserve nullity
statement:
  If a subset of the plane is covered by countably many pieces and the
  critical values attained on each piece have zero measure, then the critical
  values attained on the original subset have zero measure.
proof:
  By [the original critical-value set lies in the countable union of the critical-value sets of the pieces](lean:JJMath.Uniformization.planeCriticalValues_subset_iUnion).  The union is null by countable subadditivity, so its subset is null.
-/
theorem planeCriticalValues_volume_zero_of_iUnion
    {ι : Type*} [Countable ι] {g : ℂ → ℝ} {S : Set ℂ} {A : ι → Set ℂ}
    (hcover : S ⊆ ⋃ i : ι, A i)
    (hA_zero : ∀ i : ι,
      MeasureTheory.volume {c : ℝ | PlaneCriticalValueOn g (A i) c} = 0) :
    MeasureTheory.volume {c : ℝ | PlaneCriticalValueOn g S c} = 0 := by
  have hsubset := planeCriticalValues_subset_iUnion (g := g) hcover
  have hUnion_zero :
      MeasureTheory.volume
          (⋃ i : ι, {c : ℝ | PlaneCriticalValueOn g (A i) c}) = 0 :=
    MeasureTheory.measure_iUnion_null hA_zero
  exact MeasureTheory.measure_mono_null hsubset hUnion_zero

/--
%%handwave
name:
  Critical values split by second derivative
statement:
  Every critical value attained on a subset of the plane is either attained at
  a critical point with nondegenerate second derivative or at a critical point
  with degenerate second derivative.
proof:
  Given a witnessing critical point \(z\), distinguish whether its second
  derivative is degenerate.  The two alternatives place the value in the
  corresponding part of the union.
-/
theorem planeCriticalValues_subset_secondDerivative_split
    {g : ℂ → ℝ} {S : Set ℂ} :
    {c : ℝ | PlaneCriticalValueOn g S c} ⊆
      {c : ℝ | PlaneSecondDerivativeRegularCriticalValueOn g S c} ∪
        {c : ℝ | PlaneSecondDerivativeDegenerateCriticalValueOn g S c} := by
  intro c hc
  rcases hc with ⟨z, hzS, hgz, hzcrit⟩
  by_cases hdeg : PlaneSecondDerivativeDegenerateAt g z
  · exact Or.inr ⟨z, hzS, hgz, hzcrit, hdeg⟩
  · exact Or.inl ⟨z, hzS, hgz, hzcrit, hdeg⟩

/--
%%handwave
name:
  Critical values are null from the second-derivative split
statement:
  If both the second-derivative regular and second-derivative degenerate
  critical values on a set have measure zero, then all critical values on that
  set have measure zero.
proof:
  By [every critical value lies in the union of the nondegenerate and degenerate second-derivative parts](lean:JJMath.Uniformization.planeCriticalValues_subset_secondDerivative_split).  The two hypotheses make this union null, hence its critical-value subset is null.
-/
theorem planeCriticalValues_volume_zero_of_secondDerivative_split
    {g : ℂ → ℝ} {S : Set ℂ}
    (hregular :
      MeasureTheory.volume
        {c : ℝ | PlaneSecondDerivativeRegularCriticalValueOn g S c} = 0)
    (hdegenerate :
      MeasureTheory.volume
        {c : ℝ | PlaneSecondDerivativeDegenerateCriticalValueOn g S c} = 0) :
    MeasureTheory.volume {c : ℝ | PlaneCriticalValueOn g S c} = 0 := by
  have hsubset :=
    planeCriticalValues_subset_secondDerivative_split (g := g) (S := S)
  have hunion :
      MeasureTheory.volume
          ({c : ℝ | PlaneSecondDerivativeRegularCriticalValueOn g S c} ∪
            {c : ℝ | PlaneSecondDerivativeDegenerateCriticalValueOn g S c}) = 0 := by
    rw [MeasureTheory.measure_union_null_iff]
    exact ⟨hregular, hdegenerate⟩
  exact MeasureTheory.measure_mono_null hsubset hunion

/--
%%handwave
name:
  Arbitrarily short countable covers have zero length
statement:
  A subset of the real line has zero Lebesgue measure if, for every positive
  number, it is covered by countably many sets whose total Lebesgue measure is
  at most that number.
proof:
  For each \(\varepsilon>0\), monotonicity and countable subadditivity bound the
  measure of the set by the total measure of the chosen cover, hence by
  \(\varepsilon\).  A nonnegative extended real number bounded by every
  positive \(\varepsilon\) is zero.
-/
theorem real_volume_zero_of_countable_covers_with_small_total {E : Set ℝ}
    (hcover : ∀ ε : ℝ, 0 < ε →
      ∃ A : ℕ → Set ℝ,
        E ⊆ ⋃ n : ℕ, A n ∧
          (∑' n : ℕ, MeasureTheory.volume (A n)) ≤ ENNReal.ofReal ε) :
    MeasureTheory.volume E = 0 := by
  apply le_antisymm ?_ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hzero_ne_top
  have hε_real : 0 < (ε : ℝ) := by
    exact_mod_cast hε
  rcases hcover (ε : ℝ) hε_real with ⟨A, hE_cover, hA_sum⟩
  have hle :
      MeasureTheory.volume E ≤ ENNReal.ofReal (ε : ℝ) := by
    calc
      MeasureTheory.volume E ≤ MeasureTheory.volume (⋃ n : ℕ, A n) :=
        MeasureTheory.measure_mono hE_cover
      _ ≤ ∑' n : ℕ, MeasureTheory.volume (A n) :=
        MeasureTheory.measure_iUnion_le _
      _ ≤ ENNReal.ofReal (ε : ℝ) := hA_sum
  simpa [ENNReal.ofReal_coe_nnreal] using hle

/--
%%handwave
name:
  Finite real covers as countable covers
statement:
  A finite cover of a real set whose total length is bounded by a given number
  can be regarded as a countable cover with the same total length by adding
  empty sets after the finite list.
-/
theorem real_countable_cover_of_fin_cover {E : Set ℝ} {N : ℕ}
    {A : Fin N → Set ℝ} {ε : ℝ}
    (hcover : E ⊆ ⋃ i : Fin N, A i)
    (hsum :
      (∑ i : Fin N, MeasureTheory.volume (A i)) ≤ ENNReal.ofReal ε) :
    ∃ B : ℕ → Set ℝ,
      E ⊆ ⋃ n : ℕ, B n ∧
        (∑' n : ℕ, MeasureTheory.volume (B n)) ≤ ENNReal.ofReal ε := by
  let B : ℕ → Set ℝ := fun n ↦ if hn : n < N then A ⟨n, hn⟩ else ∅
  refine ⟨B, ?_, ?_⟩
  · intro x hx
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hxi⟩
    exact Set.mem_iUnion.mpr ⟨(i : ℕ), by simp [B, i.isLt, hxi]⟩
  · have hzero : ∀ n ∉ Finset.range N, MeasureTheory.volume (B n) = 0 := by
      intro n hn
      have hnlt : ¬ n < N := by simpa [Finset.mem_range] using hn
      simp [B, hnlt]
    rw [tsum_eq_sum hzero]
    calc
      (∑ n ∈ Finset.range N, MeasureTheory.volume (B n)) =
          ∑ i : Fin N, MeasureTheory.volume (A i) := by
        rw [Finset.sum_range]
        simp [B]
      _ ≤ ENNReal.ofReal ε := hsum

/--
%%handwave
name:
  Finite-index real covers as countable covers
statement:
  A cover indexed by any finite type can be regarded as a countable cover with
  the same total length.
-/
theorem real_countable_cover_of_fintype_cover {ι : Type*} [Fintype ι]
    {E : Set ℝ} {A : ι → Set ℝ} {ε : ℝ}
    (hcover : E ⊆ ⋃ i : ι, A i)
    (hsum : (∑ i : ι, MeasureTheory.volume (A i)) ≤ ENNReal.ofReal ε) :
    ∃ B : ℕ → Set ℝ,
      E ⊆ ⋃ n : ℕ, B n ∧
        (∑' n : ℕ, MeasureTheory.volume (B n)) ≤ ENNReal.ofReal ε := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let AFin : Fin (Fintype.card ι) → Set ℝ := fun j ↦ A (e.symm j)
  refine real_countable_cover_of_fin_cover (E := E) (A := AFin) ?_ ?_
  · intro x hx
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hxi⟩
    exact Set.mem_iUnion.mpr ⟨e i, by simp [AFin, hxi]⟩
  · have hsum_eq :
        (∑ j : Fin (Fintype.card ι), MeasureTheory.volume (AFin j)) =
          ∑ i : ι, MeasureTheory.volume (A i) := by
      rw [← Equiv.sum_comp e (fun j : Fin (Fintype.card ι) ↦
        MeasureTheory.volume (AFin j))]
      simp [AFin]
    simpa [hsum_eq] using hsum

/--
%%handwave
name:
  Uniformly bounded finite real covers as countable covers
statement:
  If a finite cover has each member bounded by a prescribed extended
  nonnegative length and the sum of these prescribed lengths is small, then it
  gives a countable cover with small total length.
-/
theorem real_countable_cover_of_fintype_cover_of_uniform_volume_bound
    {ι : Type*} [Fintype ι] {E : Set ℝ} {A : ι → Set ℝ} {η : ENNReal} {ε : ℝ}
    (hcover : E ⊆ ⋃ i : ι, A i)
    (hvol : ∀ i : ι, MeasureTheory.volume (A i) ≤ η)
    (hsum : (∑ _ : ι, η) ≤ ENNReal.ofReal ε) :
    ∃ B : ℕ → Set ℝ,
      E ⊆ ⋃ n : ℕ, B n ∧
        (∑' n : ℕ, MeasureTheory.volume (B n)) ≤ ENNReal.ofReal ε := by
  exact real_countable_cover_of_fintype_cover hcover
    ((Finset.sum_le_sum fun i _hi ↦ hvol i).trans hsum)

/--
%%handwave
name:
  Length of a centered interval
statement:
  The Lebesgue measure of the interval centered at a real number with radius
  \(r\) is the nonnegative real number \(2r\).
-/
theorem real_volume_Icc_center_radius (a r : ℝ) :
    MeasureTheory.volume (Set.Icc (a - r) (a + r)) = ENNReal.ofReal (2 * r) := by
  rw [Real.volume_Icc]
  ring_nf

/--
%%handwave
name:
  Uniform grid interval
statement:
  The \(i\)-th interval in the uniform subdivision of \([-R,R]\) with mesh
  \(2R/M\).
-/
def sardRealGridInterval (R : ℝ) (M : ℕ) (i : Fin (M + 1)) : Set ℝ :=
  Set.Icc (-R + (i : ℝ) * (2 * R / (M : ℝ)))
    (-R + ((i : ℝ) + 1) * (2 * R / (M : ℝ)))

/--
%%handwave
name:
  The centered interval is covered by the uniform grid
statement:
  If \(R>0\) and \(M>0\), then the interval \([-R,R]\) is covered by the
  \(M+1\) uniform grid intervals of mesh \(2R/M\).
proof:
  For a point \(x\), take the floor of \((x+R)/(2R/M)\).  The right endpoint
  is covered by allowing the final, slightly overhanging interval.
-/
theorem real_Icc_subset_iUnion_sardRealGridInterval
    (R : ℝ) {M : ℕ} (hR : 0 < R) (hM : 0 < M) :
    Set.Icc (-R) R ⊆ ⋃ i : Fin (M + 1), sardRealGridInterval R M i := by
  intro x hx
  let δ : ℝ := 2 * R / (M : ℝ)
  have hM_real_pos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  let q : ℝ := (x + R) / δ
  have hx_add_nonneg : 0 ≤ x + R := by linarith [hx.1]
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hx_add_nonneg hδ_pos.le
  have hx_add_le : x + R ≤ 2 * R := by linarith [hx.2]
  have hMδ : (M : ℝ) * δ = 2 * R := by
    dsimp [δ]
    field_simp [hM_real_pos.ne']
  have hq_le_M : q ≤ (M : ℝ) := by
    dsimp [q]
    rw [div_le_iff₀ hδ_pos]
    simpa [hMδ] using hx_add_le
  let n : ℕ := Nat.floor q
  have hn_le_M : n ≤ M := by
    have hn_real_le : (n : ℝ) ≤ (M : ℝ) := by
      exact (Nat.floor_le hq_nonneg).trans hq_le_M
    exact_mod_cast hn_real_le
  let i : Fin (M + 1) := ⟨n, Nat.lt_succ_of_le hn_le_M⟩
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  change x ∈ Set.Icc (-R + (i : ℝ) * δ) (-R + ((i : ℝ) + 1) * δ)
  have hleft_q : (n : ℝ) ≤ q := Nat.floor_le hq_nonneg
  have hright_q : q < (n : ℝ) + 1 := Nat.lt_floor_add_one q
  have hleft : -R + (i : ℝ) * δ ≤ x := by
    dsimp [i, n, q] at hleft_q ⊢
    have := mul_le_mul_of_nonneg_right hleft_q hδ_pos.le
    field_simp [hδ_pos.ne'] at this
    linarith
  have hright : x ≤ -R + ((i : ℝ) + 1) * δ := by
    dsimp [i, n, q] at hright_q ⊢
    have := mul_lt_mul_of_pos_right hright_q hδ_pos
    field_simp [hδ_pos.ne'] at this
    linarith
  exact ⟨hleft, hright⟩

/--
%%handwave
name:
  Uniform complex grid cell
statement:
  A complex grid cell consists of points whose real and imaginary coordinates,
  measured relative to a center, lie in prescribed uniform grid intervals.
-/
def sardComplexGridCell (z : ℂ) (R : ℝ) (M : ℕ)
    (ij : Fin (M + 1) × Fin (M + 1)) : Set ℂ :=
  {w : ℂ |
    (w - z).re ∈ sardRealGridInterval R M ij.1 ∧
      (w - z).im ∈ sardRealGridInterval R M ij.2}

/--
%%handwave
name:
  The closed disk is covered by the uniform complex grid
statement:
  If \(R>0\) and \(M>0\), then the closed disk of radius \(R\) is covered by
  the square grid obtained from the uniform subdivisions of the real and
  imaginary coordinate intervals \([-R,R]\).
-/
theorem complex_closedBall_subset_iUnion_sardComplexGridCell
    (z : ℂ) (R : ℝ) {M : ℕ} (hR : 0 < R) (hM : 0 < M) :
    Metric.closedBall z R ⊆
      ⋃ ij : Fin (M + 1) × Fin (M + 1), sardComplexGridCell z R M ij := by
  intro w hw
  have hnorm : ‖w - z‖ ≤ R := by
    simpa [dist_eq_norm] using hw
  have hre : (w - z).re ∈ Set.Icc (-R) R :=
    abs_le.mp ((Complex.abs_re_le_norm (w - z)).trans hnorm)
  have him : (w - z).im ∈ Set.Icc (-R) R :=
    abs_le.mp ((Complex.abs_im_le_norm (w - z)).trans hnorm)
  rcases Set.mem_iUnion.mp
      (real_Icc_subset_iUnion_sardRealGridInterval R hR hM hre) with
    ⟨i, hi⟩
  rcases Set.mem_iUnion.mp
      (real_Icc_subset_iUnion_sardRealGridInterval R hR hM him) with
    ⟨j, hj⟩
  exact Set.mem_iUnion.mpr ⟨(i, j), hi, hj⟩

/--
%%handwave
name:
  Two points in one real grid interval are close
statement:
  Two points in the same interval of a uniform grid differ by at most the mesh
  size.
-/
theorem real_abs_sub_le_of_mem_sardRealGridInterval
    {R : ℝ} {M : ℕ} {i : Fin (M + 1)} {x y : ℝ}
    (hx : x ∈ sardRealGridInterval R M i)
    (hy : y ∈ sardRealGridInterval R M i) :
    |x - y| ≤ 2 * R / (M : ℝ) := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/--
%%handwave
name:
  Diameter bound for a complex grid cell
statement:
  Two points in the same complex grid cell are at distance at most
  \(\sqrt 2\) times the mesh size.
-/
theorem complex_norm_sub_le_of_mem_sardComplexGridCell
    {z : ℂ} {R : ℝ} {M : ℕ} {ij : Fin (M + 1) × Fin (M + 1)} {w p : ℂ}
    (hR : 0 < R) (hM : 0 < M)
    (hw : w ∈ sardComplexGridCell z R M ij)
    (hp : p ∈ sardComplexGridCell z R M ij) :
    ‖w - p‖ ≤ Real.sqrt 2 * (2 * R / (M : ℝ)) := by
  let δ : ℝ := 2 * R / (M : ℝ)
  have hM_real_pos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hre : |(w - p).re| ≤ δ := by
    have h :
        |(w - z).re - (p - z).re| ≤ δ := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [hw.1.1, hw.1.2, hp.1.1, hp.1.2]
    simpa [δ, Complex.sub_re] using h
  have him : |(w - p).im| ≤ δ := by
    have h :
        |(w - z).im - (p - z).im| ≤ δ := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [hw.2.1, hw.2.2, hp.2.1, hp.2.2]
    simpa [δ, Complex.sub_im] using h
  have hmax : max |(w - p).re| |(w - p).im| ≤ δ := max_le hre him
  calc
    ‖w - p‖ ≤ Real.sqrt 2 * max |(w - p).re| |(w - p).im| :=
      Complex.norm_le_sqrt_two_mul_max (w - p)
    _ ≤ Real.sqrt 2 * δ :=
      mul_le_mul_of_nonneg_left hmax (Real.sqrt_nonneg 2)
    _ = Real.sqrt 2 * (2 * R / (M : ℝ)) := rfl

/--
%%handwave
name:
  Cellwise oscillation gives a finite critical-value cover
statement:
  Suppose a neighborhood is contained in a closed disk covered by a finite
  square grid.  If, in each grid cell meeting the zero-Hessian critical set,
  all corresponding critical values lie within a fixed radius of one selected
  critical value, then the zero-Hessian critical values are covered by one
  real interval for each grid cell.  Each interval has length at most twice
  that radius.
-/
theorem zeroSecondDerivativeCriticalValues_subset_gridIntervals_of_cell_oscillation
    {g : ℂ → ℝ} {V : Set ℂ} {z : ℂ} {R : ℝ} {M : ℕ} {ρ : ℝ}
    (hR : 0 < R) (hM : 0 < M)
    (hV_closedBall : V ⊆ Metric.closedBall z R)
    (hosc :
      ∀ {ij : Fin (M + 1) × Fin (M + 1)} {p w : ℂ},
        p ∈ V → fderiv ℝ g p = 0 → PlaneSecondDerivativeZeroAt g p →
        p ∈ sardComplexGridCell z R M ij →
        w ∈ V → fderiv ℝ g w = 0 → PlaneSecondDerivativeZeroAt g w →
        w ∈ sardComplexGridCell z R M ij →
        |g w - g p| ≤ ρ) :
    ∃ A : (Fin (M + 1) × Fin (M + 1)) → Set ℝ,
      {c : ℝ | PlaneSecondDerivativeZeroCriticalValueOn g V c} ⊆
        ⋃ ij : Fin (M + 1) × Fin (M + 1), A ij ∧
      ∀ ij : Fin (M + 1) × Fin (M + 1),
        MeasureTheory.volume (A ij) ≤ ENNReal.ofReal (2 * ρ) := by
  classical
  let Z : Set ℂ :=
    {p : ℂ | p ∈ V ∧ fderiv ℝ g p = 0 ∧ PlaneSecondDerivativeZeroAt g p}
  let cell : Fin (M + 1) × Fin (M + 1) → Set ℂ :=
    sardComplexGridCell z R M
  let center : Fin (M + 1) × Fin (M + 1) → ℂ := fun ij ↦
    if h : ∃ p : ℂ, p ∈ Z ∧ p ∈ cell ij then Classical.choose h else z
  let A : (Fin (M + 1) × Fin (M + 1)) → Set ℝ := fun ij ↦
    if h : ∃ p : ℂ, p ∈ Z ∧ p ∈ cell ij then
      Set.Icc (g (center ij) - ρ) (g (center ij) + ρ)
    else ∅
  refine ⟨A, ?_, ?_⟩
  · intro c hc
    rcases hc with ⟨w, hwV, hgw, hwcrit, hwzero⟩
    have hw_closed : w ∈ Metric.closedBall z R := hV_closedBall hwV
    rcases Set.mem_iUnion.mp
        (complex_closedBall_subset_iUnion_sardComplexGridCell z R hR hM hw_closed) with
      ⟨ij, hwij⟩
    have hwZ : w ∈ Z := ⟨hwV, hwcrit, hwzero⟩
    have hcell_nonempty : ∃ p : ℂ, p ∈ Z ∧ p ∈ cell ij := ⟨w, hwZ, hwij⟩
    refine Set.mem_iUnion.mpr ⟨ij, ?_⟩
    have hcenter_spec : center ij ∈ Z ∧ center ij ∈ cell ij := by
      simpa [center, hcell_nonempty] using Classical.choose_spec hcell_nonempty
    have hcenterV : center ij ∈ V := hcenter_spec.1.1
    have hcenterCrit : fderiv ℝ g (center ij) = 0 := hcenter_spec.1.2.1
    have hcenterZero : PlaneSecondDerivativeZeroAt g (center ij) := hcenter_spec.1.2.2
    have hbound :
        |g w - g (center ij)| ≤ ρ :=
      hosc hcenterV hcenterCrit hcenterZero hcenter_spec.2
        hwV hwcrit hwzero hwij
    have hinterval :
        g w ∈ Set.Icc (g (center ij) - ρ) (g (center ij) + ρ) := by
      rw [abs_sub_le_iff] at hbound
      constructor <;> linarith
    simpa [A, hcell_nonempty, hgw] using hinterval
  · intro ij
    by_cases hcell_nonempty : ∃ p : ℂ, p ∈ Z ∧ p ∈ cell ij
    · dsimp [A]
      rw [if_pos hcell_nonempty]
      exact le_of_eq (real_volume_Icc_center_radius (g (center ij)) ρ)
    · simp [A, hcell_nonempty]

/--
%%handwave
name:
  Segment Taylor bound from a Hessian bound
statement:
  Along a line segment, if the first differential of a real-valued function
  vanishes at one endpoint and the derivative of that first differential is
  bounded by \(K\), then the change in the function along the segment is at
  most \(K\) times the square of the segment length.
proof:
  Apply the mean-value inequality first to the first differential and then to
  the original function.
-/
theorem planeFunction_segment_oscillation_le_of_fderiv_bound
    {g : ℂ → ℝ} {F : ℂ → (ℂ →L[ℝ] ℝ)}
    {H : ℂ → (ℂ →L[ℝ] (ℂ →L[ℝ] ℝ))} {p w : ℂ} {K : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hpcrit : F p = 0)
    (hg_deriv :
      ∀ x ∈ segment ℝ p w, HasFDerivWithinAt g (F x) (segment ℝ p w) x)
    (hF_deriv :
      ∀ x ∈ segment ℝ p w, HasFDerivWithinAt F (H x) (segment ℝ p w) x)
    (hH_bound : ∀ x ∈ segment ℝ p w, ‖H x‖ ≤ K) :
    |g w - g p| ≤ K * ‖w - p‖ ^ 2 := by
  have hseg : Convex ℝ (segment ℝ p w) := convex_segment p w
  have hpseg : p ∈ segment ℝ p w := left_mem_segment ℝ p w
  have hwseg : w ∈ segment ℝ p w := right_mem_segment ℝ p w
  have hF_bound_on_segment :
      ∀ x ∈ segment ℝ p w, ‖F x‖ ≤ K * ‖w - p‖ := by
    intro x hx
    have hFx :
        ‖F x - F p‖ ≤ K * ‖x - p‖ :=
      hseg.norm_image_sub_le_of_norm_hasFDerivWithin_le
        hF_deriv hH_bound hpseg hx
    have hdist : ‖x - p‖ ≤ ‖w - p‖ :=
      norm_sub_le_of_mem_segment hx
    calc
      ‖F x‖ = ‖F x - F p‖ := by simp [hpcrit]
      _ ≤ K * ‖x - p‖ := hFx
      _ ≤ K * ‖w - p‖ := mul_le_mul_of_nonneg_left hdist hK_nonneg
  have hg_mvt :
      ‖g w - g p‖ ≤ (K * ‖w - p‖) * ‖w - p‖ :=
    hseg.norm_image_sub_le_of_norm_hasFDerivWithin_le
      hg_deriv hF_bound_on_segment hpseg hwseg
  calc
    |g w - g p| = ‖g w - g p‖ := by simp [Real.norm_eq_abs]
    _ ≤ (K * ‖w - p‖) * ‖w - p‖ := hg_mvt
    _ = K * ‖w - p‖ ^ 2 := by ring

/--
%%handwave
name:
  Small Hessian operators form a neighborhood of zero
statement:
  In the operator space of second differentials on the plane, the set of
  operators with norm less than any fixed positive number is a neighborhood of
  the zero operator.
proof:
  Use the defining neighborhood basis for continuous linear maps: controlling
  the image of the unit ball in a sufficiently small neighborhood of zero
  controls the operator norm.
-/
theorem hessianOperator_norm_lt_mem_nhds_zero_sard {η : ℝ} (hη : 0 < η) :
    {L : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) | ‖L‖ < η} ∈
      𝓝 (0 : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) := by
  let S : Set ℂ := Metric.closedBall (0 : ℂ) 1
  let V : Set (ℂ →L[ℝ] ℝ) := Metric.ball 0 (η / 2)
  have hS : Bornology.IsVonNBounded ℝ S := by
    simpa [S] using NormedSpace.isVonNBounded_closedBall ℝ ℂ 1
  have hV : V ∈ 𝓝 (0 : ℂ →L[ℝ] ℝ) :=
    Metric.ball_mem_nhds 0 (half_pos hη)
  have hbasic :
      {L : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) | ∀ x ∈ S, L x ∈ V} ∈
        𝓝 (0 : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) := by
    have hbasis := ContinuousLinearMap.hasBasis_nhds_zero_of_basis
      (𝕜₁ := ℝ) (𝕜₂ := ℝ) (E := ℂ) (F := ℂ →L[ℝ] ℝ)
      (σ := RingHom.id ℝ) Metric.nhds_basis_ball
    rw [hbasis.mem_iff]
    refine ⟨(S, η / 2), ⟨hS, half_pos hη⟩, ?_⟩
    intro L hL x hxS
    exact hL x hxS
  refine Filter.mem_of_superset hbasic ?_
  intro L hL
  have hle : ‖L‖ ≤ η / 2 := by
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (𝕜 := ℝ) (𝕜₂ := ℝ)
      (σ₁₂ := RingHom.id ℝ) (f := L) (by linarith) ?_
    intro x hx
    have hxS : x ∈ S := by
      simp [S, hx.le]
    have hxV : L x ∈ V := hL x hxS
    have : ‖L x‖ < η / 2 := by
      simpa [V, mem_ball_zero_iff] using hxV
    exact this.le
  exact lt_of_le_of_lt hle (half_lt_self hη)

/--
%%handwave
name:
  Uniform smallness of the Hessian near zero-Hessian points
statement:
  On a compact subset of the domain of a smooth real-valued plane function,
  the second differential is uniformly small near points where it vanishes.
proof:
  The second differential is continuous on the compact set, hence uniformly
  continuous.  Near a point where it is zero, uniform continuity bounds its
  norm by the prescribed amount.
-/
theorem smoothPlaneFunction_hessian_uniformly_small_near_zeroHessian_points_sard
    {g : ℂ → ℝ} {U K : Set ℂ}
    (hU_open : IsOpen U)
    (hK_compact : IsCompact K) (hK_subset : K ⊆ U)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ p ∈ K, PlaneSecondDerivativeZeroAt g p →
          ∀ x ∈ K, ‖x - p‖ < δ →
            ‖fderiv ℝ (fun w : ℂ ↦ fderiv ℝ g w) x‖ < η := by
  intro η hη
  let H : ℂ → (ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) :=
    fun x ↦ fderiv ℝ (fun w : ℂ ↦ fderiv ℝ g w) x
  have hH_cont : ContinuousOn H K := by
    intro x hxK
    have hxU : x ∈ U := hK_subset hxK
    have hg_at : ContDiffAt ℝ ∞ g x :=
      hg_smooth.contDiffAt (hU_open.mem_nhds hxU)
    have hF_at :
        ContDiffAt ℝ ∞ (fun w : ℂ ↦ fderiv ℝ g w) x :=
      hg_at.fderiv_right (m := ∞) (by simp)
    have hH_at : ContDiffAt ℝ ∞ H x := by
      simpa [H] using hF_at.fderiv_right (m := ∞) (by simp)
    exact hH_at.continuousAt.continuousWithinAt
  have hH_uc : UniformContinuousOn H K :=
    hK_compact.uniformContinuousOn_of_continuous hH_cont
  let target : Set ((ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) × (ℂ →L[ℝ] (ℂ →L[ℝ] ℝ))) :=
    {q | ‖q.2 - q.1‖ < η}
  have htarget : target ∈ 𝓤 (ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) := by
    rw [uniformity_eq_comap_nhds_zero (ℂ →L[ℝ] (ℂ →L[ℝ] ℝ))]
    refine Filter.mem_comap.mpr ⟨{L : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) | ‖L‖ < η},
      hessianOperator_norm_lt_mem_nhds_zero_sard hη, ?_⟩
    intro q hq
    simpa [target] using hq
  have hpre := hH_uc htarget
  rw [Filter.mem_map] at hpre
  rw [Filter.mem_inf_principal] at hpre
  rcases Metric.mem_uniformity_dist.mp hpre with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro p hpK hpzero x hxK hxp
  have hdist : dist p x < δ := by
    simpa [dist_eq_norm, norm_sub_rev] using hxp
  have htarget_px : (H p, H x) ∈ target := by
    exact hδ hdist ⟨hpK, hxK⟩
  have hpH : H p = 0 := by
    simpa [H, PlaneSecondDerivativeZeroAt] using hpzero
  have hx_small : ‖H x‖ < η := by
    change ‖H x - H p‖ < η at htarget_px
    rw [hpH] at htarget_px
    calc
      ‖H x‖ = ‖H x - 0‖ :=
        (congrArg (fun L : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) ↦ ‖L‖) (sub_zero (H x))).symm
      _ < η := htarget_px
  simpa [H] using hx_small

/--
%%handwave
name:
  Total quadratic grid length is uniformly bounded
statement:
  For a square grid with mesh \(2R/M\), the number of cells times the
  quadratic diameter bound is controlled independently of \(M\), up to a
  universal constant.
proof:
  The grid has \((M+1)^2\) cells and each cell has diameter at most
  \(\sqrt2\,2R/M\).  Since \(M+1\le 2M\), the product is bounded by a fixed
  multiple of \(R^2\).
-/
theorem sard_grid_quadratic_total_length_bound
    {R η ε : ℝ} {M : ℕ}
    (hM : 0 < M) (hη_nonneg : 0 ≤ η)
    (hε_bound : 64 * η * R ^ 2 ≤ ε) :
    ((Fintype.card (Fin (M + 1) × Fin (M + 1)) : ℝ) *
        (2 * (η * (Real.sqrt 2 * (2 * R / (M : ℝ))) ^ 2))) ≤ ε := by
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hM1_nat : M + 1 ≤ 2 * M := by omega
  have hM1_le : ((M + 1 : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
    exact_mod_cast hM1_nat
  have hcard_le :
      (Fintype.card (Fin (M + 1) × Fin (M + 1)) : ℝ) ≤ 4 * (M : ℝ) ^ 2 := by
    rw [Fintype.card_prod]
    simp only [Fintype.card_fin, Nat.cast_mul]
    calc
      ((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) ≤
          (2 * (M : ℝ)) * (2 * (M : ℝ)) := by
        exact mul_le_mul hM1_le hM1_le (by positivity) (by positivity)
      _ = 4 * (M : ℝ) ^ 2 := by ring
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hfactor_eq :
      2 * (η * (Real.sqrt 2 * (2 * R / (M : ℝ))) ^ 2) =
        16 * η * R ^ 2 / (M : ℝ) ^ 2 := by
    field_simp [hMreal.ne']
    rw [hsqrt_sq]
    ring
  have hfactor_nonneg : 0 ≤ 16 * η * R ^ 2 / (M : ℝ) ^ 2 := by positivity
  have hmain :
      ((Fintype.card (Fin (M + 1) × Fin (M + 1)) : ℝ) *
          (2 * (η * (Real.sqrt 2 * (2 * R / (M : ℝ))) ^ 2))) ≤
        64 * η * R ^ 2 := by
    rw [hfactor_eq]
    calc
      (Fintype.card (Fin (M + 1) × Fin (M + 1)) : ℝ) *
          (16 * η * R ^ 2 / (M : ℝ) ^ 2) ≤
          (4 * (M : ℝ) ^ 2) * (16 * η * R ^ 2 / (M : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_right hcard_le hfactor_nonneg
      _ = 64 * η * R ^ 2 := by
        field_simp [hMreal.ne']
        ring
  exact hmain.trans hε_bound

/--
%%handwave
name:
  Real grid length bounds give extended nonnegative measure bounds
statement:
  A real bound on the total length of the finitely many grid intervals gives
  the corresponding bound for their extended nonnegative Lebesgue measures.
proof:
  Rewrite the finite sum of identical extended nonnegative numbers as the
  image under \(x\mapsto \max(x,0)\) of the corresponding real finite sum.
-/
theorem sard_grid_quadratic_total_length_bound_ennreal
    {ρ ε : ℝ} {M : ℕ} (hρ : 0 ≤ ρ)
    (hreal :
      (Fintype.card (Fin (M + 1) × Fin (M + 1)) : ℝ) * (2 * ρ) ≤ ε) :
    (∑ _ : Fin (M + 1) × Fin (M + 1), ENNReal.ofReal (2 * ρ)) ≤
      ENNReal.ofReal ε := by
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · exact ENNReal.ofReal_le_ofReal
      (by simpa [Finset.sum_const, nsmul_eq_mul] using hreal)
  · intro _i _hi
    positivity

/--
%%handwave
name:
  A small Hessian on grid cells gives a short critical-value cover
statement:
  On a closed disk contained in the domain, suppose the second differential is
  bounded by \(\eta\) throughout the grid-diameter neighborhood of each
  zero-Hessian critical point.  Then the zero-Hessian critical values in the
  concentric open disk admit a countable cover whose total length is controlled
  by \(64\eta R^2\).
proof:
  In each grid cell, connect two zero-Hessian critical points by a segment.
  Convexity of the closed disk keeps the segment in the domain, and two
  applications of the mean-value inequality bound the oscillation by
  \(\eta\) times the squared grid diameter.  The finite grid cover is then
  converted to a countable cover.
-/
theorem smoothPlaneFunction_zeroSecondDerivativeCriticalValuesOn_ball_countable_cover_of_hessian_grid_sard
    {g : ℂ → ℝ} {U : Set ℂ} {z : ℂ} {R η ε : ℝ} {M : ℕ}
    (hU_open : IsOpen U) (hR : 0 < R) (hM : 0 < M)
    (hclosedBallU : Metric.closedBall z R ⊆ U)
    (hg_smooth : ContDiffOn ℝ ∞ g U)
    (hη_nonneg : 0 ≤ η)
    (hH_small :
      ∀ p ∈ Metric.closedBall z R, PlaneSecondDerivativeZeroAt g p →
        ∀ x ∈ Metric.closedBall z R,
          ‖x - p‖ ≤ Real.sqrt 2 * (2 * R / (M : ℝ)) →
            ‖fderiv ℝ (fun y : ℂ ↦ fderiv ℝ g y) x‖ ≤ η)
    (hε_bound : 64 * η * R ^ 2 ≤ ε) :
    ∃ A : ℕ → Set ℝ,
      {c : ℝ | PlaneSecondDerivativeZeroCriticalValueOn g (Metric.ball z R) c} ⊆
          ⋃ n : ℕ, A n ∧
        (∑' n : ℕ, MeasureTheory.volume (A n)) ≤ ENNReal.ofReal ε := by
  let D : ℝ := Real.sqrt 2 * (2 * R / (M : ℝ))
  let ρ : ℝ := η * D ^ 2
  have hρ_nonneg : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hosc :
      ∀ {ij : Fin (M + 1) × Fin (M + 1)} {p w : ℂ},
        p ∈ Metric.ball z R → fderiv ℝ g p = 0 → PlaneSecondDerivativeZeroAt g p →
        p ∈ sardComplexGridCell z R M ij →
        w ∈ Metric.ball z R → fderiv ℝ g w = 0 → PlaneSecondDerivativeZeroAt g w →
        w ∈ sardComplexGridCell z R M ij →
        |g w - g p| ≤ ρ := by
    intro ij p w hpV hpcrit hpzero hpij hwV _hwcrit _hwzero hwij
    let F : ℂ → (ℂ →L[ℝ] ℝ) := fun x ↦ fderiv ℝ g x
    let H : ℂ → (ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) :=
      fun x ↦ fderiv ℝ (fun y : ℂ ↦ fderiv ℝ g y) x
    have hpK : p ∈ Metric.closedBall z R := Metric.ball_subset_closedBall hpV
    have hwK : w ∈ Metric.closedBall z R := Metric.ball_subset_closedBall hwV
    have hsegK : segment ℝ p w ⊆ Metric.closedBall z R :=
      (convex_closedBall z R).segment_subset hpK hwK
    have hsegU : segment ℝ p w ⊆ U := hsegK.trans hclosedBallU
    have hg_deriv :
        ∀ x ∈ segment ℝ p w, HasFDerivWithinAt g (F x) (segment ℝ p w) x := by
      intro x hxseg
      have hxU : x ∈ U := hsegU hxseg
      have hg_at : ContDiffAt ℝ ∞ g x :=
        hg_smooth.contDiffAt (hU_open.mem_nhds hxU)
      exact ((hg_at.differentiableAt (by simp)).hasFDerivAt).hasFDerivWithinAt
    have hF_deriv :
        ∀ x ∈ segment ℝ p w, HasFDerivWithinAt F (H x) (segment ℝ p w) x := by
      intro x hxseg
      have hxU : x ∈ U := hsegU hxseg
      have hg_at : ContDiffAt ℝ ∞ g x :=
        hg_smooth.contDiffAt (hU_open.mem_nhds hxU)
      have hF_at : ContDiffAt ℝ ∞ F x := by
        simpa [F] using hg_at.fderiv_right (m := ∞) (by simp)
      have hF_has : HasFDerivAt F (H x) x := by
        simpa [H] using (hF_at.differentiableAt (by simp)).hasFDerivAt
      exact hF_has.hasFDerivWithinAt
    have hwp_le_D : ‖w - p‖ ≤ D := by
      simpa [D] using
        complex_norm_sub_le_of_mem_sardComplexGridCell
          (z := z) (R := R) (M := M) (ij := ij) hR hM hwij hpij
    have hH_bound :
        ∀ x ∈ segment ℝ p w, ‖H x‖ ≤ η := by
      intro x hxseg
      have hxK : x ∈ Metric.closedBall z R := hsegK hxseg
      have hxp_le : ‖x - p‖ ≤ D :=
        (norm_sub_le_of_mem_segment hxseg).trans hwp_le_D
      simpa [H, D] using hH_small p hpK hpzero x hxK hxp_le
    have hsegment_bound :
        |g w - g p| ≤ η * ‖w - p‖ ^ 2 :=
      planeFunction_segment_oscillation_le_of_fderiv_bound
        (g := g) (F := F) (H := H) (p := p) (w := w) (K := η)
        hη_nonneg hpcrit hg_deriv hF_deriv hH_bound
    have hD_nonneg : 0 ≤ D := by
      dsimp [D]
      positivity
    have hsq_le : ‖w - p‖ ^ 2 ≤ D ^ 2 := by
      nlinarith [hwp_le_D, norm_nonneg (w - p), hD_nonneg]
    calc
      |g w - g p| ≤ η * ‖w - p‖ ^ 2 := hsegment_bound
      _ ≤ η * D ^ 2 := mul_le_mul_of_nonneg_left hsq_le hη_nonneg
      _ = ρ := by simp [ρ]
  rcases zeroSecondDerivativeCriticalValues_subset_gridIntervals_of_cell_oscillation
      (g := g) (V := Metric.ball z R) (z := z) (R := R) (M := M) (ρ := ρ)
      hR hM Metric.ball_subset_closedBall hosc with
    ⟨A, hcover, hvol⟩
  refine real_countable_cover_of_fintype_cover hcover ?_
  calc
    (∑ ij : Fin (M + 1) × Fin (M + 1), MeasureTheory.volume (A ij)) ≤
        ∑ _ij : Fin (M + 1) × Fin (M + 1), ENNReal.ofReal (2 * ρ) :=
      Finset.sum_le_sum fun ij _hij ↦ hvol ij
    _ ≤ ENNReal.ofReal ε := by
      exact sard_grid_quadratic_total_length_bound_ennreal hρ_nonneg
        (by
          dsimp [ρ, D]
          exact sard_grid_quadratic_total_length_bound hM hη_nonneg hε_bound)

/--
%%handwave
name:
  One-dimensional zero-derivative images have zero length
statement:
  If a real-valued function of one real variable has derivative zero at every
  point of a subset, relative to that subset, then the image of the subset has
  one-dimensional Lebesgue measure zero.
proof:
  This is the one-dimensional instance of the fixed-dimensional Sard lemma:
  the determinant of the derivative vanishes everywhere on the subset.
-/
theorem real_image_volume_zero_of_hasDerivWithinAt_zero_sard
    {φ : ℝ → ℝ} {T : Set ℝ}
    (hφ : ∀ t ∈ T, HasDerivWithinAt φ 0 T t) :
    MeasureTheory.volume (φ '' T) = 0 := by
  let φ' : ℝ → ℝ →L[ℝ] ℝ := fun _ ↦ 0
  have hφ' : ∀ t ∈ T, HasFDerivWithinAt φ (φ' t) T t := by
    intro t ht
    simpa [φ'] using (hφ t ht).hasFDerivWithinAt
  have hdet : ∀ t ∈ T, (φ' t).det = 0 := by
    intro t _ht
    simp [φ']
  simpa using
    (MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (μ := MeasureTheory.volume) (s := T) (f := φ) (f' := φ') hφ' hdet)

/--
%%handwave
name:
  Subsets of one-dimensional zero-derivative images have zero length
statement:
  If a subset of the real line is contained in the image of a set under a
  real-valued function whose relative derivative vanishes on that set, then
  the subset has one-dimensional Lebesgue measure zero.
proof:
  By [the whole image of a one-variable function with zero relative derivative is null](lean:JJMath.Uniformization.real_image_volume_zero_of_hasDerivWithinAt_zero_sard).  Measure monotonicity then makes every subset of that image null.
-/
theorem real_subset_image_volume_zero_of_hasDerivWithinAt_zero_sard
    {E T : Set ℝ} {φ : ℝ → ℝ}
    (hE : E ⊆ φ '' T)
    (hφ : ∀ t ∈ T, HasDerivWithinAt φ 0 T t) :
    MeasureTheory.volume E = 0 := by
  exact MeasureTheory.measure_mono_null hE
    (real_image_volume_zero_of_hasDerivWithinAt_zero_sard (φ := φ) (T := T) hφ)

/--
%%handwave
name:
  One-dimensional parameter images with zero differential have zero length
statement:
  If a real-valued function on a one-dimensional real normed vector space has
  zero relative Fréchet derivative on a subset, then the image of that subset
  has one-dimensional Lebesgue measure zero.
proof:
  Choose a continuous linear coordinate on the one-dimensional parameter
  space and reduce to the corresponding theorem for functions of one real
  variable.
-/
theorem real_image_volume_zero_of_oneDim_hasFDerivWithinAt_zero_sard
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 1) {φ : E → ℝ} {T : Set E}
    (hφ : ∀ t ∈ T, HasFDerivWithinAt φ (0 : E →L[ℝ] ℝ) T t) :
    MeasureTheory.volume (φ '' T) = 0 := by
  let e : ℝ ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simpa using hE.symm)
  let ψ : ℝ → ℝ := fun x ↦ φ (e x)
  let T' : Set ℝ := e ⁻¹' T
  have himage : φ '' T = ψ '' T' := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨e.symm t, by simpa [T'] using ht, by simp [ψ]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e x, by simpa [T'] using hx, rfl⟩
  have hψ : ∀ x ∈ T', HasDerivWithinAt ψ 0 T' x := by
    intro x hx
    have he : HasFDerivWithinAt (fun y : ℝ ↦ e y)
        (e : ℝ →L[ℝ] E) T' x := by
      simpa using (e : ℝ →L[ℝ] E).hasFDerivWithinAt (s := T') (x := x)
    have hcomp :
        HasFDerivWithinAt ψ
          ((0 : E →L[ℝ] ℝ).comp (e : ℝ →L[ℝ] E)) T' x := by
      simpa [ψ, T'] using (hφ (e x) (by simpa [T'] using hx)).comp x he (by
        intro y hy
        simpa [T'] using hy)
    simpa using hcomp.hasDerivWithinAt
  simpa [himage] using
    (real_image_volume_zero_of_hasDerivWithinAt_zero_sard (φ := ψ) (T := T') hψ)

/--
%%handwave
name:
  Subsets of one-dimensional zero-differential images have zero length
statement:
  If a subset of the real line is contained in the image of a set under a
  real-valued function on a one-dimensional real normed vector space whose
  relative Fréchet derivative vanishes on that set, then the subset has
  one-dimensional Lebesgue measure zero.
proof:
  By [the full image of the one-dimensional parameter set under such a function is null](lean:JJMath.Uniformization.real_image_volume_zero_of_oneDim_hasFDerivWithinAt_zero_sard).  The asserted subset is therefore null by monotonicity of measure.
-/
theorem real_subset_image_volume_zero_of_oneDim_hasFDerivWithinAt_zero_sard
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 1) {A : Set ℝ} {T : Set E} {φ : E → ℝ}
    (hA : A ⊆ φ '' T)
    (hφ : ∀ t ∈ T, HasFDerivWithinAt φ (0 : E →L[ℝ] ℝ) T t) :
    MeasureTheory.volume A = 0 := by
  exact MeasureTheory.measure_mono_null hA
    (real_image_volume_zero_of_oneDim_hasFDerivWithinAt_zero_sard
      (E := E) hE (φ := φ) (T := T) hφ)

/--
%%handwave
name:
  One-dimensional differentiable families of critical points have null value image
statement:
  Let a smooth real-valued function on an open subset of the plane be restricted
  to a one-dimensional differentiable family of critical points.  Then every
  subset of the corresponding set of values has one-dimensional Lebesgue
  measure zero.
proof:
  Along the family, the differential of the original function vanishes.  The
  chain rule therefore gives zero relative derivative for the composed
  one-dimensional value function, and the one-dimensional zero-derivative image
  theorem applies.
-/
theorem real_subset_parametricCriticalValues_volume_zero_of_oneDim_sard
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 1)
    {g : ℂ → ℝ} {U : Set ℂ} {A : Set ℝ} {T : Set E} {ψ : E → ℂ}
    (hU_open : IsOpen U)
    (hg_smooth : ContDiffOn ℝ ∞ g U)
    (hψU : ∀ t ∈ T, ψ t ∈ U)
    (hcrit : ∀ t ∈ T, fderiv ℝ g (ψ t) = 0)
    (hψdiff : ∀ t ∈ T, ∃ ψ' : E →L[ℝ] ℂ, HasFDerivWithinAt ψ ψ' T t)
    (hA : A ⊆ (fun t : E ↦ g (ψ t)) '' T) :
    MeasureTheory.volume A = 0 := by
  refine real_subset_image_volume_zero_of_oneDim_hasFDerivWithinAt_zero_sard
    (E := E) hE (A := A) (T := T) (φ := fun t : E ↦ g (ψ t)) hA ?_
  intro t ht
  rcases hψdiff t ht with ⟨ψ', hψ'⟩
  have hg_at : ContDiffAt ℝ ∞ g (ψ t) :=
    hg_smooth.contDiffAt (hU_open.mem_nhds (hψU t ht))
  have hgd : HasFDerivAt g (fderiv ℝ g (ψ t)) (ψ t) :=
    (hg_at.differentiableAt (by simp)).hasFDerivAt
  have hcomp :
      HasFDerivWithinAt (fun t : E ↦ g (ψ t))
        ((fderiv ℝ g (ψ t)).comp ψ') T t := by
    simpa [Function.comp_def] using hgd.comp_hasFDerivWithinAt t hψ'
  simpa [hcrit t ht] using hcomp

/--
%%handwave
name:
  Kernel of a nonzero real functional on the plane is one-dimensional
statement:
  The kernel of a nonzero real linear functional on the complex plane has real
  dimension one.
proof:
  Rank-nullity for a nonzero functional gives
  \(\dim \ker L + 1 = \dim_{\mathbb R}\mathbb C = 2\).
-/
theorem complex_realLinearFunctional_ker_finrank_eq_one
    {L : ℂ →L[ℝ] ℝ} (hL : L ≠ 0) :
    Module.finrank ℝ L.ker = 1 := by
  have hLlin : (L.toLinearMap : Module.Dual ℝ ℂ) ≠ 0 := by
    intro h
    apply hL
    ext z
    exact LinearMap.ext_iff.mp h z
  have hrank :=
    Module.Dual.finrank_ker_add_one_of_ne_zero
      (K := ℝ) (V₁ := ℂ) (f := (L.toLinearMap : Module.Dual ℝ ℂ)) hLlin
  have hrank' : Module.finrank ℝ L.ker + 1 = 2 := by
    simpa [Complex.finrank_real_complex] using hrank
  omega

/--
%%handwave
name:
  Nonzero real functionals on the plane are surjective
statement:
  A nonzero real linear functional on the complex plane has range all of the
  real line.
proof:
  A nonzero linear functional into the one-dimensional space \(\mathbb R\)
  has rank one.  Its range is therefore a nonzero subspace of \(\mathbb R\),
  hence all of \(\mathbb R\).
-/
theorem complex_realLinearFunctional_range_eq_top
    {L : ℂ →L[ℝ] ℝ} (hL : L ≠ 0) :
    L.range = ⊤ := by
  have hLlin : (L.toLinearMap : Module.Dual ℝ ℂ) ≠ 0 := by
    intro h
    apply hL
    ext z
    exact LinearMap.ext_iff.mp h z
  simpa using
    (Module.Dual.range_eq_top_of_ne_zero
      (K := ℝ) (V₁ := ℂ) (f := (L.toLinearMap : Module.Dual ℝ ℂ)) hLlin)

/--
%%handwave
name:
  Nonzero second derivative has a nonzero component
statement:
  If the second derivative of a smooth real-valued function on the plane does
  not vanish at a point, then some directional component of that second
  derivative is a nonzero real linear functional.
proof:
  Regard the second derivative as a linear map
  \(H\colon\mathbb C\to\operatorname{Hom}_{\mathbb R}(\mathbb C,\mathbb R)\).
  If \(H(v)=0\) for every \(v\), then extensionality gives \(H=0\), contrary
  to the hypothesis.
-/
theorem planeSecondDerivative_nonzero_has_nonzero_component
    {g : ℂ → ℝ} {z : ℂ}
    (hznonzero : ¬ PlaneSecondDerivativeZeroAt g z) :
    ∃ v : ℂ,
      (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ g w) z) v ≠ 0 := by
  by_contra hnone
  apply hznonzero
  have hforall : ∀ v : ℂ,
      ¬ (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ g w) z) v ≠ 0 := by
    simpa [not_exists] using hnone
  exact ContinuousLinearMap.ext fun v ↦ not_not.mp (hforall v)

/--
%%handwave
name:
  Nonzero second derivative has a nonzero evaluated component
statement:
  If the second derivative of a smooth real-valued function on the plane does
  not vanish at a point, then there are two directions for which the
  corresponding bilinear evaluation is nonzero.
proof:
  By [some directional component \(H(u)\) is a nonzero linear functional](lean:JJMath.Uniformization.planeSecondDerivative_nonzero_has_nonzero_component).  A nonzero functional has some \(v\) with \(H(u)(v)\ne0\).
-/
theorem planeSecondDerivative_nonzero_has_nonzero_evaluation
    {g : ℂ → ℝ} {z : ℂ}
    (hznonzero : ¬ PlaneSecondDerivativeZeroAt g z) :
    ∃ u v : ℂ,
      (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ g w) z) u v ≠ 0 := by
  rcases planeSecondDerivative_nonzero_has_nonzero_component
      (g := g) (z := z) hznonzero with
    ⟨u, hu⟩
  by_contra hnone
  apply hu
  have hforall₂ : ∀ u v : ℂ,
      ¬ (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ g w) z) u v ≠ 0 := by
    simpa [not_exists] using hnone
  have hforall : ∀ v : ℂ,
      ¬ (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ g w) z) u v ≠ 0 := by
    intro v
    exact hforall₂ u v
  exact ContinuousLinearMap.ext fun v ↦ not_not.mp (hforall v)

/--
%%handwave
name:
  Nonzero evaluated component gives a nonzero scalar functional
statement:
  If an evaluated second-derivative component is nonzero, then the scalar
  functional obtained by evaluating the second derivative in the second
  direction is nonzero.
proof:
  If the functional \(w\mapsto H(w)(v)\) were zero, evaluating it at \(u\)
  would give \(H(u)(v)=0\), contradicting the hypothesis.
-/
theorem planeSecondDerivative_evaluation_functional_ne_zero
    {H : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)} {u v : ℂ}
    (huv : H u v ≠ 0) :
    ((ContinuousLinearMap.apply ℝ ℝ v).comp H) ≠ 0 := by
  intro hzero
  have hval :
      ((ContinuousLinearMap.apply ℝ ℝ v).comp H) u = 0 := by
    simpa using congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L u) hzero
  exact huv (by simpa using hval)

/--
%%handwave
name:
  Nonzero evaluated component has one-dimensional scalar kernel
statement:
  If an evaluated second-derivative component is nonzero, then the kernel of
  the corresponding scalar functional on the plane has real dimension one.
proof:
  By [the evaluation functional is nonzero](lean:JJMath.Uniformization.planeSecondDerivative_evaluation_functional_ne_zero), and [the kernel of any nonzero real functional on \(\mathbb C\) has dimension one](lean:JJMath.Uniformization.complex_realLinearFunctional_ker_finrank_eq_one).
-/
theorem planeSecondDerivative_evaluation_functional_ker_finrank_eq_one
    {H : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)} {u v : ℂ}
    (huv : H u v ≠ 0) :
    Module.finrank ℝ (((ContinuousLinearMap.apply ℝ ℝ v).comp H).ker) = 1 :=
  complex_realLinearFunctional_ker_finrank_eq_one
    (planeSecondDerivative_evaluation_functional_ne_zero
      (H := H) (u := u) (v := v) huv)

/--
%%handwave
name:
  Nonzero evaluated component is a surjective scalar functional
statement:
  If an evaluated second-derivative component is nonzero, then the
  corresponding scalar functional on the plane has range all of the real line.
proof:
  By [the evaluation functional is nonzero](lean:JJMath.Uniformization.planeSecondDerivative_evaluation_functional_ne_zero), and [every nonzero real functional on \(\mathbb C\) is surjective](lean:JJMath.Uniformization.complex_realLinearFunctional_range_eq_top).
-/
theorem planeSecondDerivative_evaluation_functional_range_eq_top
    {H : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)} {u v : ℂ}
    (huv : H u v ≠ 0) :
    ((ContinuousLinearMap.apply ℝ ℝ v).comp H).range = ⊤ :=
  complex_realLinearFunctional_range_eq_top
    (planeSecondDerivative_evaluation_functional_ne_zero
      (H := H) (u := u) (v := v) huv)

/--
%%handwave
name:
  Smooth functions have strictly differentiable first differential
statement:
  If a real-valued function is smooth on an open subset of the plane, then its
  first differential, viewed as a map to the dual plane, is strictly
  differentiable at each point of the open subset.
proof:
  Smoothness on an open neighborhood gives smoothness at the chosen point.
  Differentiating once preserves smoothness, and a smooth map is strictly
  differentiable there with derivative equal to its Fréchet derivative.
-/
theorem smoothPlaneFunction_hasStrictFDerivAt_fderiv
    {g : ℂ → ℝ} {U : Set ℂ} {z : ℂ}
    (hU_open : IsOpen U) (hzU : z ∈ U)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    HasStrictFDerivAt
      (fun w : ℂ ↦ fderiv ℝ g w)
      (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ g w) z) z := by
  have hg_at : ContDiffAt ℝ ∞ g z :=
    hg_smooth.contDiffAt (hU_open.mem_nhds hzU)
  have hF_smooth :
      ContDiffAt ℝ ∞ (fun w : ℂ ↦ fderiv ℝ g w) z :=
    hg_at.fderiv_right (m := ∞) (by simp)
  simpa using hF_smooth.hasStrictFDerivAt (by simp)

/--
%%handwave
name:
  Smooth directional differential components are strictly differentiable
statement:
  If a real-valued function is smooth on an open subset of the plane, then
  each directional component of its first differential is strictly
  differentiable at each point of the open subset, with derivative obtained
  by evaluating the second derivative in that direction.
proof:
  By [the differential-valued map is strictly differentiable with derivative equal to the second derivative](lean:JJMath.Uniformization.smoothPlaneFunction_hasStrictFDerivAt_fderiv).  Compose it with evaluation at \(v\); the chain rule gives \(w\mapsto H(w)(v)\).
-/
theorem smoothPlaneFunction_hasStrictFDerivAt_fderiv_apply
    {g : ℂ → ℝ} {U : Set ℂ} {z v : ℂ}
    (hU_open : IsOpen U) (hzU : z ∈ U)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    HasStrictFDerivAt
      (fun w : ℂ ↦ fderiv ℝ g w v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp
        (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ g w) z)) z := by
  let ev : (ℂ →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  have hF :=
    smoothPlaneFunction_hasStrictFDerivAt_fderiv
      (g := g) (U := U) (z := z) hU_open hzU hg_smooth
  simpa [ev, Function.comp_def] using ev.hasStrictFDerivAt.comp z hF

/--
%%handwave
name:
  Quadratic remainder at a zero-Hessian critical point
statement:
  If the first and second differentials of a smooth real-valued plane
  function vanish at a point, then the change in the function is little-oh of
  the square of the distance to that point.
proof:
  On a small convex disk inside the domain, the first differential is
  little-oh of the distance from the center.  The mean-value Taylor estimate
  upgrades this to a quadratic little-oh estimate for the function itself.
-/
theorem smoothPlaneFunction_zeroSecondDerivativeAt_quadratic_remainder_sard
    {g : ℂ → ℝ} {U : Set ℂ} {z : ℂ}
    (hU_open : IsOpen U) (hzU : z ∈ U)
    (hzcrit : fderiv ℝ g z = 0)
    (hzzero : PlaneSecondDerivativeZeroAt g z)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    (fun w : ℂ ↦ g w - g z) =o[𝓝 z] fun w : ℂ ↦ ‖w - z‖ ^ 2 := by
  let F : ℂ → (ℂ →L[ℝ] ℝ) := fun w ↦ fderiv ℝ g w
  rcases Metric.isOpen_iff.mp hU_open z hzU with ⟨r, hr_pos, hball_subset_U⟩
  let S : Set ℂ := Metric.ball z r
  have hzS : z ∈ S := by
    simp [S, hr_pos]
  have hS_nhds : S ∈ 𝓝 z := by
    exact Metric.ball_mem_nhds z hr_pos
  have hF_deriv0 : HasFDerivAt F (0 : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) z := by
    have hF_strict :=
      smoothPlaneFunction_hasStrictFDerivAt_fderiv
        (g := g) (U := U) (z := z) hU_open hzU hg_smooth
    have hF_at := hF_strict.hasFDerivAt
    rw [show fderiv ℝ (fun w : ℂ ↦ fderiv ℝ g w) z = 0 by
      simpa [PlaneSecondDerivativeZeroAt] using hzzero] at hF_at
    simpa [F] using hF_at
  have hF_littleO :
      F =o[𝓝 z] fun w : ℂ ↦ ‖w - z‖ ^ 1 := by
    have hF0 : F z = 0 := by
      simpa [F] using hzcrit
    have hraw :
        (fun w : ℂ ↦ F w - F z - (0 : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) (w - z))
          =o[𝓝 z] fun w : ℂ ↦ w - z :=
      hF_deriv0.isLittleO
    have hF_vec : F =o[𝓝 z] fun w : ℂ ↦ w - z := by
      simpa [hF0] using hraw
    simpa [pow_one] using hF_vec.norm_right
  have hF_littleO_within :
      F =o[𝓝[S] z] fun w : ℂ ↦ ‖w - z‖ ^ 1 :=
    hF_littleO.mono nhdsWithin_le_nhds
  have hg_deriv_on : ∀ w ∈ S, HasFDerivWithinAt g (F w) S w := by
    intro w hwS
    have hwU : w ∈ U := hball_subset_U hwS
    have hg_at : ContDiffAt ℝ ∞ g w :=
      hg_smooth.contDiffAt (hU_open.mem_nhds hwU)
    have hgd : HasFDerivAt g (fderiv ℝ g w) w :=
      (hg_at.differentiableAt (by simp)).hasFDerivAt
    simpa [F] using hgd.hasFDerivWithinAt (s := S)
  have hwithin :
      (fun w : ℂ ↦ g w - g z) =o[𝓝[S] z] fun w : ℂ ↦ ‖w - z‖ ^ (1 + 1) :=
    (convex_ball z r).isLittleO_pow_succ hzS hg_deriv_on hF_littleO_within
  have hfilter : 𝓝[S] z = 𝓝 z := nhdsWithin_eq_nhds.mpr hS_nhds
  simpa [hfilter, one_add_one_eq_two] using hwithin

/--
%%handwave
name:
  Local regular critical values are single-valued
statement:
  If a smooth real-valued function has a critical point at which the second
  derivative is nondegenerate, then some neighborhood of that point has at
  most one critical value attained at critical points with nondegenerate
  second derivative.
proof:
  Apply the inverse-function theorem to the first differential.  The first
  differential is locally injective, so its zero fiber has at most one point in
  a sufficiently small neighborhood.
-/
theorem smoothPlaneFunction_regularCriticalValuesOn_nhds_subsingleton_sard
    {g : ℂ → ℝ} {U : Set ℂ} {z : ℂ}
    (hU_open : IsOpen U) (hzU : z ∈ U)
    (hzcrit : fderiv ℝ g z = 0)
    (hzreg : ¬ PlaneSecondDerivativeDegenerateAt g z)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      {c : ℝ | PlaneSecondDerivativeRegularCriticalValueOn g V c}.Subsingleton := by
  classical
  let F : ℂ → (ℂ →L[ℝ] ℝ) := fun w ↦ fderiv ℝ g w
  have hF_inv : (fderiv ℝ F z).IsInvertible := by
    by_contra hnot
    exact hzreg (by simpa [PlaneSecondDerivativeDegenerateAt, F] using hnot)
  let e : ℂ ≃L[ℝ] (ℂ →L[ℝ] ℝ) := Classical.choose hF_inv
  have he : (e : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) = fderiv ℝ F z :=
    Classical.choose_spec hF_inv
  have hg_at : ContDiffAt ℝ ∞ g z :=
    hg_smooth.contDiffAt (hU_open.mem_nhds hzU)
  have hF_smooth : ContDiffAt ℝ ∞ F z := by
    dsimp [F]
    exact hg_at.fderiv_right (m := ∞) (by simp)
  have hF_strict :
      HasStrictFDerivAt F (e : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) z := by
    simpa [he] using hF_smooth.hasStrictFDerivAt (by simp)
  let E : OpenPartialHomeomorph ℂ (ℂ →L[ℝ] ℝ) :=
    hF_strict.toOpenPartialHomeomorph F
  have hz_source : z ∈ E.source := by
    simpa [E] using hF_strict.mem_toOpenPartialHomeomorph_source
  refine ⟨E.source ∩ U, E.open_source.inter hU_open, ⟨hz_source, hzU⟩, ?_, ?_⟩
  · intro w hw
    exact hw.2
  · intro c hc d hd
    rcases hc with ⟨w, hwV, hgw, hwcrit, _hwreg⟩
    rcases hd with ⟨w', hw'V, hgw', hw'crit, _hw'reg⟩
    have hE_apply (x : ℂ) : E x = F x := by
      simp [E]
    have hF_z : F z = 0 := by
      simpa [F] using hzcrit
    have hF_w : F w = 0 := by
      simpa [F] using hwcrit
    have hF_w' : F w' = 0 := by
      simpa [F] using hw'crit
    have hzw : z = w := by
      apply E.injOn hz_source hwV.1
      rw [hE_apply z, hE_apply w, hF_z, hF_w]
    have hzw' : z = w' := by
      apply E.injOn hz_source hw'V.1
      rw [hE_apply z, hE_apply w', hF_z, hF_w']
    calc
      c = g w := hgw.symm
      _ = g z := by rw [← hzw]
      _ = g w' := by rw [hzw']
      _ = d := hgw'

/--
%%handwave
name:
  Local regular critical values have measure zero
statement:
  If a smooth real-valued function has a critical point at which the second
  derivative is nondegenerate, then some neighborhood of that point has a null
  set of critical values attained at critical points with nondegenerate second
  derivative.
proof:
  The local critical values are single-valued, and singleton subsets of the
  real line have zero Lebesgue measure.
-/
theorem smoothPlaneFunction_regularCriticalValuesOn_nhds_volume_zero_sard
    {g : ℂ → ℝ} {U : Set ℂ} {z : ℂ}
    (hU_open : IsOpen U) (hzU : z ∈ U)
    (hzcrit : fderiv ℝ g z = 0)
    (hzreg : ¬ PlaneSecondDerivativeDegenerateAt g z)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      MeasureTheory.volume
        {c : ℝ | PlaneSecondDerivativeRegularCriticalValueOn g V c} = 0 := by
  rcases smoothPlaneFunction_regularCriticalValuesOn_nhds_subsingleton_sard
      (g := g) (U := U) (z := z) hU_open hzU hzcrit hzreg hg_smooth with
    ⟨V, hV_open, hzV, hVU, hV_subsingleton⟩
  exact ⟨V, hV_open, hzV, hVU, hV_subsingleton.measure_zero MeasureTheory.volume⟩

/--
%%handwave
name:
  Closed-ball regular critical values have measure zero
statement:
  For a smooth real-valued function on an open subset of the complex plane,
  the critical values attained on a closed ball at critical points with
  nondegenerate second derivative have one-dimensional Lebesgue measure zero.
proof:
  The nondegenerate second derivative makes the first differential locally
  injective by the inverse-function theorem, so local regular critical values
  are single-valued.  A Lindelof subcover reduces the closed ball to
  countably many such neighborhoods.
-/
theorem smoothPlaneFunction_closedBallRegularCriticalValuesOn_volume_zero_sard
    {g : ℂ → ℝ} {U : Set ℂ} (a : ℂ) (r : ℝ)
    (hU_open : IsOpen U) (hball_subset : Metric.closedBall a r ⊆ U)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    MeasureTheory.volume
        {c : ℝ |
          PlaneSecondDerivativeRegularCriticalValueOn
            g (Metric.closedBall a r) c} = 0 := by
  classical
  let R : Set ℂ :=
    {z : ℂ | z ∈ Metric.closedBall a r ∧ fderiv ℝ g z = 0 ∧
      ¬ PlaneSecondDerivativeDegenerateAt g z}
  have hR_lindelof : IsLindelof R :=
    HereditarilyLindelofSpace.isLindelof R
  let V : R → Set ℂ := fun x ↦
    Classical.choose
      (smoothPlaneFunction_regularCriticalValuesOn_nhds_volume_zero_sard
        (g := g) (U := U) (z := (x : ℂ)) hU_open
        (hball_subset x.property.1) x.property.2.1 x.property.2.2 hg_smooth)
  have hV_spec : ∀ x : R, IsOpen (V x) ∧ (x : ℂ) ∈ V x ∧ V x ⊆ U ∧
      MeasureTheory.volume
        {c : ℝ | PlaneSecondDerivativeRegularCriticalValueOn g (V x) c} = 0 := by
    intro x
    exact Classical.choose_spec
      (smoothPlaneFunction_regularCriticalValuesOn_nhds_volume_zero_sard
        (g := g) (U := U) (z := (x : ℂ)) hU_open
        (hball_subset x.property.1) x.property.2.1 x.property.2.2 hg_smooth)
  have hR_cover : R ⊆ ⋃ x : R, V x := by
    intro z hzR
    exact Set.mem_iUnion.mpr ⟨⟨z, hzR⟩, (hV_spec ⟨z, hzR⟩).2.1⟩
  rcases hR_lindelof.elim_countable_subcover V (fun x ↦ (hV_spec x).1) hR_cover with
    ⟨t, ht_countable, ht_cover⟩
  have hsubset :
      {c : ℝ |
        PlaneSecondDerivativeRegularCriticalValueOn
          g (Metric.closedBall a r) c} ⊆
        ⋃ x ∈ t, {c : ℝ | PlaneSecondDerivativeRegularCriticalValueOn g (V x) c} := by
    intro c hc
    rcases hc with ⟨z, hz_ball, hgz, hzcrit, hzreg⟩
    have hzR : z ∈ R := ⟨hz_ball, hzcrit, hzreg⟩
    have hz_cover : z ∈ ⋃ x ∈ t, V x := ht_cover hzR
    rcases Set.mem_iUnion.mp hz_cover with ⟨x, hx_cover⟩
    rcases Set.mem_iUnion.mp hx_cover with ⟨hxt, hzV⟩
    exact Set.mem_iUnion.mpr
      ⟨x, Set.mem_iUnion.mpr ⟨hxt, ⟨z, hzV, hgz, hzcrit, hzreg⟩⟩⟩
  have hunion_zero :
      MeasureTheory.volume
          (⋃ x ∈ t,
            {c : ℝ | PlaneSecondDerivativeRegularCriticalValueOn g (V x) c}) = 0 := by
    rw [MeasureTheory.measure_biUnion_null_iff ht_countable]
    intro x _hx
    exact (hV_spec x).2.2.2
  exact MeasureTheory.measure_mono_null hsubset hunion_zero

/--
%%handwave
name:
  The implicit curve covers nearby nonzero singular critical points
statement:
  Near a critical point with nonzero second derivative, a nonzero scalar
  component of the derivative of the first differential has a one-dimensional
  implicit level curve.  After shrinking to where the chart derivative remains
  invertible, every nearby critical value is attained along a differentiable
  parametrization of that curve.
proof:
  Choose a nonzero evaluated component of the second derivative and apply the
  implicit-function theorem to the corresponding scalar component of the first
  differential.  Openness of the invertible linear maps lets us shrink the
  neighborhood so the inverse chart is differentiable along the selected
  parameters.  The local inverse chart represents all nearby points on the
  selected level set, and every critical point lies on that level set.
-/
theorem smoothPlaneFunction_nonzeroSingularCriticalValuesOn_nhds_implicit_curve_cover_sard
    {g : ℂ → ℝ} {U : Set ℂ} {z : ℂ}
    (hU_open : IsOpen U) (hzU : z ∈ U)
    (hzcrit : fderiv ℝ g z = 0)
    (hznonzero : ¬ PlaneSecondDerivativeZeroAt g z)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    ∃ (V : Set ℂ) (L : ℂ →L[ℝ] ℝ) (T : Set L.ker) (ψ : L.ker → ℂ),
      IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
        Module.finrank ℝ L.ker = 1 ∧
        (∀ t ∈ T, ψ t ∈ V) ∧
        (∀ t ∈ T, fderiv ℝ g (ψ t) = 0) ∧
        (∀ t ∈ T, ∃ ψ' : L.ker →L[ℝ] ℂ, HasFDerivWithinAt ψ ψ' T t) ∧
        {c : ℝ | PlaneSecondDerivativeNonzeroSingularCriticalValueOn g V c} ⊆
          (fun t : L.ker ↦ g (ψ t)) '' T := by
  classical
  let H : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    fderiv ℝ (fun w : ℂ ↦ fderiv ℝ g w) z
  rcases planeSecondDerivative_nonzero_has_nonzero_evaluation
      (g := g) (z := z) hznonzero with
    ⟨u, v, huv⟩
  let L : ℂ →L[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ v).comp H
  let h : ℂ → ℝ := fun w ↦ fderiv ℝ g w v
  let hker : L.ker.ClosedComplemented :=
    L.ker_closedComplemented_of_finiteDimensional_range
  let P : ℂ →L[ℝ] L.ker := Classical.choose hker
  have hLdim : Module.finrank ℝ L.ker = 1 := by
    simpa [L, H] using
      planeSecondDerivative_evaluation_functional_ker_finrank_eq_one
        (H := H) (u := u) (v := v) huv
  have hLrange : L.range = ⊤ := by
    simpa [L, H] using
      planeSecondDerivative_evaluation_functional_range_eq_top
        (H := H) (u := u) (v := v) huv
  have hh_strict : HasStrictFDerivAt h L z := by
    simpa [h, L, H] using
      smoothPlaneFunction_hasStrictFDerivAt_fderiv_apply
        (g := g) (U := U) (z := z) (v := v) hU_open hzU hg_smooth
  let E : OpenPartialHomeomorph ℂ (ℝ × L.ker) :=
    hh_strict.implicitToOpenPartialHomeomorph h L hLrange
  let ψ : L.ker → ℂ := hh_strict.implicitFunction h L hLrange (h z)
  let coordDeriv : ℂ → ℂ →L[ℝ] (ℝ × L.ker) :=
    fun w ↦ (fderiv ℝ h w).prod P
  have hP_range : P.range = ⊤ := by
    exact LinearMap.range_eq_of_proj (Classical.choose_spec hker)
  have hLP_compl : IsCompl (L : ℂ →ₗ[ℝ] ℝ).ker (P : ℂ →ₗ[ℝ] L.ker).ker := by
    exact LinearMap.isCompl_of_proj (Classical.choose_spec hker)
  haveI hker_complete : CompleteSpace L.ker := inferInstance
  haveI hprod_complete : CompleteSpace (ℝ × L.ker) := inferInstance
  let baseE : ℂ ≃L[ℝ] (ℝ × L.ker) :=
    @ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl ℝ ℂ ℝ L.ker
      _ _ _ _ _ _ _ _ hprod_complete L P hLrange hP_range hLP_compl
  have hdh_z : fderiv ℝ h z = L := by
    exact hh_strict.hasFDerivAt.fderiv
  have hbaseE_prod : (baseE : ℂ →L[ℝ] (ℝ × L.ker)) = L.prod P := by
    rfl
  have hbaseE : (baseE : ℂ →L[ℝ] (ℝ × L.ker)) = coordDeriv z := by
    rw [hbaseE_prod]
    simp [coordDeriv, hdh_z]
  have hh_smooth_at_z : ContDiffAt ℝ ∞ h z := by
    let ev : (ℂ →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
    have hg_at : ContDiffAt ℝ ∞ g z :=
      hg_smooth.contDiffAt (hU_open.mem_nhds hzU)
    have hF_smooth : ContDiffAt ℝ ∞ (fun w : ℂ ↦ fderiv ℝ g w) z :=
      hg_at.fderiv_right (m := ∞) (by simp)
    simpa [h, ev, Function.comp_def] using ev.contDiff.contDiffAt.comp z hF_smooth
  have hcoord_cont : ContinuousAt coordDeriv z := by
    have hfderiv_cont : ContinuousAt (fun x : ℂ ↦ fderiv ℝ h x) z :=
      hh_smooth_at_z.continuousAt_fderiv (by simp)
    have hpair : ContinuousAt (fun x : ℂ ↦ (fderiv ℝ h x, P)) z :=
      hfderiv_cont.prodMk continuousAt_const
    simpa [coordDeriv] using
      ((ContinuousLinearMap.prodL ℝ (𝕜 := ℝ) (E := ℂ) (F := ℝ) (G := L.ker)).continuous
        |>.continuousAt.comp hpair)
  have hgood_mem :
      {w : ℂ |
        coordDeriv w ∈
          Set.range ((↑) : (ℂ ≃L[ℝ] (ℝ × L.ker)) → ℂ →L[ℝ] (ℝ × L.ker))} ∈ 𝓝 z := by
    have htarget :
        Set.range ((↑) : (ℂ ≃L[ℝ] (ℝ × L.ker)) → ℂ →L[ℝ] (ℝ × L.ker)) ∈
          𝓝 (baseE : ℂ →L[ℝ] (ℝ × L.ker)) :=
      ContinuousLinearEquiv.nhds baseE
    have htendsto :
        Filter.Tendsto coordDeriv (𝓝 z) (𝓝 (baseE : ℂ →L[ℝ] (ℝ × L.ker))) := by
      simpa [hbaseE] using hcoord_cont
    exact htendsto htarget
  rcases mem_nhds_iff.mp hgood_mem with ⟨W, hW_good, hW_open, hzW⟩
  let V : Set ℂ := E.source ∩ U ∩ W
  let T : Set L.ker :=
    {t | ∃ w ∈ V, fderiv ℝ g w = 0 ∧ (E w).snd = t}
  have hz_source : z ∈ E.source := by
    simpa [E] using hh_strict.mem_implicitToOpenPartialHomeomorph_source hLrange
  have hzV : z ∈ V := ⟨⟨hz_source, hzU⟩, hzW⟩
  have hVU : V ⊆ U := fun _ hw ↦ hw.1.2
  have hz_level : h z = 0 := by
    simpa [h] using congrArg (fun L' : ℂ →L[ℝ] ℝ ↦ L' v) hzcrit
  have hE_fst (w : ℂ) : (E w).fst = h w := by
    simp [E]
  have hψ_eq_of_witness :
      ∀ {t : L.ker} {w : ℂ}, w ∈ V → fderiv ℝ g w = 0 → (E w).snd = t →
        ψ t = w := by
    intro t w hwV hwcrit hwt
    have hw_level : h w = h z := by
      have : h w = 0 := by
        simpa [h] using congrArg (fun L' : ℂ →L[ℝ] ℝ ↦ L' v) hwcrit
      rw [this, hz_level]
    have hp : (h z, t) = E w := by
      ext <;> simp [hE_fst, hw_level, hwt]
    change E.symm (h z, t) = w
    rw [hp]
    exact E.left_inv hwV.1.1
  have hE_apply (x : ℂ) : E x = (h x, P x - P z) := by
    simpa [E, P, hker, HasStrictFDerivAt.implicitToOpenPartialHomeomorph] using
      (hh_strict.implicitToOpenPartialHomeomorphOfComplemented_apply
        (f := h) (f' := L) hLrange hker x)
  have hE_fun : (E : ℂ → ℝ × L.ker) = fun x : ℂ ↦ (h x, P x - P z) := by
    funext x
    exact hE_apply x
  refine
    ⟨V, L, T, ψ, (E.open_source.inter hU_open).inter hW_open, hzV, hVU,
      hLdim, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases ht with ⟨w, hwV, hwcrit, hwt⟩
    rw [hψ_eq_of_witness hwV hwcrit hwt]
    exact hwV
  · intro t ht
    rcases ht with ⟨w, hwV, hwcrit, hwt⟩
    rw [hψ_eq_of_witness hwV hwcrit hwt]
    exact hwcrit
  · intro t ht
    rcases ht with ⟨w, hwV, hwcrit, hwt⟩
    have hw_good :
        coordDeriv w ∈
          Set.range ((↑) : (ℂ ≃L[ℝ] (ℝ × L.ker)) → ℂ →L[ℝ] (ℝ × L.ker)) :=
      hW_good hwV.2
    rcases hw_good with ⟨ew, hew⟩
    have hh_smooth_at_w : ContDiffAt ℝ ∞ h w := by
      let ev : (ℂ →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
      have hg_at : ContDiffAt ℝ ∞ g w :=
        hg_smooth.contDiffAt (hU_open.mem_nhds (hVU hwV))
      have hF_smooth : ContDiffAt ℝ ∞ (fun y : ℂ ↦ fderiv ℝ g y) w :=
        hg_at.fderiv_right (m := ∞) (by simp)
      simpa [h, ev, Function.comp_def] using ev.contDiff.contDiffAt.comp w hF_smooth
    have hh_deriv_w : HasFDerivAt h (fderiv ℝ h w) w :=
      (hh_smooth_at_w.differentiableAt (by simp)).hasFDerivAt
    have hP_deriv_w : HasFDerivAt (fun y : ℂ ↦ P y - P z) P w :=
      P.hasFDerivAt.sub_const (P z)
    have hprod_deriv_w :
        HasFDerivAt (fun y : ℂ ↦ (h y, P y - P z)) (coordDeriv w) w := by
      simpa [coordDeriv] using hh_deriv_w.prodMk hP_deriv_w
    have hE_deriv_w : HasFDerivAt E (ew : ℂ →L[ℝ] (ℝ × L.ker)) w := by
      have hE_deriv_coord : HasFDerivAt E (coordDeriv w) w := by
        simpa [hE_fun] using hprod_deriv_w
      simpa [hew] using hE_deriv_coord
    have hw_level : h w = h z := by
      have : h w = 0 := by
        simpa [h] using congrArg (fun L' : ℂ →L[ℝ] ℝ ↦ L' v) hwcrit
      rw [this, hz_level]
    have hp : (h z, t) = E w := by
      ext <;> simp [hE_fst, hw_level, hwt]
    have htarget : (h z, t) ∈ E.target := by
      rw [hp]
      exact E.map_source hwV.1.1
    have hsymm_point : E.symm (h z, t) = w := by
      change ψ t = w
      exact hψ_eq_of_witness hwV hwcrit hwt
    have hsymm_deriv :
        HasFDerivAt E.symm (ew.symm : (ℝ × L.ker) →L[ℝ] ℂ) (h z, t) := by
      refine E.hasFDerivAt_symm htarget ?_
      convert hE_deriv_w using 1
    let ι : L.ker →L[ℝ] (ℝ × L.ker) :=
      (0 : L.ker →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ L.ker)
    have hparam_deriv : HasFDerivAt (fun s : L.ker ↦ (h z, s)) ι t := by
      simpa [ι] using
        (hasFDerivAt_const (x := t) (c := h z)).prodMk (hasFDerivAt_id t)
    refine ⟨(ew.symm : (ℝ × L.ker) →L[ℝ] ℂ).comp ι, ?_⟩
    have hψ_deriv : HasFDerivAt ψ
        ((ew.symm : (ℝ × L.ker) →L[ℝ] ℂ).comp ι) t := by
      change HasFDerivAt (fun s : L.ker ↦ E.symm (h z, s))
        ((ew.symm : (ℝ × L.ker) →L[ℝ] ℂ).comp ι) t
      exact hsymm_deriv.comp t hparam_deriv
    exact hψ_deriv.hasFDerivWithinAt
  · intro c hc
    rcases hc with ⟨w, hwV, hgw, hwcrit, _hwdeg, _hwnonzero⟩
    let t : L.ker := (E w).snd
    have ht : t ∈ T := ⟨w, hwV, hwcrit, rfl⟩
    refine ⟨t, ht, ?_⟩
    have hψt : ψ t = w := hψ_eq_of_witness hwV hwcrit rfl
    simpa [hψt] using hgw

/--
%%handwave
name:
  Local nonzero singular critical points admit a differentiable curve parametrization
statement:
  Near a critical point where the second derivative is singular but not zero,
  the corresponding critical points lie on a one-dimensional differentiable
  family.  The critical values are therefore contained in the values of the
  original function along this family.
proof:
  Choose a nonzero component of the derivative of the first differential and
  use the implicit-function theorem to parametrize the local zero set by a
  smooth curve.
-/
theorem smoothPlaneFunction_nonzeroSingularCriticalValuesOn_nhds_curve_parametrized_sard
    {g : ℂ → ℝ} {U : Set ℂ} {z : ℂ}
    (hU_open : IsOpen U) (hzU : z ∈ U)
    (hzcrit : fderiv ℝ g z = 0)
    (_hzdeg : PlaneSecondDerivativeDegenerateAt g z)
    (hznonzero : ¬ PlaneSecondDerivativeZeroAt g z)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    ∃ (V : Set ℂ) (L : ℂ →L[ℝ] ℝ) (T : Set L.ker) (ψ : L.ker → ℂ),
      IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
        Module.finrank ℝ L.ker = 1 ∧
        (∀ t ∈ T, ψ t ∈ V) ∧
        (∀ t ∈ T, fderiv ℝ g (ψ t) = 0) ∧
        (∀ t ∈ T, ∃ ψ' : L.ker →L[ℝ] ℂ, HasFDerivWithinAt ψ ψ' T t) ∧
        {c : ℝ | PlaneSecondDerivativeNonzeroSingularCriticalValueOn g V c} ⊆
          (fun t : L.ker ↦ g (ψ t)) '' T := by
  rcases smoothPlaneFunction_nonzeroSingularCriticalValuesOn_nhds_implicit_curve_cover_sard
      (g := g) (U := U) (z := z) hU_open hzU hzcrit hznonzero hg_smooth with
    ⟨V, L, T, ψ, hV_open, hzV, hVU, hLdim, hψV, hψcrit, hψdiff, hsubset⟩
  exact ⟨V, L, T, ψ, hV_open, hzV, hVU, hLdim, hψV, hψcrit, hψdiff, hsubset⟩

/--
%%handwave
name:
  Local nonzero singular critical values have measure zero
statement:
  Near a critical point where the second derivative is singular but not zero,
  the critical values attained at such points have one-dimensional Lebesgue
  measure zero.
proof:
  Use the local curve parametrization and apply the one-dimensional
  zero-derivative image theorem.
-/
theorem smoothPlaneFunction_nonzeroSingularCriticalValuesOn_nhds_volume_zero_sard
    {g : ℂ → ℝ} {U : Set ℂ} {z : ℂ}
    (hU_open : IsOpen U) (hzU : z ∈ U)
    (hzcrit : fderiv ℝ g z = 0)
    (hzdeg : PlaneSecondDerivativeDegenerateAt g z)
    (hznonzero : ¬ PlaneSecondDerivativeZeroAt g z)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      MeasureTheory.volume
        {c : ℝ | PlaneSecondDerivativeNonzeroSingularCriticalValueOn g V c} = 0 := by
  rcases smoothPlaneFunction_nonzeroSingularCriticalValuesOn_nhds_curve_parametrized_sard
      (g := g) (U := U) (z := z)
      hU_open hzU hzcrit hzdeg hznonzero hg_smooth with
    ⟨V, L, T, ψ, hV_open, hzV, hVU, hLdim, hψV, hψcrit, hψdiff, hsubset⟩
  exact ⟨V, hV_open, hzV, hVU,
    real_subset_parametricCriticalValues_volume_zero_of_oneDim_sard
      (E := L.ker) hLdim (U := U)
      (A := {c : ℝ | PlaneSecondDerivativeNonzeroSingularCriticalValueOn g V c})
      (T := T) (ψ := ψ) hU_open hg_smooth
      (fun t ht ↦ hVU (hψV t ht)) hψcrit hψdiff hsubset⟩

/--
%%handwave
name:
  Local zero-Hessian critical values admit arbitrarily short covers
statement:
  Near a critical point where the first and second derivatives vanish, the
  corresponding critical values can be covered, for every positive length
  bound, by countably many sets whose total length is at most that bound.
proof:
  Use Taylor's theorem and uniform continuity of the second derivative on a
  sufficiently small closed neighborhood.  A fine square grid covers the
  zero-Hessian critical set, and the oscillation on each selected square is
  \(o(\ell^2)\); the total length of the selected image intervals can
  therefore be made arbitrarily small.
-/
theorem smoothPlaneFunction_zeroSecondDerivativeCriticalValuesOn_nhds_countable_covers_sard
    {g : ℂ → ℝ} {U : Set ℂ} {z : ℂ}
    (hU_open : IsOpen U) (hzU : z ∈ U)
    (_hzcrit : fderiv ℝ g z = 0)
    (_hzzero : PlaneSecondDerivativeZeroAt g z)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ A : ℕ → Set ℝ,
          {c : ℝ | PlaneSecondDerivativeZeroCriticalValueOn g V c} ⊆ ⋃ n : ℕ, A n ∧
            (∑' n : ℕ, MeasureTheory.volume (A n)) ≤ ENNReal.ofReal ε := by
  rcases Metric.mem_nhds_iff.mp (hU_open.mem_nhds hzU) with ⟨r, hr_pos, hr_subset⟩
  let R : ℝ := r / 2
  have hR_pos : 0 < R := by
    dsimp [R]
    positivity
  have hR_lt_r : R < r := by
    dsimp [R]
    linarith
  have hclosedBallU : Metric.closedBall z R ⊆ U :=
    (Metric.closedBall_subset_ball hR_lt_r).trans hr_subset
  refine ⟨Metric.ball z R, Metric.isOpen_ball, Metric.mem_ball_self hR_pos,
    Metric.ball_subset_closedBall.trans hclosedBallU, ?_⟩
  intro ε hε
  let η : ℝ := ε / (128 * (R ^ 2 + 1))
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hη_nonneg : 0 ≤ η := hη_pos.le
  have hε_bound : 64 * η * R ^ 2 ≤ ε := by
    dsimp [η]
    have hden_pos : 0 < 128 * (R ^ 2 + 1) := by positivity
    field_simp [hden_pos.ne']
    nlinarith [sq_nonneg R, hε.le]
  have hK_compact : IsCompact (Metric.closedBall z R) := isCompact_closedBall z R
  rcases smoothPlaneFunction_hessian_uniformly_small_near_zeroHessian_points_sard
      (g := g) (U := U) (K := Metric.closedBall z R)
      hU_open hK_compact hclosedBallU hg_smooth η hη_pos with
    ⟨δ, hδ_pos, hδ⟩
  rcases exists_nat_gt (max (Real.sqrt 2 * (2 * R) / δ) 1 : ℝ) with ⟨M, hMgt⟩
  have hM_gt_one_real : (1 : ℝ) < (M : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hMgt
  have hM_pos : 0 < M := by
    exact_mod_cast (lt_trans zero_lt_one hM_gt_one_real)
  have hMreal_pos : 0 < (M : ℝ) := by exact_mod_cast hM_pos
  have hdiv_lt : Real.sqrt 2 * (2 * R) / δ < (M : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hMgt
  have hnum_lt : Real.sqrt 2 * (2 * R) < (M : ℝ) * δ := by
    have hmul := mul_lt_mul_of_pos_right hdiv_lt hδ_pos
    field_simp [hδ_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hdiam_lt : Real.sqrt 2 * (2 * R / (M : ℝ)) < δ := by
    have hquot : Real.sqrt 2 * (2 * R) / (M : ℝ) < δ := by
      rw [div_lt_iff₀ hMreal_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hnum_lt
    simpa [mul_div_assoc] using hquot
  exact
    smoothPlaneFunction_zeroSecondDerivativeCriticalValuesOn_ball_countable_cover_of_hessian_grid_sard
      (g := g) (U := U) (z := z) (R := R) (η := η) (ε := ε) (M := M)
      hU_open hR_pos hM_pos hclosedBallU hg_smooth hη_nonneg
      (by
        intro p hpK hpzero x hxK hxp_le
        exact le_of_lt (hδ p hpK hpzero x hxK (lt_of_le_of_lt hxp_le hdiam_lt)))
      hε_bound

/--
%%handwave
name:
  Local zero-Hessian critical values have measure zero
statement:
  Near a critical point where the first and second derivatives vanish, the
  critical values attained at such points have one-dimensional Lebesgue
  measure zero.
proof:
  Convert the arbitrarily short countable covers into zero Lebesgue measure.
-/
theorem smoothPlaneFunction_zeroSecondDerivativeCriticalValuesOn_nhds_volume_zero_sard
    {g : ℂ → ℝ} {U : Set ℂ} {z : ℂ}
    (hU_open : IsOpen U) (hzU : z ∈ U)
    (hzcrit : fderiv ℝ g z = 0)
    (hzzero : PlaneSecondDerivativeZeroAt g z)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      MeasureTheory.volume
        {c : ℝ | PlaneSecondDerivativeZeroCriticalValueOn g V c} = 0 := by
  rcases smoothPlaneFunction_zeroSecondDerivativeCriticalValuesOn_nhds_countable_covers_sard
      (g := g) (U := U) (z := z)
      hU_open hzU hzcrit hzzero hg_smooth with
    ⟨V, hV_open, hzV, hVU, hcovers⟩
  exact ⟨V, hV_open, hzV, hVU,
    real_volume_zero_of_countable_covers_with_small_total
      (E := {c : ℝ | PlaneSecondDerivativeZeroCriticalValueOn g V c}) hcovers⟩

/--
%%handwave
name:
  Closed-ball nonzero singular critical values have measure zero
statement:
  For a smooth real-valued function on an open subset of the complex plane,
  the critical values attained on a closed ball at critical points where the
  Hessian is singular but not zero have one-dimensional Lebesgue measure zero.
proof:
  At such a point, some component of the first differential has nonzero
  differential.  The implicit-function theorem puts its zero set in a smooth
  curve.  The critical set is contained in that curve, and the original
  function has zero derivative along the selected critical points.  The
  one-dimensional null-image theorem gives zero length locally, and a Lindelof
  subcover gives the closed-ball result.
-/
theorem smoothPlaneFunction_closedBallNonzeroSingularCriticalValuesOn_volume_zero_sard
    {g : ℂ → ℝ} {U : Set ℂ} (a : ℂ) (r : ℝ)
    (hU_open : IsOpen U) (hball_subset : Metric.closedBall a r ⊆ U)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    MeasureTheory.volume
        {c : ℝ |
          PlaneSecondDerivativeNonzeroSingularCriticalValueOn
            g (Metric.closedBall a r) c} = 0 := by
  classical
  let R : Set ℂ :=
    {z : ℂ | z ∈ Metric.closedBall a r ∧ fderiv ℝ g z = 0 ∧
      PlaneSecondDerivativeDegenerateAt g z ∧
        ¬ PlaneSecondDerivativeZeroAt g z}
  have hR_lindelof : IsLindelof R :=
    HereditarilyLindelofSpace.isLindelof R
  let V : R → Set ℂ := fun x ↦
    Classical.choose
      (smoothPlaneFunction_nonzeroSingularCriticalValuesOn_nhds_volume_zero_sard
        (g := g) (U := U) (z := (x : ℂ)) hU_open
        (hball_subset x.property.1) x.property.2.1 x.property.2.2.1
        x.property.2.2.2 hg_smooth)
  have hV_spec : ∀ x : R, IsOpen (V x) ∧ (x : ℂ) ∈ V x ∧ V x ⊆ U ∧
      MeasureTheory.volume
        {c : ℝ | PlaneSecondDerivativeNonzeroSingularCriticalValueOn g (V x) c} = 0 := by
    intro x
    exact Classical.choose_spec
      (smoothPlaneFunction_nonzeroSingularCriticalValuesOn_nhds_volume_zero_sard
        (g := g) (U := U) (z := (x : ℂ)) hU_open
        (hball_subset x.property.1) x.property.2.1 x.property.2.2.1
        x.property.2.2.2 hg_smooth)
  have hR_cover : R ⊆ ⋃ x : R, V x := by
    intro z hzR
    exact Set.mem_iUnion.mpr ⟨⟨z, hzR⟩, (hV_spec ⟨z, hzR⟩).2.1⟩
  rcases hR_lindelof.elim_countable_subcover V (fun x ↦ (hV_spec x).1) hR_cover with
    ⟨t, ht_countable, ht_cover⟩
  have hsubset :
      {c : ℝ |
        PlaneSecondDerivativeNonzeroSingularCriticalValueOn
          g (Metric.closedBall a r) c} ⊆
        ⋃ x ∈ t, {c : ℝ | PlaneSecondDerivativeNonzeroSingularCriticalValueOn g (V x) c} := by
    intro c hc
    rcases hc with ⟨z, hz_ball, hgz, hzcrit, hzdeg, hzzero⟩
    have hzR : z ∈ R := ⟨hz_ball, hzcrit, hzdeg, hzzero⟩
    have hz_cover : z ∈ ⋃ x ∈ t, V x := ht_cover hzR
    rcases Set.mem_iUnion.mp hz_cover with ⟨x, hx_cover⟩
    rcases Set.mem_iUnion.mp hx_cover with ⟨hxt, hzV⟩
    exact Set.mem_iUnion.mpr
      ⟨x, Set.mem_iUnion.mpr
        ⟨hxt, ⟨z, hzV, hgz, hzcrit, hzdeg, hzzero⟩⟩⟩
  have hunion_zero :
      MeasureTheory.volume
          (⋃ x ∈ t,
            {c : ℝ | PlaneSecondDerivativeNonzeroSingularCriticalValueOn g (V x) c}) = 0 := by
    rw [MeasureTheory.measure_biUnion_null_iff ht_countable]
    intro x _hx
    exact (hV_spec x).2.2.2
  exact MeasureTheory.measure_mono_null hsubset hunion_zero

/--
%%handwave
name:
  Closed-ball zero-Hessian critical values have measure zero
statement:
  For a smooth real-valued function on an open subset of the complex plane,
  the critical values attained on a closed ball at critical points where the
  Hessian vanishes have one-dimensional Lebesgue measure zero.
proof:
  Use uniform Taylor estimates on a slightly larger ball.  On each fine square
  meeting the zero-Hessian critical set, the first-order part and Hessian at a
  selected critical point vanish, while uniform continuity of the Hessian makes
  the remainder \(o(\ell^2)\).  Since only \(O(\ell^{-2})\) squares are needed,
  the total length of the covering intervals tends to zero.
-/
theorem smoothPlaneFunction_closedBallZeroSecondDerivativeCriticalValuesOn_volume_zero_sard
    {g : ℂ → ℝ} {U : Set ℂ} (a : ℂ) (r : ℝ)
    (hU_open : IsOpen U) (hball_subset : Metric.closedBall a r ⊆ U)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    MeasureTheory.volume
        {c : ℝ |
          PlaneSecondDerivativeZeroCriticalValueOn
            g (Metric.closedBall a r) c} = 0 := by
  classical
  let R : Set ℂ :=
    {z : ℂ | z ∈ Metric.closedBall a r ∧ fderiv ℝ g z = 0 ∧
      PlaneSecondDerivativeZeroAt g z}
  have hR_lindelof : IsLindelof R :=
    HereditarilyLindelofSpace.isLindelof R
  let V : R → Set ℂ := fun x ↦
    Classical.choose
      (smoothPlaneFunction_zeroSecondDerivativeCriticalValuesOn_nhds_volume_zero_sard
        (g := g) (U := U) (z := (x : ℂ)) hU_open
        (hball_subset x.property.1) x.property.2.1 x.property.2.2 hg_smooth)
  have hV_spec : ∀ x : R, IsOpen (V x) ∧ (x : ℂ) ∈ V x ∧ V x ⊆ U ∧
      MeasureTheory.volume
        {c : ℝ | PlaneSecondDerivativeZeroCriticalValueOn g (V x) c} = 0 := by
    intro x
    exact Classical.choose_spec
      (smoothPlaneFunction_zeroSecondDerivativeCriticalValuesOn_nhds_volume_zero_sard
        (g := g) (U := U) (z := (x : ℂ)) hU_open
        (hball_subset x.property.1) x.property.2.1 x.property.2.2 hg_smooth)
  have hR_cover : R ⊆ ⋃ x : R, V x := by
    intro z hzR
    exact Set.mem_iUnion.mpr ⟨⟨z, hzR⟩, (hV_spec ⟨z, hzR⟩).2.1⟩
  rcases hR_lindelof.elim_countable_subcover V (fun x ↦ (hV_spec x).1) hR_cover with
    ⟨t, ht_countable, ht_cover⟩
  have hsubset :
      {c : ℝ |
        PlaneSecondDerivativeZeroCriticalValueOn
          g (Metric.closedBall a r) c} ⊆
        ⋃ x ∈ t, {c : ℝ | PlaneSecondDerivativeZeroCriticalValueOn g (V x) c} := by
    intro c hc
    rcases hc with ⟨z, hz_ball, hgz, hzcrit, hzzero⟩
    have hzR : z ∈ R := ⟨hz_ball, hzcrit, hzzero⟩
    have hz_cover : z ∈ ⋃ x ∈ t, V x := ht_cover hzR
    rcases Set.mem_iUnion.mp hz_cover with ⟨x, hx_cover⟩
    rcases Set.mem_iUnion.mp hx_cover with ⟨hxt, hzV⟩
    exact Set.mem_iUnion.mpr
      ⟨x, Set.mem_iUnion.mpr
        ⟨hxt, ⟨z, hzV, hgz, hzcrit, hzzero⟩⟩⟩
  have hunion_zero :
      MeasureTheory.volume
          (⋃ x ∈ t,
            {c : ℝ | PlaneSecondDerivativeZeroCriticalValueOn g (V x) c}) = 0 := by
    rw [MeasureTheory.measure_biUnion_null_iff ht_countable]
    intro x _hx
    exact (hV_spec x).2.2.2
  exact MeasureTheory.measure_mono_null hsubset hunion_zero

/--
%%handwave
name:
  Closed-ball degenerate critical values have measure zero
statement:
  For a smooth real-valued function on an open subset of the complex plane,
  the critical values attained on a closed ball at critical points with
  degenerate second derivative have one-dimensional Lebesgue measure zero.
proof:
  Split the degenerate critical set into the nonzero singular-Hessian part and
  the zero-Hessian part.  The first is controlled by local implicit curves,
  and the second by the square-grid Taylor estimate.
-/
theorem smoothPlaneFunction_closedBallDegenerateCriticalValuesOn_volume_zero_sard
    {g : ℂ → ℝ} {U : Set ℂ} (a : ℂ) (r : ℝ)
    (hU_open : IsOpen U) (hball_subset : Metric.closedBall a r ⊆ U)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    MeasureTheory.volume
        {c : ℝ |
          PlaneSecondDerivativeDegenerateCriticalValueOn
            g (Metric.closedBall a r) c} = 0 := by
  exact
    planeSecondDerivativeDegenerateCriticalValues_volume_zero_of_nonzeroSingular_zero_split
      (g := g) (S := Metric.closedBall a r)
      (smoothPlaneFunction_closedBallNonzeroSingularCriticalValuesOn_volume_zero_sard
        (g := g) (U := U) a r hU_open hball_subset hg_smooth)
      (smoothPlaneFunction_closedBallZeroSecondDerivativeCriticalValuesOn_volume_zero_sard
        (g := g) (U := U) a r hU_open hball_subset hg_smooth)

/--
%%handwave
name:
  Closed-ball local Sard theorem
statement:
  For a smooth real-valued function on an open subset of the complex plane,
  the critical values attained on a closed ball contained in the open set have
  one-dimensional Lebesgue measure zero.
proof:
  This is the local square-grid Sard estimate on a single compact coordinate
  ball.
-/
theorem smoothPlaneFunction_closedBallCriticalValuesOn_volume_zero_sard
    {g : ℂ → ℝ} {U : Set ℂ} (a : ℂ) (r : ℝ)
    (hU_open : IsOpen U) (hball_subset : Metric.closedBall a r ⊆ U)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    MeasureTheory.volume
        {c : ℝ | PlaneCriticalValueOn g (Metric.closedBall a r) c} = 0 := by
  exact planeCriticalValues_volume_zero_of_secondDerivative_split
    (g := g) (S := Metric.closedBall a r)
    (smoothPlaneFunction_closedBallRegularCriticalValuesOn_volume_zero_sard
      (g := g) (U := U) a r hU_open hball_subset hg_smooth)
    (smoothPlaneFunction_closedBallDegenerateCriticalValuesOn_volume_zero_sard
      (g := g) (U := U) a r hU_open hball_subset hg_smooth)

/--
%%handwave
name:
  Compact local Sard theorem
statement:
  For a smooth real-valued function on an open subset of the complex plane,
  the critical values attained on any compact subset contained in the open set
  have one-dimensional Lebesgue measure zero.
proof:
  Cover the compact subset by finitely many small rectangles whose closures
  remain in the open set.  On each rectangle use the two-dimensional local
  Sard estimate: the regular part of the critical set is contained in smooth
  arcs, while the degenerate part is controlled by Taylor estimates on a fine
  square grid.  Finite additivity over the cover gives the result.
-/
theorem smoothPlaneFunction_compactCriticalValuesOn_volume_zero_sard
    {g : ℂ → ℝ} {U K : Set ℂ} (hU_open : IsOpen U)
    (hK_compact : IsCompact K) (hK_subset : K ⊆ U)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    MeasureTheory.volume {c : ℝ | PlaneCriticalValueOn g K c} = 0 := by
  rcases hK_compact.exists_cthickening_subset_open hU_open hK_subset with
    ⟨δ, hδ_pos, hδ_subset_U⟩
  let ε : ℝ := δ / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact half_pos hδ_pos
  have hε_le_delta : ε ≤ δ := by
    dsimp [ε]
    exact half_le_self hδ_pos.le
  rcases finite_cover_balls_of_compact hK_compact hε_pos with
    ⟨t, ht_subset_K, ht_finite, hK_cover⟩
  haveI : Countable t := by
    haveI : Finite t := ht_finite.to_subtype
    infer_instance
  let A : t → Set ℂ := fun x ↦ Metric.closedBall (x : ℂ) ε
  have hcover_closed : K ⊆ ⋃ x : t, A x := by
    intro z hzK
    have hz_cover : z ∈ ⋃ x ∈ t, Metric.ball x ε := hK_cover hzK
    rcases Set.mem_iUnion.mp hz_cover with ⟨x, hx_union⟩
    rcases Set.mem_iUnion.mp hx_union with ⟨hx_t, hz_ball⟩
    exact Set.mem_iUnion.mpr
      ⟨⟨x, hx_t⟩, Metric.ball_subset_closedBall hz_ball⟩
  exact planeCriticalValues_volume_zero_of_iUnion
    (g := g) (S := K) (A := A) hcover_closed (fun x ↦ by
      have hxK : (x : ℂ) ∈ K := ht_subset_K x.property
      have hball_subset_U : Metric.closedBall (x : ℂ) ε ⊆ U := by
        exact ((Metric.closedBall_subset_cthickening hxK ε).trans
          (Metric.cthickening_mono hε_le_delta K)).trans hδ_subset_U
      exact smoothPlaneFunction_closedBallCriticalValuesOn_volume_zero_sard
        (g := g) (U := U) (x : ℂ) ε hU_open hball_subset_U hg_smooth)

/--
%%handwave
name:
  Cushioned bounded local Sard theorem
statement:
  For a smooth real-valued function on an open subset of the complex plane,
  the critical values attained on a bounded subset have zero measure provided
  the subset has a positive metric thickening still contained in the open set.
proof:
  Work on a compact closed thickening of the bounded set.  Smoothness on the
  surrounding open set gives uniform control of the derivatives needed for the
  square-grid proof of the local two-dimensional Sard theorem.
-/
theorem smoothPlaneFunction_cushionedBoundedCriticalValuesOn_volume_zero_sard
    {g : ℂ → ℝ} {U S : Set ℂ} (hU_open : IsOpen U)
    (hS_bounded : Bornology.IsBounded S)
    (hS_cushion : ∃ δ : ℝ, 0 < δ ∧ Metric.thickening δ S ⊆ U)
    (hg_smooth : ContDiffOn ℝ ∞ g U) :
    MeasureTheory.volume {c : ℝ | PlaneCriticalValueOn g S c} = 0 := by
  rcases hS_cushion with ⟨δ, hδ_pos, hδ_subset⟩
  have hclosure_subset_thickening :
      closure S ⊆ Metric.thickening δ S := by
    rw [← Metric.cthickening_zero S]
    exact Metric.cthickening_subset_thickening' hδ_pos hδ_pos S
  have hclosure_subset_U : closure S ⊆ U :=
    hclosure_subset_thickening.trans hδ_subset
  have hclosure_zero :
      MeasureTheory.volume {c : ℝ | PlaneCriticalValueOn g (closure S) c} = 0 :=
    smoothPlaneFunction_compactCriticalValuesOn_volume_zero_sard
      (g := g) (U := U) (K := closure S) hU_open
      hS_bounded.isCompact_closure hclosure_subset_U hg_smooth
  exact MeasureTheory.measure_mono_null
    (planeCriticalValueOn_mono (g := g) (S := S) (T := closure S) subset_closure)
    hclosure_zero

/--
%%handwave
name:
  Bounded cushioned pieces
statement:
  A point belongs to the bounded cushioned piece with indices \(n,m\) if it
  lies in the original set, lies in the centered closed ball of radius \(n\),
  and its closed ball of radius \(1/(m+1)\) is contained in the ambient open
  set.
-/
def sardCushionedPiece (U S : Set ℂ) (i : ℕ × ℕ) : Set ℂ :=
  S ∩ Metric.closedBall (0 : ℂ) (i.1 : ℝ) ∩
    {z : ℂ | Metric.closedBall z (1 / ((i.2 : ℝ) + 1)) ⊆ U}

/--
%%handwave
name:
  Boundedness of cushioned pieces
statement:
  Each bounded cushioned piece lies in a fixed centered closed ball, and hence
  is bounded.
proof:
  The definition places every point of the piece in the centered closed ball
  of radius \(n\).  A subset of this bounded ball is bounded.
-/
theorem sardCushionedPiece_isBounded (U S : Set ℂ) (i : ℕ × ℕ) :
    Bornology.IsBounded (sardCushionedPiece U S i) := by
  exact Metric.isBounded_closedBall.subset (by
    intro z hz
    exact hz.1.2)

/--
%%handwave
name:
  Cushioned pieces have a uniform cushion
statement:
  Each bounded cushioned piece has a positive metric thickening still contained
  in the ambient open set.
proof:
  Put \(r=1/(m+1)>0\) and use the cushion \(r/2\).  If \(y\) lies within
  \(r/2\) of a point \(z\) of the piece, then \(y\in\overline B(z,r)\);
  the defining condition on the piece gives \(\overline B(z,r)\subseteq U\).
-/
theorem sardCushionedPiece_has_cushion (U S : Set ℂ) (i : ℕ × ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.thickening δ (sardCushionedPiece U S i) ⊆ U := by
  let r : ℝ := 1 / ((i.2 : ℝ) + 1)
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  refine ⟨r / 2, half_pos hr_pos, ?_⟩
  intro y hy
  rcases Metric.mem_thickening_iff.mp hy with ⟨z, hz_piece, hyz⟩
  have hz_ball_subset : Metric.closedBall z r ⊆ U := by
    simpa [sardCushionedPiece, r] using hz_piece.2
  exact hz_ball_subset (Metric.mem_closedBall.mpr <|
    le_of_lt (hyz.trans (half_lt_self hr_pos)))

/--
%%handwave
name:
  Countable cover by bounded cushioned pieces
statement:
  Every subset of an open subset of the complex plane is covered by the
  countable family of its bounded cushioned pieces.
proof:
  For a point in the subset, choose a small ball contained in the ambient open
  set and then choose an index \(m\) with \(1/(m+1)\) smaller than that radius.
  A separate index \(n\) places the point in a centered closed ball.
-/
theorem subset_iUnion_sardCushionedPiece {U S : Set ℂ}
    (hU_open : IsOpen U) (hS_subset : S ⊆ U) :
    S ⊆ ⋃ i : ℕ × ℕ, sardCushionedPiece U S i := by
  intro z hzS
  have hzU : z ∈ U := hS_subset hzS
  rcases (Metric.isOpen_iff.mp hU_open) z hzU with
    ⟨ε, hε_pos, hε_subset⟩
  rcases exists_nat_gt (1 / ε - 1 : ℝ) with ⟨m, hm⟩
  have hm' : 1 / ε < (m : ℝ) + 1 := by linarith
  have hm_radius : 1 / ((m : ℝ) + 1) < ε := by
    exact (one_div_lt (Nat.cast_add_one_pos m) hε_pos).mpr hm'
  have hz_union : z ∈ ⋃ n : ℕ, Metric.closedBall (0 : ℂ) (n : ℝ) := by
    rw [Metric.iUnion_closedBall_nat]
    exact Set.mem_univ z
  rcases Set.mem_iUnion.mp hz_union with ⟨n, hzn⟩
  refine Set.mem_iUnion.mpr ⟨(n, m), ?_⟩
  refine ⟨⟨hzS, hzn⟩, ?_⟩
  exact (Metric.closedBall_subset_ball hm_radius).trans hε_subset

/--
%%handwave
name:
  Local Sard theorem for bounded plane critical values
statement:
  For a smooth real-valued function on an open subset of the complex plane,
  the set of critical values attained on any bounded subset has
  one-dimensional Lebesgue measure zero.
proof:
  Reduce to compact rectangles contained in coordinate balls and cover the
  critical set by small squares.  At nondegenerate Hessian points, the inverse
  function theorem gives the local regular-value estimate.  Singular Hessian
  points split further into nonzero singular points, controlled by implicit
  curves, and zero-Hessian points, controlled by Taylor's theorem with a
  uniform third-order remainder.  Summing over a grid and then letting the
  grid size tend to zero gives zero one-dimensional measure for the critical
  values on each bounded piece.
-/
theorem smoothPlaneFunction_boundedCriticalValuesOn_volume_zero_sard
    {g : ℂ → ℝ} {U S : Set ℂ} (_hU_open : IsOpen U)
    (_hS_subset : S ⊆ U) (_hS_bounded : Bornology.IsBounded S)
    (_hg_smooth : ContDiffOn ℝ ∞ g U) :
    MeasureTheory.volume {c : ℝ | PlaneCriticalValueOn g S c} = 0 := by
  let A : ℕ × ℕ → Set ℂ := sardCushionedPiece U S
  have hcover : S ⊆ ⋃ i : ℕ × ℕ, A i := by
    simpa [A] using
      subset_iUnion_sardCushionedPiece
        (U := U) (S := S) _hU_open _hS_subset
  exact planeCriticalValues_volume_zero_of_iUnion
    (g := g) (S := S) (A := A) hcover (fun i ↦
      smoothPlaneFunction_cushionedBoundedCriticalValuesOn_volume_zero_sard
        (g := g) (U := U) (S := A i) _hU_open
        (sardCushionedPiece_isBounded U S i)
        (sardCushionedPiece_has_cushion U S i) _hg_smooth)

end Uniformization

end JJMath
