import JJMath.Analysis.Sobolev.Basic

/-!
# Dirichlet capacity for zero-trace Sobolev functions on surfaces

This file records the homogeneous Dirichlet seminorm, positive capacity at
infinity, and the truncation lemmas used to turn failure of local control into
capacity competitors.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff

namespace Uniformization

noncomputable section

/--
%%handwave
name:
  Global Dirichlet seminorm
statement:
  The global Dirichlet seminorm of a zero-trace Sobolev function is the
  integral of the background cotangent norm squared of its weak gradient.
-/
noncomputable def greenDirichletSeminormSq {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X)
    (u : SobolevH1ZeroOnSurface g.volume) : ℝ :=
  ∫ x, g.gradientInner x (u.weakGradient x) (u.weakGradient x) ∂g.volume

/--
%%handwave
name:
  Dirichlet seminorm is nonnegative
statement:
  The Dirichlet seminorm squared is nonnegative.
proof:
  The background metric gives a nonnegative pointwise cotangent norm squared.
  Integrating this nonnegative function gives a nonnegative number.
-/
theorem greenDirichletSeminormSq_nonneg {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X)
    (u : SobolevH1ZeroOnSurface g.volume) :
    0 ≤ greenDirichletSeminormSq g u := by
  dsimp [greenDirichletSeminormSq]
  exact integral_nonneg (fun x ↦ g.gradientInner_nonneg x (u.weakGradient x))

/--
%%handwave
name:
  Local \(L^2\) seminorm on a compact set
statement:
  The local \(L^2\) seminorm squared of a zero-trace Sobolev function on a
  compact set is the integral of \(h^2\) over that compact set.
-/
noncomputable def greenLocalL2SeminormSq {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) (K : Set X)
    (h : SobolevH1ZeroOnSurface g.volume) : ℝ :=
  ∫ x in K, h x ^ 2 ∂g.volume

/--
%%handwave
name:
  Local \(L^2\) seminorm is nonnegative
statement:
  The local \(L^2\) seminorm squared of a zero-trace Sobolev function on a set
  is nonnegative.
proof:
  The integrand is the square of a real-valued function, hence is pointwise
  nonnegative.
-/
theorem greenLocalL2SeminormSq_nonneg {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) (K : Set X)
    (h : SobolevH1ZeroOnSurface g.volume) :
    0 ≤ greenLocalL2SeminormSq g K h := by
  dsimp [greenLocalL2SeminormSq]
  exact integral_nonneg (fun x ↦ sq_nonneg (h x))

/--
%%handwave
name:
  Positive capacity at infinity
statement:
  A background metric has positive capacity at infinity if every compact set
  of positive area has a positive Dirichlet-energy capacity: zero-trace
  Sobolev functions which are at least one on that compact set have Dirichlet
  energy bounded below by a positive constant.
-/
def HasPositiveCapacityAtInfinity {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) : Prop :=
  ∀ K : Set X, IsCompact K → 0 < g.volume K →
    ∃ c : ℝ, 0 < c ∧
      ∀ u : SobolevH1ZeroOnSurface g.volume,
        (∀ x ∈ K, 1 ≤ u x) →
          c ≤ greenDirichletSeminormSq g u

/--
%%handwave
name:
  Failure of local Poincare gives a bad test function
statement:
  If no constant controls the local \(L^2\) norm on a compact set by the
  Dirichlet norm, then every proposed constant is beaten by some zero-trace
  Sobolev function.
proof:
  This is the negation of the desired estimate.  If a nonnegative proposed
  constant were not beaten by any test function, it would itself give the
  missing local Poincare inequality.
-/
theorem exists_bad_localL2_test_of_no_localL2_control
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (K : Set X)
    (hfail : ¬ ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      greenLocalL2SeminormSq g K h ≤ P * greenDirichletSeminormSq g h)
    (P : ℝ) (hP : 0 ≤ P) :
    ∃ h : SobolevH1ZeroOnSurface g.volume,
      P * greenDirichletSeminormSq g h < greenLocalL2SeminormSq g K h := by
  by_contra hno_test
  apply hfail
  refine ⟨P, hP, ?_⟩
  intro h
  exact not_lt.mp (fun hlt ↦ hno_test ⟨h, hlt⟩)

/--
%%handwave
name:
  Failure of local Poincare gives a bad sequence
statement:
  If no constant controls the local \(L^2\) norm on a compact set by the
  Dirichlet norm, then there is a sequence of zero-trace Sobolev functions for
  which the local \(L^2\) mass dominates the Dirichlet energy by factors
  tending to infinity.
proof:
  Apply the previous observation to the constants \(0,1,2,\ldots\), and choose
  one function for each constant.
-/
theorem exists_bad_localL2_sequence_of_no_localL2_control
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (K : Set X)
    (hfail : ¬ ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      greenLocalL2SeminormSq g K h ≤ P * greenDirichletSeminormSq g h) :
    ∃ H : ℕ → SobolevH1ZeroOnSurface g.volume,
      ∀ n : ℕ,
        (n : ℝ) * greenDirichletSeminormSq g (H n) <
          greenLocalL2SeminormSq g K (H n) := by
  choose H hH using fun n : ℕ ↦
    exists_bad_localL2_test_of_no_localL2_control
      K hfail (n : ℝ) (Nat.cast_nonneg n)
  exact ⟨H, hH⟩

/--
%%handwave
name:
  Failure of finite-energy local control gives a bad test function
statement:
  If no constant controls the local \(L^2\) norm by the Dirichlet norm among
  zero-trace Sobolev functions with integrable gradient energy, then every
  proposed nonnegative constant is beaten by such a finite-energy function.
proof:
  This is the negation of the restricted estimate.  If no finite-energy test
  beat a proposed constant, that constant would give the missing restricted
  estimate.
-/
theorem exists_bad_localL2_test_of_no_localL2_control_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (K : Set X)
    (hfail : ¬ ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      Integrable
        (fun x : X ↦
          g.gradientInner x (h.weakGradient x) (h.weakGradient x))
        g.volume →
        greenLocalL2SeminormSq g K h ≤ P * greenDirichletSeminormSq g h)
    (P : ℝ) (hP : 0 ≤ P) :
    ∃ h : SobolevH1ZeroOnSurface g.volume,
      Integrable
        (fun x : X ↦
          g.gradientInner x (h.weakGradient x) (h.weakGradient x))
        g.volume ∧
      P * greenDirichletSeminormSq g h < greenLocalL2SeminormSq g K h := by
  by_contra hno_test
  apply hfail
  refine ⟨P, hP, ?_⟩
  intro h hInt
  exact not_lt.mp (fun hlt ↦ hno_test ⟨h, hInt, hlt⟩)

/--
%%handwave
name:
  Failure of finite-energy local control gives a bad sequence
statement:
  If local \(L^2\)-Dirichlet control fails among finite-energy zero-trace
  Sobolev functions, then there is a finite-energy bad sequence whose local
  \(L^2\) mass dominates its Dirichlet energy by factors tending to infinity.
proof:
  Apply the finite-energy bad-test lemma to the proposed constants
  \(0,1,2,\ldots\), and choose one function for each constant.
-/
theorem exists_bad_localL2_sequence_of_no_localL2_control_of_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (K : Set X)
    (hfail : ¬ ∃ P : ℝ, 0 ≤ P ∧ ∀ h : SobolevH1ZeroOnSurface g.volume,
      Integrable
        (fun x : X ↦
          g.gradientInner x (h.weakGradient x) (h.weakGradient x))
        g.volume →
        greenLocalL2SeminormSq g K h ≤ P * greenDirichletSeminormSq g h) :
    ∃ H : ℕ → SobolevH1ZeroOnSurface g.volume,
      (∀ n : ℕ,
        Integrable
          (fun x : X ↦
            g.gradientInner x ((H n).weakGradient x) ((H n).weakGradient x))
          g.volume) ∧
      ∀ n : ℕ,
        (n : ℝ) * greenDirichletSeminormSq g (H n) <
          greenLocalL2SeminormSq g K (H n) := by
  choose H hH using fun n : ℕ ↦
    exists_bad_localL2_test_of_no_localL2_control_of_integrable
      K hfail (n : ℝ) (Nat.cast_nonneg n)
  refine ⟨H, ?_, ?_⟩
  · intro n
    exact (hH n).1
  · intro n
    exact (hH n).2

/--
%%handwave
name:
  Domination makes the local \(L^2\) mass positive
statement:
  If the local \(L^2\) mass of a zero-trace Sobolev function dominates its
  Dirichlet energy by a positive inverse factor, then that local \(L^2\) mass
  is positive.
proof:
  The Dirichlet energy is nonnegative, and the inverse factor is nonnegative.
  Hence the left-hand side of the domination inequality is nonnegative, so the
  right-hand side is strictly positive.
-/
theorem greenLocalL2SeminormSq_pos_of_localL2_dominates_inv
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (K : Set X) (h : SobolevH1ZeroOnSurface g.volume)
    (ε : ℝ) (hε : 0 < ε)
    (hdominates :
      ε⁻¹ * greenDirichletSeminormSq g h < greenLocalL2SeminormSq g K h) :
    0 < greenLocalL2SeminormSq g K h := by
  have hD_nonneg : 0 ≤ greenDirichletSeminormSq g h :=
    greenDirichletSeminormSq_nonneg g h
  have hinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
  exact lt_of_le_of_lt (mul_nonneg hinv_nonneg hD_nonneg) hdominates

/--
%%handwave
name:
  Domination gives the normalized Dirichlet bound
statement:
  If the local \(L^2\) mass of a zero-trace Sobolev function dominates its
  Dirichlet energy by the factor \(\varepsilon^{-1}\), then the Dirichlet
  energy is less than \(\varepsilon\) times that local \(L^2\) mass.
proof:
  Multiply the domination inequality by the positive number \(\varepsilon\).
-/
theorem greenDirichletSeminormSq_lt_mul_localL2_of_localL2_dominates_inv
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (K : Set X) (h : SobolevH1ZeroOnSurface g.volume)
    (ε : ℝ) (hε : 0 < ε)
    (hdominates :
      ε⁻¹ * greenDirichletSeminormSq g h < greenLocalL2SeminormSq g K h) :
    greenDirichletSeminormSq g h <
      ε * greenLocalL2SeminormSq g K h := by
  have hmul :
      ε * (ε⁻¹ * greenDirichletSeminormSq g h) <
        ε * greenLocalL2SeminormSq g K h :=
    mul_lt_mul_of_pos_left hdominates hε
  calc
    greenDirichletSeminormSq g h
        = ε * (ε⁻¹ * greenDirichletSeminormSq g h) := by
          rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
    _ < ε * greenLocalL2SeminormSq g K h := hmul

/--
%%handwave
name:
  Positive measurable area contains positive compact area
statement:
  For an inner-regular measure, every measurable finite-area set of positive
  area contains a compact subset of positive area.
proof:
  Apply inner regularity with the comparison value \(0\).
-/
theorem exists_compact_subset_pos_measure_of_measurable_pos_measure
    {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [Measure.InnerRegularCompactLTTop μ]
    {A : Set X} (hA_meas : MeasurableSet A) (hA_ne_top : μ A ≠ (∞ : ℝ≥0∞))
    (hA_pos : 0 < μ A) :
    ∃ L : Set X, IsCompact L ∧ L ⊆ A ∧ 0 < μ L := by
  rcases hA_meas.exists_lt_isCompact_of_ne_top hA_ne_top hA_pos with
    ⟨L, hLA, hL_compact, hL_pos⟩
  exact ⟨L, hL_compact, hLA, hL_pos⟩

end

end Uniformization

end JJMath
