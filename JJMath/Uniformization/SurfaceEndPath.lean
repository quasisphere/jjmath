import JJMath.Uniformization.SimplyConnectedExhaustion
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.ContinuousMap.Interval

/-!
# Nested exterior components along a smooth exhaustion

An exterior component of the complement of a compact set determines an end.
Along a smooth relatively compact exhaustion, that end can be represented by
a nested sequence of exterior complementary components.  This is the compact
escape data used in the construction of a proper ray.
-/

open Set
open scoped Manifold Topology ContDiff

namespace JJMath.Uniformization

noncomputable section

/-! ## Gluing a countable chain of paths -/

/-! ## Proper-ray gluing -/

/--
%%handwave
name:
  Nested exterior components along an exhaustion
statement:
  Let \(V\) be an exterior component of \(X\setminus K\), with \(K\) compact.
  Along a smooth relatively compact exhaustion there are an index \(N\) and
  exterior components \(U_n\) of
  \(X\setminus\overline{E_{N+n}}\) such that
  \[
    K\subseteq\overline{E_N},\qquad U_0\subseteq V,
    \qquad U_{n+1}\subseteq U_n.
  \]
proof:
  Choose \(N\) containing \(K\).  Finiteness of complementary components at
  each compact exhaustion level lets one choose an exterior component nested
  inside the preceding one; define the sequence recursively.
-/
theorem IsExteriorComponent.exists_nested_sequence_along_smoothExhaustion
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X)
    {K V : Set X} (hKcompact : IsCompact K)
    (hV : IsExteriorComponent K V) :
    ∃ (N : ℕ) (U : ℕ → Set X),
      K ⊆ closure (E.domain N).carrier ∧
      (∀ n : ℕ,
        IsExteriorComponent
          (closure (E.domain (N + n)).carrier) (U n)) ∧
      U 0 ⊆ V ∧
      ∀ n : ℕ, U (n + 1) ⊆ U n := by
  classical
  rcases smoothRelativelyCompactExhaustion_compact_subset_domain E hKcompact with
    ⟨N, hKN⟩
  let obstacle : ℕ → Set X :=
    fun n => closure (E.domain (N + n)).carrier
  have hobstacle_compact : ∀ n : ℕ, IsCompact (obstacle n) := by
    intro n
    exact (E.domain (N + n)).compact_closure
  have hobstacle_mono : ∀ n : ℕ, obstacle n ⊆ obstacle (n + 1) := by
    intro n x hx
    apply subset_closure
    simpa [obstacle, Nat.add_assoc] using
      E.closure_subset_next (N + n) hx
  have hobstacle_components_finite :
      ∀ n : ℕ,
        {W : Set X | IsComponentOf W (obstacle n)ᶜ}.Finite := by
    intro n
    simpa [obstacle] using
      smoothBoundaryDomain_complement_components_finite (E.domain (N + n))
  have hK_obstacle : K ⊆ obstacle 0 := by
    intro x hx
    exact subset_closure (hKN hx)
  rcases hV.exists_nested_of_subset_left_of_finite_components
      hK_obstacle (hobstacle_compact 0)
      (hobstacle_components_finite 0) with
    ⟨U0, hU0exterior, hU0V⟩
  let State : ℕ → Type :=
    fun n => {W : Set X // IsExteriorComponent (obstacle n) W}
  let next : (n : ℕ) → State n → State (n + 1) :=
    fun n W =>
      ⟨Classical.choose
          (W.property.exists_nested_of_subset_left_of_finite_components
            (hobstacle_mono n) (hobstacle_compact (n + 1))
            (hobstacle_components_finite (n + 1))),
        (Classical.choose_spec
          (W.property.exists_nested_of_subset_left_of_finite_components
            (hobstacle_mono n) (hobstacle_compact (n + 1))
            (hobstacle_components_finite (n + 1)))).1⟩
  let states : (n : ℕ) → State n :=
    fun n => Nat.rec (motive := State) ⟨U0, hU0exterior⟩ next n
  let U : ℕ → Set X := fun n => states n
  refine ⟨N, U, ?_, ?_, ?_, ?_⟩
  · simpa [obstacle] using hK_obstacle
  · intro n
    exact (states n).property
  · simpa [U, states] using hU0V
  · intro n
    have hspec :=
      Classical.choose_spec
        ((states n).property.exists_nested_of_subset_left_of_finite_components
          (hobstacle_mono n) (hobstacle_compact (n + 1))
          (hobstacle_components_finite (n + 1)))
    exact hspec.2

/--
%%handwave
name:
  An escaping path chain through nested exterior components
statement:
  The nested exterior components \(U_n\) can be equipped with points
  \(x_n\in U_n\) and paths \(\gamma_n:x_n\leadsto x_{n+1}\) contained in \(U_n\).
  Every later path \(\gamma_m\), \(m\ge n\), avoids
  \(\overline{E_{N+n}}\).
proof:
  Choose one point in each nonempty exterior component.  Surface exterior
  components are path connected, and nesting places both successive points in
  \(U_n\).  Antitonicity then puts each later path in \(U_n\), which is
  disjoint from the corresponding compact obstacle.
-/
theorem IsExteriorComponent.exists_escaping_path_chain_along_smoothExhaustion
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X)
    {K V : Set X} (hKcompact : IsCompact K)
    (hV : IsExteriorComponent K V) :
    ∃ (N : ℕ) (U : ℕ → Set X) (x : ℕ → X)
        (gamma : ∀ n : ℕ, Path (x n) (x (n + 1))),
      K ⊆ closure (E.domain N).carrier ∧
      (∀ n : ℕ,
        IsExteriorComponent
          (closure (E.domain (N + n)).carrier) (U n)) ∧
      U 0 ⊆ V ∧
      Antitone U ∧
      (∀ n : ℕ, x n ∈ U n) ∧
      (∀ n : ℕ, ∀ t : unitInterval, gamma n t ∈ U n) ∧
      (∀ n m : ℕ, n ≤ m → ∀ t : unitInterval,
        gamma m t ∉ closure (E.domain (N + n)).carrier) := by
  classical
  rcases hV.exists_nested_sequence_along_smoothExhaustion E hKcompact with
    ⟨N, U, hK, hUexterior, hU0V, hUsucc⟩
  have hUanti : Antitone U := antitone_nat_of_succ_le hUsucc
  let x : ℕ → X := fun n =>
    Classical.choose (hUexterior n).nonempty
  have hx : ∀ n : ℕ, x n ∈ U n := by
    intro n
    exact Classical.choose_spec (hUexterior n).nonempty
  have hjoined : ∀ n : ℕ, JoinedIn (U n) (x n) (x (n + 1)) := by
    intro n
    have hpathConnected : IsPathConnected (U n) :=
      (hUexterior n).isComponentOf.isPathConnected_of_compl_isClosed
        isClosed_closure
    exact hpathConnected.joinedIn (x n) (hx n) (x (n + 1))
      (hUanti (Nat.le_succ n) (hx (n + 1)))
  let gamma : ∀ n : ℕ, Path (x n) (x (n + 1)) :=
    fun n => (hjoined n).somePath
  refine ⟨N, U, x, gamma, hK, hUexterior, hU0V, hUanti, hx, ?_, ?_⟩
  · intro n t
    exact (hjoined n).somePath_mem t
  · intro n m hnm t hmem
    have hgammaUm : gamma m t ∈ U m :=
      (hjoined m).somePath_mem t
    have hgammaUn : gamma m t ∈ U n := hUanti hnm hgammaUm
    exact (hUexterior n).subset_compl hgammaUn hmem

end

end JJMath.Uniformization
