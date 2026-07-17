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

/-- An open time interval on which the `n`-th path in a path chain is used.
The extra quarter-unit at each end is where the extended path is constant. -/
def pathChainPatch (n : ℕ) : Set NNReal :=
  {t | (n : ℝ) - 1 / 4 < (t : ℝ) ∧
    (t : ℝ) < (n : ℝ) + 5 / 4}

theorem isOpen_pathChainPatch (n : ℕ) : IsOpen (pathChainPatch n) := by
  change IsOpen
    ({t : NNReal | (n : ℝ) - 1 / 4 < (t : ℝ)} ∩
      {t : NNReal | (t : ℝ) < (n : ℝ) + 5 / 4})
  exact
    (isOpen_lt continuous_const NNReal.continuous_coe).inter
      (isOpen_lt NNReal.continuous_coe continuous_const)

/-- The local representative of a path chain on its `n`-th time patch. -/
def pathChainLocalMap
    {X : Type} [TopologicalSpace X]
    (x : ℕ → X) (gamma : ∀ n : ℕ, Path (x n) (x (n + 1)))
    (n : ℕ) : C(pathChainPatch n, X) where
  toFun t :=
    (gamma n).extend
      (2 * ((t.1 : ℝ) - (n : ℝ)) - 1 / 2)
  continuous_toFun := by
    fun_prop

theorem pathChainLocalMap_agree
    {X : Type} [TopologicalSpace X]
    (x : ℕ → X) (gamma : ∀ n : ℕ, Path (x n) (x (n + 1)))
    (i j : ℕ) (t : NNReal)
    (hti : t ∈ pathChainPatch i) (htj : t ∈ pathChainPatch j) :
    pathChainLocalMap x gamma i ⟨t, hti⟩ =
      pathChainLocalMap x gamma j ⟨t, htj⟩ := by
  have adjacent_of_lt (hij : i < j) : j = i + 1 := by
    have hlt : j < i + 2 := by
      by_contra hnot
      have hle : i + 2 ≤ j := Nat.le_of_not_gt hnot
      have hle' : (i : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hle
      dsimp [pathChainPatch] at hti htj
      linarith [hti.2, htj.1]
    omega
  have adjacent_of_gt (hji : j < i) : i = j + 1 := by
    have hlt : i < j + 2 := by
      by_contra hnot
      have hle : j + 2 ≤ i := Nat.le_of_not_gt hnot
      have hle' : (j : ℝ) + 2 ≤ (i : ℝ) := by exact_mod_cast hle
      dsimp [pathChainPatch] at hti htj
      linarith [htj.2, hti.1]
    omega
  rcases lt_trichotomy i j with hij | hij | hij
  · have hji : j = i + 1 := adjacent_of_lt hij
    subst j
    have hleft : 1 ≤ 2 * ((t : ℝ) - (i : ℝ)) - 1 / 2 := by
      dsimp [pathChainPatch] at hti htj
      push_cast at htj
      linarith [htj.1]
    have hright :
        2 * ((t : ℝ) - ((i + 1 : ℕ) : ℝ)) - 1 / 2 ≤ 0 := by
      dsimp [pathChainPatch] at hti htj
      push_cast
      linarith [hti.2]
    change
      (gamma i).extend (2 * ((t : ℝ) - (i : ℝ)) - 1 / 2) =
        (gamma (i + 1)).extend
          (2 * ((t : ℝ) - ((i + 1 : ℕ) : ℝ)) - 1 / 2)
    rw [(gamma i).extend_of_one_le hleft,
      (gamma (i + 1)).extend_of_le_zero hright]
  · subst j
    rfl
  · have hij' : i = j + 1 := adjacent_of_gt hij
    subst i
    have hleft :
        2 * ((t : ℝ) - ((j + 1 : ℕ) : ℝ)) - 1 / 2 ≤ 0 := by
      dsimp [pathChainPatch] at hti htj
      push_cast
      linarith [htj.2]
    have hright : 1 ≤ 2 * ((t : ℝ) - (j : ℝ)) - 1 / 2 := by
      dsimp [pathChainPatch] at hti htj
      push_cast at hti
      linarith [hti.1]
    change
      (gamma (j + 1)).extend
          (2 * ((t : ℝ) - ((j + 1 : ℕ) : ℝ)) - 1 / 2) =
        (gamma j).extend (2 * ((t : ℝ) - (j : ℝ)) - 1 / 2)
    rw [(gamma (j + 1)).extend_of_le_zero hleft,
      (gamma j).extend_of_one_le hright]

theorem pathChainPatch_mem_nhds (t : NNReal) :
    pathChainPatch ⌊(t : ℝ)⌋₊ ∈ 𝓝 t := by
  apply (isOpen_pathChainPatch ⌊(t : ℝ)⌋₊).mem_nhds
  have hfloor : (⌊(t : ℝ)⌋₊ : ℝ) ≤ (t : ℝ) :=
    Nat.floor_le (NNReal.coe_nonneg t)
  have hnext : (t : ℝ) < (⌊(t : ℝ)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one (t : ℝ)
  constructor <;> dsimp [pathChainPatch] <;> linarith

theorem pathChainPatch_cover (t : NNReal) :
    ∃ n : ℕ, pathChainPatch n ∈ 𝓝 t :=
  ⟨⌊(t : ℝ)⌋₊, pathChainPatch_mem_nhds t⟩

/-- A countable chain of composable paths, glued into one continuous ray. -/
noncomputable def pathChainRay
    {X : Type} [TopologicalSpace X]
    (x : ℕ → X) (gamma : ∀ n : ℕ, Path (x n) (x (n + 1))) :
    C(NNReal, X) :=
  ContinuousMap.liftCover pathChainPatch (pathChainLocalMap x gamma)
    (pathChainLocalMap_agree x gamma)
    pathChainPatch_cover

theorem pathChainRay_apply_floor
    {X : Type} [TopologicalSpace X]
    (x : ℕ → X) (gamma : ∀ n : ℕ, Path (x n) (x (n + 1)))
    (t : NNReal) :
    pathChainRay x gamma t =
      pathChainLocalMap x gamma ⌊(t : ℝ)⌋₊
        ⟨t, mem_of_mem_nhds (pathChainPatch_mem_nhds t)⟩ := by
  unfold pathChainRay
  convert
    (ContinuousMap.liftCover_coe
      (S := pathChainPatch) (φ := pathChainLocalMap x gamma)
      (hφ := pathChainLocalMap_agree x gamma)
      (hS := pathChainPatch_cover)
      ⟨t, mem_of_mem_nhds (pathChainPatch_mem_nhds t)⟩) using 1

theorem pathChainLocalMap_mem
    {X : Type} [TopologicalSpace X]
    {U : ℕ → Set X} (x : ℕ → X)
    (gamma : ∀ n : ℕ, Path (x n) (x (n + 1)))
    (hgamma : ∀ n : ℕ, ∀ s : unitInterval, gamma n s ∈ U n)
    (n : ℕ) (t : pathChainPatch n) :
    pathChainLocalMap x gamma n t ∈ U n := by
  have hrange :
      pathChainLocalMap x gamma n t ∈ Set.range (gamma n) := by
    rw [← (gamma n).extend_range]
    exact ⟨2 * ((t.1 : ℝ) - (n : ℝ)) - 1 / 2, rfl⟩
  rcases hrange with ⟨s, hs⟩
  rw [← hs]
  exact hgamma n s

theorem pathChainRay_mem_floor
    {X : Type} [TopologicalSpace X]
    {U : ℕ → Set X} (x : ℕ → X)
    (gamma : ∀ n : ℕ, Path (x n) (x (n + 1)))
    (hgamma : ∀ n : ℕ, ∀ s : unitInterval, gamma n s ∈ U n)
    (t : NNReal) :
    pathChainRay x gamma t ∈ U ⌊(t : ℝ)⌋₊ := by
  rw [pathChainRay_apply_floor]
  exact pathChainLocalMap_mem x gamma hgamma _ _

theorem pathChainRay_mem_of_le
    {X : Type} [TopologicalSpace X]
    {U : ℕ → Set X} (x : ℕ → X)
    (gamma : ∀ n : ℕ, Path (x n) (x (n + 1)))
    (hU : Antitone U)
    (hgamma : ∀ n : ℕ, ∀ s : unitInterval, gamma n s ∈ U n)
    (n : ℕ) (t : NNReal) (hnt : (n : ℝ) ≤ (t : ℝ)) :
    pathChainRay x gamma t ∈ U n := by
  apply hU (Nat.le_floor hnt)
  exact pathChainRay_mem_floor x gamma hgamma t

/-! ## Proper-ray gluing -/

/-- Prepend a compact path to a ray.  The path is traversed during the first
half-unit of time; the original ray then starts at time one half. -/
noncomputable def pathPrependRay
    {X : Type} [TopologicalSpace X] {a : X}
    (r : C(NNReal, X)) (p : Path a (r 0)) : C(NNReal, X) where
  toFun t :=
    if t ≤ (1 / 2 : NNReal) then
      p.extend (2 * (t : ℝ))
    else
      r (t - (1 / 2 : NNReal))
  continuous_toFun := by
    apply Continuous.if_le
    · fun_prop
    · fun_prop
    · exact continuous_id
    · exact continuous_const
    · intro t ht
      subst t
      simp

theorem pathPrependRay_zero
    {X : Type} [TopologicalSpace X] {a : X}
    (r : C(NNReal, X)) (p : Path a (r 0)) :
    pathPrependRay r p 0 = a := by
  simp [pathPrependRay]

/-- Prepending a compact path preserves properness of a ray. -/
theorem isProperMap_pathPrependRay
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactlyCoherentSpace X]
    {a : X} (r : C(NNReal, X)) (p : Path a (r 0))
    (hr : IsProperMap r) :
    IsProperMap (pathPrependRay r p) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨(pathPrependRay r p).continuous, ?_⟩
  intro C hC
  have hr_compact : IsCompact (r ⁻¹' C) :=
    (isProperMap_iff_isCompact_preimage.mp hr).2 hC
  let h : NNReal := 1 / 2
  have hIic : IsCompact (Set.Iic h) := by
    rw [show Set.Iic h = Set.Icc 0 h by
      ext t
      simp]
    exact isCompact_Icc
  have hshift : IsCompact ((fun s : NNReal => s + h) '' (r ⁻¹' C)) :=
    hr_compact.image (by fun_prop)
  have hunion :
      IsCompact (Set.Iic h ∪ ((fun s : NNReal => s + h) '' (r ⁻¹' C))) :=
    hIic.union hshift
  have hpre_closed : IsClosed ((pathPrependRay r p) ⁻¹' C) :=
    hC.isClosed.preimage (pathPrependRay r p).continuous
  apply hunion.of_isClosed_subset hpre_closed
  intro t htC
  by_cases ht : t ≤ h
  · exact Or.inl ht
  · apply Or.inr
    have hle : h ≤ t := le_of_not_ge ht
    refine ⟨t - h, ?_, ?_⟩
    · have ht' : ¬ t ≤ (1 / 2 : NNReal) := by simpa [h] using ht
      change
        (if t ≤ (1 / 2 : NNReal) then
          p.extend (2 * (t : ℝ))
        else
          r (t - (1 / 2 : NNReal))) ∈ C at htC
      rw [if_neg ht'] at htC
      simpa [h] using htC
    · exact (tsub_add_cancel_of_le hle)

/-- Glue two rays with a common initial point, reversing the first one, to
obtain a continuous map from the real line. -/
noncomputable def twoRaysLine
    {X : Type} [TopologicalSpace X]
    (rneg rpos : C(NNReal, X)) (hstart : rneg 0 = rpos 0) : C(ℝ, X) where
  toFun t :=
    if t ≤ 0 then
      rneg (-t).toNNReal
    else
      rpos t.toNNReal
  continuous_toFun := by
    apply Continuous.if_le
    · fun_prop
    · fun_prop
    · exact continuous_id
    · exact continuous_const
    · intro t ht
      subst t
      simpa using hstart

@[simp]
theorem twoRaysLine_zero
    {X : Type} [TopologicalSpace X]
    (rneg rpos : C(NNReal, X)) (hstart : rneg 0 = rpos 0) :
    twoRaysLine rneg rpos hstart 0 = rneg 0 := by
  simp [twoRaysLine]

/-- Gluing two proper rays at their common initial point gives a proper map
from the real line. -/
theorem isProperMap_twoRaysLine
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactlyCoherentSpace X]
    (rneg rpos : C(NNReal, X)) (hstart : rneg 0 = rpos 0)
    (hneg : IsProperMap rneg) (hpos : IsProperMap rpos) :
    IsProperMap (twoRaysLine rneg rpos hstart) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨(twoRaysLine rneg rpos hstart).continuous, ?_⟩
  intro C hC
  have hneg_compact : IsCompact (rneg ⁻¹' C) :=
    (isProperMap_iff_isCompact_preimage.mp hneg).2 hC
  have hpos_compact : IsCompact (rpos ⁻¹' C) :=
    (isProperMap_iff_isCompact_preimage.mp hpos).2 hC
  let negTime : NNReal → ℝ := fun s => -(s : ℝ)
  let posTime : NNReal → ℝ := fun s => (s : ℝ)
  have hneg_image : IsCompact (negTime '' (rneg ⁻¹' C)) :=
    hneg_compact.image (by fun_prop)
  have hpos_image : IsCompact (posTime '' (rpos ⁻¹' C)) :=
    hpos_compact.image (by fun_prop)
  have hunion :
      IsCompact (negTime '' (rneg ⁻¹' C) ∪ posTime '' (rpos ⁻¹' C)) :=
    hneg_image.union hpos_image
  have hpre_closed : IsClosed ((twoRaysLine rneg rpos hstart) ⁻¹' C) :=
    hC.isClosed.preimage (twoRaysLine rneg rpos hstart).continuous
  apply hunion.of_isClosed_subset hpre_closed
  intro t htC
  by_cases ht : t ≤ 0
  · apply Or.inl
    refine ⟨(-t).toNNReal, ?_, ?_⟩
    · change rneg (-t).toNNReal ∈ C
      simpa [twoRaysLine, ht] using htC
    · dsimp [negTime]
      rw [max_eq_left (neg_nonneg.mpr ht)]
      ring
  · apply Or.inr
    have htpos : 0 ≤ t := (lt_of_not_ge ht).le
    refine ⟨t.toNNReal, ?_, ?_⟩
    · change rpos t.toNNReal ∈ C
      simpa [twoRaysLine, ht] using htC
    · dsimp [posTime]
      rw [max_eq_left htpos]

/-- An exterior component contains a nested sequence of exterior components
outside the members of any smooth relatively compact exhaustion. -/
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

/-- The nested exterior components can be equipped with points and compatible
paths.  Every path in the tail lies outside the corresponding earlier compact
exhaustion member. -/
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

/-- Every exterior complementary component contains a proper ray.  Moreover,
the ray eventually avoids each prescribed compact member of the exhaustion. -/
theorem IsExteriorComponent.exists_proper_ray_along_smoothExhaustion
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (E : SmoothRelativelyCompactExhaustion X)
    {K V : Set X} (hKcompact : IsCompact K)
    (hV : IsExteriorComponent K V) :
    ∃ (N : ℕ) (r : C(NNReal, X)),
      K ⊆ closure (E.domain N).carrier ∧
      IsProperMap r ∧
      Set.range r ⊆ V ∧
      ∀ (n : ℕ) (t : NNReal), (n : ℝ) ≤ (t : ℝ) →
        r t ∉ closure (E.domain (N + n)).carrier := by
  classical
  rcases hV.exists_escaping_path_chain_along_smoothExhaustion E hKcompact with
    ⟨N, U, x, gamma, hK, hUexterior, hU0V, hUanti, _hx, hgamma, _hescape⟩
  let r : C(NNReal, X) := pathChainRay x gamma
  have hr_mem (n : ℕ) (t : NNReal) (hnt : (n : ℝ) ≤ (t : ℝ)) :
      r t ∈ U n := by
    exact pathChainRay_mem_of_le x gamma hUanti hgamma n t hnt
  have hr_escape (n : ℕ) (t : NNReal) (hnt : (n : ℝ) ≤ (t : ℝ)) :
      r t ∉ closure (E.domain (N + n)).carrier := by
    intro hmem
    exact (hUexterior n).subset_compl (hr_mem n t hnt) hmem
  have hr_range : Set.range r ⊆ V := by
    intro y hy
    rcases hy with ⟨t, rfl⟩
    apply hU0V
    exact hr_mem 0 t (by simpa using NNReal.coe_nonneg t)
  have hr_proper : IsProperMap r := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨r.continuous, ?_⟩
    intro C hC
    rcases smoothRelativelyCompactExhaustion_compact_subset_domain E hC with
      ⟨q, hCq⟩
    have hC_obstacle : C ⊆ closure (E.domain (N + q)).carrier := by
      exact hCq.trans
        (smoothRelativelyCompactExhaustion_carrier_mono E (by omega) |>.trans
          subset_closure)
    have hpre_closed : IsClosed (r ⁻¹' C) :=
      hC.isClosed.preimage r.continuous
    have hpre_subset : r ⁻¹' C ⊆ Set.Iic (q : NNReal) := by
      intro t ht
      by_contra hnot
      have hqt : (q : NNReal) ≤ t := le_of_not_ge hnot
      have hqt_real : (q : ℝ) ≤ (t : ℝ) := by exact_mod_cast hqt
      exact hr_escape q t hqt_real (hC_obstacle ht)
    have hIic : IsCompact (Set.Iic (q : NNReal)) := by
      rw [show Set.Iic (q : NNReal) = Set.Icc 0 (q : NNReal) by
        ext t
        simp]
      exact isCompact_Icc
    exact hIic.of_isClosed_subset hpre_closed hpre_subset
  exact ⟨N, r, hK, hr_proper, hr_range, hr_escape⟩

end

end JJMath.Uniformization
