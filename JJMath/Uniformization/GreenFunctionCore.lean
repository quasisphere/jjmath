import JJMath.Uniformization.ComplexSurfaceMaps
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Shared potential-theoretic vocabulary

This module contains the common objects used by both the Green-function route
and the Evans-potential annular Perron construction.  Keeping these definitions
separate lets the Green route call the Evans construction without creating an
import cycle.
-/

namespace JJMath

open scoped Manifold Topology BigOperators

namespace Uniformization

instance instT2SpaceComplexUnitDisc : T2Space Complex.UnitDisc :=
  inferInstanceAs (T2Space (Metric.ball (0 : ℂ) 1))

instance instLocallyCompactSpaceComplexUnitDisc : LocallyCompactSpace Complex.UnitDisc := by
  change LocallyCompactSpace (Metric.ball (0 : ℂ) 1)
  exact (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1)).locallyCompactSpace

/--
%%handwave
name:
  Unique preimages imply surjectivity
statement:
  If every \(y\) has a unique \(x\) satisfying \(f(x)=y\), then \(f\) is
  surjective.
proof:
  For each \(y\), discard uniqueness and retain the asserted preimage.
-/
theorem surjective_of_existsUnique_preimage {α β : Type*} {f : α → β}
    (hfiber : ∀ y : β, ∃! x : α, f x = y) :
    Function.Surjective f := by
  intro y
  rcases hfiber y with ⟨x, hx, _⟩
  exact ⟨x, hx⟩

/--
%%handwave
name:
  Unique preimages imply injectivity
statement:
  If every target fiber of \(f:\alpha\to\beta\) contains exactly one point,
  then \(f\) is injective.
proof:
  If \(f(x)=f(y)\), both \(x\) and \(y\) are the unique preimage of
  \(f(x)\), so they are equal.
-/
theorem injective_of_existsUnique_preimage {α β : Type*} {f : α → β}
    (hfiber : ∀ y : β, ∃! x : α, f x = y) :
    Function.Injective f := by
  intro x y hxy
  rcases hfiber (f x) with ⟨w, _hw, huniq⟩
  have hxw : x = w := huniq x rfl
  have hyw : y = w := huniq y (by simp [hxy])
  exact hxw.trans hyw.symm

/--
%%handwave
name:
  Unique preimages imply bijectivity
statement:
  If every target fiber of a map contains exactly one point, then the map is
  bijective.
proof:
  The unique-preimage hypothesis separately gives injectivity and
  surjectivity.
-/
theorem bijective_of_existsUnique_preimage {α β : Type*} {f : α → β}
    (hfiber : ∀ y : β, ∃! x : α, f x = y) :
    Function.Bijective f :=
  ⟨injective_of_existsUnique_preimage hfiber,
    surjective_of_existsUnique_preimage hfiber⟩

/--
%%handwave
name:
  Neighborhood statements through an open complex embedding
statement:
  Let \(\varphi:Y\to\mathbb C\) be an open embedding.  A property \(P(y)\)
  holds for all \(y\) near \(y_0\) if and only if, for all \(z\) near
  \(\varphi(y_0)\), every \(y\) with \(\varphi(y)=z\) satisfies \(P(y)\).
proof:
  Transport eventual membership through the identity between the mapped
  neighborhood filter at \(y_0\) and the neighborhood filter at
  \(\varphi(y_0)\), using injectivity of the embedding.
-/
theorem eventually_nhds_complexModel_iff
    {Y : Type} [TopologicalSpace Y] {φ : Y → ℂ}
    (hφ : Topology.IsOpenEmbedding φ) {y₀ : Y} {P : Y → Prop} :
    (∀ᶠ y in 𝓝 y₀, P y) ↔
      ∀ᶠ z in 𝓝 (φ y₀), ∀ y : Y, φ y = z → P y := by
  constructor
  · intro hP
    have himage : φ '' {y : Y | P y} ∈ 𝓝 (φ y₀) := by
      rw [← hφ.map_nhds_eq y₀, Filter.mem_map]
      exact Filter.mem_of_superset hP (by
        intro y hy
        exact ⟨y, hy, rfl⟩)
    filter_upwards [himage] with z hz y hy
    rcases hz with ⟨y', hy'P, hy'z⟩
    have hyy' : y = y' := hφ.injective (hy.trans hy'z.symm)
    simpa [hyy'] using hy'P
  · intro hP
    rw [← hφ.map_nhds_eq y₀] at hP
    rw [Filter.eventually_map] at hP
    exact hP.mono (by
      intro y hy
      exact hy y rfl)

/--
%%handwave
name:
  Fibers of a proper map are compact
statement:
  If \(f:\alpha\to\beta\) is proper, then \(f^{-1}(y)\) is compact for every
  \(y\in\beta\).
proof:
  The singleton \(\{y\}\) is compact, and a proper map has compact preimage of
  every compact set.
-/
theorem isCompact_fiber_of_isProperMap {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
    (hproper : IsProperMap f) (y : β) :
    IsCompact {x : α | f x = y} := by
  simpa [Set.preimage, Set.mem_singleton_iff] using
    hproper.isCompact_preimage (K := {y}) isCompact_singleton

/--
%%handwave
name:
  Proper maps propagate fiberwise neighborhood properties
statement:
  Let \(f:\alpha\to\beta\) be proper.  If membership in a set \(S\) holds
  near every point of \(f^{-1}(y_0)\), then
  \(f^{-1}(y)\subseteq S\) for every sufficiently nearby \(y\).
proof:
  A proper map is closed.  Apply the closed-map fiber-neighborhood theorem to
  the neighborhoods on which membership in \(S\) holds.
-/
theorem eventually_fiber_subset_of_isProperMap {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
    (hproper : IsProperMap f) {y₀ : β} {s : Set α}
    (hs : ∀ x : α, f x = y₀ → ∀ᶠ x' in 𝓝 x, x' ∈ s) :
    ∀ᶠ y in 𝓝 y₀, {x : α | f x = y} ⊆ s := by
  have hnear :
      ∀ᶠ y in 𝓝 y₀, ∀ x ∈ f ⁻¹' {y}, x ∈ s :=
    hproper.isClosedMap.eventually_nhds_fiber y₀ (by
      intro x hx
      exact hs x (by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hx))
  filter_upwards [hnear] with y hy x hx
  exact hy x (by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hx)

/--
%%handwave
name:
  Nearby fibers of a proper map lie in any open fiber neighborhood
statement:
  If \(f\) is proper and an open set \(U\) contains \(f^{-1}(y_0)\), then
  \(f^{-1}(y)\subseteq U\) for every sufficiently nearby \(y\).
proof:
  Openness makes membership in \(U\) hold near every point of the old fiber.
  Apply the proper-map fiberwise propagation result.
-/
theorem eventually_fiber_subset_open_of_isProperMap {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
    (hproper : IsProperMap f) {y₀ : β} {U : Set α}
    (hU : IsOpen U) (hcover : {x : α | f x = y₀} ⊆ U) :
    ∀ᶠ y in 𝓝 y₀, {x : α | f x = y} ⊆ U :=
  eventually_fiber_subset_of_isProperMap hproper (by
    intro x hx
    exact hU.mem_nhds (hcover hx))

/--
%%handwave
name:
  Disjoint neighborhoods capturing nearby fibers of a proper map
statement:
  Let \(f:\alpha\to\beta\) be proper with Hausdorff source and finite fiber
  over \(y_0\).  There are pairwise disjoint open neighborhoods \(U_x\) of
  the points \(x\in f^{-1}(y_0)\) such that every sufficiently nearby fiber is
  contained in \(\bigcup_{x\in f^{-1}(y_0)}U_x\).
proof:
  Hausdorff separation supplies pairwise disjoint open neighborhoods for the
  finite old fiber.  Their union is an open neighborhood of that fiber, and
  properness forces all nearby fibers into it.
-/
theorem properMap_finite_fiber_exists_pairwiseDisjoint_open_nhds_eventually
    {α β : Type*} [TopologicalSpace α] [T2Space α] [TopologicalSpace β]
    {f : α → β} (hproper : IsProperMap f) (y₀ : β)
    (hfinite : {x : α | f x = y₀}.Finite) :
    ∃ U : α → Set α,
      (∀ x : α, x ∈ {x : α | f x = y₀} → x ∈ U x ∧ IsOpen (U x)) ∧
        ({x : α | f x = y₀}.PairwiseDisjoint U) ∧
          ∀ᶠ y in 𝓝 y₀,
            {x : α | f x = y} ⊆
              ⋃ x : {x : α | f x = y₀}, U x.1 := by
  rcases hfinite.t2_separation with ⟨U, hU, hpair⟩
  refine ⟨U, ?_, hpair, ?_⟩
  · intro x _hx
    exact hU x
  · let V : Set α := ⋃ x : {x : α | f x = y₀}, U x.1
    have hV_open : IsOpen V := by
      dsimp [V]
      exact isOpen_iUnion fun x ↦ (hU x.1).2
    have hcover : {x : α | f x = y₀} ⊆ V := by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (hU x).1⟩
    exact eventually_fiber_subset_open_of_isProperMap hproper hV_open hcover

/--
%%handwave
name:
  Uniqueness of a disjoint fiber neighborhood containing a point
statement:
  If neighborhoods \((U_x)_{x\in f^{-1}(y_0)}\) are pairwise disjoint and a
  point \(z\) belongs to both \(U_{x_0}\) and \(U_{x_1}\), then
  \(x_0=x_1\).
proof:
  Distinct indices would give disjoint neighborhoods, contradicting the
  common point \(z\).
-/
theorem eq_of_mem_pairwiseDisjoint_fiber_neighborhoods
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} {y₀ : β} {U : α → Set α}
    (hpair : ({x : α | f x = y₀}.PairwiseDisjoint U))
    {x₀ x₁ z : α} (hx₀ : f x₀ = y₀) (hx₁ : f x₁ = y₀)
    (hz₀ : z ∈ U x₀) (hz₁ : z ∈ U x₁) :
    x₀ = x₁ := by
  by_contra hne
  have hdisj : Disjoint (U x₀) (U x₁) :=
    hpair hx₀ hx₁ hne
  exact (Set.disjoint_left.mp hdisj hz₀ hz₁).elim

/--
%%handwave
name:
  An old fiber point in another selected neighborhood has the same index
statement:
  Suppose each \(x\in f^{-1}(y_0)\) lies in \(U_x\), and these neighborhoods
  are pairwise disjoint.  If \(z\in f^{-1}(y_0)\cap U_{x_0}\), then
  \(z=x_0\).
proof:
  The point \(z\) lies in both \(U_z\) and \(U_{x_0}\).  Uniqueness of the
  containing disjoint neighborhood makes the two indices equal.
-/
theorem eq_of_old_fiber_mem_pairwiseDisjoint_fiber_neighborhood
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} {y₀ : β} {U : α → Set α}
    (hU_mem : ∀ x : α, f x = y₀ → x ∈ U x)
    (hpair : ({x : α | f x = y₀}.PairwiseDisjoint U))
    {x₀ z : α} (hx₀ : f x₀ = y₀) (hz : f z = y₀)
    (hzU : z ∈ U x₀) :
    z = x₀ := by
  exact eq_of_mem_pairwiseDisjoint_fiber_neighborhoods
    (f := f) (y₀ := y₀) (U := U) hpair
    (x₀ := z) (x₁ := x₀) (z := z)
    hz hx₀ (hU_mem z hz) hzU

/--
%%handwave
name:
  A selected fiber neighborhood isolates its indexed point
statement:
  Under pairwise disjoint selected neighborhoods containing their indexed
  old-fiber points,
  \(U_{x_0}\cap f^{-1}(y_0)\subseteq\{x_0\}\).
proof:
  Any point in the intersection is an old-fiber point lying in
  \(U_{x_0}\), so the preceding uniqueness result identifies it with
  \(x_0\).
-/
theorem fiber_neighborhood_inter_old_fiber_subset_singleton
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} {y₀ : β} {U : α → Set α}
    (hU_mem : ∀ x : α, f x = y₀ → x ∈ U x)
    (hpair : ({x : α | f x = y₀}.PairwiseDisjoint U))
    {x₀ : α} (hx₀ : f x₀ = y₀) :
    U x₀ ∩ {z : α | f z = y₀} ⊆ {x₀} := by
  intro z hz
  exact Set.mem_singleton_iff.mpr
    (eq_of_old_fiber_mem_pairwiseDisjoint_fiber_neighborhood
      hU_mem hpair hx₀ hz.2 hz.1)

/--
%%handwave
name:
  Other fiber points are locally outside a selected neighborhood
statement:
  Let \((U_x)\) be pairwise disjoint open neighborhoods of
  \(f^{-1}(y_0)\).  If \(z\ne x_0\) are points of that fiber, then every point
  sufficiently near \(z\) lies outside \(U_{x_0}\).
proof:
  The open neighborhood \(U_z\) of \(z\) is disjoint from \(U_{x_0}\).
-/
theorem eventually_not_mem_fiber_neighborhood_of_pairwiseDisjoint_ne
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} {y₀ : β} {U : α → Set α}
    (hU : ∀ x : α, f x = y₀ → x ∈ U x ∧ IsOpen (U x))
    (hpair : ({x : α | f x = y₀}.PairwiseDisjoint U))
    {x₀ z : α} (hx₀ : f x₀ = y₀) (hz : f z = y₀)
    (hz_ne : z ≠ x₀) :
    ∀ᶠ w in 𝓝 z, w ∉ U x₀ := by
  have hdisj : Disjoint (U z) (U x₀) :=
    hpair hz hx₀ hz_ne
  have hUz_nhds : U z ∈ 𝓝 z :=
    (hU z hz).2.mem_nhds (hU z hz).1
  exact Filter.mem_of_superset hUz_nhds (by
    intro w hw hzU
    exact (Set.disjoint_left.mp hdisj hw hzU).elim)

/--
%%handwave
name:
  Unique old-fiber neighborhood for a captured nearby point
statement:
  Suppose pairwise disjoint neighborhoods \((U_x)_{x\in f^{-1}(y_0)}\)
  contain \(f^{-1}(y)\) in their union.  Then every \(z\in f^{-1}(y)\) lies
  in a unique \(U_x\) indexed by \(x\in f^{-1}(y_0)\).
proof:
  The covering gives existence.  If two indices worked, the point would lie
  in two pairwise disjoint neighborhoods, forcing the indices to agree.
-/
theorem existsUnique_fiber_neighborhood_of_mem_fiber_subset_pairwiseDisjoint
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} {y₀ y : β} {U : α → Set α}
    (hpair : ({x : α | f x = y₀}.PairwiseDisjoint U))
    (hcover : {x : α | f x = y} ⊆
      ⋃ x : {x : α | f x = y₀}, U x.1)
    {z : α} (hz : f z = y) :
    ∃! x₀ : {x : α | f x = y₀}, z ∈ U x₀.1 := by
  rcases Set.mem_iUnion.mp (hcover hz) with ⟨x₀, hzU⟩
  refine ⟨x₀, hzU, ?_⟩
  intro x₁ hzU₁
  apply Subtype.ext
  exact (eq_of_mem_pairwiseDisjoint_fiber_neighborhoods
    (f := f) (y₀ := y₀) (U := U) hpair
    (x₀ := x₀.1) (x₁ := x₁.1) (z := z) x₀.2 x₁.2 hzU hzU₁).symm

/--
%%handwave
name:
  Eventual unique assignment to old-fiber neighborhoods
statement:
  Let \(f\) be proper with Hausdorff source and finite fiber over \(y_0\).
  There are pairwise disjoint open neighborhoods of the old fiber points such
  that, for every sufficiently nearby \(y\), each point of \(f^{-1}(y)\) lies
  in exactly one selected neighborhood.
proof:
  Choose disjoint neighborhoods whose union eventually contains every nearby
  fiber, then apply uniqueness of the containing neighborhood pointwise.
-/
theorem eventually_existsUnique_fiber_neighborhood_of_properMap_finite_fiber
    {α β : Type*} [TopologicalSpace α] [T2Space α] [TopologicalSpace β]
    {f : α → β} (hproper : IsProperMap f) (y₀ : β)
    (hfinite : {x : α | f x = y₀}.Finite) :
    ∃ U : α → Set α,
      (∀ x : α, x ∈ {x : α | f x = y₀} → x ∈ U x ∧ IsOpen (U x)) ∧
        ({x : α | f x = y₀}.PairwiseDisjoint U) ∧
          ∀ᶠ y in 𝓝 y₀,
            ∀ z : α, f z = y →
              ∃! x₀ : {x : α | f x = y₀}, z ∈ U x₀.1 := by
  rcases properMap_finite_fiber_exists_pairwiseDisjoint_open_nhds_eventually
      hproper y₀ hfinite with ⟨U, hU, hpair, hcover_event⟩
  refine ⟨U, hU, hpair, ?_⟩
  filter_upwards [hcover_event] with y hcover z hz
  exact existsUnique_fiber_neighborhood_of_mem_fiber_subset_pairwiseDisjoint
    hpair hcover hz

/--
%%handwave
name:
  Nearby fibers of an open map meet an open source neighborhood
statement:
  Let \(f:\alpha\to\beta\) be open, let \(f(x_0)=y_0\), and let \(U\) be an
  open neighborhood of \(x_0\).  Then every sufficiently nearby \(y\) has a
  preimage in \(U\).
proof:
  The image \(f(U)\) is an open neighborhood of \(y_0\).  Every point of this
  image has, by definition, a preimage in \(U\).
-/
theorem eventually_exists_mem_open_of_isOpenMap
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hopen : IsOpenMap f) {y₀ : β} {U : Set α}
    (hU_open : IsOpen U) {x₀ : α} (hx₀U : x₀ ∈ U) (hx₀ : f x₀ = y₀) :
    ∀ᶠ y in 𝓝 y₀, ∃ z : α, z ∈ U ∧ f z = y := by
  have hy₀ : y₀ ∈ f '' U := ⟨x₀, hx₀U, hx₀⟩
  have hnhds : f '' U ∈ 𝓝 y₀ :=
    (hopen U hU_open).mem_nhds hy₀
  filter_upwards [hnhds] with y hy
  rcases hy with ⟨z, hzU, hzF⟩
  exact ⟨z, hzU, hzF⟩

/--
%%handwave
name:
  Nearby fibers meet every selected neighborhood of a finite old fiber
statement:
  Let \(f\) be open and let \(f^{-1}(y_0)\) be finite.  If each old-fiber
  point \(x_0\) has a selected open neighborhood \(U_{x_0}\), then for every
  sufficiently nearby \(y\), each \(U_{x_0}\) contains a point of
  \(f^{-1}(y)\).
proof:
  Openness gives the assertion eventually for each individual old-fiber
  point.  Intersect the finitely many resulting target neighborhoods.
-/
theorem eventually_forall_fiber_neighborhood_exists_of_isOpenMap
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hopen : IsOpenMap f) {y₀ : β} {U : α → Set α}
    (hU : ∀ x₀ : α, f x₀ = y₀ → x₀ ∈ U x₀ ∧ IsOpen (U x₀))
    (hfinite : {x : α | f x = y₀}.Finite) :
    ∀ᶠ y in 𝓝 y₀,
      ∀ x₀ : {x : α | f x = y₀},
        ∃ z : α, z ∈ U x₀.1 ∧ f z = y := by
  classical
  let s : Finset α := hfinite.toFinset
  have hall :
      ∀ x₀ : α, f x₀ = y₀ →
        ∀ᶠ y in 𝓝 y₀, ∃ z : α, z ∈ U x₀ ∧ f z = y := by
    intro x₀ hx₀
    exact eventually_exists_mem_open_of_isOpenMap hopen
      (hU x₀ hx₀).2 (hU x₀ hx₀).1 hx₀
  have hfin :
      ∀ᶠ y in 𝓝 y₀,
        ∀ x₀ ∈ s, ∃ z : α, z ∈ U x₀ ∧ f z = y := by
    rw [Finset.eventually_all]
    intro x₀ hx₀s
    exact hall x₀ (hfinite.mem_toFinset.mp (by simpa [s] using hx₀s))
  filter_upwards [hfin] with y hy x₀
  exact hy x₀.1 (by
    simp [s, hfinite.mem_toFinset.mpr x₀.2])

/--
%%handwave
name:
  Reindexing a finite sum by a unique partition
statement:
  Let \(S\) and \(T\) be finite sets, and suppose each \(x\in S\) belongs to
  exactly one part indexed by \(i\in T\).  For any additive weights \(m(x)\),
  \[
    \sum_{x\in S}m(x)
      =\sum_{i\in T}\sum_{\substack{x\in S\\P(x,i)}}m(x).
  \]
proof:
  Replace each summand \(m(x)\) by the sum over indices which is zero except at
  its unique index.  Interchange the two finite sums and identify the inner
  conditional sums with sums over the filtered parts.
-/
theorem finset_sum_eq_sum_filter_of_existsUnique
    {α ι M : Type*} [AddCommMonoid M]
    (s : Finset α) (t : Finset ι) (m : α → M) (P : α → ι → Prop)
    [DecidableRel P]
    (hunique : ∀ x ∈ s, ∃! i : ι, i ∈ t ∧ P x i) :
    s.sum m = t.sum fun i ↦ (s.filter fun x ↦ P x i).sum m := by
  classical
  calc
    s.sum m =
        s.sum (fun x ↦ t.sum fun i ↦ if P x i then m x else 0) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rcases hunique x hx with ⟨i, hi, huniq⟩
      have hi_mem : i ∈ t := hi.1
      have hiP : P x i := hi.2
      symm
      refine (Finset.sum_eq_single (s := t) (a := i)
        (f := fun j ↦ if P x j then m x else 0) ?_ ?_).trans ?_
      · intro j hjt hji
        have hnot : ¬ P x j := by
          intro hjP
          exact hji (huniq j ⟨hjt, hjP⟩)
        simp [hnot]
      · intro hi_not_mem
        exact (hi_not_mem hi_mem).elim
      · simp [hiP]
    _ = t.sum (fun i ↦ s.sum fun x ↦ if P x i then m x else 0) := by
      rw [Finset.sum_comm]
    _ = t.sum fun i ↦ (s.filter fun x ↦ P x i).sum m := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [Finset.sum_filter]

/--
%%handwave
name:
  Compactness plus locally finite singleton family implies finiteness
statement:
  Let \(S\) be compact.  If the family \((\{x\})_{x\in S}\) is locally finite
  in the ambient space, then \(S\) is finite.
proof:
  A locally finite family has only finitely many members meeting a fixed
  compact set.  Every singleton indexed by \(S\) meets \(S\), so only finitely
  many indices occur.
-/
theorem finite_of_isCompact_of_locallyFinite_singletons {α : Type*}
    [TopologicalSpace α] {s : Set α}
    (hs : IsCompact s)
    (hloc : LocallyFinite fun x : s ↦ ({(x : α)} : Set α)) :
    s.Finite := by
  have hfin :
      {x : s | (({(x : α)} : Set α) ∩ s).Nonempty}.Finite :=
    hloc.finite_nonempty_inter_compact hs
  have hfin_univ : (Set.univ : Set s).Finite := by
    simpa using hfin
  haveI : Finite s := Set.finite_univ_iff.mp hfin_univ
  exact Set.toFinite s

/--
%%handwave
name:
  A proper fiber with locally finite singletons is finite
statement:
  If \(f\) is proper and the singleton family indexed by \(f^{-1}(y)\) is
  locally finite, then the fiber \(f^{-1}(y)\) is finite.
proof:
  Properness makes the fiber compact.  Apply the compactness criterion for a
  locally finite family of its singleton subsets.
-/
theorem finite_fiber_of_isProperMap_of_locallyFinite_singletons {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {f : α → β} (hproper : IsProperMap f)
    (y : β)
    (hloc : LocallyFinite fun x : {x : α | f x = y} ↦ ({(x : α)} : Set α)) :
    {x : α | f x = y}.Finite :=
  finite_of_isCompact_of_locallyFinite_singletons
    (isCompact_fiber_of_isProperMap hproper y) hloc

/--
%%handwave
name:
  Isolated points of a closed set form a locally finite singleton family
statement:
  Let \(S\) be closed, and suppose every \(x\in S\) has an open neighborhood
  meeting \(S\) only at \(x\).  Then the family \((\{x\})_{x\in S}\) is
  locally finite.
proof:
  At a point of \(S\), use its isolating neighborhood, which meets only one
  indexed singleton.  At a point outside \(S\), use the open complement,
  which meets none.
-/
theorem locallyFinite_singletons_of_isClosed_of_isolated_points {α : Type*}
    [TopologicalSpace α] {s : Set α} (hclosed : IsClosed s)
    (hiso : ∀ x : s, ∃ P : Set α,
      IsOpen P ∧ (x : α) ∈ P ∧
        ∀ y : s, (y : α) ∈ P → y = x) :
    LocallyFinite fun x : s ↦ ({(x : α)} : Set α) := by
  intro a
  by_cases ha : a ∈ s
  · let x : s := ⟨a, ha⟩
    rcases hiso x with ⟨P, hP_open, hxP, hP_iso⟩
    refine ⟨P, hP_open.mem_nhds hxP, ?_⟩
    exact (Set.finite_singleton x).subset (by
      intro y hy
      rcases hy with ⟨z, hz_y, hzP⟩
      have hz_eq : z = (y : α) := by
        simpa using hz_y
      have hyP : (y : α) ∈ P := by
        simpa [hz_eq] using hzP
      exact hP_iso y hyP)
  · refine ⟨sᶜ, hclosed.isOpen_compl.mem_nhds (by simpa using ha), ?_⟩
    refine (Set.finite_empty : (∅ : Set s).Finite).subset ?_
    intro y hy
    rcases hy with ⟨z, hz_y, hz_not_s⟩
    have hz_eq : z = (y : α) := by
      simpa using hz_y
    exact False.elim (by
      exact hz_not_s (by simp [hz_eq, y.2]))

/--
%%handwave
name:
  Fibers of a nonconstant holomorphic map are locally finite
statement:
  If \(f:X\to\mathbb C\) is a nonconstant holomorphic map from a Riemann
  surface, then the singleton family indexed by each fiber \(f^{-1}(a)\) is
  locally finite.
proof:
  Continuity makes the fiber closed.  The isolated-zero theorem for a
  nonconstant holomorphic map gives an isolating neighborhood at each fiber
  point, so the closed isolated-set criterion applies.
-/
theorem nonconstant_holomorphicMap_fiber_singletons_locallyFinite
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {f : X → ℂ}
    (hf : HolomorphicMap X ℂ f)
    (hnonconstant : (Set.range f).Nontrivial) (a : ℂ) :
    LocallyFinite fun x : {x : X | f x = a} ↦ ({(x : X)} : Set X) := by
  refine locallyFinite_singletons_of_isClosed_of_isolated_points ?_ ?_
  · simpa [Set.setOf_eq_eq_singleton] using
      (isClosed_eq hf.continuous continuous_const : IsClosed {x : X | f x = a})
  · intro x
    rcases nonconstant_holomorphicMap_exists_isolatedFiber_neighborhood
        (f := f) hf hnonconstant x with
      ⟨P, hP_open, hxP, hP_iso⟩
    refine ⟨P, hP_open, hxP, ?_⟩
    intro y hyP
    apply Subtype.ext
    by_contra hyne
    have hne : (y : X) ≠ (x : X) := hyne
    have hvalue_ne : f (y : X) ≠ f (x : X) :=
      hP_iso (y : X) hyP hne
    exact hvalue_ne (by rw [y.2, x.2])

/--
%%handwave
name:
  Proper nonconstant holomorphic maps to the plane have finite fibers
statement:
  A proper nonconstant holomorphic map from a Riemann surface to
  \(\mathbb C\) has finite fibers.
proof:
  Each fiber is compact by properness and its singleton family is locally
  finite by isolation of zeros.  Hence the fiber is finite.
-/
theorem proper_nonconstant_holomorphicMap_fiber_finite
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : X → ℂ}
    (hF : HolomorphicMap X ℂ F)
    (hnonconstant : (Set.range F).Nontrivial)
    (hproper : IsProperMap F) (z : ℂ) :
    {x : X | F x = z}.Finite :=
  finite_fiber_of_isProperMap_of_locallyFinite_singletons hproper z
    (nonconstant_holomorphicMap_fiber_singletons_locallyFinite
      (f := F) hF hnonconstant z)

/--
%%handwave
name:
  Open mapping theorem for Riemann surfaces
statement:
  A nonconstant holomorphic map from a Riemann surface to \(\mathbb C\) is an
  open map.
proof:
  In a chart at each source point, the map becomes a one-variable analytic
  function which is not locally constant.  The analytic open mapping theorem
  makes the coordinate germ open; transporting its neighborhood-filter
  statement through the chart proves that the surface map is open.
-/
theorem nonconstant_holomorphicMap_isOpenMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : X → ℂ}
    (hF : HolomorphicMap X ℂ F)
    (hnonconstant : (Set.range F).Nontrivial) :
    IsOpenMap F := by
  classical
  refine IsOpenMap.of_nhds_le ?_
  intro x
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let z₀ : ℂ := e x
  have hx_source : x ∈ e.source := mem_chart_source ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have hg_an : AnalyticAt ℂ (fun z : ℂ ↦ F (e.symm z)) z₀ := by
    simpa [z₀] using
      surface_coordinateExpression_analyticAt (X := X) (f := F) hF he hx_source
  have hnot_surface :
      ¬ ∀ᶠ y in 𝓝 x, F y = F x :=
    nonconstant_holomorphicMap_not_eventually_eq_value
      (f := F) hF hnonconstant x
  have hnot_coord :
      ¬ ∀ᶠ z in 𝓝 z₀,
        (fun z : ℂ ↦ F (e.symm z)) z =
          (fun z : ℂ ↦ F (e.symm z)) z₀ := by
    intro hcoord
    apply hnot_surface
    have hcoord_set :
        {z : ℂ | F (e.symm z) = F (e.symm z₀)} ∈ 𝓝 z₀ := by
      simpa using hcoord
    have hpre :
        e ⁻¹' {z : ℂ | F (e.symm z) = F (e.symm z₀)} ∈ 𝓝 x := by
      rw [← e.map_nhds_eq hx_source, Filter.mem_map] at hcoord_set
      exact hcoord_set
    have hsource_mem : e.source ∈ 𝓝 x :=
      e.open_source.mem_nhds hx_source
    refine Filter.mem_of_superset (Filter.inter_mem hsource_mem hpre) ?_
    intro y hy
    rcases hy with ⟨hy_source, hy_pre⟩
    change F (e.symm (e y)) = F (e.symm z₀) at hy_pre
    simpa [z₀, e.left_inv hy_source, e.left_inv hx_source] using hy_pre
  have hlocal_coord :
      𝓝 ((fun z : ℂ ↦ F (e.symm z)) z₀) ≤
        Filter.map (fun z : ℂ ↦ F (e.symm z)) (𝓝 z₀) :=
    (hg_an.eventually_constant_or_nhds_le_map_nhds).resolve_left hnot_coord
  have hlocal_surface :
      𝓝 (F x) ≤ Filter.map (fun z : ℂ ↦ F (e.symm z)) (𝓝 z₀) := by
    simpa [z₀, e.left_inv hx_source] using hlocal_coord
  have hmap_eq :
      Filter.map (fun z : ℂ ↦ F (e.symm z)) (𝓝 z₀) =
        Filter.map F (𝓝 x) := by
    dsimp [z₀]
    rw [← e.map_nhds_eq hx_source, Filter.map_map]
    exact Filter.map_congr (by
      filter_upwards [e.open_source.mem_nhds hx_source] with y hy
      simp [e.left_inv hy])
  simpa [hmap_eq] using hlocal_surface

/--
%%handwave
name:
  A proper nonconstant holomorphic map to the plane is surjective
statement:
  Every proper nonconstant holomorphic map from a Riemann surface to
  \(\mathbb C\) is surjective.
proof:
  Its range is open by the open mapping theorem and closed by properness.  It
  is nonempty, and the complex plane is connected, so the range is all of
  \(\mathbb C\).
-/
theorem proper_nonconstant_holomorphicMap_surjective
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {F : X → ℂ}
    (hF : HolomorphicMap X ℂ F)
    (hnonconstant : (Set.range F).Nontrivial)
    (hproper : IsProperMap F) :
    Function.Surjective F := by
  classical
  have hopen_map : IsOpenMap F :=
    nonconstant_holomorphicMap_isOpenMap hF hnonconstant
  have hclosed : IsClosed (Set.range F) :=
    hproper.isClosed_range
  have hopen : IsOpen (Set.range F) := by
    simpa [Set.image_univ] using hopen_map Set.univ isOpen_univ
  have hnonempty : (Set.range F).Nonempty := by
    rcases hnonconstant with ⟨z, hz, _w, _hw, _hzw⟩
    exact ⟨z, hz⟩
  have hrange_univ : Set.range F = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ hnonempty
  intro z
  have hz : z ∈ Set.range F := by
    rw [hrange_univ]
    exact Set.mem_univ z
  simpa [Set.mem_range] using hz

/--
%%handwave
name:
  Fibers of a nonconstant pointed disk map are locally finite
statement:
  For a pointed holomorphic map \(F:X\to\mathbb D\) whose complex range is
  nontrivial, the singleton family indexed by each fiber is locally finite.
proof:
  The fiber is closed by continuity.  After composing with the inclusion
  \(\mathbb D\hookrightarrow\mathbb C\), nonconstancy gives isolated fiber
  points, so the closed isolated-set criterion applies.
-/
theorem nonconstant_pointedDiskMap_fiber_singletons_locallyFinite
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hnonconstant :
      (Set.range fun x : X ↦ ((F.toFun x : Complex.UnitDisc) : ℂ)).Nontrivial)
    (z : Complex.UnitDisc) :
    LocallyFinite fun x : {x : X | F.toFun x = z} ↦ ({(x : X)} : Set X) := by
  refine locallyFinite_singletons_of_isClosed_of_isolated_points ?_ ?_
  · simpa using
      (isClosed_eq F.holomorphic.continuous continuous_const :
        IsClosed {x : X | F.toFun x = z})
  · intro x
    rcases nonconstant_holomorphicMap_exists_isolatedFiber_neighborhood
        (f := fun y : X ↦ ((F.toFun y : Complex.UnitDisc) : ℂ))
        F.holomorphic_coe_unitDisc hnonconstant (x : X) with
      ⟨P, hP_open, hxP, hP_iso⟩
    refine ⟨P, hP_open, hxP, ?_⟩
    intro y hyP
    apply Subtype.ext
    by_contra hyne
    have hne : (y : X) ≠ (x : X) := hyne
    have hvalue_ne :
        ((F.toFun (y : X) : Complex.UnitDisc) : ℂ) ≠
          ((F.toFun (x : X) : Complex.UnitDisc) : ℂ) :=
      hP_iso (y : X) hyP hne
    exact hvalue_ne (by rw [y.2, x.2])

/--
%%handwave
name:
  Proper nonconstant pointed disk maps have finite fibers
statement:
  A proper pointed holomorphic map to the unit disk with nontrivial complex
  range has finite fibers.
proof:
  Properness makes each fiber compact, while nonconstancy makes its singleton
  family locally finite.  Compactness then forces finiteness.
-/
theorem proper_nonconstant_pointedDiskMap_fiber_finite
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hnonconstant :
      (Set.range fun x : X ↦ ((F.toFun x : Complex.UnitDisc) : ℂ)).Nontrivial)
    (hproper : IsProperMap F.toFun) (z : Complex.UnitDisc) :
    {x : X | F.toFun x = z}.Finite :=
  finite_fiber_of_isProperMap_of_locallyFinite_singletons hproper z
    (nonconstant_pointedDiskMap_fiber_singletons_locallyFinite F hnonconstant z)

/--
%%handwave
name:
  Open mapping theorem for pointed disk maps
statement:
  A pointed holomorphic map \(F:X\to\mathbb D\) with nontrivial complex range
  is open.
proof:
  Its composite with the inclusion into \(\mathbb C\) is nonconstant and
  holomorphic, hence open.  Since the disk has the subspace topology, the
  image under \(F\) of any open set is the inverse image in the disk of that
  open complex image.
-/
theorem nonconstant_pointedDiskMap_isOpenMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hnonconstant :
      (Set.range fun x : X ↦ ((F.toFun x : Complex.UnitDisc) : ℂ)).Nontrivial) :
    IsOpenMap F.toFun := by
  let f : X → ℂ := fun x : X ↦ ((F.toFun x : Complex.UnitDisc) : ℂ)
  have hfopen : IsOpenMap f :=
    nonconstant_holomorphicMap_isOpenMap F.holomorphic_coe_unitDisc hnonconstant
  intro U hU
  have hcomplex_open : IsOpen (f '' U) :=
    hfopen U hU
  have himage_eq :
      F.toFun '' U = Subtype.val ⁻¹' (f '' U) := by
    ext z
    constructor
    · rintro ⟨x, hxU, rfl⟩
      exact ⟨x, hxU, rfl⟩
    · rintro ⟨x, hxU, hx⟩
      refine ⟨x, hxU, ?_⟩
      exact Subtype.ext hx
  rw [himage_eq]
  exact hcomplex_open.preimage continuous_subtype_val

/--
%%handwave
name:
  A proper nonconstant pointed disk map is surjective
statement:
  A proper pointed holomorphic map to \(\mathbb D\) with nontrivial complex
  range is onto the disk.
proof:
  Its range is open by the disk open mapping theorem and closed by properness.
  The range is nonempty, and the disk is connected, so it equals the whole
  disk.
-/
theorem proper_nonconstant_pointedDiskMap_surjective
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hnonconstant :
      (Set.range fun x : X ↦ ((F.toFun x : Complex.UnitDisc) : ℂ)).Nontrivial)
    (hproper : IsProperMap F.toFun) :
    Function.Surjective F.toFun := by
  classical
  have hopen_map : IsOpenMap F.toFun :=
    nonconstant_pointedDiskMap_isOpenMap F hnonconstant
  have hclosed : IsClosed (Set.range F.toFun) :=
    hproper.isClosed_range
  have hopen : IsOpen (Set.range F.toFun) := by
    simpa [Set.image_univ] using hopen_map Set.univ isOpen_univ
  have hnonempty : (Set.range F.toFun).Nonempty :=
    ⟨F.toFun p, ⟨p, rfl⟩⟩
  have hrange_univ : Set.range F.toFun = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ hnonempty
  intro z
  have hz : z ∈ Set.range F.toFun := by
    rw [hrange_univ]
    exact Set.mem_univ z
  simpa [Set.mem_range] using hz

/--
%%handwave
name:
  Open mapping theorem for a target with an open complex model
statement:
  Let \(F:X\to Y\) be a map from a Riemann surface and let
  \(\varphi:Y\to\mathbb C\) be an open embedding.  If \(\varphi\circ F\) is
  holomorphic with nontrivial range, then \(F\) is open.
proof:
  The complex-coordinate expression is open by the Riemann-surface open
  mapping theorem.  Openness of \(\varphi\) identifies this with openness of
  \(F\).
-/
theorem nonconstant_holomorphicMap_to_openComplexModel_isOpenMap
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_open : Topology.IsOpenEmbedding φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hnonconstant : (Set.range fun x : X ↦ φ (F x)).Nontrivial) :
    IsOpenMap F := by
  have hcomplex_open : IsOpenMap (fun x : X ↦ φ (F x)) :=
    nonconstant_holomorphicMap_isOpenMap hF hnonconstant
  exact (hφ_open.isOpenMap_iff (f := F)).mpr (by
    simpa [Function.comp_def] using hcomplex_open)

/--
%%handwave
name:
  Local finiteness of fibers in an open complex target model
statement:
  Under an open embedding \(\varphi:Y\to\mathbb C\), if
  \(\varphi\circ F\) is nonconstant and holomorphic, then the singleton family
  indexed by each fiber \(F^{-1}(y)\) is locally finite.
proof:
  Injectivity of \(\varphi\) identifies the fiber with a level set of the
  complex-coordinate expression.  That level set is closed and has isolated
  points by the nonconstant holomorphic isolated-zero theorem.
-/
theorem nonconstant_holomorphicMap_to_openComplexModel_fiber_singletons_locallyFinite
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_open : Topology.IsOpenEmbedding φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hnonconstant : (Set.range fun x : X ↦ φ (F x)).Nontrivial)
    (y : Y) :
    LocallyFinite fun x : {x : X | F x = y} ↦ ({(x : X)} : Set X) := by
  refine locallyFinite_singletons_of_isClosed_of_isolated_points ?_ ?_
  · have hset_eq :
        {x : X | F x = y} = {x : X | φ (F x) = φ y} := by
      ext x
      exact ⟨fun hx ↦ congrArg φ hx, fun hx ↦ hφ_open.injective hx⟩
    rw [hset_eq]
    simpa [Set.setOf_eq_eq_singleton] using
      (isClosed_eq hF.continuous continuous_const :
        IsClosed {x : X | φ (F x) = φ y})
  · intro x
    rcases nonconstant_holomorphicMap_exists_isolatedFiber_neighborhood
        (f := fun x : X ↦ φ (F x)) hF hnonconstant (x : X) with
      ⟨P, hP_open, hxP, hP_iso⟩
    refine ⟨P, hP_open, hxP, ?_⟩
    intro x' hx'P
    apply Subtype.ext
    by_contra hne
    have hvalue_ne : φ (F (x' : X)) ≠ φ (F (x : X)) :=
      hP_iso (x' : X) hx'P hne
    exact hvalue_ne (by rw [x'.2, x.2])

/--
%%handwave
name:
  Proper nonconstant maps to an open complex model have finite fibers
statement:
  A proper map \(F:X\to Y\) whose expression in an open complex target model
  is nonconstant and holomorphic has finite fibers.
proof:
  Properness makes each fiber compact, while holomorphic nonconstancy makes
  its singleton family locally finite.  The compactness criterion gives
  finiteness.
-/
theorem proper_nonconstant_holomorphicMap_to_openComplexModel_fiber_finite
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_open : Topology.IsOpenEmbedding φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hnonconstant : (Set.range fun x : X ↦ φ (F x)).Nontrivial)
    (hproper : IsProperMap F) (y : Y) :
    {x : X | F x = y}.Finite :=
  finite_fiber_of_isProperMap_of_locallyFinite_singletons hproper y
    (nonconstant_holomorphicMap_to_openComplexModel_fiber_singletons_locallyFinite
      hφ_open hF hnonconstant y)

/--
%%handwave
name:
  Surjectivity of a proper nonconstant map to a preconnected complex model
statement:
  Let \(Y\) be preconnected and openly embedded in \(\mathbb C\).  A proper
  map \(F:X\to Y\) whose complex-coordinate expression is nonconstant and
  holomorphic is surjective.
proof:
  The range of \(F\) is open by the open mapping theorem and closed by
  properness.  It is nonempty, so preconnectedness forces it to be all of
  \(Y\).
-/
theorem proper_nonconstant_holomorphicMap_to_openComplexModel_surjective
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y] [PreconnectedSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_open : Topology.IsOpenEmbedding φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hnonconstant : (Set.range fun x : X ↦ φ (F x)).Nontrivial)
    (hproper : IsProperMap F) :
    Function.Surjective F := by
  classical
  have hopen_map : IsOpenMap F :=
    nonconstant_holomorphicMap_to_openComplexModel_isOpenMap
      hφ_open hF hnonconstant
  have hclosed : IsClosed (Set.range F) :=
    hproper.isClosed_range
  have hopen : IsOpen (Set.range F) := by
    simpa [Set.image_univ] using hopen_map Set.univ isOpen_univ
  have hnonempty : (Set.range F).Nonempty := by
    rcases hnonconstant with ⟨_z, hz, _w, _hw, _hzw⟩
    rcases hz with ⟨x, _rfl⟩
    exact ⟨F x, ⟨x, rfl⟩⟩
  have hrange_univ : Set.range F = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ hnonempty
  intro y
  have hy : y ∈ Set.range F := by
    rw [hrange_univ]
    exact Set.mem_univ y
  simpa [Set.mem_range] using hy

/--
%%handwave
name:
  Nearby fibers meet selected neighborhoods in an open complex model
statement:
  Let \(F:X\to Y\) have nonconstant holomorphic expression in an open complex
  target model, and suppose \(F^{-1}(y_0)\) is finite.  For any selected open
  neighborhood of each old-fiber point, every sufficiently nearby fiber meets
  every selected neighborhood.
proof:
  The map \(F\) is open by the open mapping theorem.  Apply the general
  finite-fiber neighborhood result for open maps.
-/
theorem eventually_forall_fiber_neighborhood_exists_of_holomorphicMap_to_openComplexModel
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_open : Topology.IsOpenEmbedding φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hnonconstant : (Set.range fun x : X ↦ φ (F x)).Nontrivial)
    {y₀ : Y} {U : X → Set X}
    (hU : ∀ x₀ : X, F x₀ = y₀ → x₀ ∈ U x₀ ∧ IsOpen (U x₀))
    (hfinite : {x : X | F x = y₀}.Finite) :
    ∀ᶠ y in 𝓝 y₀,
      ∀ x₀ : {x : X | F x = y₀},
        ∃ z : X, z ∈ U x₀.1 ∧ F z = y := by
  exact eventually_forall_fiber_neighborhood_exists_of_isOpenMap
    (nonconstant_holomorphicMap_to_openComplexModel_isOpenMap
      hφ_open hF hnonconstant)
    hU hfinite

/--
%%handwave
name:
  Fiber-neighborhood data for local degree constancy
statement:
  Let \(F:X\to Y\) be proper, with a nonconstant holomorphic expression in an
  open complex target model, and suppose \(F^{-1}(y_0)\) is finite.  There are
  pairwise disjoint open neighborhoods \(U_x\) of the old-fiber points such
  that, for every sufficiently nearby \(y\): the fiber \(F^{-1}(y)\) is
  contained in their union; each nearby preimage lies in a unique \(U_x\);
  and every \(U_x\) is met by the nearby fiber.
proof:
  Properness supplies disjoint old-fiber neighborhoods whose union captures
  nearby fibers.  Pairwise disjointness gives unique assignment, while the
  open mapping theorem guarantees that each selected neighborhood continues
  to meet every nearby fiber.
-/
theorem proper_holomorphicMap_to_openComplexModel_eventually_fiber_neighborhood_data
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_open : Topology.IsOpenEmbedding φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hproper : IsProperMap F)
    (hnonconstant : (Set.range fun x : X ↦ φ (F x)).Nontrivial)
    {y₀ : Y} (hfinite : {x : X | F x = y₀}.Finite) :
    ∃ U : X → Set X,
      (∀ x : X, x ∈ {x : X | F x = y₀} → x ∈ U x ∧ IsOpen (U x)) ∧
        ({x : X | F x = y₀}.PairwiseDisjoint U) ∧
          ∀ᶠ y in 𝓝 y₀,
            {x : X | F x = y} ⊆
              ⋃ x : {x : X | F x = y₀}, U x.1 ∧
            (∀ z : X, F z = y →
              ∃! x₀ : {x : X | F x = y₀}, z ∈ U x₀.1) ∧
            (∀ x₀ : {x : X | F x = y₀},
              ∃ z : X, z ∈ U x₀.1 ∧ F z = y) := by
  rcases properMap_finite_fiber_exists_pairwiseDisjoint_open_nhds_eventually
      hproper y₀ hfinite with ⟨U, hU, hpair, hcover_event⟩
  have hhit_event :
      ∀ᶠ y in 𝓝 y₀,
        ∀ x₀ : {x : X | F x = y₀},
          ∃ z : X, z ∈ U x₀.1 ∧ F z = y :=
    eventually_forall_fiber_neighborhood_exists_of_holomorphicMap_to_openComplexModel
      hφ_open hF hnonconstant hU hfinite
  refine ⟨U, hU, hpair, ?_⟩
  filter_upwards [hcover_event, hhit_event] with y hcover hhit
  refine ⟨hcover, ?_, hhit⟩
  intro z hz
  exact existsUnique_fiber_neighborhood_of_mem_fiber_subset_pairwiseDisjoint
    hpair hcover hz

/--
The local multiplicity of a complex-valued holomorphic map at a source point,
with respect to a chosen source coordinate and target value.
-/
noncomputable def holomorphicMapLocalOrderAtValueInCoordinate
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x : X} (χ : PointedSurfaceCoordinate X x) (F : X → ℂ) (a : ℂ) : ℕ∞ :=
  analyticOrderAt (fun z : ℂ ↦ F (χ.chart.symm z) - a) (χ.chart x)

/-- The local analytic order at the value of the point itself. -/
noncomputable def holomorphicMapLocalOrderInCoordinate
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x : X} (χ : PointedSurfaceCoordinate X x) (F : X → ℂ) : ℕ∞ :=
  holomorphicMapLocalOrderAtValueInCoordinate χ F (F x)

/--
%%handwave
name:
  An injective map has finite local analytic order
statement:
  Let \(F:X\to\mathbb C\) be injective and let \(\chi\) be a pointed
  coordinate at \(x\).  Then the local analytic order of
  \(F\circ\chi^{-1}-F(x)\) at \(\chi(x)\) is not infinite.
proof:
  Infinite analytic order would make the coordinate expression equal to
  \(F(x)\) on a neighborhood of \(\chi(x)\).  A punctured neighborhood
  contains a point distinct from \(\chi(x)\), giving a distinct source point
  with the same value and contradicting injectivity.
-/
theorem holomorphicMapLocalOrderInCoordinate_ne_top_of_injective
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x : X} (χ : PointedSurfaceCoordinate X x) {F : X → ℂ}
    (hinj : Function.Injective F) :
    holomorphicMapLocalOrderInCoordinate χ F ≠ ⊤ := by
  let fcoord : ℂ → ℂ := fun z : ℂ ↦ F (χ.chart.symm z) - F x
  let z₀ : ℂ := χ.chart x
  intro htop
  have hzero :
      ∀ᶠ z in 𝓝 z₀, fcoord z = 0 := by
    simpa [holomorphicMapLocalOrderInCoordinate,
      holomorphicMapLocalOrderAtValueInCoordinate, fcoord, z₀]
      using (analyticOrderAt_eq_top.mp htop)
  have htarget : χ.chart.target ∈ 𝓝 z₀ := by
    dsimp [z₀]
    exact χ.chart.open_target.mem_nhds
      (χ.chart.map_source χ.base_mem_source)
  let S : Set ℂ :=
    χ.chart.target ∩ {z : ℂ | fcoord z = 0} ∩ {z : ℂ | z ≠ z₀}
  have hS_mem : S ∈ 𝓝[≠] z₀ := by
    refine Filter.inter_mem ?_ self_mem_nhdsWithin
    exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds htarget)
      (mem_nhdsWithin_of_mem_nhds hzero)
  haveI : Filter.NeBot (𝓝[≠] z₀) := inferInstance
  rcases Filter.nonempty_of_mem hS_mem with ⟨z, hzS⟩
  rcases hzS with ⟨hz_target_zero, hz_ne⟩
  rcases hz_target_zero with ⟨hz_target, hz_zero⟩
  have hF_eq : F (χ.chart.symm z) = F x := by
    simpa [fcoord] using sub_eq_zero.mp hz_zero
  have hsymm_eq : χ.chart.symm z = x := hinj hF_eq
  have hz_eq : z = z₀ := by
    calc
      z = χ.chart (χ.chart.symm z) := (χ.chart.right_inv hz_target).symm
      _ = χ.chart x := by rw [hsymm_eq]
      _ = z₀ := rfl
  exact hz_ne hz_eq

/--
The natural-number local multiplicity of a complex-valued holomorphic map at a
source point, with respect to a chosen source coordinate and target value.
-/
noncomputable def holomorphicMapLocalMultiplicityAtValueInCoordinate
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x : X} (χ : PointedSurfaceCoordinate X x) (F : X → ℂ) (a : ℂ) : ℕ :=
  analyticOrderNatAt (fun z : ℂ ↦ F (χ.chart.symm z) - a) (χ.chart x)

/-- The local multiplicity at the value of the point itself. -/
noncomputable def holomorphicMapLocalMultiplicityInCoordinate
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x : X} (χ : PointedSurfaceCoordinate X x) (F : X → ℂ) : ℕ :=
  holomorphicMapLocalMultiplicityAtValueInCoordinate χ F (F x)

/--
%%handwave
name:
  Injectivity of a surface map in source coordinates
statement:
  If \(F:X\to\mathbb C\) is injective and \(\chi\) is a pointed coordinate,
  then \(z\mapsto F(\chi^{-1}(z))\) is injective on the chart target.
proof:
  Equality of two coordinate-expression values gives equality of their
  inverse-chart source points by injectivity of \(F\).  Applying the chart and
  using its right inverse recovers equality of the coordinate points.
-/
theorem coordinateExpression_injOn_chartTarget_of_injective
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x : X} (χ : PointedSurfaceCoordinate X x) {F : X → ℂ}
    (hinj : Function.Injective F) :
    Set.InjOn (fun z : ℂ ↦ F (χ.chart.symm z)) χ.chart.target := by
  intro z hz w hw hzw
  have hsymm_eq : χ.chart.symm z = χ.chart.symm w := hinj hzw
  calc
    z = χ.chart (χ.chart.symm z) := (χ.chart.right_inv hz).symm
    _ = χ.chart (χ.chart.symm w) := by rw [hsymm_eq]
    _ = w := χ.chart.right_inv hw

/--
%%handwave
name:
  Injectivity of the coordinate difference of an injective map
statement:
  If \(F:X\to\mathbb C\) is injective, then
  \(z\mapsto F(\chi^{-1}(z))-F(x)\) is injective on the chart target of a
  pointed coordinate \(\chi\) at \(x\).
proof:
  Addition of the constant \(F(x)\) cancels the subtraction, reducing equality
  of the differences to equality of the injective coordinate expression.
-/
theorem coordinateDifference_injOn_chartTarget_of_injective
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {x : X} (χ : PointedSurfaceCoordinate X x) {F : X → ℂ}
    (hinj : Function.Injective F) :
    Set.InjOn (fun z : ℂ ↦ F (χ.chart.symm z) - F x) χ.chart.target := by
  intro z hz w hw hzw
  apply coordinateExpression_injOn_chartTarget_of_injective χ hinj hz hw
  have hcancel := congr_arg (fun t : ℂ ↦ t + F x) hzw
  simpa [sub_eq_add_neg, add_assoc] using hcancel

/--
%%handwave
name:
  Factorization of a finite-order coordinate germ
statement:
  Let \(F:X\to\mathbb C\) be holomorphic and let \(\chi\) be pointed at
  \(x\).  If \(F\circ\chi^{-1}-a\) has finite analytic order at
  \(z_0=\chi(x)\), then there is a function \(g\), analytic near \(z_0\) with
  \(g(z_0)\ne0\), such that
  \[
    F(\chi^{-1}(z))-a=(z-z_0)^n g(z)
  \]
  near \(z_0\), where \(n\) is the local multiplicity.
proof:
  The coordinate expression is analytic by holomorphicity of \(F\).  Apply
  the standard analytic factorization theorem for a zero of finite order and
  identify the natural order with the defined local multiplicity.
-/
theorem holomorphicMapLocalOrderAtValueInCoordinate_factorization_of_ne_top
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {x : X} (χ : PointedSurfaceCoordinate X x)
    {F : X → ℂ} {a : ℂ}
    (hF : HolomorphicMap X ℂ F)
    (hfinite : holomorphicMapLocalOrderAtValueInCoordinate χ F a ≠ ⊤) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g (χ.chart x) ∧ g (χ.chart x) ≠ 0 ∧
        (fun z : ℂ ↦ F (χ.chart.symm z) - a) =ᶠ[𝓝 (χ.chart x)]
          fun z : ℂ ↦ (z - χ.chart x) ^
            holomorphicMapLocalMultiplicityAtValueInCoordinate χ F a * g z := by
  let fcoord : ℂ → ℂ := fun z : ℂ ↦ F (χ.chart.symm z) - a
  let z₀ : ℂ := χ.chart x
  have hbase :
      AnalyticAt ℂ (fun z : ℂ ↦ F (χ.chart.symm z)) z₀ := by
    simpa [z₀] using
      surface_coordinateExpression_analyticAt
        (X := X) (f := F) hF χ.chart_mem_atlas χ.base_mem_source
  have hfcoord : AnalyticAt ℂ fcoord z₀ := by
    simpa [fcoord] using hbase.sub analyticAt_const
  have hfinite_coord : analyticOrderAt fcoord z₀ ≠ ⊤ := by
    simpa [holomorphicMapLocalOrderAtValueInCoordinate, fcoord, z₀] using hfinite
  rcases (hfcoord.analyticOrderAt_ne_top).mp hfinite_coord with
    ⟨g, hg, hg_ne, hfactor⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa [z₀] using hg
  · simpa [z₀] using hg_ne
  · simpa [fcoord, z₀, holomorphicMapLocalMultiplicityAtValueInCoordinate,
      smul_eq_mul] using hfactor

/--
%%handwave
name:
  Factorization at the image value in a pointed coordinate
statement:
  If the local analytic order of \(F-F(x)\) at \(x\) is finite, then in a
  pointed coordinate \(z_0=\chi(x)\),
  \[
    F(\chi^{-1}(z))-F(x)=(z-z_0)^n g(z)
  \]
  near \(z_0\), where \(g\) is analytic, \(g(z_0)\ne0\), and \(n\) is the
  local multiplicity.
proof:
  Apply the finite-order factorization theorem with target value \(a=F(x)\).
-/
theorem holomorphicMapLocalOrderInCoordinate_factorization_of_ne_top
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {x : X} (χ : PointedSurfaceCoordinate X x)
    {F : X → ℂ}
    (hF : HolomorphicMap X ℂ F)
    (hfinite : holomorphicMapLocalOrderInCoordinate χ F ≠ ⊤) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g (χ.chart x) ∧ g (χ.chart x) ≠ 0 ∧
        (fun z : ℂ ↦ F (χ.chart.symm z) - F x) =ᶠ[𝓝 (χ.chart x)]
          fun z : ℂ ↦ (z - χ.chart x) ^
            holomorphicMapLocalMultiplicityInCoordinate χ F * g z := by
  simpa [holomorphicMapLocalOrderInCoordinate,
    holomorphicMapLocalMultiplicityInCoordinate] using
    holomorphicMapLocalOrderAtValueInCoordinate_factorization_of_ne_top
      χ hF hfinite

/--
%%handwave
name:
  A noncritical zero has local multiplicity one
statement:
  Let \(F:X\to\mathbb C\) be holomorphic with \(F(x)=a\).  If the complex
  derivative of \(F\) in a pointed coordinate at \(x\) is nonzero, then the
  local multiplicity of \(F-a\) at \(x\) is one.
proof:
  The coordinate germ vanishes at the base point and has nonzero first
  derivative.  The analytic-order criterion therefore gives order exactly
  one, whose natural value is the local multiplicity.
-/
theorem holomorphicMapLocalMultiplicityAtValueInCoordinate_eq_one_of_deriv_ne_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {x : X} (χ : PointedSurfaceCoordinate X x)
    {F : X → ℂ} {a : ℂ}
    (hF : HolomorphicMap X ℂ F) (hxa : F x = a)
    (hderiv : surfaceComplexDerivativeInCoordinate χ F ≠ 0) :
    holomorphicMapLocalMultiplicityAtValueInCoordinate χ F a = 1 := by
  let fcoord : ℂ → ℂ := fun z : ℂ ↦ F (χ.chart.symm z) - a
  let z₀ : ℂ := χ.chart x
  have hbase :
      AnalyticAt ℂ (fun z : ℂ ↦ F (χ.chart.symm z)) z₀ := by
    simpa [z₀] using
      surface_coordinateExpression_analyticAt
        (X := X) (f := F) hF χ.chart_mem_atlas χ.base_mem_source
  have hfcoord : AnalyticAt ℂ fcoord z₀ := by
    simpa [fcoord] using hbase.sub analyticAt_const
  have hleft : χ.chart.symm (χ.chart x) = x :=
    χ.chart.left_inv χ.base_mem_source
  have hfcoord_zero : fcoord z₀ = 0 := by
    simp [fcoord, z₀, hleft, hxa]
  have hderiv_coord : deriv fcoord z₀ ≠ 0 := by
    simpa [fcoord, z₀, surfaceComplexDerivativeInCoordinate, deriv_sub_const]
      using hderiv
  have horder :
      analyticOrderAt fcoord z₀ = (1 : ℕ) :=
    hfcoord.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      hfcoord_zero hderiv_coord
  simp [holomorphicMapLocalMultiplicityAtValueInCoordinate, fcoord, z₀,
    analyticOrderNatAt, horder]

/--
%%handwave
name:
  A noncritical point has multiplicity one at its image
statement:
  If a holomorphic map has nonzero coordinate derivative at \(x\), then its
  local multiplicity over the value \(F(x)\) is one.
proof:
  Apply the noncritical-zero result to the value \(a=F(x)\).
-/
theorem holomorphicMapLocalMultiplicityInCoordinate_eq_one_of_deriv_ne_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {x : X} (χ : PointedSurfaceCoordinate X x)
    {F : X → ℂ}
    (hF : HolomorphicMap X ℂ F)
    (hderiv : surfaceComplexDerivativeInCoordinate χ F ≠ 0) :
    holomorphicMapLocalMultiplicityInCoordinate χ F = 1 := by
  exact
    holomorphicMapLocalMultiplicityAtValueInCoordinate_eq_one_of_deriv_ne_zero
      χ hF rfl hderiv

/--
%%handwave
name:
  A point of a finite fiber has finite local order
statement:
  If \(F^{-1}(a)\) is finite and \(F(x)=a\), then in every pointed coordinate
  at \(x\), the analytic order of \(F-a\) is not infinite.
proof:
  Infinite order would make the coordinate germ identically zero near the
  base point.  After removing the finitely many other points of the fiber,
  choose a distinct coordinate point in this zero neighborhood; its inverse
  chart point is a new point of the fiber, a contradiction.
-/
theorem holomorphicMapLocalOrderAtValueInCoordinate_ne_top_of_finite_fiber
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {x : X} (χ : PointedSurfaceCoordinate X x)
    {F : X → ℂ} {a : ℂ}
    (hfinite : {y : X | F y = a}.Finite) (_hx : F x = a) :
    holomorphicMapLocalOrderAtValueInCoordinate χ F a ≠ ⊤ := by
  classical
  let z₀ : ℂ := χ.chart x
  intro htop
  have hzero :
      ∀ᶠ z in 𝓝 z₀, F (χ.chart.symm z) - a = 0 := by
    simpa [holomorphicMapLocalOrderAtValueInCoordinate, z₀]
      using (analyticOrderAt_eq_top.mp htop)
  let S : Set X := {y : X | F y = a} \ {x}
  have hS_finite : S.Finite :=
    hfinite.subset (by
      intro y hy
      exact hy.1)
  have hS_closed : IsClosed S := hS_finite.isClosed
  have hx_not_S : x ∉ S := by
    simp [S]
  have hnotS_nhds : Sᶜ ∈ 𝓝 x :=
    hS_closed.isOpen_compl.mem_nhds hx_not_S
  have hz₀_target : z₀ ∈ χ.chart.target := by
    dsimp [z₀]
    exact χ.chart.map_source χ.base_mem_source
  have hsymm_z₀ : χ.chart.symm z₀ = x := by
    simpa [z₀] using χ.chart.left_inv χ.base_mem_source
  have hnotS_nhds_z₀ : Sᶜ ∈ 𝓝 (χ.chart.symm z₀) := by
    simpa [hsymm_z₀] using hnotS_nhds
  have hpre_notS : χ.chart.symm ⁻¹' Sᶜ ∈ 𝓝 z₀ :=
    χ.chart.continuousAt_symm hz₀_target hnotS_nhds_z₀
  have htarget : χ.chart.target ∈ 𝓝 z₀ :=
    χ.chart.open_target.mem_nhds hz₀_target
  let U : Set ℂ :=
    χ.chart.target ∩ χ.chart.symm ⁻¹' Sᶜ ∩
      {z : ℂ | F (χ.chart.symm z) - a = 0}
  have hU_nhds : U ∈ 𝓝 z₀ := by
    exact Filter.inter_mem
      (Filter.inter_mem htarget hpre_notS) hzero
  have hUne : U ∩ {z : ℂ | z ≠ z₀} ∈ 𝓝[≠] z₀ := by
    exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hU_nhds)
      self_mem_nhdsWithin
  haveI : Filter.NeBot (𝓝[≠] z₀) := inferInstance
  rcases Filter.nonempty_of_mem hUne with ⟨z, hz⟩
  rcases hz with ⟨hzU, hz_ne⟩
  rcases hzU with ⟨hz_target_notS, hz_zero⟩
  rcases hz_target_notS with ⟨hz_target, hz_notS⟩
  have hfiber : F (χ.chart.symm z) = a := sub_eq_zero.mp hz_zero
  have hsymm_ne : χ.chart.symm z ≠ x := by
    intro hsymm
    have hz_eq : z = z₀ := by
      calc
        z = χ.chart (χ.chart.symm z) := (χ.chart.right_inv hz_target).symm
        _ = χ.chart x := by rw [hsymm]
        _ = z₀ := rfl
    exact hz_ne hz_eq
  exact hz_notS ⟨hfiber, by simpa [Set.mem_singleton_iff] using hsymm_ne⟩

/--
%%handwave
name:
  Positivity of local multiplicity in a finite fiber
statement:
  Let \(F:X\to\mathbb C\) be holomorphic, let \(F(x)=a\), and suppose
  \(F^{-1}(a)\) is finite.  Then the local multiplicity of \(F-a\) at \(x\)
  is at least one.
proof:
  The analytic coordinate germ vanishes at the base point, so its order is
  nonzero.  Finiteness of the fiber rules out infinite order.  Thus its
  natural-number order, which is the local multiplicity, is positive.
-/
theorem one_le_holomorphicMapLocalMultiplicityAtValueInCoordinate_of_mem_finite_fiber
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {x : X} (χ : PointedSurfaceCoordinate X x)
    {F : X → ℂ} {a : ℂ}
    (hF : HolomorphicMap X ℂ F)
    (hfinite : {y : X | F y = a}.Finite) (hx : F x = a) :
    1 ≤ holomorphicMapLocalMultiplicityAtValueInCoordinate χ F a := by
  let fcoord : ℂ → ℂ := fun z : ℂ ↦ F (χ.chart.symm z) - a
  let z₀ : ℂ := χ.chart x
  have hbase :
      AnalyticAt ℂ (fun z : ℂ ↦ F (χ.chart.symm z)) z₀ := by
    simpa [z₀] using
      surface_coordinateExpression_analyticAt
        (X := X) (f := F) hF χ.chart_mem_atlas χ.base_mem_source
  have hfcoord : AnalyticAt ℂ fcoord z₀ := by
    simpa [fcoord] using hbase.sub analyticAt_const
  have hleft : χ.chart.symm (χ.chart x) = x :=
    χ.chart.left_inv χ.base_mem_source
  have hfcoord_zero : fcoord z₀ = 0 := by
    simp [fcoord, z₀, hleft, hx]
  have horder_ne_zero : analyticOrderAt fcoord z₀ ≠ 0 := by
    exact analyticOrderAt_ne_zero.mpr ⟨hfcoord, hfcoord_zero⟩
  have horder_ne_top :
      analyticOrderAt fcoord z₀ ≠ ⊤ := by
    simpa [holomorphicMapLocalOrderAtValueInCoordinate, fcoord, z₀] using
      holomorphicMapLocalOrderAtValueInCoordinate_ne_top_of_finite_fiber
        χ hfinite hx
  have hcast :
      (holomorphicMapLocalMultiplicityAtValueInCoordinate χ F a : ℕ∞) =
        analyticOrderAt fcoord z₀ := by
    rw [holomorphicMapLocalMultiplicityAtValueInCoordinate]
    simpa [fcoord, z₀] using Nat.cast_analyticOrderNatAt horder_ne_top
  have hmult_ne_zero :
      holomorphicMapLocalMultiplicityAtValueInCoordinate χ F a ≠ 0 := by
    intro hzero_mult
    apply horder_ne_zero
    rw [← hcast, hzero_mult]
    simp
  exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hmult_ne_zero)

/-- The canonical coordinate used for counting local multiplicity at a point. -/
noncomputable def chartAtPointedSurfaceCoordinate
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) :
    PointedSurfaceCoordinate X x where
  chart := chartAt ℂ x
  chart_mem_atlas := chart_mem_atlas ℂ x
  base_mem_source := mem_chart_source ℂ x

/--
The fiber multiplicity sum of a complex-coordinate model of a holomorphic
map, counted in the canonical source coordinate at each point of a finite
fiber.
-/
noncomputable def holomorphicMapFiberMultiplicityInCoordinateModel
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] (F : X → Y) (φ : Y → ℂ)
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite) (y : Y) : ℕ :=
  (hfinite y).toFinset.sum fun x ↦
    holomorphicMapLocalMultiplicityAtValueInCoordinate
      (chartAtPointedSurfaceCoordinate X x)
      (fun x' : X ↦ φ (F x')) (φ y)

/--
The part of the fiber multiplicity sum coming from preimages lying in a
specified subset of the source.
-/
noncomputable def holomorphicMapFiberMultiplicityInCoordinateModelOnSet
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] (F : X → Y) (φ : Y → ℂ)
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite) (U : Set X)
    (y : Y) : ℕ := by
  classical
  exact ((hfinite y).toFinset.filter fun x ↦ x ∈ U).sum fun x ↦
    holomorphicMapLocalMultiplicityAtValueInCoordinate
      (chartAtPointedSurfaceCoordinate X x)
      (fun x' : X ↦ φ (F x')) (φ y)

/--
The corresponding local fiber-multiplicity contribution for a genuinely
complex-valued map, counted over a source subset.
-/
noncomputable def holomorphicMapComplexFiberMultiplicityOnSet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (f : X → ℂ) (hfinite : ∀ a : ℂ, {x : X | f x = a}.Finite)
    (U : Set X) (a : ℂ) : ℕ := by
  classical
  exact ((hfinite a).toFinset.filter fun x ↦ x ∈ U).sum fun x ↦
    holomorphicMapLocalMultiplicityAtValueInCoordinate
      (chartAtPointedSurfaceCoordinate X x) f a

/--
%%handwave
name:
  Multiplicity in an isolating set equals the isolated local multiplicity
statement:
  Let \(f:X\to\mathbb C\) have finite fibers, with \(f(x_0)=a_0\).  If a set
  \(U\) contains \(x_0\) and
  \(U\cap f^{-1}(a_0)\subseteq\{x_0\}\), then the total multiplicity of the
  old fiber inside \(U\) equals the local multiplicity of \(f-a_0\) at
  \(x_0\).
proof:
  The isolation and membership hypotheses identify the filtered finite fiber
  inside \(U\) with the singleton \(\{x_0\}\).  Its multiplicity sum therefore
  consists of the single local summand at \(x_0\).
-/
theorem holomorphicMapComplexFiberMultiplicityOnSet_eq_localMultiplicity_at_base
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {f : X → ℂ}
    (hfinite : ∀ a : ℂ, {x : X | f x = a}.Finite)
    {a₀ : ℂ} {U : Set X} {x₀ : X}
    (hx₀U : x₀ ∈ U) (hx₀ : f x₀ = a₀)
    (hisolating : U ∩ {x : X | f x = a₀} ⊆ {x₀}) :
    holomorphicMapComplexFiberMultiplicityOnSet f hfinite U a₀ =
      holomorphicMapLocalMultiplicityAtValueInCoordinate
        (chartAtPointedSurfaceCoordinate X x₀) f a₀ := by
  classical
  let s : Finset X := (hfinite a₀).toFinset
  have hfilter : (s.filter fun x ↦ x ∈ U) = ({x₀} : Finset X) := by
    ext z
    constructor
    · intro hz
      have hz_fiber : f z = a₀ :=
        (hfinite a₀).mem_toFinset.mp (Finset.mem_filter.mp hz).1
      have hzU : z ∈ U := (Finset.mem_filter.mp hz).2
      have hz_eq : z = x₀ := by
        exact Set.mem_singleton_iff.mp (hisolating ⟨hzU, hz_fiber⟩)
      simp [hz_eq]
    · intro hz
      have hz_eq : z = x₀ := by
        simpa using hz
      rw [hz_eq]
      exact Finset.mem_filter.mpr
        ⟨(hfinite a₀).mem_toFinset.mpr hx₀, hx₀U⟩
  simp [holomorphicMapComplexFiberMultiplicityOnSet, s, hfilter]

/--
%%handwave
name:
  Fiber multiplicity depends only on membership along the fiber
statement:
  Let \(f:X\to\mathbb C\) have finite fibers.  If two sets \(U,W\subseteq X\)
  contain exactly the same points of \(f^{-1}(a)\), then the total local
  multiplicity of that fiber in \(U\) equals its total multiplicity in \(W\).
proof:
  The membership equivalence makes the two filtered finite fiber sets equal.
  The multiplicity sums over these equal finite sets are identical.
-/
theorem holomorphicMapComplexFiberMultiplicityOnSet_eq_of_mem_iff_on_fiber
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {f : X → ℂ}
    (hfinite : ∀ a : ℂ, {x : X | f x = a}.Finite)
    {U W : Set X} {a : ℂ}
    (hmem : ∀ x : X, f x = a → (x ∈ U ↔ x ∈ W)) :
    holomorphicMapComplexFiberMultiplicityOnSet f hfinite U a =
      holomorphicMapComplexFiberMultiplicityOnSet f hfinite W a := by
  classical
  have hfilter :
      ((hfinite a).toFinset.filter fun x ↦ x ∈ U) =
        ((hfinite a).toFinset.filter fun x ↦ x ∈ W) := by
    ext x
    constructor
    · intro hx
      have hxa : f x = a := (hfinite a).mem_toFinset.mp (Finset.mem_filter.mp hx).1
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hx).1, (hmem x hxa).mp (Finset.mem_filter.mp hx).2⟩
    · intro hx
      have hxa : f x = a := (hfinite a).mem_toFinset.mp (Finset.mem_filter.mp hx).1
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hx).1, (hmem x hxa).mpr (Finset.mem_filter.mp hx).2⟩
  simp [holomorphicMapComplexFiberMultiplicityOnSet, hfilter]

/--
A complex-valued map is proper over a neighborhood of a value if compact
subsets of some neighborhood of that value have compact preimage.
-/
def IsProperOverComplexNeighborhood
    {X : Type} [TopologicalSpace X] (f : X → ℂ) (a₀ : ℂ) : Prop :=
  ∃ V : Set ℂ, V ∈ 𝓝 a₀ ∧
    ∀ K : Set ℂ, IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K)

/--
%%handwave
name:
  Fiberwise neighborhood control from local properness
statement:
  Let \(f:X\to\mathbb C\) be continuous and proper over a neighborhood of
  \(a_0\).  Suppose a property \(P\) holds near every point of
  \(f^{-1}(a_0)\).  Then for all \(a\) sufficiently close to \(a_0\), every
  point of \(f^{-1}(a)\) satisfies \(P\).
proof:
  Restrict to the compact preimage of a small closed ball about \(a_0\).
  There the restricted map is a continuous map from a compact space and hence
  closed.  The closed-map fiber-neighborhood theorem propagates the local
  property to nearby fibers; shrinking the target neighborhood keeps every
  such fiber inside the compact restriction.
-/
theorem eventually_fiber_forall_of_isProperOverComplexNeighborhood
    {X : Type} [TopologicalSpace X] {f : X → ℂ} {a₀ : ℂ}
    (hfcont : Continuous f)
    (hproper_local : IsProperOverComplexNeighborhood f a₀)
    {p : X → Prop}
    (hp : ∀ x : X, f x = a₀ → ∀ᶠ y in 𝓝 x, p y) :
    ∀ᶠ a in 𝓝 a₀, ∀ x : X, f x = a → p x := by
  rcases hproper_local with ⟨V, hV, hproperV⟩
  rcases Metric.nhds_basis_closedBall.mem_iff.mp hV with ⟨r, hr, hclosed_sub⟩
  let K : Set ℂ := Metric.closedBall a₀ r
  let L : Set X := f ⁻¹' K
  have hK_compact : IsCompact K := isCompact_closedBall a₀ r
  have hL_compact : IsCompact L := hproperV K hK_compact hclosed_sub
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hL_compact
  let g : L → ℂ := fun x ↦ f x.1
  have hg_cont : Continuous g := hfcont.comp continuous_subtype_val
  have hclosed : IsClosedMap g := hg_cont.isClosedMap
  have hfiber_event :
      ∀ᶠ a in 𝓝 a₀, ∀ x : L, g x = a → p x.1 := by
    have H :
        ∀ x₀ ∈ g ⁻¹' {a₀}, ∀ᶠ x in 𝓝 x₀, p x.1 := by
      intro x₀ hx₀
      have hx₀_fiber : f x₀.1 = a₀ := by
        simpa [g, Set.mem_preimage, Set.mem_singleton_iff] using hx₀
      exact continuous_subtype_val.continuousAt (hp x₀.1 hx₀_fiber)
    filter_upwards [hclosed.eventually_nhds_fiber a₀ H] with a ha x hx
    exact ha x (by
      simpa [g, Set.mem_preimage, Set.mem_singleton_iff] using hx)
  filter_upwards [hfiber_event, Metric.closedBall_mem_nhds a₀ hr] with a ha haK x hx
  have hxL : x ∈ L := by
    have hxK : f x ∈ K := by
      rw [hx]
      exact haK
    simpa [L] using hxK
  exact ha ⟨x, hxL⟩ (by simpa [g] using hx)

/--
%%handwave
name:
  Nearby fibers lie in any open neighborhood of a locally proper fiber
statement:
  Let \(f:X\to\mathbb C\) be continuous and proper over a neighborhood of
  \(a_0\).  If an open set \(U\) contains \(f^{-1}(a_0)\), then
  \(f^{-1}(a)\subseteq U\) for every sufficiently close \(a\) to \(a_0\).
proof:
  Apply fiberwise neighborhood control to the property of belonging to
  \(U\).  Openness makes this property hold on a neighborhood of every old
  fiber point.
-/
theorem eventually_fiber_subset_open_of_isProperOverComplexNeighborhood
    {X : Type} [TopologicalSpace X] {f : X → ℂ} {a₀ : ℂ}
    (hfcont : Continuous f)
    (hproper_local : IsProperOverComplexNeighborhood f a₀)
    {U : Set X} (hU_open : IsOpen U)
    (hcover : {x : X | f x = a₀} ⊆ U) :
    ∀ᶠ a in 𝓝 a₀, {x : X | f x = a} ⊆ U := by
  filter_upwards
    [eventually_fiber_forall_of_isProperOverComplexNeighborhood
      hfcont hproper_local
      (fun x hx ↦ hU_open.mem_nhds (hcover hx))] with a ha x hx
  exact ha x hx

/--
%%handwave
name:
  Properness over complex neighborhoods from a proper open-model map
statement:
  Let \(F:X\to Y\) be proper and let
  \(\varphi:Y\to\mathbb C\) be an open embedding.  For every \(y_0\in Y\),
  the coordinate expression \(\varphi\circ F\) is proper over the complex
  neighborhood \(\varphi(Y)\) of \(\varphi(y_0)\).
proof:
  A compact subset of the open range of \(\varphi\) has compact preimage in
  \(Y\) because \(\varphi\) is an inducing embedding.  Properness of \(F\)
  then makes its preimage in \(X\) compact.
-/
theorem isProperOverComplexNeighborhood_of_proper_openComplexModel
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_open : Topology.IsOpenEmbedding φ)
    (hproper : IsProperMap F) (y₀ : Y) :
    IsProperOverComplexNeighborhood
      (fun x : X ↦ φ (F x)) (φ y₀) := by
  refine ⟨Set.range φ, hφ_open.isOpen_range.mem_nhds ⟨y₀, rfl⟩, ?_⟩
  intro K hK hK_range
  have hpre_compact : IsCompact (φ ⁻¹' K) :=
    hφ_open.isInducing.isCompact_preimage' hK hK_range
  simpa [Set.preimage, Function.comp_def] using
    hproper.isCompact_preimage hpre_compact

/--
%%handwave
name:
  Finite fibers persist in an injective complex model
statement:
  Let \(F:X\to Y\) have finite fibers and let
  \(\varphi:Y\to\mathbb C\) be injective.  Then every level set
  \(\{x:\varphi(F(x))=a\}\) is finite.
proof:
  If \(a=\varphi(y)\), injectivity identifies this level set with a subset of
  the finite fiber \(F^{-1}(y)\).  If \(a\) is outside the range of
  \(\varphi\), the level set is empty.
-/
theorem finite_complexModel_fiber_of_finite_target_fibers
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_inj : Function.Injective φ)
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite) :
    ∀ a : ℂ, {x : X | φ (F x) = a}.Finite := by
  classical
  intro a
  by_cases ha : ∃ y : Y, φ y = a
  · rcases ha with ⟨y, rfl⟩
    exact (hfinite y).subset (by
      intro x hx
      exact hφ_inj hx)
  · have hempty : {x : X | φ (F x) = a} = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (ha ⟨F x, hx⟩)
      · intro hx
        cases hx
    rw [hempty]
    exact Set.finite_empty

/--
%%handwave
name:
  Coordinate-model fiber multiplicity equals complex level multiplicity
statement:
  Let \(F:X\to Y\) have finite fibers and let
  \(\varphi:Y\to\mathbb C\) be injective.  For any \(U\subseteq X\) and
  \(y\in Y\), the sum of local multiplicities of \(F^{-1}(y)\cap U\) equals
  the corresponding level-set multiplicity of \(\varphi\circ F\) at
  \(\varphi(y)\) in \(U\).
proof:
  Injectivity of \(\varphi\) identifies the two finite fibers pointwise, and
  both definitions use the same local coordinate multiplicity at each point.
-/
theorem holomorphicMapFiberMultiplicityInCoordinateModelOnSet_eq_complexFiberMultiplicity
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_inj : Function.Injective φ)
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    (U : Set X) (y : Y) :
    holomorphicMapFiberMultiplicityInCoordinateModelOnSet F φ hfinite U y =
      holomorphicMapComplexFiberMultiplicityOnSet
        (fun x : X ↦ φ (F x))
        (finite_complexModel_fiber_of_finite_target_fibers hφ_inj hfinite)
        U (φ y) := by
  classical
  have hfiber :
      ((finite_complexModel_fiber_of_finite_target_fibers
          (F := F) (φ := φ) hφ_inj hfinite (φ y)).toFinset) =
        (hfinite y).toFinset := by
    ext x
    constructor
    · intro hx
      exact (hfinite y).mem_toFinset.mpr
        (hφ_inj ((finite_complexModel_fiber_of_finite_target_fibers
          (F := F) (φ := φ) hφ_inj hfinite (φ y)).mem_toFinset.mp hx))
    · intro hx
      have hxF : F x = y := (hfinite y).mem_toFinset.mp hx
      exact (finite_complexModel_fiber_of_finite_target_fibers
        (F := F) (φ := φ) hφ_inj hfinite (φ y)).mem_toFinset.mpr
        (by simp [hxF])
  simp [holomorphicMapFiberMultiplicityInCoordinateModelOnSet,
    holomorphicMapComplexFiberMultiplicityOnSet, hfiber]

/--
%%handwave
name:
  Decomposition of fiber multiplicity over disjoint old-fiber neighborhoods
statement:
  Let the finite fiber \(F^{-1}(y_0)\) have pairwise disjoint neighborhoods
  \((U_{x_0})\).  If another finite fiber \(F^{-1}(y)\) is contained in their
  union, then its total multiplicity is the sum, over
  \(x_0\in F^{-1}(y_0)\), of the multiplicities contributed inside
  \(U_{x_0}\).
proof:
  Every point of the new fiber lies in exactly one of the pairwise disjoint
  neighborhoods.  Partition the finite sum of its local multiplicities by
  this unique neighborhood.
-/
theorem holomorphicMapFiberMultiplicityInCoordinateModel_eq_sum_on_fiber_neighborhoods
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    {y₀ y : Y} {U : X → Set X}
    (hpair : ({x : X | F x = y₀}.PairwiseDisjoint U))
    (hcover : {x : X | F x = y} ⊆
      ⋃ x : {x : X | F x = y₀}, U x.1) :
    holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y =
      (hfinite y₀).toFinset.sum fun x₀ ↦
        holomorphicMapFiberMultiplicityInCoordinateModelOnSet
          F φ hfinite (U x₀) y := by
  classical
  let s : Finset X := (hfinite y).toFinset
  let t : Finset X := (hfinite y₀).toFinset
  let m : X → ℕ := fun x ↦
    holomorphicMapLocalMultiplicityAtValueInCoordinate
      (chartAtPointedSurfaceCoordinate X x)
      (fun x' : X ↦ φ (F x')) (φ y)
  have hunique :
      ∀ z ∈ s, ∃! x₀ : X, x₀ ∈ t ∧ z ∈ U x₀ := by
    intro z hz
    have hz_fiber : F z = y := by
      exact (hfinite y).mem_toFinset.mp (by simpa [s] using hz)
    rcases Set.mem_iUnion.mp (hcover hz_fiber) with ⟨x₀, hzU⟩
    refine ⟨x₀.1, ?_, ?_⟩
    · exact ⟨(hfinite y₀).mem_toFinset.mpr x₀.2, hzU⟩
    · intro x₁ hx₁
      have hx₁_fiber : F x₁ = y₀ :=
        (hfinite y₀).mem_toFinset.mp (by simpa [t] using hx₁.1)
      exact
        eq_of_mem_pairwiseDisjoint_fiber_neighborhoods
          (f := F) (y₀ := y₀) (U := U) hpair
          (x₀ := x₁) (x₁ := x₀.1) (z := z)
          hx₁_fiber x₀.2 hx₁.2 hzU
  simpa [holomorphicMapFiberMultiplicityInCoordinateModel,
    holomorphicMapFiberMultiplicityInCoordinateModelOnSet, s, t, m] using
    finset_sum_eq_sum_filter_of_existsUnique s t m
      (fun z x₀ ↦ z ∈ U x₀) hunique

/--
%%handwave
name:
  Old-fiber contribution of one isolating neighborhood
statement:
  Let \((U_x)_{x\in F^{-1}(y_0)}\) be pairwise disjoint neighborhoods, each
  containing its indexed old-fiber point.  Then the multiplicity contributed
  by \(F^{-1}(y_0)\) inside \(U_{x_0}\) is exactly the local multiplicity at
  \(x_0\).
proof:
  Pairwise disjointness and the self-membership conditions show that
  \(U_{x_0}\) contains no other point of the old fiber.  The filtered finite
  sum therefore reduces to its single summand at \(x_0\).
-/
theorem holomorphicMapFiberMultiplicityInCoordinateModelOnSet_eq_localMultiplicity_at_base
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    {y₀ : Y} {U : X → Set X}
    (hU_mem : ∀ x : X, F x = y₀ → x ∈ U x)
    (hpair : ({x : X | F x = y₀}.PairwiseDisjoint U))
    (x₀ : {x : X | F x = y₀}) :
    holomorphicMapFiberMultiplicityInCoordinateModelOnSet
        F φ hfinite (U x₀.1) y₀ =
      holomorphicMapLocalMultiplicityAtValueInCoordinate
        (chartAtPointedSurfaceCoordinate X x₀.1)
        (fun x : X ↦ φ (F x)) (φ y₀) := by
  classical
  let s : Finset X := (hfinite y₀).toFinset
  let m : X → ℕ := fun x ↦
    holomorphicMapLocalMultiplicityAtValueInCoordinate
      (chartAtPointedSurfaceCoordinate X x)
      (fun x' : X ↦ φ (F x')) (φ y₀)
  have hfilter :
      (s.filter fun x ↦ x ∈ U x₀.1) = ({x₀.1} : Finset X) := by
    ext z
    constructor
    · intro hz
      have hz_fiber : F z = y₀ :=
        (hfinite y₀).mem_toFinset.mp (by
          exact (Finset.mem_filter.mp hz).1)
      have hzU : z ∈ U x₀.1 :=
        (Finset.mem_filter.mp hz).2
      have hz_eq : z = x₀.1 :=
        eq_of_old_fiber_mem_pairwiseDisjoint_fiber_neighborhood
          hU_mem hpair x₀.2 hz_fiber hzU
      simp [hz_eq]
    · intro hz
      have hz_eq : z = x₀.1 := by
        simpa using hz
      rw [hz_eq]
      exact Finset.mem_filter.mpr
        ⟨(hfinite y₀).mem_toFinset.mpr x₀.2, hU_mem x₀.1 x₀.2⟩
  simp [holomorphicMapFiberMultiplicityInCoordinateModelOnSet, s, hfilter]

/--
%%handwave
name:
  A nonempty finite fiber has positive total multiplicity
statement:
  Let \(F:X\to Y\) have finite fibers, and suppose an injective complex model
  \(\varphi:Y\to\mathbb C\) makes \(\varphi\circ F\) holomorphic.  If
  \(F(x)=y\), then the total multiplicity of the fiber over \(y\) is at least
  one.
proof:
  The local multiplicity at \(x\) is at least one because it is a finite
  zero of the holomorphic coordinate expression.  This nonnegative summand is
  bounded above by the sum over the whole finite fiber.
-/
theorem one_le_holomorphicMapFiberMultiplicityInCoordinateModel_of_mem
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_inj : Function.Injective φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    {x : X} {y : Y} (hx : F x = y) :
    1 ≤ holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y := by
  classical
  let s : Finset X := (hfinite y).toFinset
  let m : X → ℕ := fun w ↦
    holomorphicMapLocalMultiplicityAtValueInCoordinate
      (chartAtPointedSurfaceCoordinate X w)
      (fun x' : X ↦ φ (F x')) (φ y)
  have hxmem : x ∈ s := by
    simpa [s] using (hfinite y).mem_toFinset.mpr hx
  have hfinite_complex : {w : X | φ (F w) = φ y}.Finite :=
    (hfinite y).subset (by
      intro w hw
      exact hφ_inj hw)
  have hxpos : 1 ≤ m x := by
    exact
      one_le_holomorphicMapLocalMultiplicityAtValueInCoordinate_of_mem_finite_fiber
        (chartAtPointedSurfaceCoordinate X x) hF hfinite_complex
        (by simp [hx])
  have hsingleton_subset : ({x} : Finset X) ⊆ s := by
    intro w hw
    have hwx : w = x := by
      simpa [Finset.mem_singleton] using hw
    simpa [hwx] using hxmem
  have hsingle_sum_le :
      ({x} : Finset X).sum m ≤ s.sum m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsingleton_subset
      (by intro _ _ _; exact Nat.zero_le _)
  have hsingle_eq : ({x} : Finset X).sum m = m x := by
    simp
  have htotal_le :
      m x ≤ holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y := by
    simpa [holomorphicMapFiberMultiplicityInCoordinateModel, s, m, hsingle_eq]
      using hsingle_sum_le
  exact le_trans hxpos htotal_le

/--
%%handwave
name:
  Surjectivity gives positive total multiplicity in every fiber
statement:
  Under the finite-fiber holomorphic coordinate-model hypotheses, if
  \(F:X\to Y\) is surjective, then every fiber has total multiplicity at least
  one.
proof:
  For each \(y\), choose \(x\) with \(F(x)=y\) and apply positivity of the
  total multiplicity of a nonempty finite fiber.
-/
theorem one_le_holomorphicMapFiberMultiplicityInCoordinateModel_of_surjective
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_inj : Function.Injective φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    (hsurjective : Function.Surjective F) :
    ∀ y : Y, 1 ≤ holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y := by
  intro y
  rcases hsurjective y with ⟨x, hx⟩
  exact
    one_le_holomorphicMapFiberMultiplicityInCoordinateModel_of_mem
      hφ_inj hF hfinite hx

/--
%%handwave
name:
  Zero total multiplicity characterizes an empty fiber
statement:
  Under the finite-fiber holomorphic coordinate-model hypotheses, the total
  multiplicity over \(y\) is zero if and only if there is no \(x\) with
  \(F(x)=y\).
proof:
  A nonempty fiber has total multiplicity at least one.  Conversely, if the
  fiber is empty, its finite multiplicity sum is the empty sum and equals
  zero.
-/
theorem holomorphicMapFiberMultiplicityInCoordinateModel_eq_zero_iff_no_fiber
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_inj : Function.Injective φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    (y : Y) :
    holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y = 0 ↔
      ¬ ∃ x : X, F x = y := by
  classical
  constructor
  · intro hzero hnonempty
    rcases hnonempty with ⟨x, hx⟩
    have hpos :
        1 ≤ holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y :=
      one_le_holomorphicMapFiberMultiplicityInCoordinateModel_of_mem
        hφ_inj hF hfinite hx
    have : (1 : ℕ) ≤ 0 := by
      rw [hzero] at hpos
      exact hpos
    exact (by norm_num : ¬ (1 : ℕ) ≤ 0) this
  · intro hnone
    have hfiber_empty : (hfinite y).toFinset = (∅ : Finset X) := by
      ext x
      constructor
      · intro hxmem
        exact False.elim
          (hnone ⟨x, (hfinite y).mem_toFinset.mp hxmem⟩)
      · intro hxempty
        cases hxempty
    simp [holomorphicMapFiberMultiplicityInCoordinateModel, hfiber_empty]

/--
%%handwave
name:
  Zero total fiber multiplicity characterizes points outside the range
statement:
  The total multiplicity of the fiber over \(y\) is zero if and only if
  \(y\notin F(X)\).
proof:
  Membership in the range is exactly the existence of a preimage.  Rewrite
  the empty-fiber characterization using this equivalence.
-/
theorem holomorphicMapFiberMultiplicityInCoordinateModel_eq_zero_iff_not_mem_range
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_inj : Function.Injective φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    (y : Y) :
    holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y = 0 ↔
      y ∉ Set.range F := by
  simpa [Set.mem_range] using
    holomorphicMapFiberMultiplicityInCoordinateModel_eq_zero_iff_no_fiber
      hφ_inj hF hfinite y

/--
%%handwave
name:
  Positive total fiber multiplicity characterizes the range
statement:
  The total multiplicity of the fiber over \(y\) is positive if and only if
  \(y\in F(X)\).
proof:
  Outside the range the total multiplicity is zero.  If \(y=F(x)\), positivity
  follows from the local contribution at \(x\).
-/
theorem holomorphicMapFiberMultiplicityInCoordinateModel_pos_iff_mem_range
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_inj : Function.Injective φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    (y : Y) :
    0 < holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y ↔
      y ∈ Set.range F := by
  constructor
  · intro hpos
    by_contra hnot
    have hzero :
        holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y = 0 :=
      (holomorphicMapFiberMultiplicityInCoordinateModel_eq_zero_iff_not_mem_range
        hφ_inj hF hfinite y).mpr hnot
    exact (Nat.ne_of_gt hpos) hzero
  · rintro ⟨x, rfl⟩
    exact lt_of_lt_of_le zero_lt_one
      (one_le_holomorphicMapFiberMultiplicityInCoordinateModel_of_mem
        hφ_inj hF hfinite rfl)

/--
%%handwave
name:
  A fiber of total multiplicity one is nonempty
statement:
  If the total multiplicity of a finite fiber \(F^{-1}(y)\) is one, then there
  exists \(x\) with \(F(x)=y\).
proof:
  An empty fiber has total multiplicity zero, contradicting the assumed value
  one.
-/
theorem exists_of_holomorphicMapFiberMultiplicityInCoordinateModel_eq_one
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_inj : Function.Injective φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    {y : Y}
    (hmult : holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y = 1) :
    ∃ x : X, F x = y := by
  classical
  by_contra hnone
  have hzero :
      holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y = 0 :=
    (holomorphicMapFiberMultiplicityInCoordinateModel_eq_zero_iff_no_fiber
      hφ_inj hF hfinite y).mpr hnone
  have : (0 : ℕ) = 1 := by
    rw [← hzero, hmult]
  norm_num at this

/--
%%handwave
name:
  A finite fiber of total multiplicity one is a singleton
statement:
  If \(F^{-1}(y)\) is nonempty and its total holomorphic multiplicity equals
  one, then there is a unique \(x\) with \(F(x)=y\).
proof:
  Choose one preimage \(x\).  If a distinct preimage \(z\) existed, both
  local multiplicities would be at least one, so the total fiber multiplicity
  would be at least two, contradicting that it equals one.
-/
theorem existsUnique_of_fiberMultiplicityInCoordinateModel_eq_one_at
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_inj : Function.Injective φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    {y : Y} (hexists : ∃ x : X, F x = y)
    (hmult : holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y = 1) :
    ∃! x : X, F x = y := by
  classical
  rcases hexists with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  intro z hz
  by_contra hzx
  let s : Finset X := (hfinite y).toFinset
  let m : X → ℕ := fun w ↦
    holomorphicMapLocalMultiplicityAtValueInCoordinate
      (chartAtPointedSurfaceCoordinate X w)
      (fun x' : X ↦ φ (F x')) (φ y)
  have hxmem : x ∈ s := by
    simpa [s] using (hfinite y).mem_toFinset.mpr hx
  have hzmem : z ∈ s := by
    simpa [s] using (hfinite y).mem_toFinset.mpr hz
  have hfinite_complex : {w : X | φ (F w) = φ y}.Finite :=
    (hfinite y).subset (by
      intro w hw
      exact hφ_inj hw)
  have hxpos : 1 ≤ m x := by
    exact
      one_le_holomorphicMapLocalMultiplicityAtValueInCoordinate_of_mem_finite_fiber
        (chartAtPointedSurfaceCoordinate X x) hF hfinite_complex
        (by simp [hx])
  have hzpos : 1 ≤ m z := by
    exact
      one_le_holomorphicMapLocalMultiplicityAtValueInCoordinate_of_mem_finite_fiber
        (chartAtPointedSurfaceCoordinate X z) hF hfinite_complex
        (by simp [hz])
  have hpair_subset : ({x, z} : Finset X) ⊆ s := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hxmem
    · exact hzmem
  have hpair_sum_le :
      ({x, z} : Finset X).sum m ≤ s.sum m :=
    Finset.sum_le_sum_of_subset_of_nonneg hpair_subset
      (by intro _ _ _; exact Nat.zero_le _)
  have htwo_le_pair : 2 ≤ ({x, z} : Finset X).sum m := by
    rw [Finset.sum_insert]
    · simpa using add_le_add hxpos hzpos
    · intro hxz_mem
      have hxz : x = z := by
        simpa [Finset.mem_singleton] using hxz_mem
      exact hzx hxz.symm
  have htwo_le_total : 2 ≤ s.sum m :=
    le_trans htwo_le_pair hpair_sum_le
  have htotal_eq_one : s.sum m = 1 := by
    simpa [holomorphicMapFiberMultiplicityInCoordinateModel, s, m] using hmult
  have : (2 : ℕ) ≤ 1 := by
    rw [htotal_eq_one] at htwo_le_total
    exact htwo_le_total
  exact (by norm_num : ¬ (2 : ℕ) ≤ 1) this

/--
%%handwave
name:
  Unit total multiplicity makes every fiber a singleton
statement:
  If every finite fiber of \(F:X\to Y\) has total holomorphic multiplicity
  one, then every \(y\in Y\) has a unique preimage.
proof:
  Unit multiplicity first implies that the fiber is nonempty.  The
  single-fiber unit-multiplicity result then shows that it contains only one
  point.
-/
theorem existsUnique_of_fiberMultiplicityInCoordinateModel_eq_one_of_all
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_inj : Function.Injective φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    (hmult :
      ∀ y : Y,
        holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y = 1) :
    ∀ y : Y, ∃! x : X, F x = y := by
  intro y
  exact existsUnique_of_fiberMultiplicityInCoordinateModel_eq_one_at
    hφ_inj hF hfinite
    (exists_of_holomorphicMapFiberMultiplicityInCoordinateModel_eq_one
      hφ_inj hF hfinite (hmult y))
    (hmult y)

/--
%%handwave
name:
  Unit multiplicity in every fiber implies surjectivity
statement:
  If every finite fiber of \(F:X\to Y\) has total multiplicity one, then
  \(F\) is surjective.
proof:
  For every target point, unit total multiplicity rules out the empty fiber
  and therefore supplies a preimage.
-/
theorem surjective_of_holomorphicMapFiberMultiplicityInCoordinateModel_eq_one
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_inj : Function.Injective φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    (hmult :
      ∀ y : Y,
        holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y = 1) :
    Function.Surjective F := by
  intro y
  exact exists_of_holomorphicMapFiberMultiplicityInCoordinateModel_eq_one
    hφ_inj hF hfinite (hmult y)

/--
%%handwave
name:
  Every unit-multiplicity fiber has a unique point
statement:
  Under the finite-fiber holomorphic coordinate-model hypotheses, if every
  fiber has total multiplicity one, then every \(y\) has a unique preimage.
proof:
  Apply the result that unit multiplicity itself forces both existence and
  uniqueness in each fiber; the additional surjectivity hypothesis is
  redundant.
-/
theorem existsUnique_of_fiberMultiplicityInCoordinateModel_eq_one
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_inj : Function.Injective φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    (_hsurjective : Function.Surjective F)
    (hmult :
      ∀ y : Y,
        holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y = 1) :
    ∀ y : Y, ∃! x : X, F x = y := by
  exact existsUnique_of_fiberMultiplicityInCoordinateModel_eq_one_of_all
    hφ_inj hF hfinite hmult

/--
%%handwave
name:
  Total multiplicity of a unique simple zero fiber
statement:
  Suppose the complex coordinate expression \(\varphi\circ F\) vanishes
  exactly at \(p\), and its local multiplicity there is one in every pointed
  coordinate.  Then the total multiplicity of the fiber over \(F(p)\) equals
  one.
proof:
  Injectivity of the zero condition identifies the finite fiber over \(F(p)\)
  with the singleton \(\{p\}\).  The total fiber sum therefore reduces to the
  single local multiplicity at \(p\), which is one.
-/
theorem holomorphicMapFiberMultiplicityInCoordinateModel_eq_one_at_simple_single_zero
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {p : X} {F : X → Y} {φ : Y → ℂ}
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    (hzero : ∀ x : X, φ (F x) = 0 ↔ x = p)
    (hsimple : ∀ χ : PointedSurfaceCoordinate X p,
      holomorphicMapLocalMultiplicityAtValueInCoordinate χ
        (fun x : X ↦ φ (F x)) 0 = 1) :
    holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite (F p) = 1 := by
  classical
  have hp_zero : φ (F p) = 0 := (hzero p).mpr rfl
  have hfiber_singleton :
      (hfinite (F p)).toFinset = ({p} : Finset X) := by
    ext x
    constructor
    · intro hx
      have hxF : F x = F p :=
        (hfinite (F p)).mem_toFinset.mp hx
      have hxzero : φ (F x) = 0 := by
        rw [hxF, hp_zero]
      exact by
        simpa using (hzero x).mp hxzero
    · intro hx
      have hxp : x = p := by
        simpa using hx
      exact (hfinite (F p)).mem_toFinset.mpr (by simp [hxp])
  rw [holomorphicMapFiberMultiplicityInCoordinateModel, hfiber_singleton]
  simp [hp_zero, hsimple (chartAtPointedSurfaceCoordinate X p)]

/--
%%handwave
name:
  Pointed coordinate transitions have nonzero derivative
statement:
  The holomorphic transition between two pointed coordinates at the same point
  has nonzero complex derivative at the marked coordinate value.
proof:
  The two coordinate transitions are local inverses near the marked point.
  Differentiating their composition gives derivative \(1\), so neither
  transition derivative can vanish.
-/
theorem pointedCoordinate_transition_deriv_ne_zero
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {p : X}
    (χ ψ : PointedSurfaceCoordinate X p) :
    deriv (fun z : ℂ ↦ χ.chart (ψ.chart.symm z)) (ψ.chart p) ≠ 0 := by
  let F : ℂ → ℂ := fun z ↦ χ.chart (ψ.chart.symm z)
  let G : ℂ → ℂ := fun w ↦ ψ.chart (χ.chart.symm w)
  let z₀ : ℂ := ψ.chart p
  let w₀ : ℂ := χ.chart p
  have hz₀_target : z₀ ∈ ψ.chart.target := by
    dsimp [z₀]
    exact ψ.chart.map_source ψ.base_mem_source
  have hw₀_target : w₀ ∈ χ.chart.target := by
    dsimp [w₀]
    exact χ.chart.map_source χ.base_mem_source
  have hz₀_sourceχ : ψ.chart.symm z₀ ∈ χ.chart.source := by
    dsimp [z₀]
    simpa [ψ.chart.left_inv ψ.base_mem_source] using χ.base_mem_source
  have hw₀_sourceψ : χ.chart.symm w₀ ∈ ψ.chart.source := by
    dsimp [w₀]
    simpa [χ.chart.left_inv χ.base_mem_source] using ψ.base_mem_source
  have hF_an : AnalyticAt ℂ F z₀ := by
    dsimp [F, z₀]
    exact chartTransition_analyticAt ψ.chart ψ.chart_mem_atlas
      χ.chart χ.chart_mem_atlas hz₀_target hz₀_sourceχ
  have hG_an : AnalyticAt ℂ G w₀ := by
    dsimp [G, w₀]
    exact chartTransition_analyticAt χ.chart χ.chart_mem_atlas
      ψ.chart ψ.chart_mem_atlas hw₀_target hw₀_sourceψ
  have hF_deriv : HasDerivAt F (deriv F z₀) z₀ :=
    hF_an.differentiableAt.hasDerivAt
  have hG_deriv : HasDerivAt G (deriv G w₀) w₀ :=
    hG_an.differentiableAt.hasDerivAt
  have hFG_event : (fun w : ℂ ↦ F (G w)) =ᶠ[𝓝 w₀] fun w : ℂ ↦ w := by
    have hχtarget_nhds : χ.chart.target ∈ 𝓝 w₀ :=
      χ.chart.open_target.mem_nhds hw₀_target
    have hχsymm_w₀ : χ.chart.symm w₀ = p := by
      dsimp [w₀]
      exact χ.chart.left_inv χ.base_mem_source
    have hpre_sourceψ :
        χ.chart.symm ⁻¹' ψ.chart.source ∈ 𝓝 w₀ :=
      χ.chart.continuousAt_symm hw₀_target
        (by simpa [hχsymm_w₀] using
          (ψ.chart.open_source.mem_nhds ψ.base_mem_source))
    filter_upwards [hχtarget_nhds, hpre_sourceψ] with w hw_target hw_sourceψ
    dsimp [F, G]
    rw [ψ.chart.left_inv hw_sourceψ]
    rw [χ.chart.right_inv hw_target]
  have hG_w₀ : G w₀ = z₀ := by
    dsimp [G, z₀, w₀]
    rw [χ.chart.left_inv χ.base_mem_source]
  have hcomp :
      HasDerivAt (fun w : ℂ ↦ F (G w))
        (deriv F z₀ * deriv G w₀) w₀ := by
    have hF_deriv_at_G : HasDerivAt F (deriv F z₀) (G w₀) := by
      simpa [hG_w₀] using hF_deriv
    simpa [Function.comp_def] using hF_deriv_at_G.comp w₀ hG_deriv
  have hid : HasDerivAt (fun w : ℂ ↦ w) 1 w₀ := hasDerivAt_id w₀
  have hcomp' : HasDerivAt (fun w : ℂ ↦ F (G w)) 1 w₀ :=
    hid.congr_of_eventuallyEq hFG_event
  have hmul_eq : deriv F z₀ * deriv G w₀ = 1 :=
    hcomp.unique hcomp'
  have hF_ne : deriv F z₀ ≠ 0 := by
    intro hzero
    simp [hzero] at hmul_eq
  simpa [F, z₀] using hF_ne

/--
%%handwave
name:
  Local holomorphic multiplicity is independent of pointed coordinate
statement:
  Let \(\chi\) and \(\psi\) be pointed complex coordinates at the same point
  \(x\).  For every complex-valued map \(F\) and value \(a\), the local
  multiplicity of \(F-a\) computed in \(\chi\) equals that computed in
  \(\psi\).
proof:
  The two coordinate expressions differ by composition with the holomorphic
  chart transition.  This transition has nonzero derivative at the base
  point, so analytic order, and hence its natural-number multiplicity, is
  invariant under the composition.
-/
theorem holomorphicMapLocalMultiplicityAtValueInCoordinate_congr_coordinate
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {x : X}
    (χ ψ : PointedSurfaceCoordinate X x) (F : X → ℂ) (a : ℂ) :
    holomorphicMapLocalMultiplicityAtValueInCoordinate χ F a =
      holomorphicMapLocalMultiplicityAtValueInCoordinate ψ F a := by
  let fχ : ℂ → ℂ := fun w ↦ F (χ.chart.symm w) - a
  let fψ : ℂ → ℂ := fun z ↦ F (ψ.chart.symm z) - a
  let g : ℂ → ℂ := fun z ↦ χ.chart (ψ.chart.symm z)
  let z₀ : ℂ := ψ.chart x
  let w₀ : ℂ := χ.chart x
  have hz₀_target : z₀ ∈ ψ.chart.target := by
    dsimp [z₀]
    exact ψ.chart.map_source ψ.base_mem_source
  have hz₀_sourceχ : ψ.chart.symm z₀ ∈ χ.chart.source := by
    dsimp [z₀]
    simpa [ψ.chart.left_inv ψ.base_mem_source] using χ.base_mem_source
  have hg_an : AnalyticAt ℂ g z₀ := by
    dsimp [g, z₀]
    exact chartTransition_analyticAt ψ.chart ψ.chart_mem_atlas
      χ.chart χ.chart_mem_atlas hz₀_target hz₀_sourceχ
  have hg_deriv_ne : deriv g z₀ ≠ 0 := by
    simpa [g, z₀] using pointedCoordinate_transition_deriv_ne_zero X χ ψ
  have hg_z₀ : g z₀ = w₀ := by
    dsimp [g, z₀, w₀]
    rw [ψ.chart.left_inv ψ.base_mem_source]
  have hpre_sourceχ : ψ.chart.symm ⁻¹' χ.chart.source ∈ 𝓝 z₀ := by
    have hx_symm : ψ.chart.symm z₀ = x := by
      dsimp [z₀]
      exact ψ.chart.left_inv ψ.base_mem_source
    have hsource_nhds : χ.chart.source ∈ 𝓝 (ψ.chart.symm z₀) := by
      simpa [hx_symm] using
        χ.chart.open_source.mem_nhds χ.base_mem_source
    exact ψ.chart.continuousAt_symm hz₀_target hsource_nhds
  have hfψ_eq : fψ =ᶠ[𝓝 z₀] fχ ∘ g := by
    filter_upwards [hpre_sourceχ] with z hz_sourceχ
    dsimp [fψ, fχ, g, Function.comp_def]
    rw [χ.chart.left_inv hz_sourceχ]
  have horder :
      analyticOrderAt fψ z₀ = analyticOrderAt fχ w₀ := by
    calc
      analyticOrderAt fψ z₀ =
          analyticOrderAt (fχ ∘ g) z₀ :=
        analyticOrderAt_congr hfψ_eq
      _ = analyticOrderAt fχ (g z₀) :=
        analyticOrderAt_comp_of_deriv_ne_zero hg_an hg_deriv_ne
      _ = analyticOrderAt fχ w₀ := by rw [hg_z₀]
  simp [holomorphicMapLocalMultiplicityAtValueInCoordinate,
    analyticOrderNatAt, fχ, fψ, z₀, w₀, horder]

/--
The zero-counting multiplicity of a complex analytic level set inside a
specified plane set.
-/
noncomputable def complexAnalyticLevelMultiplicityOnSet
    (F : ℂ → ℂ) (U : Set ℂ)
    (hfinite : ∀ a : ℂ, {z : ℂ | z ∈ U ∧ F z = a}.Finite)
    (a : ℂ) : ℕ := by
  classical
  exact (hfinite a).toFinset.sum fun z ↦
    analyticOrderNatAt (fun w : ℂ ↦ F w - a) z

/--
%%handwave
name:
  Plane level multiplicity depends only on the chosen fiber
statement:
  For a fixed level of a complex-valued function, the analytic multiplicity
  sum over two subsets is the same if the two subsets contain exactly the same
  points of that level.
proof:
  The two finite level fibers have the same elements, so their finite sums are
  over the same finite set with the same local multiplicity assigned to each
  point.
-/
theorem complexAnalyticLevelMultiplicityOnSet_eq_of_mem_iff_on_level
    {F : ℂ → ℂ} {U W : Set ℂ}
    (hfiniteU : ∀ a : ℂ, {z : ℂ | z ∈ U ∧ F z = a}.Finite)
    (hfiniteW : ∀ a : ℂ, {z : ℂ | z ∈ W ∧ F z = a}.Finite)
    {a : ℂ}
    (hmem : ∀ z : ℂ, F z = a → (z ∈ U ↔ z ∈ W)) :
    complexAnalyticLevelMultiplicityOnSet F U hfiniteU a =
      complexAnalyticLevelMultiplicityOnSet F W hfiniteW a := by
  classical
  have hfinset :
      (hfiniteU a).toFinset = (hfiniteW a).toFinset := by
    ext z
    constructor
    · intro hz
      have hzset : z ∈ U ∧ F z = a :=
        (hfiniteU a).mem_toFinset.mp hz
      exact (hfiniteW a).mem_toFinset.mpr
        ⟨(hmem z hzset.2).mp hzset.1, hzset.2⟩
    · intro hz
      have hzset : z ∈ W ∧ F z = a :=
        (hfiniteW a).mem_toFinset.mp hz
      exact (hfiniteU a).mem_toFinset.mpr
        ⟨(hmem z hzset.2).mpr hzset.1, hzset.2⟩
  simp [complexAnalyticLevelMultiplicityOnSet, hfinset]

/--
%%handwave
name:
  Local multiplicity is unchanged by a noncritical coordinate
statement:
  If a level equation is locally the pullback of another analytic equation
  along a holomorphic coordinate whose derivative is nonzero at the point,
  then the two equations have the same natural analytic multiplicity.
proof:
  Analytic order is unchanged by replacing a germ with an equal germ.  The
  composition formula for analytic order then applies, and the coordinate has
  order one because its derivative is nonzero.
-/
theorem analyticOrderNatAt_congr_comp_of_deriv_ne_zero
    {f g H : ℂ → ℂ} {z : ℂ}
    (hfg : f =ᶠ[𝓝 z] g ∘ H)
    (hH : AnalyticAt ℂ H z) (hderiv : deriv H z ≠ 0) :
    analyticOrderNatAt f z = analyticOrderNatAt g (H z) := by
  have horder :
      analyticOrderAt f z = analyticOrderAt (g ∘ H) z :=
    analyticOrderAt_congr hfg
  have hcomp :
      analyticOrderAt (g ∘ H) z = analyticOrderAt g (H z) :=
    analyticOrderAt_comp_of_deriv_ne_zero hH hderiv
  change (analyticOrderAt f z).toNat =
    (analyticOrderAt g (H z)).toNat
  rw [horder, hcomp]

/--
%%handwave
name:
  Injective coordinate changes preserve total level multiplicity
statement:
  Suppose a coordinate map is injective on a set and carries the level fiber
  of one complex-valued function bijectively onto the level fiber of another
  function on the image set.  If the local analytic multiplicities agree at
  corresponding points, then the two total multiplicity sums are equal.
proof:
  Use the coordinate map as a bijection between the two finite fibers.  The
  injectivity hypothesis gives uniqueness, the fiber equivalence gives
  surjectivity onto the image fiber, and the pointwise multiplicity equality
  identifies the summands.
-/
theorem complexAnalyticLevelMultiplicityOnSet_eq_image_of_injOn
    {F P H : ℂ → ℂ} {U : Set ℂ} {a b : ℂ}
    (hfiniteF : ∀ a : ℂ, {z : ℂ | z ∈ U ∧ F z = a}.Finite)
    (hfiniteP : ∀ b : ℂ, {w : ℂ | w ∈ H '' U ∧ P w = b}.Finite)
    (hinj : Set.InjOn H U)
    (hfiber : ∀ z : ℂ, z ∈ U → (F z = a ↔ P (H z) = b))
    (hmult : ∀ z : ℂ, z ∈ U → F z = a →
      analyticOrderNatAt (fun w : ℂ ↦ F w - a) z =
        analyticOrderNatAt (fun w : ℂ ↦ P w - b) (H z)) :
    complexAnalyticLevelMultiplicityOnSet F U hfiniteF a =
      complexAnalyticLevelMultiplicityOnSet P (H '' U) hfiniteP b := by
  classical
  let s : Finset ℂ := (hfiniteF a).toFinset
  let t : Finset ℂ := (hfiniteP b).toFinset
  let mF : ℂ → ℕ := fun z ↦ analyticOrderNatAt (fun w : ℂ ↦ F w - a) z
  let mP : ℂ → ℕ := fun w ↦ analyticOrderNatAt (fun ζ : ℂ ↦ P ζ - b) w
  have hsum : s.sum mF = t.sum mP := by
    refine Finset.sum_bij (fun z _hz ↦ H z) ?_ ?_ ?_ ?_
    · intro z hz
      have hzset : z ∈ U ∧ F z = a :=
        (hfiniteF a).mem_toFinset.mp (by simpa [s] using hz)
      exact (hfiniteP b).mem_toFinset.mpr
        ⟨⟨z, hzset.1, rfl⟩, (hfiber z hzset.1).mp hzset.2⟩
    · intro z₁ hz₁ z₂ hz₂ hHz
      have hz₁set : z₁ ∈ U ∧ F z₁ = a :=
        (hfiniteF a).mem_toFinset.mp (by simpa [s] using hz₁)
      have hz₂set : z₂ ∈ U ∧ F z₂ = a :=
        (hfiniteF a).mem_toFinset.mp (by simpa [s] using hz₂)
      exact hinj hz₁set.1 hz₂set.1 hHz
    · intro w hw
      have hwset : w ∈ H '' U ∧ P w = b :=
        (hfiniteP b).mem_toFinset.mp (by simpa [t] using hw)
      rcases hwset.1 with ⟨z, hzU, rfl⟩
      have hzF : F z = a :=
        (hfiber z hzU).mpr hwset.2
      exact ⟨z, (hfiniteF a).mem_toFinset.mpr ⟨hzU, hzF⟩, rfl⟩
    · intro z hz
      have hzset : z ∈ U ∧ F z = a :=
        (hfiniteF a).mem_toFinset.mp (by simpa [s] using hz)
      exact hmult z hzset.1 hzset.2
  simpa [complexAnalyticLevelMultiplicityOnSet, s, t, mF, mP] using hsum

/--
%%handwave
name:
  Nonvanishing analytic germs have analytic roots
statement:
  If an analytic complex germ is nonzero at a point and \(n>0\), then near
  that point it admits an analytic \(n\)th root whose value is nonzero at the
  point.
proof:
  Choose an algebraic \(n\)th root of the nonzero base value and normalize the
  germ to have value \(1\).  The normalized germ lies in the logarithm slit
  domain near the base point, so its fractional power is analytic there; after
  multiplying by the chosen algebraic root, the \(n\)th power recovers the
  original germ.
-/
theorem analyticAt_exists_nthRoot_pow_eq_of_ne_zero
    {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : AnalyticAt ℂ g z₀) (hg_ne : g z₀ ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    ∃ r : ℂ → ℂ,
      AnalyticAt ℂ r z₀ ∧ r z₀ ≠ 0 ∧ ∀ z : ℂ, r z ^ n = g z := by
  classical
  rcases IsAlgClosed.exists_pow_nat_eq (g z₀) hn with ⟨c, hc⟩
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  have hc_ne : c ≠ 0 := by
    intro hc0
    exact hg_ne (by rw [← hc, hc0, zero_pow hn_ne])
  let h : ℂ → ℂ := fun z : ℂ ↦ g z / g z₀
  let r : ℂ → ℂ := fun z : ℂ ↦ c * (h z ^ ((n : ℂ)⁻¹))
  have hh : AnalyticAt ℂ h z₀ := by
    simpa [h] using hg.div_const (c := g z₀)
  have hh0 : h z₀ = 1 := by
    simp [h, hg_ne]
  have hone_slit : (1 : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_arg]
    constructor
    · simpa using Real.pi_ne_zero.symm
    · exact one_ne_zero
  have hh_slit : h z₀ ∈ Complex.slitPlane := by
    simp [hh0, hone_slit]
  have hroot_an :
      AnalyticAt ℂ (fun z : ℂ ↦ h z ^ ((n : ℂ)⁻¹)) z₀ :=
    hh.cpow analyticAt_const hh_slit
  have hr_an : AnalyticAt ℂ r z₀ := by
    have hc_an : AnalyticAt ℂ (fun _ : ℂ ↦ c) z₀ := analyticAt_const
    simpa [r] using hc_an.mul hroot_an
  have hroot0 : h z₀ ^ ((n : ℂ)⁻¹) = 1 := by
    simp [hh0]
  have hr_ne : r z₀ ≠ 0 := by
    simp [r, hc_ne, hroot0]
  refine ⟨r, hr_an, hr_ne, ?_⟩
  intro z
  have hroot_pow :
      (h z ^ ((n : ℂ)⁻¹)) ^ n = h z :=
    Complex.cpow_nat_inv_pow (h z) hn_ne
  calc
    r z ^ n = c ^ n * (h z ^ ((n : ℂ)⁻¹)) ^ n := by
      simp [r, mul_pow]
    _ = g z₀ * h z := by rw [hc, hroot_pow]
    _ = g z := by
      dsimp [h]
      rw [div_eq_mul_inv, ← mul_assoc, mul_comm (g z₀) (g z), mul_assoc,
        mul_inv_cancel₀ hg_ne, mul_one]

/--
%%handwave
name:
  Branch coordinate derivative
statement:
  If \(r\) is analytic at \(z_0\), then the coordinate
  \(z\mapsto (z-z_0)r(z)\) has strict complex derivative \(r(z_0)\) at
  \(z_0\).
proof:
  Differentiate the product of the translation \(z-z_0\) and the analytic
  factor \(r\).  The translation vanishes at \(z_0\), so only the factor
  \(r(z_0)\) remains in the product rule.
-/
theorem analyticAt_branchCoordinate_hasStrictDerivAt
    {r : ℂ → ℂ} {z₀ : ℂ} (hr : AnalyticAt ℂ r z₀) :
    HasStrictDerivAt (fun z : ℂ ↦ (z - z₀) * r z) (r z₀) z₀ := by
  have hr_strict : HasStrictDerivAt r (deriv r z₀) z₀ :=
    hr.hasStrictDerivAt
  have hsub_strict :
      HasStrictDerivAt (fun z : ℂ ↦ z - z₀) 1 z₀ := by
    simpa using
      (hasStrictDerivAt_id (x := z₀)).sub
        (hasStrictDerivAt_const (x := z₀) (c := z₀))
  have hmul := hsub_strict.mul hr_strict
  simpa using hmul

/--
%%handwave
name:
  Branch coordinates are locally invertible
statement:
  If \(r\) is analytic and nonzero at \(z_0\), then
  \(z\mapsto (z-z_0)r(z)\) is injective on a neighborhood of \(z_0\), and the
  image of every sufficiently small neighborhood of \(z_0\) is a neighborhood
  of the origin.
proof:
  The previous derivative computation gives a strict derivative equal to the
  nonzero number \(r(z_0)\).  The inverse-function theorem supplies a local
  homeomorphic chart, whose source gives injectivity and whose image behavior
  sends neighborhoods of \(z_0\) to neighborhoods of the image point \(0\).
-/
theorem analyticAt_branchCoordinate_local_injOn_image
    {r : ℂ → ℂ} {z₀ : ℂ}
    (hr : AnalyticAt ℂ r z₀) (hr_ne : r z₀ ≠ 0) :
    ∃ V : Set ℂ, V ∈ 𝓝 z₀ ∧
      Set.InjOn (fun z : ℂ ↦ (z - z₀) * r z) V ∧
        ∀ U : Set ℂ, U ∈ 𝓝 z₀ → U ⊆ V →
          (fun z : ℂ ↦ (z - z₀) * r z) '' U ∈ 𝓝 (0 : ℂ) := by
  let H : ℂ → ℂ := fun z : ℂ ↦ (z - z₀) * r z
  have hstrict : HasStrictDerivAt H (r z₀) z₀ :=
    analyticAt_branchCoordinate_hasStrictDerivAt hr
  let hf := hstrict.hasStrictFDerivAt_equiv hr_ne
  let e : OpenPartialHomeomorph ℂ ℂ := hf.toOpenPartialHomeomorph H
  have hz_source : z₀ ∈ e.source := by
    simpa [e] using hf.mem_toOpenPartialHomeomorph_source
  refine ⟨e.source, e.open_source.mem_nhds hz_source, ?_, ?_⟩
  · intro z hz w hw hzw
    exact e.injOn hz hw (by simpa [e, H] using hzw)
  · intro U hU _hUV
    have himage : H '' U ∈ 𝓝 (H z₀) := by
      simpa [e] using e.image_mem_nhds hz_source hU
    simpa [H] using himage

/--
%%handwave
name:
  Nearby levels stay near an isolated level point
statement:
  If a continuous complex-valued function has exactly one point of a given
  level in a closed disk, then for every open neighborhood of that point, all
  sufficiently nearby levels in the open disk lie in that neighborhood.
proof:
  Remove the chosen neighborhood from the closed disk.  Its image is compact,
  hence closed, and it does not contain the original level value.  A small
  neighborhood of the original value therefore misses this compact image, so
  any preimage of a nearby value in the disk must lie in the chosen
  neighborhood.
-/
theorem eventually_levelSet_ball_subset_open_of_isolated_on_closedBall
    {F : ℂ → ℂ} {a₀ z₀ : ℂ} {r : ℝ} {U : Set ℂ}
    (hF_cont : ContinuousOn F (Metric.closedBall z₀ r))
    (hU_open : IsOpen U) (hz₀U : z₀ ∈ U)
    (hisolating :
      ∀ z : ℂ, z ∈ Metric.closedBall z₀ r → F z = a₀ → z = z₀) :
    ∀ᶠ a in 𝓝 a₀,
      ∀ z : ℂ, z ∈ Metric.ball z₀ r → F z = a → z ∈ U := by
  let K : Set ℂ := Metric.closedBall z₀ r \ U
  have hK_compact : IsCompact K :=
    (isCompact_closedBall z₀ r).diff hU_open
  have hF_image_compact : IsCompact (F '' K) :=
    hK_compact.image_of_continuousOn (hF_cont.mono Set.diff_subset)
  have hF_image_closed : IsClosed (F '' K) :=
    hF_image_compact.isClosed
  have ha₀_not_image : a₀ ∉ F '' K := by
    rintro ⟨z, hzK, hzF⟩
    have hz_eq : z = z₀ :=
      hisolating z hzK.1 hzF
    exact hzK.2 (by simpa [hz_eq] using hz₀U)
  filter_upwards [hF_image_closed.compl_mem_nhds ha₀_not_image] with a ha z hz_ball hzF
  by_contra hzU
  exact ha ⟨z, ⟨Metric.ball_subset_closedBall hz_ball, hzU⟩, hzF⟩

/--
%%handwave
name:
  Finite local fiber gives finite vanishing order
statement:
  If a level set in a disk is finite and a chosen point belongs to that level,
  then the analytic order of the level equation at the chosen point is finite.
proof:
  Infinite analytic order would make the level equation vanish throughout a
  neighborhood of the point.  Intersecting that neighborhood with the disk and
  avoiding the other finitely many points of the fiber gives a second nearby
  point in the same finite fiber, a contradiction.
-/
theorem analyticOrderAt_sub_ne_top_of_finite_level_in_ball
    {F : ℂ → ℂ} {a₀ z₀ : ℂ} {r : ℝ}
    (hfinite : {z : ℂ | z ∈ Metric.ball z₀ r ∧ F z = a₀}.Finite)
    (_hz₀ : F z₀ = a₀) (hr : 0 < r) :
    analyticOrderAt (fun z : ℂ ↦ F z - a₀) z₀ ≠ ⊤ := by
  intro htop
  have hzero :
      ∀ᶠ z in 𝓝 z₀, F z - a₀ = 0 := by
    simpa using (analyticOrderAt_eq_top.mp htop)
  let S : Set ℂ := {z : ℂ | z ∈ Metric.ball z₀ r ∧ F z = a₀} \ {z₀}
  have hS_finite : S.Finite :=
    hfinite.subset (by
      intro z hz
      exact hz.1)
  have hS_closed : IsClosed S :=
    hS_finite.isClosed
  have hz₀_notS : z₀ ∉ S := by
    simp [S]
  have hnotS_nhds : Sᶜ ∈ 𝓝 z₀ :=
    hS_closed.compl_mem_nhds hz₀_notS
  have hball_nhds : Metric.ball z₀ r ∈ 𝓝 z₀ :=
    Metric.ball_mem_nhds z₀ hr
  let U : Set ℂ :=
    Metric.ball z₀ r ∩ {z : ℂ | F z - a₀ = 0} ∩ Sᶜ
  have hU_nhds : U ∈ 𝓝 z₀ := by
    exact Filter.inter_mem (Filter.inter_mem hball_nhds hzero) hnotS_nhds
  have hUne : U ∩ {z : ℂ | z ≠ z₀} ∈ 𝓝[≠] z₀ := by
    exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hU_nhds)
      self_mem_nhdsWithin
  haveI : Filter.NeBot (𝓝[≠] z₀) := inferInstance
  rcases Filter.nonempty_of_mem hUne with ⟨z, hz⟩
  rcases hz with ⟨hzU, hz_ne⟩
  rcases hzU with ⟨hz_ball_zero, hz_notS⟩
  rcases hz_ball_zero with ⟨hz_ball, hz_zero⟩
  have hzF : F z = a₀ := sub_eq_zero.mp hz_zero
  exact hz_notS ⟨⟨hz_ball, hzF⟩, by
    simpa [Set.mem_singleton_iff] using hz_ne⟩

/--
%%handwave
name:
  Power map zero level has order \(n\)
statement:
  The zero level of the complex power map \(z\mapsto z^n\) has analytic
  multiplicity \(n\) at the origin.
proof:
  This is the standard centered monomial computation for analytic order.
-/
theorem analyticOrderNatAt_complex_pow_sub_zero (n : ℕ) :
    analyticOrderNatAt (fun z : ℂ ↦ z ^ n - 0) 0 = n := by
  have horder :
      analyticOrderAt (fun z : ℂ ↦ z ^ n - 0) 0 = (n : ℕ∞) := by
    simpa using
      (analyticOrderAt_centeredMonomial (𝕜 := ℂ) (z₀ := (0 : ℂ)) (n := n))
  rw [analyticOrderNatAt, horder]
  simp

/--
%%handwave
name:
  Nonzero power-map levels are simple
statement:
  Every nonzero level of the complex power map \(z\mapsto z^n\), with
  \(n>0\), is simple at each of its roots.
proof:
  A root of a nonzero level is nonzero.  The derivative of \(z^n\) is
  \(n z^{n-1}\), which is nonzero there, so the level equation has analytic
  order one.
-/
theorem analyticOrderNatAt_complex_pow_sub_eq_one_of_ne_zero
    {n : ℕ} (hn : 0 < n) {a z : ℂ}
    (hzpow : z ^ n = a) (ha : a ≠ 0) :
    analyticOrderNatAt (fun w : ℂ ↦ w ^ n - a) z = 1 := by
  have hz_ne : z ≠ 0 := by
    intro hz0
    exact ha (by
      rw [← hzpow, hz0, zero_pow (Nat.ne_of_gt hn)])
  have hn_ne_complex : (n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hderiv : deriv (fun w : ℂ ↦ w ^ n) z ≠ 0 := by
    rw [deriv_pow_field n]
    exact mul_ne_zero hn_ne_complex (pow_ne_zero _ hz_ne)
  have horder :
      analyticOrderAt (fun w : ℂ ↦ w ^ n - a) z = (1 : ℕ) := by
    have hbase :
        analyticOrderAt ((fun w : ℂ ↦ w ^ n) · - (fun w : ℂ ↦ w ^ n) z) z =
          (1 : ℕ) :=
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ w ^ n) z)
        |>.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hderiv
    simpa [hzpow] using hbase
  simp [analyticOrderNatAt, horder]

/--
%%handwave
name:
  Power-map zero fiber has total multiplicity \(n\)
statement:
  In any set containing the origin, the zero fiber of \(z\mapsto z^n\)
  contributes total analytic multiplicity \(n\).
proof:
  The zero fiber is the singleton consisting of the origin, and the preceding
  monomial-order computation gives contribution \(n\) there.
-/
theorem complexAnalyticLevelMultiplicityOnSet_complex_pow_zero
    {U : Set ℂ} {n : ℕ} (hn : 0 < n) (h0U : (0 : ℂ) ∈ U)
    (hfinite : ∀ a : ℂ, {z : ℂ | z ∈ U ∧ z ^ n = a}.Finite) :
    complexAnalyticLevelMultiplicityOnSet
        (fun z : ℂ ↦ z ^ n) U hfinite 0 = n := by
  classical
  have hfiber_singleton :
      (hfinite 0).toFinset = {0} := by
    ext z
    constructor
    · intro hz
      have hzset : z ∈ U ∧ z ^ n = 0 :=
        (hfinite 0).mem_toFinset.mp hz
      have hz0 : z = 0 :=
        (pow_eq_zero_iff'.mp hzset.2).1
      simp [hz0]
    · intro hz
      have hz0 : z = 0 := by simpa using hz
      exact (hfinite 0).mem_toFinset.mpr ⟨by simpa [hz0] using h0U, by simp [hz0, hn.ne']⟩
  change (hfinite 0).toFinset.sum
      (fun z ↦ analyticOrderNatAt (fun w : ℂ ↦ w ^ n - 0) z) = n
  rw [hfiber_singleton]
  have hpow0 : analyticOrderNatAt (fun w : ℂ ↦ w ^ n) 0 = n := by
    simpa using analyticOrderNatAt_complex_pow_sub_zero n
  simp [hpow0]

/--
%%handwave
name:
  Nonzero power-map fibers count their points
statement:
  For a nonzero level of \(z\mapsto z^n\), every root in a finite fiber
  contributes multiplicity one, so the total analytic multiplicity in a set is
  the number of roots in that set.
proof:
  Apply the simple-root computation at each point of the finite fiber and sum
  the resulting constant contribution.
-/
theorem complexAnalyticLevelMultiplicityOnSet_complex_pow_nonzero
    {U : Set ℂ} {n : ℕ} (hn : 0 < n) {a : ℂ} (ha : a ≠ 0)
    (hfinite : ∀ a : ℂ, {z : ℂ | z ∈ U ∧ z ^ n = a}.Finite) :
    complexAnalyticLevelMultiplicityOnSet
        (fun z : ℂ ↦ z ^ n) U hfinite a =
      (hfinite a).toFinset.card := by
  classical
  change (hfinite a).toFinset.sum
      (fun z ↦ analyticOrderNatAt (fun w : ℂ ↦ w ^ n - a) z) =
    (hfinite a).toFinset.card
  calc
    (hfinite a).toFinset.sum
        (fun z ↦ analyticOrderNatAt (fun w : ℂ ↦ w ^ n - a) z) =
        (hfinite a).toFinset.sum (fun _ : ℂ ↦ 1) := by
      refine Finset.sum_congr rfl ?_
      intro z hz
      have hzpow : z ^ n = a :=
        ((hfinite a).mem_toFinset.mp hz).2
      exact analyticOrderNatAt_complex_pow_sub_eq_one_of_ne_zero hn hzpow ha
    _ = (hfinite a).toFinset.card := by
      simp

/--
%%handwave
name:
  Nonzero complex numbers have \(n\) distinct \(n\)th roots
statement:
  Every nonzero complex number has exactly \(n\) distinct \(n\)th roots when
  \(n>0\).
proof:
  Use a primitive \(n\)th root of unity in the complex plane.  The roots are
  obtained by multiplying one chosen \(n\)th root by the \(n\) powers of the
  primitive root, and these roots are distinct.
-/
theorem complex_nthRootsFinset_card_of_ne_zero
    {n : ℕ} (hn : 0 < n) {a : ℂ} (ha : a ≠ 0) :
    (Polynomial.nthRootsFinset n a : Finset ℂ).card = n := by
  classical
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n :=
    Complex.isPrimitiveRoot_exp n (Nat.ne_of_gt hn)
  have hroots_card : Multiset.card (Polynomial.nthRoots n a) = n := by
    have hex : ∃ α : ℂ, α ^ n = a :=
      IsAlgClosed.exists_pow_nat_eq a hn
    rw [hζ.card_nthRoots a, if_pos hex]
  rw [Polynomial.nthRootsFinset_def,
    ← Multiset.toFinset_eq (hζ.nthRoots_nodup ha), Finset.card_mk]
  exact hroots_card

/--
%%handwave
name:
  A set containing all roots has power-map multiplicity \(n\)
statement:
  If a set contains every root of a nonzero level of \(z\mapsto z^n\), then
  the total analytic multiplicity of that level inside the set is \(n\).
proof:
  For a nonzero level, every root is simple.  The set contains the entire
  finite fiber, and the complex \(n\)th-root count says that this fiber has
  exactly \(n\) points.
-/
theorem complexAnalyticLevelMultiplicityOnSet_complex_pow_nonzero_of_roots_subset
    {U : Set ℂ} {n : ℕ} (hn : 0 < n) {a : ℂ} (ha : a ≠ 0)
    (hfinite : ∀ a : ℂ, {z : ℂ | z ∈ U ∧ z ^ n = a}.Finite)
    (hroots_subset : ∀ z : ℂ, z ^ n = a → z ∈ U) :
    complexAnalyticLevelMultiplicityOnSet
        (fun z : ℂ ↦ z ^ n) U hfinite a = n := by
  classical
  have hcard :
      (hfinite a).toFinset.card = n := by
    have hfinset_eq :
        (hfinite a).toFinset = Polynomial.nthRootsFinset n a := by
      ext z
      constructor
      · intro hz
        have hzset : z ∈ U ∧ z ^ n = a :=
          (hfinite a).mem_toFinset.mp hz
        exact (Polynomial.mem_nthRootsFinset hn a).mpr hzset.2
      · intro hz
        have hzpow : z ^ n = a :=
          (Polynomial.mem_nthRootsFinset hn a).mp hz
        exact (hfinite a).mem_toFinset.mpr ⟨hroots_subset z hzpow, hzpow⟩
    rw [hfinset_eq]
    exact complex_nthRootsFinset_card_of_ne_zero hn ha
  rw [complexAnalyticLevelMultiplicityOnSet_complex_pow_nonzero hn ha hfinite,
    hcard]

/--
%%handwave
name:
  Small power-map levels have constant multiplicity
statement:
  In every neighborhood of the origin, all sufficiently small levels of
  \(z\mapsto z^n\) have total analytic multiplicity \(n\).
proof:
  Choose a small disk contained in the neighborhood.  If \(|a|<\epsilon^n\)
  and \(z^n=a\), then \(|z|<\epsilon\), so all roots of the level lie in the
  neighborhood.  The zero level is counted by the monomial-order computation,
  and nonzero levels are counted by the complete-root-set result.
-/
theorem complexAnalyticLevelMultiplicityOnSet_complex_pow_eventually_eq
    {U : Set ℂ} {n : ℕ} (hn : 0 < n) (hU : U ∈ 𝓝 (0 : ℂ))
    (hfinite : ∀ a : ℂ, {z : ℂ | z ∈ U ∧ z ^ n = a}.Finite) :
    ∀ᶠ a in 𝓝 (0 : ℂ),
      complexAnalyticLevelMultiplicityOnSet
          (fun z : ℂ ↦ z ^ n) U hfinite a = n := by
  classical
  have h0U : (0 : ℂ) ∈ U :=
    mem_of_mem_nhds hU
  rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε_pos, hε_subset⟩
  let δ : ℝ := ε ^ n
  have hδ_pos : 0 < δ :=
    pow_pos hε_pos n
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ_pos] with a ha
  by_cases ha0 : a = 0
  · subst a
    exact complexAnalyticLevelMultiplicityOnSet_complex_pow_zero hn h0U hfinite
  · refine
      complexAnalyticLevelMultiplicityOnSet_complex_pow_nonzero_of_roots_subset
        hn ha0 hfinite ?_
    intro z hzpow
    have ha_norm_lt : ‖a‖ < ε ^ n := by
      simpa [Metric.mem_ball, dist_eq_norm, δ] using ha
    have hz_norm_pow : ‖z‖ ^ n = ‖a‖ := by
      rw [← norm_pow, hzpow]
    have hz_norm_lt : ‖z‖ < ε := by
      exact lt_of_pow_lt_pow_left₀ n hε_pos.le (by
        simpa [hz_norm_pow] using ha_norm_lt)
    exact hε_subset (by
      simpa [Metric.mem_ball, dist_eq_norm] using hz_norm_lt)

/--
%%handwave
name:
  Local factorized level count
statement:
  Suppose a level equation near a point has the local form
  \((z-z_0)^n\) times a nonvanishing analytic factor, and suppose nearby
  level points in the ambient disk are already confined to arbitrarily small
  neighborhoods of the point.  Then all sufficiently nearby levels have total
  analytic multiplicity equal to the local order at the point.
proof:
  If \(n=0\), the function is locally separated from the original level value,
  so nearby localized fibers are empty and both sides are zero.  For positive
  \(n\), choose a local analytic \(n\)th root of the nonvanishing factor and
  use the corresponding branch coordinate to reduce the level equation to the
  power map \(w\mapsto w^n\).  The small-level power-map count gives total
  multiplicity \(n\), and the localization hypothesis ensures that no roots
  outside this coordinate neighborhood contribute.
-/
theorem complexAnalyticLevelMultiplicityOnBall_eventually_eq_localMultiplicity_of_localized_factorization
    {F g : ℂ → ℂ} {a₀ z₀ : ℂ} {r : ℝ} {n : ℕ}
    (_hF : ∀ z : ℂ, z ∈ Metric.closedBall z₀ r → AnalyticAt ℂ F z)
    (hfinite : ∀ a : ℂ,
      {z : ℂ | z ∈ Metric.ball z₀ r ∧ F z = a}.Finite)
    (_hr : 0 < r)
    (_hg : AnalyticAt ℂ g z₀) (_hg_ne : g z₀ ≠ 0)
    (_hfactor :
      (fun z : ℂ ↦ F z - a₀) =ᶠ[𝓝 z₀]
        fun z : ℂ ↦ (z - z₀) ^ n * g z)
    (_hn : n = analyticOrderNatAt (fun z : ℂ ↦ F z - a₀) z₀)
    (_hlocalized :
      ∀ U : Set ℂ, U ∈ 𝓝 z₀ →
        ∀ᶠ a in 𝓝 a₀,
          ∀ z : ℂ, z ∈ Metric.ball z₀ r → F z = a → z ∈ U) :
    ∀ᶠ a in 𝓝 a₀,
      complexAnalyticLevelMultiplicityOnSet F (Metric.ball z₀ r) hfinite a =
        analyticOrderNatAt (fun z : ℂ ↦ F z - a₀) z₀ := by
  by_cases hn0 : n = 0
  · have hz₀_closed : z₀ ∈ Metric.closedBall z₀ r := by
      simpa [Metric.mem_closedBall] using _hr.le
    have hF_cont : ContinuousAt F z₀ :=
      (_hF z₀ hz₀_closed).continuousAt
    have hsub_ne : F z₀ - a₀ ≠ 0 := by
      have hsub_eq : F z₀ - a₀ = g z₀ := by
        simpa [hn0] using _hfactor.self_of_nhds
      simpa [hsub_eq] using _hg_ne
    have hFz₀_ne : F z₀ ≠ a₀ :=
      sub_ne_zero.mp hsub_ne
    let δ : ℝ := dist (F z₀) a₀ / 2
    have hδ_pos : 0 < δ := by
      have hd_pos : 0 < dist (F z₀) a₀ :=
        dist_pos.mpr hFz₀_ne
      dsimp [δ]
      linarith
    let U : Set ℂ := F ⁻¹' Metric.ball (F z₀) δ
    have hU_nhds : U ∈ 𝓝 z₀ :=
      hF_cont (Metric.ball_mem_nhds (F z₀) hδ_pos)
    have hloc :
        ∀ᶠ a in 𝓝 a₀,
          ∀ z : ℂ, z ∈ Metric.ball z₀ r → F z = a → z ∈ U :=
      _hlocalized U hU_nhds
    have ha_near : Metric.ball a₀ δ ∈ 𝓝 a₀ :=
      Metric.ball_mem_nhds a₀ hδ_pos
    filter_upwards [hloc, ha_near] with a hloca ha_ball
    have hno_fiber :
        ∀ z : ℂ, ¬ (z ∈ Metric.ball z₀ r ∧ F z = a) := by
      intro z hz
      rcases hz with ⟨hz_ball, hzF⟩
      have hzU : z ∈ U := hloca z hz_ball hzF
      have hdist_z : dist (F z) (F z₀) < δ := by
        simpa [U, Metric.mem_ball] using hzU
      have hdist_a : dist a a₀ < δ := by
        simpa [Metric.mem_ball] using ha_ball
      have hlt_self : dist (F z₀) a₀ < dist (F z₀) a₀ := by
        calc
          dist (F z₀) a₀ ≤ dist (F z₀) (F z) + dist (F z) a₀ :=
            dist_triangle (F z₀) (F z) a₀
          _ = dist (F z) (F z₀) + dist a a₀ := by
            rw [dist_comm (F z₀) (F z), hzF]
          _ < δ + δ := add_lt_add hdist_z hdist_a
          _ = dist (F z₀) a₀ := by
            dsimp [δ]
            ring
      exact (lt_irrefl _ hlt_self)
    have hfinset_empty : (hfinite a).toFinset = ∅ := by
      ext z
      constructor
      · intro hz
        exact False.elim (hno_fiber z ((hfinite a).mem_toFinset.mp hz))
      · intro hz
        simp at hz
    have hleft :
        complexAnalyticLevelMultiplicityOnSet F (Metric.ball z₀ r) hfinite a = 0 := by
      change (hfinite a).toFinset.sum
          (fun z ↦ analyticOrderNatAt (fun w : ℂ ↦ F w - a) z) = 0
      rw [hfinset_empty]
      simp
    have hright :
        analyticOrderNatAt (fun z : ℂ ↦ F z - a₀) z₀ = 0 :=
      _hn.symm.trans hn0
    exact hleft.trans hright.symm
  · have _hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    rcases analyticAt_exists_nthRoot_pow_eq_of_ne_zero _hg _hg_ne _hn_pos with
      ⟨ρ, hρ, hρ_ne, hρ_pow⟩
    let H : ℂ → ℂ := fun z : ℂ ↦ (z - z₀) * ρ z
    have hfactor_pow :
        (fun z : ℂ ↦ F z - a₀) =ᶠ[𝓝 z₀] fun z : ℂ ↦ H z ^ n := by
      filter_upwards [_hfactor] with z hz
      calc
        F z - a₀ = (z - z₀) ^ n * g z := hz
        _ = (z - z₀) ^ n * ρ z ^ n := by rw [hρ_pow z]
        _ = H z ^ n := by simp [H, mul_pow]
    have hH_an0 : AnalyticAt ℂ H z₀ := by
      simpa [H] using (analyticAt_id.sub analyticAt_const).mul hρ
    have hstrict : HasStrictDerivAt H (ρ z₀) z₀ := by
      simpa [H] using
        analyticAt_branchCoordinate_hasStrictDerivAt (z₀ := z₀) hρ
    have hH_deriv0 : deriv H z₀ ≠ 0 := by
      rw [hstrict.hasDerivAt.deriv]
      exact hρ_ne
    rcases analyticAt_branchCoordinate_local_injOn_image hρ hρ_ne with
      ⟨V, hV_nhds, hV_inj, hV_image⟩
    have hfactor_set :
        {z : ℂ | F z - a₀ = H z ^ n} ∈ 𝓝 z₀ := by
      exact hfactor_pow
    rcases mem_nhds_iff.mp hfactor_set with
      ⟨W, hW_subset, hW_open, hz₀W⟩
    have hW_nhds : W ∈ 𝓝 z₀ :=
      hW_open.mem_nhds hz₀W
    have hball_nhds : Metric.ball z₀ r ∈ 𝓝 z₀ :=
      Metric.ball_mem_nhds z₀ _hr
    have hA_nhds : {z : ℂ | AnalyticAt ℂ H z} ∈ 𝓝 z₀ :=
      hH_an0.eventually_analyticAt
    have hD_nhds : {z : ℂ | deriv H z ≠ 0} ∈ 𝓝 z₀ :=
      hH_an0.deriv.continuousAt.eventually_ne hH_deriv0
    let U : Set ℂ :=
      {z : ℂ | z ∈ Metric.ball z₀ r ∧ z ∈ V ∧ z ∈ W ∧
        AnalyticAt ℂ H z ∧ deriv H z ≠ 0}
    have hU_nhds : U ∈ 𝓝 z₀ := by
      dsimp [U]
      exact Filter.inter_mem hball_nhds
        (Filter.inter_mem hV_nhds
          (Filter.inter_mem hW_nhds
            (Filter.inter_mem hA_nhds hD_nhds)))
    have hU_subset_ball : U ⊆ Metric.ball z₀ r := by
      intro z hz
      exact hz.1
    have hU_subset_V : U ⊆ V := by
      intro z hz
      exact hz.2.1
    have hHU_nhds : H '' U ∈ 𝓝 (0 : ℂ) := by
      simpa [H] using hV_image U hU_nhds hU_subset_V
    have hfiniteU : ∀ a : ℂ, {z : ℂ | z ∈ U ∧ F z = a}.Finite := by
      intro a
      exact (hfinite a).subset (by
        intro z hz
        exact ⟨hU_subset_ball hz.1, hz.2⟩)
    have hfinitePow :
        ∀ b : ℂ, {w : ℂ | w ∈ H '' U ∧ w ^ n = b}.Finite := by
      intro b
      refine ((hfinite (a₀ + b)).image H).subset ?_
      intro w hw
      rcases hw.1 with ⟨z, hzU, rfl⟩
      have hzfactor : F z - a₀ = H z ^ n :=
        hW_subset hzU.2.2.1
      have hsub : F z - a₀ = b := by
        rw [hzfactor]
        exact hw.2
      have hzF : F z = a₀ + b := by
        calc
          F z = (F z - a₀) + a₀ := by ring
          _ = b + a₀ := by rw [hsub]
          _ = a₀ + b := by ring
      exact ⟨z, ⟨hzU.1, hzF⟩, rfl⟩
    have hpow_event :
        ∀ᶠ b in 𝓝 (0 : ℂ),
          complexAnalyticLevelMultiplicityOnSet
              (fun z : ℂ ↦ z ^ n) (H '' U) hfinitePow b = n :=
      complexAnalyticLevelMultiplicityOnSet_complex_pow_eventually_eq
        _hn_pos hHU_nhds hfinitePow
    have hshift_tendsto :
        Filter.Tendsto (fun a : ℂ ↦ a - a₀) (𝓝 a₀) (𝓝 (0 : ℂ)) := by
      have hcont :
          Filter.Tendsto (fun a : ℂ ↦ a - a₀) (𝓝 a₀) (𝓝 (a₀ - a₀)) :=
        (continuousAt_id.sub continuousAt_const :
          ContinuousAt (fun a : ℂ ↦ a - a₀) a₀)
      simpa using hcont
    have hpow_near :
        ∀ᶠ a in 𝓝 a₀,
          complexAnalyticLevelMultiplicityOnSet
              (fun z : ℂ ↦ z ^ n) (H '' U) hfinitePow (a - a₀) = n :=
      hshift_tendsto.eventually hpow_event
    have hloc :
        ∀ᶠ a in 𝓝 a₀,
          ∀ z : ℂ, z ∈ Metric.ball z₀ r → F z = a → z ∈ U :=
      _hlocalized U hU_nhds
    filter_upwards [hloc, hpow_near] with a hloca hpowa
    have hball_to_U :
        complexAnalyticLevelMultiplicityOnSet F (Metric.ball z₀ r) hfinite a =
          complexAnalyticLevelMultiplicityOnSet F U hfiniteU a := by
      exact
        complexAnalyticLevelMultiplicityOnSet_eq_of_mem_iff_on_level
          hfinite hfiniteU (a := a) (by
            intro z hzFa
            constructor
            · intro hzball
              exact hloca z hzball hzFa
            · intro hzU
              exact hU_subset_ball hzU)
    have hcoord_to_power :
        complexAnalyticLevelMultiplicityOnSet F U hfiniteU a =
          complexAnalyticLevelMultiplicityOnSet
            (fun w : ℂ ↦ w ^ n) (H '' U) hfinitePow (a - a₀) := by
      refine
        complexAnalyticLevelMultiplicityOnSet_eq_image_of_injOn
          (F := F) (P := fun w : ℂ ↦ w ^ n) (H := H) (U := U)
          (a := a) (b := a - a₀)
          hfiniteU hfinitePow ?_ ?_ ?_
      · intro z hzU ζ hζU hH
        exact hV_inj (hU_subset_V hzU) (hU_subset_V hζU) (by
          simpa [H] using hH)
      · intro z hzU
        have hzfactor : F z - a₀ = H z ^ n :=
          hW_subset hzU.2.2.1
        constructor
        · intro hzFa
          calc
            H z ^ n = F z - a₀ := hzfactor.symm
            _ = a - a₀ := by rw [hzFa]
        · intro hpow
          change H z ^ n = a - a₀ at hpow
          calc
            F z = (F z - a₀) + a₀ := by ring
            _ = H z ^ n + a₀ := by rw [hzfactor]
            _ = (a - a₀) + a₀ := by rw [hpow]
            _ = a := by ring
      · intro z hzU _hzFa
        refine
          analyticOrderNatAt_congr_comp_of_deriv_ne_zero
            (f := fun w : ℂ ↦ F w - a)
            (g := fun w : ℂ ↦ w ^ n - (a - a₀))
            (H := H) ?_ hzU.2.2.2.1 hzU.2.2.2.2
        exact Filter.eventually_of_mem (hW_open.mem_nhds hzU.2.2.1) (by
          intro w hwW
          have hwfactor : F w - a₀ = H w ^ n :=
            hW_subset hwW
          dsimp [Function.comp]
          calc
            F w - a = (F w - a₀) - (a - a₀) := by ring
            _ = H w ^ n - (a - a₀) := by rw [hwfactor])
    calc
      complexAnalyticLevelMultiplicityOnSet F (Metric.ball z₀ r) hfinite a =
          complexAnalyticLevelMultiplicityOnSet F U hfiniteU a := hball_to_U
      _ = complexAnalyticLevelMultiplicityOnSet
            (fun w : ℂ ↦ w ^ n) (H '' U) hfinitePow (a - a₀) :=
          hcoord_to_power
      _ = n := hpowa
      _ = analyticOrderNatAt (fun z : ℂ ↦ F z - a₀) z₀ := _hn

/--
%%handwave
name:
  Local zero-count conservation under localization of nearby fibers
statement:
  Let \(F\) be analytic on a closed ball \(\overline B(z_0,r)\), with finite
  level fibers in \(B(z_0,r)\), and suppose \(F(z_0)=a_0\).  If, for every
  neighborhood \(U\) of \(z_0\), all roots of \(F(z)=a\) in the ball lie in
  \(U\) for every sufficiently close \(a\) to \(a_0\), then eventually
  \[
    \sum_{\substack{z\in B(z_0,r)\\F(z)=a}}
      \operatorname{ord}_z(F-a)
      =\operatorname{ord}_{z_0}(F-a_0).
  \]
proof:
  Finiteness of the old level set makes the germ \(F-a_0\) have finite order.
  Factor it as \((z-z_0)^n g(z)\) with \(g(z_0)\ne0\), and apply the local
  conservation theorem for this factorization.  The localization hypothesis
  ensures that no nearby roots escape the factorization neighborhood.
-/
theorem complexAnalyticLevelMultiplicityOnBall_eventually_eq_localMultiplicity_of_eventually_localized
    {F : ℂ → ℂ} {a₀ z₀ : ℂ} {r : ℝ}
    (_hF : ∀ z : ℂ, z ∈ Metric.closedBall z₀ r → AnalyticAt ℂ F z)
    (hfinite : ∀ a : ℂ,
      {z : ℂ | z ∈ Metric.ball z₀ r ∧ F z = a}.Finite)
    (_hz₀ : F z₀ = a₀) (_hr : 0 < r)
    (_hlocalized :
      ∀ U : Set ℂ, U ∈ 𝓝 z₀ →
        ∀ᶠ a in 𝓝 a₀,
          ∀ z : ℂ, z ∈ Metric.ball z₀ r → F z = a → z ∈ U) :
    ∀ᶠ a in 𝓝 a₀,
      complexAnalyticLevelMultiplicityOnSet F (Metric.ball z₀ r) hfinite a =
        analyticOrderNatAt (fun z : ℂ ↦ F z - a₀) z₀ := by
  let f₀ : ℂ → ℂ := fun z : ℂ ↦ F z - a₀
  have hz₀_closed : z₀ ∈ Metric.closedBall z₀ r := by
    simpa [Metric.mem_closedBall] using _hr.le
  have hFz₀ : AnalyticAt ℂ F z₀ :=
    _hF z₀ hz₀_closed
  have hf₀ : AnalyticAt ℂ f₀ z₀ := by
    simpa [f₀] using hFz₀.sub analyticAt_const
  have horder_ne_top : analyticOrderAt f₀ z₀ ≠ ⊤ := by
    simpa [f₀] using
      analyticOrderAt_sub_ne_top_of_finite_level_in_ball
        (F := F) (a₀ := a₀) (z₀ := z₀) (r := r)
        (hfinite a₀) _hz₀ _hr
  rcases (hf₀.analyticOrderAt_ne_top.mp horder_ne_top) with
    ⟨g, hg, hg_ne, hfactor⟩
  let n : ℕ := analyticOrderNatAt f₀ z₀
  have hfactor_mul :
      (fun z : ℂ ↦ F z - a₀) =ᶠ[𝓝 z₀]
        fun z : ℂ ↦ (z - z₀) ^ n * g z := by
    filter_upwards [hfactor] with z hz
    simpa [f₀, n] using hz
  have hn :
      n = analyticOrderNatAt (fun z : ℂ ↦ F z - a₀) z₀ := by
    rfl
  exact
    complexAnalyticLevelMultiplicityOnBall_eventually_eq_localMultiplicity_of_localized_factorization
      _hF hfinite _hr hg hg_ne hfactor_mul hn _hlocalized

/--
%%handwave
name:
  Conservation of analytic zero count in an isolating ball
statement:
  Let \(F\) be analytic on \(\overline B(z_0,r)\), with finite level fibers in
  \(B(z_0,r)\), and suppose \(F(z_0)=a_0\).  If \(z_0\) is the only solution
  of \(F(z)=a_0\) in the closed ball, then for every sufficiently close
  \(a\) to \(a_0\), the total multiplicity of \(F(z)=a\) in the open ball is
  \(\operatorname{ord}_{z_0}(F-a_0)\).
proof:
  On the compact closed ball minus an arbitrary neighborhood of \(z_0\),
  continuity and isolation keep nearby level sets away from that complement.
  Thus all nearby roots localize at \(z_0\), and the localized conservation
  theorem applies.
-/
theorem complexAnalyticLevelMultiplicityOnBall_eventually_eq_localMultiplicity
    {F : ℂ → ℂ} {a₀ z₀ : ℂ} {r : ℝ}
    (_hF : ∀ z : ℂ, z ∈ Metric.closedBall z₀ r → AnalyticAt ℂ F z)
    (hfinite : ∀ a : ℂ,
      {z : ℂ | z ∈ Metric.ball z₀ r ∧ F z = a}.Finite)
    (_hz₀ : F z₀ = a₀) (_hr : 0 < r)
    (_hisolating :
      ∀ z : ℂ, z ∈ Metric.closedBall z₀ r → F z = a₀ → z = z₀) :
    ∀ᶠ a in 𝓝 a₀,
      complexAnalyticLevelMultiplicityOnSet F (Metric.ball z₀ r) hfinite a =
        analyticOrderNatAt (fun z : ℂ ↦ F z - a₀) z₀ := by
  have hF_cont : ContinuousOn F (Metric.closedBall z₀ r) := by
    intro z hz
    exact (_hF z hz).continuousAt.continuousWithinAt
  have hlocalized :
      ∀ U : Set ℂ, U ∈ 𝓝 z₀ →
        ∀ᶠ a in 𝓝 a₀,
          ∀ z : ℂ, z ∈ Metric.ball z₀ r → F z = a → z ∈ U := by
    intro U hU
    rcases mem_nhds_iff.mp hU with ⟨V, hVU, hV_open, hz₀V⟩
    filter_upwards
      [eventually_levelSet_ball_subset_open_of_isolated_on_closedBall
        hF_cont hV_open hz₀V _hisolating] with a ha z hz_ball hzF
    exact hVU (ha z hz_ball hzF)
  exact
    complexAnalyticLevelMultiplicityOnBall_eventually_eq_localMultiplicity_of_eventually_localized
      _hF hfinite _hz₀ _hr hlocalized

/--
%%handwave
name:
  Fiber multiplicity agrees with its coordinate-plane zero count
statement:
  Let \(\chi\) be a pointed surface coordinate and \(U\) a subset of its chart
  target.  For a complex-valued map \(f\) with finite fibers, the total local
  multiplicity of the fiber \(f^{-1}(a)\) in
  \(\chi^{-1}(U)\) equals the analytic zero count of
  \(z\mapsto f(\chi^{-1}(z))-a\) in \(U\).
proof:
  The chart is a bijection between the two finite level sets.  Reindex the
  finite sum by this bijection; invariance of local multiplicity under a
  change of pointed coordinate identifies corresponding summands.
-/
theorem holomorphicMapComplexFiberMultiplicityOnSet_eq_complexAnalyticLevelMultiplicityOnSet_coordinate
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {f : X → ℂ}
    (hfinite : ∀ a : ℂ, {x : X | f x = a}.Finite)
    {x₀ : X} (χ : PointedSurfaceCoordinate X x₀)
    {U : Set ℂ} (hU_target : U ⊆ χ.chart.target)
    (hfinite_plane : ∀ a : ℂ,
      {z : ℂ | z ∈ U ∧ f (χ.chart.symm z) = a}.Finite)
    (a : ℂ) :
    holomorphicMapComplexFiberMultiplicityOnSet f hfinite
        (χ.chart.source ∩ χ.chart ⁻¹' U) a =
      complexAnalyticLevelMultiplicityOnSet
        (fun z : ℂ ↦ f (χ.chart.symm z)) U hfinite_plane a := by
  classical
  let W : Set X := χ.chart.source ∩ χ.chart ⁻¹' U
  let s : Finset X := (hfinite a).toFinset.filter fun x ↦ x ∈ W
  let t : Finset ℂ := (hfinite_plane a).toFinset
  let mX : X → ℕ := fun x ↦
    holomorphicMapLocalMultiplicityAtValueInCoordinate
      (chartAtPointedSurfaceCoordinate X x) f a
  let mZ : ℂ → ℕ := fun z ↦
    analyticOrderNatAt (fun w : ℂ ↦ f (χ.chart.symm w) - a) z
  have hsum : s.sum mX = t.sum mZ := by
    refine Finset.sum_bij (fun x _hx ↦ χ.chart x) ?_ ?_ ?_ ?_
    · intro x hx
      have hx_filter : f x = a ∧ x ∈ W := by
        simpa [s] using hx
      have hx_fiber : f x = a := hx_filter.1
      have hxW : x ∈ W := hx_filter.2
      exact (hfinite_plane a).mem_toFinset.mpr
        ⟨hxW.2, by
          simpa [χ.chart.left_inv hxW.1] using hx_fiber⟩
    · intro x₁ hx₁ x₂ hx₂ hχ
      have hx₁W : x₁ ∈ W := (by simpa [s] using hx₁ : f x₁ = a ∧ x₁ ∈ W).2
      have hx₂W : x₂ ∈ W := (by simpa [s] using hx₂ : f x₂ = a ∧ x₂ ∈ W).2
      exact χ.chart.injOn hx₁W.1 hx₂W.1 hχ
    · intro z hz
      have hz_set :
          z ∈ U ∧ f (χ.chart.symm z) = a :=
        (hfinite_plane a).mem_toFinset.mp (by simpa [t] using hz)
      have hz_target : z ∈ χ.chart.target := hU_target hz_set.1
      let x : X := χ.chart.symm z
      have hx_source : x ∈ χ.chart.source := by
        dsimp [x]
        exact χ.chart.map_target hz_target
      have hx_fiber : f x = a := by
        dsimp [x]
        exact hz_set.2
      have hxW : x ∈ W := by
        refine ⟨hx_source, ?_⟩
        dsimp [x]
        simpa [χ.chart.right_inv hz_target] using hz_set.1
      refine ⟨x, ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨(hfinite a).mem_toFinset.mpr hx_fiber, hxW⟩
      · dsimp [x]
        exact χ.chart.right_inv hz_target
    · intro x hx
      have hxW : x ∈ W := (by simpa [s] using hx : f x = a ∧ x ∈ W).2
      let χx : PointedSurfaceCoordinate X x :=
        { chart := χ.chart
          chart_mem_atlas := χ.chart_mem_atlas
          base_mem_source := hxW.1 }
      calc
        mX x =
            holomorphicMapLocalMultiplicityAtValueInCoordinate χx f a := by
              dsimp [mX]
              exact
                (holomorphicMapLocalMultiplicityAtValueInCoordinate_congr_coordinate
                  χx (chartAtPointedSurfaceCoordinate X x) f a).symm
        _ = mZ (χ.chart x) := by
              simp [mZ, χx, holomorphicMapLocalMultiplicityAtValueInCoordinate]
  simpa [holomorphicMapComplexFiberMultiplicityOnSet,
    complexAnalyticLevelMultiplicityOnSet, W, s, t, mX, mZ] using hsum

/--
%%handwave
name:
  Conservation of fiber multiplicity in an isolating coordinate ball
statement:
  Let \(f:X\to\mathbb C\) be holomorphic with finite fibers and
  \(f(x_0)=a_0\).  Suppose a closed ball about \(\chi(x_0)\) lies in the chart
  target and its coordinate preimage contains no other point of
  \(f^{-1}(a_0)\).  Then, for all \(a\) near \(a_0\), the total multiplicity
  of \(f^{-1}(a)\) in the corresponding open coordinate ball equals the local
  multiplicity of \(f-a_0\) at \(x_0\).
proof:
  Transport the problem through \(\chi\) to the coordinate plane.  The
  isolating hypothesis becomes uniqueness of the old zero in a closed ball,
  so one-variable zero-count conservation applies.  The coordinate
  multiplicity identity transports the resulting count back to the surface.
-/
theorem holomorphicMapComplexFiberMultiplicityOnSet_eventually_eq_localMultiplicity_on_coordinate_ball
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {f : X → ℂ}
    (hf : HolomorphicMap X ℂ f)
    (hfinite : ∀ a : ℂ, {x : X | f x = a}.Finite)
    {a₀ : ℂ} {x₀ : X} (χ : PointedSurfaceCoordinate X x₀)
    (hx₀ : f x₀ = a₀) {r : ℝ} (hr : 0 < r)
    (hclosed : Metric.closedBall (χ.chart x₀) r ⊆ χ.chart.target)
    (hisolating :
      ∀ x : X, x ∈ χ.chart.source →
        χ.chart x ∈ Metric.closedBall (χ.chart x₀) r →
          f x = a₀ → x = x₀) :
    ∀ᶠ a in 𝓝 a₀,
      holomorphicMapComplexFiberMultiplicityOnSet f hfinite
          (χ.chart.source ∩ χ.chart ⁻¹' Metric.ball (χ.chart x₀) r) a =
        holomorphicMapLocalMultiplicityAtValueInCoordinate
          χ f a₀ := by
  classical
  let z₀ : ℂ := χ.chart x₀
  let F : ℂ → ℂ := fun z ↦ f (χ.chart.symm z)
  let U : Set ℂ := Metric.ball z₀ r
  have hU_target : U ⊆ χ.chart.target := by
    intro z hz
    exact hclosed (Metric.ball_subset_closedBall hz)
  have hfinite_plane :
      ∀ a : ℂ, {z : ℂ | z ∈ U ∧ F z = a}.Finite := by
    intro a
    exact ((hfinite a).image χ.chart).subset (by
      intro z hz
      have hz_target : z ∈ χ.chart.target := hU_target hz.1
      exact ⟨χ.chart.symm z, by simpa [F] using hz.2,
        χ.chart.right_inv hz_target⟩)
  have hF_closed :
      ∀ z : ℂ, z ∈ Metric.closedBall z₀ r → AnalyticAt ℂ F z := by
    intro z hz
    have hz_target : z ∈ χ.chart.target := hclosed (by simpa [z₀] using hz)
    have hx_source : χ.chart.symm z ∈ χ.chart.source :=
      χ.chart.map_target hz_target
    have h :=
      surface_coordinateExpression_analyticAt
        (X := X) (f := f) hf χ.chart_mem_atlas hx_source
    simpa [F, χ.chart.right_inv hz_target] using h
  have hz₀_value : F z₀ = a₀ := by
    simpa [F, z₀, χ.chart.left_inv χ.base_mem_source] using hx₀
  have hisolating_plane :
      ∀ z : ℂ, z ∈ Metric.closedBall z₀ r → F z = a₀ → z = z₀ := by
    intro z hz hzF
    have hz_target : z ∈ χ.chart.target := hclosed (by simpa [z₀] using hz)
    let x : X := χ.chart.symm z
    have hx_source : x ∈ χ.chart.source := by
      dsimp [x]
      exact χ.chart.map_target hz_target
    have hx_closed : χ.chart x ∈ Metric.closedBall (χ.chart x₀) r := by
      dsimp [x]
      simpa [z₀, χ.chart.right_inv hz_target] using hz
    have hx_f : f x = a₀ := by
      dsimp [x]
      simpa [F] using hzF
    have hx_eq : x = x₀ :=
      hisolating x hx_source hx_closed hx_f
    calc
      z = χ.chart x := (χ.chart.right_inv hz_target).symm
      _ = z₀ := by simp [z₀, hx_eq]
  have hplane_event :
      ∀ᶠ a in 𝓝 a₀,
        complexAnalyticLevelMultiplicityOnSet F U hfinite_plane a =
          analyticOrderNatAt (fun z : ℂ ↦ F z - a₀) z₀ := by
    simpa [F, U, z₀] using
      complexAnalyticLevelMultiplicityOnBall_eventually_eq_localMultiplicity
        (F := F) (a₀ := a₀) (z₀ := z₀) (r := r)
        hF_closed hfinite_plane hz₀_value hr hisolating_plane
  have hbridge :
      ∀ a : ℂ,
        holomorphicMapComplexFiberMultiplicityOnSet f hfinite
            (χ.chart.source ∩ χ.chart ⁻¹' U) a =
          complexAnalyticLevelMultiplicityOnSet F U hfinite_plane a := by
    intro a
    simpa [F] using
      holomorphicMapComplexFiberMultiplicityOnSet_eq_complexAnalyticLevelMultiplicityOnSet_coordinate
        (f := f) hfinite χ hU_target hfinite_plane a
  filter_upwards [hplane_event] with a ha
  calc
    holomorphicMapComplexFiberMultiplicityOnSet f hfinite
        (χ.chart.source ∩ χ.chart ⁻¹' Metric.ball (χ.chart x₀) r) a =
        complexAnalyticLevelMultiplicityOnSet F U hfinite_plane a := by
          simpa [U, z₀] using hbridge a
    _ = analyticOrderNatAt (fun z : ℂ ↦ F z - a₀) z₀ := ha
    _ = holomorphicMapLocalMultiplicityAtValueInCoordinate χ f a₀ := by
          simp [holomorphicMapLocalMultiplicityAtValueInCoordinate, F, z₀]

/--
%%handwave
name:
  A small neighborhood conserving local fiber multiplicity
statement:
  Let \(f:X\to\mathbb C\) be holomorphic with finite fibers, let
  \(f(x_0)=a_0\), and let \(U\) be an open neighborhood of \(x_0\).  There is
  an open \(W\) with \(x_0\in W\subseteq U\) such that, for every sufficiently
  close \(a\) to \(a_0\), the multiplicity of \(f^{-1}(a)\) in \(W\) equals
  the local multiplicity of \(f-a_0\) at \(x_0\).
proof:
  Remove the finitely many other points of the old fiber and choose a small
  closed coordinate ball inside both \(U\) and this complement.  Its open
  preimage is \(W\); the closed ball isolates \(x_0\), so coordinate-ball
  conservation gives the asserted eventual equality.
-/
theorem holomorphicMapComplexFiberMultiplicityOnSet_eventually_eq_localMultiplicity_on_small_nhds
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {f : X → ℂ}
    (hf : HolomorphicMap X ℂ f)
    (hfinite : ∀ a : ℂ, {x : X | f x = a}.Finite)
    {a₀ : ℂ} {U : Set X} {x₀ : X}
    (hU_open : IsOpen U) (hx₀U : x₀ ∈ U) (hx₀ : f x₀ = a₀) :
    ∃ W : Set X,
      IsOpen W ∧ x₀ ∈ W ∧ W ⊆ U ∧
        ∀ᶠ a in 𝓝 a₀,
          holomorphicMapComplexFiberMultiplicityOnSet f hfinite W a =
            holomorphicMapLocalMultiplicityAtValueInCoordinate
              (chartAtPointedSurfaceCoordinate X x₀) f a₀ := by
  let χ : PointedSurfaceCoordinate X x₀ := chartAtPointedSurfaceCoordinate X x₀
  let z₀ : ℂ := χ.chart x₀
  have hz₀_target : z₀ ∈ χ.chart.target := by
    dsimp [z₀]
    exact χ.chart.map_source χ.base_mem_source
  have htarget_nhds : χ.chart.target ∈ 𝓝 z₀ :=
    χ.chart.open_target.mem_nhds hz₀_target
  let S : Set X := {x : X | f x = a₀} \ {x₀}
  have hS_finite : S.Finite :=
    (hfinite a₀).subset (by
      intro x hx
      exact hx.1)
  have hS_closed : IsClosed S := hS_finite.isClosed
  have hx₀_not_S : x₀ ∉ S := by
    simp [S]
  have hnotS_nhds : Sᶜ ∈ 𝓝 x₀ :=
    hS_closed.isOpen_compl.mem_nhds hx₀_not_S
  have hsymm_x₀ : χ.chart.symm z₀ = x₀ := by
    simpa [z₀] using χ.chart.left_inv χ.base_mem_source
  have hsymm_preU : χ.chart.symm ⁻¹' U ∈ 𝓝 z₀ := by
    have hU_nhds : U ∈ 𝓝 (χ.chart.symm z₀) := by
      simpa [hsymm_x₀] using hU_open.mem_nhds hx₀U
    exact χ.chart.continuousAt_symm hz₀_target hU_nhds
  have hsymm_pre_notS : χ.chart.symm ⁻¹' Sᶜ ∈ 𝓝 z₀ := by
    have hnotS_nhds_z₀ : Sᶜ ∈ 𝓝 (χ.chart.symm z₀) := by
      simpa [hsymm_x₀] using hnotS_nhds
    exact χ.chart.continuousAt_symm hz₀_target hnotS_nhds_z₀
  have hgood_nhds :
      χ.chart.target ∩ χ.chart.symm ⁻¹' U ∩ χ.chart.symm ⁻¹' Sᶜ ∈ 𝓝 z₀ :=
    Filter.inter_mem (Filter.inter_mem htarget_nhds hsymm_preU)
      hsymm_pre_notS
  rcases Metric.nhds_basis_closedBall.mem_iff.mp hgood_nhds with
    ⟨r, hr, hclosed_sub⟩
  let W : Set X := χ.chart.source ∩ χ.chart ⁻¹' Metric.ball z₀ r
  have hclosed_target : Metric.closedBall z₀ r ⊆ χ.chart.target := by
    intro z hz
    exact (hclosed_sub hz).1.1
  have hclosed_isolating :
      ∀ x : X, x ∈ χ.chart.source →
        χ.chart x ∈ Metric.closedBall (χ.chart x₀) r →
          f x = a₀ → x = x₀ := by
    intro x hx_source hx_closed hx_f
    by_contra hx_ne
    have hx_closed_z₀ : χ.chart x ∈ Metric.closedBall z₀ r := by
      simpa [z₀] using hx_closed
    have hx_notS_symm : χ.chart.symm (χ.chart x) ∈ Sᶜ :=
      (hclosed_sub hx_closed_z₀).2
    have hx_notS : x ∈ Sᶜ := by
      simpa [χ.chart.left_inv hx_source] using hx_notS_symm
    exact hx_notS ⟨hx_f, by
      simpa [Set.mem_singleton_iff] using hx_ne⟩
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · dsimp [W, z₀]
    exact χ.chart.isOpen_inter_preimage Metric.isOpen_ball
  · dsimp [W, z₀]
    exact ⟨χ.base_mem_source, by simp [Metric.mem_ball, hr]⟩
  · intro x hx
    have hx_closed : χ.chart x ∈ Metric.closedBall z₀ r :=
      Metric.ball_subset_closedBall hx.2
    have hx_preU : χ.chart.symm (χ.chart x) ∈ U :=
      (hclosed_sub hx_closed).1.2
    simpa [χ.chart.left_inv hx.1] using hx_preU
  · simpa [W, z₀] using
      holomorphicMapComplexFiberMultiplicityOnSet_eventually_eq_localMultiplicity_on_coordinate_ball
        (f := f) hf hfinite χ hx₀ hr hclosed_target hclosed_isolating

/--
%%handwave
name:
  Conservation of multiplicity in one isolating neighborhood
statement:
  Let \(f:X\to\mathbb C\) be holomorphic with finite fibers and proper over a
  neighborhood of \(a_0\).  Let \(U\) be an open neighborhood of
  \(x_0\in f^{-1}(a_0)\) which contains no other old fiber point, and assume
  every other old fiber point has a neighborhood disjoint from \(U\).  Then,
  for all \(a\) near \(a_0\), the total multiplicity of \(f^{-1}(a)\) inside
  \(U\) equals its value at \(a_0\).
proof:
  Choose a smaller neighborhood \(W\subseteq U\) on which local zero-count
  conservation gives the multiplicity at \(x_0\).  Properness confines every
  nearby preimage either to \(W\) or outside \(U\), so the counts in \(U\) and
  \(W\) agree.  The old count in \(U\) is the same local multiplicity.
-/
theorem holomorphicMapComplexFiberMultiplicityOnSet_eventually_eq_base
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {f : X → ℂ}
    (hf : HolomorphicMap X ℂ f)
    {a₀ : ℂ} {U : Set X} {x₀ : X}
    (hproper_local : IsProperOverComplexNeighborhood f a₀)
    (hfinite : ∀ a : ℂ, {x : X | f x = a}.Finite)
    (hU_open : IsOpen U) (hx₀U : x₀ ∈ U) (hx₀ : f x₀ = a₀)
    (hisolating : U ∩ {x : X | f x = a₀} ⊆ {x₀})
    (hisolating_nhds :
      ∀ x : X, f x = a₀ → x ≠ x₀ → ∀ᶠ y in 𝓝 x, y ∉ U) :
    ∀ᶠ a in 𝓝 a₀,
      holomorphicMapComplexFiberMultiplicityOnSet f hfinite U a =
        holomorphicMapComplexFiberMultiplicityOnSet f hfinite U a₀ := by
  classical
  rcases
      holomorphicMapComplexFiberMultiplicityOnSet_eventually_eq_localMultiplicity_on_small_nhds
        (f := f) hf hfinite hU_open hx₀U hx₀ with
    ⟨W, hW_open, hx₀W, hWU, hW_event⟩
  have hbase :
      holomorphicMapComplexFiberMultiplicityOnSet f hfinite U a₀ =
        holomorphicMapLocalMultiplicityAtValueInCoordinate
          (chartAtPointedSurfaceCoordinate X x₀) f a₀ :=
    holomorphicMapComplexFiberMultiplicityOnSet_eq_localMultiplicity_at_base
      hfinite hx₀U hx₀ hisolating
  have hfiber_control :
      ∀ᶠ a in 𝓝 a₀, ∀ x : X, f x = a → x ∈ W ∨ x ∉ U :=
    eventually_fiber_forall_of_isProperOverComplexNeighborhood
      hf.continuous hproper_local (by
        intro x hx
        by_cases hxx₀ : x = x₀
        · subst hxx₀
          exact Filter.mem_of_superset (hW_open.mem_nhds hx₀W)
            (fun y hy ↦ Or.inl hy)
        · exact Filter.mem_of_superset (hisolating_nhds x hx hxx₀)
            (fun y hy ↦ Or.inr hy))
  filter_upwards [hW_event, hfiber_control] with a hW_count hcontrol
  have hUW :
      holomorphicMapComplexFiberMultiplicityOnSet f hfinite U a =
        holomorphicMapComplexFiberMultiplicityOnSet f hfinite W a :=
    holomorphicMapComplexFiberMultiplicityOnSet_eq_of_mem_iff_on_fiber
      hfinite (by
        intro x hx
        constructor
        · intro hxU
          rcases hcontrol x hx with hxW | hx_not_U
          · exact hxW
          · exact False.elim (hx_not_U hxU)
        · intro hxW
          exact hWU hxW)
  calc
    holomorphicMapComplexFiberMultiplicityOnSet f hfinite U a =
        holomorphicMapComplexFiberMultiplicityOnSet f hfinite W a := hUW
    _ =
        holomorphicMapLocalMultiplicityAtValueInCoordinate
          (chartAtPointedSurfaceCoordinate X x₀) f a₀ := hW_count
    _ = holomorphicMapComplexFiberMultiplicityOnSet f hfinite U a₀ := hbase.symm

/--
%%handwave
name:
  Coordinate-model conservation in one fiber neighborhood
statement:
  Let \(F:X\to Y\) be proper and let an open embedding
  \(\varphi:Y\to\mathbb C\) make \(\varphi\circ F\) holomorphic.  Around the
  finite fiber over \(y_0\), choose pairwise disjoint open neighborhoods
  \(U_x\), one for each old fiber point.  For each \(x_0\in F^{-1}(y_0)\), the
  total multiplicity of \(F^{-1}(y)\) inside \(U_{x_0}\) is eventually equal
  to its value at \(y_0\).
proof:
  The coordinate embedding turns target neighborhoods into complex
  neighborhoods and preserves fiber equations by injectivity.  Each
  \(U_{x_0}\) is isolating by pairwise disjointness, while the other old fiber
  points are eventually outside it.  Apply complex-valued local conservation
  and pull the eventual statement back through \(\varphi\).
-/
theorem holomorphicMapFiberMultiplicityInCoordinateModelOnSet_eventually_eq_base
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_open : Topology.IsOpenEmbedding φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (_hproper : IsProperMap F)
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    {y₀ : Y} {U : X → Set X}
    (hU : ∀ x : X, F x = y₀ → x ∈ U x ∧ IsOpen (U x))
    (hpair : ({x : X | F x = y₀}.PairwiseDisjoint U))
    (x₀ : {x : X | F x = y₀}) :
    ∀ᶠ y in 𝓝 y₀,
      holomorphicMapFiberMultiplicityInCoordinateModelOnSet
          F φ hfinite (U x₀.1) y =
        holomorphicMapFiberMultiplicityInCoordinateModelOnSet
          F φ hfinite (U x₀.1) y₀ := by
  classical
  let f : X → ℂ := fun x ↦ φ (F x)
  let hfinite_complex : ∀ a : ℂ, {x : X | f x = a}.Finite :=
    finite_complexModel_fiber_of_finite_target_fibers
      (F := F) (φ := φ) hφ_open.injective hfinite
  have hx₀_complex : f x₀.1 = φ y₀ := by
    exact congrArg φ x₀.2
  have hU_mem : ∀ x : X, F x = y₀ → x ∈ U x :=
    fun x hx ↦ (hU x hx).1
  have hisolating :
      U x₀.1 ∩ {x : X | f x = φ y₀} ⊆ {x₀.1} := by
    intro z hz
    have hzF : F z = y₀ := hφ_open.injective hz.2
    exact Set.mem_singleton_iff.mpr
      (eq_of_old_fiber_mem_pairwiseDisjoint_fiber_neighborhood
        hU_mem hpair x₀.2 hzF hz.1)
  have hisolating_nhds :
      ∀ z : X, f z = φ y₀ → z ≠ x₀.1 →
        ∀ᶠ w in 𝓝 z, w ∉ U x₀.1 := by
    intro z hz_complex hz_ne
    have hzF : F z = y₀ := hφ_open.injective hz_complex
    exact
      eventually_not_mem_fiber_neighborhood_of_pairwiseDisjoint_ne
        (f := F) (y₀ := y₀) (U := U) hU hpair x₀.2 hzF hz_ne
  have hcomplex_event :
      ∀ᶠ a in 𝓝 (φ y₀),
        holomorphicMapComplexFiberMultiplicityOnSet
            f hfinite_complex (U x₀.1) a =
          holomorphicMapComplexFiberMultiplicityOnSet
            f hfinite_complex (U x₀.1) (φ y₀) :=
    holomorphicMapComplexFiberMultiplicityOnSet_eventually_eq_base
      (f := f) hF
      (isProperOverComplexNeighborhood_of_proper_openComplexModel
        (F := F) (φ := φ) hφ_open _hproper y₀)
      hfinite_complex
      (hU x₀.1 x₀.2).2 (hU x₀.1 x₀.2).1 hx₀_complex
      hisolating hisolating_nhds
  rw [eventually_nhds_complexModel_iff hφ_open]
  filter_upwards [hcomplex_event] with a ha y hy
  calc
    holomorphicMapFiberMultiplicityInCoordinateModelOnSet
        F φ hfinite (U x₀.1) y =
        holomorphicMapComplexFiberMultiplicityOnSet
          f hfinite_complex (U x₀.1) (φ y) := by
      simpa [f, hfinite_complex] using
        holomorphicMapFiberMultiplicityInCoordinateModelOnSet_eq_complexFiberMultiplicity
          (F := F) (φ := φ) hφ_open.injective hfinite (U x₀.1) y
    _ = holomorphicMapComplexFiberMultiplicityOnSet
          f hfinite_complex (U x₀.1) (φ y₀) := by
      simpa [hy]
        using ha
    _ = holomorphicMapFiberMultiplicityInCoordinateModelOnSet
          F φ hfinite (U x₀.1) y₀ := by
      simpa [f, hfinite_complex] using
        (holomorphicMapFiberMultiplicityInCoordinateModelOnSet_eq_complexFiberMultiplicity
          (F := F) (φ := φ) hφ_open.injective hfinite (U x₀.1) y₀).symm

/--
%%handwave
name:
  Local fiber contribution equals the old local multiplicity
statement:
  Under the proper holomorphic coordinate-model hypotheses and a pairwise
  disjoint system of neighborhoods of the fiber over \(y_0\), the
  multiplicity contributed inside the neighborhood of
  \(x_0\in F^{-1}(y_0)\) is, for all nearby \(y\), equal to the local
  multiplicity of \(\varphi\circ F-\varphi(y_0)\) at \(x_0\).
proof:
  Local coordinate-model conservation first identifies the nearby
  contribution with the contribution at \(y_0\).  Pairwise disjointness makes
  \(x_0\) the only old fiber point in its neighborhood, so the old
  contribution is exactly its local multiplicity.
-/
theorem holomorphicMapFiberMultiplicityInCoordinateModelOnSet_eventually_eq_localMultiplicity
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_open : Topology.IsOpenEmbedding φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hproper : IsProperMap F)
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    {y₀ : Y} {U : X → Set X}
    (hU : ∀ x : X, F x = y₀ → x ∈ U x ∧ IsOpen (U x))
    (hpair : ({x : X | F x = y₀}.PairwiseDisjoint U))
    (x₀ : {x : X | F x = y₀}) :
    ∀ᶠ y in 𝓝 y₀,
      holomorphicMapFiberMultiplicityInCoordinateModelOnSet
          F φ hfinite (U x₀.1) y =
        holomorphicMapLocalMultiplicityAtValueInCoordinate
          (chartAtPointedSurfaceCoordinate X x₀.1)
          (fun x : X ↦ φ (F x)) (φ y₀) := by
  have hbase :
      holomorphicMapFiberMultiplicityInCoordinateModelOnSet
          F φ hfinite (U x₀.1) y₀ =
        holomorphicMapLocalMultiplicityAtValueInCoordinate
          (chartAtPointedSurfaceCoordinate X x₀.1)
          (fun x : X ↦ φ (F x)) (φ y₀) :=
    holomorphicMapFiberMultiplicityInCoordinateModelOnSet_eq_localMultiplicity_at_base
      hfinite (fun x hx ↦ (hU x hx).1) hpair x₀
  filter_upwards
    [holomorphicMapFiberMultiplicityInCoordinateModelOnSet_eventually_eq_base
      hφ_open hF hproper hfinite hU hpair x₀] with y hy
  exact hy.trans hbase

/--
%%handwave
name:
  Local conservation of total multiplicity for a proper holomorphic map
statement:
  Let \(F:X\to Y\) be proper with finite fibers and surjective image, and let
  an open embedding \(\varphi:Y\to\mathbb C\) make \(\varphi\circ F\)
  holomorphic.  For every \(y_0\in Y\), all sufficiently nearby \(y\) satisfy
  \[
    \sum_{x\in F^{-1}(y)}m_x(F)
      =\sum_{x\in F^{-1}(y_0)}m_x(F).
  \]
proof:
  In the nonconstant case, properness gives finitely many pairwise disjoint
  neighborhoods of the old fiber which capture each nearby fiber exactly
  once.  Sum the locally conserved contribution from each neighborhood.  In
  the constant-range case, surjectivity and injectivity of \(\varphi\) make
  the target a singleton, so the assertion is immediate.
-/
theorem proper_holomorphicMap_fiberMultiplicity_eventually_eq_to_complexModel
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_open : Topology.IsOpenEmbedding φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hproper : IsProperMap F)
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    (hsurjective : Function.Surjective F) :
    ∀ y₀ : Y,
      ∀ᶠ y in 𝓝 y₀,
        holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y =
          holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y₀ := by
  classical
  intro y₀
  by_cases hnonconstant : (Set.range fun x : X ↦ φ (F x)).Nontrivial
  · rcases
      proper_holomorphicMap_to_openComplexModel_eventually_fiber_neighborhood_data
        hφ_open hF hproper hnonconstant (hfinite y₀) with
      ⟨U, hU, hpair, hdata_event⟩
    let t : Finset X := (hfinite y₀).toFinset
    have hlocal_event :
        ∀ᶠ y in 𝓝 y₀,
          ∀ x₀ ∈ t,
            holomorphicMapFiberMultiplicityInCoordinateModelOnSet
                F φ hfinite (U x₀) y =
              holomorphicMapLocalMultiplicityAtValueInCoordinate
                (chartAtPointedSurfaceCoordinate X x₀)
                (fun x : X ↦ φ (F x)) (φ y₀) := by
      rw [Finset.eventually_all]
      intro x₀ hx₀
      have hx₀_fiber : F x₀ = y₀ :=
        (hfinite y₀).mem_toFinset.mp (by simpa [t] using hx₀)
      simpa using
        holomorphicMapFiberMultiplicityInCoordinateModelOnSet_eventually_eq_localMultiplicity
          hφ_open hF hproper hfinite hU hpair
          (⟨x₀, hx₀_fiber⟩ : {x : X | F x = y₀})
    filter_upwards [hdata_event, hlocal_event] with y hdata hlocal
    rcases hdata with ⟨hcover, _hunique, _hhit⟩
    calc
      holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y =
          t.sum fun x₀ ↦
            holomorphicMapFiberMultiplicityInCoordinateModelOnSet
              F φ hfinite (U x₀) y := by
        simpa [t] using
          holomorphicMapFiberMultiplicityInCoordinateModel_eq_sum_on_fiber_neighborhoods
            (F := F) (φ := φ) hfinite hpair hcover
      _ = t.sum fun x₀ ↦
            holomorphicMapLocalMultiplicityAtValueInCoordinate
              (chartAtPointedSurfaceCoordinate X x₀)
              (fun x : X ↦ φ (F x)) (φ y₀) := by
        refine Finset.sum_congr rfl ?_
        intro x₀ hx₀
        exact hlocal x₀ hx₀
      _ = holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y₀ := by
        simp [holomorphicMapFiberMultiplicityInCoordinateModel, t]
  · have hrange_subsingleton :
        (Set.range fun x : X ↦ φ (F x)).Subsingleton :=
      Set.not_nontrivial_iff.mp hnonconstant
    have hY_subsingleton : Subsingleton Y := by
      refine ⟨?_⟩
      intro y y'
      rcases hsurjective y with ⟨x, rfl⟩
      rcases hsurjective y' with ⟨x', rfl⟩
      apply hφ_open.injective
      exact hrange_subsingleton
        ⟨x, rfl⟩
        ⟨x', rfl⟩
    letI : Subsingleton Y := hY_subsingleton
    filter_upwards [] with y
    have hy : y = y₀ := Subsingleton.elim y y₀
    simp [hy]

/--
%%handwave
name:
  Local constancy of total multiplicity for a proper holomorphic map
statement:
  Let \(F:X\to Y\) be proper with finite fibers and surjective image, and
  suppose an open embedding \(\varphi:Y\to\mathbb C\) makes
  \(\varphi\circ F\) holomorphic.  Then
  \(y\mapsto\sum_{x\in F^{-1}(y)}m_x(F)\) is locally constant.
proof:
  The local multiplicity theorem supplies, at each target point, a
  neighborhood on which the total fiber multiplicity equals its value at the
  center.  This is exactly the neighborhood characterization of local
  constancy.
-/
theorem proper_holomorphicMap_fiberMultiplicity_isLocallyConstant_to_complexModel
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_open : Topology.IsOpenEmbedding φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hproper : IsProperMap F)
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    (hsurjective : Function.Surjective F) :
    IsLocallyConstant
      (fun y : Y ↦
        holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y) := by
  exact IsLocallyConstant.iff_eventually_eq _ |>.mpr
    (proper_holomorphicMap_fiberMultiplicity_eventually_eq_to_complexModel
      hφ_open hF hproper hfinite hsurjective)

/--
%%handwave
name:
  Constancy of total multiplicity on a preconnected target
statement:
  Under the proper holomorphic finite-fiber hypotheses above, if \(Y\) is
  preconnected, then for every \(y,y_0\in Y\),
  \[
    \sum_{x\in F^{-1}(y)}m_x(F)=\sum_{x\in F^{-1}(y_0)}m_x(F).
  \]
proof:
  The total multiplicity is locally constant, and a locally constant function
  on a preconnected space takes the same value at every two points.
-/
theorem proper_holomorphicMap_fiberMultiplicity_constant_to_complexModel
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y] [PreconnectedSpace Y]
    {F : X → Y} {φ : Y → ℂ}
    (hφ_open : Topology.IsOpenEmbedding φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hproper : IsProperMap F)
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    (hsurjective : Function.Surjective F) :
    ∀ y y₀ : Y,
      holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y =
        holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y₀ := by
  intro y y₀
  exact
    (proper_holomorphicMap_fiberMultiplicity_isLocallyConstant_to_complexModel
      hφ_open hF hproper hfinite hsurjective).apply_eq_of_preconnectedSpace y y₀

/--
%%handwave
name:
  A simple single zero fixes every fiber multiplicity to one
statement:
  Suppose the proper holomorphic finite-fiber map \(F:X\to Y\) has a unique
  point \(p\) over the model value \(0\), and this point has local multiplicity
  one in every pointed coordinate.  Then the total multiplicity of every
  fiber \(F^{-1}(y)\) equals one.
proof:
  Total fiber multiplicity is constant on the preconnected target.  Evaluate
  it at \(F(p)\): the unique-zero hypothesis reduces that fiber to \(p\), and
  its local multiplicity is one.
-/
theorem proper_holomorphicMap_fiberMultiplicity_eq_one_of_simple_single_zero_to_complexModel
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y] [PreconnectedSpace Y]
    {p : X} {F : X → Y} {φ : Y → ℂ}
    (hφ_open : Topology.IsOpenEmbedding φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hproper : IsProperMap F)
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    (hsurjective : Function.Surjective F)
    (hzero : ∀ x : X, φ (F x) = 0 ↔ x = p)
    (hsimple : ∀ χ : PointedSurfaceCoordinate X p,
      holomorphicMapLocalMultiplicityAtValueInCoordinate χ
        (fun x : X ↦ φ (F x)) 0 = 1) :
    ∀ y : Y,
      holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y = 1 := by
  intro y
  calc
    holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite y =
        holomorphicMapFiberMultiplicityInCoordinateModel F φ hfinite (F p) :=
      proper_holomorphicMap_fiberMultiplicity_constant_to_complexModel
        hφ_open hF hproper hfinite hsurjective y (F p)
    _ = 1 :=
      holomorphicMapFiberMultiplicityInCoordinateModel_eq_one_at_simple_single_zero
        hfinite hzero hsimple

/--
%%handwave
name:
  Degree one from a unique simple model zero
statement:
  Let \(F:X\to Y\) be a proper surjective map with finite fibers from a
  Riemann surface to a preconnected target openly embedded in \(\mathbb C\).
  Suppose its coordinate expression is holomorphic, the model value \(0\) has
  the unique preimage \(p\), and that preimage has local multiplicity one.
  Then every \(y\in Y\) has a unique preimage under \(F\).
proof:
  Total fiber multiplicity is constant and the unique simple zero fiber fixes
  it to one.  A finite fiber whose positive local multiplicities sum to one
  contains exactly one point.
-/
theorem proper_holomorphicMap_degree_one_of_simple_single_zero_to_complexModel
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y] [PreconnectedSpace Y]
    {p : X} {F : X → Y} {φ : Y → ℂ}
    (hφ_open : Topology.IsOpenEmbedding φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hproper : IsProperMap F)
    (hfinite : ∀ y : Y, {x : X | F x = y}.Finite)
    (hsurjective : Function.Surjective F)
    (hzero : ∀ x : X, φ (F x) = 0 ↔ x = p)
    (hsimple : ∀ χ : PointedSurfaceCoordinate X p,
      holomorphicMapLocalMultiplicityAtValueInCoordinate χ
        (fun x : X ↦ φ (F x)) 0 = 1) :
    ∀ y : Y, ∃! x : X, F x = y := by
  exact existsUnique_of_fiberMultiplicityInCoordinateModel_eq_one_of_all
    hφ_open.injective hF hfinite
    (proper_holomorphicMap_fiberMultiplicity_eq_one_of_simple_single_zero_to_complexModel
      hφ_open hF hproper hfinite hsurjective hzero hsimple)

/--
%%handwave
name:
  A critical holomorphic germ has order at least two
statement:
  Let \(F:X\to\mathbb C\) be holomorphic, let \(\chi\) be a pointed coordinate
  at \(x\), and suppose \(F(x)=a\).  If the complex derivative of \(F\) in
  this coordinate vanishes, then the analytic order at \(x\) of \(F-a\) is at
  least two.
proof:
  In the coordinate expression, both the value and first derivative of
  \(F-a\) vanish at the base coordinate.  The characterization of analytic
  order by vanishing iterated derivatives gives order at least two.
-/
theorem two_le_holomorphicMapLocalOrderAtValueInCoordinate_of_deriv_eq_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {x : X} (χ : PointedSurfaceCoordinate X x)
    {F : X → ℂ} {a : ℂ}
    (hF : HolomorphicMap X ℂ F) (hxa : F x = a)
    (hderiv : surfaceComplexDerivativeInCoordinate χ F = 0) :
    (2 : ℕ∞) ≤ holomorphicMapLocalOrderAtValueInCoordinate χ F a := by
  let fcoord : ℂ → ℂ := fun z : ℂ ↦ F (χ.chart.symm z) - a
  let z₀ : ℂ := χ.chart x
  have hbase :
      AnalyticAt ℂ (fun z : ℂ ↦ F (χ.chart.symm z)) z₀ := by
    simpa [z₀] using
      surface_coordinateExpression_analyticAt
        (X := X) (f := F) hF χ.chart_mem_atlas χ.base_mem_source
  have hfcoord : AnalyticAt ℂ fcoord z₀ := by
    simpa [fcoord] using hbase.sub analyticAt_const
  have hleft : χ.chart.symm (χ.chart x) = x :=
    χ.chart.left_inv χ.base_mem_source
  have hfcoord_zero : fcoord z₀ = 0 := by
    simp [fcoord, z₀, hleft, hxa]
  have hderiv_coord : deriv fcoord z₀ = 0 := by
    simpa [fcoord, z₀, surfaceComplexDerivativeInCoordinate, deriv_sub_const]
      using hderiv
  rw [holomorphicMapLocalOrderAtValueInCoordinate]
  change ((2 : ℕ) : ℕ∞) ≤ analyticOrderAt fcoord z₀
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hfcoord]
  intro i hi
  interval_cases i
  · simpa [iteratedDeriv_zero] using hfcoord_zero
  · simpa [iteratedDeriv_one] using hderiv_coord

/--
%%handwave
name:
  Criticality gives local order at least two at the image value
statement:
  If a holomorphic map \(F:X\to\mathbb C\) has zero complex derivative at
  \(x\) in a pointed coordinate, then the local analytic order of
  \(F-F(x)\) at \(x\) is at least two.
proof:
  Apply the critical-order result with the target value \(a=F(x)\).
-/
theorem two_le_holomorphicMapLocalOrderInCoordinate_of_deriv_eq_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {x : X} (χ : PointedSurfaceCoordinate X x)
    {F : X → ℂ}
    (hF : HolomorphicMap X ℂ F)
    (hderiv : surfaceComplexDerivativeInCoordinate χ F = 0) :
    (2 : ℕ∞) ≤ holomorphicMapLocalOrderInCoordinate χ F := by
  exact
    two_le_holomorphicMapLocalOrderAtValueInCoordinate_of_deriv_eq_zero
      χ hF rfl hderiv

/--
%%handwave
name:
  Finite order at an injective critical point
statement:
  Let \(F:X\to\mathbb C\) be an injective holomorphic map and let \(\chi\) be
  a pointed coordinate at a critical point \(x\).  Then the local analytic
  order of \(F-F(x)\) is finite and at least two.
proof:
  Vanishing of the coordinate derivative gives order at least two.  Injectivity
  prevents the coordinate germ from being identically zero, so its analytic
  order is not infinite.
-/
theorem critical_holomorphicMapLocalOrderInCoordinate_finite_two_le_of_injective
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {x : X} (χ : PointedSurfaceCoordinate X x)
    {F : X → ℂ}
    (hF : HolomorphicMap X ℂ F)
    (hinj : Function.Injective F)
    (hderiv : surfaceComplexDerivativeInCoordinate χ F = 0) :
    (2 : ℕ∞) ≤ holomorphicMapLocalOrderInCoordinate χ F ∧
      holomorphicMapLocalOrderInCoordinate χ F ≠ ⊤ := by
  exact
    ⟨two_le_holomorphicMapLocalOrderInCoordinate_of_deriv_eq_zero
        χ hF hderiv,
      holomorphicMapLocalOrderInCoordinate_ne_top_of_injective χ hinj⟩

/--
%%handwave
name:
  Multiplicity at an injective critical point is at least two
statement:
  If an injective holomorphic map \(F:X\to\mathbb C\) has zero complex
  derivative at \(x\), then its local multiplicity at \(x\) in any pointed
  coordinate is at least two.
proof:
  The local analytic order is finite and at least two.  For a finite-order
  holomorphic germ, the natural local multiplicity is precisely that order,
  so it inherits the same lower bound.
-/
theorem two_le_holomorphicMapLocalMultiplicityInCoordinate_of_deriv_eq_zero_of_injective
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {x : X} (χ : PointedSurfaceCoordinate X x)
    {F : X → ℂ}
    (hF : HolomorphicMap X ℂ F)
    (hinj : Function.Injective F)
    (hderiv : surfaceComplexDerivativeInCoordinate χ F = 0) :
    2 ≤ holomorphicMapLocalMultiplicityInCoordinate χ F := by
  have hcrit :=
    critical_holomorphicMapLocalOrderInCoordinate_finite_two_le_of_injective
      χ hF hinj hderiv
  have hcast :
      (holomorphicMapLocalMultiplicityInCoordinate χ F : ℕ∞) =
        holomorphicMapLocalOrderInCoordinate χ F := by
    rw [holomorphicMapLocalMultiplicityInCoordinate,
      holomorphicMapLocalMultiplicityAtValueInCoordinate,
      holomorphicMapLocalOrderInCoordinate,
      holomorphicMapLocalOrderAtValueInCoordinate]
    exact Nat.cast_analyticOrderNatAt hcrit.2
  have hle_enat :
      ((2 : ℕ) : ℕ∞) ≤
        (holomorphicMapLocalMultiplicityInCoordinate χ F : ℕ∞) := by
    rw [hcast]
    exact hcrit.1
  exact ENat.coe_le_coe.mp hle_enat

/--
%%handwave
name:
  Local factorization at an injective critical point
statement:
  Let \(F:X\to\mathbb C\) be injective and holomorphic, and suppose its
  coordinate derivative vanishes at \(x\).  Writing \(z_0=\chi(x)\), there
  are an integer \(n\ge2\) and a function \(g\), analytic near \(z_0\) with
  \(g(z_0)\ne0\), such that near \(z_0\),
  \[
    F(\chi^{-1}(z))-F(x)=(z-z_0)^n g(z).
  \]
proof:
  Criticality and injectivity give a finite local order \(n\ge2\).  Apply the
  standard analytic factorization of a finite-order zero to the coordinate
  expression of \(F-F(x)\).
-/
theorem critical_holomorphicMap_coordinate_factorization_of_injective
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {x : X} (χ : PointedSurfaceCoordinate X x)
    {F : X → ℂ}
    (hF : HolomorphicMap X ℂ F)
    (hinj : Function.Injective F)
    (hderiv : surfaceComplexDerivativeInCoordinate χ F = 0) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g (χ.chart x) ∧ g (χ.chart x) ≠ 0 ∧
        (fun z : ℂ ↦ F (χ.chart.symm z) - F x) =ᶠ[𝓝 (χ.chart x)]
          fun z : ℂ ↦ (z - χ.chart x) ^ n * g z := by
  let n : ℕ := holomorphicMapLocalMultiplicityInCoordinate χ F
  have hn : 2 ≤ n :=
    two_le_holomorphicMapLocalMultiplicityInCoordinate_of_deriv_eq_zero_of_injective
      χ hF hinj hderiv
  have hcrit :=
    critical_holomorphicMapLocalOrderInCoordinate_finite_two_le_of_injective
      χ hF hinj hderiv
  rcases holomorphicMapLocalOrderInCoordinate_factorization_of_ne_top
      χ hF hcrit.2 with ⟨g, hg, hg_ne, hfactor⟩
  exact ⟨n, hn, g, hg, hg_ne, by simpa [n] using hfactor⟩

/--
%%handwave
name:
  A higher complex power is not injective near zero
statement:
  If \(n\ge2\), then for every neighborhood \(U\) of \(0\) in \(\mathbb C\),
  the map \(z\mapsto z^n\) is not injective on \(U\).
proof:
  Choose a small radius \(R>0\) whose circle lies in \(U\).  The distinct
  points \(R\) and \(Re^{2\pi i/n}\) both lie in \(U\) and have the same
  \(n\)-th power.
-/
theorem complex_pow_not_injOn_of_mem_nhds_zero {n : ℕ} (hn : 2 ≤ n)
    {U : Set ℂ} (hU : U ∈ 𝓝 (0 : ℂ)) :
    ¬ Set.InjOn (fun z : ℂ ↦ z ^ n) U := by
  classical
  rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε_pos, hε_subset⟩
  let R : ℝ := ε / 2
  let θ : ℝ := (2 * Real.pi) / (n : ℝ)
  let z : ℂ := circleMap 0 R 0
  let w : ℂ := circleMap 0 R θ
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn_pos_nat.ne'
  have hn_pos_real : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hn_gt_one_real : (1 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hn)
  have hR_pos : 0 < R := by
    dsimp [R]
    linarith
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  have hθ_pos : 0 < θ := by
    dsimp [θ]
    exact div_pos Real.two_pi_pos hn_pos_real
  have hθ_lt : θ < 2 * Real.pi := by
    dsimp [θ]
    field_simp [hn_ne]
    nlinarith [Real.two_pi_pos, hn_gt_one_real]
  have hdist_angles : |(0 : ℝ) - θ| < 2 * Real.pi := by
    rw [zero_sub, abs_neg, abs_of_pos hθ_pos]
    exact hθ_lt
  have hz_ball : z ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp [z, R, abs_of_pos hR_pos]
    linarith
  have hw_ball : w ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp [w, R, abs_of_pos hR_pos]
    linarith
  have hzU : z ∈ U := hε_subset hz_ball
  have hwU : w ∈ U := hε_subset hw_ball
  have hangle : (n : ℝ) * θ = 2 * Real.pi := by
    dsimp [θ]
    field_simp [hn_ne]
  have hpow : z ^ n = w ^ n := by
    dsimp [z, w]
    rw [circleMap_zero_pow, circleMap_zero_pow]
    simpa [hangle] using (periodic_circleMap 0 (R ^ n) 0).symm
  have hzw_ne : z ≠ w := by
    intro hzw
    have hangle_eq : (0 : ℝ) = θ :=
      eq_of_circleMap_eq hR_ne hdist_angles hzw
    exact hθ_pos.ne' hangle_eq.symm
  intro hinj
  exact hzw_ne (hinj hzU hwU hpow)

/--
%%handwave
name:
  A higher complex power is not locally injective at zero
statement:
  If \(n\ge2\), there is no neighborhood of \(0\) on which
  \(z\mapsto z^n\) is injective.
proof:
  Any proposed injective neighborhood contradicts the noninjectivity of the
  power map on every neighborhood of zero.
-/
theorem complex_pow_not_locally_injective_at_zero {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ U : Set ℂ, U ∈ 𝓝 (0 : ℂ) ∧
      Set.InjOn (fun z : ℂ ↦ z ^ n) U := by
  rintro ⟨U, hU, hinj⟩
  exact complex_pow_not_injOn_of_mem_nhds_zero hn hU hinj

/--
%%handwave
name:
  An injective holomorphic map has nonzero coordinate derivative
statement:
  Let \(F:X\to\mathbb C\) be an injective holomorphic map from a complex
  one-manifold.  Then its complex derivative in every pointed coordinate is
  nonzero.
proof:
  If the derivative vanished, the coordinate expression would factor as
  \((z-z_0)^n g(z)\) with \(n\ge2\) and \(g(z_0)\ne0\).  Taking an analytic
  \(n\)-th root of \(g\) gives a local coordinate in which the expression is
  an \(n\)-th power.  Injectivity of \(F\) would make this power map injective
  near zero, contradicting its rotational symmetry for \(n\ge2\).
-/
theorem injective_holomorphicMap_surfaceComplexDerivative_ne_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {x : X} (χ : PointedSurfaceCoordinate X x)
    {F : X → ℂ}
    (hF : HolomorphicMap X ℂ F)
    (hinj : Function.Injective F) :
    surfaceComplexDerivativeInCoordinate χ F ≠ 0 := by
  intro hcrit
  have _hcritical_order :
      (2 : ℕ∞) ≤ holomorphicMapLocalOrderInCoordinate χ F ∧
        holomorphicMapLocalOrderInCoordinate χ F ≠ ⊤ :=
    critical_holomorphicMapLocalOrderInCoordinate_finite_two_le_of_injective
      χ hF hinj hcrit
  have _hcritical_multiplicity :
      2 ≤ holomorphicMapLocalMultiplicityInCoordinate χ F :=
    two_le_holomorphicMapLocalMultiplicityInCoordinate_of_deriv_eq_zero_of_injective
      χ hF hinj hcrit
  rcases critical_holomorphicMap_coordinate_factorization_of_injective
      χ hF hinj hcrit with ⟨n, hn, g, hg, hg_ne, hfactor⟩
  let z₀ : ℂ := χ.chart x
  let fcoord : ℂ → ℂ := fun z : ℂ ↦ F (χ.chart.symm z) - F x
  have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  rcases analyticAt_exists_nthRoot_pow_eq_of_ne_zero hg hg_ne hn_pos with
    ⟨r, hr, hr_ne, hrpow⟩
  let H : ℂ → ℂ := fun z : ℂ ↦ (z - z₀) * r z
  have hfactor_pow :
      fcoord =ᶠ[𝓝 z₀] fun z : ℂ ↦ H z ^ n := by
    filter_upwards [hfactor] with z hz
    calc
      fcoord z = (z - z₀) ^ n * g z := by
        simpa [fcoord, z₀] using hz
      _ = (z - z₀) ^ n * r z ^ n := by
        rw [hrpow z]
      _ = H z ^ n := by
        simp [H, mul_pow]
  rcases analyticAt_branchCoordinate_local_injOn_image hr hr_ne with
    ⟨V, hV_nhds, hV_inj, hV_image⟩
  have hchart_nhds : χ.chart.target ∈ 𝓝 z₀ := by
    dsimp [z₀]
    exact χ.chart.open_target.mem_nhds
      (χ.chart.map_source χ.base_mem_source)
  have hfactor_set :
      {z : ℂ | fcoord z = H z ^ n} ∈ 𝓝 z₀ := by
    simpa using hfactor_pow
  let U : Set ℂ :=
    V ∩ χ.chart.target ∩ {z : ℂ | fcoord z = H z ^ n}
  have hU_nhds : U ∈ 𝓝 z₀ := by
    exact Filter.inter_mem (Filter.inter_mem hV_nhds hchart_nhds) hfactor_set
  have hU_subset_V : U ⊆ V := by
    intro z hz
    exact hz.1.1
  have hHU_nhds : H '' U ∈ 𝓝 (0 : ℂ) :=
    hV_image U hU_nhds hU_subset_V
  have hpow_inj : Set.InjOn (fun w : ℂ ↦ w ^ n) (H '' U) := by
    intro y hy w hw hyw
    rcases hy with ⟨z, hzU, rfl⟩
    rcases hw with ⟨ζ, hζU, rfl⟩
    have hz_eq_hζ :
        z = ζ := by
      apply coordinateDifference_injOn_chartTarget_of_injective χ hinj
      · exact hzU.1.2
      · exact hζU.1.2
      · calc
          fcoord z = H z ^ n := hzU.2
          _ = H ζ ^ n := hyw
          _ = fcoord ζ := (hζU.2).symm
    exact congr_arg H hz_eq_hζ
  exact complex_pow_not_injOn_of_mem_nhds_zero hn hHU_nhds hpow_inj

/--
%%handwave
name:
  Harmonicity is preserved by equality on an open set
statement:
  Let \(U\) be open in a complex surface.  If \(u\) is harmonic on \(U\) and
  \(v=u\) pointwise on \(U\), then \(v\) is harmonic on \(U\).
proof:
  In every complex chart, the two coordinate expressions agree on an open
  neighborhood of each point of \(U\).  Harmonicity is local and invariant
  under equality of germs, so harmonicity transfers from \(u\) to \(v\).
-/
theorem harmonicOnSurface_congr_on_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u v : X → ℝ}
    (hU_open : IsOpen U)
    (hu : IsHarmonicOnSurface U u)
    (heq : ∀ x ∈ U, v x = u x) :
    IsHarmonicOnSurface U v := by
  intro e he z hz
  have hS_open : IsOpen (e.target ∩ e.symm ⁻¹' U) :=
    e.isOpen_inter_preimage_symm hU_open
  have hevent :
      (fun z : ℂ ↦ v (e.symm z)) =ᶠ[𝓝 z]
      (fun z : ℂ ↦ u (e.symm z)) := by
    filter_upwards [hS_open.mem_nhds hz] with y hy
    exact heq (e.symm y) hy.2
  exact (InnerProductSpace.harmonicAt_congr_nhds hevent).2 (hu e he z hz)

/--
%%handwave
name:
  Round Euclidean annuli
statement:
  The round annulus with center \(c\) and radii \(\rho<R\) consists of the
  points whose distance from \(c\) lies between the two radii.
-/
def complexRoundAnnulus (c : ℂ) (ρ R : ℝ) : Set ℂ :=
  {z : ℂ | ρ < ‖z - c‖ ∧ ‖z - c‖ < R}

/--
%%handwave
name:
  Round Euclidean annuli are open
statement:
  The set \(\rho<|z-c|<R\) is open in the complex plane.
proof:
  It is the inverse image of the open interval \((\rho,R)\) under the
  continuous distance-to-\(c\) function.
-/
theorem complexRoundAnnulus_isOpen (c : ℂ) (ρ R : ℝ) :
    IsOpen (complexRoundAnnulus c ρ R) := by
  have hcont : Continuous fun z : ℂ ↦ ‖z - c‖ :=
    (continuous_id.sub continuous_const).norm
  simpa [complexRoundAnnulus, Set.mem_Ioo] using
    (isOpen_Ioo.preimage hcont : IsOpen ((fun z : ℂ ↦ ‖z - c‖) ⁻¹' Set.Ioo ρ R))

/--
%%handwave
name:
  Round Euclidean annuli are connected
statement:
  If \(0<\rho<R\), then the round annulus \(\rho<|z-c|<R\) is connected.
proof:
  Parametrize the annulus by radius and direction.  The interval of radii is
  connected, the unit circle in the complex plane is connected, and the
  radial parametrization is continuous and surjective onto the annulus.
-/
theorem complexRoundAnnulus_preconnected
    (c : ℂ) {ρ R : ℝ} (hρ : 0 < ρ) (_hρR : ρ < R) :
    IsPreconnected (complexRoundAnnulus c ρ R) := by
  let S : Set (ℝ × ℂ) := Set.Ioo ρ R ×ˢ Metric.sphere (0 : ℂ) 1
  let F : ℝ × ℂ → ℂ := fun q ↦ c + q.1 • q.2
  have hsphere : IsPreconnected (Metric.sphere (0 : ℂ) 1) :=
    isPreconnected_sphere
      (Complex.rank_real_complex ▸ (by norm_num : (1 : Cardinal) < 2))
      (0 : ℂ) 1
  have hS : IsPreconnected S := isPreconnected_Ioo.prod hsphere
  have hcont : ContinuousOn F S := by
    dsimp [F]
    fun_prop
  have hpre : IsPreconnected (F '' S) := hS.image F hcont
  have himage : F '' S = complexRoundAnnulus c ρ R := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨r, u⟩
      rcases hq with ⟨hr, hu⟩
      have hrpos : 0 < r := hρ.trans hr.1
      have hunorm : ‖u‖ = 1 := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hu
      have hnorm : ‖c + r • u - c‖ = r := by
        simp [sub_eq_add_neg, add_assoc, hunorm, abs_of_nonneg hrpos.le]
      change ρ < ‖c + r • u - c‖ ∧ ‖c + r • u - c‖ < R
      rw [hnorm]
      exact hr
    · intro hz
      let r : ℝ := ‖z - c‖
      rcases hz with ⟨hzρ, hzR⟩
      have hrpos : 0 < r := hρ.trans hzρ
      have hr_ne : r ≠ 0 := ne_of_gt hrpos
      let u : ℂ := (r⁻¹ : ℝ) • (z - c)
      have hu_sphere : u ∈ Metric.sphere (0 : ℂ) 1 := by
        have hunorm : ‖u‖ = 1 := by
          simp [u, r, inv_mul_cancel₀ hr_ne]
        simp [hunorm]
      refine ⟨(r, u), ⟨⟨hzρ, hzR⟩, hu_sphere⟩, ?_⟩
      have hscale : (r : ℝ) • u = z - c := by
        simp [u, hr_ne]
      dsimp [F]
      change c + r • u = z
      rw [hscale]
      simp [sub_eq_add_neg]
  simpa [himage] using hpre

/--
%%handwave
name:
  Closure of a round annulus lies in the closed annulus
statement:
  The closure of \(\rho<|z-c|<R\) is contained in
  \(\rho\le |z-c|\le R\).
proof:
  The closed annulus is a closed set containing the open annulus.
-/
theorem complexRoundAnnulus_closure_subset_closed_annulus
    (c : ℂ) (ρ R : ℝ) :
    closure (complexRoundAnnulus c ρ R) ⊆
      {z : ℂ | ρ ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ R} := by
  have hcont : Continuous fun z : ℂ ↦ ‖z - c‖ :=
    (continuous_id.sub continuous_const).norm
  have hclosed₁ : IsClosed {z : ℂ | ρ ≤ ‖z - c‖} :=
    isClosed_le continuous_const hcont
  have hclosed₂ : IsClosed {z : ℂ | ‖z - c‖ ≤ R} :=
    isClosed_le hcont continuous_const
  have hclosed :
      IsClosed {z : ℂ | ρ ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ R} := by
    simpa [Set.setOf_and] using hclosed₁.inter hclosed₂
  refine closure_minimal ?_ hclosed
  intro z hz
  exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩

/--
%%handwave
name:
  Round Euclidean annuli have compact closure
statement:
  If \(0<\rho<R\), then the closure of \(\rho<|z-c|<R\) is compact.
proof:
  The closure lies in the closed ball of radius \(R\), hence is a closed
  subset of a compact set.
-/
theorem complexRoundAnnulus_compact_closure
    (c : ℂ) {ρ R : ℝ} (_hρ : 0 < ρ) (_hρR : ρ < R) :
    IsCompact (closure (complexRoundAnnulus c ρ R)) := by
  have hsubset_closedBall :
      closure (complexRoundAnnulus c ρ R) ⊆ Metric.closedBall c R := by
    intro z hz
    have hz' :=
      complexRoundAnnulus_closure_subset_closed_annulus c ρ R hz
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz'.2
  exact (isCompact_closedBall c R).of_isClosed_subset
    isClosed_closure hsubset_closedBall

/--
%%handwave
name:
  The frontier of a round annulus lies on its two boundary circles
statement:
  Every frontier point of \(\rho<|z-c|<R\) has radius either \(\rho\) or
  \(R\).
proof:
  A frontier point lies in the closed annulus.  Since the annulus is open, it
  cannot lie in the strict annulus, so one of the two closed radius
  inequalities is an equality.
-/
theorem complexRoundAnnulus_frontier_subset_inner_or_outer
    (c : ℂ) {ρ R : ℝ} :
    frontier (complexRoundAnnulus c ρ R) ⊆
      {z : ℂ | ‖z - c‖ = ρ ∨ ‖z - c‖ = R} := by
  intro z hzfront
  have hzclosed :=
    complexRoundAnnulus_closure_subset_closed_annulus c ρ R
      (frontier_subset_closure hzfront)
  have hUopen : IsOpen (complexRoundAnnulus c ρ R) :=
    complexRoundAnnulus_isOpen c ρ R
  have hznotU : z ∉ complexRoundAnnulus c ρ R := by
    intro hzU
    have hz_inter :
        z ∈ complexRoundAnnulus c ρ R ∩
          frontier (complexRoundAnnulus c ρ R) := ⟨hzU, hzfront⟩
    have h_empty :
        complexRoundAnnulus c ρ R ∩ frontier (complexRoundAnnulus c ρ R) = ∅ :=
      hUopen.inter_frontier_eq
    rw [h_empty] at hz_inter
    exact hz_inter
  by_cases hinner : ‖z - c‖ = ρ
  · exact Or.inl hinner
  · right
    have hρlt : ρ < ‖z - c‖ :=
      lt_of_le_of_ne hzclosed.1 (by
        intro h
        exact hinner h.symm)
    by_contra houter
    have hltR : ‖z - c‖ < R := lt_of_le_of_ne hzclosed.2 houter
    exact hznotU ⟨hρlt, hltR⟩

/--
%%handwave
name:
  Round Euclidean annuli have nonempty frontier
statement:
  If \(0<\rho<R\), then the frontier of \(\rho<|z-c|<R\) is nonempty.
proof:
  The annulus is nonempty, for instance at the midpoint radius, and it is not
  all of the connected complex plane because it omits its center.  A nonempty
  proper subset of a connected space has nonempty frontier.
-/
theorem complexRoundAnnulus_frontier_nonempty
    (c : ℂ) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) :
    (frontier (complexRoundAnnulus c ρ R)).Nonempty := by
  have hmidρ : ρ < (ρ + R) / 2 := by linarith
  have hmidR : (ρ + R) / 2 < R := by linarith
  let z : ℂ := c + (((ρ + R) / 2 : ℝ) : ℂ)
  have hz_norm : ‖z - c‖ = (ρ + R) / 2 := by
    have hsub : z - c = (((ρ + R) / 2 : ℝ) : ℂ) := by
      simp [z]
    rw [hsub, Complex.norm_real, Real.norm_of_nonneg]
    linarith [hρ]
  have hU_nonempty : (complexRoundAnnulus c ρ R).Nonempty := by
    refine ⟨z, ?_⟩
    simpa [complexRoundAnnulus, hz_norm] using And.intro hmidρ hmidR
  have hU_ne_univ : complexRoundAnnulus c ρ R ≠ Set.univ := by
    intro hU
    have hcU : c ∈ complexRoundAnnulus c ρ R := by
      rw [hU]
      exact Set.mem_univ c
    have hρ0 : ρ < 0 := by
      simpa [complexRoundAnnulus] using hcU.1
    exact (not_lt_of_ge hρ.le) hρ0
  exact (nonempty_frontier_iff (s := complexRoundAnnulus c ρ R)).2
    ⟨hU_nonempty, hU_ne_univ⟩

/--
%%handwave
name:
  Strong maximum principle for plane harmonic functions
statement:
  On a connected open plane region, a harmonic function that attains its
  maximum inside the region is constant on the region.
proof:
  The maximum locus is open by the local strong maximum principle for
  harmonic functions and closed in the region by continuity.  Connectedness
  forces it to be the whole region.
-/
theorem harmonicOnNhd_eqOn_of_isPreconnected_of_isMaxOn
    {U : Set ℂ} {u : ℂ → ℝ}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    {c : ℂ} (hcU : c ∈ U) (hm : IsMaxOn u U c) :
    Set.EqOn u (fun _ ↦ u c) U := by
  let V : Set ℂ := U ∩ {x | u x = u c}
  have hVo : IsOpen V := by
    refine isOpen_iff_mem_nhds.2 ?_
    intro x hxV
    have hxU : x ∈ U := hxV.1
    have hx_eq : u x = u c := hxV.2
    have hxmaxU : IsMaxOn u U x := by
      intro y hy
      simpa [hx_eq] using hm hy
    have hxlocalmax : IsLocalMax u x :=
      hxmaxU.isLocalMax (hU_open.mem_nhds hxU)
    have hevent : ∀ᶠ y in 𝓝 x, u y = u x :=
      harmonicAt_eventually_eq_of_isLocalMax (hu x hxU) hxlocalmax
    have heqset : {y : ℂ | u y = u c} ∈ 𝓝 x := by
      filter_upwards [hevent] with y hy
      exact hy.trans hx_eq
    exact Filter.inter_mem (hU_open.mem_nhds hxU) heqset
  have hcont : ContinuousOn u U := hu.continuousOn
  let W : Set ℂ := U ∩ {x | u x ≠ u c}
  have hWo : IsOpen W :=
    hcont.isOpen_inter_preimage hU_open isOpen_ne
  have hdVW : Disjoint V W := by
    rw [Set.disjoint_left]
    intro x hxV hxW
    exact hxW.2 hxV.2
  have hUVW : U ⊆ V ∪ W := by
    intro x hx
    by_cases hx_eq : u x = u c
    · exact Or.inl ⟨hx, hx_eq⟩
    · exact Or.inr ⟨hx, hx_eq⟩
  have hVne : (U ∩ V).Nonempty := ⟨c, hcU, hcU, rfl⟩
  have hsubset : U ⊆ V :=
    hU_preconnected.subset_left_of_subset_union hVo hWo hdVW hUVW hVne
  intro x hx
  exact (hsubset hx).2

/--
%%handwave
name:
  Plane harmonic maximum principle with boundary values
statement:
  A harmonic function on a relatively compact connected open plane region,
  continuous on the closed region and bounded above by a constant on the
  frontier, is bounded above by that constant throughout the region.
proof:
  The continuous function attains a maximum on the compact closure.  If the
  maximum occurs in the interior, the strong maximum principle makes the
  function constant and the boundary bound applies; otherwise the maximum is
  already a boundary value.
-/
theorem harmonicOnNhd_le_constant_of_boundary_le
    {U : Set ℂ} {u : ℂ → ℝ} {M : ℝ}
    (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    (hU_compact : IsCompact (closure U))
    (hU_frontier_nonempty : (frontier U).Nonempty)
    (hu_harmonic : InnerProductSpace.HarmonicOnNhd u U)
    (hu_continuous : ContinuousOn u (closure U))
    (hbd : ∀ x ∈ frontier U, u x ≤ M) :
    ∀ x ∈ U, u x ≤ M := by
  rcases hU_frontier_nonempty with ⟨b, hbfrontier⟩
  have hbclosure : b ∈ closure U := frontier_subset_closure hbfrontier
  rcases hU_compact.exists_isMaxOn ⟨b, hbclosure⟩ hu_continuous with
    ⟨c, hcclosure, hcmax_closure⟩
  have hc_mem : c ∈ U ∪ frontier U := by
    simpa [closure_eq_self_union_frontier] using hcclosure
  rcases hc_mem with hcU | hcfrontier
  · have hcmaxU : IsMaxOn u U c := by
      intro y hy
      exact hcmax_closure (subset_closure hy)
    have heqU : Set.EqOn u (fun _ ↦ u c) U :=
      harmonicOnNhd_eqOn_of_isPreconnected_of_isMaxOn
        hU_open hU_preconnected hu_harmonic hcU hcmaxU
    have heq_closure : Set.EqOn u (fun _ ↦ u c) (closure U) :=
      heqU.of_subset_closure hu_continuous continuousOn_const
        subset_closure subset_rfl
    have huc_le : u c ≤ M := by
      have hbc : u b = u c := heq_closure hbclosure
      rw [← hbc]
      exact hbd b hbfrontier
    intro x hx
    exact (heqU hx).trans_le huc_le
  · have huc_le : u c ≤ M := hbd c hcfrontier
    intro x hx
    exact (hcmax_closure (subset_closure hx)).trans huc_le

/--
%%handwave
name:
  Logarithmic annulus barrier
statement:
  The logarithmic annulus barrier is the harmonic function on
  \(\rho<|z-c|<R\) that takes value \(B\) on the inner circle and \(0\) on
  the outer circle.
-/
noncomputable def complexAnnularLogBarrier
    (c : ℂ) (ρ R B : ℝ) : ℂ → ℝ :=
  fun z : ℂ ↦
    (B * (Real.log R - Real.log ρ)⁻¹) *
      (Real.log R - Real.log ‖z - c‖)

/--
%%handwave
name:
  The logarithmic annulus barrier has the inner boundary value
statement:
  On the circle \(|z-c|=\rho\), the logarithmic annulus barrier equals
  \(B\).
proof:
  Substitute \(|z-c|=\rho\).  Since \(0<\rho<R\), the logarithmic denominator
  \(\log R-\log\rho\) is nonzero, so it cancels with the identical numerator
  factor and leaves \(B\).
-/
theorem complexAnnularLogBarrier_inner_boundary
    (c : ℂ) {ρ R B : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    {z : ℂ} (hznorm : ‖z - c‖ = ρ) :
    complexAnnularLogBarrier c ρ R B z = B := by
  have hden_ne : Real.log R - Real.log ρ ≠ 0 := by
    have hlog_lt : Real.log ρ < Real.log R := Real.log_lt_log hρ hρR
    linarith
  calc
    complexAnnularLogBarrier c ρ R B z
        = (B * (Real.log R - Real.log ρ)⁻¹) *
            (Real.log R - Real.log ρ) := by
          simp [complexAnnularLogBarrier, hznorm]
    _ = B := by
          field_simp [hden_ne]

/--
%%handwave
name:
  The logarithmic annulus barrier has the outer boundary value
statement:
  On the circle \(|z-c|=R\), the logarithmic annulus barrier equals \(0\).
proof:
  Substituting \(|z-c|=R\) makes the final factor
  \(\log R-\log R\) vanish.
-/
theorem complexAnnularLogBarrier_outer_boundary
    (c : ℂ) {ρ R B : ℝ} {z : ℂ} (hznorm : ‖z - c‖ = R) :
    complexAnnularLogBarrier c ρ R B z = 0 := by
  simp [complexAnnularLogBarrier, hznorm]

/--
%%handwave
name:
  The logarithmic annulus barrier is harmonic
statement:
  The logarithmic annulus barrier is harmonic on
  \(\rho<|z-c|<R\).
proof:
  It is an affine multiple of \(\log R-\log |z-c|\), and
  \(\log |z-c|\) is harmonic away from \(c\).
-/
theorem complexAnnularLogBarrier_harmonicOn
    (c : ℂ) {ρ R B : ℝ} (hρ : 0 < ρ) :
    InnerProductSpace.HarmonicOnNhd
      (complexAnnularLogBarrier c ρ R B) (complexRoundAnnulus c ρ R) := by
  let U : Set ℂ := complexRoundAnnulus c ρ R
  have hlog :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦ Real.log ‖z - c‖) U := by
    intro z hz
    have hsub :
        AnalyticAt ℂ (fun w : ℂ ↦ w - c) z :=
      analyticAt_id.sub (analyticAt_const (𝕜 := ℂ) (x := z) (v := c))
    have hne : z - c ≠ 0 := by
      have hpos : 0 < ‖z - c‖ := hρ.trans hz.1
      exact norm_ne_zero_iff.mp hpos.ne'
    simpa using hsub.harmonicAt_log_norm hne
  have hbase :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦ Real.log R - Real.log ‖z - c‖) U :=
    (by
      simpa using
        (InnerProductSpace.HarmonicOnNhd.sub
          (by simp : InnerProductSpace.HarmonicOnNhd
            (fun _ : ℂ ↦ Real.log R) U)
          hlog))
  simpa [complexAnnularLogBarrier, U] using
      (InnerProductSpace.HarmonicOnNhd.const_smul
        (c := B * (Real.log R - Real.log ρ)⁻¹) hbase)

/--
%%handwave
name:
  The logarithmic annulus barrier is continuous on the closed annulus
statement:
  The logarithmic annulus barrier is continuous on the closure of
  \(\rho<|z-c|<R\) when \(\rho>0\).
proof:
  On the closed annulus the distance to \(c\) is bounded below by \(\rho>0\),
  so the logarithm has no singularity there.
-/
theorem complexAnnularLogBarrier_continuousOn_closure
    (c : ℂ) {ρ R B : ℝ} (hρ : 0 < ρ) :
    ContinuousOn (complexAnnularLogBarrier c ρ R B)
      (closure (complexRoundAnnulus c ρ R)) := by
  have hnorm_cont : Continuous fun z : ℂ ↦ ‖z - c‖ :=
    (continuous_id.sub continuous_const).norm
  have hlog_cont :
      ContinuousOn (fun z : ℂ ↦ Real.log ‖z - c‖)
        (closure (complexRoundAnnulus c ρ R)) := by
    intro z hz
    have hzclosed :=
      complexRoundAnnulus_closure_subset_closed_annulus c ρ R hz
    have hne : ‖z - c‖ ≠ 0 :=
      (ne_of_gt (hρ.trans_le hzclosed.1))
    exact (hnorm_cont.continuousAt.log hne).continuousWithinAt
  have hbase :
      ContinuousOn (fun z : ℂ ↦ Real.log R - Real.log ‖z - c‖)
        (closure (complexRoundAnnulus c ρ R)) :=
    continuousOn_const.sub hlog_cont
  simpa [complexAnnularLogBarrier] using
      (hbase.const_mul (B * (Real.log R - Real.log ρ)⁻¹))

/--
%%handwave
name:
  Harmonic functions compare with the logarithmic annulus barrier
statement:
  Let \(u\) be harmonic on \(\rho<|z-c|<R\), continuous on the closed
  annulus, bounded by \(B\) on the inner boundary circle and by \(0\) on the
  outer boundary circle.  Then \(u\) is bounded above by the logarithmic
  annulus barrier throughout the annulus.
proof:
  Apply the harmonic maximum principle to \(u\) minus the barrier.  The
  frontier of the annulus lies on the two boundary circles, where the
  assumed bounds match the barrier values.
-/
theorem harmonicOnNhd_le_complexAnnularLogBarrier_of_boundary_le
    (c : ℂ) {ρ R B : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    {u : ℂ → ℝ}
    (hu_harmonic :
      InnerProductSpace.HarmonicOnNhd u (complexRoundAnnulus c ρ R))
    (hu_continuous :
      ContinuousOn u (closure (complexRoundAnnulus c ρ R)))
    (hinner : ∀ z : ℂ, ‖z - c‖ = ρ → u z ≤ B)
    (houter : ∀ z : ℂ, ‖z - c‖ = R → u z ≤ 0) :
    ∀ z ∈ complexRoundAnnulus c ρ R,
      u z ≤ complexAnnularLogBarrier c ρ R B z := by
  let b : ℂ → ℝ := complexAnnularLogBarrier c ρ R B
  let w : ℂ → ℝ := fun z ↦ u z - b z
  have hb_harmonic :
      InnerProductSpace.HarmonicOnNhd b (complexRoundAnnulus c ρ R) :=
    complexAnnularLogBarrier_harmonicOn c hρ
  have hw_harmonic :
      InnerProductSpace.HarmonicOnNhd w (complexRoundAnnulus c ρ R) := by
    simpa [w, b] using hu_harmonic.sub hb_harmonic
  have hb_continuous :
      ContinuousOn b (closure (complexRoundAnnulus c ρ R)) :=
    complexAnnularLogBarrier_continuousOn_closure c hρ
  have hw_continuous :
      ContinuousOn w (closure (complexRoundAnnulus c ρ R)) :=
    hu_continuous.sub hb_continuous
  have hw_boundary :
      ∀ z ∈ frontier (complexRoundAnnulus c ρ R), w z ≤ 0 := by
    intro z hzfront
    rcases complexRoundAnnulus_frontier_subset_inner_or_outer c hzfront with hzin | hzout
    · have hbz : b z = B :=
        complexAnnularLogBarrier_inner_boundary c hρ hρR hzin
      dsimp [w]
      rw [hbz]
      linarith [hinner z hzin]
    · have hbz : b z = 0 :=
        complexAnnularLogBarrier_outer_boundary c hzout
      dsimp [w]
      rw [hbz]
      linarith [houter z hzout]
  have hw_le :
      ∀ z ∈ complexRoundAnnulus c ρ R, w z ≤ 0 :=
    harmonicOnNhd_le_constant_of_boundary_le
      (complexRoundAnnulus_isOpen c ρ R)
      (complexRoundAnnulus_preconnected c hρ hρR)
      (complexRoundAnnulus_compact_closure c hρ hρR)
      (complexRoundAnnulus_frontier_nonempty c hρ hρR)
      hw_harmonic hw_continuous hw_boundary
  intro z hz
  have hzw := hw_le z hz
  dsimp [w] at hzw
  linarith

/--
%%handwave
name:
  The logarithmic annulus barrier vanishes as the inner radius shrinks
statement:
  At a fixed point \(z\) with \(0<|z-c|<R\), the logarithmic annulus barrier
  tends to \(0\) as the inner radius \(\rho\) tends to \(0\) through positive
  values.
proof:
  The numerator is fixed, while the denominator
  \(\log R-\log\rho\) tends to \(+\infty\).
-/
theorem complexAnnularLogBarrier_tendsto_innerRadius_zero
    (c : ℂ) {R B : ℝ} (_hR : 0 < R)
    {z : ℂ} (_hzpos : 0 < ‖z - c‖) (_hzR : ‖z - c‖ < R) :
    Filter.Tendsto
      (fun ρ : ℝ ↦ complexAnnularLogBarrier c ρ R B z)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let A : ℝ := B * (Real.log R - Real.log ‖z - c‖)
  have ht :
      Filter.Tendsto (fun ρ : ℝ ↦ -Real.log ρ) (𝓝[>] (0 : ℝ)) Filter.atTop := by
    simpa [Function.comp_def] using
      (Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  have hden :
      Filter.Tendsto (fun ρ : ℝ ↦ Real.log R - Real.log ρ)
        (𝓝[>] (0 : ℝ)) Filter.atTop := by
    simpa [sub_eq_add_neg, add_comm] using
      ht.atTop_add (tendsto_const_nhds (x := Real.log R))
  have hdiv :
      Filter.Tendsto (fun ρ : ℝ ↦ A / (Real.log R - Real.log ρ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  refine hdiv.congr' ?_
  filter_upwards with ρ
  simp [complexAnnularLogBarrier, A, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc]

/--
%%handwave
name:
  A sufficiently small inner radius makes the annulus barrier tiny
statement:
  If \(a>0\) and \(0<|z-c|<R\), then for some
  \(0<\rho<|z-c|\) the logarithmic annulus barrier at \(z\) is less than
  \(a\).
proof:
  Use the preceding limit of the barrier to \(0\) as \(\rho\to0^+\), then
  choose \(\rho\) smaller than the point radius and the outer radius.
-/
theorem exists_inner_radius_complexAnnularLogBarrier_lt
    (c : ℂ) {R B a : ℝ} (hR : 0 < R)
    {z : ℂ} (hzpos : 0 < ‖z - c‖) (hzR : ‖z - c‖ < R)
    (ha : 0 < a) :
    ∃ ρ : ℝ,
      0 < ρ ∧ ρ < ‖z - c‖ ∧ ρ < R ∧
        complexAnnularLogBarrier c ρ R B z < a := by
  have htend :
      Filter.Tendsto
        (fun ρ : ℝ ↦ complexAnnularLogBarrier c ρ R B z)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    complexAnnularLogBarrier_tendsto_innerRadius_zero
      c hR hzpos hzR
  have hsmall_within :
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
        complexAnnularLogBarrier c ρ R B z < a := by
    exact htend.eventually (Iio_mem_nhds ha)
  have hsmall_nhds :
      ∀ᶠ ρ in 𝓝 (0 : ℝ),
        ρ ∈ Set.Ioi (0 : ℝ) →
          complexAnnularLogBarrier c ρ R B z < a :=
    eventually_nhdsWithin_iff.mp hsmall_within
  rcases Metric.eventually_nhds_iff.mp hsmall_nhds with
    ⟨δ, hδ_pos, hδ⟩
  let ρ : ℝ := min δ (min ‖z - c‖ R) / 2
  have hmin_pos : 0 < min δ (min ‖z - c‖ R) :=
    lt_min hδ_pos (lt_min hzpos hR)
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ_lt_delta : ρ < δ := by
    dsimp [ρ]
    exact (half_lt_self hmin_pos).trans_le (min_le_left _ _)
  have hρ_lt_norm : ρ < ‖z - c‖ := by
    dsimp [ρ]
    exact (half_lt_self hmin_pos).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hρ_lt_R : ρ < R := by
    dsimp [ρ]
    exact (half_lt_self hmin_pos).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  have hdist : dist ρ (0 : ℝ) < δ := by
    simpa [Real.dist_eq, abs_of_pos hρ_pos] using hρ_lt_delta
  refine ⟨ρ, hρ_pos, hρ_lt_norm, hρ_lt_R, ?_⟩
  exact hδ hdist (by simpa [Set.mem_Ioi] using hρ_pos)

/--
%%handwave
name:
  Local removable extensions globalize on the chart source
statement:
  If a punctured harmonic function has a local removable extension at the
  puncture, then it has a harmonic extension on the whole coordinate source
  agreeing with the original function near the puncture.
proof:
  Use the local extension near the puncture and the original harmonic function
  away from the puncture.  On the punctured overlap these agree in a
  neighborhood of the puncture, so harmonicity patches locally across the
  chart source.
-/
theorem bounded_harmonicOn_punctured_pointed_coordinate_local_extension_globalizes
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ : PointedSurfaceCoordinate X p) (g h₀ : X → ℝ) {N : Set X}
    (hharm :
      IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p}) g)
    (hN_open : IsOpen N) (hpN : p ∈ N) (_hN_source : N ⊆ χ.chart.source)
    (hh₀ : IsHarmonicOnSurface N h₀)
    (heq :
      ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
        g x = h₀ x) :
    ∃ h : X → ℝ,
      IsHarmonicOnSurface χ.chart.source h ∧
        ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
          g x = h x := by
  classical
  let h : X → ℝ := fun x ↦ if x = p then h₀ x else g x
  refine ⟨h, ?_, ?_⟩
  · refine harmonicOnSurface_of_locally_harmonic ?_
    intro x hxsource
    by_cases hxp : x = p
    · let E : Set X :=
        {y : X | y ∈ χ.chart.source ∩ {x : X | x ≠ p} → g y = h₀ y}
      have hE_nhds : E ∈ 𝓝 p := by
        simpa [E] using eventually_nhdsWithin_iff.mp heq
      rcases mem_nhds_iff.mp hE_nhds with ⟨W, hWE, hW_open, hpW⟩
      let V : Set X := W ∩ N ∩ χ.chart.source
      have hV_open : IsOpen V := (hW_open.inter hN_open).inter χ.chart.open_source
      have hxV : x ∈ V := by
        rw [hxp]
        exact ⟨⟨hpW, hpN⟩, χ.base_mem_source⟩
      have hV_source : V ⊆ χ.chart.source := by
        intro y hy
        exact hy.2
      have hV_N : V ⊆ N := by
        intro y hy
        exact hy.1.2
      have hh₀V : IsHarmonicOnSurface V h₀ :=
        harmonicOnSurface_mono hV_N hh₀
      refine ⟨V, hxV, hV_source, ?_⟩
      exact harmonicOnSurface_congr_on_open hV_open hh₀V (by
        intro y hy
        by_cases hyp : y = p
        · simp [h, hyp]
        · have hyE : y ∈ E := hWE hy.1.1
          have hyS : y ∈ χ.chart.source ∩ {x : X | x ≠ p} :=
            ⟨hy.2, hyp⟩
          simpa [h, hyp] using (hyE hyS))
    · let V : Set X := χ.chart.source ∩ {y : X | y ≠ p}
      have hV_open : IsOpen V :=
        χ.chart.open_source.inter (isOpen_ne (x := p))
      have hxV : x ∈ V := ⟨hxsource, hxp⟩
      have hV_source : V ⊆ χ.chart.source := Set.inter_subset_left
      refine ⟨V, hxV, hV_source, ?_⟩
      exact harmonicOnSurface_congr_on_open hV_open hharm (by
        intro y hy
        have hyne : y ≠ p := hy.2
        change (if y = p then h₀ y else g y) = g y
        exact if_neg hyne)
  · filter_upwards [(self_mem_nhdsWithin :
        χ.chart.source ∩ {x : X | x ≠ p} ∈
          𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p)] with x hx
    have hxne : x ≠ p := hx.2
    change g x = (if x = p then h₀ x else g x)
    exact (if_neg hxne).symm

/--
%%handwave
name:
  Bounded punctured disk harmonic functions are removable, core
statement:
  A bounded harmonic function on a punctured Euclidean disk has a harmonic
  extension across the puncture on a smaller disk, agreeing with the original
  function near the puncture away from the puncture.
proof:
  This is the classical removable singularity theorem for bounded harmonic
  functions, proved for instance from the Poisson representation on shrinking
  circles or by applying the removable singularity theorem for bounded
  holomorphic functions to local harmonic conjugates.
-/
theorem bounded_harmonicOn_punctured_complex_ball_has_removable_extension_core
    {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ}
    (hharm :
      InnerProductSpace.HarmonicOnNhd f (Metric.ball c r \ {c}))
    (hbound :
      ∃ M : ℝ,
        ∀ᶠ z in 𝓝[Metric.ball c r \ {c}] c, ‖f z‖ ≤ M) :
    ∃ δ : ℝ, ∃ F : ℂ → ℝ,
      0 < δ ∧ δ ≤ r ∧
        InnerProductSpace.HarmonicOnNhd F (Metric.ball c δ) ∧
          ∀ᶠ z in 𝓝[Metric.ball c r \ {c}] c, f z = F z := by
  rcases hbound with ⟨M₀, hM₀⟩
  let M : ℝ := max M₀ 0
  have hM_nonneg : 0 ≤ M := le_max_right M₀ 0
  have hM :
      ∀ᶠ z in 𝓝[Metric.ball c r \ {c}] c, ‖f z‖ ≤ M := by
    filter_upwards [hM₀] with z hz
    exact hz.trans (le_max_left M₀ 0)
  have hM_nhds :
      ∀ᶠ z in 𝓝 c,
        z ∈ Metric.ball c r \ {c} → ‖f z‖ ≤ M :=
    eventually_nhdsWithin_iff.mp hM
  rcases Metric.eventually_nhds_iff.mp hM_nhds with
    ⟨ε, hε_pos, hε⟩
  let R : ℝ := min r ε / 2
  have hmin_pos : 0 < min r ε := lt_min hr hε_pos
  have hR_pos : 0 < R := by
    dsimp [R]
    positivity
  have hR_lt_r : R < r := by
    dsimp [R]
    exact (half_lt_self hmin_pos).trans_le (min_le_left r ε)
  have hR_lt_ε : R < ε := by
    dsimp [R]
    exact (half_lt_self hmin_pos).trans_le (min_le_right r ε)
  have hfront_subset_punct :
      frontier (Metric.ball c R) ⊆ Metric.ball c r \ {c} := by
    intro z hz
    have hz_sphere : z ∈ Metric.sphere c R := by
      simpa [frontier_ball c hR_pos.ne'] using hz
    have hz_dist : dist z c = R := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz_sphere
    have hz_ball_r : z ∈ Metric.ball c r := by
      rw [Metric.mem_ball, hz_dist]
      exact hR_lt_r
    have hz_ne : z ≠ c := by
      exact Metric.ne_of_mem_sphere hz_sphere hR_pos.ne'
    exact ⟨hz_ball_r, by simpa [Set.mem_singleton_iff] using hz_ne⟩
  have hf_front_cont :
      ContinuousOn f (frontier (Metric.ball c R)) :=
    hharm.continuousOn.mono hfront_subset_punct
  let F : ℂ → ℝ := poissonDiskDirichletCandidate c R f
  have hF_harm :
      InnerProductSpace.HarmonicOnNhd F (Metric.ball c R) := by
    simpa [F] using
      poissonDiskDirichletCandidate_harmonicOn c hR_pos f hf_front_cont
  have hF_cont :
      ContinuousOn F (closure (Metric.ball c R)) := by
    simpa [F] using
      poissonDiskDirichletCandidate_continuousOn_closedBall c hR_pos f hf_front_cont
  have hF_boundary :
      ∀ z ∈ frontier (Metric.ball c R), F z = f z := by
    simpa [F] using
      poissonDiskDirichletCandidate_boundary_eq c R f
  have hf_front_bound :
      ∀ z ∈ frontier (Metric.ball c R), ‖f z‖ ≤ M := by
    intro z hz
    have hz_sphere : z ∈ Metric.sphere c R := by
      simpa [frontier_ball c hR_pos.ne'] using hz
    have hz_dist : dist z c = R := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz_sphere
    have hz_punct := hfront_subset_punct hz
    have hdist : dist z c < ε := by
      rw [hz_dist]
      exact hR_lt_ε
    exact hε hdist hz_punct
  have hf_front_le :
      ∀ z ∈ frontier (Metric.ball c R), f z ≤ M := by
    intro z hz
    have hz_abs : |f z| ≤ M := by
      simpa [Real.norm_eq_abs] using hf_front_bound z hz
    exact (abs_le.mp hz_abs).2
  have hf_front_ge :
      ∀ z ∈ frontier (Metric.ball c R), -M ≤ f z := by
    intro z hz
    have hz_abs : |f z| ≤ M := by
      simpa [Real.norm_eq_abs] using hf_front_bound z hz
    exact (abs_le.mp hz_abs).1
  have hF_le :
      ∀ z ∈ closure (Metric.ball c R), F z ≤ M := by
    simpa [F] using
      poissonDiskDirichletCandidate_le_of_boundaryData_le
        c hR_pos f hf_front_cont hf_front_le
  have hF_ge :
      ∀ z ∈ closure (Metric.ball c R), -M ≤ F z := by
    simpa [F] using
      le_poissonDiskDirichletCandidate_of_le_boundaryData
        c hR_pos f hf_front_cont hf_front_ge
  have hf_bound_of_norm_lt_R :
      ∀ z : ℂ, ‖z - c‖ < R → z ≠ c → ‖f z‖ ≤ M := by
    intro z hzR hz_ne
    have hz_punct : z ∈ Metric.ball c r \ {c} := by
      refine ⟨?_, by simpa [Set.mem_singleton_iff] using hz_ne⟩
      rw [Metric.mem_ball, dist_eq_norm]
      exact hzR.trans hR_lt_r
    have hdist : dist z c < ε := by
      rw [dist_eq_norm]
      exact hzR.trans hR_lt_ε
    exact hε hdist hz_punct
  have hF_mem_closure_of_norm_le_R :
      ∀ z : ℂ, ‖z - c‖ ≤ R → z ∈ closure (Metric.ball c R) := by
    intro z hzR
    rw [closure_ball c hR_pos.ne']
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzR
  have hF_abs_bound_of_norm_le_R :
      ∀ z : ℂ, ‖z - c‖ ≤ R → |F z| ≤ M := by
    intro z hzR
    have hzcl := hF_mem_closure_of_norm_le_R z hzR
    exact abs_le.mpr ⟨hF_ge z hzcl, hF_le z hzcl⟩
  have heq_on_punctured_ball :
      ∀ z : ℂ, z ∈ Metric.ball c R → z ≠ c → f z = F z := by
    intro z hz_ball hz_ne
    have hzR : ‖z - c‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz_ball
    have hzpos : 0 < ‖z - c‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne)
    let u : ℂ → ℝ := fun y ↦ f y - F y
    have upper_nonpos : u z ≤ 0 := by
      by_contra hnot
      have hposu : 0 < u z := lt_of_not_ge hnot
      rcases exists_inner_radius_complexAnnularLogBarrier_lt
          c hR_pos hzpos hzR hposu with
        ⟨ρ, hρ_pos, hρ_lt_z, hρ_lt_R, hbar_lt⟩
      have hρR : ρ < R := hρ_lt_R
      have h_ann_subset_punct :
          complexRoundAnnulus c ρ R ⊆ Metric.ball c r \ {c} := by
        intro y hy
        have hy_ne : y ≠ c := by
          have hpos : 0 < ‖y - c‖ := hρ_pos.trans hy.1
          exact sub_ne_zero.mp (norm_pos_iff.mp hpos)
        refine ⟨?_, by simpa [Set.mem_singleton_iff] using hy_ne⟩
        rw [Metric.mem_ball, dist_eq_norm]
        exact hy.2.trans hR_lt_r
      have h_ann_subset_ball_R :
          complexRoundAnnulus c ρ R ⊆ Metric.ball c R := by
        intro y hy
        simpa [Metric.mem_ball, dist_eq_norm] using hy.2
      have hu_harm :
          InnerProductSpace.HarmonicOnNhd u (complexRoundAnnulus c ρ R) := by
        have hf_ann : InnerProductSpace.HarmonicOnNhd f (complexRoundAnnulus c ρ R) :=
          hharm.mono h_ann_subset_punct
        have hF_ann : InnerProductSpace.HarmonicOnNhd F (complexRoundAnnulus c ρ R) :=
          hF_harm.mono h_ann_subset_ball_R
        simpa [u] using hf_ann.sub hF_ann
      have h_closure_subset_punct :
          closure (complexRoundAnnulus c ρ R) ⊆ Metric.ball c r \ {c} := by
        intro y hy
        have hyclosed :=
          complexRoundAnnulus_closure_subset_closed_annulus c ρ R hy
        have hy_ne : y ≠ c := by
          have hpos : 0 < ‖y - c‖ := hρ_pos.trans_le hyclosed.1
          exact sub_ne_zero.mp (norm_pos_iff.mp hpos)
        refine ⟨?_, by simpa [Set.mem_singleton_iff] using hy_ne⟩
        rw [Metric.mem_ball, dist_eq_norm]
        exact lt_of_le_of_lt hyclosed.2 hR_lt_r
      have h_closure_subset_closed_R :
          closure (complexRoundAnnulus c ρ R) ⊆ closure (Metric.ball c R) := by
        intro y hy
        have hyclosed :=
          complexRoundAnnulus_closure_subset_closed_annulus c ρ R hy
        exact hF_mem_closure_of_norm_le_R y hyclosed.2
      have hu_cont :
          ContinuousOn u (closure (complexRoundAnnulus c ρ R)) := by
        have hf_cont := hharm.continuousOn.mono h_closure_subset_punct
        have hF_cont' := hF_cont.mono h_closure_subset_closed_R
        exact hf_cont.sub hF_cont'
      have hinner :
          ∀ y : ℂ, ‖y - c‖ = ρ → u y ≤ 2 * M := by
        intro y hyρ
        have hy_ne : y ≠ c := by
          have hpos : 0 < ‖y - c‖ := by rw [hyρ]; exact hρ_pos
          exact sub_ne_zero.mp (norm_pos_iff.mp hpos)
        have hf_abs : |f y| ≤ M := by
          have hfy := hf_bound_of_norm_lt_R y (by rw [hyρ]; exact hρ_lt_R) hy_ne
          simpa [Real.norm_eq_abs] using hfy
        have hF_abs : |F y| ≤ M :=
          hF_abs_bound_of_norm_le_R y (by rw [hyρ]; exact le_of_lt hρ_lt_R)
        have hf_le : f y ≤ M := (abs_le.mp hf_abs).2
        have hF_ge_y : -M ≤ F y := (abs_le.mp hF_abs).1
        dsimp [u]
        linarith
      have houter :
          ∀ y : ℂ, ‖y - c‖ = R → u y ≤ 0 := by
        intro y hyR
        have hy_front : y ∈ frontier (Metric.ball c R) := by
          rw [frontier_ball c hR_pos.ne']
          simpa [Metric.mem_sphere, dist_eq_norm] using hyR
        dsimp [u]
        rw [hF_boundary y hy_front]
        linarith
      have hcomp :=
        harmonicOnNhd_le_complexAnnularLogBarrier_of_boundary_le
          c hρ_pos hρR hu_harm hu_cont hinner houter
          z ⟨hρ_lt_z, hzR⟩
      dsimp [u] at hbar_lt hcomp hposu
      linarith
    have lower_nonneg : 0 ≤ u z := by
      by_contra hnot
      have hposu : 0 < -u z := neg_pos.mpr (lt_of_not_ge hnot)
      rcases exists_inner_radius_complexAnnularLogBarrier_lt
          c hR_pos hzpos hzR hposu with
        ⟨ρ, hρ_pos, hρ_lt_z, hρ_lt_R, hbar_lt⟩
      have hρR : ρ < R := hρ_lt_R
      let v : ℂ → ℝ := fun y ↦ -u y
      have h_ann_subset_punct :
          complexRoundAnnulus c ρ R ⊆ Metric.ball c r \ {c} := by
        intro y hy
        have hy_ne : y ≠ c := by
          have hpos : 0 < ‖y - c‖ := hρ_pos.trans hy.1
          exact sub_ne_zero.mp (norm_pos_iff.mp hpos)
        refine ⟨?_, by simpa [Set.mem_singleton_iff] using hy_ne⟩
        rw [Metric.mem_ball, dist_eq_norm]
        exact hy.2.trans hR_lt_r
      have h_ann_subset_ball_R :
          complexRoundAnnulus c ρ R ⊆ Metric.ball c R := by
        intro y hy
        simpa [Metric.mem_ball, dist_eq_norm] using hy.2
      have hv_harm :
          InnerProductSpace.HarmonicOnNhd v (complexRoundAnnulus c ρ R) := by
        have hf_ann : InnerProductSpace.HarmonicOnNhd f (complexRoundAnnulus c ρ R) :=
          hharm.mono h_ann_subset_punct
        have hF_ann : InnerProductSpace.HarmonicOnNhd F (complexRoundAnnulus c ρ R) :=
          hF_harm.mono h_ann_subset_ball_R
        have hu_harm : InnerProductSpace.HarmonicOnNhd u (complexRoundAnnulus c ρ R) := by
          simpa [u] using hf_ann.sub hF_ann
        simpa [v] using hu_harm.neg
      have h_closure_subset_punct :
          closure (complexRoundAnnulus c ρ R) ⊆ Metric.ball c r \ {c} := by
        intro y hy
        have hyclosed :=
          complexRoundAnnulus_closure_subset_closed_annulus c ρ R hy
        have hy_ne : y ≠ c := by
          have hpos : 0 < ‖y - c‖ := hρ_pos.trans_le hyclosed.1
          exact sub_ne_zero.mp (norm_pos_iff.mp hpos)
        refine ⟨?_, by simpa [Set.mem_singleton_iff] using hy_ne⟩
        rw [Metric.mem_ball, dist_eq_norm]
        exact lt_of_le_of_lt hyclosed.2 hR_lt_r
      have h_closure_subset_closed_R :
          closure (complexRoundAnnulus c ρ R) ⊆ closure (Metric.ball c R) := by
        intro y hy
        have hyclosed :=
          complexRoundAnnulus_closure_subset_closed_annulus c ρ R hy
        exact hF_mem_closure_of_norm_le_R y hyclosed.2
      have hv_cont :
          ContinuousOn v (closure (complexRoundAnnulus c ρ R)) := by
        have hf_cont := hharm.continuousOn.mono h_closure_subset_punct
        have hF_cont' := hF_cont.mono h_closure_subset_closed_R
        have hu_cont : ContinuousOn u (closure (complexRoundAnnulus c ρ R)) :=
          hf_cont.sub hF_cont'
        exact hu_cont.neg
      have hinner :
          ∀ y : ℂ, ‖y - c‖ = ρ → v y ≤ 2 * M := by
        intro y hyρ
        have hy_ne : y ≠ c := by
          have hpos : 0 < ‖y - c‖ := by rw [hyρ]; exact hρ_pos
          exact sub_ne_zero.mp (norm_pos_iff.mp hpos)
        have hf_abs : |f y| ≤ M := by
          have hfy := hf_bound_of_norm_lt_R y (by rw [hyρ]; exact hρ_lt_R) hy_ne
          simpa [Real.norm_eq_abs] using hfy
        have hF_abs : |F y| ≤ M :=
          hF_abs_bound_of_norm_le_R y (by rw [hyρ]; exact le_of_lt hρ_lt_R)
        have hf_ge : -M ≤ f y := (abs_le.mp hf_abs).1
        have hF_le_y : F y ≤ M := (abs_le.mp hF_abs).2
        dsimp [v, u]
        linarith
      have houter :
          ∀ y : ℂ, ‖y - c‖ = R → v y ≤ 0 := by
        intro y hyR
        have hy_front : y ∈ frontier (Metric.ball c R) := by
          rw [frontier_ball c hR_pos.ne']
          simpa [Metric.mem_sphere, dist_eq_norm] using hyR
        dsimp [v, u]
        rw [hF_boundary y hy_front]
        linarith
      have hcomp :=
        harmonicOnNhd_le_complexAnnularLogBarrier_of_boundary_le
          c hρ_pos hρR hv_harm hv_cont hinner houter
          z ⟨hρ_lt_z, hzR⟩
      dsimp [v] at hbar_lt hcomp hposu
      linarith
    have huz : u z = 0 := le_antisymm upper_nonpos lower_nonneg
    dsimp [u] at huz
    linarith
  refine ⟨R, F, hR_pos, le_of_lt hR_lt_r, hF_harm, ?_⟩
  have hsmall_ball :
      Metric.ball c R ∈ 𝓝[Metric.ball c r \ {c}] c :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds c hR_pos)
  filter_upwards
    [hsmall_ball,
      (self_mem_nhdsWithin :
        Metric.ball c r \ {c} ∈ 𝓝[Metric.ball c r \ {c}] c)] with
      z hzR hzpunct
  exact heq_on_punctured_ball z hzR
    (by simpa [Set.mem_singleton_iff] using hzpunct.2)

/--
%%handwave
name:
  Bounded punctured disk harmonic functions have a finite limit
statement:
  A bounded harmonic function on a punctured Euclidean disk has a finite limit
  at the puncture.
proof:
  Apply the removable-extension theorem.  The harmonic extension is continuous
  at the puncture, and the original function agrees with it eventually on the
  punctured neighborhood.
-/
theorem bounded_harmonicOn_punctured_complex_ball_has_limit
    {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ}
    (hharm :
      InnerProductSpace.HarmonicOnNhd f (Metric.ball c r \ {c}))
    (hbound :
      ∃ M : ℝ,
        ∀ᶠ z in 𝓝[Metric.ball c r \ {c}] c, ‖f z‖ ≤ M) :
    ∃ a : ℝ, Filter.Tendsto f (𝓝[Metric.ball c r \ {c}] c) (𝓝 a) := by
  rcases bounded_harmonicOn_punctured_complex_ball_has_removable_extension_core
      hr hharm hbound with
    ⟨δ, F, hδ_pos, _hδ_le, hF_harm, hF_eq⟩
  refine ⟨F c, ?_⟩
  have hcδ : c ∈ Metric.ball c δ := by
    simpa [Metric.mem_ball] using hδ_pos
  have hF_cont : ContinuousOn F (Metric.ball c δ) :=
    hF_harm.continuousOn
  have hF_tendsto : Filter.Tendsto F (𝓝[Metric.ball c δ] c) (𝓝 (F c)) :=
    hF_cont c hcδ
  have hsmall :
      Metric.ball c δ ∈ 𝓝[Metric.ball c r \ {c}] c :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds c hδ_pos)
  have hmono :
      𝓝[Metric.ball c r \ {c}] c ≤ 𝓝[Metric.ball c δ] c :=
    nhdsWithin_le_iff.mpr hsmall
  have hFeq :
      F =ᶠ[𝓝[Metric.ball c r \ {c}] c] f := by
    filter_upwards [hF_eq] with z hz
    exact hz.symm
  exact (hF_tendsto.mono_left hmono).congr' hFeq

/--
%%handwave
name:
  The punctured disk accumulates at its centre
statement:
  In the complex plane, the centre of a positive-radius disk lies in the
  closure of the same disk with the centre removed.
proof:
  Every neighborhood of the centre contains a smaller point on a real radius.
-/
theorem complex_punctured_ball_nhdsWithin_neBot
    {c : ℂ} {r : ℝ} (hr : 0 < r) :
    Filter.NeBot (𝓝[Metric.ball c r \ {c}] c) := by
  refine mem_closure_iff_nhdsWithin_neBot.mp ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := min r ε / 2
  have hδ_pos : 0 < δ := half_pos (lt_min hr hε)
  have hδ_le_r_half : δ ≤ r / 2 := by
    dsimp [δ]
    exact div_le_div_of_nonneg_right (min_le_left r ε) (by norm_num : (0 : ℝ) ≤ 2)
  have hδ_lt_r : δ < r :=
    hδ_le_r_half.trans_lt (half_lt_self hr)
  have hδ_le_ε_half : δ ≤ ε / 2 := by
    dsimp [δ]
    exact div_le_div_of_nonneg_right (min_le_right r ε) (by norm_num : (0 : ℝ) ≤ 2)
  have hδ_lt_ε : δ < ε :=
    hδ_le_ε_half.trans_lt (half_lt_self hε)
  let z : ℂ := c + (δ : ℂ)
  have hz_dist : dist z c = δ := by
    rw [Complex.dist_eq]
    have hsub : z - c = (δ : ℂ) := by
      simp [z]
    rw [hsub, Complex.norm_real, Real.norm_of_nonneg hδ_pos.le]
  have hz_ne : z ≠ c := by
    intro hzc
    have hδ_zero : (δ : ℂ) = 0 := by
      calc
        (δ : ℂ) = z - c := by simp [z]
        _ = 0 := by simp [hzc]
    have : δ = 0 := Complex.ofReal_injective hδ_zero
    exact hδ_pos.ne' this
  refine ⟨z, ?_, ?_⟩
  · exact ⟨by simpa [Metric.mem_ball, hz_dist] using hδ_lt_r,
      by simpa [Set.mem_singleton_iff] using hz_ne⟩
  · have hz_dist' : dist c z = δ := by
      simpa [dist_comm] using hz_dist
    simpa [Metric.mem_ball, hz_dist'] using hδ_lt_ε

/--
%%handwave
name:
  A finite-limit punctured harmonic function is removable
statement:
  If a harmonic function on a punctured Euclidean disk has a finite limit at
  the puncture, then updating the function to that limiting value is harmonic
  on a smaller full disk.
proof:
  The finite limit gives continuity of the updated function at the puncture.
  Apply the removable singularity theorem for harmonic functions, equivalently
  apply the holomorphic removable singularity theorem to local harmonic
  conjugates on small simply connected disks and identify the real parts.
-/
theorem punctured_harmonicOn_complex_ball_update_harmonic_of_tendsto
    {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ} {a : ℝ}
    (hharm :
      InnerProductSpace.HarmonicOnNhd f (Metric.ball c r \ {c}))
    (hlim : Filter.Tendsto f (𝓝[Metric.ball c r \ {c}] c) (𝓝 a)) :
    ∃ δ : ℝ,
      0 < δ ∧ δ ≤ r ∧
        InnerProductSpace.HarmonicOnNhd (Function.update f c a) (Metric.ball c δ) := by
  let l : Filter ℂ := 𝓝[Metric.ball c r \ {c}] c
  haveI : Filter.NeBot l := complex_punctured_ball_nhdsWithin_neBot hr
  have hbound :
      ∃ M : ℝ,
        ∀ᶠ z in 𝓝[Metric.ball c r \ {c}] c, ‖f z‖ ≤ M := by
    have hnorm : Filter.Tendsto (fun z ↦ ‖f z‖) l (𝓝 ‖a‖) :=
      tendsto_norm.comp hlim
    refine ⟨‖a‖ + 1, ?_⟩
    exact (hnorm.eventually (Iio_mem_nhds (lt_add_of_pos_right ‖a‖ zero_lt_one))).mono
      (by intro z hz; exact le_of_lt hz)
  rcases bounded_harmonicOn_punctured_complex_ball_has_removable_extension_core
      hr hharm hbound with
    ⟨δ, F, hδ_pos, hδ_le, hF_harm, hF_eq⟩
  have hcδ : c ∈ Metric.ball c δ := by
    simpa [Metric.mem_ball] using hδ_pos
  have hF_cont : ContinuousOn F (Metric.ball c δ) :=
    hF_harm.continuousOn
  have hF_tendsto_ball : Filter.Tendsto F (𝓝[Metric.ball c δ] c) (𝓝 (F c)) :=
    hF_cont c hcδ
  have hsmall :
      Metric.ball c δ ∈ 𝓝[Metric.ball c r \ {c}] c :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds c hδ_pos)
  have hmono :
      𝓝[Metric.ball c r \ {c}] c ≤ 𝓝[Metric.ball c δ] c :=
    nhdsWithin_le_iff.mpr hsmall
  have hF_tendsto_punct :
      Filter.Tendsto F (𝓝[Metric.ball c r \ {c}] c) (𝓝 (F c)) :=
    hF_tendsto_ball.mono_left hmono
  have hF_tendsto_a :
      Filter.Tendsto F (𝓝[Metric.ball c r \ {c}] c) (𝓝 a) :=
    hlim.congr' hF_eq
  have hFc : F c = a :=
    tendsto_nhds_unique hF_tendsto_punct hF_tendsto_a
  have hupdate_eq_F_nhds : Function.update f c a =ᶠ[𝓝 c] F := by
    let E : Set ℂ := {z : ℂ | z ∈ Metric.ball c r \ {c} → f z = F z}
    have hE_nhds : E ∈ 𝓝 c := by
      simpa [E] using eventually_nhdsWithin_iff.mp hF_eq
    filter_upwards [hE_nhds, Metric.ball_mem_nhds c hr] with z hzE hzball
    by_cases hzc : z = c
    · subst z
      simp [hFc]
    · have hzpunct : z ∈ Metric.ball c r \ {c} :=
        ⟨hzball, by simpa [Set.mem_singleton_iff] using hzc⟩
      simpa [Function.update, hzc] using hzE hzpunct
  refine ⟨δ, hδ_pos, hδ_le, ?_⟩
  intro z hz
  by_cases hzc : z = c
  · subst z
    exact (InnerProductSpace.harmonicAt_congr_nhds hupdate_eq_F_nhds).2
      (hF_harm c hcδ)
  · have hz_ball_r : z ∈ Metric.ball c r := by
      rw [Metric.mem_ball] at hz ⊢
      exact hz.trans_le hδ_le
    have hupdate_eq_f_nhds : Function.update f c a =ᶠ[𝓝 z] f := by
      filter_upwards [eventually_ne_nhds hzc] with y hy
      simp [Function.update, hy]
    exact (InnerProductSpace.harmonicAt_congr_nhds hupdate_eq_f_nhds).2
      (hharm z ⟨hz_ball_r, by simpa [Set.mem_singleton_iff] using hzc⟩)

/--
%%handwave
name:
  A removable punctured disk harmonic function is harmonic on the whole disk
statement:
  If a harmonic function on a punctured disk has a finite limit at the
  puncture, then filling in that limiting value gives a harmonic function on
  the entire disk.
proof:
  The removable-singularity theorem gives harmonicity in a small full disk
  around the puncture.  Away from the puncture the filled-in function agrees
  locally with the original harmonic function.
-/
theorem punctured_harmonicOn_complex_ball_update_harmonicOn_ball_of_tendsto
    {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ} {a : ℝ}
    (hharm :
      InnerProductSpace.HarmonicOnNhd f (Metric.ball c r \ {c}))
    (hlim : Filter.Tendsto f (𝓝[Metric.ball c r \ {c}] c) (𝓝 a)) :
    InnerProductSpace.HarmonicOnNhd (Function.update f c a)
      (Metric.ball c r) := by
  rcases punctured_harmonicOn_complex_ball_update_harmonic_of_tendsto
      hr hharm hlim with
    ⟨δ, hδ_pos, _hδ_le, hupdate_local⟩
  intro z hz
  by_cases hzc : z = c
  · subst z
    exact hupdate_local c (by simpa [Metric.mem_ball] using hδ_pos)
  · have hupdate_eq_f_nhds :
        Function.update f c a =ᶠ[𝓝 z] f := by
      filter_upwards [eventually_ne_nhds hzc] with y hy
      simp [Function.update, hy]
    exact (InnerProductSpace.harmonicAt_congr_nhds hupdate_eq_f_nhds).2
      (hharm z ⟨hz, by simpa [Set.mem_singleton_iff] using hzc⟩)

/--
%%handwave
name:
  The Euclidean coordinate logarithm is harmonic off its centre
statement:
  On a punctured complex disk, the function \(z\mapsto \log |z-c|\) is
  harmonic.
proof:
  It is the logarithm of the norm of the nonvanishing holomorphic function
  \(z\mapsto z-c\) on the punctured disk.
-/
theorem complex_log_norm_sub_harmonicOn_punctured_ball
    {c : ℂ} {r : ℝ} :
    InnerProductSpace.HarmonicOnNhd
      (fun z : ℂ ↦ Real.log ‖z - c‖) (Metric.ball c r \ {c}) := by
  intro z hz
  have hzc : z ≠ c := by
    simpa [Set.mem_singleton_iff] using hz.2
  have hne : (fun w : ℂ ↦ w - c) z ≠ 0 := sub_ne_zero.mpr hzc
  exact (by fun_prop :
    AnalyticAt ℂ (fun w : ℂ ↦ w - c) z).harmonicAt_log_norm hne

/--
%%handwave
name:
  Filling a punctured disk limit gives closed-disk continuity
statement:
  If a real-valued function is continuous on the punctured closed disk and has
  a finite limit at the puncture through the punctured open disk, then filling
  in that limiting value gives a continuous function on the closed disk.
proof:
  Away from the puncture, changing the value at the puncture is irrelevant.
  At the puncture, a closed-disk approach eventually lies in the open disk, so
  the assumed punctured-disk limit applies.
-/
theorem punctured_tendsto_update_continuousOn_closedBall
    {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ} {a : ℝ}
    (hlim : Filter.Tendsto f (𝓝[Metric.ball c r \ {c}] c) (𝓝 a))
    (hcont : ContinuousOn f (Metric.closedBall c r \ {c})) :
    ContinuousOn (Function.update f c a) (Metric.closedBall c r) := by
  rw [continuousOn_update_iff]
  refine ⟨hcont, ?_⟩
  intro _hc_closed
  have hsmall :
      Metric.ball c r \ {c} ∈ 𝓝[Metric.closedBall c r \ {c}] c := by
    filter_upwards
      [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds c hr),
        (self_mem_nhdsWithin :
          Metric.closedBall c r \ {c} ∈
            𝓝[Metric.closedBall c r \ {c}] c)] with
        z hz_ball hz_closed
    exact ⟨hz_ball, hz_closed.2⟩
  exact hlim.mono_left (nhdsWithin_le_iff.mpr hsmall)

/--
%%handwave
name:
  Boundary norm bounds control disk harmonic functions
statement:
  A harmonic function on a disk, continuous on the closed disk, whose absolute
  value is bounded by \(M\) on the boundary circle, has absolute value bounded
  by \(M\) throughout the disk.
proof:
  Apply the maximum principle to the function and to its negative.
-/
theorem harmonicOn_complex_ball_norm_le_of_frontier_norm_le
    {c : ℂ} {r : ℝ} (hr : 0 < r) {F : ℂ → ℝ} {M : ℝ}
    (hF_harm : InnerProductSpace.HarmonicOnNhd F (Metric.ball c r))
    (hF_cont : ContinuousOn F (closure (Metric.ball c r)))
    (hfront : ∀ z ∈ frontier (Metric.ball c r), ‖F z‖ ≤ M) :
    ∀ z ∈ Metric.ball c r, ‖F z‖ ≤ M := by
  have hF_front_le : ∀ z ∈ frontier (Metric.ball c r), F z ≤ M := by
    intro z hz
    have hz_abs : |F z| ≤ M := by
      simpa [Real.norm_eq_abs] using hfront z hz
    exact (abs_le.mp hz_abs).2
  have hF_front_ge : ∀ z ∈ frontier (Metric.ball c r), -M ≤ F z := by
    intro z hz
    have hz_abs : |F z| ≤ M := by
      simpa [Real.norm_eq_abs] using hfront z hz
    exact (abs_le.mp hz_abs).1
  have hball_compact : IsCompact (closure (Metric.ball c r)) := by
    rw [closure_ball c hr.ne']
    exact isCompact_closedBall c r
  have hfront_nonempty : (frontier (Metric.ball c r)).Nonempty := by
    refine ⟨c + (r : ℂ), ?_⟩
    rw [frontier_ball c hr.ne']
    have hdist : dist (c + (r : ℂ)) c = r := by
      rw [Complex.dist_eq]
      have hsub : c + (r : ℂ) - c = (r : ℂ) := by ring
      rw [hsub, Complex.norm_real, Real.norm_of_nonneg hr.le]
    simpa [Metric.mem_sphere] using hdist
  have hF_le : ∀ z ∈ Metric.ball c r, F z ≤ M :=
    harmonicOnNhd_le_constant_of_boundary_le
      Metric.isOpen_ball Metric.isPreconnected_ball hball_compact
      hfront_nonempty hF_harm hF_cont hF_front_le
  have hnegF_harm :
      InnerProductSpace.HarmonicOnNhd (fun z : ℂ ↦ -F z)
        (Metric.ball c r) :=
    hF_harm.neg
  have hnegF_cont : ContinuousOn (fun z : ℂ ↦ -F z)
      (closure (Metric.ball c r)) :=
    hF_cont.neg
  have hnegF_front_le :
      ∀ z ∈ frontier (Metric.ball c r), -F z ≤ M := by
    intro z hz
    exact neg_le.mp (hF_front_ge z hz)
  have hnegF_le : ∀ z ∈ Metric.ball c r, -F z ≤ M :=
    harmonicOnNhd_le_constant_of_boundary_le
      Metric.isOpen_ball Metric.isPreconnected_ball hball_compact
      hfront_nonempty hnegF_harm hnegF_cont hnegF_front_le
  intro z hz
  have hF_abs : |F z| ≤ M :=
    abs_le.mpr ⟨neg_le.mp (hnegF_le z hz), hF_le z hz⟩
  simpa [Real.norm_eq_abs] using hF_abs

/--
%%handwave
name:
  Boundary norm bounds control removable punctured disk harmonic functions
statement:
  Let a harmonic function on a punctured disk have a finite limit at the
  puncture and be continuous on the punctured closed disk.  If its absolute
  value is bounded on the outer circle, then the same bound holds throughout
  the punctured disk.
proof:
  Fill in the puncture by the limiting value.  The filled-in function is
  harmonic on the whole disk and continuous on the closed disk, so the disk
  maximum principle applied to the function and to its negative gives the
  asserted absolute-value bound.
-/
theorem punctured_harmonicOn_complex_ball_norm_le_of_frontier_norm_le_of_tendsto
    {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ} {a M : ℝ}
    (hharm :
      InnerProductSpace.HarmonicOnNhd f (Metric.ball c r \ {c}))
    (hlim : Filter.Tendsto f (𝓝[Metric.ball c r \ {c}] c) (𝓝 a))
    (hcont : ContinuousOn f (Metric.closedBall c r \ {c}))
    (hfront : ∀ z ∈ frontier (Metric.ball c r), ‖f z‖ ≤ M) :
    ∀ z ∈ Metric.ball c r \ {c}, ‖f z‖ ≤ M := by
  let F : ℂ → ℝ := Function.update f c a
  have hF_harm :
      InnerProductSpace.HarmonicOnNhd F (Metric.ball c r) := by
    simpa [F] using
      punctured_harmonicOn_complex_ball_update_harmonicOn_ball_of_tendsto
        hr hharm hlim
  have hF_cont_closed :
      ContinuousOn F (Metric.closedBall c r) := by
    simpa [F] using
      punctured_tendsto_update_continuousOn_closedBall
        hr hlim hcont
  have hF_cont :
      ContinuousOn F (closure (Metric.ball c r)) := by
    rwa [closure_ball c hr.ne']
  have hF_front : ∀ z ∈ frontier (Metric.ball c r), ‖F z‖ ≤ M := by
    intro z hz
    have hz_sphere : z ∈ Metric.sphere c r := by
      simpa [frontier_ball c hr.ne'] using hz
    have hzc : z ≠ c := Metric.ne_of_mem_sphere hz_sphere hr.ne'
    simpa [F, Function.update, hzc] using hfront z hz
  have hmax :
      ∀ z ∈ Metric.ball c r, ‖F z‖ ≤ M :=
    harmonicOn_complex_ball_norm_le_of_frontier_norm_le
      hr hF_harm hF_cont hF_front
  intro z hz
  have hzc : z ≠ c := by
    simpa [Set.mem_singleton_iff] using hz.2
  simpa [F, Function.update, hzc] using hmax z hz.1

/--
%%handwave
name:
  Bounded punctured disk harmonic functions are removable
statement:
  A bounded harmonic function on a punctured Euclidean disk has a harmonic
  extension across the puncture on a smaller disk.
proof:
  This is the classical removable singularity theorem for harmonic functions.
  One may prove it by taking a local harmonic conjugate and applying the
  removable singularity theorem for bounded holomorphic functions, or directly
  from the Poisson representation and the mean-value property.
-/
theorem bounded_harmonicOn_punctured_complex_ball_has_removable_extension
    {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ}
    (hharm :
      InnerProductSpace.HarmonicOnNhd f (Metric.ball c r \ {c}))
    (hbound :
      ∃ M : ℝ,
        ∀ᶠ z in 𝓝[Metric.ball c r \ {c}] c, ‖f z‖ ≤ M) :
    ∃ δ : ℝ, ∃ F : ℂ → ℝ,
      0 < δ ∧ δ ≤ r ∧
        InnerProductSpace.HarmonicOnNhd F (Metric.ball c δ) ∧
          ∀ᶠ z in 𝓝[Metric.ball c r \ {c}] c, f z = F z := by
  exact bounded_harmonicOn_punctured_complex_ball_has_removable_extension_core
    hr hharm hbound

/--
%%handwave
name:
  Local removable singularity for bounded punctured harmonic functions
statement:
  A bounded harmonic function on a punctured coordinate neighborhood has a
  harmonic extension on some full neighborhood of the puncture.
proof:
  Transport the function to a punctured planar neighborhood and apply
  [the bounded punctured-disk removable singularity theorem](lean:JJMath.Uniformization.bounded_harmonicOn_punctured_complex_ball_has_removable_extension).
  Pull the planar harmonic extension back to the surface.
-/
theorem bounded_harmonicOn_punctured_pointed_coordinate_has_local_removable_extension
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ : PointedSurfaceCoordinate X p) (g : X → ℝ)
    (hharm :
      IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p}) g)
    (hbound :
      ∃ M : ℝ,
        ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
          ‖g x‖ ≤ M) :
    ∃ N : Set X, ∃ h : X → ℝ,
      IsOpen N ∧ p ∈ N ∧ N ⊆ χ.chart.source ∧
        IsHarmonicOnSurface N h ∧
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            g x = h x := by
  let c : ℂ := χ.chart p
  have hc_target : c ∈ χ.chart.target :=
    χ.chart.map_source χ.base_mem_source
  rcases Metric.mem_nhds_iff.mp (χ.chart.open_target.mem_nhds hc_target) with
    ⟨R₀, hR₀_pos, hball_target⟩
  let r : ℝ := R₀ / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hrR₀ : r < R₀ := by
    dsimp [r]
    linarith
  have hclosed_r : Metric.closedBall c r ⊆ χ.chart.target :=
    (Metric.closedBall_subset_ball hrR₀).trans hball_target
  let f : ℂ → ℝ := fun z ↦ g (χ.chart.symm z)
  have hharm_planar :
      InnerProductSpace.HarmonicOnNhd f (Metric.ball c r \ {c}) := by
    have hsurface := hharm χ.chart χ.chart_mem_atlas
    refine hsurface.mono ?_
    intro z hz
    have hzball : z ∈ Metric.ball c r := hz.1
    have hz_target : z ∈ χ.chart.target :=
      hclosed_r (Metric.ball_subset_closedBall hzball)
    have hsymm_source : χ.chart.symm z ∈ χ.chart.source :=
      χ.chart.map_target hz_target
    have hsymm_ne : χ.chart.symm z ≠ p := by
      intro hsymm_eq
      have hz_eq_c : z = c := by
        calc
          z = χ.chart (χ.chart.symm z) := (χ.chart.right_inv hz_target).symm
          _ = χ.chart p := by rw [hsymm_eq]
          _ = c := rfl
      exact hz.2 (by simpa [Set.mem_singleton_iff] using hz_eq_c)
    exact ⟨hz_target, hsymm_source, hsymm_ne⟩
  have hbound_planar :
      ∃ M : ℝ,
        ∀ᶠ z in 𝓝[Metric.ball c r \ {c}] c, ‖f z‖ ≤ M := by
    rcases hbound with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    let E : Set X :=
      {x : X | x ∈ χ.chart.source ∩ {x : X | x ≠ p} → ‖g x‖ ≤ M}
    have hE_nhds : E ∈ 𝓝 p := by
      simpa [E] using eventually_nhdsWithin_iff.mp hM
    have hpre_map :
        E ∈ Filter.map χ.chart.symm (𝓝 c) :=
      χ.chart.continuousAt_symm hc_target
        (by simpa [c, χ.chart.left_inv χ.base_mem_source] using hE_nhds)
    have hpre : χ.chart.symm ⁻¹' E ∈ 𝓝 c := by
      simpa [Filter.mem_map] using hpre_map
    filter_upwards [mem_nhdsWithin_of_mem_nhds hpre, self_mem_nhdsWithin] with
      z hzE hzpunct
    have hz_target : z ∈ χ.chart.target :=
      hclosed_r (Metric.ball_subset_closedBall hzpunct.1)
    have hsymm_source : χ.chart.symm z ∈ χ.chart.source :=
      χ.chart.map_target hz_target
    have hsymm_ne : χ.chart.symm z ≠ p := by
      intro hsymm_eq
      have hz_eq_c : z = c := by
        calc
          z = χ.chart (χ.chart.symm z) := (χ.chart.right_inv hz_target).symm
          _ = χ.chart p := by rw [hsymm_eq]
          _ = c := rfl
      exact hzpunct.2 (by simpa [Set.mem_singleton_iff] using hz_eq_c)
    exact hzE ⟨hsymm_source, hsymm_ne⟩
  rcases bounded_harmonicOn_punctured_complex_ball_has_removable_extension
      hr hharm_planar hbound_planar with
    ⟨δ, F, hδ_pos, _hδr, hF_harm, hF_eq⟩
  let N : Set X := χ.chart.source ∩ χ.chart ⁻¹' Metric.ball c δ
  let h : X → ℝ := fun x ↦ F (χ.chart x)
  refine ⟨N, h, ?_, ?_, ?_, ?_, ?_⟩
  · exact χ.chart.isOpen_inter_preimage Metric.isOpen_ball
  · exact ⟨χ.base_mem_source, by simp [Metric.mem_ball, c, hδ_pos]⟩
  · intro x hx
    exact hx.1
  · intro e he z hz
    have hz_target : z ∈ e.target := hz.1
    have hxN : e.symm z ∈ N := hz.2
    have hxχ_source : e.symm z ∈ χ.chart.source := hxN.1
    have hF_at :
        InnerProductSpace.HarmonicAt F (χ.chart (e.symm z)) :=
      hF_harm (χ.chart (e.symm z)) hxN.2
    have htransition :
        AnalyticAt ℂ (fun w : ℂ ↦ χ.chart (e.symm w)) z :=
      chartTransition_analyticAt e he χ.chart χ.chart_mem_atlas
        hz_target hxχ_source
    simpa [h, Function.comp_def] using
      harmonicAt_comp_analyticAt hF_at htransition
  · let E : Set ℂ :=
      {z : ℂ | z ∈ Metric.ball c r \ {c} → f z = F z}
    have hE_nhds : E ∈ 𝓝 c := by
      simpa [E] using eventually_nhdsWithin_iff.mp hF_eq
    have hpre : χ.chart ⁻¹' E ∈ 𝓝 p :=
      χ.chart.continuousAt χ.base_mem_source hE_nhds
    have hball :
        {x : X | χ.chart x ∈ Metric.ball c r} ∈ 𝓝 p := by
      exact (χ.chart.continuousAt χ.base_mem_source).preimage_mem_nhds
        (Metric.ball_mem_nhds _ hr)
    filter_upwards
      [mem_nhdsWithin_of_mem_nhds hpre,
        mem_nhdsWithin_of_mem_nhds hball,
        self_mem_nhdsWithin]
      with x hxE hxball hxpunct
    have hxchart_ne : χ.chart x ≠ c := by
      intro hxchart
      exact hxpunct.2 (χ.chart.injOn hxpunct.1 χ.base_mem_source (by
        simpa [c] using hxchart))
    have hxchart_punct : χ.chart x ∈ Metric.ball c r \ {c} :=
      ⟨hxball, by simpa [Set.mem_singleton_iff] using hxchart_ne⟩
    have heq := hxE hxchart_punct
    simpa [f, h, χ.chart.left_inv hxpunct.1] using heq

/--
%%handwave
name:
  Bounded punctured harmonic functions in a coordinate are removable
statement:
  A harmonic function on a punctured coordinate neighborhood that is bounded
  near the puncture extends harmonically across the puncture.
proof:
  Transport the function to a punctured plane disk.  The classical removable
  singularity theorem for bounded harmonic functions gives a harmonic
  extension over the center, and transporting back gives a harmonic function
  on the whole coordinate neighborhood agreeing with the original one near the
  puncture.
-/
theorem bounded_harmonicOn_punctured_pointed_coordinate_removable
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ : PointedSurfaceCoordinate X p) (g : X → ℝ)
    (hharm :
      IsHarmonicOnSurface (χ.chart.source ∩ {x : X | x ≠ p}) g)
    (hbound :
      ∃ M : ℝ,
        ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
          ‖g x‖ ≤ M) :
    ∃ h : X → ℝ,
      IsHarmonicOnSurface χ.chart.source h ∧
        ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
          g x = h x := by
  rcases bounded_harmonicOn_punctured_pointed_coordinate_has_local_removable_extension
      X χ g hharm hbound with
    ⟨N, h₀, hN_open, hpN, hN_source, hh₀, heq⟩
  exact bounded_harmonicOn_punctured_pointed_coordinate_local_extension_globalizes
    X χ g h₀ hharm hN_open hpN hN_source hh₀ heq

/--
%%handwave
name:
  A Riemann surface has at least two points
statement:
  Every Riemann surface containing a point \(p\) is a nontrivial topological
  space.
proof:
  If the surface were a singleton, the target of a chart at \(p\) would be
  the singleton consisting of the coordinate of \(p\).  But a chart target is
  open in \(\mathbb C\), whereas no singleton in \(\mathbb C\) is open.
-/
theorem riemannSurface_nontrivial
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) :
    Nontrivial X := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  let e := chartAt ℂ p
  have htarget_subset : e.target ⊆ {e p} := by
    intro z hz
    have hz_eq : z = e (e.symm z) := (e.right_inv hz).symm
    have hsymm : e.symm z = p := Subsingleton.elim _ _
    simpa [hsymm] using hz_eq
  have htarget_eq : e.target = {e p} := by
    refine subset_antisymm htarget_subset ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact e.map_source (mem_chart_source ℂ p)
  haveI : Filter.NeBot (𝓝[≠] (e p)) := inferInstance
  exact not_isOpen_singleton (e p) (by simpa [htarget_eq] using e.open_target)

/--
%%handwave
name:
  A function with a unique zero on a Riemann surface has nontrivial range
statement:
  Let \(X\) be a Riemann surface and \(F:X\to\mathbb C\).  If
  \(F(x)=0\) exactly when \(x=p\), then the range of \(F\) contains at least
  two distinct values.
proof:
  Choose \(q\ne p\), which exists because a Riemann surface is nontrivial.
  Then \(F(p)=0\), while uniqueness of the zero gives \(F(q)\ne0\).
-/
theorem range_nontrivial_of_unique_zero_on_riemannSurface
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X} {F : X → ℂ}
    (hzero : ∀ x : X, F x = 0 ↔ x = p) :
    (Set.range F).Nontrivial := by
  classical
  haveI : Nontrivial X := riemannSurface_nontrivial X p
  rcases exists_ne p with ⟨q, hq⟩
  refine ⟨F p, ⟨p, rfl⟩, F q, ⟨q, rfl⟩, ?_⟩
  intro hpq
  have hp_zero : F p = 0 := (hzero p).mpr rfl
  have hq_zero : F q = 0 := by
    simpa [hp_zero] using hpq.symm
  exact hq ((hzero q).mp hq_zero)

/--
%%handwave
name:
  Nontrivial coordinate range from a unique model zero
statement:
  Let \(F:X\to Y\) be a map from a Riemann surface and
  \(\varphi:Y\to\mathbb C\).  If \(\varphi(F(x))=0\) exactly when \(x=p\),
  then the range of \(\varphi\circ F\) contains at least two distinct values.
proof:
  Apply the unique-zero nontrivial-range result to the complex-valued function
  \(\varphi\circ F\).
-/
theorem complexModel_range_nontrivial_of_unique_zero_on_riemannSurface
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {Y : Type} {p : X}
    {F : X → Y} {φ : Y → ℂ}
    (hzero : ∀ x : X, φ (F x) = 0 ↔ x = p) :
    (Set.range fun x : X ↦ φ (F x)).Nontrivial := by
  exact range_nontrivial_of_unique_zero_on_riemannSurface
    X (F := fun x : X ↦ φ (F x)) hzero

/--
%%handwave
name:
  Degree-one criterion for a proper map to an open complex model
statement:
  Let \(X\) be a Riemann surface, let \(Y\) be preconnected and openly
  embedded in \(\mathbb C\) by \(\varphi\), and let \(F:X\to Y\) be proper
  with \(\varphi\circ F\) holomorphic.  Suppose \(\varphi(F(x))=0\) exactly
  at \(p\), and the local multiplicity there is one in every pointed
  coordinate.  Then every \(y\in Y\) has a unique preimage under \(F\).
proof:
  The unique zero makes the coordinate range nontrivial.  Properness and the
  open mapping theorem give finite fibers and surjectivity.  The constant
  degree theorem then makes every fiber have the multiplicity of the simple
  zero fiber, namely one, and hence exactly one point.
-/
theorem proper_holomorphicMap_degree_one_of_simple_single_zero_to_openComplexModel
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [TopologicalSpace Y] [PreconnectedSpace Y]
    {p : X} {F : X → Y} {φ : Y → ℂ}
    (hφ_open : Topology.IsOpenEmbedding φ)
    (hF : HolomorphicMap X ℂ (fun x : X ↦ φ (F x)))
    (hproper : IsProperMap F)
    (hzero : ∀ x : X, φ (F x) = 0 ↔ x = p)
    (hsimple : ∀ χ : PointedSurfaceCoordinate X p,
      holomorphicMapLocalMultiplicityAtValueInCoordinate χ
        (fun x : X ↦ φ (F x)) 0 = 1) :
    ∀ y : Y, ∃! x : X, F x = y := by
  have hnonconstant : (Set.range fun x : X ↦ φ (F x)).Nontrivial :=
    complexModel_range_nontrivial_of_unique_zero_on_riemannSurface
      X (F := F) (φ := φ) hzero
  have hfinite : ∀ y : Y, {x : X | F x = y}.Finite :=
    proper_nonconstant_holomorphicMap_to_openComplexModel_fiber_finite
      hφ_open hF hnonconstant hproper
  have hsurjective : Function.Surjective F :=
    proper_nonconstant_holomorphicMap_to_openComplexModel_surjective
      hφ_open hF hnonconstant hproper
  exact proper_holomorphicMap_degree_one_of_simple_single_zero_to_complexModel
    hφ_open hF hproper hfinite hsurjective hzero hsimple

/--
%%handwave
name:
  A pointed disk map with a unique zero has nontrivial complex range
statement:
  Let \(F:X\to\mathbb D\) be a pointed holomorphic map from a Riemann surface,
  taking \(p\) to \(0\).  If its complex value is zero exactly at \(p\), then
  its complex range contains two distinct values.
proof:
  Choose \(q\ne p\).  The pointed value at \(p\) is zero, while uniqueness of
  the zero forces the complex value at \(q\) to be nonzero.
-/
theorem pointedDiskMap_complex_range_nontrivial_of_unique_zero
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hzero : ∀ x : X, (((F.toFun x : Complex.UnitDisc) : ℂ) = 0) ↔ x = p) :
    (Set.range fun x : X ↦ ((F.toFun x : Complex.UnitDisc) : ℂ)).Nontrivial := by
  classical
  haveI : Nontrivial X := riemannSurface_nontrivial X p
  rcases exists_ne p with ⟨q, hq⟩
  refine
    ⟨((F.toFun p : Complex.UnitDisc) : ℂ), ⟨p, rfl⟩,
      ((F.toFun q : Complex.UnitDisc) : ℂ), ⟨q, rfl⟩, ?_⟩
  intro hpq
  have hp_zero : ((F.toFun p : Complex.UnitDisc) : ℂ) = 0 :=
    (hzero p).mpr rfl
  have hq_zero : ((F.toFun q : Complex.UnitDisc) : ℂ) = 0 := by
    simpa [hp_zero] using hpq.symm
  exact hq ((hzero q).mp hq_zero)

/--
%%handwave
name:
  Tiny closed coordinate disks avoid two prescribed exterior points
statement:
  Given a point \(p\) on a Riemann surface and two points different
  from \(p\), there is a closed coordinate disk containing \(p\) and avoiding
  both prescribed exterior points.
proof:
  Choose a chart at \(p\).  Since the chart target is open, take a small
  Euclidean ball around the coordinate of \(p\).  If either exterior point
  lies in the chart source, shrink the radius below its coordinate distance
  from \(p\); if it is outside the source, it is automatically avoided.
-/
theorem exists_closedCoordinateDisk_mem_point_avoids_two_points
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p x y : X}
    (hxp : x ≠ p) (hyp : y ≠ p) :
    ∃ D : ClosedCoordinateDisk X, p ∈ D.carrier ∧ x ∉ D.carrier ∧ y ∉ D.carrier := by
  classical
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let c : ℂ := e p
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ p
  have hc_target : c ∈ e.target := e.map_source hp_source
  rcases Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hc_target) with
    ⟨R, hRpos, hball_target⟩
  let δx : ℝ := if hxsrc : x ∈ e.source then dist (e x) c else R
  have hδx_pos : 0 < δx := by
    dsimp [δx]
    split_ifs with hxsrc
    · refine dist_pos.mpr ?_
      intro hxchart
      exact hxp (e.injOn hxsrc hp_source hxchart)
    · exact hRpos
  let δy : ℝ := if hysrc : y ∈ e.source then dist (e y) c else R
  have hδy_pos : 0 < δy := by
    dsimp [δy]
    split_ifs with hysrc
    · refine dist_pos.mpr ?_
      intro hychart
      exact hyp (e.injOn hysrc hp_source hychart)
    · exact hRpos
  let r : ℝ := min R (min δx δy) / 2
  have hmin_pos : 0 < min R (min δx δy) :=
    lt_min hRpos (lt_min hδx_pos hδy_pos)
  have hrpos : 0 < r := by
    dsimp [r]
    linarith
  have hrR : r < R := by
    have hmin_le : min R (min δx δy) ≤ R := min_le_left _ _
    dsimp [r]
    linarith
  have hrδx : r < δx := by
    have hmin_le : min R (min δx δy) ≤ δx :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    dsimp [r]
    linarith
  have hrδy : r < δy := by
    have hmin_le : min R (min δx δy) ≤ δy :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    dsimp [r]
    linarith
  let D : ClosedCoordinateDisk X :=
    closedCoordinateDiskOfChartBall e he c hrpos hrR hball_target
  refine ⟨D, ?_, ?_, ?_⟩
  · change p ∈ e.source ∩ e ⁻¹' Metric.closedBall c r
    refine ⟨hp_source, ?_⟩
    simpa [c, Metric.mem_closedBall] using hrpos.le
  · intro hxD
    change x ∈ e.source ∩ e ⁻¹' Metric.closedBall c r at hxD
    have hxsrc : x ∈ e.source := hxD.1
    have hxle : dist (e x) c ≤ r := by
      simpa [Metric.mem_closedBall] using hxD.2
    have hδx_eq : δx = dist (e x) c := by
      simp [δx, hxsrc]
    linarith
  · intro hyD
    change y ∈ e.source ∩ e ⁻¹' Metric.closedBall c r at hyD
    have hysrc : y ∈ e.source := hyD.1
    have hyle : dist (e y) c ≤ r := by
      simpa [Metric.mem_closedBall] using hyD.2
    have hδy_eq : δy = dist (e y) c := by
      simp [δy, hysrc]
    linarith

/--
%%handwave
name:
  Punctured Riemann surfaces are path joined
statement:
  Any two points of a Riemann surface different from \(p\) can be
  joined by a path that avoids \(p\).
proof:
  Join the two points by an arbitrary path.  Choose a closed coordinate disk
  around \(p\) avoiding the endpoints, and replace every portion of the path
  that enters the disk by an arc on a surrounding coordinate circle.
-/
theorem punctured_riemannSurface_joinedIn
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p x y : X}
    (hx : x ≠ p) (hy : y ≠ p) :
    JoinedIn {z : X | z ≠ p} x y := by
  rcases exists_closedCoordinateDisk_mem_point_avoids_two_points X hx hy with
    ⟨D, hpD, hxD, hyD⟩
  let γ : Path x y := (riemannSurface_joined x y).somePath
  rcases path_can_be_pushed_off_closedCoordinateDisk D γ hxD hyD with ⟨η, hη⟩
  refine ⟨η, ?_⟩
  intro t hηp
  exact hη t (by simpa [hηp] using hpD)

/--
%%handwave
name:
  Punctured Riemann surfaces are preconnected
statement:
  Removing one point from a Riemann surface leaves a preconnected
  punctured surface.
proof:
  The punctured path-joining theorem joins any two punctured points by a path
  that stays in the punctured surface; path connectedness implies
  preconnectedness.
-/
theorem punctured_riemannSurface_preconnected
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) :
    IsPreconnected {x : X | x ≠ p} := by
  refine isPreconnected_of_forall_joinedIn ?_
  intro x hx y hy
  exact punctured_riemannSurface_joinedIn X hx hy

/--
%%handwave
name:
  Punctured neighborhoods of a point are nontrivial
statement:
  On a Riemann surface, the punctured-neighborhood filter at a point
  is nontrivial.
proof:
  In a complex coordinate around the point, punctured neighborhoods correspond
  to punctured neighborhoods of a point in \(\mathbb C\), and these are
  nonempty arbitrarily close to the point.
-/
theorem punctured_nhds_neBot_riemannSurface
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) :
    Filter.NeBot (𝓝[≠] p) := by
  haveI : Nontrivial X := riemannSurface_nontrivial X p
  infer_instance

/--
%%handwave
name:
  Nonnegative harmonic functions with pole blow-up are positive
statement:
  Let \(u\) be a nonnegative harmonic function on the punctured surface
  \(X\setminus\{p\}\), and suppose \(u\to+\infty\) at \(p\).  Then \(u\) is
  strictly positive on \(X\setminus\{p\}\).
proof:
  If \(u\) vanished at a punctured point, then nonnegativity would make that
  point a local minimum.  The strong minimum principle for harmonic functions
  would make \(u\) vanish on the punctured component.  A connected Riemann
  surface remains connected after removing one point, so this would contradict
  the blow-up at the pole.
-/
theorem nonnegative_harmonicOn_punctured_tendsto_atTop_positive
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) {u : X → ℝ}
    (hnonneg : ∀ x : X, 0 ≤ u x)
    (hharm : IsHarmonicOnSurface {x : X | x ≠ p} u)
    (hblow : Filter.Tendsto u (𝓝[≠] p) Filter.atTop) :
    ∀ x : X, x ≠ p → 0 < u x := by
  intro x hxp
  by_contra hnot_pos
  have hux_nonpos : u x ≤ 0 := le_of_not_gt hnot_pos
  have hux_zero : u x = 0 := le_antisymm hux_nonpos (hnonneg x)
  let U : Set X := {y : X | y ≠ p}
  have hU_open : IsOpen U := by
    simpa [U] using (isOpen_ne (x := p) : IsOpen {y : X | y ≠ p})
  have hU_preconnected : IsPreconnected U := by
    simpa [U] using punctured_riemannSurface_preconnected X p
  have hxU : x ∈ U := hxp
  have hmax_neg : IsMaxOn (fun y : X ↦ -u y) U x := by
    intro y _hy
    have hy_nonneg : 0 ≤ u y := hnonneg y
    simpa [hux_zero] using neg_nonpos.mpr hy_nonneg
  have hneg_const :
      Set.EqOn (fun y : X ↦ -u y) (fun _ ↦ -u x) U :=
    harmonicOnSurface_eqOn_of_isPreconnected_of_isMaxOn
      hU_open hU_preconnected (harmonicOnSurface_neg hharm) hxU hmax_neg
  have hzero_on_U : Set.EqOn u (fun _ : X ↦ 0) U := by
    intro y hy
    have hneg : -u y = -u x := hneg_const hy
    exact (neg_inj.mp hneg).trans hux_zero
  have hevent_zero : u =ᶠ[𝓝[≠] p] fun _ : X ↦ 0 := by
    filter_upwards [(self_mem_nhdsWithin : U ∈ 𝓝[≠] p)] with y hy
    exact hzero_on_U hy
  have htendsto_zero : Filter.Tendsto u (𝓝[≠] p) (𝓝 0) :=
    hevent_zero.tendsto
  haveI : Filter.NeBot (𝓝[≠] p) :=
    punctured_nhds_neBot_riemannSurface X p
  exact (not_tendsto_nhds_of_tendsto_atTop hblow (0 : ℝ)) htendsto_zero

/--
%%handwave
name:
  Punctured nonnegative harmonic functions with pole blow-up are positive
statement:
  Let \(u\) be harmonic and nonnegative on the punctured surface
  \(X\setminus\{p\}\), and suppose \(u\to+\infty\) at \(p\).  Then \(u\) is
  strictly positive on \(X\setminus\{p\}\).
proof:
  If \(u\) vanished at a punctured point, then nonnegativity on the punctured
  surface would make that point a local minimum.  The strong minimum
  principle for harmonic functions would force \(u\) to vanish on the
  punctured surface, contradicting the blow-up at the pole.
-/
theorem nonnegative_on_punctured_harmonicOn_punctured_tendsto_atTop_positive
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) {u : X → ℝ}
    (hnonneg : ∀ x : X, x ≠ p → 0 ≤ u x)
    (hharm : IsHarmonicOnSurface {x : X | x ≠ p} u)
    (hblow : Filter.Tendsto u (𝓝[≠] p) Filter.atTop) :
    ∀ x : X, x ≠ p → 0 < u x := by
  intro x hxp
  by_contra hnot_pos
  have hux_nonpos : u x ≤ 0 := le_of_not_gt hnot_pos
  have hux_zero : u x = 0 := le_antisymm hux_nonpos (hnonneg x hxp)
  let U : Set X := {y : X | y ≠ p}
  have hU_open : IsOpen U := by
    simpa [U] using (isOpen_ne (x := p) : IsOpen {y : X | y ≠ p})
  have hU_preconnected : IsPreconnected U := by
    simpa [U] using punctured_riemannSurface_preconnected X p
  have hxU : x ∈ U := hxp
  have hmax_neg : IsMaxOn (fun y : X ↦ -u y) U x := by
    intro y hy
    have hy_nonneg : 0 ≤ u y := hnonneg y hy
    simpa [hux_zero] using neg_nonpos.mpr hy_nonneg
  have hneg_const :
      Set.EqOn (fun y : X ↦ -u y) (fun _ ↦ -u x) U :=
    harmonicOnSurface_eqOn_of_isPreconnected_of_isMaxOn
      hU_open hU_preconnected (harmonicOnSurface_neg hharm) hxU hmax_neg
  have hzero_on_U : Set.EqOn u (fun _ : X ↦ 0) U := by
    intro y hy
    have hneg : -u y = -u x := hneg_const hy
    exact (neg_inj.mp hneg).trans hux_zero
  have hevent_zero : u =ᶠ[𝓝[≠] p] fun _ : X ↦ 0 := by
    filter_upwards [(self_mem_nhdsWithin : U ∈ 𝓝[≠] p)] with y hy
    exact hzero_on_U hy
  have htendsto_zero : Filter.Tendsto u (𝓝[≠] p) (𝓝 0) :=
    hevent_zero.tendsto
  haveI : Filter.NeBot (𝓝[≠] p) :=
    punctured_nhds_neBot_riemannSurface X p
  exact (not_tendsto_nhds_of_tendsto_atTop hblow (0 : ℝ)) htendsto_zero

/--
%%handwave
name:
  Pointed coordinate annulus
statement:
  The pointed coordinate annulus \(\rho<|z-z(p)|<R\) is the part of the
  coordinate source where the coordinate distance from the pole lies between
  \(\rho\) and \(R\).
-/
def pointedCoordinateAnnulus
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (χ : PointedSurfaceCoordinate X p) (ρ R : ℝ) : Set X :=
  χ.chart.source ∩
    {x : X | ρ < ‖χ.chart x - χ.chart p‖ ∧
      ‖χ.chart x - χ.chart p‖ < R}

/--
%%handwave
name:
  Logarithmic annular patch with constant exterior
statement:
  This patch is the logarithmic model on an inner coordinate ball, a harmonic
  support on the surrounding annulus, and a positive constant outside a larger
  coordinate ball.
-/
noncomputable def pointedCoordinateLogarithmicConstantAnnularPatch
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (χ : PointedSurfaceCoordinate X p) (r R : ℝ)
    (h : X → ℝ) (A B : ℝ) : X → ℝ :=
  by
    classical
    exact fun x : X ↦
      if x = p then 0
      else if x ∈ χ.chart.source ∧ ‖χ.chart x - χ.chart p‖ < r then
        -Real.log ‖χ.chart x - χ.chart p‖ + A
      else if x ∈ χ.chart.source ∧ ‖χ.chart x - χ.chart p‖ < R then
        h x
      else B

/--
%%handwave
name:
  The constant-exterior annular patch is nonnegative
statement:
  If the inner logarithmic model, the annular support, and the exterior
  constant are nonnegative on their respective pieces, then the whole
  constant-exterior annular patch is nonnegative.
proof:
  Split according to whether the point is the pole, lies in the inner
  coordinate ball, lies in the surrounding coordinate ball, or lies outside.
  The four values are respectively \(0\), the logarithmic model, the annular
  support, and the exterior constant, so the corresponding hypothesis applies
  in each case.
-/
theorem pointedCoordinateLogarithmicConstantAnnularPatch_nonnegative
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (χ : PointedSurfaceCoordinate X p) {r R A B : ℝ}
    {h : X → ℝ}
    (hlog_nonneg :
      ∀ x ∈ χ.chart.source,
        ‖χ.chart x - χ.chart p‖ < r →
          x ≠ p →
            0 ≤ -Real.log ‖χ.chart x - χ.chart p‖ + A)
    (hbridge_nonneg :
      ∀ x ∈ χ.chart.source,
        r ≤ ‖χ.chart x - χ.chart p‖ →
          ‖χ.chart x - χ.chart p‖ < R →
            0 ≤ h x)
    (hB_nonneg : 0 ≤ B) :
    ∀ x : X,
      0 ≤ pointedCoordinateLogarithmicConstantAnnularPatch X χ r R h A B x := by
  intro x
  by_cases hxp : x = p
  · simp [pointedCoordinateLogarithmicConstantAnnularPatch, hxp]
  · by_cases hinner : x ∈ χ.chart.source ∧ ‖χ.chart x - χ.chart p‖ < r
    · simp [pointedCoordinateLogarithmicConstantAnnularPatch, hxp, hinner,
        hlog_nonneg x hinner.1 hinner.2 hxp]
    · by_cases houter : x ∈ χ.chart.source ∧ ‖χ.chart x - χ.chart p‖ < R
      · have hr_le : r ≤ ‖χ.chart x - χ.chart p‖ := by
          exact le_of_not_gt (fun hlt ↦ hinner ⟨houter.1, hlt⟩)
        have hnot_lt : ¬ ‖χ.chart x - χ.chart p‖ < r := by
          intro hlt
          exact hinner ⟨houter.1, hlt⟩
        simp [pointedCoordinateLogarithmicConstantAnnularPatch, hxp, houter,
          hnot_lt, hbridge_nonneg x houter.1 hr_le houter.2]
      · simp [pointedCoordinateLogarithmicConstantAnnularPatch, hxp, hinner,
          houter, hB_nonneg]

/--
%%handwave
name:
  The constant-exterior annular patch has the exact local model
statement:
  On the punctured inner coordinate ball, the constant-exterior annular patch
  agrees with \(-\log |z-z(p)|\) plus the chosen constant.
proof:
  At a non-pole point of the inner coordinate ball, the first nontrivial branch
  of the piecewise definition is selected, and that branch is exactly the
  stated logarithmic model.
-/
theorem pointedCoordinateLogarithmicConstantAnnularPatch_eq_model
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (χ : PointedSurfaceCoordinate X p) {r R A B : ℝ}
    {h : X → ℝ} :
    ∀ x ∈ χ.chart.source,
      ‖χ.chart x - χ.chart p‖ < r →
        x ≠ p →
          pointedCoordinateLogarithmicConstantAnnularPatch X χ r R h A B x =
            -Real.log ‖χ.chart x - χ.chart p‖ + A := by
  intro x hxsource hxr hxp
  have hinner : x ∈ χ.chart.source ∧ ‖χ.chart x - χ.chart p‖ < r :=
    ⟨hxsource, hxr⟩
  simp [pointedCoordinateLogarithmicConstantAnnularPatch, hxp, hinner]



/--
%%handwave
name:
  Pointed coordinate inner balls are eventually reached from any pointed coordinate
statement:
  If \(r>0\), then every point sufficiently close to \(p\) in any pointed
  coordinate also lies in the \(r\)-ball of any other pointed coordinate at
  \(p\).
proof:
  The target coordinate map is continuous at \(p\), and its coordinate
  distance from \(p\) is zero at \(p\).
-/
theorem pointedCoordinate_eventually_mem_inner_ball
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (χ ψ : PointedSurfaceCoordinate X p) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ x in 𝓝[ψ.chart.source ∩ {x : X | x ≠ p}] p,
      x ∈ χ.chart.source ∧ ‖χ.chart x - χ.chart p‖ < r := by
  have hsource : χ.chart.source ∈ 𝓝 p :=
    χ.chart.open_source.mem_nhds χ.base_mem_source
  have hcont :
      ContinuousAt (fun x : X ↦ ‖χ.chart x - χ.chart p‖) p :=
    (χ.chart.continuousAt χ.base_mem_source).sub continuousAt_const |>.norm
  have hball : {x : X | ‖χ.chart x - χ.chart p‖ < r} ∈ 𝓝 p := by
    have hp : ‖χ.chart p - χ.chart p‖ < r := by
      simpa using hr
    exact hcont.preimage_mem_nhds (Iio_mem_nhds hp)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hsource,
    mem_nhdsWithin_of_mem_nhds hball] with x hxsource hxball
  exact ⟨hxsource, hxball⟩

/--
%%handwave
name:
  Pointed-coordinate logarithmic distance differences are locally harmonic
statement:
  For two pointed coordinates at the same pole, the difference of their
  logarithmic coordinate distances has a harmonic extension across the pole on
  a small neighborhood.
proof:
  Write the transition as \(F\) in the second coordinate.  Since the transition
  derivative is nonzero at the pole, the divided slope
  \((F(z)-F(z_0))/(z-z_0)\), extended by \(F'(z_0)\), is analytic and nonzero
  near \(z_0\).  The logarithm of its norm is harmonic and equals the
  difference of the two coordinate logarithmic distances off the pole.
-/
theorem pointedCoordinate_log_distance_difference_local_harmonic_extension
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ ψ : PointedSurfaceCoordinate X p) :
    ∃ U : Set X, ∃ H : X → ℝ,
      IsOpen U ∧ p ∈ U ∧ U ⊆ χ.chart.source ∧
        IsHarmonicOnSurface U H ∧
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            Real.log ‖χ.chart x - χ.chart p‖ -
              Real.log ‖ψ.chart x - ψ.chart p‖ = H x := by
  let F : ℂ → ℂ := fun z ↦ χ.chart (ψ.chart.symm z)
  let z₀ : ℂ := ψ.chart p
  let q : ℂ → ℂ := dslope F z₀
  have hz₀_target : z₀ ∈ ψ.chart.target := by
    dsimp [z₀]
    exact ψ.chart.map_source ψ.base_mem_source
  have hz₀_sourceχ : ψ.chart.symm z₀ ∈ χ.chart.source := by
    dsimp [z₀]
    simpa [ψ.chart.left_inv ψ.base_mem_source] using χ.base_mem_source
  have hF_an : AnalyticAt ℂ F z₀ := by
    dsimp [F, z₀]
    exact chartTransition_analyticAt ψ.chart ψ.chart_mem_atlas
      χ.chart χ.chart_mem_atlas hz₀_target hz₀_sourceχ
  have hq_an : AnalyticAt ℂ q z₀ := by
    rcases hF_an with ⟨pF, hpF⟩
    exact (HasFPowerSeriesAt.has_fpower_series_dslope_fslope hpF).analyticAt
  have hq_z₀_ne : q z₀ ≠ 0 := by
    dsimp [q]
    simpa [F, z₀] using pointedCoordinate_transition_deriv_ne_zero X χ ψ
  rcases hq_an.exists_ball_analyticOnNhd with
    ⟨r_an, hr_an_pos, hq_an_ball⟩
  have hq_ne_nhds : {z : ℂ | q z ≠ 0} ∈ 𝓝 z₀ :=
    hq_an.differentiableAt.continuousAt.preimage_mem_nhds
      (isOpen_ne.mem_nhds hq_z₀_ne)
  rcases Metric.mem_nhds_iff.mp hq_ne_nhds with
    ⟨r_ne, hr_ne_pos, hq_ne_ball⟩
  let δ : ℝ := min r_an r_ne
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min hr_an_pos hr_ne_pos
  have hδ_le_an : δ ≤ r_an := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_le_ne : δ ≤ r_ne := by
    dsimp [δ]
    exact min_le_right _ _
  let U : Set X :=
    χ.chart.source ∩ (ψ.chart.source ∩ ψ.chart ⁻¹' Metric.ball z₀ δ)
  let H : X → ℝ := fun x ↦ Real.log ‖q (ψ.chart x)‖
  have hU_open : IsOpen U := by
    dsimp [U]
    exact χ.chart.open_source.inter
      (ψ.chart.isOpen_inter_preimage Metric.isOpen_ball)
  have hpU : p ∈ U := by
    refine ⟨χ.base_mem_source, ψ.base_mem_source, ?_⟩
    simp [z₀, hδ_pos]
  have hUχ : U ⊆ χ.chart.source := fun _ hx ↦ hx.1
  have hq_an_on :
      ∀ z ∈ Metric.ball z₀ δ, AnalyticAt ℂ q z := by
    intro z hz
    exact hq_an_ball z (Metric.ball_subset_ball hδ_le_an hz)
  have hq_ne_on :
      ∀ z ∈ Metric.ball z₀ δ, q z ≠ 0 := by
    intro z hz
    exact hq_ne_ball (Metric.ball_subset_ball hδ_le_ne hz)
  have hlog_harm :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦ Real.log ‖q z‖) (Metric.ball z₀ δ) := by
    intro z hz
    exact (hq_an_on z hz).harmonicAt_log_norm (hq_ne_on z hz)
  have hH_harm : IsHarmonicOnSurface U H := by
    intro e he z hz
    have hz_target : z ∈ e.target := hz.1
    have hxU : e.symm z ∈ U := hz.2
    have hxψ_source : e.symm z ∈ ψ.chart.source := hxU.2.1
    have hxball : ψ.chart (e.symm z) ∈ Metric.ball z₀ δ := hxU.2.2
    have h_at :
        InnerProductSpace.HarmonicAt
          (fun z : ℂ ↦ Real.log ‖q z‖) (ψ.chart (e.symm z)) :=
      hlog_harm (ψ.chart (e.symm z)) hxball
    have htransition :
        AnalyticAt ℂ (fun w : ℂ ↦ ψ.chart (e.symm w)) z :=
      chartTransition_analyticAt e he ψ.chart ψ.chart_mem_atlas
        hz_target hxψ_source
    simpa [H, Function.comp_def] using
      harmonicAt_comp_analyticAt h_at htransition
  have heq_on_U :
      ∀ x ∈ U, x ≠ p →
        Real.log ‖χ.chart x - χ.chart p‖ -
          Real.log ‖ψ.chart x - ψ.chart p‖ = H x := by
    intro x hxU hxne
    have hxψ_source : x ∈ ψ.chart.source := hxU.2.1
    have hz_ne : ψ.chart x ≠ z₀ := by
      intro hz
      exact hxne (ψ.chart.injOn hxψ_source ψ.base_mem_source (by
        simpa [z₀] using hz))
    have hψ_pos : 0 < ‖ψ.chart x - ψ.chart p‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (by simpa [z₀] using hz_ne))
    have hq_ne : q (ψ.chart x) ≠ 0 :=
      hq_ne_on (ψ.chart x) hxU.2.2
    have hq_pos : 0 < ‖q (ψ.chart x)‖ :=
      norm_pos_iff.mpr hq_ne
    have hdiff :
        χ.chart x - χ.chart p =
          (ψ.chart x - ψ.chart p) * q (ψ.chart x) := by
      have h := (sub_smul_dslope F z₀ (ψ.chart x)).symm
      simpa [q, F, z₀, smul_eq_mul, ψ.chart.left_inv hxψ_source,
        ψ.chart.left_inv ψ.base_mem_source] using h
    calc
      Real.log ‖χ.chart x - χ.chart p‖ -
          Real.log ‖ψ.chart x - ψ.chart p‖
          = Real.log (‖ψ.chart x - ψ.chart p‖ * ‖q (ψ.chart x)‖) -
              Real.log ‖ψ.chart x - ψ.chart p‖ := by
              rw [hdiff, norm_mul]
      _ = Real.log ‖q (ψ.chart x)‖ := by
          rw [Real.log_mul hψ_pos.ne' hq_pos.ne']
          ring
      _ = H x := rfl
  refine ⟨U, H, hU_open, hpU, hUχ, hH_harm, ?_⟩
  filter_upwards
    [mem_nhdsWithin_of_mem_nhds (hU_open.mem_nhds hpU),
      self_mem_nhdsWithin]
    with x hxU hxχpunct
  exact heq_on_U x hxU hxχpunct.2

/--
%%handwave
name:
  Pointed coordinate distances are locally comparable
statement:
  For two pointed coordinates at the same point, the distance to the marked
  point in one coordinate is bounded above by a fixed multiple of the distance
  in the other coordinate near the marked point.
proof:
  The transition map from the second coordinate to the first is holomorphic
  and has nonzero derivative at the marked point.  The inverse-function
  estimate therefore bounds the norm of the transition map by a fixed
  multiple of the norm of its argument on a sufficiently small punctured
  neighborhood.
-/
theorem pointedCoordinate_distances_eventually_le_mul
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ ψ : PointedSurfaceCoordinate X p) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ᶠ x in 𝓝[ψ.chart.source ∩ {x : X | x ≠ p}] p,
        x ∈ χ.chart.source ∧
          ‖χ.chart x - χ.chart p‖ ≤
            C * ‖ψ.chart x - ψ.chart p‖ := by
  let F : ℂ → ℂ := fun z ↦ χ.chart (ψ.chart.symm z)
  let z₀ : ℂ := ψ.chart p
  have hz₀_target : z₀ ∈ ψ.chart.target := by
    dsimp [z₀]
    exact ψ.chart.map_source ψ.base_mem_source
  have hz₀_source : ψ.chart.symm z₀ ∈ χ.chart.source := by
    dsimp [z₀]
    simpa [ψ.chart.left_inv ψ.base_mem_source] using χ.base_mem_source
  have hF_an : AnalyticAt ℂ F z₀ := by
    dsimp [F, z₀]
    exact chartTransition_analyticAt ψ.chart ψ.chart_mem_atlas
      χ.chart χ.chart_mem_atlas hz₀_target hz₀_source
  have hbig :
      (fun z : ℂ ↦ F z - F z₀) =O[𝓝 z₀] (fun z : ℂ ↦ z - z₀) :=
    hF_an.differentiableAt.isBigO_sub
  rcases hbig.exists_pos with ⟨C₀, hC₀_pos, hC₀⟩
  refine ⟨max 1 C₀, le_max_left 1 C₀, ?_⟩
  have hψ_tendsto :
      Filter.Tendsto ψ.chart
        (𝓝[ψ.chart.source ∩ {x : X | x ≠ p}] p) (𝓝 z₀) := by
    dsimp [z₀]
    exact (ψ.chart.continuousAt ψ.base_mem_source).mono_left nhdsWithin_le_nhds
  have hbound :
      ∀ᶠ x in 𝓝[ψ.chart.source ∩ {x : X | x ≠ p}] p,
        ‖F (ψ.chart x) - F z₀‖ ≤ C₀ * ‖ψ.chart x - z₀‖ :=
    hψ_tendsto hC₀.bound
  have hχsource_event :
      ∀ᶠ x in 𝓝[ψ.chart.source ∩ {x : X | x ≠ p}] p,
        x ∈ χ.chart.source ∧ ‖χ.chart x - χ.chart p‖ < (1 : ℝ) :=
    pointedCoordinate_eventually_mem_inner_ball X χ ψ zero_lt_one
  filter_upwards [hbound, hχsource_event, self_mem_nhdsWithin] with
    x hboundx hxχ hxψ
  refine ⟨hxχ.1, ?_⟩
  have hF_eq : F (ψ.chart x) = χ.chart x := by
    dsimp [F]
    rw [ψ.chart.left_inv hxψ.1]
  have hF₀_eq : F z₀ = χ.chart p := by
    dsimp [F, z₀]
    rw [ψ.chart.left_inv ψ.base_mem_source]
  calc
    ‖χ.chart x - χ.chart p‖ = ‖F (ψ.chart x) - F z₀‖ := by
      rw [hF_eq, hF₀_eq]
    _ ≤ C₀ * ‖ψ.chart x - ψ.chart p‖ := by
      simpa [z₀] using hboundx
    _ ≤ max 1 C₀ * ‖ψ.chart x - ψ.chart p‖ :=
      mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) C₀) (norm_nonneg _)

/--
%%handwave
name:
  The coordinate logarithm tends to negative infinity at the puncture
statement:
  In any pointed complex coordinate, \(\log |z-z(p)|\) tends to \(-\infty\)
  when \(z\) tends to \(p\) through the punctured coordinate domain.
proof:
  The coordinate map is a local homeomorphism at \(p\), so
  \(\chi(x)-\chi(p)\) tends to \(0\) through nonzero complex numbers.  The norm
  tends to \(0\) through positive real numbers, and the real logarithm tends to
  \(-\infty\) at \(0^+\).
-/
theorem pointedCoordinate_log_norm_tendsto_atBot
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ : PointedSurfaceCoordinate X p) :
    Filter.Tendsto
      (fun x : X => Real.log ‖χ.chart x - χ.chart p‖)
      (𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p)
      Filter.atBot := by
  let F : Filter X := 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p
  have hchart : Filter.Tendsto χ.chart F (𝓝 (χ.chart p)) := by
    exact (χ.chart.continuousAt χ.base_mem_source).mono_left (by
      simp [F, nhdsWithin_le_nhds])
  have hconst :
      Filter.Tendsto (fun _ : X => χ.chart p) F (𝓝 (χ.chart p)) :=
    tendsto_const_nhds
  have hsub_nhds :
      Filter.Tendsto (fun x : X => χ.chart x - χ.chart p) F (𝓝 0) := by
    simpa using hchart.sub hconst
  have hsub_event :
      ∀ᶠ x in F, χ.chart x - χ.chart p ∈ ({0}ᶜ : Set ℂ) := by
    refine eventually_nhdsWithin_of_forall ?_
    intro x hx
    rw [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero]
    intro hEq
    exact hx.2 (χ.chart.injOn hx.1 χ.base_mem_source hEq)
  have hsub :
      Filter.Tendsto (fun x : X => χ.chart x - χ.chart p) F (𝓝[≠] (0 : ℂ)) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨hsub_nhds, hsub_event⟩
  have hnorm :
      Filter.Tendsto (fun x : X => ‖χ.chart x - χ.chart p‖) F (𝓝[>] (0 : ℝ)) := by
    simpa [Function.comp_def] using (tendsto_norm_nhdsNE_zero.comp hsub)
  exact Real.tendsto_log_nhdsGT_zero.comp hnorm

/--
%%handwave
name:
  Logarithmic pole asymptotics imply pole blow-up
statement:
  A function whose sum with \(\log |z-z(p)|\) is harmonically removable at
  \(p\) tends to \(+\infty\) along the punctured surface.
proof:
  In a pointed coordinate, the harmonic remainder is finite and continuous at
  the pole, while \(\log |z-z(p)|\to-\infty\).  Therefore the original function,
  equal to the harmonic remainder minus the logarithm, tends to \(+\infty\).
-/
theorem logarithmic_singularity_tendsto_atTop
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) {u : X → ℝ}
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ h : X → ℝ,
          IsHarmonicOnSurface χ.chart.source h ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              u x + Real.log ‖χ.chart x - χ.chart p‖ = h x) :
    Filter.Tendsto u (𝓝[≠] p) Filter.atTop := by
  let χ : PointedSurfaceCoordinate X p :=
    { chart := chartAt ℂ p
      chart_mem_atlas := chart_mem_atlas ℂ p
      base_mem_source := mem_chart_source ℂ p }
  let F : Filter X := 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p
  have hF_eq : F = 𝓝[≠] p := by
    have hsource_mem : χ.chart.source ∈ 𝓝[{x : X | x ≠ p}] p :=
      mem_nhdsWithin_of_mem_nhds
        (χ.chart.open_source.mem_nhds χ.base_mem_source)
    simpa [F] using nhdsWithin_inter_of_mem hsource_mem
  rcases hlog χ with ⟨h, hharm, hevent⟩
  have hh_cont :
      Filter.Tendsto h F (𝓝 (h p)) := by
    have hcont_on : ContinuousOn h χ.chart.source :=
      harmonicOnSurface_continuousOn χ.chart.open_source hharm
    have hwithin :
        Filter.Tendsto h (𝓝[χ.chart.source] p) (𝓝 (h p)) :=
      hcont_on.continuousWithinAt χ.base_mem_source
    exact hwithin.mono_left (by
      simpa [F] using
        (nhdsWithin_mono p (Set.inter_subset_left :
          χ.chart.source ∩ {x : X | x ≠ p} ⊆ χ.chart.source)))
  have hlog_bot :
      Filter.Tendsto
        (fun x : X => Real.log ‖χ.chart x - χ.chart p‖)
        F Filter.atBot := by
    simpa [F] using pointedCoordinate_log_norm_tendsto_atBot X χ
  have hneglog_top :
      Filter.Tendsto
        (fun x : X => -Real.log ‖χ.chart x - χ.chart p‖)
        F Filter.atTop :=
    Filter.tendsto_neg_atBot_atTop.comp hlog_bot
  have hsub_top :
      Filter.Tendsto
        (fun x : X => h x + -Real.log ‖χ.chart x - χ.chart p‖)
        F Filter.atTop :=
    hh_cont.add_atTop hneglog_top
  have hu_event :
      (fun x : X => h x + -Real.log ‖χ.chart x - χ.chart p‖) =ᶠ[F] u := by
    filter_upwards [by simpa [F] using hevent] with x hx
    linarith
  have hu_tendsto_F : Filter.Tendsto u F Filter.atTop :=
    Filter.Tendsto.congr' hu_event hsub_top
  simpa [hF_eq] using hu_tendsto_F

/--
%%handwave
name:
  Logarithmic zero asymptotics imply pole decay
statement:
  A function whose difference with \(\log |z-z(p)|\) is harmonically removable
  at \(p\) tends to \(-\infty\) along the punctured surface.
proof:
  In a pointed coordinate, the harmonic remainder is finite and continuous at
  the pole, while \(\log |z-z(p)|\to-\infty\).  Therefore the original function,
  equal to the harmonic remainder plus the logarithm, tends to \(-\infty\).
-/
theorem logarithmic_zero_tendsto_atBot
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) {u : X → ℝ}
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ h : X → ℝ,
          IsHarmonicOnSurface χ.chart.source h ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              u x - Real.log ‖χ.chart x - χ.chart p‖ = h x) :
    Filter.Tendsto u (𝓝[≠] p) Filter.atBot := by
  let χ : PointedSurfaceCoordinate X p :=
    { chart := chartAt ℂ p
      chart_mem_atlas := chart_mem_atlas ℂ p
      base_mem_source := mem_chart_source ℂ p }
  let F : Filter X := 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p
  have hF_eq : F = 𝓝[≠] p := by
    have hsource_mem : χ.chart.source ∈ 𝓝[{x : X | x ≠ p}] p :=
      mem_nhdsWithin_of_mem_nhds
        (χ.chart.open_source.mem_nhds χ.base_mem_source)
    simpa [F] using nhdsWithin_inter_of_mem hsource_mem
  rcases hlog χ with ⟨h, hharm, hevent⟩
  have hh_cont :
      Filter.Tendsto h F (𝓝 (h p)) := by
    have hcont_on : ContinuousOn h χ.chart.source :=
      harmonicOnSurface_continuousOn χ.chart.open_source hharm
    have hwithin :
        Filter.Tendsto h (𝓝[χ.chart.source] p) (𝓝 (h p)) :=
      hcont_on.continuousWithinAt χ.base_mem_source
    exact hwithin.mono_left (by
      simpa [F] using
        (nhdsWithin_mono p (Set.inter_subset_left :
          χ.chart.source ∩ {x : X | x ≠ p} ⊆ χ.chart.source)))
  have hlog_bot :
      Filter.Tendsto
        (fun x : X => Real.log ‖χ.chart x - χ.chart p‖)
        F Filter.atBot := by
    simpa [F] using pointedCoordinate_log_norm_tendsto_atBot X χ
  have hsum_bot :
      Filter.Tendsto
        (fun x : X => h x + Real.log ‖χ.chart x - χ.chart p‖)
        F Filter.atBot :=
    hh_cont.add_atBot hlog_bot
  have hu_event :
      (fun x : X => h x + Real.log ‖χ.chart x - χ.chart p‖) =ᶠ[F] u := by
    filter_upwards [by simpa [F] using hevent] with x hx
    linarith
  have hu_tendsto_F : Filter.Tendsto u F Filter.atBot :=
    Filter.Tendsto.congr' hu_event hsum_bot
  simpa [hF_eq] using hu_tendsto_F

/--
%%handwave
name:
  Compact subsets of the disk stay away from the boundary
statement:
  Every compact subset of the unit disk is contained in a closed subdisk of
  some radius \(r<1\).
proof:
  The norm is continuous and reaches a maximum on a nonempty compact subset.
  The maximum is still strictly less than one because all points lie in the
  open unit disk.  Replace the maximum by the midpoint between it and \(1\).
-/
theorem compact_unitDisc_subset_closed_norm_lt_one
    {K : Set Complex.UnitDisc} (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ z ∈ K, ‖((z : Complex.UnitDisc) : ℂ)‖ ≤ r := by
  classical
  by_cases hne : K.Nonempty
  · have hcont :
        ContinuousOn (fun z : Complex.UnitDisc ↦ ‖((z : Complex.UnitDisc) : ℂ)‖) K :=
      Complex.UnitDisc.continuous_coe.norm.continuousOn
    rcases hK.exists_isMaxOn hne hcont with ⟨z₀, hz₀K, hz₀max⟩
    let m : ℝ := ‖((z₀ : Complex.UnitDisc) : ℂ)‖
    have hm_nonneg : 0 ≤ m := norm_nonneg _
    have hm_lt_one : m < 1 := Complex.UnitDisc.norm_lt_one z₀
    refine ⟨(m + 1) / 2, ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · intro z hzK
      have hz_le_m : ‖((z : Complex.UnitDisc) : ℂ)‖ ≤ m := by
        simpa [m] using hz₀max hzK
      nlinarith
  · refine ⟨(1 : ℝ) / 2, by norm_num, by norm_num, ?_⟩
    intro z hzK
    exact (hne ⟨z, hzK⟩).elim

/--
%%handwave
name:
  Green function with one pole
statement:
  A Green function with pole \(p\) is a positive harmonic function on the
  punctured surface, with the standard logarithmic pole at \(p\), vanishing at
  infinity, and compact positive superlevel sets after adjoining the pole.
-/
structure GreenFunctionWithPole (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (p : X) where
  /-- The Green function, represented as an ambient real-valued function. -/
  toFun : X → ℝ
  /-- The Green function is positive away from the pole. -/
  positive_away_pole : ∀ x : X, x ≠ p → 0 < toFun x
  /-- The Green function is harmonic on the punctured surface. -/
  harmonic_away_pole : IsHarmonicOnSurface {x : X | x ≠ p} toFun
  /-- The Green function diverges to \(+\infty\) at the pole. -/
  tends_to_infinity_at_pole :
    Filter.Tendsto toFun (𝓝[≠] p) Filter.atTop
  /-- In every coordinate at the pole, the logarithmic singularity is removable. -/
  logarithmic_singularity :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ h : X → ℝ,
        IsHarmonicOnSurface χ.chart.source h ∧
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            toFun x + Real.log ‖χ.chart x - χ.chart p‖ = h x
  /-- The Green function tends to zero along the ends of the surface. -/
  tends_to_zero_at_infinity :
    Filter.Tendsto toFun (Filter.cocompact X) (𝓝 0)
  /--
  Positive superlevel sets of the Green function are compact after adjoining
  the pole.  The pole is adjoined explicitly because `toFun` is represented as
  an ordinary real-valued function at `p`, while the mathematical limiting
  value there is `+∞`.
  -/
  compact_positive_superlevel :
    ∀ a : ℝ, 0 < a → IsCompact ({p} ∪ {x : X | a ≤ toFun x})

/--
%%handwave
name:
  Potential-theoretically parabolic surface
statement:
  A Riemann surface is potential-theoretically parabolic when it has no Green
  function with any pole.
-/
def IsPotentialTheoreticallyParabolic
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ p : X, ¬ Nonempty (GreenFunctionWithPole X p)



/--
%%handwave
name:
  Evans potential
statement:
  An Evans potential with logarithmic zero at \(p\) is harmonic on the
  punctured surface, has local form \(\log |z-z(p)|\) plus a harmonic
  function near \(p\), and tends to \(+\infty\) at infinity with compact
  sublevel sets after adjoining \(p\).
-/
structure EvansPotentialAt (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (p : X) where
  /-- The real-valued Evans potential. -/
  toFun : X → ℝ
  /-- The potential is harmonic away from its logarithmic zero. -/
  harmonic_away_pole : IsHarmonicOnSurface {x : X | x ≠ p} toFun
  /-- The potential tends to \(-\infty\) at its logarithmic zero. -/
  tends_to_neg_infinity_at_pole :
    Filter.Tendsto toFun (𝓝[≠] p) Filter.atBot
  /-- In every coordinate at the pole, the logarithmic singularity is removable. -/
  logarithmic_zero :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ h : X → ℝ,
        IsHarmonicOnSurface χ.chart.source h ∧
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            toFun x - Real.log ‖χ.chart x - χ.chart p‖ = h x
  /-- The potential tends to \(+\infty\) along the ends of the surface. -/
  tends_to_infinity_at_infinity :
    Filter.Tendsto toFun (Filter.cocompact X) Filter.atTop
  /--
  Sublevel sets of the potential are compact after adjoining the logarithmic
  zero.  The point is adjoined explicitly because `toFun` is represented as an
  ordinary real-valued function at `p`, while the mathematical limiting value
  there is `-∞`.
  -/
  compact_sublevel_with_zero :
    ∀ a : ℝ, IsCompact ({p} ∪ {x : X | toFun x ≤ a})

/--
%%handwave
name:
  Plane map associated to an Evans potential
statement:
  A holomorphic plane map is associated to an Evans potential when its
  logarithmic modulus is the potential away from \(p\), its only zero is
  \(p\), and that zero is simple.
-/
structure EvansPotentialPlaneMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (E : EvansPotentialAt X p) where
  /-- The holomorphic map to the complex plane. -/
  toFun : X → ℂ
  /-- The map is holomorphic. -/
  holomorphic : HolomorphicMap X ℂ toFun
  /-- Away from the zero, the logarithmic modulus is the Evans potential. -/
  log_norm_eq : ∀ x : X, x ≠ p → Real.log ‖toFun x‖ = E.toFun x
  /-- The only zero of the plane map is the marked point. -/
  zero_fiber : ∀ x : X, toFun x = 0 ↔ x = p
  /-- The zero at the marked point is simple. -/
  simple_zero :
    ∀ χ : PointedSurfaceCoordinate X p,
      surfaceComplexDerivativeInCoordinate χ toFun ≠ 0

end Uniformization

end JJMath
